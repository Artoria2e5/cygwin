/* winf.cc

This software is a copyrighted work licensed under the terms of the
Cygwin license.  Please consult the file "CYGWIN_LICENSE" for
details. */

#include "winsup.h"
#include <stdlib.h>
#include "cygerrno.h"
#include "security.h"
#include "path.h"
#include "fhandler.h"
#include "dtable.h"
#include "cygheap.h"
#include "tls_pbuf.h"
#include "winf.h"
#include "sys/cygwin.h"
#include <ctype.h>
#include "glob.h"

void
linebuf::finish (bool cmdlenoverflow_ok)
{
  if (!ix)
    add ("", 1);
  else
    {
      if (ix-- > MAXCYGWINCMDLEN && cmdlenoverflow_ok)
	ix = MAXCYGWINCMDLEN - 1;
      buf[ix] = '\0';
    }
}

void
linebuf::add (const char *what, int len)
{
  size_t newix = ix + len;
  if (newix >= alloced || !buf)
    {
      alloced += LINE_BUF_CHUNK + newix;
      buf = (char *) realloc (buf, alloced + 1);
    }
  memcpy (buf + ix, what, len);
  ix = newix;
  buf[ix] = '\0';
}

void
linebuf::prepend (const char *what, int len)
{
  int buflen;
  size_t newix;
  if ((newix = ix + len) >= alloced)
    {
      alloced += LINE_BUF_CHUNK + newix;
      buf = (char *) realloc (buf, alloced + 1);
      buf[ix] = '\0';
    }
  if ((buflen = strlen (buf)))
      memmove (buf + len, buf, buflen + 1);
  else
      buf[newix] = '\0';
  memcpy (buf, what, len);
  ix = newix;
}

bool
linebuf::fromargv (av& newargv, const char *real_path, bool cmdlenoverflow_ok)
{
  bool success = true;
  for (int i = 0; i < newargv.argc; i++)
    {
      char *p = NULL;
      const char *a;

      a = i ? newargv[i] : (char *) real_path;
      int len = strlen (a);
      if (len != 0 && !strpbrk (a, " \t\n\r\""))
	add (a, len);
      else
	{
	  add ("\"", 1);
	  /* Handle embedded special characters " and \.
	     A " is always preceded by a \.
	     A \ is not special unless it precedes a ".  If it does,
	     then all preceding \'s must be doubled to avoid having
	     the Windows command line parser interpret the \ as quoting
	     the ".  This rule applies to a string of \'s before the end
	     of the string, since cygwin/windows uses a " to delimit the
	     argument. */
	  for (; (p = strpbrk (a, "\"\\")); a = ++p)
	    {
	      add (a, p - a);
	      /* Find length of string of backslashes */
	      int n = strspn (p, "\\");
	      if (!n)
		add ("\\\"", 2);	/* No backslashes, so it must be a ".
					       The " has to be protected with a backslash. */
	      else
		{
		  add (p, n);	/* Add the run of backslashes */
		  /* Need to double up all of the preceding
		     backslashes if they precede a quote or EOS. */
		  if (!p[n] || p[n] == '"')
		    add (p, n);
		  p += n - 1;		/* Point to last backslash */
		}
	    }
	  if (*a)
	    add (a);
	  add ("\"", 1);
	}
      add (" ", 1);
    }

  finish (cmdlenoverflow_ok);

  if (ix >= MAXWINCMDLEN)
    {
      debug_printf ("command line too long (>32K), return E2BIG");
      set_errno (E2BIG);
      success = false;
    }

  return success;
}

int
av::unshift (const char *what)
{
  char **av;
  av = (char **) crealloc (argv, (argc + 2) * sizeof (char *));
  if (!av)
    return 0;

  argv = av;
  memmove (argv + 1, argv, (argc + 1) * sizeof (char *));
  *argv = cstrdup1 (what);
  calloced++;
  argc++;
  return 1;
}

#define MAX_AT_FILE_LEVEL 10

/*
 * Replaces @file in the command line with the contents of the file.
 * There may be multiple @file's in a single command line
 * A \@file is replaced with @file so that echo \@foo would print
 * @foo and not the contents of foo.
 */
static bool
insert_file (char *name, char *&cmd)
{
  HANDLE f;
  DWORD size;
  tmp_pathbuf tp;

  PWCHAR wname = tp.w_get ();
  sys_mbstowcs (wname, NT_MAX_PATH, name + 1);
  f = CreateFileW (wname,
		   GENERIC_READ,		/* open for reading	*/
		   FILE_SHARE_VALID_FLAGS,      /* share for reading	*/
		   &sec_none_nih,		/* default security	*/
		   OPEN_EXISTING,		/* existing file only	*/
		   FILE_ATTRIBUTE_NORMAL,	/* normal file		*/
		   NULL);			/* no attr. template	*/

  if (f == INVALID_HANDLE_VALUE)
    {
      debug_printf ("couldn't open file '%s', %E", name);
      return false;
    }

  /* This only supports files up to about 4 billion bytes in
     size.  I am making the bold assumption that this is big
     enough for this feature */
  size = GetFileSize (f, NULL);
  if (size == 0xFFFFFFFF)
    {
      CloseHandle (f);
      debug_printf ("couldn't get file size for '%s', %E", name);
      return false;
    }

  int new_size = strlen (cmd) + size + 2;
  char *tmp = (char *) malloc (new_size);
  if (!tmp)
    {
      CloseHandle (f);
      debug_printf ("malloc failed, %E");
      return false;
    }

  /* realloc passed as it should */
  DWORD rf_read;
  BOOL rf_result;
  rf_result = ReadFile (f, tmp, size, &rf_read, NULL);
  CloseHandle (f);
  if (!rf_result || (rf_read != size))
    {
      free (tmp);
      debug_printf ("ReadFile failed, %E");
      return false;
    }

  tmp[size++] = ' ';
  strcpy (tmp + size, cmd);
  cmd = tmp;
  return true;
}

static inline int
isquote (char c)
{
  char ch = c;
  return ch == '"' || ch == '\'';
}

/* Step over a run of characters delimited by quotes */
static /*__inline*/ char *
quoted (char *cmd, int winshell)
{
  char *p;
  char quote = *cmd;

  if (!winshell)
    {
      char *p;
      memmove (cmd, cmd + 1, strlen (cmd));
      if (*(p = strchrnul (cmd, quote)))
	memmove (p, p + 1, strlen (p));
      return p;
    }

  const char *s = quote == '\'' ? "'" : "\\\"";
  /* This must have been run from a Windows shell, so preserve
     quotes for globify to play with later. */
  while (*cmd && *++cmd)
    if ((p = strpbrk (cmd, s)) == NULL)
      {
	cmd = strchr (cmd, '\0');	// no closing quote
	break;
      }
    else if (*p == '\\')
      cmd = ++p;
    else if (quote == '"' && p[1] == '"')
      {
	*p = '\\';
	cmd = ++p;			// a quoted quote
      }
    else
      {
	cmd = p + 1;		// point to after end
	break;
      }
  return cmd;
}

/* Grab the next argument from the command line, terminating it in place.
   Return false when the command line is exhausted.  */
static bool
next_arg (char *&cmd, char *&word, char *&sawquote, bool winshell, bool first)
{
  while (issep (*cmd))
    cmd++;

  if (!*cmd)
    return false;

  word = cmd;
  sawquote = NULL;
  while (*cmd)
    {
      if (*cmd != '"' && (!winshell || *cmd != '\''))
	cmd++;			// Skip over this character
      else
	/* Skip over characters until the closing quote */
	{
	  sawquote = cmd;
	  /* Handle quoting.  Only strip off quotes if the parent is
	     a Cygwin process, or if the word starts with a '@'.
	     In this case, the insert_file function needs an unquoted
	     DOS filename and globbing isn't performed anyway. */
	  cmd = quoted (cmd, winshell && !first && *word != '@');
	}
      if (issep (*cmd))		// End of argument if space
	break;
    }
  if (*cmd)
    *cmd++ = '\0';		// Terminate `word'

  return true;
}

/* Perform a glob on word if it contains wildcard characters.
   Also quote every character between quotes to force glob to
   treat the characters literally. */

/* Either X:[...] or \\server\[...] */
#define is_dos_path(s) (isdrive(s) \
			|| ((s)[0] == '\\' \
			    && (s)[1] == '\\' \
			    && isalpha ((s)[2]) \
			    && strchr ((s) + 3, '\\')))

static int
globify (char *word, char **&argv, int &argc, int &argvlen)
{
  if (*word != '~' && strpbrk (word, "?*[\"\'(){}") == NULL)
    return 0;

  int n = 0;
  char *p, *s;
  int dos_spec = is_dos_path (word);
  if (!dos_spec && isquote (*word) && word[1] && word[2])
    dos_spec = is_dos_path (word + 1);

  /* We'll need more space if there are quoting characters in
     word.  If that is the case, doubling the size of the
     string should provide more than enough space. */
  if (strpbrk (word, "'\""))
    n = strlen (word);
  char pattern[strlen (word) + ((dos_spec + 1) * n) + 1];

  /* Fill pattern with characters from word, quoting any
     characters found within quotes. */
  for (p = pattern, s = word; *s != '\000'; s++, p++)
    if (!isquote (*s))
      {
	if (dos_spec && *s == '\\')
	  *p++ = '\\';
	*p = *s;
      }
    else
      {
	char quote = *s;
	while (*++s && *s != quote)
	  {
	    mbstate_t mbs = { 0 };
	    if (dos_spec || *s != '\\')
	      /* nothing */;
	    else if (s[1] == quote || s[1] == '\\')
	      s++;
	    *p++ = '\\';
	    size_t cnt = isascii (*s) ? 1 : mbrtowi (NULL, s, MB_CUR_MAX, &mbs);
	    if (cnt <= 1 || cnt == (size_t)-1)
	      *p++ = *s;
	    else
	      {
		--s;
		while (cnt-- > 0)
		  *p++ = *++s;
	      }
	  }
	if (*s == quote)
	  p--;
	if (*s == '\0')
	    break;
      }

  *p = '\0';

  glob_t gl;
  gl.gl_offs = 0;

  /* Attempt to match the argument.  Return just word (minus quoting) if no match. */
  if (glob (pattern, GLOB_TILDE | GLOB_NOCHECK | GLOB_BRACE | GLOB_QUOTE, NULL, &gl) || !gl.gl_pathc)
    return 0;

  /* Allocate enough space in argv for the matched filenames. */
  n = argc;
  if ((argc += gl.gl_pathc) > argvlen)
    {
      argvlen = argc + 10;
      argv = (char **) realloc (argv, (1 + argvlen) * sizeof (argv[0]));
    }

  /* Copy the matched filenames to argv. */
  char **gv = gl.gl_pathv;
  char **av = argv + n;
  while (*gv)
    {
      debug_printf ("argv[%d] = '%s'", n++, *gv);
      *av++ = *gv++;
    }

  /* Clean up after glob. */
  free (gl.gl_pathv);
  return 1;
}


/* Build argv, argc from string passed from Windows.  */

static void
build_argv (char *cmd, char **&argv, int &argc, int winshell)
{
  int argvlen = 0;
  int nesting = 0;		// monitor "nesting" from insert_file

  argc = 0;
  argvlen = 0;
  argv = NULL;

  char *word;
  char *sawquote;

  /* Scan command line until there is nothing left. */
  while (next_arg (cmd, word, sawquote, winshell, argc == 0))
    {
      /* Possibly look for @file construction assuming that this isn't
	 the very first argument and the @ wasn't quoted */
      if (argc && sawquote != word && *word == '@')
	{
	  if (++nesting > MAX_AT_FILE_LEVEL)
	    api_fatal ("Too many levels of nesting for %s", word);
	  if (insert_file (word, cmd))
	      continue;			// There's new stuff in cmd now
	}

      /* See if we need to allocate more space for argv */
      if (argc >= argvlen)
	{
	  argvlen = argc + 10;
	  argv = (char **) realloc (argv, (1 + argvlen) * sizeof (argv[0]));
	}

      /* Add word to argv file after (optional) wildcard expansion. */
      if (!winshell || !argc || !globify (word, argv, argc, argvlen))
	{
	  debug_printf ("argv[%d] = '%s'", argc, word);
	  argv[argc++] = word;
	}
    }

  if (argv)
    argv[argc] = NULL;

  debug_printf ("argc %d", argc);
}
