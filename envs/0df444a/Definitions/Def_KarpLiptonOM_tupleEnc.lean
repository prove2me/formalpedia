-- Prove2me | Definitions.Def_KarpLiptonOM_tupleEnc
-- name    : KarpLiptonOM_tupleEnc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:37:03.732242+00:00
-- url     : https://prove2.me/theorems/3520d0b7-a7df-4a03-a261-ef6d47b20e93
-- title:
--   Tuple encoding $(u_1,\dots,u_k) \mapsto u_1\#u_2\#\cdots\#u_k$
-- statement:
--   The **tuple encoding** writes a list $(u_1, \dots, u_k)$ of binary strings as the single string
--   $$
--   u_1 \# u_2 \# \cdots \# u_k
--   $$
--   over the three-letter alphabet $\{0, 1, \#\}$. It is how machines of this development receive several arguments: a predicate $V(x, y, r)$ reads $x\#y\#r$, a randomized machine reads $x\#r$, a generator reads $1^n$.
--
--   For a fixed number $k$ of components the encoding is injective, and its length $|u_1| + \dots + |u_k| + k - 1$ is determined by and determines nothing beyond the component lengths, which is the paper's "length-regular" pairing.
--
--   **Formalization Note** Bits are `some b` and the separator is `none` in `Option Bool`; a one-component tuple is the string itself.
-- source:
--   Hirsch–Volkovich, The Ultimate Karp–Lipton Collapse, STOC 2027 submission (manuscript sha256 aca09a2b…), §A.2.1, p.20 (tuples and length-regular pairs)

import Mathlib

namespace KarpLiptonOM

/-- Encoding of a tuple of binary strings as one string over `{0, 1, #}` (Hirsch–Volkovich, *The Ultimate Karp–Lipton Collapse*, STOC 2027 submission manuscript (sha256 aca09a2b…7c62fd1b), §A.2.1, p.20:
"strings … are identified with tuples of strings"; "pairs are encoded in a length-regular way").
The components are written one after the other, bit `b` as `some b`, separated by `none`.

**Formalization Note** `tupleEnc [x] = x` (bitwise), so a machine on input `x` reads `x`; a tuple
`(x, y, r)` is read as `x # y # r`. For a fixed number of components the encoding is injective and
the length of the encoding of `(x, w)` is `|x| + |w| + 1`; every use fixes the number of components. -/
def tupleEnc (l : List (List Bool)) : List (Option Bool) :=
  List.intercalate [none] (l.map (fun u => u.map some))

end KarpLiptonOM


