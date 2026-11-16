-- Prove2me | Definitions.Def_DDNNFNeg_Supplement_pairEnc
-- name    : DDNNFNeg_Supplement_pairEnc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T21:46:13.8751+00:00
-- url     : https://prove2.me/theorems/fd64c948-6523-48ec-9531-436a79632e6b
-- title:
--   Encoding of a pair of binary strings
-- statement:
--   The pair $(x, w)$ of binary strings is encoded as one binary string by writing each bit $b$ of $x$ as $1b$, then a $0$, then $w$. The encoding is injective and has length $2|x| + 1 + |w|$; it is how a verifier receives its input together with a certificate or a random string.
-- source:
--   Arenas–Broadrick–Liew–Van den Broeck, d-DNNF is Not Polynomially Closed Under Negation, STOC 2027 submission manuscript (sha256 64e4212767c37c44…fbb68), §4, pp.10–11 (classes NP and RP)

import Mathlib

namespace DDNNFNeg.Supplement

/-- An encoding of a pair of binary strings `(x, w)` as one binary string, used to give a
verifier its input and its certificate or random string (Arenas–Broadrick–Liew–Van den Broeck, *d-DNNF is Not Polynomially Closed Under Negation*, STOC 2027 submission manuscript (sha256 64e42127…fbb68), §4, p.10, the classes NP and RP):
each bit `b` of `x` is written as `1 b`, then a `0` marks the end of `x`, then `w` follows.

**Formalization Note** The encoding is injective and of length `2|x| + 1 + |w|`. -/
def pairEnc (x w : List Bool) : List Bool :=
  x.flatMap (fun b => [true, b]) ++ false :: w

end DDNNFNeg.Supplement


