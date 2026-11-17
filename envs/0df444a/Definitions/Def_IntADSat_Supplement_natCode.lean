-- Prove2me | Definitions.Def_IntADSat_Supplement_natCode
-- name    : IntADSat_Supplement_natCode
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:40:37.091128+00:00
-- url     : https://prove2.me/theorems/24416a1b-41e0-40b2-92b4-375a25aa0955
-- title:
--   Self-delimiting binary code of a natural number
-- statement:
--   For a natural number $a$ with binary digits $b_1\cdots b_\ell$ (Mathlib's `Computability.encodeNat`, least significant digit first; empty for $a=0$), the code is
--   $$\langle a\rangle = 1\,b_1\,1\,b_2\cdots 1\,b_\ell\,0 .$$
--   The code is prefix-free, so concatenations of codes are uniquely decodable, and its length is $2\ell+1$, linear in the bit length of $a$. It is used to encode the output of the algorithm of Theorem A.6.
-- source:
--   Z. Lu, Integral saturation of adjacency-degree lattices, arXiv:2611.01838 (held version, sha256 d1acbc32826e81e9ed42d927759ebc2d62786404cb2c44cedc931020e3631145), Theorem A.6, p.13 (PDF 14) (encoding of the algorithm's output)

import Mathlib

set_option autoImplicit false

namespace IntADSat.Supplement

/-- A self-delimiting binary code of a natural number: each binary digit `b` of Mathlib's
`Computability.encodeNat a` is written as the pair `true, b`, and the code ends with `false`. Used to
encode the output of the algorithm in Theorem A.6 (Z. Lu, *Integral saturation of adjacency-degree lattices*, arXiv:2611.01838 (held version, sha256 d1acbc32…3631145), p.13 (PDF 14)).

**Formalization Note** The code is prefix-free, so concatenations of codes are uniquely decodable;
its length is `2⌊log₂ a⌋ + 3` for `a ≥ 1` and `1` for `a = 0` (bit length, not unary). -/
def natCode (a : ℕ) : List Bool :=
  (Computability.encodeNat a).flatMap (fun b => [true, b]) ++ [false]

end IntADSat.Supplement


