-- Prove2me | Definitions.Def_IntADSat_Supplement_outputCode
-- name    : IntADSat_Supplement_outputCode
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:41:19.474165+00:00
-- url     : https://prove2.me/theorems/7e2de8d4-44fd-4b8f-89f0-a88f768248e1
-- title:
--   Binary code of a lattice basis and a list of Smith invariants
-- statement:
--   For a list $B=(x_1,\dots,x_k)$ of integer vectors in $\mathbb Z^n$ and a list $s=(s_1,\dots,s_r)$ of natural numbers, the code is
--   $$\langle k\rangle\ \prod_{j=1}^k\prod_{i=1}^n\big(\sigma(x_{j,i})\,\langle |x_{j,i}|\rangle\big)\ \langle r\rangle\ \langle s_1\rangle\cdots\langle s_r\rangle,$$
--   where $\langle\cdot\rangle$ is the self-delimiting binary code of a natural number and $\sigma(z)$ is a sign bit ($1$ iff $z<0$). For fixed $n$ it is injective, and its length is the bit size of the output. It encodes the output of the algorithm of Theorem A.6: a lattice basis of $\Lambda_G$ and its Smith invariants.
-- source:
--   Z. Lu, Integral saturation of adjacency-degree lattices, arXiv:2611.01838 (held version, sha256 d1acbc32826e81e9ed42d927759ebc2d62786404cb2c44cedc931020e3631145), Theorem A.6, p.13 (PDF 14) (output of the algorithm)

import Mathlib
import Definitions.Def_IntADSat_Supplement_natCode

set_option autoImplicit false

namespace IntADSat.Supplement

/-- The output code of the algorithm in Theorem A.6 (Z. Lu, *Integral saturation of adjacency-degree lattices*, arXiv:2611.01838 (held version, sha256 d1acbc32…3631145), p.13 (PDF 14)): a list `B` of integer vectors
in `ℤⁿ` (the lattice basis) followed by a list `s` of natural numbers (the Smith invariants). It is the
code of the length of `B`, then each vector of `B` as its `n` coordinates in order, each coordinate as a
sign bit (`true` for negative) followed by the code of its absolute value, then the code of the length
of `s` and the code of each entry of `s`.

**Formalization Note** All numbers are in self-delimiting binary (`natCode`), so for fixed `n` the code
is injective in `(B, s)`, and its length is the bit size of the output. -/
def outputCode {n : ℕ} (B : List (Fin n → ℤ)) (s : List ℕ) : List Bool :=
  natCode B.length ++
    B.flatMap (fun x => (List.finRange n).flatMap fun i => decide (x i < 0) :: natCode (x i).natAbs) ++
    natCode s.length ++ s.flatMap natCode

end IntADSat.Supplement


