-- Prove2me | Definitions.Def_RobustToDynamics_encLD
-- name    : RobustToDynamics_encLD
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:38:36.984001+00:00
-- url     : https://prove2.me/theorems/e532e5e5-27d7-4e0d-b701-3d9e452562ce
-- title:
--   Binary encoding of the data $(A,b,G)$
-- statement:
--   The data $(A,b,G)$ are written as: $n$ in binary, a separator, $m$ in binary, a separator, the rows of $A$, the entries of $b$ followed by a separator, and the rows of $G$. The dimensions come first, so the encoding determines the instance (injectivity is checked in the mission's sanity file). There is no padding and no unary number.
--
--   **Formalization Note** Complexity is read in the standard Turing model (footnote 3, p.5) as Mathlib's `Turing.TM2ComputableInPolyTime` over the four-letter alphabet `OnlineCRS.Combine.Sym` (bits $0,1$; $2$ separates numerator and denominator; $3$ separates items). Numbers are written in binary with the published encodings `encNat`, `encRat` (lowest terms) and `encVec`, so the length of an encoding is polynomially related to the size $\sigma$ of p.13.
-- source:
--   Ahmadi & Günlük, Robust-to-Dynamics Optimization, arXiv:1805.03682v2, Theorem 2.7, p.13; footnote 3, p.5

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_OnlineCRS_Combine_encNat
import Definitions.Def_OnlineCRS_Combine_encVec
import Definitions.Def_RobustToDynamics_encMat
import Definitions.Def_RobustToDynamics_LDData

namespace RobustToDynamics

/-- **Encoding of the data `(A, b, G)`.**
Ahmadi & Günlük, *Robust-to-Dynamics Optimization*, arXiv:1805.03682v2, Theorem 2.7, p.13 (time
polynomial in `σ(A, b, G)`) and footnote 3, p.5.

`encLD d` is `n` in binary, `3`, `m` in binary, `3`, the rows of `A` (`encMat`), the
vector `b` (`encVec`) followed by `3`, and the rows of `G` (`encMat`). The dimensions come
first, so the encoding determines the instance; it has no padding and no unary numbers.

**Formalization Note.** Complexity questions are read in the standard Turing model (footnote 3,
p.5) as Mathlib's `Turing.TM2ComputableInPolyTime` over the alphabet `OnlineCRS.Combine.Sym = Fin 4`
(`0`, `1` bits, `2` separates numerator and denominator, `3` separates items). Numbers are written in
binary with the published encodings `encNat`/`encRat`/`encVec` (rationals in lowest terms), so the
length of an encoding is polynomially related to the size σ of p.13. -/
def encLD (d : LDData) : List OnlineCRS.Combine.Sym :=
  OnlineCRS.Combine.encNat d.n ++ [3] ++ OnlineCRS.Combine.encNat d.m ++ [3] ++ encMat d.A ++
    OnlineCRS.Combine.encVec d.b ++ [3] ++ encMat d.G

end RobustToDynamics


