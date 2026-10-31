-- Prove2me | Definitions.Def_RobustToDynamics_encLinSys
-- name    : RobustToDynamics_encLinSys
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:38:33.361297+00:00
-- url     : https://prove2.me/theorems/8fdf2477-421a-4fdc-b34b-54d713528b41
-- title:
--   Binary encoding of a rational linear system
-- statement:
--   A system $Ax=b$ is written as $p$ in binary, a separator, $q$ in binary, a separator, the rows of $A$, and the entries of $b$.
--
--   **Formalization Note** Complexity is read in the standard Turing model (footnote 3, p.5) as Mathlib's `Turing.TM2ComputableInPolyTime` over the four-letter alphabet `OnlineCRS.Combine.Sym` (bits $0,1$; $2$ separates numerator and denominator; $3$ separates items). Numbers are written in binary with the published encodings `encNat`, `encRat` (lowest terms) and `encVec`, so the length of an encoding is polynomially related to the size $\sigma$ of p.13.
-- source:
--   Ahmadi & Günlük, Robust-to-Dynamics Optimization, arXiv:1805.03682v2, p.13

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_OnlineCRS_Combine_encNat
import Definitions.Def_OnlineCRS_Combine_encVec
import Definitions.Def_RobustToDynamics_encMat
import Definitions.Def_RobustToDynamics_LinSys

namespace RobustToDynamics

/-- **Encoding of a rational linear system `Ax = b`.**
Ahmadi & Günlük, *Robust-to-Dynamics Optimization*, arXiv:1805.03682v2, p.13 ("the size of the data
defining the equality system").

`encLinSys s` is `p` in binary, `3`, `q` in binary, `3`, the rows of `A` (`encMat`) and
`b` (`encVec`).

**Formalization Note.** Complexity questions are read in the standard Turing model (footnote 3,
p.5) as Mathlib's `Turing.TM2ComputableInPolyTime` over the alphabet `OnlineCRS.Combine.Sym = Fin 4`
(`0`, `1` bits, `2` separates numerator and denominator, `3` separates items). Numbers are written in
binary with the published encodings `encNat`/`encRat`/`encVec` (rationals in lowest terms), so the
length of an encoding is polynomially related to the size σ of p.13. -/
def encLinSys (s : LinSys) : List OnlineCRS.Combine.Sym :=
  OnlineCRS.Combine.encNat s.p ++ [3] ++ OnlineCRS.Combine.encNat s.q ++ [3] ++ encMat s.A ++
    OnlineCRS.Combine.encVec s.b

end RobustToDynamics


