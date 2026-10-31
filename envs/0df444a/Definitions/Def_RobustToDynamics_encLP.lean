-- Prove2me | Definitions.Def_RobustToDynamics_encLP
-- name    : RobustToDynamics_encLP
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:38:39.279535+00:00
-- url     : https://prove2.me/theorems/c6b7009e-474d-4c8a-838c-138d2b76a21c
-- title:
--   Binary encoding of a rational linear program
-- statement:
--   A linear program $(A,b,c)$ is written as $p$ in binary, a separator, $q$ in binary, a separator, the rows of $A$, the entries of $b$ followed by a separator, and the entries of $c$.
--
--   **Formalization Note** Complexity is read in the standard Turing model (footnote 3, p.5) as Mathlib's `Turing.TM2ComputableInPolyTime` over the four-letter alphabet `OnlineCRS.Combine.Sym` (bits $0,1$; $2$ separates numerator and denominator; $3$ separates items). Numbers are written in binary with the published encodings `encNat`, `encRat` (lowest terms) and `encVec`, so the length of an encoding is polynomially related to the size $\sigma$ of p.13.
-- source:
--   Ahmadi & Günlük, Robust-to-Dynamics Optimization, arXiv:1805.03682v2, p.13

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_OnlineCRS_Combine_encNat
import Definitions.Def_OnlineCRS_Combine_encVec
import Definitions.Def_RobustToDynamics_encMat
import Definitions.Def_RobustToDynamics_LPInst

namespace RobustToDynamics

/-- **Encoding of a rational linear program `min {cᵀx : Ax ≤ b}`.**
Ahmadi & Günlük, *Robust-to-Dynamics Optimization*, arXiv:1805.03682v2, p.13 ("the data defining
the LP").

`encLP L` is `p` in binary, `3`, `q` in binary, `3`, the rows of `A` (`encMat`), `b`
(`encVec`) followed by `3`, and `c` (`encVec`).

**Formalization Note.** Complexity questions are read in the standard Turing model (footnote 3,
p.5) as Mathlib's `Turing.TM2ComputableInPolyTime` over the alphabet `OnlineCRS.Combine.Sym = Fin 4`
(`0`, `1` bits, `2` separates numerator and denominator, `3` separates items). Numbers are written in
binary with the published encodings `encNat`/`encRat`/`encVec` (rationals in lowest terms), so the
length of an encoding is polynomially related to the size σ of p.13. -/
def encLP (L : LPInst) : List OnlineCRS.Combine.Sym :=
  OnlineCRS.Combine.encNat L.p ++ [3] ++ OnlineCRS.Combine.encNat L.q ++ [3] ++ encMat L.A ++
    OnlineCRS.Combine.encVec L.b ++ [3] ++ OnlineCRS.Combine.encVec L.c

end RobustToDynamics


