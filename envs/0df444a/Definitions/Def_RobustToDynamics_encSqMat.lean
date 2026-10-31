-- Prove2me | Definitions.Def_RobustToDynamics_encSqMat
-- name    : RobustToDynamics_encSqMat
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:38:51.754401+00:00
-- url     : https://prove2.me/theorems/0799295e-cc62-4a61-a16a-d7669d12548a
-- title:
--   Binary encoding of a rational square matrix
-- statement:
--   A rational square matrix $G\in\mathbb Q^{n\times n}$ is written as $n$ in binary, a separator, and the rows of $G$.
--
--   **Formalization Note** Complexity is read in the standard Turing model (footnote 3, p.5) as Mathlib's `Turing.TM2ComputableInPolyTime` over the four-letter alphabet `OnlineCRS.Combine.Sym` (bits $0,1$; $2$ separates numerator and denominator; $3$ separates items). Numbers are written in binary with the published encodings `encNat`, `encRat` (lowest terms) and `encVec`, so the length of an encoding is polynomially related to the size $\sigma$ of p.13.
-- source:
--   Ahmadi & Günlük, Robust-to-Dynamics Optimization, arXiv:1805.03682v2, Theorem 2.7, proof, Step 1, p.14

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_OnlineCRS_Combine_encNat
import Definitions.Def_RobustToDynamics_encMat
import Definitions.Def_RobustToDynamics_SqMatQ

namespace RobustToDynamics

/-- **Encoding of a rational square matrix `G`.**
Ahmadi & Günlük, *Robust-to-Dynamics Optimization*, arXiv:1805.03682v2, Theorem 2.7, proof,
Step 1, p.14 (polynomial in `σ(G)`).

`encSqMat s` is `n` in binary, `3`, and the rows of `G` (`encMat`).

**Formalization Note.** Complexity questions are read in the standard Turing model (footnote 3,
p.5) as Mathlib's `Turing.TM2ComputableInPolyTime` over the alphabet `OnlineCRS.Combine.Sym = Fin 4`
(`0`, `1` bits, `2` separates numerator and denominator, `3` separates items). Numbers are written in
binary with the published encodings `encNat`/`encRat`/`encVec` (rationals in lowest terms), so the
length of an encoding is polynomially related to the size σ of p.13. -/
def encSqMat (s : SqMatQ) : List OnlineCRS.Combine.Sym :=
  OnlineCRS.Combine.encNat s.n ++ [3] ++ encMat s.G

end RobustToDynamics


