-- Prove2me | Definitions.Def_RobustToDynamics_encListRat
-- name    : RobustToDynamics_encListRat
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:37:24.565963+00:00
-- url     : https://prove2.me/theorems/e196f69f-a68b-48a0-9fd2-da259086c1d3
-- title:
--   Binary encoding of a list of rationals (output vector)
-- statement:
--   A finite list $(q_1,\dots,q_k)$ of rationals is written as the binary encodings of $q_1,\dots,q_k$ (lowest terms), each followed by a separator.
--
--   It is the output encoding of the polynomial-time statements whose output is a rational vector: an optimal solution of an R-LD-LP or an LP, a solution of a linear system, or the entries of the Lyapunov solution $M$.
--
--   **Formalization Note** Complexity is read in the standard Turing model (footnote 3, p.5) as Mathlib's `Turing.TM2ComputableInPolyTime` over the four-letter alphabet `OnlineCRS.Combine.Sym` (bits $0,1$; $2$ separates numerator and denominator; $3$ separates items). Numbers are written in binary with the published encodings `encNat`, `encRat` (lowest terms) and `encVec`, so the length of an encoding is polynomially related to the size $\sigma$ of p.13.
-- source:
--   Ahmadi & Günlük, Robust-to-Dynamics Optimization, arXiv:1805.03682v2, Theorem 2.7, pp.13–14; p.13

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_OnlineCRS_Combine_encRat

namespace RobustToDynamics

/-- **Encoding of a finite list of rationals (an output vector).**
Ahmadi & Günlük, *Robust-to-Dynamics Optimization*, arXiv:1805.03682v2, Theorem 2.7, p.13–14
("R-LD-LPs … can be solved": the output is an optimal solution in ℚⁿ) and p.13 (rational solutions
of linear systems and linear programs).

`encListRat l` writes each entry of `l` with `encRat`, followed by the separator `3`.

**Formalization Note.** Complexity questions are read in the standard Turing model (footnote 3,
p.5) as Mathlib's `Turing.TM2ComputableInPolyTime` over the alphabet `OnlineCRS.Combine.Sym = Fin 4`
(`0`, `1` bits, `2` separates numerator and denominator, `3` separates items). Numbers are written in
binary with the published encodings `encNat`/`encRat`/`encVec` (rationals in lowest terms), so the
length of an encoding is polynomially related to the size σ of p.13. -/
def encListRat (l : List ℚ) : List OnlineCRS.Combine.Sym :=
  l.flatMap fun q => OnlineCRS.Combine.encRat q ++ [3]

end RobustToDynamics


