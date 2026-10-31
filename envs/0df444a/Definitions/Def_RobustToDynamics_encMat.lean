-- Prove2me | Definitions.Def_RobustToDynamics_encMat
-- name    : RobustToDynamics_encMat
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:37:41.710334+00:00
-- url     : https://prove2.me/theorems/6710a3bb-7dc1-4044-80d2-cf5180ed66b7
-- title:
--   Binary encoding of a rational matrix
-- statement:
--   A rational matrix $A\in\mathbb Q^{p\times q}$ is written row by row: each row as the encoded vector of its entries (each entry in binary, numerator and denominator in lowest terms, followed by a separator), and then one more separator closing the row.
--
--   This is the matrix part of the input encodings of the mission's polynomial-time statements.
--
--   **Formalization Note** Complexity is read in the standard Turing model (footnote 3, p.5) as Mathlib's `Turing.TM2ComputableInPolyTime` over the four-letter alphabet `OnlineCRS.Combine.Sym` (bits $0,1$; $2$ separates numerator and denominator; $3$ separates items). Numbers are written in binary with the published encodings `encNat`, `encRat` (lowest terms) and `encVec`, so the length of an encoding is polynomially related to the size $\sigma$ of p.13.
-- source:
--   Ahmadi & Günlük, Robust-to-Dynamics Optimization, arXiv:1805.03682v2, footnote 3, p.5; p.13 (size of a rational matrix)

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_OnlineCRS_Combine_encVec

namespace RobustToDynamics

/-- **Encoding of a rational matrix.**
Ahmadi & Günlük, *Robust-to-Dynamics Optimization*, arXiv:1805.03682v2, footnote 3, p.5 (rational
input data in the Turing model) and p.13 (size of a rational matrix).

`encMat A` lists the rows of `A ∈ ℚ^{p×q}` in order, each row written with `encVec` (every entry
followed by `3`) and then closed by one more separator `3`.

**Formalization Note.** Complexity questions are read in the standard Turing model (footnote 3,
p.5) as Mathlib's `Turing.TM2ComputableInPolyTime` over the alphabet `OnlineCRS.Combine.Sym = Fin 4`
(`0`, `1` bits, `2` separates numerator and denominator, `3` separates items). Numbers are written in
binary with the published encodings `encNat`/`encRat`/`encVec` (rationals in lowest terms), so the
length of an encoding is polynomially related to the size σ of p.13. -/
def encMat {p q : ℕ} (A : Matrix (Fin p) (Fin q) ℚ) : List OnlineCRS.Combine.Sym :=
  (List.finRange p).flatMap fun i => OnlineCRS.Combine.encVec (A i) ++ [3]

end RobustToDynamics


