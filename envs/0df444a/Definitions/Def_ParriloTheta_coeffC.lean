-- Prove2me | Definitions.Def_ParriloTheta_coeffC
-- name    : ParriloTheta_coeffC
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:27:23.052982+00:00
-- url     : https://prove2.me/theorems/f292ae35-9606-47b6-96f5-ff1e7f65331e
-- title:
--   The constant $c$ of (6.6)
-- statement:
--   For an integer $k$ and a real number $b$,
--   $$
--   c=-1-\frac{2}{k}(b+1).
--   $$
--   It is the off-diagonal entry of the block $M_b$ of the matrix (6.5).
-- source:
--   Laurent & Vargas, Exactness of Parrilo's conic approximations for copositive matrices and associated low order bounds for the stability number of a graph, arXiv:2109.12876v1, eq. (6.6), p.21

import Mathlib

namespace ParriloTheta

/-- **The constant `c` of (6.6).**
Laurent & Vargas, arXiv:2109.12876v1, eq. (6.6), p.21: "c = −1 − (2/k)(b + 1)".

**Formalization Note.** `k` is a natural number cast to `ℝ`; `b : ℝ`. -/
noncomputable def coeffC (k : ℕ) (b : ℝ) : ℝ :=
  -1 - (2 / (k : ℝ)) * (b + 1)

end ParriloTheta


