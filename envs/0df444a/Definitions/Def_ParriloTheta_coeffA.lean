-- Prove2me | Definitions.Def_ParriloTheta_coeffA
-- name    : ParriloTheta_coeffA
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:27:20.660928+00:00
-- url     : https://prove2.me/theorems/898b5fb4-97c2-41b5-b3c7-31cb90429aa8
-- title:
--   The constant $a$ of (6.6)
-- statement:
--   For integers $\alpha,k$ and a real number $b$,
--   $$
--   a=\alpha-3-\frac{2}{k}\big(b(k+1)+1-\alpha-b\alpha\big).
--   $$
--   It is the diagonal entry of the block $M_b$ of the matrix (6.5).
-- source:
--   Laurent & Vargas, Exactness of Parrilo's conic approximations for copositive matrices and associated low order bounds for the stability number of a graph, arXiv:2109.12876v1, eq. (6.6), p.21

import Mathlib

namespace ParriloTheta

/-- **The constant `a` of (6.6).**
Laurent & Vargas, arXiv:2109.12876v1, eq. (6.6), p.21:
"a = α − 3 − (2/k)(b(k + 1) + 1 − α − bα)".

**Formalization Note.** `α, k` are natural numbers cast to `ℝ`; `b : ℝ`. -/
noncomputable def coeffA (α k : ℕ) (b : ℝ) : ℝ :=
  (α : ℝ) - 3 - (2 / (k : ℝ)) * (b * ((k : ℝ) + 1) + 1 - (α : ℝ) - b * (α : ℝ))

end ParriloTheta


