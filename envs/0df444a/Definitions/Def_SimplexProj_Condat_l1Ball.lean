-- Prove2me | Definitions.Def_SimplexProj_Condat_l1Ball
-- name    : SimplexProj_Condat_l1Ball
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-01T22:43:41.594883+00:00
-- url     : https://prove2.me/theorems/41997c39-085b-4175-92c4-ca435819ee67
-- title:
--   The $\ell_1$ ball $B$ of radius $a$ in $\mathbb{R}^N$
-- statement:
--   Fix an integer $N$ and a real number $a$. The **$\ell_1$ ball of radius $a$** (also called the cross-polytope) is the set of real vectors of length $N$ whose absolute values sum up to at most $a$:
--
--   $$B := \Big\{ (x_1, \dots, x_N) \in \mathbb{R}^N \;\Big|\; \sum_{n=1}^N |x_n| \le a \Big\}.$$
--
--   Projection onto $B$ reduces to projection onto the simplex of radius $a$ (Condat, Proposition 2.1), and conversely (Remark 2.1).
--
--   **Formalization Note.** Vectors are functions `Fin N → ℝ`.
-- source:
--   Condat, Fast Projection onto the Simplex and the ℓ1 Ball, HAL hal-01056171v2, p. 2 (definition of B, Sect. 1)

import Mathlib

namespace SimplexProj.Condat

/-- The `ℓ1` ball `B ⊂ ℝ^N` of radius `a` (Condat, p. 2): the vectors whose absolute values
sum up to at most `a`. -/
def l1Ball {N : ℕ} (a : ℝ) : Set (Fin N → ℝ) :=
  {x | ∑ n, |x n| ≤ a}

end SimplexProj.Condat


