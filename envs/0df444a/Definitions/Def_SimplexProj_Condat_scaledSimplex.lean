-- Prove2me | Definitions.Def_SimplexProj_Condat_scaledSimplex
-- name    : SimplexProj_Condat_scaledSimplex
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-01T22:36:11.031902+00:00
-- url     : https://prove2.me/theorems/2014d0ae-e142-456e-8369-5fea87864acd
-- title:
--   The simplex $\Delta$ of radius $a$ in $\mathbb{R}^N$ (Eq. (3))
-- statement:
--   Fix an integer $N$ and a real number $a$. The **simplex of radius $a$** is the set of real vectors of length $N$ whose entries are nonnegative and sum up to $a$:
--
--   $$\Delta := \Big\{ (x_1, \dots, x_N) \in \mathbb{R}^N \;\Big|\; \sum_{n=1}^N x_n = a \text{ and } x_n \ge 0 \ \forall n = 1, \dots, N \Big\}.$$
--
--   For $a = 1$ this is the unit (standard, probability) simplex. It is the feasible set of the projection problem studied by Condat, and the target set of the Proposed Algorithm.
--
--   **Formalization Note.** Vectors are functions `Fin N → ℝ` (indices $0, \dots, N-1$ in Lean for the paper's $1, \dots, N$). The set is defined for every $N$ and $a$; the theorems that use it add the paper's standing assumptions $N \ge 1$ and $a > 0$.
-- source:
--   Condat, Fast Projection onto the Simplex and the ℓ1 Ball, HAL hal-01056171v2, p. 1, Eq. (3)

import Mathlib

namespace SimplexProj.Condat

/-- The simplex `Δ ⊂ ℝ^N` of radius `a` (Condat, Eq. (3)): the vectors whose entries are
nonnegative and sum up to `a`. -/
def scaledSimplex {N : ℕ} (a : ℝ) : Set (Fin N → ℝ) :=
  {x | ∑ n, x n = a ∧ ∀ n, 0 ≤ x n}

end SimplexProj.Condat


