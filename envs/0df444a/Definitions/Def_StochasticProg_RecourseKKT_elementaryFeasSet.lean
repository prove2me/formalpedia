-- Prove2me | Definitions.Def_StochasticProg_RecourseKKT_elementaryFeasSet
-- name    : StochasticProg_RecourseKKT_elementaryFeasSet
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:43:42.413983+00:00
-- url     : https://prove2.me/theorems/86934432-daba-4744-846f-a0be280b51dc
-- title:
--   Elementary feasibility set $K_2(\xi)$
-- statement:
--   For a recourse matrix $W$ and a realization $(h, T)$, the **elementary feasibility set** is the set of first-stage decisions for which the second stage has a feasible solution:
--
--   $$
--   K_2(\xi) = \{\, x \in \mathbb R^{n_1} \mid \text{there is } y \ge 0 \text{ with } W y = h - T x \,\}.
--   $$
--
--   Equivalently $K_2(\xi) = \{x \mid Q(x,\xi) < \infty\}$ (p. 109). Theorem 1(a) shows that it is a convex polyhedron.
-- source:
--   Birge & Louveaux, Introduction to Stochastic Programming, 2nd ed., Springer 2011, doi:10.1007/978-1-4614-0237-4, Chapter 3, §3.1b, printed p. 105 (PDF p. 130), and §3.1c, printed p. 109 (PDF p. 134)

import Mathlib
open Matrix

namespace StochasticProg.RecourseKKT

/-- **The elementary feasibility set `K₂(ξ)`.**
Birge & Louveaux, *Introduction to Stochastic Programming*, 2nd ed., Springer 2011,
doi:10.1007/978-1-4614-0237-4, Chapter 3, §3.1b, printed p. 105 (PDF p. 130), repeated in §3.1c, printed p. 109
(PDF p. 134): "K₂(ξ) = {x | y ≥ 0 exists s. t. W(ω)y = h(ω) − T(ω)x}".

The set of first-stage decisions `x` for which the second-stage system `W y = h − T x`, `y ≥ 0`
has a solution, for one fixed realization `(h, T)` (and recourse matrix `W`).

**Formalization Note.** Vectors are `Fin n → ℝ` with the componentwise order, so `0 ≤ y` is
`y ≥ 0`. -/
def elementaryFeasSet {n1 m2 n2 : ℕ} (W : Matrix (Fin m2) (Fin n2) ℝ) (h : Fin m2 → ℝ)
    (T : Matrix (Fin m2) (Fin n1) ℝ) : Set (Fin n1 → ℝ) :=
  {x | ∃ y : Fin n2 → ℝ, 0 ≤ y ∧ W *ᵥ y = h - T *ᵥ x}

end StochasticProg.RecourseKKT


