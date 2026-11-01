-- Prove2me | Definitions.Def_StochCoordProx_WellAligned
-- name    : StochCoordProx_WellAligned
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:32:23.570322+00:00
-- url     : https://prove2.me/theorems/795e80f0-2a71-42ab-8b42-0be22ac10644
-- title:
--   Well-aligned matrix (Definition 4)
-- statement:
--   Let $\alpha\in\mathbb R$, $g\in\mathbb R^n$ and $U\in\mathbb R^{n\times p}$. The matrix $U$ is **well-aligned** with $g$ at level $\alpha$ if
--
--   $$
--   \|U^Tg\|\ge\alpha\|g\| .
--   $$
--
--   In the paper $g=\nabla F(x_k)$ and $\alpha\in(0,1)$ is fixed. A well-aligned subspace preserves a fixed fraction of the full gradient, which links the step $d_k$ to $\nabla F(x_k)$.
-- source:
--   Necoara & Chorobura, Efficiency of stochastic coordinate proximal gradient methods on nonseparable composite optimization, arXiv:2104.13370v3, Definition 4, display (14), p.7

import Mathlib

open Matrix

namespace StochCoordProx

/-- **Well-aligned matrix** (Definition 4, display (14)): the matrix `U ∈ ℝ^{n×p}` is
well-aligned with the vector `g ∈ ℝⁿ` (in the paper, `g = ∇F(x_k)`) at level `α` if
`‖Uᵀ g‖ ≥ α ‖g‖`.

Necoara & Chorobura, arXiv:2104.13370v3, Definition 4, display (14), p.7.

**Formalization Note.** The predicate takes the gradient `g = ∇F(x_k)` as an argument; the
SCPG statements instantiate it with `gradient (fun y => f y + ψ y) (x k ω)`. The paper's
`α ∈ (0,1)` is a hypothesis of the statements that use the predicate. -/
def WellAligned {n p : ℕ} (α : ℝ) (g : EuclideanSpace ℝ (Fin n))
    (U : Matrix (Fin n) (Fin p) ℝ) : Prop :=
  α * ‖g‖ ≤ ‖Matrix.toEuclideanLin Uᵀ g‖

end StochCoordProx


