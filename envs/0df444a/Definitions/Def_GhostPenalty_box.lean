-- Prove2me | Definitions.Def_GhostPenalty_box
-- name    : GhostPenalty_box
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:33:59.867274+00:00
-- url     : https://prove2.me/theorems/632e6b16-d16c-4aac-a022-2ad71902fb42
-- title:
--   The box $\alpha\mathbb B^n_\infty$
-- statement:
--   For $\alpha\in\mathbb R$, the box $\alpha\mathbb B^n_\infty$ is the closed $\infty$-norm ball of radius $\alpha$:
--   $$\alpha\mathbb B^n_\infty=\{d\in\mathbb R^n:\ |d_i|\le\alpha\ \text{for } i=1,\dots,n\}=\{d:\ \|d\|_\infty\le\alpha\}.$$
--   The constraint $\|d\|_\infty\le\beta$ of the direction-finding subproblem and the constraint $\|d\|_\infty\le\rho$ in the definition of $\kappa$ are membership in such boxes.
--
--   **Formalization Note** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)`, whose norm is Euclidean; the $\infty$-norm constraint is written coordinatewise.
-- source:
--   Facchinei, Kungurtsev, Lampariello & Scutari, Ghost Penalties in Nonconvex Constrained Optimization, arXiv:1709.03384v3, §3, p.7

import Mathlib

namespace GhostPenalty

/-- **The box `αBⁿ∞`** (closed ∞-norm ball of radius `α`).
Facchinei, Kungurtsev, Lampariello & Scutari, *Ghost Penalties in Nonconvex Constrained
Optimization*, arXiv:1709.03384v3, §3, p.7: "we equivalently refer to constraint `‖d‖∞ ≤ β` as
`d ∈ βBⁿ∞`, where `Bⁿ∞` is the closed unit ball in `ℝⁿ` associated with the infinity-norm."

`box n α = {d ∈ ℝⁿ : |d_i| ≤ α for every i}`.

**Formalization Note.** `ℝⁿ` is `EuclideanSpace ℝ (Fin n)` (whose own norm is the Euclidean
one); the ∞-norm constraint `‖d‖∞ ≤ α` is written coordinatewise. -/
def box (n : ℕ) (α : ℝ) : Set (EuclideanSpace ℝ (Fin n)) :=
  {d | ∀ i, |d i| ≤ α}

end GhostPenalty


