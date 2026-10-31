-- Prove2me | Definitions.Def_DualRCD_IsPrimalOptimal
-- name    : DualRCD_IsPrimalOptimal
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:44:34.502459+00:00
-- url     : https://prove2.me/theorems/123ce90c-83e4-454c-9934-a96dbfec6ebb
-- title:
--   $x$ solves the primal problem (3)
-- statement:
--   The primal problem is
--   $$
--   \min_{x\in\mathbb R^n}g(x)\quad\text{s.t.}\quad x\in\bigcap_{i=1}^mX_i .
--   $$
--   A point $x$ solves it if it is feasible and $g(x)\le g(x')$ for every feasible $x'$.
-- source:
--   Necoara & Fercoq, Linear convergence of dual coordinate descent on non-polyhedral convex problems, arXiv:1911.06014v1, display (3), p.4

import Mathlib

namespace DualRCD

/-- `x` solves the primal problem (3) of Necoara & Fercoq, arXiv:1911.06014v1, p.4:
`min_{x∈ℝⁿ} g(x)` subject to `x ∈ ⋂ᵢ Xᵢ`. -/
def IsPrimalOptimal {n m : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (X : Fin m → Set (EuclideanSpace ℝ (Fin n))) (x : EuclideanSpace ℝ (Fin n)) : Prop :=
  x ∈ ⋂ i, X i ∧ ∀ x' ∈ ⋂ i, X i, g x ≤ g x'

end DualRCD


