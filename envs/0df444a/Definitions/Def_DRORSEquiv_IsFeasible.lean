-- Prove2me | Definitions.Def_DRORSEquiv_IsFeasible
-- name    : DRORSEquiv_IsFeasible
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:36:13.983407+00:00
-- url     : https://prove2.me/theorems/a9a87ef0-425f-4015-b562-9d74f3d41506
-- title:
--   Common feasible set of Problems (DRO) and (RS)
-- statement:
--   A pair $(x,k)$ is **feasible at level $\tau\in\mathbb R$** when
--
--   $$x\in\mathcal X,\qquad k\ge0,\qquad h(x,k)\le\tau .$$
--
--   In Problem (RS) the level $\tau$ is the fixed cost target; in Problem (DRO) it is a decision variable, so the feasible triples of (DRO) are the $(\tau,k,x)$ with $(x,k)$ feasible at level $\tau$.
-- source:
--   Wang, Ran, Zhou, He, On the Equivalence and Performance of Distributionally Robust Optimization and Robust Satisficing Models, authors' manuscript (2025), (DRO), p.7, and (RS), p.8

import Mathlib
import Definitions.Def_DRORSEquiv_worstCaseLoss

namespace DRORSEquiv

/-- **The common feasible set of Problems (DRO) and (RS)** (Wang, Ran, Zhou, He, *On the Equivalence and Performance of Distributionally Robust Optimization and Robust Satisficing Models*, authors' manuscript (2025), (DRO) p.7, (RS) p.8):
`(x, k)` is feasible at level `τ` when `x ∈ X`, `k ≥ 0` and
`(1/S) ∑_s sup_{z ∈ Z} { f(x, z) − k ρ(z, ẑ_s) } ≤ τ`. In (RS) the level `τ` is the fixed target; in
(DRO) it is a decision variable. -/
def IsFeasible {E Ω : Type*} {S : ℕ} (M : Model E Ω S) (τ : ℝ) (x : E) (k : ℝ) : Prop :=
  x ∈ M.X ∧ 0 ≤ k ∧ worstCaseLoss M x k ≤ (τ : EReal)

end DRORSEquiv


