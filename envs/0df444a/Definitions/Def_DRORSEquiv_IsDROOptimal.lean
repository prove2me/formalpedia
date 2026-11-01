-- Prove2me | Definitions.Def_DRORSEquiv_IsDROOptimal
-- name    : DRORSEquiv_IsDROOptimal
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:36:55.112238+00:00
-- url     : https://prove2.me/theorems/f315b89f-0498-4bd5-9a50-88710f036a9a
-- title:
--   Optimal solution of Problem (DRO) with radius $\theta$
-- statement:
--   A triple $(\tau,k,x)$ is an **optimal solution of Problem (DRO) with radius $\theta$**, written DRO($\theta$), when $(x,k)$ is feasible at level $\tau$ and
--
--   $$\tau+k\theta\le\tau'+k'\theta$$
--
--   for every triple $(\tau',k',x')$ with $(x',k')$ feasible at level $\tau'$, where $\tau'$ ranges over all real numbers. Problem (DRO) is the dual reformulation of the Wasserstein distributionally robust problem with radius $\theta$.
-- source:
--   Wang, Ran, Zhou, He, On the Equivalence and Performance of Distributionally Robust Optimization and Robust Satisficing Models, authors' manuscript (2025), (DRO), p.7

import Mathlib
import Definitions.Def_DRORSEquiv_IsFeasible

namespace DRORSEquiv

/-- **Optimal solution of Problem (DRO) with radius `θ`** (Wang, Ran, Zhou, He, *On the Equivalence and Performance of Distributionally Robust Optimization and Robust Satisficing Models*, authors' manuscript (2025), (DRO), p.7):
`(τ, k, x)` is feasible (`x ∈ X`, `k ≥ 0`, `h(x, k) ≤ τ`) and `τ + k θ ≤ τ' + k' θ` for every feasible
`(τ', k', x')`, with `τ'` ranging over all real numbers. -/
def IsDROOptimal {E Ω : Type*} {S : ℕ} (M : Model E Ω S) (θ τ k : ℝ) (x : E) : Prop :=
  IsFeasible M τ x k ∧
    ∀ (τ' k' : ℝ) (x' : E), IsFeasible M τ' x' k' → τ + k * θ ≤ τ' + k' * θ

end DRORSEquiv


