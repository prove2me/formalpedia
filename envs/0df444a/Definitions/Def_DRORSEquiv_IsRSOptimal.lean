-- Prove2me | Definitions.Def_DRORSEquiv_IsRSOptimal
-- name    : DRORSEquiv_IsRSOptimal
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:36:58.331381+00:00
-- url     : https://prove2.me/theorems/f2f5ab3d-88c3-46eb-ae46-ce9dfdd5d43a
-- title:
--   Optimal solution of Problem (RS) with target $\tau$
-- statement:
--   A pair $(x,k)$ is an **optimal solution of Problem (RS) with target $\tau$**, written RS($\tau$), when it is feasible at level $\tau$ and $k\le k'$ for every pair $(x',k')$ feasible at level $\tau$:
--
--   $$\kappa(\tau)=\min\Big\{k:\ \frac1S\sum_{s\in[S]}\sup_{z\in\mathcal Z}\{f(x,z)-k\rho(z,\hat z_s)\}\le\tau,\ x\in\mathcal X,\ k\ge0\Big\}$$
--
--   is attained at $(x,k)$. The robust satisficing model minimizes the fragility $k$ with which the expected cost may exceed the target $\tau$ in proportion to the Wasserstein distance from $\mathbb P^\dagger$.
-- source:
--   Wang, Ran, Zhou, He, On the Equivalence and Performance of Distributionally Robust Optimization and Robust Satisficing Models, authors' manuscript (2025), (RS), p.8

import Mathlib
import Definitions.Def_DRORSEquiv_IsFeasible

namespace DRORSEquiv

/-- **Optimal solution of Problem (RS) with target `τ`** (Wang, Ran, Zhou, He, *On the Equivalence and Performance of Distributionally Robust Optimization and Robust Satisficing Models*, authors' manuscript (2025), (RS), p.8):
`(x, k)` is feasible for RS(τ) (`x ∈ X`, `k ≥ 0`, `h(x, k) ≤ τ`) and `k ≤ k'` for every feasible
`(x', k')` of RS(τ); that is, `(x, k)` attains `κ(τ) = min k`. -/
def IsRSOptimal {E Ω : Type*} {S : ℕ} (M : Model E Ω S) (τ : ℝ) (x : E) (k : ℝ) : Prop :=
  IsFeasible M τ x k ∧ ∀ (x' : E) (k' : ℝ), IsFeasible M τ x' k' → k ≤ k'

end DRORSEquiv


