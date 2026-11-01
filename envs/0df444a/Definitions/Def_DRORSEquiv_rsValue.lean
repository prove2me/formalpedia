-- Prove2me | Definitions.Def_DRORSEquiv_rsValue
-- name    : DRORSEquiv_rsValue
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:37:04.217995+00:00
-- url     : https://prove2.me/theorems/85087654-5da3-4bc0-8e94-faa87ffe7aa3
-- title:
--   RS value function $\kappa(\tau)$ (written $k^*(\tau)$ in Appendix A)
-- statement:
--   The **RS value function** is
--
--   $$\kappa(\tau)=\inf\Big\{k:\ x\in\mathcal X,\ k\ge0,\ h(x,k)\le\tau\Big\}\in[0,\infty],$$
--
--   the optimal value of Problem (RS) with target $\tau$; it is $+\infty$ exactly when RS($\tau$) is infeasible. The proof of Theorem 1 calls the same function $k^*(\tau)$ ("We first define $k^*(\tau)$ as the optimal value of the problem RS($\tau$)", p.33).
--
--   **Formalization Note** The paper writes $\min$; here $\kappa$ is the infimum in $[0,\infty]$, never a default $0$ on an infeasible target. Statements that need attainment assume an optimal solution.
-- source:
--   Wang, Ran, Zhou, He, On the Equivalence and Performance of Distributionally Robust Optimization and Robust Satisficing Models, authors' manuscript (2025), (RS), p.8; Appendix A, proof of Theorem 1, p.33

import Mathlib
import Definitions.Def_DRORSEquiv_IsFeasible

open scoped ENNReal

namespace DRORSEquiv

/-- **The RS value function** `κ(τ)` (Wang, Ran, Zhou, He, *On the Equivalence and Performance of Distributionally Robust Optimization and Robust Satisficing Models*, authors' manuscript (2025), (RS), p.8; written `k*(τ)` in Appendix A,
proof of Theorem 1, p.33: "We first define k∗(τ) as the optimal value of the problem RS(τ)"):
`κ(τ) = inf { k : x ∈ X, k ≥ 0, h(x, k) ≤ τ }`.

**Formalization Note.** The paper writes `min`; here `κ(τ)` is the infimum in `[0, ∞]`, equal to `∞`
exactly when RS(τ) is infeasible (never a junk `0`). Statements that need the minimum to be attained
assume an optimal solution (`Model.IsRSOptimal`). `κ` and `k*` are this one function. -/
noncomputable def rsValue {E Ω : Type*} {S : ℕ} (M : Model E Ω S) (τ : ℝ) : ℝ≥0∞ :=
  ⨅ (x : E) (k : ℝ) (_ : IsFeasible M τ x k), ENNReal.ofReal k

end DRORSEquiv


