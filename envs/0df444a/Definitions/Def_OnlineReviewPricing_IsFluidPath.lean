-- Prove2me | Definitions.Def_OnlineReviewPricing_IsFluidPath
-- name    : OnlineReviewPricing_IsFluidPath
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T04:27:39.495199+00:00
-- url     : https://prove2.me/theorems/07ccdc34-27cb-42f5-b813-e041d389215b
-- title:
--   Admissible pairs $(p,n)$ of the fluid problem: $\dot n=\lambda(p,n)$, $n(0)=0$
-- statement:
--   A pair $(p,n)$ of functions on $[0,T]$ is **admissible** for the fluid problem if $p$ is piecewise continuous, $n$ is continuous, and
--
--   $$
--   \dot n(t)=\lambda\bigl(p(t),n(t)\bigr),\qquad n(0)=0 .
--   $$
--
--   The number of reviews $n$ is thus driven by the demand that the price path induces, and the demand in turn depends on $n$ through the posterior mean.
--
--   **Formalization Note** The equation is stated in integral form, $n(t)=\int_0^t\lambda(p(s),n(s))\,ds$ for $t\in[0,T]$. This is its meaning at the discontinuities of $p$, and it gives $\dot n(t)=\lambda(p(t),n(t))$ at every continuity point of $p$.
-- source:
--   Shin, Vaccari, Zeevi, Dynamic Pricing with Online Reviews, SSRN 3439836 (Nov. 24, 2021), §3.1, p.12, constraints of (10)

import Mathlib
import Definitions.Def_OnlineReviewPricing_demand
import Definitions.Def_OnlineReviewPricing_IsPiecewiseContinuousOn

namespace OnlineReviewPricing

/-- `(p, n)` is admissible for the fluid problem (10): `p` is piecewise continuous, and `n` solves
`ṅ(t) = λ(p(t), n(t))`, `n(0) = 0` on `[0, T]`
(Shin, Vaccari, Zeevi, Dynamic Pricing with Online Reviews, SSRN 3439836 (Nov. 24, 2021), §3.1, p.12).

**Formalization Note.** The differential equation is stated in integral form. The integrand is
bounded and measurable, so the integral is genuine. Since `p` has discontinuities, the integral
form is the meaning of the equation there, and it gives `ṅ(t) = λ(p(t), n(t))` at every continuity
point of `p`. -/
def IsFluidPath (μ μ₀ γ T : ℝ) (p n : ℝ → ℝ) : Prop :=
  IsPiecewiseContinuousOn T p ∧ ContinuousOn n (Set.Icc 0 T) ∧ n 0 = 0 ∧
    ∀ t ∈ Set.Icc 0 T, n t = ∫ s in (0 : ℝ)..t, demand μ μ₀ γ (p s) (n s)

end OnlineReviewPricing


