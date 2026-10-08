-- Prove2me | Definitions.Def_GenEmpLik_Consistency_AssumptionE
-- name    : GenEmpLik_Consistency_AssumptionE
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T08:52:55.105058+00:00
-- url     : https://prove2.me/theorems/83151ec6-ff18-4947-8881-b19c5978a2cd
-- title:
--   Assumption E — an envelope of the loss with more than one moment
-- statement:
--   Let $P_0$ be a probability distribution on a measurable space $\Xi$, $\mathcal X$ a set of decisions and $\ell:\mathcal X\times\Xi\to\mathbb R$ a loss. **Assumption E** holds if there is a measurable envelope $Z:\Xi\to\mathbb R_+$ with
--
--   $$
--   |\ell(x;\xi)|\le Z(\xi)\quad\text{for all } x\in\mathcal X,\ \xi\in\Xi,
--   \qquad\text{and}\qquad
--   E_{P_0}\big[Z(\xi)^{1+\epsilon}\big]<\infty\ \text{ for some }\epsilon>0 .
--   $$
--
--   Compared with sample average approximation, which needs only an integrable envelope, the robust objective requires slightly more than one moment; this is what lets the worst-case reweighting inside a $\rho/n$ divergence ball be controlled uniformly in $x$.
--
--   **Formalization Note** Measurability of $Z$, implicit in the expectation $E_{P_0}[Z^{1+\epsilon}]$, is stated explicitly; finiteness of the expectation is integrability of $Z^{1+\epsilon}$ (a nonnegative function).
-- source:
--   Duchi, Glynn & Namkoong, Statistics of Robust Optimization: A Generalized Empirical Likelihood Approach, arXiv:1610.03425v3, p. 16, Assumption E

import Mathlib

open MeasureTheory

namespace GenEmpLik.Consistency

/-- Assumption E (arXiv:1610.03425v3, p. 16): there is a measurable envelope `Z : Ξ → ℝ₊` with
`|ℓ(x; ξ)| ≤ Z(ξ)` for all `x ∈ X` and all `ξ`, and some `ε > 0` with `E_{P₀}[Z(ξ)^{1+ε}] < ∞`. -/
def AssumptionE {E Ξ : Type*} [MeasurableSpace Ξ] (P₀ : Measure Ξ) (X : Set E)
    (ℓ : E → Ξ → ℝ) : Prop :=
  ∃ Z : Ξ → ℝ, Measurable Z ∧ (∀ s, 0 ≤ Z s) ∧ (∀ x ∈ X, ∀ s, |ℓ x s| ≤ Z s) ∧
    ∃ ε : ℝ, 0 < ε ∧ Integrable (fun s => Z s ^ (1 + ε)) P₀

end GenEmpLik.Consistency


