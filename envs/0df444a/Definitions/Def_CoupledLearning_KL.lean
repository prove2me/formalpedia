-- Prove2me | Definitions.Def_CoupledLearning_KL
-- name    : CoupledLearning_KL
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:38:58.004786+00:00
-- url     : https://prove2.me/theorems/048f8e91-e1df-41cf-9983-c8d8a03eb38d
-- title:
--   Kullback–Leibler divergence $D_{KL}(\varphi^{s}(y|q)\|\varphi^{s'}(y|q))$ (Definition 1)
-- statement:
--   For a profile $q$ and parameters $s,s'$,
--
--   $$D_{KL}\big(\varphi^{s}(y|q)\,\|\,\varphi^{s'}(y|q)\big)=\begin{cases}\int\varphi^{s}(y|q)\log\dfrac{\varphi^{s}(y|q)}{\varphi^{s'}(y|q)}\,dy, & \varphi^{s}(\cdot|q)\ll\varphi^{s'}(\cdot|q),\\[4pt] \infty, & \text{otherwise.}\end{cases}$$
--
--   The paper uses it with $s=s^*$, the true parameter. It defines payoff-equivalent parameters and the rate in (3).
--
--   **Formalization Note** The value is Mathlib's `InformationTheory.klDiv` of the two payoff distributions, in $[0,\infty]$. It is $\infty$ when absolute continuity fails or the log-likelihood ratio is not integrable; in the second case the integral above is $+\infty$ as well, so the two agree.
-- source:
--   Wu, Amin, Ozdaglar, Convergence and Stability of Coupled Belief–Strategy Learning Dynamics in Continuous Games, arXiv:2206.05637v2, Definition 1, p.12

import Mathlib
import Definitions.Def_CoupledLearning_payoffMeasure

open MeasureTheory

namespace CoupledLearning

/-- Definition 1 (Kullback–Leibler divergence), arXiv:2206.05637v2, p.12:
`D_KL(φ^{s₁}(y|q) ‖ φ^{s₂}(y|q)) = ∫ φ^{s₁}(y|q) log(φ^{s₁}(y|q)/φ^{s₂}(y|q)) dy` if
`φ^{s₁}(·|q) ≪ φ^{s₂}(·|q)`, and `∞` otherwise.

**Formalization Note.** This is Mathlib's `InformationTheory.klDiv` of the two payoff
distributions, valued in `[0, ∞]`. For probability measures it is `∞` unless the first is
absolutely continuous with respect to the second and the log-likelihood ratio is integrable, and
it is `∫ log(dμ/dν) dμ` otherwise. In the remaining case (absolutely continuous, log-likelihood
ratio not integrable) the integral of Definition 1 is `+∞` as well, since its negative part is
integrable; so the two agree on every pair of densities. -/
noncomputable def KL {I S : Type*} [Fintype I] {d : I → ℕ}
    (φ : S → Prof d → (I → ℝ) → ℝ) (s₁ s₂ : S) (q : Prof d) : ENNReal :=
  InformationTheory.klDiv (payoffMeasure φ s₁ q) (payoffMeasure φ s₂ q)

end CoupledLearning


