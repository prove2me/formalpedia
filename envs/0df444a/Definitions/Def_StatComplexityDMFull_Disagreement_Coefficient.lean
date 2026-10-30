-- Prove2me | Definitions.Def_StatComplexityDMFull_Disagreement_Coefficient
-- name    : StatComplexityDMFull_Disagreement_Coefficient
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T14:53:21.818583+00:00
-- url     : https://prove2.me/theorems/78f4defc-fdd7-4600-9f21-17dad270c04d
-- title:
--   Definition 6.3 — the full two-scale disagreement coefficient
-- statement:
--   Let $\mu$ be an index probability law on $Z$, let $a:Z\to\Pi$ select decisions, and write $\rho=a_\#\mu$. For a function $f:\Pi\to\mathbb R$, its squared moment is $Q_\rho(f)=\mathbb E_{z'\sim\mu}f(a(z'))^2$. For a function class $\mathcal F$ and thresholds $d,s$, define the event
--
--   $$E_{d,s}=\{\pi:\exists f\in\mathcal F,\ |f(\pi)|>d\ \text{and}\ Q_\rho(f)\le s^2\}.$$
--
--   For positive lower cutoffs $\Delta_0,\varepsilon_0$, the coefficient is
--
--   $$\theta(\mathcal F,\Delta_0,\varepsilon_0;\rho)
--   =\max\left\{1,\sup_{d\ge\Delta_0,\ s\ge\varepsilon_0}
--   \frac{d^2}{s^2}\,\mu(a^{-1}(E_{d,s}))\right\}.$$
--
--   Both scales vary independently. The inner squared-moment draw is independent of the outer event draw. This coefficient measures the probability that some class member has large pointwise value despite a small squared moment. It is the exact complexity parameter in (72) and (140).
--
--   **Formalization Note** Supremum values use extended reals. Under boundedness and positive cutoffs they are finite, so this changes no source value. Events are evaluated by their index preimages; the general decoupling theorem explicitly records their null measurability and that of the displayed random variables.
-- source:
--   Foster, Kakade, Qian and Rakhlin, The Statistical Complexity of Interactive Decision Making, arXiv:2112.13487v3, p. 45, Definition 6.3, (71); p. 104, Section E.2.1 index representation

import Mathlib
import Definitions.Def_StatComplexityDMFull_Disagreement_RadonLaw

set_option autoImplicit false

namespace StatComplexityDMFull.Disagreement

/-- The inner decision is a fresh independent index, not the outer decision. -/
noncomputable def squareMoment {Z A : Type*} [MeasurableSpace Z]
    (μ : MeasureTheory.Measure Z) (a : Z → A) (f : A → ℝ) : ℝ :=
  ∫ z, (f (a z)) ^ 2 ∂μ

/-- Strict outer threshold and non-strict squared-moment threshold of (71). -/
def disagreementEvent {Z A : Type*} [MeasurableSpace Z]
    (μ : MeasureTheory.Measure Z) (a : Z → A) (F : Set (A → ℝ)) (d s : ℝ) : Set A :=
  {x | ∃ f ∈ F, d < |f x| ∧ squareMoment μ a f ≤ s ^ 2}

/-- (71), evaluated under the law of a(z). Extended suprema have no real-default collapse.
On a general index space its random variables and events obey the explicit hypotheses of E.2.
On a discrete Radon model space the preimage gives the canonical atomic event probability. -/
noncomputable def disagreementCoeff {Z A : Type*} [MeasurableSpace Z]
    (μ : MeasureTheory.Measure Z) (a : Z → A) (F : Set (A → ℝ)) (Δ₀ ε₀ : ℝ) : EReal :=
  max 1 (sSup {x : EReal | ∃ d s : ℝ, Δ₀ ≤ d ∧ ε₀ ≤ s ∧
    x = ((d ^ 2 / s ^ 2 * pullbackProb μ a (disagreementEvent μ a F d s) : ℝ) : EReal)})

end StatComplexityDMFull.Disagreement


