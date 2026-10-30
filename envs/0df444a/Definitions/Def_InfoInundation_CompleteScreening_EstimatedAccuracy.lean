-- Prove2me | Definitions.Def_InfoInundation_CompleteScreening_EstimatedAccuracy
-- name    : InfoInundation_CompleteScreening_EstimatedAccuracy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T14:36:33.371399+00:00
-- url     : https://prove2.me/theorems/0f691cc9-46b1-4208-a2f1-ed84228a819a
-- title:
--   §3 equation (2) — ex-post unknown squared-error estimate and screening scores
-- statement:
--   Let the consumer's current belief about the real truth be $N(\mu,s^2)$, where $\mu\in\mathbb R$ and $s>0$ is the standard deviation. For a real observed post value $z$, equation (2) defines the squared estimate of its noise scale by
--
--   $$
--   A(\mu,s,z)=\int_{\mathbb R}(u-z)^2\,dN(\mu,s^2)(u),\qquad a=\sqrt{A(\mu,s,z)}.
--   $$
--
--   The integral is taken under the current unconditioned normal belief, holding $z$ fixed. It is not conditional on observing that post and does not average over the Bayes posterior of its true scale. With $s'(s,a)=\sqrt{s^2a^2/(s^2+a^2)}$, the two screening scores are
--
--   $$
--   S_{\mathrm{unknown,sd}}(z)=s-s'(s,\sqrt A),\qquad
--   S_{\mathrm{unknown,var}}(z)=s^2-s'(s,\sqrt A)^2.
--   $$
--
--   Here $A=A(\mu,s,z)$. After $z$ is fixed the estimate is deterministic, so the outer expectation in the Screening Equation reduces to these values. These definitions extend the published known-accuracy model without redefining its update or menu operations.
--
--   **Formalization Note** Mathlib's Gaussian parameter is the variance $(s^2).\mathrm{toNNReal}$; this cast does not change the nonnegative square. The definitions are total on real inputs; the target uses $s>0$. Integrability, positivity and the Gaussian second-moment identity are proof obligations, not hypotheses and not replacement definitions.
-- source:
--   Allon, Drakopoulos & Manshadi, Information Inundation on Platforms and Implications, SSRN 3385627, https://ssrn.com/abstract=3385627, supplied PDF created 2020-04-05, SHA256 58d685a3d44192b751d84a3068d681206ddf992c17423e0c4e138ebf661a5517, p. 9 (PDF 9), §3 equation (2); p. 8 (PDF 8), Screening and Belief Updating Equations.

import Definitions.Def_InfoInundation_Screening_Model

namespace InfoInundation.CompleteScreening

open MeasureTheory ProbabilityTheory InfoInundation.Screening

/-- Equation (2), p. 9: the squared accuracy estimate under the current,
unconditioned belief N(μ,s²), with the post value z held fixed.
Mathlib's Gaussian parameter is the variance. This integral is not a
posterior expectation conditional on observing z. -/
noncomputable def estimatedAccuracySq (μ s z : ℝ) : ℝ :=
  ∫ u : ℝ, (u - z) ^ 2 ∂(gaussianReal μ (s ^ 2).toNNReal)

/-- Screening Equation, p. 8, using equation (2)'s ex-post unknown estimate.
Once z is fixed, the estimated scale and updated sd are deterministic. -/
noncomputable def unknownSdScore (μ s z : ℝ) : ℝ :=
  s - nextSd s (Real.sqrt (estimatedAccuracySq μ s z))

/-- The variance reading of the same ex-post unknown screening rule. -/
noncomputable def unknownVarScore (μ s z : ℝ) : ℝ :=
  s ^ 2 - (nextSd s (Real.sqrt (estimatedAccuracySq μ s z))) ^ 2

end InfoInundation.CompleteScreening


