-- Prove2me | Definitions.Def_QiFixedDesign_Concentration_LightTail
-- name    : QiFixedDesign_Concentration_LightTail
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T14:59:07.625444+00:00
-- url     : https://prove2.me/theorems/987fc345-b0ce-4bed-a794-c84cd91dc13e
-- title:
--   Light-tail moment and the printed variance-bound constant
-- statement:
--   The exponential moment is $A_a(\mu)=\int\exp(|u|^a)\,\mu(du)$, computed as a nonnegative extended integral. The light-tail assumption with parameters $a,A\in\mathbb R$ means $a>1$, $A>1$, and $A_a(\mu)=A$. Equality to a finite real enforces genuine finiteness. Define $\kappa(a,A)=(2(A-1))^{1/a}$. This is a numerical formula only: the definition does not assert that it bounds variance. All measures in the concentration theorems are probability measures of mean zero.
-- source:
--   Qi, Cao and Shen (2021), Distributionally Robust Conditional Quantile Prediction with Fixed Design, DOI 10.1287/mnsc.2020.3903, supplied source.pdf, Assumption 3 and (33), PDF/printed p. 16

import Mathlib

open MeasureTheory Matrix Filter Topology
open scoped ENNReal

namespace QiFixedDesign.Concentration

noncomputable def exponentialMoment (μ : Measure ℝ) (a : ℝ) : ℝ≥0∞ :=
  ∫⁻ u, ENNReal.ofReal (Real.exp (|u| ^ a)) ∂μ

def LightTail (μ : Measure ℝ) (a A : ℝ) : Prop :=
  1 < a ∧ 1 < A ∧ exponentialMoment μ a = ENNReal.ofReal A

noncomputable def kappa (a A : ℝ) : ℝ := (2 * (A - 1)) ^ (1 / a)

end QiFixedDesign.Concentration


