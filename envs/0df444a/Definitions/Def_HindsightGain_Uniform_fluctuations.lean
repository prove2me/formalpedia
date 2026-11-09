-- Prove2me | Definitions.Def_HindsightGain_Uniform_fluctuations
-- name    : HindsightGain_Uniform_fluctuations
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:52:12.907073+00:00
-- url     : https://prove2.me/theorems/a7eba49f-39cd-4a70-aba4-d34834e6612c
-- title:
--   Support-function fluctuation and its variance scale
-- statement:
--   Let $\zeta_i$ be independent nonnegative weights on a probability space, with finite second moments, and put $p_i=\mathbb E\zeta_i$. For the concrete row maps $L_i$ of the interaction tensor, set
--   $$\Delta(\zeta)=\max_{\|w\|\le1}\sum_i(\zeta_i-p_i)h_{K_i}(L_iw),\qquad V^2=\sum_i\operatorname{Var}(\zeta_i)\|L_i\|_F^2,\quad V=\sqrt{V^2}.$$
--   The tensor unit ball carries its Euclidean norm. The maximum is taken from the actual support functions and matrix coefficients, with no assumed fluctuation bound. This layer defines the random variable and its scale; its measurability and square integrability follow from the source hypotheses and are obligations of Lemma 3.2.
-- source:
--   Xiaohui Bei, Wenhao Wu, The Optimizer's Windfall: Bounding Hindsight Gain under Random Restrictions, STOC 2027 submission #464 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/464.pdf, §3.3, (19)–(20), p.16

import Mathlib
import Definitions.Def_HindsightGain_Uniform_tensors

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace HindsightGain.Uniform

/-- The actual compact unit-ball maximum in (20); no bound is built into this definition. -/
def fluctuation {n D r : ℕ} (M : Model n D r) (p ζ : Fin n → ℝ) : ℝ :=
  sSup ((fun w : Tensor (Fin n × Fin D) (r - 1) =>
    ∑ i, (ζ i - p i) * support (M.K i) (rowBlock M i w)) '' Metric.closedBall 0 1)

def weightMeans {Ω : Type} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) (ζ : Fin n → Ω → ℝ) : Fin n → ℝ := fun i => ∫ ω, ζ i ω ∂μ

def fluctuationRV {Ω : Type} [MeasurableSpace Ω] {n D r : ℕ}
    (M : Model n D r) (μ : Measure Ω) (ζ : Fin n → Ω → ℝ) : Ω → ℝ :=
  fun ω => fluctuation M (weightMeans μ ζ) (fun i => ζ i ω)

def varianceScaleSq {Ω : Type} [MeasurableSpace Ω] {n D r : ℕ}
    (M : Model n D r) (μ : Measure Ω) (ζ : Fin n → Ω → ℝ) : ℝ :=
  ∑ i, variance (ζ i) μ * rowFrobeniusSq M i

def varianceScale {Ω : Type} [MeasurableSpace Ω] {n D r : ℕ}
    (M : Model n D r) (μ : Measure Ω) (ζ : Fin n → Ω → ℝ) : ℝ :=
  Real.sqrt (varianceScaleSq M μ ζ)

end HindsightGain.Uniform


