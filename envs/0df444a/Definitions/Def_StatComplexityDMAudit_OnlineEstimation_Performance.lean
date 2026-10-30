-- Prove2me | Definitions.Def_StatComplexityDMAudit_OnlineEstimation_Performance
-- name    : StatComplexityDMAudit_OnlineEstimation_Performance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T14:04:40.896676+00:00
-- url     : https://prove2.me/theorems/6d8b5519-c65d-475b-aa7e-88a88e90c23f
-- title:
--   Extended log-loss regret and conditional Hellinger error
-- statement:
--   For a realizable density process, let $L(q)=\sum_{t<T}\ell_{\log,t}(q_t)$, where $\ell_{\log,t}(q_t)=-\log q_t(y_t\mid x_t;H_{<t})$. For experts $g_i$ and true index $i^\star$, define
--   $$\mathrm{Reg}_{\mathrm{KL}}=L(\widehat g)-\inf_{i\in I}L(g_i),\qquad\mathrm{Est}_{\mathrm H}=\sum_{t<T}\mathbb E[D_{\mathrm H}^2(\widehat g_t(x_t),g_{i^\star,t}(x_t))\mid H_{<t}].$$
--   For a predictable Boolean mask $J_t$, define the corresponding masked conditional error and realized true-expert loss gap by summing only rounds with $J_t=1$.
--
--   These are computed performance objects, with no assumed bound. Losses and the arbitrary expert infimum are extended-real; the infimum can be $-\infty$ and need not be measurable or attained. Under realizability the true expert's realized loss is finite almost surely, so regret has no indeterminate subtraction there. Outside this full-measure set Lean's total arithmetic supplies a value without affecting the probability statements. Masks use an explicit zero branch to discard even an infinite unused loss. Conditional error averages the current context given the past alone.
-- source:
--   Foster, Kakade, Qian and Rakhlin, The Statistical Complexity of Interactive Decision Making, arXiv:2112.13487v3 (11 July 2023), https://arxiv.org/abs/2112.13487v3, §A.3.1, equations (99)–(100), printed/PDF pp. 75–76; Lemma A.14 (103), p. 76.

import Mathlib
import Definitions.Def_StatComplexityDMAudit_OnlineEstimation_Protocol

set_option autoImplicit false
open scoped ENNReal NNReal

namespace StatComplexityDMAudit.OnlineEstimation

open MeasureTheory ProbabilityTheory

/-- The realized cumulative extended log loss, equation (99). -/
noncomputable def cumulativeLoss {Ω X Y : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] [MeasurableSpace Y] {T : ℕ} {ν : Kernel X Y}
    (o : Observations Ω X Y T) (q : Predictor ν T) (ω : Ω) : EReal :=
  ∑ t, logLoss (densityAt o q t ω (o.obs t ω).2)

/-- Regret to the pointwise infimum over all experts, without attainment or measurability
of that infimum. The true expert has finite cumulative loss almost surely under A.1. -/
noncomputable def regKL {Ω I X Y : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] [MeasurableSpace Y] {T : ℕ} {ν : Kernel X Y}
    (o : Observations Ω X Y T) (q : Predictor ν T) (g : I → Predictor ν T)
    (ω : Ω) : EReal := cumulativeLoss o q ω - ⨅ i, cumulativeLoss o (g i) ω

/-- The one-round Hellinger error before averaging the random current context. -/
noncomputable def roundHellinger {Ω I X Y : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] [MeasurableSpace Y] {T : ℕ} {ν : Kernel X Y}
    (o : Observations Ω X Y T) (q : Predictor ν T) (g : I → Predictor ν T)
    (istar : I) (t : Fin T) (ω : Ω) : ℝ≥0∞ :=
  hellingerSq (ν ((o.obs t ω).1)) (densityAt o q t ω) (densityAt o (g istar) t ω)

/-- Equation (100): conditional averaging over the current context is with respect
to the past alone. Nonnegative conditional expectation retains infinite inputs. -/
noncomputable def estH {Ω I X Y : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] [MeasurableSpace Y] {T : ℕ} {ν : Kernel X Y}
    (μ : Measure Ω) (o : Observations Ω X Y T) (q : Predictor ν T)
    (g : I → Predictor ν T) (istar : I) (ω : Ω) : ℝ≥0∞ :=
  ∑ t, condLExp (o.past t) μ (roundHellinger o q g istar t) ω

/-- Realized log-loss gap to the true expert. At a zero learner density it is +infinity
a.s.; no finite-loss hypothesis is imposed. -/
noncomputable def roundGap {Ω I X Y : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] [MeasurableSpace Y] {T : ℕ} {ν : Kernel X Y}
    (o : Observations Ω X Y T) (q : Predictor ν T) (g : I → Predictor ν T)
    (istar : I) (t : Fin T) (ω : Ω) : EReal :=
  logLoss (densityAt o q t ω (o.obs t ω).2) -
    logLoss (densityAt o (g istar) t ω (o.obs t ω).2)

/-- A Boolean mask is a measurable function of the preceding history. -/
structure PredictableMask (X Y : Type*) [MeasurableSpace X] [MeasurableSpace Y] (T : ℕ) where
  value : (t : Fin T) → History X Y t.val → Bool
  measurable_value : ∀ t, Measurable (value t)

/-- The zero branch discards a round even when its loss is infinite. -/
noncomputable def maskedGap {Ω I X Y : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] [MeasurableSpace Y] {T : ℕ} {ν : Kernel X Y}
    (o : Observations Ω X Y T) (q : Predictor ν T) (g : I → Predictor ν T)
    (istar : I) (mask : PredictableMask X Y T) (ω : Ω) : EReal :=
  ∑ t, if mask.value t (o.history t ω) then roundGap o q g istar t ω else 0

/-- Masked conditional Hellinger error from equation (103). -/
noncomputable def maskedEstH {Ω I X Y : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] [MeasurableSpace Y] {T : ℕ} {ν : Kernel X Y}
    (μ : Measure Ω) (o : Observations Ω X Y T) (q : Predictor ν T)
    (g : I → Predictor ν T) (istar : I) (mask : PredictableMask X Y T) (ω : Ω) : ℝ≥0∞ :=
  ∑ t, if mask.value t (o.history t ω) then
    condLExp (o.past t) μ (roundHellinger o q g istar t) ω else 0

end StatComplexityDMAudit.OnlineEstimation


