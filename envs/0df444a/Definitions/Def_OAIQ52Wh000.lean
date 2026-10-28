-- Prove2me | Definitions.Def_OAIQ52Wh000
-- name    : OAIQ52Wh000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T18:39:15.882026+00:00
-- url     : https://prove2.me/theorems/c70acc5d-d980-4689-a92c-027caeb7c1a4
-- title:
--   Definitions bundle OAIQ52Wh000 of the split of OpenAI, Weak Hessian bounds along every geodesic in RCD spaces
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.WeakHessian.every_geodesic`, carved from OpenAI's openai/math development (OpenAI, *Weak Hessian bounds along every geodesic in RCD spaces*, OpenAI Math Release, September 24, 2026, result family 358, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 289 declarations of OpenAI's Lean: 46 definitions, 5 inductive types or structures, 2 instances and 236 theorems. The definitions and types are `OAI.WeakHessian.BoundedLipschitzRepresentative`, `OAI.WeakHessian.CDEnvironment`, `OAI.WeakHessian.CDEnvironment.build`, `OAI.WeakHessian.CDEnvironment.limitPlan`, `OAI.WeakHessian.CDEnvironment.midpoint`, `OAI.WeakHessian.CDEnvironment.stablePlanFamily`, `OAI.WeakHessian.CellMidpoint`, `OAI.WeakHessian.CellMidpoint.join`, `OAI.WeakHessian.CellMidpoint.leftCell`, `OAI.WeakHessian.CellMidpoint.middle`, `OAI.WeakHessian.CellMidpoint.rightCell`, `OAI.WeakHessian.CellPlan`, `OAI.WeakHessian.ControlSpace`, `OAI.WeakHessian.CouplingCostBound`, `OAI.WeakHessian.DynamicActionBound`, `OAI.WeakHessian.EntropyCell`, `OAI.WeakHessian.EntropyCell.nextCap`, `OAI.WeakHessian.FiniteEntropy`, `OAI.WeakHessian.HasControlBound`, `OAI.WeakHessian.IsSquareControl`, `OAI.WeakHessian.Joinable`, `OAI.WeakHessian.OptimalPlansShort`, `OAI.WeakHessian.StrictSurplusCarrier`, `OAI.WeakHessian.affineTime`, `OAI.WeakHessian.boundedEndpointTube`, `OAI.WeakHessian.cappedExcess`, `OAI.WeakHessian.cellPlanFamily`, `OAI.WeakHessian.clippedEndpointCost`, `OAI.WeakHessian.compressionRate`, `OAI.WeakHessian.controlNorm`, `OAI.WeakHessian.dyadicTimes`, `OAI.WeakHessian.entropyReal`, `OAI.WeakHessian.halfCurve`, `OAI.WeakHessian.halfTime`, `OAI.WeakHessian.intervalFunctional`, `OAI.WeakHessian.intervalVector`, `OAI.WeakHessian.joinCurve`, `OAI.WeakHessian.joinMap`, `OAI.WeakHessian.kineticAction`, `OAI.WeakHessian.lawAt` and 11 more.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry/WeakHessian, in whole or in part: `WeakHessian_Calculus_ControlNorm`, `WeakHessian_Calculus_DerivSinSubMul`, `WeakHessian_Calculus_DominatedCompactRerouting`, `WeakHessian_Calculus_RnDerivRestrictReference`, `WeakHessian_Calculus_RnDerivSmul`, `WeakHessian_Curvature_Nonbranching`, `WeakHessian_Entropy_AcBoundedRenyiGaps`, `WeakHessian_Entropy_CdEntropyBoundFinite`, `WeakHessian_Entropy_CenteredMulLogDeriv`, `WeakHessian_Entropy_EntropyCell`, `WeakHessian_Entropy_FiniteEntropy`, `WeakHessian_Entropy_RenyiKernel`, `WeakHessian_Entropy_TauDensityLinearLower`, `WeakHessian_Entropy_TendstoRenyiGap`, `WeakHessian_Geodesics_GeodesicPlanSupportedBall`, `WeakHessian_Geodesics_Join`, `WeakHessian_Geodesics_MidpointSigmaLower`, `WeakHessian_HeatFlow_StrictSurplusCarrier`, `WeakHessian_LocalBounds_AffineTime`, `WeakHessian_LocalBounds_BoundedEndpointTube`, `WeakHessian_LocalBounds_BoundedRnRestriction`, `WeakHessian_LocalBounds_CappedExcess`, `WeakHessian_LocalBounds_CompressionRate`, `WeakHessian_LocalBounds_DyadicTimes`, `WeakHessian_LocalBounds_EvalRealCoe`, `WeakHessian_LocalBounds_ExcessRelocation`, `WeakHessian_LocalBounds_GammaRepresentativePairing`, `WeakHessian_LocalBounds_HalfTime`, `WeakHessian_LocalBounds_JoinCurve`, `WeakHessian_LocalBounds_Law`, `WeakHessian_LocalBounds_SigmaCoeffExpLower`, `WeakHessian_LocalBounds_SpeedApprox`, `WeakHessian_LocalBounds_SquareControl`, `WeakHessian_LocalBounds_TimeHalf`, `WeakHessian_Measure_MeasurePositiveNegativeBalance`, `WeakHessian_Measure_OptimalTimeLawSupported`, `WeakHessian_Measure_TimeMeasure`, `WeakHessian_Transport_CdEntropyPlanBounded`, `WeakHessian_Transport_CouplingCostBound`, `WeakHessian_Transport_DynamicActionBound`, `WeakHessian_Transport_HopfObjective`, `WeakHessian_Transport_KineticAction`, `WeakHessian_Transport_LiftBoundedCoupling`, `WeakHessian_Transport_MapCompProdComap`, `WeakHessian_Transport_OptimalPlansShort`, `WeakHessian_Transport_PlanEnergy`, `WeakHessian_Transport_RerouteFiniteSubplanShort`, `WeakHessian_Transport_RestrictCurve`.
--
--   **Imports.** It imports the published bundle `Def_WeakHessian`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ52Wh003` and `OAIQ52Wh004`; the statements `OAI.WeakHessian.RCD.bounded_entropy_subdifferential`, `OAI.WeakHessian.RCD.compact_sobolev_entropy_subdifferential` and `OAI.WeakHessian.RCD.generator_entropy_subdifferential`.
-- source:
--   OpenAI, Weak Hessian bounds along every geodesic in RCD spaces, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 358; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Weak-Hessian-bounds-along-every-geodesic-in-RCD-spaces-September-24-2026/weak-hessian-geodesics.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry/WeakHessian at commit adc7f12

import Mathlib
import Definitions.Def_WeakHessian

section
-- module Solutions.OAIQ52_WH.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    dite p a b = b h := dif_neg h
/-- The first projection of a probability measure on a product: found by instance search in d13f23b
(total `Measure.map`), here a measurable map. -/
instance isProbabilityMeasure_map_fst {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.fst) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
instance isProbabilityMeasure_map_snd {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.snd) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_SquareControl
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open Set Filter Topology Bornology
open scoped InnerProductSpace
open scoped NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped Topology ENNReal NNReal
open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable

namespace WeakHessian
variable {X : Type*} [MetricSpace X]

def IsSquareControl (γ : Curve X) (a : ℝ → ℝ) : Prop :=
  Measurable a ∧ MemLp a 2 (volume.restrict (Icc (0:ℝ) 1)) ∧
    (∀ᵐ t ∂volume.restrict (Icc (0:ℝ) 1), 0 ≤ a t) ∧
    ∀ s t : Time, (s:ℝ) ≤ (t:ℝ) →
      dist (γ s) (γ t) ≤ ∫ r in (s:ℝ)..(t:ℝ), a r

end WeakHessian

open Set Filter Topology Bornology
open scoped InnerProductSpace

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Measure_TimeMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped Topology ENNReal NNReal
open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace

namespace WeakHessian

abbrev timeMeasure : Measure ℝ := volume.restrict (Icc (0:ℝ) 1)
abbrev ControlSpace := Lp ℝ 2 timeMeasure

def intervalVector (s t : Time) : ControlSpace :=
  indicatorConstLp 2 measurableSet_Icc (measure_ne_top _ _) (1:ℝ)
    (s := Icc (s:ℝ) (t:ℝ))

def intervalFunctional (s t : Time) : ControlSpace →L[ℝ] ℝ :=
  innerSL ℝ (intervalVector s t)

lemma intervalFunctional_apply (s t : Time) (u : ControlSpace) (hst : s ≤ t) :
    intervalFunctional s t u = ∫ r in (s:ℝ)..(t:ℝ), u r := by
  rw [intervalFunctional, innerSL_apply_apply, intervalVector,
    L2.inner_indicatorConstLp_one]
  rw [Measure.restrict_restrict measurableSet_Icc, inter_eq_left.mpr
    (Icc_subset_Icc s.2.1 t.2.2), integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le hst]

def HasControlBound {X : Type*} [MetricSpace X] (γ : Curve X) (B : ℝ) : Prop :=
  ∃ u : ControlSpace, ‖u‖ ≤ B ∧ ∀ s t : Time, s ≤ t →
    dist (γ s) (γ t) ≤ intervalFunctional s t u

end WeakHessian

open scoped BoundedContinuousFunction

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Calculus_ControlNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped Topology ENNReal NNReal
open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace
open scoped BoundedContinuousFunction

namespace WeakHessian
variable {X : Type*} [MetricSpace X]

def controlNorm (γ : Curve X) : ℝ≥0∞ :=
  ⨅ (B : ℝ) (_ : HasControlBound γ B), ENNReal.ofReal B

lemma controlNorm_le {γ : Curve X} {B : ℝ} (h : HasControlBound γ B) :
    controlNorm γ ≤ ENNReal.ofReal B :=
  iInf_le_of_le B (iInf_le _ h)

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Calculus_DerivSinSubMul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter

attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology
open Set Filter MeasureTheory InformationTheory
open Set Filter
open scoped Topology

namespace WeakHessian

lemma hasDerivAt_sin_sub_mul_cos (x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.sin y-y*Real.cos y) (x*Real.sin x) x := by
  convert (Real.hasDerivAt_sin x).sub ((hasDerivAt_id x).mul (Real.hasDerivAt_cos x)) using 1 <;> first | rfl | (dsimp; ring)

lemma hasDerivAt_sin_cubic (x : ℝ) :
    HasDerivAt (fun y : ℝ => (1-y^2/3)*Real.sin y-y*Real.cos y)
      (x*(Real.sin x-x*Real.cos x)/3) x := by
  convert (((hasDerivAt_const x (1:ℝ)).sub
    (((hasDerivAt_id x).pow 2).div_const 3)).mul (Real.hasDerivAt_sin x)).sub
    ((hasDerivAt_id x).mul (Real.hasDerivAt_cos x)) using 1 <;> first | rfl | (dsimp; ring)

lemma hasDerivAt_mul_cosh_sub_sinh (x : ℝ) :
    HasDerivAt (fun y : ℝ => y*Real.cosh y-Real.sinh y) (x*Real.sinh x) x := by
  convert ((hasDerivAt_id x).mul (Real.hasDerivAt_cosh x)).sub (Real.hasDerivAt_sinh x) using 1 <;> first | rfl | (dsimp; ring)

lemma hasDerivAt_sinh_cubic (x : ℝ) :
    HasDerivAt (fun y : ℝ => (1+y^2/3)*Real.sinh y-y*Real.cosh y)
      (x*(x*Real.cosh x-Real.sinh x)/3) x := by
  convert (((hasDerivAt_const x (1:ℝ)).add
    (((hasDerivAt_id x).pow 2).div_const 3)).mul (Real.hasDerivAt_sinh x)).sub
    ((hasDerivAt_id x).mul (Real.hasDerivAt_cosh x)) using 1 <;> first | rfl | (dsimp; ring)

lemma hasDerivAt_log_sin_correction {x : ℝ} (hx : 0 < x) (hpi : x < Real.pi) :
    HasDerivAt (fun y : ℝ => Real.log (Real.sin y)-Real.log y+y^2/6)
      (Real.cos x/Real.sin x-1/x+x/3) x := by
  have hs := Real.sin_pos_of_pos_of_lt_pi hx hpi
  convert (((Real.hasDerivAt_sin x).log hs.ne').sub
    ((hasDerivAt_id x).log hx.ne')).add (((hasDerivAt_id x).pow 2).div_const 6) using 1 <;> first | rfl | (dsimp; ring)

lemma hasDerivAt_log_sinh_correction {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => Real.log (Real.sinh y)-Real.log y-y^2/6)
      (Real.cosh x/Real.sinh x-1/x-x/3) x := by
  have hs := Real.sinh_pos_iff.mpr hx
  convert (((Real.hasDerivAt_sinh x).log hs.ne').sub
    ((hasDerivAt_id x).log hx.ne')).sub (((hasDerivAt_id x).pow 2).div_const 6) using 1 <;> first | rfl | (dsimp; ring)

lemma sin_sub_mul_cos_nonneg {x : ℝ} (hx : 0 ≤ x) (hpi : x ≤ Real.pi) :
    0 ≤ Real.sin x - x * Real.cos x := by
  have hm : MonotoneOn (fun y : ℝ => Real.sin y - y * Real.cos y) (Icc 0 Real.pi) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _) (by fun_prop)
    · intro y hy
      exact (hasDerivAt_sin_sub_mul_cos y).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [(hasDerivAt_sin_sub_mul_cos y).deriv]
      have hy' : y ∈ Icc 0 Real.pi := interior_subset hy
      have hs := Real.sin_nonneg_of_nonneg_of_le_pi hy'.1 hy'.2
      exact mul_nonneg hy'.1 hs
  simpa using hm (by simp [Real.pi_pos.le]) ⟨hx,hpi⟩ hx

lemma sin_cubic_cot_bound {x : ℝ} (hx : 0 ≤ x) (hpi : x ≤ Real.pi) :
    x * Real.cos x ≤ (1-x^2/3) * Real.sin x := by
  have hm : MonotoneOn (fun y : ℝ => (1-y^2/3)*Real.sin y-y*Real.cos y)
      (Icc 0 Real.pi) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _) (by fun_prop)
    · intro y hy
      exact (hasDerivAt_sin_cubic y).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [(hasDerivAt_sin_cubic y).deriv]
      have hy' : y ∈ Icc 0 Real.pi := interior_subset hy
      exact div_nonneg (mul_nonneg hy'.1 (sin_sub_mul_cos_nonneg hy'.1 hy'.2)) (by norm_num)
  have H := hm (by simp [Real.pi_pos.le]) ⟨hx,hpi⟩ hx
  simp only [sub_zero, zero_pow (by norm_num : 2 ≠ 0), zero_div, Real.sin_zero,
    Real.cos_zero, zero_mul, mul_zero] at H
  linarith

lemma mul_cosh_sub_sinh_nonneg {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ x * Real.cosh x - Real.sinh x := by
  have hm : MonotoneOn (fun y : ℝ => y*Real.cosh y-Real.sinh y) (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici _) (by fun_prop)
    · intro y hy
      exact (hasDerivAt_mul_cosh_sub_sinh y).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [(hasDerivAt_mul_cosh_sub_sinh y).deriv]
      have hy' : 0 ≤ y := interior_subset hy
      exact mul_nonneg hy' (Real.sinh_nonneg_iff.mpr hy')
  simpa using hm (by simp) hx hx

lemma sinh_cubic_coth_bound {x : ℝ} (hx : 0 ≤ x) :
    x * Real.cosh x ≤ (1+x^2/3)*Real.sinh x := by
  have hm : MonotoneOn (fun y : ℝ => (1+y^2/3)*Real.sinh y-y*Real.cosh y) (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici _) (by fun_prop)
    · intro y hy
      exact (hasDerivAt_sinh_cubic y).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [(hasDerivAt_sinh_cubic y).deriv]
      have hy' : 0 ≤ y := interior_subset hy
      exact div_nonneg (mul_nonneg hy' (mul_cosh_sub_sinh_nonneg hy')) (by norm_num)
  have H := hm (by simp) hx hx
  simp only [zero_pow (by norm_num : 2 ≠ 0), zero_div, Real.sinh_zero,
    Real.cosh_zero, zero_mul, mul_zero, sub_zero, add_zero] at H
  linarith

lemma antitone_log_sin_correction :
    AntitoneOn (fun x : ℝ => Real.log (Real.sin x)-Real.log x+x^2/6) (Ioo 0 Real.pi) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ioo _ _) ?_ ?_ ?_
  · intro x hx
    exact (hasDerivAt_log_sin_correction hx.1 hx.2).continuousAt.continuousWithinAt
  · intro x hx
    have hx' : x ∈ Ioo 0 Real.pi := interior_subset hx
    exact (hasDerivAt_log_sin_correction hx'.1 hx'.2).differentiableAt.differentiableWithinAt
  · intro x hx
    have hx' : x ∈ Ioo 0 Real.pi := interior_subset hx
    have hs := Real.sin_pos_of_pos_of_lt_pi hx'.1 hx'.2
    rw [(hasDerivAt_log_sin_correction hx'.1 hx'.2).deriv]
    have hc := sin_cubic_cot_bound hx'.1.le hx'.2.le
    have hp := mul_pos hx'.1 hs
    apply (mul_le_mul_iff_of_pos_right hp).mp
    rw [zero_mul]
    calc
      _ = x * Real.cos x - Real.sin x + x^2 * Real.sin x / 3 := by
        field_simp [hx'.1.ne', hs.ne']
      _ ≤ 0 := by nlinarith

lemma antitone_log_sinh_correction :
    AntitoneOn (fun x : ℝ => Real.log (Real.sinh x)-Real.log x-x^2/6) (Ioi 0) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ioi _) ?_ ?_ ?_
  · intro x hx
    exact (hasDerivAt_log_sinh_correction hx).continuousAt.continuousWithinAt
  · intro x hx
    have hx' : 0 < x := interior_subset hx
    exact (hasDerivAt_log_sinh_correction hx').differentiableAt.differentiableWithinAt
  · intro x hx
    have hx' : 0 < x := interior_subset hx
    have hs := Real.sinh_pos_iff.mpr hx'
    rw [(hasDerivAt_log_sinh_correction hx').deriv]
    have hc := sinh_cubic_coth_bound hx'.le
    have hp := mul_pos hx' hs
    apply (mul_le_mul_iff_of_pos_right hp).mp
    field_simp [hx'.ne', hs.ne']
    nlinarith

lemma sin_ratio_exp_lower {t x : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (hx : 0 < x) (hpi : x < Real.pi) :
    t*Real.exp ((1-t^2)*x^2/6) ≤ Real.sin (t*x)/Real.sin x := by
  have htx := mul_pos ht hx
  have htxl : t*x ≤ x := by nlinarith
  have hs := Real.sin_pos_of_pos_of_lt_pi hx hpi
  have hst := Real.sin_pos_of_pos_of_lt_pi htx (htxl.trans_lt hpi)
  have H := antitone_log_sin_correction ⟨htx,htxl.trans_lt hpi⟩ ⟨hx,hpi⟩ htxl
  dsimp only at H
  rw [Real.log_mul ht.ne' hx.ne'] at H
  have H' : Real.log t + ((1-t^2)*x^2/6) ≤ Real.log (Real.sin (t*x))-Real.log (Real.sin x) := by
    nlinarith
  rw [← Real.log_div hst.ne' hs.ne'] at H'
  have HH := Real.exp_le_exp.mpr H'
  simpa only [Real.exp_add,Real.exp_log ht,Real.exp_log (div_pos hst hs)] using HH

lemma sinh_ratio_exp_lower {t x : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (hx : 0 < x) :
    t*Real.exp (-((1-t^2)*x^2/6)) ≤ Real.sinh (t*x)/Real.sinh x := by
  have htx := mul_pos ht hx
  have htxl : t*x ≤ x := by nlinarith
  have hs := Real.sinh_pos_iff.mpr hx
  have hst := Real.sinh_pos_iff.mpr htx
  have H := antitone_log_sinh_correction htx hx htxl
  dsimp only at H
  rw [Real.log_mul ht.ne' hx.ne'] at H
  have H' : Real.log t - ((1-t^2)*x^2/6) ≤ Real.log (Real.sinh (t*x))-Real.log (Real.sinh x) := by
    nlinarith
  rw [← Real.log_div hst.ne' hs.ne'] at H'
  have HH := Real.exp_le_exp.mpr H'
  simpa only [sub_eq_add_neg,Real.exp_add,Real.exp_log ht,Real.exp_log (div_pos hst hs)] using HH
end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_CappedExcess
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
namespace WeakHessian
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

def cappedExcess (ν : Measure X) (μ : ProbabilityMeasure X) : ℝ≥0∞ :=
  ⨆ f : X →ᵇ ℝ, ⨆ (_ : ∀ x, 0 ≤ f x ∧ f x ≤ 1),
    ENNReal.ofReal ((∫ x, f x ∂(μ : Measure X)) - ∫ x, f x ∂ν)

lemma cappedExcess_lowerSemicontinuous (ν : Measure X) :
    LowerSemicontinuous (cappedExcess ν) := by
  apply lowerSemicontinuous_iSup
  intro f
  apply lowerSemicontinuous_iSup
  intro _
  exact (ENNReal.continuous_ofReal.comp
    ((ProbabilityMeasure.continuous_integral_boundedContinuousFunction f).sub
      continuous_const)).lowerSemicontinuous

omit [BorelSpace X] in
lemma cappedExcess_query_le (ν : Measure X) (μ : ProbabilityMeasure X)
    (f : X →ᵇ ℝ) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) :
    ENNReal.ofReal ((∫ x, f x ∂(μ : Measure X)) - ∫ x, f x ∂ν) ≤ cappedExcess ν μ :=
  le_iSup_of_le f (le_iSup_of_le hf le_rfl)

lemma cappedExcess_le_one (ν : Measure X) (μ : ProbabilityMeasure X) :
    cappedExcess ν μ ≤ 1 := by
  apply iSup_le
  intro f
  apply iSup_le
  intro hf
  have hμ : (∫ x, f x ∂(μ : Measure X)) ≤ 1 := by
    calc
      _ ≤ ∫ _ : X, (1:ℝ) ∂(μ : Measure X) :=
        integral_mono (f.integrable _) (integrable_const _) (fun x => (hf x).2)
      _ = 1 := by simp
  have hν : 0 ≤ ∫ x, f x ∂ν := integral_nonneg (fun x => (hf x).1)
  exact (ENNReal.ofReal_le_ofReal (by linarith :
    (∫ x, f x ∂(μ : Measure X)) - ∫ x, f x ∂ν ≤ 1)).trans_eq (by simp)

lemma cappedExcess_closed_query_le (ν : Measure X) [IsFiniteMeasure ν]
    (μ : ProbabilityMeasure X) {A : Set X} (hA : IsClosed A) :
    ENNReal.ofReal (((μ : Measure X) A).toReal - (ν A).toReal) ≤ cappedExcess ν μ := by
  let f : ℕ → X →ᵇ ℝ := fun n =>
    BoundedContinuousFunction.comp NNReal.toReal NNReal.isometry_coe.lipschitz (hA.apprSeq n)
  have hf (n : ℕ) (x : X) : 0 ≤ f n x ∧ f n x ≤ 1 := by
    change 0 ≤ ((hA.apprSeq n x : ℝ≥0) : ℝ) ∧ ((hA.apprSeq n x : ℝ≥0) : ℝ) ≤ 1
    exact ⟨NNReal.coe_nonneg _, by exact_mod_cast HasOuterApproxClosed.apprSeq_apply_le_one hA n x⟩
  have ht (η : Measure X) [IsFiniteMeasure η] :
      Tendsto (fun n => ∫ x, f n x ∂η) atTop (𝓝 ((η A).toReal)) := by
    have H := (ENNReal.tendsto_toReal (measure_ne_top η A)).comp
      (HasOuterApproxClosed.tendsto_lintegral_apprSeq hA η)
    change Tendsto (fun n => (∫⁻ x, (hA.apprSeq n x : ℝ≥0∞) ∂η).toReal) _ _ at H
    simpa only [BoundedContinuousFunction.toReal_lintegral_coe_eq_integral, f, BoundedContinuousFunction.comp_apply] using H
  apply le_of_tendsto (ENNReal.continuous_ofReal.continuousAt.tendsto.comp ((ht (μ:Measure X)).sub (ht ν)))
  exact Eventually.of_forall (fun n => cappedExcess_query_le ν μ (f n) (hf n))

lemma cappedExcess_eq_zero_iff (ν : Measure X) [IsFiniteMeasure ν] (μ : ProbabilityMeasure X) :
    cappedExcess ν μ = 0 ↔ (μ : Measure X) ≤ ν := by
  constructor
  · intro he
    have hcl {A : Set X} (hA : IsClosed A) : (μ : Measure X) A ≤ ν A := by
      have h := cappedExcess_closed_query_le ν μ hA
      rw [he,nonpos_iff_eq_zero,ENNReal.ofReal_eq_zero] at h
      exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mp (sub_nonpos.mp h)
    apply Measure.le_iff.mpr
    intro A hA
    rw [hA.measure_eq_iSup_isClosed_of_ne_top (measure_ne_top (μ:Measure X) A)]
    apply iSup_le
    intro B
    apply iSup_le
    intro hB
    apply iSup_le
    intro hBc
    exact (hcl hBc).trans (measure_mono hB)
  · intro h
    apply le_antisymm _ bot_le
    apply iSup_le
    intro f
    apply iSup_le
    intro hf
    exact ENNReal.ofReal_eq_zero.mpr (sub_nonpos.mpr
      (integral_mono_measure h (Eventually.of_forall fun x => (hf x).1) (f.integrable ν))) |>.le

lemma exists_cappedExcess_minimizer (ν : Measure X) {S : Set (ProbabilityMeasure X)}
    (hne : S.Nonempty) (hc : IsCompact S) :
    ∃ μ ∈ S, ∀ ρ ∈ S, cappedExcess ν μ ≤ cappedExcess ν ρ := by
  simpa only [isMinOn_iff] using
    (cappedExcess_lowerSemicontinuous ν).lowerSemicontinuousOn S |>.exists_isMinOn hne hc

lemma measure_le_add_cappedExcess (ν : Measure X) [IsFiniteMeasure ν]
    (μ : ProbabilityMeasure X) {A : Set X} (hA : MeasurableSet A) :
    (μ : Measure X) A ≤ ν A + cappedExcess ν μ := by
  have hcl {B : Set X} (hB : IsClosed B) :
      (μ : Measure X) B ≤ ν B + cappedExcess ν μ := by
    have H := cappedExcess_closed_query_le ν μ hB
    rw [ENNReal.ofReal_sub _ ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal (measure_ne_top _ _),
      ENNReal.ofReal_toReal (measure_ne_top _ _)] at H
    exact (tsub_le_iff_right.mp H).trans_eq (add_comm _ _)
  rw [hA.measure_eq_iSup_isClosed_of_ne_top (measure_ne_top (μ:Measure X) A)]
  exact iSup_le fun B => iSup_le fun hB => iSup_le fun hBc =>
    (hcl hBc).trans (add_le_add (measure_mono hB) le_rfl)

omit [MetricSpace X] [BorelSpace X] in
lemma measure_le_sub_add (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    μ ≤ (μ - ν) + ν := by
  obtain ⟨S,hS⟩ := exists_isHahnDecomposition μ ν
  have hh : μ.restrict Sᶜ = (μ-ν).restrict Sᶜ + ν.restrict Sᶜ := by
    rw [Measure.restrict_sub_eq_restrict_sub_restrict hS.measurableSet.compl]
    exact (Measure.sub_add_cancel_of_le hS.ge_on_compl).symm
  calc
    μ = μ.restrict S + μ.restrict Sᶜ := (Measure.restrict_add_restrict_compl hS.measurableSet).symm
    _ ≤ ν.restrict S + ((μ-ν).restrict Sᶜ + ν.restrict Sᶜ) := by
      rw [hh]
      exact add_le_add hS.le_on le_rfl
    _ = (μ-ν).restrict Sᶜ + (ν.restrict S + ν.restrict Sᶜ) := by abel
    _ = (μ-ν).restrict Sᶜ + ν := by rw [Measure.restrict_add_restrict_compl hS.measurableSet]
    _ ≤ (μ-ν)+ν := add_le_add Measure.restrict_le_self le_rfl

omit [MetricSpace X] [BorelSpace X] in
lemma positivePart_total_of_hahn (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {S : Set X} (hS : IsHahnDecomposition μ ν S) :
    (μ-ν) univ = μ Sᶜ - ν Sᶜ := by
  calc
    (μ-ν) univ = (μ-ν) Sᶜ := by
      rw [← measure_add_measure_compl hS.measurableSet,
        Measure.sub_apply_eq_zero_of_isHahnDecomposition hS,zero_add]
    _ = ((μ-ν).restrict Sᶜ) univ := by simp
    _ = (μ.restrict Sᶜ - ν.restrict Sᶜ) univ := by
      rw [Measure.restrict_sub_eq_restrict_sub_restrict hS.measurableSet.compl]
    _ = μ Sᶜ - ν Sᶜ := by
      rw [Measure.sub_apply MeasurableSet.univ hS.ge_on_compl]
      simp

lemma cappedExcess_eq_positivePart (ν : Measure X) [IsFiniteMeasure ν]
    (μ : ProbabilityMeasure X) : cappedExcess ν μ = ((μ:Measure X)-ν) univ := by
  let δ := (μ:Measure X)-ν
  let : IsFiniteMeasure δ := isFiniteMeasure_of_le (μ:Measure X) Measure.sub_le
  apply le_antisymm
  · apply iSup_le
    intro f
    apply iSup_le
    intro hf
    have H := integral_mono_measure (measure_le_sub_add (μ:Measure X) ν)
      (Eventually.of_forall fun x => (hf x).1) (f.integrable (δ+ν))
    rw [integral_add_measure (f.integrable δ) (f.integrable ν)] at H
    have Hb : (∫ x, f x ∂δ) ≤ (δ univ).toReal := by
      calc
        _ ≤ ∫ _ : X, (1:ℝ) ∂δ := integral_mono (f.integrable δ)
          (integrable_const _) (fun x => (hf x).2)
        _ = _ := by simp [Measure.real]
    calc
      _ ≤ ENNReal.ofReal ((δ univ).toReal) :=
        ENNReal.ofReal_le_ofReal (by linarith)
      _ = _ := ENNReal.ofReal_toReal (measure_ne_top δ univ)
  · obtain ⟨S,hS⟩ := exists_isHahnDecomposition (μ:Measure X) ν
    rw [positivePart_total_of_hahn _ _ hS]
    exact tsub_le_iff_right.mpr (by
      simpa only [add_comm] using measure_le_add_cappedExcess ν μ hS.measurableSet.compl)

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Measure_MeasurePositiveNegativeBalance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
namespace WeakHessian
open MeasureTheory Set
open scoped ENNReal NNReal

variable {X : Type*} [MeasurableSpace X]

lemma measure_positive_negative_balance (μ ν : Measure X)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] : μ + (ν-μ) = ν + (μ-ν) := by
  let : IsFiniteMeasure (μ-ν) := isFiniteMeasure_of_le μ Measure.sub_le
  let : IsFiniteMeasure (ν-μ) := isFiniteMeasure_of_le ν Measure.sub_le
  apply Measure.toSignedMeasure_eq_toSignedMeasure_iff.mp
  rw [Measure.toSignedMeasure_add,Measure.toSignedMeasure_add]
  have H := Measure.sub_toSignedMeasure_eq_toSignedMeasure_sub (μ := μ) (ν := ν)
  have hh := sub_eq_sub_iff_add_eq_add.mp H
  simpa only [add_comm] using hh

lemma measure_add_left_cancel_finite (μ : Measure X) [IsFiniteMeasure μ]
    {ν ρ : Measure X} (h : μ+ν=μ+ρ) : ν=ρ :=
  le_antisymm (Measure.le_of_add_le_add_left h.le) (Measure.le_of_add_le_add_left h.ge)

variable [MetricSpace X] [BorelSpace X]

omit [MetricSpace X] [BorelSpace X] in
lemma excess_relocation_complementarity (μ ν ρ β : Measure X)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure β]
    (hρ : ρ ≤ μ-ν) (hmass : β univ = ρ univ)
    (hmin : (μ-ν) univ ≤ ((μ-ρ+β)-ν) univ) :
    ((μ-ρ+β)-ν) = (μ-ν)-ρ+β ∧
      (ν-(μ-ρ+β)) = ν-μ ∧ β.MutuallySingular (ν-μ) := by
  let δ := μ-ν
  let η := μ-ρ+β
  let : IsFiniteMeasure δ := isFiniteMeasure_of_le μ Measure.sub_le
  let : IsFiniteMeasure ρ := isFiniteMeasure_of_le δ hρ
  let : IsFiniteMeasure (μ-ρ) := isFiniteMeasure_of_le μ Measure.sub_le
  let : IsFiniteMeasure η := inferInstanceAs (IsFiniteMeasure (μ-ρ+β))
  let : IsFiniteMeasure (δ-ρ) := isFiniteMeasure_of_le δ Measure.sub_le
  let : IsFiniteMeasure (η-ν) := isFiniteMeasure_of_le η Measure.sub_le
  let : IsFiniteMeasure (ν-η) := isFiniteMeasure_of_le ν Measure.sub_le
  let : IsFiniteMeasure (ν-μ) := isFiniteMeasure_of_le ν Measure.sub_le
  have hρμ : ρ ≤ μ := hρ.trans Measure.sub_le
  have hμr : ρ+(μ-ρ) = μ := by rw [add_comm,Measure.sub_add_cancel_of_le hρμ]
  have hδr : ρ+(δ-ρ) = δ := by rw [add_comm,Measure.sub_add_cancel_of_le hρ]
  have hu : η-ν ≤ δ-ρ+β := by
    apply Measure.sub_le_of_le_add
    apply Measure.le_of_add_le_add_left (μ := ρ)
    calc
      ρ+η = μ+β := by dsimp [η]; rw [← add_assoc,hμr]
      _ ≤ (δ+ν)+β := add_le_add (measure_le_sub_add μ ν) le_rfl
      _ = (ρ+(δ-ρ)+ν)+β := congrArg (fun ζ : Measure X => (ζ+ν)+β) hδr.symm
      _ = ρ+(δ-ρ+β+ν) := by ac_rfl
  have htu : (δ-ρ+β) univ = δ univ := by
    rw [Measure.add_apply,Measure.sub_apply MeasurableSet.univ hρ,hmass]
    exact tsub_add_cancel_of_le (hρ univ)
  have hδ : η-ν = δ-ρ+β := by
    apply Measure.eq_of_le_of_measure_univ_eq hu
    apply le_antisymm (hu univ)
    rw [htu]
    exact hmin
  have hb := measure_positive_negative_balance η ν
  have hκ : ν-η = ν-μ := by
    apply measure_add_left_cancel_finite (μ+β)
    calc
      (μ+β)+(ν-η) = ρ+(η+(ν-η)) := by
        change (μ+β)+(ν-η) = ρ+((μ-ρ+β)+(ν-η))
        rw [← add_assoc ρ (μ-ρ+β) (ν-η),← add_assoc ρ (μ-ρ) β,hμr]
      _ = ρ+(ν+(η-ν)) := congrArg (fun ζ : Measure X => ρ+ζ) hb
      _ = (ρ+(δ-ρ)+ν)+β := by rw [hδ]; ac_rfl
      _ = (δ+ν)+β := by rw [hδr]
      _ = (μ+β)+(ν-μ) := by
        have HB := measure_positive_negative_balance μ ν
        change (μ-ν+ν)+β = _
        rw [add_comm (μ-ν) ν,← HB]
        ac_rfl
  refine ⟨hδ,hκ,?_⟩
  have hs : (η-ν).MutuallySingular (ν-η) := Measure.mutually_singular_measure_sub
  rw [hκ] at hs
  apply hs.mono _ le_rfl
  rw [hδ]
  exact Measure.le_add_left le_rfl

end WeakHessian
end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_HeatFlow_StrictSurplusCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
namespace WeakHessian

section CarrierBounds
open MeasureTheory Set
open scoped ENNReal NNReal

variable {X : Type*} [MeasurableSpace X]

lemma exists_ac_full_carrier (ν δ : Measure X) [IsFiniteMeasure ν] [IsFiniteMeasure δ] :
    ∃ P : Set X, MeasurableSet P ∧ δ Pᶜ = 0 ∧ ν.restrict P ≪ δ := by
  obtain ⟨P,hP,hsp,hδ⟩ := Measure.mutuallySingular_singularPart ν δ
  refine ⟨P,hP,hδ,?_⟩
  have he : ν.restrict P = (δ.withDensity (ν.rnDeriv δ)).restrict P := by
    conv_lhs => rw [Measure.haveLebesgueDecomposition_add ν δ]
    rw [Measure.restrict_add,Measure.restrict_eq_zero.mpr hsp,zero_add]
  rw [he]
  exact (Measure.absolutelyContinuous_of_le Measure.restrict_le_self).trans
    (withDensity_absolutelyContinuous δ (ν.rnDeriv δ))

structure StrictSurplusCarrier (μ ν : Measure X) (P : Set X) : Prop where
  measurableSet : MeasurableSet P
  surplus_compl : (μ-ν) Pᶜ = 0
  reference_ac : ν.restrict P ≪ μ-ν
  deficit_zero : (ν-μ) P = 0

lemma exists_strictSurplusCarrier (μ ν : Measure X)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] : ∃ P : Set X, StrictSurplusCarrier μ ν P := by
  let : IsFiniteMeasure (μ-ν) := isFiniteMeasure_of_le μ Measure.sub_le
  obtain ⟨S,hS,hδ,hν⟩ := exists_ac_full_carrier ν (μ-ν)
  obtain ⟨T,hT,hTδ,hTκ⟩ := (Measure.mutually_singular_measure_sub (μ := μ) (ν := ν))
  refine ⟨S ∩ Tᶜ,⟨hS.inter hT.compl,?_,?_,?_⟩⟩
  · rw [compl_inter,compl_compl]
    apply measure_union_null hδ hTδ
  · exact (Measure.absolutelyContinuous_of_le (Measure.restrict_mono_set ν inter_subset_left)).trans hν
  · exact measure_mono_null inter_subset_right hTκ

variable [MetricSpace X] [BorelSpace X]

omit [MetricSpace X] [BorelSpace X] in
lemma StrictSurplusCarrier.mass_ac {μ ν : Measure X} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {P : Set X} (hP : StrictSurplusCarrier μ ν P) : μ.restrict P ≪ μ-ν := by
  have h := Measure.restrict_mono_measure (measure_le_sub_add μ ν) P
  rw [Measure.restrict_add] at h
  exact (Measure.absolutelyContinuous_of_le h).trans
    ((Measure.absolutelyContinuous_of_le Measure.restrict_le_self).add_left hP.reference_ac)

omit [MetricSpace X] [BorelSpace X] in
lemma StrictSurplusCarrier.surplus_le_mass {μ ν : Measure X}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {P : Set X} (hP : StrictSurplusCarrier μ ν P) :
    (μ-ν) univ ≤ μ P := by
  have H := Measure.sub_le (μ := μ) (ν := ν) P
  rw [← measure_add_measure_compl hP.measurableSet,hP.surplus_compl,add_zero]
  exact H

omit [MetricSpace X] [BorelSpace X] in
lemma StrictSurplusCarrier.maximal_reference_volume {μ ν : Measure X}
    {P : Set X} (hP : StrictSurplusCarrier μ ν P)
    {A : Set X} (hA : MeasurableSet A) (hνA : ν.restrict A ≪ μ-ν) : ν A ≤ ν P := by
  have hzero : ν (A ∩ Pᶜ) = 0 := by
    have hh := hνA hP.surplus_compl
    rw [Measure.restrict_apply hP.measurableSet.compl,inter_comm] at hh
    exact hh
  calc
    ν A = ν (A ∩ P) + ν (A ∩ Pᶜ) := by
      rw [← measure_union (disjoint_left.mpr (by aesop)) (hA.inter hP.measurableSet.compl)]
      congr 1
      ext x
      simp only [mem_union,mem_inter_iff,mem_compl_iff]
      tauto
    _ ≤ ν P := by rw [hzero,add_zero]; exact measure_mono inter_subset_right

end CarrierBounds
open MeasureTheory Set
open scoped ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

omit [MetricSpace X] [BorelSpace X] in
lemma StrictSurplusCarrier.exact_mass {μ ν : Measure X}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {P : Set X}
    (hP : StrictSurplusCarrier μ ν P) : μ P = ν P + (μ-ν) univ := by
  have H := congrArg (fun η : Measure X => η P) (measure_positive_negative_balance μ ν)
  simp only [Measure.add_apply,hP.deficit_zero,add_zero] at H
  rw [← measure_add_measure_compl hP.measurableSet,hP.surplus_compl,add_zero]
  exact H

omit [MetricSpace X] [BorelSpace X] in
lemma excess_relocation_carrier_growth (μ ν ρ β : Measure X)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure β]
    {P : Set X} (_hP : StrictSurplusCarrier μ ν P)
    (hρ : ρ ≤ μ-ν) (hmass : β univ = ρ univ)
    (hmin : (μ-ν) univ ≤ ((μ-ρ+β)-ν) univ)
    (hspread : ∀ B : Set X, MeasurableSet B → β Bᶜ = 0 →
      ν P + (μ-ν) univ ≤ ν B) :
    ∃ Q : Set X, StrictSurplusCarrier (μ-ρ+β) ν Q ∧
      ν P + (μ-ν) univ ≤ ν Q := by
  let : IsFiniteMeasure (μ-ρ) := isFiniteMeasure_of_le μ Measure.sub_le
  obtain ⟨hδ,_,_⟩ := excess_relocation_complementarity μ ν ρ β hρ hmass hmin
  obtain ⟨B,hB,hβB,hνB⟩ := exists_ac_full_carrier ν β
  obtain ⟨Q,hQ⟩ := exists_strictSurplusCarrier (μ-ρ+β) ν
  refine ⟨Q,hQ,(hspread B hB hβB).trans (hQ.maximal_reference_volume hB ?_)⟩
  apply hνB.trans
  apply Measure.absolutelyContinuous_of_le
  rw [hδ]
  exact Measure.le_add_left le_rfl

end WeakHessian
end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Calculus_DominatedCompactRerouting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
namespace WeakHessian
open MeasureTheory Set
open scoped ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

lemma exists_dominated_of_compact_rerouting (ν : Measure X) [IsFiniteMeasure ν]
    {S : Set (ProbabilityMeasure X)} (hne : S.Nonempty) (hc : IsCompact S)
    (hr : ∀ μ ∈ S, ∀ P : Set X, StrictSurplusCarrier (μ:Measure X) ν P →
      0 < ((μ:Measure X)-ν) univ →
      ∃ (ρ β : Measure X) (η : ProbabilityMeasure X), IsFiniteMeasure β ∧
        ρ ≤ (μ:Measure X)-ν ∧ β univ = ρ univ ∧ η ∈ S ∧
        (η:Measure X) = (μ:Measure X)-ρ+β ∧
        ∀ B : Set X, MeasurableSet B → β Bᶜ = 0 →
          ν P + ((μ:Measure X)-ν) univ ≤ ν B) :
    ∃ μ ∈ S, (μ:Measure X) ≤ ν := by
  obtain ⟨μ₀,hμ₀,hmin⟩ := exists_cappedExcess_minimizer ν hne hc
  suffices hzero : cappedExcess ν μ₀ = 0 from ⟨μ₀,hμ₀,(cappedExcess_eq_zero_iff ν μ₀).mp hzero⟩
  by_contra hz
  let e := cappedExcess ν μ₀
  have he0 : 0 < e := bot_lt_iff_ne_bot.mpr hz
  have het : e ≠ ∞ := ne_top_of_le_ne_top (by simp) (cappedExcess_le_one ν μ₀)
  have he : 0 < e.toReal := ENNReal.toReal_pos he0.ne' het
  let T : Set ℝ := {a | ∃ μ ∈ S, cappedExcess ν μ = e ∧
    ∃ P : Set X, StrictSurplusCarrier (μ:Measure X) ν P ∧ a = (ν P).toReal}
  have hTne : T.Nonempty := by
    obtain ⟨P,hP⟩ := exists_strictSurplusCarrier (μ₀:Measure X) ν
    exact ⟨(ν P).toReal,μ₀,hμ₀,rfl,P,hP,rfl⟩
  have hTb : BddAbove T := by
    refine ⟨(ν univ).toReal,?_⟩
    rintro a ⟨μ,hμ,heq,P,hP,rfl⟩
    exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (subset_univ _))
  obtain ⟨a,ha,halt⟩ := exists_lt_of_lt_csSup hTne
    (show sSup T-e.toReal < sSup T by linarith)
  obtain ⟨μ,hμ,hμe,P,hP,rfl⟩ := ha
  have hμδ : ((μ:Measure X)-ν) univ = e := by
    rw [← cappedExcess_eq_positivePart]
    exact hμe
  obtain ⟨ρ,β,η,hβ,hρ,hmass,hη,hηeq,hspread⟩ := hr μ hμ P hP (by rw [hμδ]; exact he0)
  let := hβ
  let : IsFiniteMeasure ρ := isFiniteMeasure_of_le (μ:Measure X) (hρ.trans Measure.sub_le)
  have hmin' : ((μ:Measure X)-ν) univ ≤ (((μ:Measure X)-ρ+β)-ν) univ := by
    rw [← hηeq,← cappedExcess_eq_positivePart,← cappedExcess_eq_positivePart,hμe]
    exact hmin η hη
  obtain ⟨Q,hQ,hgrowth⟩ := excess_relocation_carrier_growth
    (μ:Measure X) ν ρ β hP hρ hmass hmin' hspread
  obtain ⟨hδ,_,_⟩ := excess_relocation_complementarity
    (μ:Measure X) ν ρ β hρ hmass hmin'
  have hηe : cappedExcess ν η = e := by
    rw [cappedExcess_eq_positivePart,hηeq,hδ,Measure.add_apply,
      Measure.sub_apply MeasurableSet.univ hρ,hmass,
      tsub_add_cancel_of_le (hρ univ),hμδ]
  have hQ' : StrictSurplusCarrier (η:Measure X) ν Q := hηeq.symm ▸ hQ
  have hQmem : (ν Q).toReal ∈ T := ⟨η,hη,hηe,Q,hQ',rfl⟩
  have hQsup : (ν Q).toReal ≤ sSup T := le_csSup hTb hQmem
  rw [hμδ] at hgrowth
  have hreal := ENNReal.toReal_mono (measure_ne_top ν Q) hgrowth
  rw [ENNReal.toReal_add (measure_ne_top ν P) het] at hreal
  linarith

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_JoinCurve
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped Topology ENNReal NNReal
open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace
open scoped BoundedContinuousFunction

namespace WeakHessian
variable {X : Type*} [MetricSpace X]

def joinCurve (γ η : Curve X) (h : γ timeOne = η timeZero) : Curve X :=
  ((Path.mk γ rfl rfl).trans (Path.mk η h.symm rfl)).toContinuousMap

lemma joinCurve_apply_left (γ η : Curve X) (h : γ timeOne = η timeZero)
    (t : Time) (ht : (t:ℝ) ≤ 1/2) :
    joinCurve γ η h t = evalReal γ (2*(t:ℝ)) := by
  simp only [joinCurve, Path.coe_toContinuousMap, Path.trans_apply, dite_eq_left ht,
    Path.coe_mk', evalReal]
  congr 1
  apply Subtype.ext
  simp only [clampTime]
  rw [min_eq_right (by linarith), max_eq_right (by have := t.2.1; linarith)]

lemma joinCurve_apply_right (γ η : Curve X) (h : γ timeOne = η timeZero)
    (t : Time) (ht : 1/2 ≤ (t:ℝ)) :
    joinCurve γ η h t = evalReal η (2*(t:ℝ)-1) := by
  rcases ht.eq_or_lt with heq | ht
  · rw [joinCurve_apply_left γ η h t (by linarith)]
    have he : (t:ℝ) = 1/2 := heq.symm
    simp only [he]
    norm_num [evalReal, clampTime]
    exact h
  · simp only [joinCurve, Path.coe_toContinuousMap, Path.trans_apply, dite_eq_right (not_le.mpr ht),
      Path.coe_mk', evalReal]
    change η _ = η _
    congr 1
    apply Subtype.ext
    simp only [clampTime]
    rw [min_eq_right (by have := t.2.2; linarith), max_eq_right (by linarith)]

lemma joinCurve_zero (γ η : Curve X) (h : γ timeOne = η timeZero) :
    joinCurve γ η h timeZero = γ timeZero := by
  rw [joinCurve_apply_left γ η h _ (by norm_num [timeZero])]
  simp only [evalReal, timeZero, clampTime]
  congr 1
  apply Subtype.ext
  norm_num

lemma joinCurve_one (γ η : Curve X) (h : γ timeOne = η timeZero) :
    joinCurve γ η h timeOne = η timeOne := by
  rw [joinCurve_apply_right γ η h _ (by norm_num [timeOne])]
  simp only [evalReal, timeOne, clampTime]
  congr 1
  apply Subtype.ext
  norm_num

abbrev Joinable (X : Type*) [MetricSpace X] :=
  {p : Curve X × Curve X | p.1 timeOne = p.2 timeZero}

def joinMap (p : Joinable X) : Curve X := joinCurve p.1.1 p.1.2 p.2

lemma isClosed_joinable : IsClosed {p : Curve X × Curve X | p.1 timeOne = p.2 timeZero} :=
  isClosed_eq ((continuous_eval_const timeOne).comp continuous_fst)
    ((continuous_eval_const timeZero).comp continuous_snd)

lemma lipschitz_joinMap : LipschitzWith 1 (joinMap (X := X)) := by
  apply LipschitzWith.of_dist_le_mul
  intro p q
  simp only [NNReal.coe_one, one_mul]
  apply (ContinuousMap.dist_le dist_nonneg).mpr
  intro t
  rcases le_total (t:ℝ) (1/2) with ht | ht
  · rw [joinMap, joinMap, joinCurve_apply_left _ _ _ t ht, joinCurve_apply_left _ _ _ t ht]
    exact (ContinuousMap.dist_apply_le_dist _).trans (le_max_left _ _)
  · rw [joinMap, joinMap, joinCurve_apply_right _ _ _ t ht, joinCurve_apply_right _ _ _ t ht]
    exact (ContinuousMap.dist_apply_le_dist _).trans (le_max_right _ _)

lemma hasControlBound_of_squareControl {γ : Curve X} {a : ℝ → ℝ}
    (ha : IsSquareControl γ a) :
    HasControlBound γ (Real.sqrt (∫ r in Icc (0:ℝ) 1, (a r)^2)) := by
  let u := ha.2.1.toLp a
  have hueq : u =ᵐ[timeMeasure] a := MemLp.coeFn_toLp ha.2.1
  have hn : ‖u‖^2 = ∫ r in Icc (0:ℝ) 1, (a r)^2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hueq] with r hr
    simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs, hr]
  refine ⟨u, ?_, fun s t hst => ?_⟩
  · rw [← hn, Real.sqrt_sq (norm_nonneg u)]
  · rw [intervalFunctional_apply s t u hst]
    have heq : (∫ r in (s:ℝ)..(t:ℝ), u r) = ∫ r in (s:ℝ)..(t:ℝ), a r := by
      apply intervalIntegral.integral_congr_ae_restrict
      rw [uIoc_of_le (show (s:ℝ) ≤ (t:ℝ) from hst)]
      exact ae_restrict_of_ae_restrict_of_subset (Ioc_subset_Icc_self.trans (Icc_subset_Icc s.2.1 t.2.2)) hueq
    rw [heq]
    exact ha.2.2.2 s t hst

end WeakHessian

open Set MeasureTheory Filter
open scoped ENNReal NNReal

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_AffineTime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
attribute [local instance] Classical.propDecidable
namespace WeakHessian
variable {X : Type*} [MetricSpace X]

def affineTime (a b u : Time) : Time :=
  ⟨(1 - (u : ℝ)) * (a : ℝ) + (u : ℝ) * (b : ℝ), by
    constructor
    · exact add_nonneg
        (mul_nonneg (sub_nonneg.mpr u.property.2) a.property.1)
        (mul_nonneg u.property.1 b.property.1)
    · have h₁ := mul_nonneg (sub_nonneg.mpr u.property.2) (sub_nonneg.mpr a.property.2)
      have h₂ := mul_nonneg u.property.1 (sub_nonneg.mpr b.property.2)
      nlinarith⟩

@[simp] theorem affineTime_zero (a b : Time) : affineTime a b timeZero = a := by
  apply Subtype.ext
  simp only [affineTime, timeZero, sub_zero, one_mul, zero_mul, add_zero]

@[simp] theorem affineTime_one (a b : Time) : affineTime a b timeOne = b := by
  apply Subtype.ext
  simp only [affineTime, timeOne, sub_self, zero_mul, one_mul, zero_add]

lemma continuous_affineTime (a b : Time) : Continuous (affineTime a b) := by
  exact (((continuous_const.sub continuous_subtype_val).mul continuous_const).add
    (continuous_subtype_val.mul continuous_const)).subtype_mk _

def restrictCurve (a b : Time) (γ : Curve X) : Curve X :=
  γ.comp ⟨affineTime a b, continuous_affineTime a b⟩

lemma continuous_restrictCurve (a b : Time) : Continuous (restrictCurve (X := X) a b) := by
  exact ContinuousMap.continuous_precomp _

@[simp] lemma restrictCurve_zero (a b : Time) (γ : Curve X) :
    restrictCurve a b γ timeZero = γ a := by simp [restrictCurve]

@[simp] lemma restrictCurve_one (a b : Time) (γ : Curve X) :
    restrictCurve a b γ timeOne = γ b := by simp [restrictCurve]

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_SpeedApprox
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
attribute [local instance] Classical.propDecidable
namespace WeakHessian
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {m : Measure X}

omit [MeasurableSpace X] [BorelSpace X] in
lemma BoundedTracks.of_plan_le_smul {π ρ : Measure (Curve X)} (hπ : BoundedTracks π)
    {C : ℝ≥0∞} (hρ : ρ ≤ C • π) : BoundedTracks ρ := by
  obtain ⟨o, R, hR, hb⟩ := hπ
  exact ⟨o, R, hR, (Measure.absolutelyContinuous_of_le_smul hρ).ae_le hb⟩

end WeakHessian

lemma continuous_ae_map_of_ae
    {A B : Type*} [TopologicalSpace A] [MeasurableSpace A] [BorelSpace A] [T2Space A]
    [TopologicalSpace B] [MeasurableSpace B] [BorelSpace B] [T2Space B]
    {μ : Measure A} [IsFiniteMeasure μ] [Measure.InnerRegularCompactLTTop μ]
    {f : A → B} (hf : Continuous f) {p : B → Prop}
    (hp : ∀ᵐ x ∂μ, p (f x)) : ∀ᵐ y ∂Measure.map f μ, p y := by
  let S := (toMeasurable μ {x | ¬p (f x)})ᶜ
  have hSm : MeasurableSet S := (measurableSet_toMeasurable _ _).compl
  have hSzero : μ Sᶜ = 0 := by
    simp only [S, compl_compl, measure_toMeasurable]
    exact ae_iff.mp hp
  have hSp : ∀ x ∈ S, p (f x) := by
    intro x hx
    by_contra hn
    exact hx (subset_toMeasurable μ {x | ¬p (f x)} hn)
  rw [ae_iff]
  apply le_antisymm _ bot_le
  apply le_of_forall_gt
  intro ε hε
  obtain ⟨K, hKS, hKc, hKsmall⟩ := hSm.exists_isCompact_sdiff_lt (measure_ne_top μ S) hε.ne'
  have hKp : {y | ¬p y} ⊆ (f '' K)ᶜ := by
    rintro y hy ⟨x, hx, rfl⟩
    exact hy (hSp x (hKS hx))
  calc
    Measure.map f μ {y | ¬p y} ≤ Measure.map f μ (f '' K)ᶜ := measure_mono hKp
    _ = μ (f ⁻¹' (f '' K)ᶜ) := Measure.map_apply hf.measurable (hKc.image hf).measurableSet.compl
    _ ≤ μ Kᶜ := measure_mono (by simpa only [preimage_compl, compl_subset_compl] using subset_preimage_image f K)
    _ ≤ μ (S \ K) + μ Sᶜ := by
      apply (measure_mono (show Kᶜ ⊆ (S \ K) ∪ Sᶜ by intro x hx; by_cases hs : x ∈ S <;> simp_all)).trans
      exact measure_union_le _ _
    _ < ε := by simpa only [hSzero, add_zero] using hKsmall

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Transport_RestrictCurve
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
attribute [local instance] Classical.propDecidable
namespace WeakHessian
variable {X : Type*} [MetricSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X]
  [MeasurableSpace X] [BorelSpace X] {m : Measure X}

omit [MeasurableSpace X] [BorelSpace X] in
lemma BoundedTracks.restrictCurve {π : Measure (Curve X)} [IsFiniteMeasure π]
    (hb : BoundedTracks π) (a b : Time) :
    BoundedTracks (Measure.map (WeakHessian.restrictCurve a b) π) := by
  obtain ⟨o, R, hR, hb⟩ := hb
  refine ⟨o, R, hR, continuous_ae_map_of_ae (continuous_restrictCurve a b) ?_⟩
  filter_upwards [hb] with γ hγ
  exact fun t => hγ (affineTime a b t)

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_EvalRealCoe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
attribute [local instance] Classical.propDecidable
namespace WeakHessian
variable {X : Type*} [MetricSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X]
  [MeasurableSpace X] [BorelSpace X] {m : Measure X}

omit [CompleteSpace X] [TopologicalSpace.SeparableSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma evalReal_coe (γ : Curve X) (t : Time) : evalReal γ (t : ℝ) = γ t := by
  apply congrArg γ
  apply Subtype.ext
  simp only [clampTime, min_eq_right t.property.2, max_eq_right t.property.1]

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Transport_KineticAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped Topology ENNReal NNReal
open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal

namespace WeakHessian
variable {X : Type*} [MetricSpace X]

def kineticAction (γ : Curve X) : ℝ≥0∞ := controlNorm γ ^ 2

end WeakHessian

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Transport_MapCompProdComap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped Topology ENNReal NNReal
open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory

namespace WeakHessianTransport
variable {A B Z : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace Z]

lemma map_compProd_comap (μ : Measure A) [SFinite μ] (κ : Kernel Z B)
    [IsSFiniteKernel κ] (f : A → Z) (hf : Measurable f) :
    (μ ⊗ₘ κ.comap f hf).map (fun p : A×B => (f p.1,p.2)) = μ.map f ⊗ₘ κ := by
  have hF : Measurable (fun p : A×B => (f p.1,p.2)) :=
    (hf.comp measurable_fst).prodMk measurable_snd
  ext s hs
  rw [Measure.map_apply hF hs,
    Measure.compProd_apply (hs.preimage hF),
    Measure.compProd_apply hs,
    lintegral_map (Kernel.measurable_kernel_prodMk_left hs) hf]
  rfl

lemma exists_fiber_gluing [StandardBorelSpace B] [Nonempty B]
    (μ : Measure A) (ν : Measure B) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : A → Z) (g : B → Z) (hf : Measurable f) (hg : Measurable g)
    (hpush : μ.map f = ν.map g) :
    ∃ q : Measure (A×B), IsProbabilityMeasure q ∧
      q.map Prod.fst = μ ∧ q.map Prod.snd = ν ∧
      q.map (fun p : A×B => (f p.1,p.2)) = ν.map (fun b => (g b,b)) := by
  let κ := condDistrib (id : B → B) g ν
  let q := μ ⊗ₘ κ.comap f hf
  have hmap : q.map (fun p : A×B => (f p.1,p.2)) = ν.map (fun b => (g b,b)) := by
    rw [map_compProd_comap μ κ f hf, hpush]
    exact compProd_map_condDistrib aemeasurable_id
  refine ⟨q, (by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)), Measure.fst_compProd μ (κ.comap f hf), ?_, hmap⟩
  have hF : Measurable (fun p : A×B => (f p.1,p.2)) :=
    (hf.comp measurable_fst).prodMk measurable_snd
  have hG : Measurable (fun b : B => (g b,b)) := hg.prodMk measurable_id
  have H := congrArg (fun r : Measure (Z×B) => r.map Prod.snd) hmap
  rw [Measure.map_map measurable_snd hF,
      Measure.map_map measurable_snd hG] at H
  simpa only [Function.comp_def, Measure.map_id'] using H

lemma exists_fiber_gluing_supported [StandardBorelSpace B] [Nonempty B]
    [StandardBorelSpace Z]
    (μ : Measure A) (ν : Measure B) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : A → Z) (g : B → Z) (hf : Measurable f) (hg : Measurable g)
    (hpush : μ.map f = ν.map g) :
    ∃ q : Measure (A×B), IsProbabilityMeasure q ∧
      q.map Prod.fst = μ ∧ q.map Prod.snd = ν ∧
      ∀ᵐ p ∂q, f p.1 = g p.2 := by
  obtain ⟨q,hqp,hq0,hq1,hq⟩ := exists_fiber_gluing μ ν f g hf hg hpush
  refine ⟨q,hqp,hq0,hq1,?_⟩
  have hfull : ∀ᵐ p ∂ν.map (fun b => (g b,b)), p.1 = g p.2 := by
    apply (ae_map_iff (hg.prodMk measurable_id).aemeasurable ?_).mpr
    · exact ae_of_all _ (fun _ => rfl)
    · exact measurableSet_eq_fun measurable_fst (hg.comp measurable_snd)
  rw [← hq] at hfull
  have hF : Measurable (fun p : A×B => (f p.1,p.2)) :=
    (hf.comp measurable_fst).prodMk measurable_snd
  exact (ae_map_iff hF.aemeasurable
    (measurableSet_eq_fun measurable_fst (hg.comp measurable_snd))).mp hfull

end WeakHessianTransport

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_HalfTime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped Topology ENNReal NNReal
open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory

namespace WeakHessian
variable {X : Type*} [MetricSpace X]

def halfTime (t : Time) : Time := ⟨(t:ℝ)/2, by constructor <;> linarith [t.2.1,t.2.2]⟩
def rightTime (t : Time) : Time := ⟨((t:ℝ)+1)/2, by constructor <;> linarith [t.2.1,t.2.2]⟩
lemma joinCurve_halfTime (γ η : Curve X) (h : γ timeOne = η timeZero) (t : Time) :
    joinCurve γ η h (halfTime t) = γ t := by
  rw [joinCurve_apply_left _ _ _ _ (by dsimp [halfTime]; have := t.2.2; linarith)]
  dsimp [halfTime]
  rw [show 2*((t:ℝ)/2) = (t:ℝ) by ring, evalReal_coe]

lemma joinCurve_rightTime (γ η : Curve X) (h : γ timeOne = η timeZero) (t : Time) :
    joinCurve γ η h (rightTime t) = η t := by
  rw [joinCurve_apply_right _ _ _ _ (by dsimp [rightTime]; have := t.2.1; linarith)]
  dsimp [rightTime]
  rw [show 2*(((t:ℝ)+1)/2)-1 = (t:ℝ) by ring, evalReal_coe]

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_DyadicTimes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped Topology ENNReal NNReal
open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory

namespace WeakHessian
lemma continuous_halfTime : Continuous halfTime :=
  (continuous_subtype_val.div_const _).subtype_mk _
lemma continuous_rightTime : Continuous rightTime :=
  ((continuous_subtype_val.add_const _).div_const _).subtype_mk _

lemma dist_halfTime (s t : Time) : dist (halfTime s) (halfTime t) = dist s t / 2 := by
  change |(s:ℝ)/2-(t:ℝ)/2| = |(s:ℝ)-(t:ℝ)|/2
  rw [← sub_div, abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2)]
lemma dist_rightTime (s t : Time) : dist (rightTime s) (rightTime t) = dist s t / 2 := by
  change |((s:ℝ)+1)/2-((t:ℝ)+1)/2| = |(s:ℝ)-(t:ℝ)|/2
  rw [← sub_div, add_sub_add_right_eq_sub, abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2)]

@[simp] lemma halfTime_zero : halfTime timeZero = timeZero := by
  apply Subtype.ext; norm_num [halfTime,timeZero]
@[simp] lemma rightTime_one : rightTime timeOne = timeOne := by
  apply Subtype.ext; norm_num [rightTime,timeOne]

def dyadicTimes : ℕ → Set Time
  | 0 => {timeZero,timeOne}
  | n+1 => halfTime '' dyadicTimes n ∪ rightTime '' dyadicTimes n

lemma zero_mem_dyadicTimes (n : ℕ) : timeZero ∈ dyadicTimes n := by
  induction n with
  | zero => simp [dyadicTimes]
  | succ n hn => exact Or.inl ⟨timeZero,hn,halfTime_zero⟩
lemma one_mem_dyadicTimes (n : ℕ) : timeOne ∈ dyadicTimes n := by
  induction n with
  | zero => simp [dyadicTimes]
  | succ n hn => exact Or.inr ⟨timeOne,hn,rightTime_one⟩

lemma monotone_dyadicTimes : Monotone dyadicTimes := by
  apply monotone_nat_of_le_succ
  intro n
  induction n with
  | zero =>
    intro t ht
    rcases ht with rfl | ht
    · exact zero_mem_dyadicTimes 1
    · have he : t = timeOne := ht
      rw [he]
      exact one_mem_dyadicTimes 1
  | succ n hn =>
    exact union_subset_union (image_mono hn) (image_mono hn)

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Transport_DynamicActionBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped Topology ENNReal NNReal
open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory

namespace WeakHessian
variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    [Nonempty X]

def DynamicActionBound (μ : Time → Measure X) (C : ℝ) : Prop :=
  ∀ s t : Time, ∃ π : Measure (Curve X), IsProbabilityMeasure π ∧
    π.map (fun γ => γ timeZero) = μ s ∧ π.map (fun γ => γ timeOne) = μ t ∧
    (∫⁻ γ, kineticAction γ ∂π) ≤ ENNReal.ofReal (C*(dist s t)^2)

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Transport_CouplingCostBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped Topology ENNReal NNReal
open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set MeasureTheory Filter
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable

open Set Filter Topology Bornology
open scoped InnerProductSpace


open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open scoped ENNReal NNReal


open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal


open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory


namespace WeakHessian
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

lemma IsCoupling.interpolation_endpoints {π : Measure (Curve X)} {μ₀ μ₁ : Measure X}
    (h : IsCoupling (endpointCoupling π) μ₀ μ₁) :
    interpolation π timeZero = μ₀ ∧ interpolation π timeOne = μ₁ := by
  have hm : Measurable (fun γ : Curve X => (γ timeZero, γ timeOne)) :=
    (continuous_eval_const timeZero).measurable.prodMk
      (continuous_eval_const timeOne).measurable
  simpa only [IsCoupling, endpointCoupling, Measure.map_map measurable_fst hm,
    Measure.map_map measurable_snd hm, Function.comp_def, interpolation] using h

omit [MeasurableSpace X] [BorelSpace X] in
lemma IsGeodesic.hasControlBound {γ : Curve X} (h : IsGeodesic γ) :
    HasControlBound γ (dist (γ timeZero) (γ timeOne)) := by
  have hc : IsSquareControl γ (fun _ => dist (γ timeZero) (γ timeOne)) := by
    refine ⟨measurable_const,memLp_const _,ae_of_all _ (fun _ => dist_nonneg),?_⟩
    intro s t hst
    rw [h s t, intervalIntegral.integral_const, smul_eq_mul,
      abs_sub_comm (s:ℝ), abs_of_nonneg (sub_nonneg.mpr hst)]
  have H := hasControlBound_of_squareControl hc
  simpa only [integral_const, measureReal_def, Measure.restrict_apply_univ, Real.volume_Icc, sub_zero,
    ENNReal.ofReal_one, ENNReal.toReal_one, smul_eq_mul, one_mul,
    Real.sqrt_sq dist_nonneg] using H

omit [MeasurableSpace X] [BorelSpace X] in
lemma IsGeodesic.kineticAction_le {γ : Curve X} (h : IsGeodesic γ) :
    kineticAction γ ≤ (edist (γ timeZero) (γ timeOne))^2 := by
  rw [edist_dist]
  exact pow_le_pow_left₀ bot_le (controlNorm_le h.hasControlBound) 2

lemma geodesic_plan_action_le_cost [SecondCountableTopology X] {π : Measure (Curve X)}
    (h : ∀ᵐ γ ∂π, IsGeodesic γ) :
    (∫⁻ γ, kineticAction γ ∂π) ≤ QuadraticTransportCost (endpointCoupling π) := by
  rw [QuadraticTransportCost, endpointCoupling, lintegral_map
    ((continuous_fst.edist continuous_snd).measurable.pow_const 2)
    ((continuous_eval_const timeZero).measurable.prodMk (continuous_eval_const timeOne).measurable)]
  exact lintegral_mono_ae (h.mono fun γ hγ => hγ.kineticAction_le)

def CouplingCostBound (μ : Time → Measure X) (C : ℝ) : Prop :=
  ∀ s t : Time, ∃ q : Measure (X×X), IsCoupling q (μ s) (μ t) ∧
    QuadraticTransportCost q ≤ ENNReal.ofReal (C*(dist s t)^2)

end WeakHessian

end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Geodesics_MidpointSigmaLower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
namespace WeakHessian
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

def midpointSigmaLower (K N D : ℝ) : ℝ :=
  1 / (2 * Real.exp (D * Real.sqrt (|K| / N)))

lemma midpointSigmaLower_pos (K N D : ℝ) : 0 < midpointSigmaLower K N D := by
  dsimp [midpointSigmaLower]
  positivity

lemma midpointSigmaLower_le_half (K N : ℝ) {D : ℝ} (hD : 0 ≤ D) :
    midpointSigmaLower K N D ≤ 1 / 2 := by
  have he := Real.one_le_exp_iff.mpr (mul_nonneg hD (Real.sqrt_nonneg (|K| / N)))
  dsimp [midpointSigmaLower]
  apply one_div_le_one_div_of_le (by norm_num)
  linarith

lemma midpoint_sin_ratio {x : ℝ} (hx : 0 < x) (hpi : x < Real.pi) :
    (1 : ℝ)/2 ≤ Real.sin (x/2) / Real.sin x := by
  have hs := Real.sin_pos_of_pos_of_lt_pi hx hpi
  have hh := Real.sin_pos_of_pos_of_lt_pi (show 0 < x/2 by linarith)
    (show x/2 < Real.pi by linarith [Real.pi_pos])
  rw [le_div_iff₀ hs]
  have hid : Real.sin x = 2*Real.sin (x/2)*Real.cos (x/2) := by
    have hh := Real.sin_two_mul (x/2)
    rw [show 2*(x/2)=x by ring] at hh
    exact hh
  nlinarith [Real.cos_le_one (x/2)]

lemma midpoint_sinh_ratio {x A : ℝ} (hx : 0 < x) (hA : x/2 ≤ A) (_hA0 : 0 ≤ A) :
    1 / (2*Real.exp A) ≤ Real.sinh (x/2) / Real.sinh x := by
  have hs := Real.sinh_pos_iff.mpr hx
  have hh := Real.sinh_pos_iff.mpr (show 0 < x/2 by linarith)
  have hc : Real.cosh (x/2) ≤ Real.exp A := by
    rw [Real.cosh_eq]
    have he₁ := Real.exp_le_exp.mpr hA
    have he₂ := Real.exp_le_exp.mpr (show -(x/2) ≤ A by linarith)
    linarith
  have hid : Real.sinh x = 2*Real.sinh (x/2)*Real.cosh (x/2) := by
    have hh := Real.sinh_two_mul (x/2)
    rw [show 2*(x/2)=x by ring] at hh
    exact hh
  rw [div_le_div_iff₀ (by positivity) hs]
  nlinarith

lemma sigmaCoeff_midpoint_lower {K N D θ : ℝ} (hN : 0 < N)
    (hD : 0 ≤ D) (hθ : 0 ≤ θ) (hθD : θ ≤ D) :
    ENNReal.ofReal (midpointSigmaLower K N D) ≤ sigmaCoeff K N (1/2) θ := by
  have hc := midpointSigmaLower_le_half K N hD
  unfold sigmaCoeff
  simp only [show ¬(1/2 : ℝ) ≤ 0 by norm_num, show ¬1 ≤ (1/2 : ℝ) by norm_num,
    ite_false]
  split_ifs with hzero hK hcut hKzero
  · exact ENNReal.ofReal_le_ofReal hc
  · apply ENNReal.ofReal_le_ofReal
    have hθpos : 0 < θ := lt_of_le_of_ne hθ (Ne.symm hzero)
    have hroot : 0 < Real.sqrt (K/N) := Real.sqrt_pos.mpr (div_pos hK hN)
    have hx : 0 < θ * Real.sqrt (K/N) := mul_pos hθpos hroot
    have hsq : (θ * Real.sqrt (K/N))^2 * N = K*θ^2 := by
      rw [mul_pow, Real.sq_sqrt (div_pos hK hN).le]
      field_simp
    have hslt : (θ * Real.sqrt (K/N))^2 < Real.pi^2 := by
      apply (mul_lt_mul_iff_left₀ hN).mp
      rw [hsq]
      nlinarith [hcut]
    have hpi : θ * Real.sqrt (K/N) < Real.pi := by
      nlinarith [Real.pi_pos]
    have hh := midpoint_sin_ratio hx hpi
    have he : (1/2 : ℝ)*θ*Real.sqrt (K/N) = (θ*Real.sqrt (K/N))/2 := by ring
    rw [he]
    exact hc.trans hh
  · exact le_top
  · exact ENNReal.ofReal_le_ofReal hc
  · apply ENNReal.ofReal_le_ofReal
    have hKneg : K < 0 := lt_of_le_of_ne (not_lt.mp hK) hKzero
    have hθpos : 0 < θ := lt_of_le_of_ne hθ (Ne.symm hzero)
    have hroot : 0 < Real.sqrt (-K/N) := Real.sqrt_pos.mpr (div_pos (neg_pos.mpr hKneg) hN)
    have hx : 0 < θ * Real.sqrt (-K/N) := mul_pos hθpos hroot
    have hA : (θ*Real.sqrt (-K/N))/2 ≤ D*Real.sqrt (-K/N) := by
      nlinarith
    have hh := midpoint_sinh_ratio hx hA (mul_nonneg hD hroot.le)
    have he : (1/2 : ℝ)*θ*Real.sqrt (-K/N) = (θ*Real.sqrt (-K/N))/2 := by ring
    rw [he]
    simpa only [midpointSigmaLower, abs_of_neg hKneg] using hh

def midpointTauLower (K N D : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (1/2 : ℝ) ^ (1/N) *
    ENNReal.ofReal (midpointSigmaLower K (N-1) D) ^ ((N-1)/N)

lemma midpointTauLower_pos (K N D : ℝ) : 0 < midpointTauLower K N D := by
  apply ENNReal.mul_pos_iff.mpr
  constructor
  · exact ENNReal.rpow_pos (by norm_num) ENNReal.ofReal_ne_top
  · exact ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr (midpointSigmaLower_pos _ _ _))
      ENNReal.ofReal_ne_top

lemma midpointTauLower_ne_top {K N D : ℝ} (hN : 1 < N) :
    midpointTauLower K N D ≠ ∞ := by
  unfold midpointTauLower
  apply ENNReal.mul_ne_top
  · exact ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top
  · exact ENNReal.rpow_ne_top_of_nonneg (div_nonneg (by linarith) (by linarith))
      ENNReal.ofReal_ne_top

lemma tauCoeff_midpoint_lower {K N D θ : ℝ} (hN : 1 < N)
    (hD : 0 ≤ D) (hθ : 0 ≤ θ) (hθD : θ ≤ D) :
    midpointTauLower K N D ≤ tauCoeff K N (1/2) θ := by
  unfold midpointTauLower tauCoeff
  apply mul_le_mul_right
  exact ENNReal.rpow_le_rpow (sigmaCoeff_midpoint_lower (by linarith) hD hθ hθD)
    (div_nonneg (by linarith) (by linarith))

omit [MetricSpace X] [BorelSpace X] in

lemma renyiIntegral_le_support {m μ : Measure X} [IsProbabilityMeasure μ]
    {Q : Set X} (hQ : MeasurableSet Q) (hμ : μ Qᶜ = 0) {N : ℝ} (hN : 1 < N) :
    renyiIntegral m μ N ≤ (m Q) ^ (1/N) := by
  have hNpos : 0 < N := by linarith
  have hNm : 0 < N-1 := by linarith
  have hp : 0 < 1-1/N := by rw [sub_pos, div_lt_one hNpos]; exact hN
  have hconj : (N/(N-1)).HolderConjugate N := by
    rw [Real.holderConjugate_iff]
    constructor
    · rw [lt_div_iff₀ hNm]; linarith
    · field_simp; ring
  have hrn : Measurable (μ.rnDeriv m) := Measure.measurable_rnDeriv μ m
  have hz : μ.rnDeriv m =ᵐ[m.restrict Qᶜ] 0 := by
    apply (lintegral_eq_zero_iff hrn).mp
    exact le_antisymm ((Measure.setLIntegral_rnDeriv_le Qᶜ).trans_eq hμ) bot_le
  have hzpow : (∫⁻ x in Qᶜ, (μ.rnDeriv m x)^(1-1/N) ∂m) = 0 := by
    apply (lintegral_eq_zero_iff (hrn.pow_const _)).mpr
    filter_upwards [hz] with x hx
    simp only [hx, Pi.zero_apply, ENNReal.zero_rpow_of_pos hp]
  have hsplit : renyiIntegral m μ N = ∫⁻ x in Q, (μ.rnDeriv m x)^(1-1/N) ∂m := by
    rw [renyiIntegral, ← lintegral_add_compl _ hQ, hzpow, add_zero]
  rw [hsplit]
  have hh := ENNReal.lintegral_mul_le_Lp_mul_Lq (m.restrict Q) hconj
    ((hrn.pow_const (1-1/N)).aemeasurable) (measurable_const (a := (1 : ℝ≥0∞))).aemeasurable
  have he₁ : (1-1/N)*(N/(N-1)) = 1 := by field_simp
  have he₂ : 1/(N/(N-1)) = 1-1/N := by field_simp
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const,
    Measure.restrict_apply_univ, one_mul, ← ENNReal.rpow_mul, he₁, ENNReal.rpow_one, he₂] at hh
  refine hh.trans ?_
  have hm : (∫⁻ x in Q, μ.rnDeriv m x ∂m) ≤ 1 :=
    (Measure.setLIntegral_rnDeriv_le Q).trans ((measure_mono (subset_univ Q)).trans_eq (measure_univ))
  calc
    (∫⁻ x in Q, μ.rnDeriv m x ∂m) ^ (1-1/N) * (m Q) ^ (1/N) ≤
        1 ^ (1-1/N) * (m Q) ^ (1/N) :=
      mul_le_mul_left (ENNReal.rpow_le_rpow hm hp.le) _
    _ = (m Q) ^ (1/N) := by simp

lemma interpolation_probability (π : Measure (Curve X)) [IsProbabilityMeasure π]
    (t : Time) : IsProbabilityMeasure (interpolation π t) :=
  (Measure.isProbabilityMeasure_map_iff
    (continuous_eval_const t).measurable.aemeasurable).mpr inferInstance

omit [BorelSpace X] in
lemma sigmaFinite_of_finiteOnBoundedSets (m : Measure X) (h : FiniteOnBoundedSets m)
    (o : X) : SigmaFinite m := by
  refine ⟨⟨⟨(fun n : ℕ => Metric.ball o (n : ℝ)), (fun _ => trivial),
    (fun n => h _ (Metric.isBounded_ball)), ?_⟩⟩⟩
  ext x
  simp only [mem_iUnion, Metric.mem_ball, mem_univ, iff_true]
  exact exists_nat_gt (dist x o)

omit [BorelSpace X] in
lemma hasSecondMoment_of_ae_dist_le {μ : Measure X} [IsProbabilityMeasure μ]
    (o : X) (R : ℝ) (h : ∀ᵐ x ∂μ, dist x o ≤ R) : HasSecondMoment μ := by
  refine ⟨o, ?_⟩
  calc
    (∫⁻ x, (edist x o)^2 ∂μ) ≤ ∫⁻ x, (ENNReal.ofReal R)^2 ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [h] with x hx
      rw [edist_dist]
      exact pow_le_pow_left₀ bot_le (ENNReal.ofReal_le_ofReal hx) 2
    _ < ∞ := by simp

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Entropy_FiniteEntropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace WeakHessian

variable {X : Type*} [MeasurableSpace X]

def FiniteEntropy (m μ : Measure X) : Prop :=
  μ ≪ m ∧ Integrable (llr μ m) μ

def entropyReal (m μ : Measure X) : ℝ := ∫ x, llr μ m x ∂μ

lemma entropyReal_eq_integral_density {m μ : Measure X} [SigmaFinite μ]
    [μ.HaveLebesgueDecomposition m] (h : μ ≪ m) :
    entropyReal m μ = ∫ x, (μ.rnDeriv m x).toReal * Real.log (μ.rnDeriv m x).toReal ∂m := by
  exact (integral_rnDeriv_mul_log h).symm

lemma absolutelyContinuous_restrict_of_ae_mem {m μ : Measure X} {Q : Set X}
    (hμ : μ ≪ m) (hs : ∀ᵐ x ∂μ, x ∈ Q) : μ ≪ m.restrict Q := by
  simpa only [Measure.restrict_eq_self_of_ae_mem hs] using hμ.restrict Q

lemma llr_restrict_right_of_ae_mem {m μ : Measure X} [SigmaFinite m]
    [IsFiniteMeasure μ] {Q : Set X} (hQ : MeasurableSet Q)
    (hμ : μ ≪ m) (hs : ∀ᵐ x ∂μ, x ∈ Q) :
    llr μ (m.restrict Q) =ᵐ[μ] llr μ m := by
  have hac := absolutelyContinuous_restrict_of_ae_mem hμ hs
  have hrn := Measure.rnDeriv_mul_rnDeriv (κ := m) hac
  filter_upwards [hμ.ae_eq hrn, hμ.ae_eq (Measure.rnDeriv_restrict_self m hQ), hs]
    with x hx hy hxi
  simp only [Pi.mul_apply, hy, indicator_of_mem hxi, Pi.one_apply, mul_one] at hx
  simp only [llr_def, hx]

end WeakHessian

open Set Filter MeasureTheory InformationTheory
open scoped Topology

end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Calculus_RnDerivRestrictReference
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter

attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology
open Set Filter MeasureTheory InformationTheory
open Set Filter
open scoped Topology

namespace WeakHessian
open MeasureTheory InformationTheory
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

lemma rnDeriv_restrict_reference {m μ : Measure X} [SigmaFinite m] [SigmaFinite μ]
    {Q : Set X} (hQ : MeasurableSet Q) :
    μ.rnDeriv m =ᵐ[m.restrict Q] μ.rnDeriv (m.restrict Q) := by
  have hs : m.restrict Q ⟂ₘ m.restrict Qᶜ := by
    refine ⟨Qᶜ,hQ.compl,?_,?_⟩ <;> simp [Measure.restrict_apply,hQ,hQ.compl]
  have H := Measure.rnDeriv_add_right_of_mutuallySingular (μ := μ) hs
  simpa only [Measure.restrict_add_restrict_compl hQ] using H

lemma rnDeriv_restrict_reference_ae {m μ : Measure X} [SigmaFinite m] [IsFiniteMeasure μ]
    {Q : Set X} (hQ : MeasurableSet Q) (hac : μ ≪ m) (hs : ∀ᵐ x ∂μ, x ∈ Q) :
    μ.rnDeriv m =ᵐ[μ] μ.rnDeriv (m.restrict Q) :=
  (absolutelyContinuous_restrict_of_ae_mem hac hs).ae_eq (rnDeriv_restrict_reference hQ)

lemma renyiIntegral_restrict_reference {m μ : Measure X} [SigmaFinite m] [IsFiniteMeasure μ]
    {Q : Set X} (hQ : MeasurableSet Q) (hs : ∀ᵐ x ∂μ, x ∈ Q) {N : ℝ} (hN : 1 < N) :
    renyiIntegral m μ N = renyiIntegral (m.restrict Q) μ N := by
  have hp : 0 < 1-1/N := by rw [sub_pos,div_lt_one (by linarith : 0<N)]; exact hN
  have hz : μ.rnDeriv m =ᵐ[m.restrict Qᶜ] 0 := by
    apply (lintegral_eq_zero_iff (Measure.measurable_rnDeriv μ m)).mp
    exact le_antisymm ((Measure.setLIntegral_rnDeriv_le Qᶜ).trans_eq
      (ae_iff.mp hs)) bot_le
  have Hzero : (∫⁻ x in Qᶜ, (μ.rnDeriv m x)^(1-1/N) ∂m) = 0 := by
    apply (lintegral_eq_zero_iff ((Measure.measurable_rnDeriv μ m).pow_const _)).mpr
    filter_upwards [hz] with x hx
    simp only [hx,Pi.zero_apply,ENNReal.zero_rpow_of_pos hp]
  unfold renyiIntegral
  rw [← lintegral_add_compl _ hQ,Hzero,add_zero]
  exact lintegral_congr_ae ((rnDeriv_restrict_reference (μ := μ) hQ).mono fun x hx => congrArg (fun z : ℝ≥0∞ => z^(1-1/N)) hx)

lemma finiteEntropy_restrict_reference_iff {m μ : Measure X} [SigmaFinite m] [IsFiniteMeasure μ]
    {Q : Set X} (hQ : MeasurableSet Q) (hs : ∀ᵐ x ∂μ, x ∈ Q) :
    FiniteEntropy (m.restrict Q) μ ↔ FiniteEntropy m μ := by
  constructor
  · rintro ⟨hac,hi⟩
    have hac' : μ ≪ m := hac.trans (Measure.restrict_le_self.absolutelyContinuous)
    exact ⟨hac',hi.congr (llr_restrict_right_of_ae_mem hQ hac' hs)⟩
  · rintro ⟨hac,hi⟩
    exact ⟨absolutelyContinuous_restrict_of_ae_mem hac hs,
      hi.congr (llr_restrict_right_of_ae_mem hQ hac hs).symm⟩

lemma entropyReal_restrict_reference {m μ : Measure X} [SigmaFinite m] [IsFiniteMeasure μ]
    {Q : Set X} (hQ : MeasurableSet Q) (hac : μ ≪ m) (hs : ∀ᵐ x ∂μ, x ∈ Q) :
    entropyReal (m.restrict Q) μ = entropyReal m μ :=
  integral_congr_ae (llr_restrict_right_of_ae_mem hQ hac hs)
end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_TimeHalf
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable

namespace WeakHessian

section MidpointBounds
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

def timeHalf : Time := ⟨1/2, by norm_num, by norm_num⟩

lemma cd_midpoint_support_lower {m μ₀ μ₁ : Measure X} {π : Measure (Curve X)}
    [IsProbabilityMeasure π] {K N D : ℝ} (hN : 1 < N) (hD : 0 ≤ D)
    {C : ℝ≥0∞} (hends : IsCoupling (endpointCoupling π) μ₀ μ₁)
    (hd₀ : ∀ᵐ x ∂μ₀, μ₀.rnDeriv m x ≤ C)
    (hd₁ : ∀ᵐ x ∂μ₁, μ₁.rnDeriv m x ≤ C)
    (hlen : ∀ᵐ γ ∂π, dist (γ timeZero) (γ timeOne) ≤ D)
    (hcd : (∫⁻ γ, tauCoeff K N (1/2) (dist (γ timeZero) (γ timeOne)) *
        (μ₀.rnDeriv m (γ timeZero))^(-1/N) +
        tauCoeff K N (1/2) (dist (γ timeZero) (γ timeOne)) *
        (μ₁.rnDeriv m (γ timeOne))^(-1/N) ∂π) ≤ renyiIntegral m (interpolation π timeHalf) N)
    {A : Set X} (hA : MeasurableSet A) (hs : interpolation π timeHalf Aᶜ = 0) :
    ((2 : ℝ≥0∞)*midpointTauLower K N D)^N / C ≤ m A := by
  have hNp : 0 < N := by linarith
  have he₀ : ∀ᵐ γ ∂π, μ₀.rnDeriv m (γ timeZero) ≤ C := by
    apply ae_of_ae_map (p := fun x => μ₀.rnDeriv m x ≤ C) (continuous_eval_const timeZero).measurable.aemeasurable
    change ∀ᵐ x ∂interpolation π timeZero, μ₀.rnDeriv m x ≤ C
    rw [hends.interpolation_endpoints.1]
    exact hd₀
  have he₁ : ∀ᵐ γ ∂π, μ₁.rnDeriv m (γ timeOne) ≤ C := by
    apply ae_of_ae_map (p := fun x => μ₁.rnDeriv m x ≤ C) (continuous_eval_const timeOne).measurable.aemeasurable
    change ∀ᵐ x ∂interpolation π timeOne, μ₁.rnDeriv m x ≤ C
    rw [hends.interpolation_endpoints.2]
    exact hd₁
  have hneg {r : ℝ≥0∞} (hr : r ≤ C) : C^(-1/N) ≤ r^(-1/N) := by
    rw [show -1/N = -(1/N) by ring, ENNReal.rpow_neg, ENNReal.rpow_neg]
    exact ENNReal.inv_le_inv.mpr (ENNReal.rpow_le_rpow hr (by positivity))
  let : IsProbabilityMeasure (interpolation π timeHalf) := interpolation_probability π timeHalf
  have hbase : (2:ℝ≥0∞)*midpointTauLower K N D*C^(-1/N) ≤ (m A)^(1/N) := by
    apply le_trans ?_ (hcd.trans (renyiIntegral_le_support hA hs hN))
    calc
      (2:ℝ≥0∞)*midpointTauLower K N D*C^(-1/N) =
        ∫⁻ _ : Curve X, midpointTauLower K N D*C^(-1/N)+midpointTauLower K N D*C^(-1/N) ∂π := by
          simp only [lintegral_const,measure_univ,mul_one]
          rw [two_mul,add_mul]
      _ ≤ _ := by
        apply lintegral_mono_ae
        filter_upwards [he₀,he₁,hlen] with γ h0 h1 hL
        have ht := tauCoeff_midpoint_lower (K := K) hN hD dist_nonneg hL
        exact add_le_add (mul_le_mul' ht (hneg h0)) (mul_le_mul' ht (hneg h1))
  have H := ENNReal.rpow_le_rpow hbase hNp.le
  have hp : (1/N)*N = 1 := by field_simp
  have hn : (-1/N)*N = -1 := by field_simp
  rw [ENNReal.mul_rpow_of_nonneg _ _ hNp.le,← ENNReal.rpow_mul,hn,ENNReal.rpow_neg_one,
    ← ENNReal.rpow_mul,hp,ENNReal.rpow_one] at H
  exact H

end MidpointBounds

open MeasureTheory Set
open scoped ENNReal NNReal

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

lemma map_sub_of_le (μ ρ : Measure X) [IsFiniteMeasure ρ]
    (hρ : ρ ≤ μ) {f : X → Y} (hf : Measurable f) :
    (μ-ρ).map f = μ.map f - ρ.map f := by
  calc
    (μ-ρ).map f = ((μ-ρ).map f+ρ.map f)-ρ.map f := Measure.add_sub_cancel.symm
    _ = μ.map f - ρ.map f := by rw [← Measure.map_add _ _ hf,Measure.sub_add_cancel_of_le hρ]

lemma replacement_map_eq (μ ρ β : Measure X) [IsFiniteMeasure ρ]
    (hρ : ρ ≤ μ) {f : X → Y} (hf : Measurable f) (hβ : β.map f = ρ.map f) :
    (μ-ρ+β).map f = μ.map f := by
  rw [Measure.map_add _ _ hf,hβ,← Measure.map_add _ _ hf,Measure.sub_add_cancel_of_le hρ]

lemma replacement_probability (μ ρ β : Measure X) [IsProbabilityMeasure μ]
    [IsFiniteMeasure ρ] (hρ : ρ ≤ μ) (hβ : β univ = ρ univ) :
    IsProbabilityMeasure (μ-ρ+β) := by
  constructor
  rw [Measure.add_apply,hβ,← Measure.add_apply,Measure.sub_add_cancel_of_le hρ,measure_univ]

variable [MetricSpace X] [BorelSpace X]

lemma endpointCoupling_add (π ξ : Measure (Curve X)) :
    endpointCoupling (π+ξ) = endpointCoupling π+endpointCoupling ξ := by
  exact Measure.map_add _ _ ((continuous_eval_const timeZero).measurable.prodMk (continuous_eval_const timeOne).measurable)

omit [BorelSpace X] in
lemma quadraticTransportCost_add (q q' : Measure (X×X)) :
    QuadraticTransportCost (q+q') = QuadraticTransportCost q + QuadraticTransportCost q' :=
  lintegral_add_measure _ _ _

lemma IsOptimalCoupling.reroute_plan {π θ ξ : Measure (Curve X)} {μ₀ μ₁ : Measure X}
    [IsFiniteMeasure θ] (hopt : IsOptimalCoupling (endpointCoupling π) μ₀ μ₁)
    (hθ : θ ≤ π)
    (hξ₀ : interpolation ξ timeZero = interpolation θ timeZero)
    (hξ₁ : interpolation ξ timeOne = interpolation θ timeOne)
    (hcost : QuadraticTransportCost (endpointCoupling ξ) ≤ QuadraticTransportCost (endpointCoupling θ)) :
    IsOptimalCoupling (endpointCoupling (π-θ+ξ)) μ₀ μ₁ := by
  have hends := hopt.1.interpolation_endpoints
  have hends' : interpolation (π-θ+ξ) timeZero = μ₀ ∧
      interpolation (π-θ+ξ) timeOne = μ₁ := by
    constructor
    · exact (replacement_map_eq π θ ξ hθ (continuous_eval_const timeZero).measurable hξ₀).trans hends.1
    · exact (replacement_map_eq π θ ξ hθ (continuous_eval_const timeOne).measurable hξ₁).trans hends.2
  have hc : IsCoupling (endpointCoupling (π-θ+ξ)) μ₀ μ₁ := by
    have hm : Measurable (fun γ : Curve X => (γ timeZero,γ timeOne)) := (continuous_eval_const timeZero).measurable.prodMk (continuous_eval_const timeOne).measurable
    constructor
    · simpa only [endpointCoupling,Measure.map_map measurable_fst hm,Function.comp_def,
        interpolation] using hends'.1
    · simpa only [endpointCoupling,Measure.map_map measurable_snd hm,Function.comp_def,
        interpolation] using hends'.2
  refine ⟨hc,fun q hq => le_trans ?_ (hopt.2 q hq)⟩
  calc
    QuadraticTransportCost (endpointCoupling (π-θ+ξ)) =
        QuadraticTransportCost (endpointCoupling (π-θ)) + QuadraticTransportCost (endpointCoupling ξ) := by
      rw [endpointCoupling_add,quadraticTransportCost_add]
    _ ≤ QuadraticTransportCost (endpointCoupling (π-θ)) + QuadraticTransportCost (endpointCoupling θ) :=
      add_le_add le_rfl hcost
    _ = QuadraticTransportCost (endpointCoupling π) := by
      rw [← quadraticTransportCost_add,← endpointCoupling_add,Measure.sub_add_cancel_of_le hθ]

omit [MeasurableSpace X] [BorelSpace X] in
lemma geodesic_plan_reroute {π θ ξ : Measure (Curve X)}
    (hπ : ∀ᵐ γ ∂π, IsGeodesic γ) (hξ : ∀ᵐ γ ∂ξ, IsGeodesic γ) :
    ∀ᵐ γ ∂(π-θ+ξ), IsGeodesic γ := by
  rw [ae_add_measure_iff]
  exact ⟨(Measure.absolutelyContinuous_of_le Measure.sub_le).ae_le hπ,hξ⟩

lemma interpolation_restricted (π : Measure (Curve X)) (t : Time)
    {A : Set X} (hA : MeasurableSet A) :
    interpolation (π.restrict ((fun γ => γ t) ⁻¹' A)) t = (interpolation π t).restrict A := by
  exact (Measure.restrict_map (continuous_eval_const t).measurable hA).symm

end WeakHessian

end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Calculus_RnDerivSmul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
namespace WeakHessian
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

omit [MetricSpace X] [BorelSpace X] in
lemma rnDeriv_le_of_le_smul {m μ : Measure X} [SigmaFinite m] {C : ℝ≥0∞}
    (h : μ ≤ C • m) : ∀ᵐ x ∂m, μ.rnDeriv m x ≤ C := by
  apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite (μ.measurable_rnDeriv m)
  intro A _ _
  calc
    (∫⁻ x in A, μ.rnDeriv m x ∂m) ≤ μ A := Measure.setLIntegral_rnDeriv_le A
    _ ≤ C*m A := h A
    _ = ∫⁻ _ in A, C ∂m := by simp

lemma endpointCoupling_couples (π : Measure (Curve X)) :
    IsCoupling (endpointCoupling π) (interpolation π timeZero) (interpolation π timeOne) := by
  have hm : Measurable (fun γ : Curve X => (γ timeZero,γ timeOne)) := (continuous_eval_const timeZero).measurable.prodMk (continuous_eval_const timeOne).measurable
  constructor
  · simp only [endpointCoupling,Measure.map_map measurable_fst hm,Function.comp_def,interpolation]
  · simp only [endpointCoupling,Measure.map_map measurable_snd hm,Function.comp_def,interpolation]

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Transport_HopfObjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open Set Filter Topology Bornology
open scoped InnerProductSpace

attribute [local instance] Classical.propDecidable
open Set
open scoped NNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology
open Set Filter
open scoped Topology ENNReal NNReal

namespace WeakHessianTransport
variable {X : Type*} [MetricSpace X]

def hopfObjective (f : X → ℝ) (t : ℝ) (x y : X) : ℝ :=
  f y + dist x y ^ 2 / (2*t)

end WeakHessianTransport

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Transport_LiftBoundedCoupling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped Topology ENNReal NNReal
open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory

namespace WeakHessian
open Set Filter MeasureTheory
open scoped ENNReal Topology

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X]

lemma CurvatureDimension.lift_bounded_coupling {m : Measure X} {K N : ℝ}
    (hcd : CurvatureDimension m K N) (q : Measure (X×X)) [IsFiniteMeasure q]
    (hac0 : q.map Prod.fst ≪ m) (hac1 : q.map Prod.snd ≪ m)
    (o : X) (R : ℝ) (hR : ∀ᵐ p ∂q, dist p.1 o ≤ R ∧ dist p.2 o ≤ R) :
    ∃ π : Measure (Curve X), interpolation π timeZero = q.map Prod.fst ∧
      interpolation π timeOne = q.map Prod.snd ∧
      (∫⁻ γ,kineticAction γ ∂π) ≤ QuadraticTransportCost q := by
  by_cases hq : q = 0
  · subst q
    exact ⟨0,by simp [interpolation],by simp [interpolation],by simp [QuadraticTransportCost]⟩
  have hz : q univ ≠ 0 := by intro H; exact hq (Measure.ext fun s hs => by have := measure_mono (subset_univ s) (μ := q); simp only [H,nonpos_iff_eq_zero] at this; simpa using this)
  have ht : q univ ≠ ∞ := measure_ne_top _ _
  let q' : Measure (X×X) := (q univ)⁻¹ • q
  have hp : IsProbabilityMeasure q' := by
    constructor
    simp only [q',Measure.smul_apply,smul_eq_mul,ENNReal.inv_mul_cancel hz ht]
  let := hp
  have hcancel : q univ • q' = q := by
    dsimp only [q']
    rw [smul_smul,ENNReal.mul_inv_cancel hz ht,one_smul]
  have hp0 : IsProbabilityMeasure (q'.map Prod.fst) := by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  have hp1 : IsProbabilityMeasure (q'.map Prod.snd) := by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  let := hp0
  let := hp1
  have hr : ∀ᵐ p ∂q', dist p.1 o ≤ R ∧ dist p.2 o ≤ R :=
    (Measure.AbsolutelyContinuous.rfl.smul_left _).ae_le hR
  have hmom (f : X×X → X) (hf : Measurable f) (hb : ∀ᵐ p ∂q',dist (f p) o ≤ R) :
      HasSecondMoment (q'.map f) := by
    let : IsProbabilityMeasure (q'.map f) := by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
    refine ⟨o,?_⟩
    calc
      (∫⁻ x,(edist x o)^2 ∂q'.map f) ≤ ∫⁻ x,(ENNReal.ofReal R)^2 ∂q'.map f := by
        apply lintegral_mono_ae
        have H : ∀ᵐ x ∂q'.map f,dist x o ≤ R := (ae_map_iff hf.aemeasurable (measurableSet_le (by fun_prop) measurable_const)).mpr hb
        filter_upwards [H] with x hx
        rw [edist_dist]
        exact pow_le_pow_left₀ bot_le (ENNReal.ofReal_le_ofReal hx) 2
      _ < ∞ := by simp
  have ha0 : q'.map Prod.fst ≪ m := by
    dsimp only [q']
    rw [Measure.map_smul]
    exact hac0.smul_left _
  have ha1 : q'.map Prod.snd ≪ m := by
    dsimp only [q']
    rw [Measure.map_smul]
    exact hac1.smul_left _
  obtain ⟨π,hπ,hgeo,hopt,_⟩ := hcd (q'.map Prod.fst) (q'.map Prod.snd) hp0 hp1
    (hmom Prod.fst measurable_fst (hr.mono fun _ hx => hx.1))
    (hmom Prod.snd measurable_snd (hr.mono fun _ hx => hx.2)) ha0 ha1
  obtain ⟨h0,h1⟩ := hopt.1.interpolation_endpoints
  refine ⟨q univ • π,?_,?_,?_⟩
  · change (q univ • π).map _ = _
    rw [Measure.map_smul]
    change q univ • interpolation π timeZero = _
    rw [h0,←Measure.map_smul,hcancel]
  · change (q univ • π).map _ = _
    rw [Measure.map_smul]
    change q univ • interpolation π timeOne = _
    rw [h1,←Measure.map_smul,hcancel]
  · rw [lintegral_smul_measure]
    change q univ * (∫⁻ γ,kineticAction γ ∂π) ≤ _
    calc
      _ ≤ q univ * QuadraticTransportCost q' := by
        gcongr
        exact (geodesic_plan_action_le_cost hgeo).trans (hopt.2 q' ⟨rfl,rfl⟩)
      _ = QuadraticTransportCost q := by
        change q univ • (∫⁻ p : X×X,(edist p.1 p.2)^2 ∂q') = ∫⁻ p : X×X,(edist p.1 p.2)^2 ∂q
        rw [←lintegral_smul_measure,hcancel]

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Curvature_Nonbranching
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
namespace WeakHessian
variable {X : Type*} [MetricSpace X]
variable [MeasurableSpace X] [BorelSpace X]

omit [MeasurableSpace X] [BorelSpace X]

@[simp] theorem clampTime_coe (t : Time) : clampTime (t : ℝ) = t := by
  apply Subtype.ext
  simp only [clampTime, min_eq_right t.property.2, max_eq_right t.property.1]
@[simp] theorem evalReal_zero (γ : Curve X) : evalReal γ 0 = γ timeZero :=
  evalReal_coe γ timeZero

@[simp] theorem evalReal_one (γ : Curve X) : evalReal γ 1 = γ timeOne :=
  evalReal_coe γ timeOne

theorem IsGeodesic.lipschitz {γ : Curve X} (hγ : IsGeodesic γ) :
    LipschitzWith (nndist (γ timeZero) (γ timeOne)) γ := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  simpa only [Subtype.dist_eq, Real.dist_eq, coe_nndist, mul_comm] using (hγ s t).le

theorem IsGeodesic.evalReal_lipschitzWith {γ : Curve X} (hγ : IsGeodesic γ) :
    LipschitzWith (nndist (γ timeZero) (γ timeOne)) (evalReal γ) := by
  change LipschitzWith _ (γ ∘ Set.projIcc 0 1 zero_le_one)
  simpa only [mul_one] using
    hγ.lipschitz.comp (LipschitzWith.projIcc (show (0 : ℝ) ≤ 1 by norm_num))

theorem isGeodesic_of_dist_le (γ : Curve X)
    (h : ∀ s t : Time, dist (γ s) (γ t) ≤
      |(s : ℝ) - (t : ℝ)| * dist (γ timeZero) (γ timeOne)) : IsGeodesic γ := by
  have ordered (s t : Time) (hst : (s : ℝ) ≤ (t : ℝ)) :
      dist (γ s) (γ t) = |(s : ℝ) - (t : ℝ)| * dist (γ timeZero) (γ timeOne) := by
    apply le_antisymm (h s t)
    have h0s := h timeZero s
    have ht1 := h t timeOne
    change dist (γ timeZero) (γ s) ≤ |0 - (s : ℝ)| * _ at h0s
    change dist (γ t) (γ timeOne) ≤ |(t : ℝ) - 1| * _ at ht1
    rw [zero_sub, abs_neg, abs_of_nonneg s.property.1] at h0s
    rw [abs_of_nonpos (sub_nonpos.mpr t.property.2), neg_sub] at ht1
    have htriangle := (dist_triangle (γ timeZero) (γ s) (γ timeOne)).trans
      (add_le_add le_rfl (dist_triangle (γ s) (γ t) (γ timeOne)))
    rw [abs_of_nonpos (sub_nonpos.mpr hst), neg_sub]
    nlinarith
  intro s t
  rcases le_total (s : ℝ) (t : ℝ) with hst | hts
  · exact ordered s t hst
  · rw [dist_comm, ordered t s hts, abs_sub_comm]

theorem lipschitzWith_if_le {L : ℝ≥0} {f g : ℝ → X} (c : ℝ)
    (hf : LipschitzWith L f) (hg : LipschitzWith L g) (hfg : f c = g c) :
    LipschitzWith L (fun t => if t ≤ c then f t else g t) := by
  have ordered (s t : ℝ) (hst : s ≤ t) :
      dist (if s ≤ c then f s else g s) (if t ≤ c then f t else g t) ≤
        (L : ℝ) * (t - s) := by
    by_cases hs : s ≤ c
    · by_cases ht : t ≤ c
      · simpa only [ite_eq_left hs, ite_eq_left ht, Real.dist_eq,
          abs_of_nonpos (sub_nonpos.mpr hst), neg_sub] using hf.dist_le_mul s t
      · simp only [ite_eq_left hs, ite_eq_right ht]
        have hct : c ≤ t := (lt_of_not_ge ht).le
        calc
          dist (f s) (g t) ≤ dist (f s) (f c) + dist (f c) (g t) :=
            dist_triangle _ _ _
          _ = dist (f s) (f c) + dist (g c) (g t) := by rw [hfg]
          _ ≤ (L : ℝ) * (c - s) + (L : ℝ) * (t - c) := by
            apply add_le_add
            · simpa only [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hs), neg_sub]
                using hf.dist_le_mul s c
            · simpa only [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hct), neg_sub]
                using hg.dist_le_mul c t
          _ = (L : ℝ) * (t - s) := by ring
    · have ht : ¬t ≤ c := fun ht => hs (hst.trans ht)
      simpa only [ite_eq_right hs, ite_eq_right ht, Real.dist_eq,
        abs_of_nonpos (sub_nonpos.mpr hst), neg_sub] using hg.dist_le_mul s t
  apply LipschitzWith.of_dist_le_mul
  intro s t
  rcases le_total s t with hst | hts
  · simpa only [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hst), neg_sub]
      using ordered s t hst
  · rw [dist_comm]
    simpa only [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hts)] using ordered t s hts

theorem IsGeodesic.stretch_lipschitzWith {τ : Curve X} (hτ : IsGeodesic τ)
    (a b : ℝ) (hab : a < b) {L : ℝ≥0}
    (hlen : dist (τ timeZero) (τ timeOne) = (b - a) * (L : ℝ)) :
    LipschitzWith L (fun t : ℝ => evalReal τ ((t - a) / (b - a))) := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  calc
    dist (evalReal τ ((s - a) / (b - a))) (evalReal τ ((t - a) / (b - a))) ≤
        ((b - a) * (L : ℝ)) * |(s - a) / (b - a) - (t - a) / (b - a)| := by
      simpa only [coe_nndist, hlen, Real.dist_eq] using
        hτ.evalReal_lipschitzWith.dist_le_mul ((s - a) / (b - a)) ((t - a) / (b - a))
    _ = (L : ℝ) * dist s t := by
      have heq : (s - a) / (b - a) - (t - a) / (b - a) = (s - t) / (b - a) := by ring
      rw [heq, abs_div, abs_of_pos (sub_pos.mpr hab), Real.dist_eq]
      field_simp [ne_of_gt (sub_pos.mpr hab)]

theorem isCompact_curve_family (S : Set (Curve X)) (hS : IsClosed S)
    (Q : Set X) (hQ : IsCompact Q) (L : ℝ≥0)
    (hQs : ∀ γ ∈ S, ∀ t : Time, γ t ∈ Q)
    (hL : ∀ γ ∈ S, LipschitzWith L γ) : IsCompact S := by
  let e := ContinuousMap.isometryEquivBoundedOfCompact Time X
  have hb : IsClosed (e '' S) := e.toHomeomorph.isClosedMap S hS
  have hc : IsCompact (e '' S) := by
    apply BoundedContinuousFunction.arzela_ascoli₂ Q hQ (e '' S) hb
    · rintro f t ⟨γ, hγ, rfl⟩
      exact hQs γ hγ t
    · apply Metric.equicontinuous_of_continuity_modulus (fun r : ℝ => (L : ℝ) * r)
        (by simpa only [id_eq, mul_zero] using
          (tendsto_id : Tendsto (fun r : ℝ => r) (𝓝 0) (𝓝 0)).const_mul (L : ℝ))
      intro s t f
      obtain ⟨γ, hγ, he⟩ := f.property
      have hed : (f.val : Time → X) = γ := by rw [← he]; rfl
      change dist (f.val s) (f.val t) ≤ (L : ℝ) * dist s t
      rw [congrFun hed s, congrFun hed t]
      exact (hL γ hγ).dist_le_mul s t
  exact e.toHomeomorph.isCompact_image.mp hc

lemma isClosed_isGeodesic : IsClosed {γ : Curve X | IsGeodesic γ} := by
  simp only [IsGeodesic, ofPred_forall]
  apply isClosed_iInter
  intro s
  apply isClosed_iInter
  intro t
  exact isClosed_eq ((continuous_eval_const s).dist (continuous_eval_const t))
    (((continuous_eval_const timeZero).dist (continuous_eval_const timeOne)).const_mul _)

end WeakHessian

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Entropy_RenyiKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter

attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology
open Set Filter MeasureTheory InformationTheory
open scoped Topology

namespace WeakHessian

def renyiKernel (a r : ℝ) : ℝ := (r-r^(1-a))/a+1-r

lemma renyiKernel_nonneg {a r : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hr : 0 ≤ r) :
    0 ≤ renyiKernel a r := by
  have H := Real.geom_mean_le_arith_mean2_weighted
    (show 0 ≤ 1-a by linarith) ha.le hr (show (0:ℝ) ≤ 1 by norm_num) (by ring : 1-a+a=1)
  simp only [Real.one_rpow,mul_one] at H
  have H' : (r-1)*a ≤ r-r^(1-a) := by nlinarith
  have H'' := (le_div_iff₀ ha).mpr H'
  unfold renyiKernel
  linarith

lemma rpow_sub_le_add_one {a r : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (hr : 0 ≤ r) :
    r^(1-a) ≤ r+1 := by
  have H := Real.geom_mean_le_arith_mean2_weighted (show 0 ≤ 1-a by linarith)
    ha hr (show (0:ℝ) ≤ 1 by norm_num) (by ring : 1-a+a=1)
  simp only [Real.one_rpow,mul_one] at H
  nlinarith [mul_nonneg ha hr]

lemma tendsto_renyiKernel {r : ℝ} (hr : 0 ≤ r) :
    Tendsto (fun a => renyiKernel a r) (𝓝[>] 0) (𝓝 (klFun r)) := by
  rcases hr.eq_or_lt with rfl | hr
  · have ha : ∀ᶠ a : ℝ in 𝓝[>] 0, a < 1 :=
      (eventually_lt_nhds (by norm_num : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds
    apply tendsto_const_nhds.congr'
    filter_upwards [ha] with a ha
    simp [renyiKernel,klFun,Real.zero_rpow (by linarith : (1-a:ℝ) ≠ 0)]
  · have hd : HasDerivAt (fun a : ℝ => r^(1-a)) (-r*Real.log r) 0 := by
      convert HasDerivAt.const_rpow hr ((hasDerivAt_const (0:ℝ) (1:ℝ)).sub (hasDerivAt_id 0)) using 1
      <;> first | rfl | (simp; ring)
    have H := hd.tendsto_slope.mono_left (nhdsGT_le_nhdsNE (0:ℝ))
    have H' := (H.neg.add_const 1).sub_const r
    convert H' using 1
    · ext a
      simp only [renyiKernel,slope_def_field,sub_zero,Real.rpow_one]
      ring
    · simp only [klFun]
      congr 1
      ring

open InformationTheory

variable {X : Type*} [MeasurableSpace X]

lemma renyiKernel_le_klFun {a r : ℝ} (ha : 0 < a) (ha1 : a < 1) (hr : 0 ≤ r) :
    renyiKernel a r ≤ klFun r := by
  rcases hr.eq_or_lt with rfl | hr
  · simp [renyiKernel, klFun, Real.zero_rpow (by linarith : (1-a:ℝ) ≠ 0)]
  have H := Real.add_one_le_exp (-a*Real.log r)
  have hp : r^(1-a) = r*Real.exp (-a*Real.log r) := by
    rw [Real.rpow_def_of_pos hr]
    rw [show Real.log r * (1-a) = Real.log r + (-a*Real.log r) by ring,
      Real.exp_add,Real.exp_log hr]
  have HH : (r-r^(1-a))/a ≤ r*Real.log r := by
    apply (div_le_iff₀ ha).mpr
    rw [hp]
    nlinarith [mul_le_mul_of_nonneg_left H hr.le]
  unfold renyiKernel klFun
  linarith

lemma integrable_rpow_sub {m : Measure X} [IsFiniteMeasure m] {r : X → ℝ}
    (hr : Integrable r m) (hr0 : ∀ᵐ x ∂m, 0 ≤ r x) {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) :
    Integrable (fun x => (r x)^(1-a)) m := by
  apply (hr.add (integrable_const 1)).mono'
  · exact (Real.continuous_rpow_const (by linarith : 0 ≤ 1-a)).comp_aestronglyMeasurable hr.1
  · filter_upwards [hr0] with x hx
    rw [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hx _)]
    exact rpow_sub_le_add_one ha ha1.le hx

lemma integrable_renyiKernel {m : Measure X} [IsFiniteMeasure m] {r : X → ℝ}
    (hr : Integrable r m) (hr0 : ∀ᵐ x ∂m, 0 ≤ r x) {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) :
    Integrable (fun x => renyiKernel a (r x)) m := by
  exact (((hr.sub (integrable_rpow_sub hr hr0 ha ha1)).div_const a).add (integrable_const 1)).sub hr

lemma tendsto_integral_rpow_sub {m : Measure X} [IsFiniteMeasure m] {r : X → ℝ}
    (hr : Integrable r m) (hr0 : ∀ᵐ x ∂m, 0 ≤ r x) {a : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (ha1 : ∀ n, a n < 1) (halim : Tendsto a atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, (r x)^(1-a n) ∂m) atTop (𝓝 (∫ x, r x ∂m)) := by
  apply tendsto_integral_of_dominated_convergence (fun x => r x+1)
  · exact fun n => (integrable_rpow_sub hr hr0 (ha n) (ha1 n)).1
  · exact hr.add (integrable_const 1)
  · intro n
    filter_upwards [hr0] with x hx
    rw [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hx _)]
    exact rpow_sub_le_add_one (ha n) (ha1 n).le hx
  · filter_upwards [hr0] with x hx
    simpa only [sub_zero, Real.rpow_one, Function.comp_def] using
      (Real.continuousAt_rpow (r x,1) (Or.inr zero_lt_one)).tendsto.comp
        (tendsto_const_nhds.prodMk_nhds (by simpa using (tendsto_const_nhds.sub halim : Tendsto (fun n => (1:ℝ)-a n) atTop (𝓝 (1-0)))))

lemma integral_klFun_le_of_renyi_bounds {m : Measure X} [IsFiniteMeasure m] {r : X → ℝ}
    (hr : Integrable r m) (hr0 : ∀ᵐ x ∂m, 0 ≤ r x) {a B : ℕ → ℝ} {L : ℝ}
    (ha : ∀ n, 0 < a n) (ha1 : ∀ n, a n < 1) (halim : Tendsto a atTop (𝓝 0))
    (hb : ∀ n, ∫ x, renyiKernel (a n) (r x) ∂m ≤ B n) (hB : Tendsto B atTop (𝓝 L)) :
    Integrable (fun x => klFun (r x)) m ∧ (∫ x, klFun (r x) ∂m) ≤ L := by
  have hmeas : AEStronglyMeasurable (fun x => klFun (r x)) m :=
    continuous_klFun.comp_aestronglyMeasurable hr.1
  have hn : ∀ n, 0 ≤ᵐ[m] fun x => renyiKernel (a n) (r x) :=
    fun n => hr0.mono (fun x hx => renyiKernel_nonneg (ha n) (ha1 n).le hx)
  have hni := fun n => integrable_renyiKernel hr hr0 (ha n).le (ha1 n)
  have hlim : ∀ᵐ x ∂m, Tendsto (fun n => ENNReal.ofReal (renyiKernel (a n) (r x)))
      atTop (𝓝 (ENNReal.ofReal (klFun (r x)))) := by
    filter_upwards [hr0] with x hx
    exact (ENNReal.continuous_ofReal.tendsto _).comp ((tendsto_renyiKernel hx).comp
      (tendsto_nhdsWithin_iff.mpr ⟨halim,Eventually.of_forall ha⟩))
  have hfat : (∫⁻ x, ENNReal.ofReal (klFun (r x)) ∂m) ≤ ENNReal.ofReal L := by
    calc
      _ = ∫⁻ x, liminf (fun n => ENNReal.ofReal (renyiKernel (a n) (r x))) atTop ∂m :=
        lintegral_congr_ae (hlim.mono (fun x hx => hx.liminf_eq.symm))
      _ ≤ liminf (fun n => ∫⁻ x, ENNReal.ofReal (renyiKernel (a n) (r x)) ∂m) atTop :=
        lintegral_liminf_le' (fun n => (hni n).1.aemeasurable.ennreal_ofReal)
      _ ≤ liminf (fun n => ENNReal.ofReal (B n)) atTop := by
        simp only [liminf_eq_iSup_iInf_of_nat]
        apply iSup_mono
        intro k
        apply iInf_mono
        intro n
        apply iInf_mono
        intro hkn
        rw [← ofReal_integral_eq_lintegral_ofReal (hni n) (hn n)]
        exact ENNReal.ofReal_le_ofReal (hb n)
      _ = _ := ((ENNReal.continuous_ofReal.tendsto _).comp hB).liminf_eq
  have hint : Integrable (fun x => klFun (r x)) m :=
    (lintegral_ofReal_ne_top_iff_integrable hmeas (hr0.mono fun x hx => klFun_nonneg hx)).mp
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hfat)
  have hL : 0 ≤ L := ge_of_tendsto hB (Eventually.of_forall fun n =>
    (integral_nonneg_of_ae (hn n)).trans (hb n))
  refine ⟨hint, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hint (hr0.mono fun x hx => klFun_nonneg hx)] at hfat
  exact (ENNReal.ofReal_le_ofReal_iff hL).mp hfat

lemma tendsto_integral_renyiKernel {m : Measure X} [IsFiniteMeasure m] {r : X → ℝ}
    (hr : Integrable r m) (hr0 : ∀ᵐ x ∂m, 0 ≤ r x)
    (hkl : Integrable (fun x => klFun (r x)) m) {a : ℕ → ℝ}
    (ha : ∀ n, 0 < a n) (ha1 : ∀ n, a n < 1) (halim : Tendsto a atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, renyiKernel (a n) (r x) ∂m) atTop
      (𝓝 (∫ x, klFun (r x) ∂m)) := by
  apply tendsto_integral_of_dominated_convergence (fun x => klFun (r x))
  · exact fun n => (integrable_renyiKernel hr hr0 (ha n).le (ha1 n)).1
  · exact hkl
  · intro n
    filter_upwards [hr0] with x hx
    rw [Real.norm_eq_abs,abs_of_nonneg (renyiKernel_nonneg (ha n) (ha1 n).le hx)]
    exact renyiKernel_le_klFun (ha n) (ha1 n) hx
  · exact hr0.mono (fun x hx => (tendsto_renyiKernel hx).comp
      (tendsto_nhdsWithin_iff.mpr ⟨halim,Eventually.of_forall ha⟩))
end WeakHessian

end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Entropy_AcBoundedRenyiGaps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter

attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology
open Set Filter MeasureTheory InformationTheory
open scoped Topology

namespace WeakHessian
open InformationTheory

variable {X : Type*} [MeasurableSpace X]

lemma ac_of_bounded_renyi_gaps {m μ : Measure X} [IsFiniteMeasure m] [IsProbabilityMeasure μ]
    {a B : ℕ → ℝ} {L : ℝ} (ha : ∀ n, 0 < a n) (ha1 : ∀ n, a n < 1)
    (halim : Tendsto a atTop (𝓝 0)) (hB : Tendsto B atTop (𝓝 L))
    (hb : ∀ n, (1-∫ x, (μ.rnDeriv m x).toReal^(1-a n) ∂m)/(a n) ≤ B n) : μ ≪ m := by
  have hi : Integrable (fun x => (μ.rnDeriv m x).toReal) m := Measure.integrable_toReal_rnDeriv
  have hn : ∀ᵐ x ∂m, 0 ≤ (μ.rnDeriv m x).toReal := Eventually.of_forall fun x => ENNReal.toReal_nonneg
  have H := tendsto_integral_rpow_sub hi hn (fun n => (ha n).le) ha1 halim
  have Hm : 1 ≤ ∫ x, (μ.rnDeriv m x).toReal ∂m := by
    have Hl : Tendsto (fun n => 1-a n*B n) atTop (𝓝 (1:ℝ)) := by
      simpa using tendsto_const_nhds.sub (halim.mul hB)
    apply le_of_tendsto_of_tendsto' Hl H
    intro n
    have HH := (div_le_iff₀ (ha n)).mp (hb n)
    nlinarith
  rw [Measure.integral_toReal_rnDeriv',probReal_univ (μ := μ)] at Hm
  have hz : (μ.singularPart m).real Set.univ = 0 := by
    have hnn := measureReal_nonneg (μ := μ.singularPart m) (s := Set.univ)
    linarith
  have hzero : μ.singularPart m = 0 := by
    apply Measure.measure_univ_eq_zero.mp
    exact (measureReal_eq_zero_iff (measure_ne_top _ _)).mp hz
  exact (Measure.singularPart_eq_zero μ m).mp hzero

lemma finiteEntropy_of_renyi_gaps {m μ : Measure X} [IsFiniteMeasure m] [IsProbabilityMeasure μ]
    {a B : ℕ → ℝ} {L : ℝ} (ha : ∀ n, 0 < a n) (ha1 : ∀ n, a n < 1)
    (halim : Tendsto a atTop (𝓝 0)) (hB : Tendsto B atTop (𝓝 L))
    (hb : ∀ n, (1-∫ x, (μ.rnDeriv m x).toReal^(1-a n) ∂m)/(a n) ≤ B n) :
    FiniteEntropy m μ ∧ entropyReal m μ ≤ L := by
  have hac := ac_of_bounded_renyi_gaps ha ha1 halim hB hb
  have hi : Integrable (fun x => (μ.rnDeriv m x).toReal) m := Measure.integrable_toReal_rnDeriv
  have hn : ∀ᵐ x ∂m, 0 ≤ (μ.rnDeriv m x).toReal := Eventually.of_forall fun x => ENNReal.toReal_nonneg
  have hh : ∀ n, (∫ x, renyiKernel (a n) (μ.rnDeriv m x).toReal ∂m) ≤ B n+m.real Set.univ-1 := by
    intro n
    simp only [renyiKernel]
    rw [integral_sub,integral_add,integral_div,integral_sub,
      Measure.integral_toReal_rnDeriv hac,probReal_univ (μ := μ),integral_const,smul_eq_mul,mul_one]
    · linarith [hb n]
    · exact hi
    · exact integrable_rpow_sub hi hn (ha n).le (ha1 n)
    · exact (hi.sub (integrable_rpow_sub hi hn (ha n).le (ha1 n))).div_const _
    · exact integrable_const 1
    · exact ((hi.sub (integrable_rpow_sub hi hn (ha n).le (ha1 n))).div_const _).add (integrable_const 1)
    · exact hi
  obtain ⟨hki,hkl⟩ := integral_klFun_le_of_renyi_bounds hi hn ha ha1 halim hh
    ((hB.add_const _).sub_const _)
  have hll := (integrable_klFun_rnDeriv_iff hac).mp hki
  refine ⟨⟨hac,hll⟩,?_⟩
  rw [integral_klFun_rnDeriv hac hll,probReal_univ (μ := μ)] at hkl
  change (∫ x, llr μ m x ∂μ) ≤ L
  linarith


lemma density_mul_neg_rpow {a r : ℝ} (ha : a < 1) (hr : 0 ≤ r) :
    r*r^(-a) = r^(1-a) := by
  rw [sub_eq_add_neg,Real.rpow_add' hr (by linarith : 1 + -a ≠ 0),Real.rpow_one]

lemma integral_density_neg_rpow {m μ : Measure X} [IsFiniteMeasure m] [IsFiniteMeasure μ]
    (hac : μ ≪ m) {a : ℝ} (ha : a < 1) :
    (∫ x, (μ.rnDeriv m x).toReal^(-a) ∂μ) =
      ∫ x, (μ.rnDeriv m x).toReal^(1-a) ∂m := by
  rw [← integral_toReal_rnDeriv_mul hac]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => density_mul_neg_rpow ha ENNReal.toReal_nonneg

lemma integrable_density_neg_rpow {m μ : Measure X} [IsFiniteMeasure m] [IsFiniteMeasure μ]
    (hac : μ ≪ m) {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) :
    Integrable (fun x => (μ.rnDeriv m x).toReal^(-a)) μ := by
  apply (integrable_toReal_rnDeriv_mul_iff hac).mp
  exact (integrable_rpow_sub Measure.integrable_toReal_rnDeriv
    (Eventually.of_forall fun x => ENNReal.toReal_nonneg) ha ha1).congr
      (Eventually.of_forall fun x => (density_mul_neg_rpow ha1 ENNReal.toReal_nonneg).symm)

lemma integrable_inverse_density {m μ : Measure X} [IsFiniteMeasure m] [IsFiniteMeasure μ]
    (hac : μ ≪ m) : Integrable (fun x => ((μ.rnDeriv m x).toReal)⁻¹) μ := by
  apply (integrable_toReal_rnDeriv_mul_iff hac).mp
  apply (integrable_const (1:ℝ)).mono'
  · exact ((Measure.measurable_rnDeriv μ m).ennreal_toReal.mul
      (Measure.measurable_rnDeriv μ m).ennreal_toReal.inv).aestronglyMeasurable
  · exact Eventually.of_forall fun x => by
      by_cases hz : (μ.rnDeriv m x).toReal = 0
      · simp [hz]
      · simp [hz]

lemma density_pos_ae {m μ : Measure X} [SigmaFinite m] [IsFiniteMeasure μ]
    (hac : μ ≪ m) : ∀ᵐ x ∂μ, 0 < (μ.rnDeriv m x).toReal := by
  filter_upwards [Measure.rnDeriv_pos hac, hac.ae_le (Measure.rnDeriv_lt_top μ m)] with x hp ht
  exact ENNReal.toReal_pos hp.ne' ht.ne

lemma tendsto_integral_weighted_density_neg_rpow {Y : Type*} [MeasurableSpace Y]
    {m μ : Measure X} [IsFiniteMeasure m] [IsFiniteMeasure μ]
    {π : Measure Y} [IsFiniteMeasure π] (hac : μ ≪ m) {e : Y → X} (he : Measurable e)
    (hmap : Measure.map e π = μ) {ψ : Y → ℝ} (hψ : AEStronglyMeasurable ψ π)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ᵐ y ∂π, |ψ y| ≤ C)
    {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (ha1 : ∀ n, a n ≤ 1)
    (halim : Tendsto a atTop (𝓝 0)) :
    Tendsto (fun n => ∫ y, ψ y*(μ.rnDeriv m (e y)).toReal^(-a n) ∂π) atTop
      (𝓝 (∫ y, ψ y ∂π)) := by
  have hi : Integrable (fun y => ((μ.rnDeriv m (e y)).toReal)⁻¹) π := by
    have H := integrable_inverse_density hac
    have H' : Integrable (fun x => ((μ.rnDeriv m x).toReal)⁻¹) (Measure.map e π) := by
      simpa only [hmap] using H
    exact H'.comp_measurable he
  have hp : ∀ᵐ y ∂π, 0 < (μ.rnDeriv m (e y)).toReal := by
    have H := density_pos_ae hac
    have H' : ∀ᵐ x ∂Measure.map e π, 0 < (μ.rnDeriv m x).toReal := by
      simpa only [hmap] using H
    exact ae_of_ae_map he.aemeasurable H'
  apply tendsto_integral_of_dominated_convergence (fun y => C*(1+((μ.rnDeriv m (e y)).toReal)⁻¹))
  · intro n
    exact hψ.mul (((Measure.measurable_rnDeriv μ m).comp he).ennreal_toReal.pow_const _).aestronglyMeasurable
  · exact ((integrable_const 1).add hi).const_mul C
  · intro n
    filter_upwards [hb,hp] with y hby hpy
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (Real.rpow_nonneg hpy.le _)]
    apply (mul_le_mul_of_nonneg_right hby (Real.rpow_nonneg hpy.le _)).trans
    apply mul_le_mul_of_nonneg_left _ hC
    rw [Real.rpow_neg_eq_inv_rpow]
    have H := rpow_sub_le_add_one (show 0 ≤ 1-a n by linarith [ha1 n])
      (show 1-a n ≤ 1 by linarith [ha n]) (inv_nonneg.mpr hpy.le)
    simpa only [sub_sub_cancel,add_comm] using H
  · filter_upwards [hp] with y hy
    have H := (Real.continuous_const_rpow hy.ne').tendsto 0
    have H' := H.comp (by simpa using halim.neg)
    simpa only [neg_zero,Real.rpow_zero,mul_one,Function.comp_def] using
      tendsto_const_nhds.mul H'
end WeakHessian

open Set Filter
open scoped Topology

end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_SigmaCoeffExpLower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter

attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology
open Set Filter MeasureTheory InformationTheory
open Set Filter
open scoped Topology

namespace WeakHessian
open scoped ENNReal

lemma sigmaCoeff_exp_lower {K N t θ : ℝ} (hN : 0 < N)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (hθ : 0 ≤ θ) :
    ENNReal.ofReal (t*Real.exp (K*θ^2*(1-t^2)/(6*N))) ≤ sigmaCoeff K N t θ := by
  rcases ht.eq_or_lt with rfl | ht
  · norm_num [sigmaCoeff]
  rcases ht1.eq_or_lt with rfl | ht1
  · norm_num [sigmaCoeff]
  unfold sigmaCoeff
  simp only [not_le_of_gt ht,not_le_of_gt ht1,ite_false]
  split_ifs with hzero hK hcut hKzero
  · simp [hzero]
  · apply ENNReal.ofReal_le_ofReal
    have hθpos : 0 < θ := lt_of_le_of_ne hθ (Ne.symm hzero)
    have hroot : 0 < Real.sqrt (K/N) := Real.sqrt_pos.mpr (div_pos hK hN)
    have hx : 0 < θ * Real.sqrt (K/N) := mul_pos hθpos hroot
    have hsq : (θ * Real.sqrt (K/N))^2 * N = K*θ^2 := by
      rw [mul_pow, Real.sq_sqrt (div_pos hK hN).le]
      field_simp
    have hslt : (θ * Real.sqrt (K/N))^2 < Real.pi^2 := by
      apply (mul_lt_mul_iff_left₀ hN).mp
      rw [hsq]
      nlinarith [hcut]
    have hpi : θ * Real.sqrt (K/N) < Real.pi := by nlinarith [Real.pi_pos]
    have he : (1-t^2)*(θ*Real.sqrt (K/N))^2/6 = K*θ^2*(1-t^2)/(6*N) := by
      rw [mul_pow,Real.sq_sqrt (div_pos hK hN).le]
      field_simp
    simpa only [he,mul_assoc] using sin_ratio_exp_lower ht ht1.le hx hpi
  · exact le_top
  · simp [hKzero]
  · apply ENNReal.ofReal_le_ofReal
    have hKneg : K < 0 := lt_of_le_of_ne (not_lt.mp hK) hKzero
    have hθpos : 0 < θ := lt_of_le_of_ne hθ (Ne.symm hzero)
    have hroot : 0 < Real.sqrt (-K/N) := Real.sqrt_pos.mpr (div_pos (neg_pos.mpr hKneg) hN)
    have hx : 0 < θ * Real.sqrt (-K/N) := mul_pos hθpos hroot
    have hsq : (θ * Real.sqrt (-K/N))^2 * N = -K*θ^2 := by
      rw [mul_pow, Real.sq_sqrt (div_pos (neg_pos.mpr hKneg) hN).le]
      field_simp
    have he : -((1-t^2)*(θ*Real.sqrt (-K/N))^2/6) = K*θ^2*(1-t^2)/(6*N) := by
      rw [mul_pow,Real.sq_sqrt (div_pos (neg_pos.mpr hKneg) hN).le]
      field_simp
    simpa only [he,mul_assoc] using sinh_ratio_exp_lower ht ht1.le hx

lemma tauCoeff_exp_lower {K N t θ : ℝ} (hN : 1 < N)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (hθ : 0 ≤ θ) :
    ENNReal.ofReal (t*Real.exp (K*θ^2*(1-t^2)/(6*N))) ≤ tauCoeff K N t θ := by
  rcases ht.eq_or_lt with rfl | ht
  · simp only [zero_mul,ENNReal.ofReal_zero]
    exact bot_le
  have hN0 : 0 < N := by linarith
  have hNm : 0 < N-1 := by linarith
  have hq : 0 ≤ (N-1)/N := (div_pos hNm hN0).le
  have H := mul_le_mul_right
    (ENNReal.rpow_le_rpow (sigmaCoeff_exp_lower (K := K) hNm ht.le ht1 hθ) hq)
    ((ENNReal.ofReal t)^(1/N))
  change _ ≤ tauCoeff K N t θ at H
  have he : (t:ℝ)^(1/N) *
      (t*Real.exp (K*θ^2*(1-t^2)/(6*(N-1))))^((N-1)/N) =
      t*Real.exp (K*θ^2*(1-t^2)/(6*N)) := by
    rw [Real.mul_rpow ht.le (Real.exp_pos _).le,← mul_assoc,← Real.rpow_add ht,
      show 1/N+(N-1)/N=1 by field_simp; ring,Real.rpow_one,← Real.exp_mul]
    congr 2
    field_simp
  rw [ENNReal.ofReal_rpow_of_pos ht,
    ENNReal.ofReal_rpow_of_pos (mul_pos ht (Real.exp_pos _)),
    ← ENNReal.ofReal_mul (Real.rpow_pos_of_pos ht _).le,he] at H
  exact H
end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Entropy_TauDensityLinearLower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter

attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology
open Set Filter MeasureTheory InformationTheory
open Set Filter
open scoped Topology

namespace WeakHessian
open MeasureTheory
open scoped ENNReal

lemma tau_density_linear_lower {K N s θ : ℝ} (hN : 1 < N)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (hθ : 0 ≤ θ) {r : ℝ≥0∞} (hr : 0 < r) (hrt : r ≠ ∞) :
    ENNReal.ofReal (s*r.toReal^(-1/N) + (1/N)*(K*s*(1-s^2)/6)*(θ^2*r.toReal^(-1/N))) ≤
      tauCoeff K N s θ * r^(-1/N) := by
  have hrp : 0 < r.toReal := ENNReal.toReal_pos hr.ne' hrt
  have he : ENNReal.ofReal (r.toReal^(-1/N)) = r^(-1/N) := by
    rw [← ENNReal.ofReal_rpow_of_pos hrp,ENNReal.ofReal_toReal hrt]
  have H := mul_le_mul_left (tauCoeff_exp_lower (K := K) hN hs hs1 hθ) (r^(-1/N))
  apply le_trans _ H
  rw [← he,← ENNReal.ofReal_mul (mul_nonneg hs (Real.exp_pos _).le)]
  apply ENNReal.ofReal_le_ofReal
  have Hexp := Real.add_one_le_exp (K*θ^2*(1-s^2)/(6*N))
  have HH := mul_le_mul_of_nonneg_left Hexp (mul_nonneg hs (Real.rpow_nonneg hrp.le (-1/N)))
  exact le_trans (le_of_eq (by field_simp; ring)) (le_trans HH (le_of_eq (by ring)))

lemma integral_le_of_lintegral_ofReal_le {Y : Type*} [MeasurableSpace Y]
    {π : Measure Y} [IsFiniteMeasure π] {f : Y → ℝ} (hi : Integrable f π)
    {R : ℝ} (hR : 0 ≤ R) (h : (∫⁻ y, ENNReal.ofReal (f y) ∂π) ≤ ENNReal.ofReal R) :
    (∫ y, f y ∂π) ≤ R := by
  have hp : Integrable (fun y => max (f y) 0) π := hi.pos_part
  have H : ENNReal.ofReal (∫ y, max (f y) 0 ∂π) ≤ ENNReal.ofReal R := by
    rw [ofReal_integral_eq_lintegral_ofReal hp (Eventually.of_forall fun y => le_max_right _ _)]
    have hmax : ∀ y, ENNReal.ofReal (max (f y) 0) = ENNReal.ofReal (f y) := by
      intro y
      rw [ENNReal.ofReal_max,ENNReal.ofReal_zero]
      exact max_eq_left bot_le
    simpa only [hmax] using h
  exact (integral_mono hi hp (fun y => le_max_left _ _)).trans
    ((ENNReal.ofReal_le_ofReal_iff hR).mp H)
end WeakHessian

namespace WeakHessian
open MeasureTheory InformationTheory
open scoped ENNReal

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
lemma renyiIntegral_ofReal {m μ : Measure X} [IsFiniteMeasure m] [IsFiniteMeasure μ]
    {N : ℝ} (hN : 1 < N) :
    renyiIntegral m μ N = ENNReal.ofReal (∫ x, (μ.rnDeriv m x).toReal^(1-1/N) ∂m) := by
  have ha : 0 ≤ 1/N := by positivity
  have ha1 : 1/N < 1 := (div_lt_one (by linarith : 0<N)).mpr hN
  rw [ofReal_integral_eq_lintegral_ofReal
    (integrable_rpow_sub Measure.integrable_toReal_rnDeriv
      (Eventually.of_forall fun x => ENNReal.toReal_nonneg) ha ha1)
    (Eventually.of_forall fun x => Real.rpow_nonneg ENNReal.toReal_nonneg _)]
  apply lintegral_congr_ae
  filter_upwards [Measure.rnDeriv_lt_top μ m] with x hx
  rw [ENNReal.toReal_rpow,ENNReal.ofReal_toReal
    (ENNReal.rpow_ne_top_of_nonneg (by linarith : 0 ≤ 1-1/N) hx.ne)]

lemma integrable_density_neg_rpow_comp {m μ : Measure X} [IsFiniteMeasure m] [IsFiniteMeasure μ]
    {π : Measure Y} (hac : μ ≪ m) {e : Y → X} (he : Measurable e)
    (hmap : Measure.map e π = μ) {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) :
    Integrable (fun y => (μ.rnDeriv m (e y)).toReal^(-a)) π := by
  have H : Integrable (fun x => (μ.rnDeriv m x).toReal^(-a)) (Measure.map e π) := by
    simpa only [hmap] using integrable_density_neg_rpow hac ha ha1
  exact H.comp_measurable he

lemma integral_density_neg_rpow_comp {m μ : Measure X} [IsFiniteMeasure m] [IsFiniteMeasure μ]
    {π : Measure Y} (hac : μ ≪ m) {e : Y → X} (he : Measurable e)
    (hmap : Measure.map e π = μ) {a : ℝ} (ha : a < 1) :
    (∫ y, (μ.rnDeriv m (e y)).toReal^(-a) ∂π) =
      ∫ x, (μ.rnDeriv m x).toReal^(1-a) ∂m := by
  have H := integral_map (μ := π) he.aemeasurable
    (((Measure.measurable_rnDeriv μ m).ennreal_toReal.pow_const (-a)).aestronglyMeasurable)
  rw [hmap] at H
  exact H.symm.trans (integral_density_neg_rpow hac ha)

lemma cd_renyi_gap_bound {m μ₀ μ₁ μt : Measure X} [IsFiniteMeasure m]
    [IsProbabilityMeasure μ₀] [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μt]
    {π : Measure Y} [IsProbabilityMeasure π] {e₀ e₁ : Y → X}
    (he₀ : Measurable e₀) (he₁ : Measurable e₁)
    (hm₀ : Measure.map e₀ π = μ₀) (hm₁ : Measure.map e₁ π = μ₁)
    (hac₀ : μ₀ ≪ m) (hac₁ : μ₁ ≪ m)
    {θ : Y → ℝ} (hθ : Measurable θ) (hθ0 : ∀ᵐ y ∂π, 0 ≤ θ y)
    {C : ℝ} (hb : ∀ᵐ y ∂π, θ y ^ 2 ≤ C) {K N t : ℝ}
    (hN : 1 < N) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hcd : (∫⁻ y, tauCoeff K N (1-t) (θ y)*(μ₀.rnDeriv m (e₀ y))^(-1/N) +
      tauCoeff K N t (θ y)*(μ₁.rnDeriv m (e₁ y))^(-1/N) ∂π) ≤ renyiIntegral m μt N) :
    (1-∫ x, (μt.rnDeriv m x).toReal^(1-1/N) ∂m)/(1/N) ≤
      (1-t)*((1-∫ x, (μ₀.rnDeriv m x).toReal^(1-1/N) ∂m)/(1/N)) +
      t*((1-∫ x, (μ₁.rnDeriv m x).toReal^(1-1/N) ∂m)/(1/N)) -
      K*(1-t)*(1-(1-t)^2)/6*(∫ y, θ y^2*(μ₀.rnDeriv m (e₀ y)).toReal^(-1/N) ∂π) -
      K*t*(1-t^2)/6*(∫ y, θ y^2*(μ₁.rnDeriv m (e₁ y)).toReal^(-1/N) ∂π) := by
  have ha : 0 < 1/N := by positivity
  have ha1 : 1/N < 1 := (div_lt_one (by linarith : 0<N)).mpr hN
  have heq : -(1/N) = -1/N := by ring
  have hi₀ := integrable_density_neg_rpow_comp hac₀ he₀ hm₀ ha.le ha1
  have hi₁ := integrable_density_neg_rpow_comp hac₁ he₁ hm₁ ha.le ha1
  rw [heq] at hi₀ hi₁
  have hθb : ∀ᵐ y ∂π, ‖θ y^2‖ ≤ C := hb.mono fun y hy => by
    rwa [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  have hc₀ := hi₀.bdd_mul (hθ.pow_const 2).aestronglyMeasurable hθb
  have hc₁ := hi₁.bdd_mul (hθ.pow_const 2).aestronglyMeasurable hθb
  let f : Y → ℝ := fun y =>
    (1-t)*(μ₀.rnDeriv m (e₀ y)).toReal^(-1/N) +
      (1/N)*(K*(1-t)*(1-(1-t)^2)/6)*(θ y^2*(μ₀.rnDeriv m (e₀ y)).toReal^(-1/N)) +
    (t*(μ₁.rnDeriv m (e₁ y)).toReal^(-1/N) +
      (1/N)*(K*t*(1-t^2)/6)*(θ y^2*(μ₁.rnDeriv m (e₁ y)).toReal^(-1/N)))
  have hfi : Integrable f π :=
    ((hi₀.const_mul _).add (hc₀.const_mul _)).add ((hi₁.const_mul _).add (hc₁.const_mul _))
  have hp₀ : ∀ᵐ y ∂π, 0 < μ₀.rnDeriv m (e₀ y) ∧ μ₀.rnDeriv m (e₀ y) ≠ ∞ := by
    have H : ∀ᵐ x ∂Measure.map e₀ π, 0 < μ₀.rnDeriv m x ∧ μ₀.rnDeriv m x ≠ ∞ := by
      rw [hm₀]
      filter_upwards [Measure.rnDeriv_pos hac₀, hac₀.ae_le (Measure.rnDeriv_lt_top μ₀ m)] with x hp ht
      exact ⟨hp,ht.ne⟩
    exact ae_of_ae_map he₀.aemeasurable H
  have hp₁ : ∀ᵐ y ∂π, 0 < μ₁.rnDeriv m (e₁ y) ∧ μ₁.rnDeriv m (e₁ y) ≠ ∞ := by
    have H : ∀ᵐ x ∂Measure.map e₁ π, 0 < μ₁.rnDeriv m x ∧ μ₁.rnDeriv m x ≠ ∞ := by
      rw [hm₁]
      filter_upwards [Measure.rnDeriv_pos hac₁, hac₁.ae_le (Measure.rnDeriv_lt_top μ₁ m)] with x hp ht
      exact ⟨hp,ht.ne⟩
    exact ae_of_ae_map he₁.aemeasurable H
  have H : (∫ y, f y ∂π) ≤ ∫ x, (μt.rnDeriv m x).toReal^(1-1/N) ∂m := by
    apply integral_le_of_lintegral_ofReal_le hfi
      (integral_nonneg fun x => Real.rpow_nonneg ENNReal.toReal_nonneg _)
    rw [← renyiIntegral_ofReal hN]
    apply le_trans (lintegral_mono_ae ?_) hcd
    filter_upwards [hp₀,hp₁,hθ0] with y hy₀ hy₁ hyθ
    exact ENNReal.ofReal_add_le.trans (add_le_add
      (tau_density_linear_lower (K := K) hN (by linarith) (by linarith) hyθ hy₀.1 hy₀.2)
      (tau_density_linear_lower (K := K) hN ht ht1 hyθ hy₁.1 hy₁.2))
  have H₀ := integral_density_neg_rpow_comp hac₀ he₀ hm₀ ha1
  have H₁ := integral_density_neg_rpow_comp hac₁ he₁ hm₁ ha1
  rw [heq] at H₀ H₁
  dsimp only [f] at H
  have HS := integral_add
    ((hi₀.const_mul (1-t)).add (hc₀.const_mul ((1/N)*(K*(1-t)*(1-(1-t)^2)/6))))
    ((hi₁.const_mul t).add (hc₁.const_mul ((1/N)*(K*t*(1-t^2)/6))))
  have HS₀ := integral_add (hi₀.const_mul (1-t)) (hc₀.const_mul ((1/N)*(K*(1-t)*(1-(1-t)^2)/6)))
  have HS₁ := integral_add (hi₁.const_mul t) (hc₁.const_mul ((1/N)*(K*t*(1-t^2)/6)))
  simp only [Pi.add_apply] at HS HS₀ HS₁
  rw [HS,HS₀,HS₁] at H
  simp only [integral_const_mul,H₀,H₁] at H
  apply (div_le_iff₀ ha).mpr
  field_simp at H ⊢
  nlinarith
end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Entropy_TendstoRenyiGap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter

attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology
open Set Filter MeasureTheory InformationTheory
open Set Filter
open scoped Topology

namespace WeakHessian
open MeasureTheory InformationTheory
open scoped ENNReal

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

lemma tendsto_renyi_gap {m μ : Measure X} [IsFiniteMeasure m] [IsProbabilityMeasure μ]
    (hE : FiniteEntropy m μ) {a : ℕ → ℝ}
    (ha : ∀ n, 0 < a n) (ha1 : ∀ n, a n < 1) (halim : Tendsto a atTop (𝓝 0)) :
    Tendsto (fun n => (1-∫ x, (μ.rnDeriv m x).toReal^(1-a n) ∂m)/(a n))
      atTop (𝓝 (entropyReal m μ)) := by
  have hi : Integrable (fun x => (μ.rnDeriv m x).toReal) m := Measure.integrable_toReal_rnDeriv
  have hn : ∀ᵐ x ∂m, 0 ≤ (μ.rnDeriv m x).toReal := Eventually.of_forall fun x => ENNReal.toReal_nonneg
  have H := tendsto_integral_renyiKernel hi hn
    ((integrable_klFun_rnDeriv_iff hE.1).mpr hE.2) ha ha1 halim
  have heq : ∀ n, (∫ x, renyiKernel (a n) (μ.rnDeriv m x).toReal ∂m) =
      (1-∫ x, (μ.rnDeriv m x).toReal^(1-a n) ∂m)/(a n) + m.real Set.univ-1 := by
    intro n
    simp only [renyiKernel]
    rw [integral_sub,integral_add,integral_div,integral_sub,
      Measure.integral_toReal_rnDeriv hE.1,probReal_univ (μ := μ),integral_const,smul_eq_mul,mul_one]
    · exact hi
    · exact integrable_rpow_sub hi hn (ha n).le (ha1 n)
    · exact (hi.sub (integrable_rpow_sub hi hn (ha n).le (ha1 n))).div_const _
    · exact integrable_const 1
    · exact ((hi.sub (integrable_rpow_sub hi hn (ha n).le (ha1 n))).div_const _).add (integrable_const 1)
    · exact hi
  simp only [heq] at H
  rw [integral_klFun_rnDeriv hE.1 hE.2,probReal_univ (μ := μ)] at H
  have HH := (H.sub_const (m.real Set.univ)).add_const 1
  have alg : ∀ x y : ℝ, x+y-1-y+1 = x := by intros; ring
  simpa only [alg,entropyReal] using HH

lemma cd_entropy_bound_of_dimensions {m μ₀ μ₁ μt : Measure X} [IsFiniteMeasure m]
    [IsProbabilityMeasure μ₀] [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μt]
    {π : Measure Y} [IsProbabilityMeasure π] {e₀ e₁ : Y → X}
    (he₀ : Measurable e₀) (he₁ : Measurable e₁)
    (hm₀ : Measure.map e₀ π = μ₀) (hm₁ : Measure.map e₁ π = μ₁)
    (hE₀ : FiniteEntropy m μ₀) (hE₁ : FiniteEntropy m μ₁)
    {θ : Y → ℝ} (hθ : Measurable θ) (hθ0 : ∀ᵐ y ∂π, 0 ≤ θ y)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ᵐ y ∂π, θ y ^ 2 ≤ C) {K t : ℝ}
    (ht : 0 ≤ t) (ht1 : t ≤ 1) {d : ℕ → ℝ} (hd : ∀ n, 1 < d n)
    (hdlim : Tendsto (fun n => 1/d n) atTop (𝓝 0))
    (hcd : ∀ n, (∫⁻ y, tauCoeff K (d n) (1-t) (θ y)*(μ₀.rnDeriv m (e₀ y))^(-1/(d n)) +
      tauCoeff K (d n) t (θ y)*(μ₁.rnDeriv m (e₁ y))^(-1/(d n)) ∂π) ≤ renyiIntegral m μt (d n)) :
    FiniteEntropy m μt ∧ entropyReal m μt ≤ (1-t)*entropyReal m μ₀+t*entropyReal m μ₁ -
      K/2*t*(1-t)*(∫ y, θ y^2 ∂π) := by
  have ha : ∀ n, 0 < 1/d n := fun n => one_div_pos.mpr (lt_trans zero_lt_one (hd n))
  have ha1 : ∀ n, 1/d n < 1 := fun n => (div_lt_one (lt_trans zero_lt_one (hd n))).mpr (hd n)
  have HL₀ := tendsto_renyi_gap hE₀ ha ha1 hdlim
  have HL₁ := tendsto_renyi_gap hE₁ ha ha1 hdlim
  have hψ : AEStronglyMeasurable (fun y => θ y^2) π := (hθ.pow_const 2).aestronglyMeasurable
  have hb' : ∀ᵐ y ∂π, |θ y^2| ≤ C := hb.mono fun y hy => by rwa [abs_of_nonneg (sq_nonneg _)]
  have HC₀ := tendsto_integral_weighted_density_neg_rpow hE₀.1 he₀ hm₀ hψ hC hb'
    (fun n => (ha n).le) (fun n => (ha1 n).le) hdlim
  have HC₁ := tendsto_integral_weighted_density_neg_rpow hE₁.1 he₁ hm₁ hψ hC hb'
    (fun n => (ha n).le) (fun n => (ha1 n).le) hdlim
  simp only [← neg_div] at HC₀ HC₁
  have HL := (((HL₀.const_mul (1-t)).add (HL₁.const_mul t)).sub
    (HC₀.const_mul (K*(1-t)*(1-(1-t)^2)/6))).sub (HC₁.const_mul (K*t*(1-t^2)/6))
  have HE := finiteEntropy_of_renyi_gaps ha ha1 hdlim HL
    (fun n => cd_renyi_gap_bound he₀ he₁ hm₀ hm₁ hE₀.1 hE₁.1 hθ hθ0 hb (hd n) ht ht1 (hcd n))
  refine ⟨HE.1,HE.2.trans_eq ?_⟩
  ring
end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Entropy_CdEntropyBoundFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter

attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology
open Set Filter MeasureTheory InformationTheory
open Set Filter
open scoped Topology

namespace WeakHessian
open MeasureTheory InformationTheory
open scoped ENNReal

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

lemma cd_entropy_bound_on_finite_region {m μ₀ μ₁ μt : Measure X} [SigmaFinite m]
    [IsProbabilityMeasure μ₀] [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μt]
    {π : Measure Y} [IsProbabilityMeasure π] {e₀ e₁ : Y → X}
    (he₀ : Measurable e₀) (he₁ : Measurable e₁)
    (hm₀ : Measure.map e₀ π = μ₀) (hm₁ : Measure.map e₁ π = μ₁)
    (hE₀ : FiniteEntropy m μ₀) (hE₁ : FiniteEntropy m μ₁)
    {Q : Set X} (hQ : MeasurableSet Q) (hQfin : m Q < ∞)
    (hs₀ : ∀ᵐ x ∂μ₀, x ∈ Q) (hs₁ : ∀ᵐ x ∂μ₁, x ∈ Q) (hst : ∀ᵐ x ∂μt, x ∈ Q)
    {θ : Y → ℝ} (hθ : Measurable θ) (hθ0 : ∀ᵐ y ∂π, 0 ≤ θ y)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ᵐ y ∂π, θ y ^ 2 ≤ C) {K t : ℝ}
    (ht : 0 ≤ t) (ht1 : t ≤ 1) {d : ℕ → ℝ} (hd : ∀ n, 1 < d n)
    (hdlim : Tendsto (fun n => 1/d n) atTop (𝓝 0))
    (hcd : ∀ n, (∫⁻ y, tauCoeff K (d n) (1-t) (θ y)*(μ₀.rnDeriv m (e₀ y))^(-1/(d n)) +
      tauCoeff K (d n) t (θ y)*(μ₁.rnDeriv m (e₁ y))^(-1/(d n)) ∂π) ≤ renyiIntegral m μt (d n)) :
    FiniteEntropy m μt ∧ entropyReal m μt ≤ (1-t)*entropyReal m μ₀+t*entropyReal m μ₁ -
      K/2*t*(1-t)*(∫ y, θ y^2 ∂π) := by
  let : IsFiniteMeasure (m.restrict Q) := ⟨by simpa using hQfin⟩
  have HE₀ := (finiteEntropy_restrict_reference_iff hQ hs₀).mpr hE₀
  have HE₁ := (finiteEntropy_restrict_reference_iff hQ hs₁).mpr hE₁
  have hr₀ : ∀ᵐ y ∂π, μ₀.rnDeriv m (e₀ y) = μ₀.rnDeriv (m.restrict Q) (e₀ y) := by
    have H : ∀ᵐ x ∂Measure.map e₀ π, μ₀.rnDeriv m x = μ₀.rnDeriv (m.restrict Q) x := by
      rw [hm₀]
      exact rnDeriv_restrict_reference_ae hQ hE₀.1 hs₀
    exact ae_of_ae_map he₀.aemeasurable H
  have hr₁ : ∀ᵐ y ∂π, μ₁.rnDeriv m (e₁ y) = μ₁.rnDeriv (m.restrict Q) (e₁ y) := by
    have H : ∀ᵐ x ∂Measure.map e₁ π, μ₁.rnDeriv m x = μ₁.rnDeriv (m.restrict Q) x := by
      rw [hm₁]
      exact rnDeriv_restrict_reference_ae hQ hE₁.1 hs₁
    exact ae_of_ae_map he₁.aemeasurable H
  have H := cd_entropy_bound_of_dimensions (μt := μt) (K := K) he₀ he₁ hm₀ hm₁ HE₀ HE₁ hθ hθ0 hC hb ht ht1 hd hdlim
    (fun n => ?_)
  · have HE := (finiteEntropy_restrict_reference_iff hQ hst).mp H.1
    refine ⟨HE,?_⟩
    simpa only [entropyReal_restrict_reference hQ HE.1 hst,
      entropyReal_restrict_reference hQ hE₀.1 hs₀,entropyReal_restrict_reference hQ hE₁.1 hs₁] using H.2
  · rw [← renyiIntegral_restrict_reference hQ hst (hd n)]
    refine (lintegral_congr_ae ?_).trans_le (hcd n)
    filter_upwards [hr₀,hr₁] with y hy₀ hy₁
    rw [hy₀,hy₁]
end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Entropy_CenteredMulLogDeriv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter

attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory InformationTheory
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace WeakHessian
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

lemma centered_mul_log_hasDeriv {B x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun r : ℝ => r*Real.log r-(Real.log B+1)*r)
      (Real.log x-Real.log B) x := by
  convert (Real.hasDerivAt_mul_log hx).sub ((hasDerivAt_id x).const_mul (Real.log B+1)) using 1 <;> first | rfl | ring

lemma centered_mul_log_antitone {B : ℝ} (hB : 0 < B) :
    AntitoneOn (fun r : ℝ => r*Real.log r-(Real.log B+1)*r) (Icc 0 B) := by
  apply antitoneOn_of_deriv_nonpos (f := fun r : ℝ => r*Real.log r-(Real.log B+1)*r) (convex_Icc _ _)
    ((Real.continuous_mul_log.sub (continuous_const.mul continuous_id)).continuousOn)
  · intro x hx
    rw [interior_Icc] at hx
    exact (centered_mul_log_hasDeriv hx.1.ne').differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    rw [(centered_mul_log_hasDeriv (B := B) hx.1.ne').deriv]
    exact sub_nonpos.mpr (Real.strictMonoOn_log.monotoneOn hx.1 hB hx.2.le)

lemma centered_mul_log_monotone {B : ℝ} (hB : 0 < B) :
    MonotoneOn (fun r : ℝ => r*Real.log r-(Real.log B+1)*r) (Ici B) := by
  apply monotoneOn_of_deriv_nonneg (f := fun r : ℝ => r*Real.log r-(Real.log B+1)*r) (convex_Ici _)
    ((Real.continuous_mul_log.sub (continuous_const.mul continuous_id)).continuousOn)
  · intro x hx
    rw [interior_Ici] at hx
    exact (centered_mul_log_hasDeriv (hB.trans hx).ne').differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    rw [(centered_mul_log_hasDeriv (B := B) (hB.trans hx).ne').deriv]
    exact sub_nonneg.mpr (Real.log_le_log hB hx.le)

lemma centered_mul_log_le_of_between {B r s : ℝ} (hB : 0 < B)
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hrB : r ≤ B) (hmin : min s B ≤ r) :
    r*Real.log r-(Real.log B+1)*r ≤ s*Real.log s-(Real.log B+1)*s := by
  by_cases hsB : s ≤ B
  · rw [min_eq_left hsB] at hmin
    exact centered_mul_log_antitone hB ⟨hs,hsB⟩ ⟨hr,hrB⟩ hmin
  · have hBs := le_of_not_ge hsB
    rw [min_eq_right hBs] at hmin
    have he : r = B := le_antisymm hrB hmin
    rw [he]
    exact centered_mul_log_monotone hB (by change B ≤ B; exact le_refl B) (by simpa only [mem_Ici] using hBs) hBs

variable {X : Type*} [MeasurableSpace X]

lemma ae_le_of_withDensity_le {m : Measure X} [SigmaFinite m]
    {f g : X → ℝ≥0∞} (hf : AEMeasurable f m) (h : m.withDensity f ≤ m.withDensity g) :
    f ≤ᵐ[m] g := by
  apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite₀ hf
  intro A hA _
  simpa only [← withDensity_apply _ hA] using h A

lemma rnDeriv_le_of_domination {m μ : Measure X} [SigmaFinite m] [IsFiniteMeasure μ]
    {B : ℝ≥0∞} (h : μ ≤ B • m) (hac : μ ≪ m) : μ.rnDeriv m ≤ᵐ[m] fun _ => B := by
  apply ae_le_of_withDensity_le (Measure.measurable_rnDeriv _ _).aemeasurable
  rw [Measure.withDensity_rnDeriv_eq μ m hac,withDensity_const]
  exact h

lemma finiteEntropy_of_bounded_density {m μ : Measure X} [IsFiniteMeasure m] [IsFiniteMeasure μ]
    {B : ℝ≥0∞} (hBt : B ≠ ∞) (hd : μ ≤ B • m) : FiniteEntropy m μ := by
  have hac : μ ≪ m := (Measure.absolutelyContinuous_of_le hd).trans
    (Measure.AbsolutelyContinuous.rfl.smul_left B)
  refine ⟨hac,(integrable_rnDeriv_mul_log_iff hac).mp ?_⟩
  obtain ⟨M,hM⟩ := (isCompact_Icc (a := (0:ℝ)) (b := B.toReal)).exists_bound_of_continuousOn
    (f := fun r : ℝ => r*Real.log r) Real.continuous_mul_log.continuousOn
  apply (integrable_const M).mono'
    (Real.continuous_mul_log.measurable.comp (Measure.measurable_rnDeriv μ m).ennreal_toReal).aestronglyMeasurable
  filter_upwards [rnDeriv_le_of_domination hd hac] with x hx
  exact hM _ ⟨ENNReal.toReal_nonneg,ENNReal.toReal_mono hBt hx⟩

lemma entropyReal_le_of_density_capping {m : Measure X} [IsFiniteMeasure m]
    (μ η : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure η]
    (hE : FiniteEntropy m μ) {B : ℝ≥0∞} (hB : B ≠ 0) (hBt : B ≠ ∞)
    (hη : η ≤ B • m)
    (hlo : m.withDensity (fun x => min (μ.rnDeriv m x) B) ≤ η) :
    FiniteEntropy m η ∧ entropyReal m η ≤ entropyReal m μ := by
  have hEη := finiteEntropy_of_bounded_density hBt hη
  have hηr := rnDeriv_le_of_domination hη hEη.1
  have hl : (fun x => min (μ.rnDeriv m x) B) ≤ᵐ[m] η.rnDeriv m := by
    apply ae_le_of_withDensity_le ((Measure.measurable_rnDeriv _ _).min measurable_const).aemeasurable
    rwa [Measure.withDensity_rnDeriv_eq η m hEη.1]
  have hpoint : ∀ᵐ x ∂m,
      (η.rnDeriv m x).toReal*Real.log (η.rnDeriv m x).toReal -
        (Real.log B.toReal+1)*(η.rnDeriv m x).toReal ≤
      (μ.rnDeriv m x).toReal*Real.log (μ.rnDeriv m x).toReal -
        (Real.log B.toReal+1)*(μ.rnDeriv m x).toReal := by
    filter_upwards [hηr,hl,Measure.rnDeriv_lt_top μ m,Measure.rnDeriv_lt_top η m] with x hx hlx hμt hηt
    apply centered_mul_log_le_of_between (ENNReal.toReal_pos hB hBt)
      ENNReal.toReal_nonneg ENNReal.toReal_nonneg (ENNReal.toReal_mono hBt hx)
    rw [← ENNReal.toReal_min hμt.ne hBt]
    exact ENNReal.toReal_mono hηt.ne hlx
  have hIμ := (integrable_rnDeriv_mul_log_iff hE.1).mpr hE.2
  have hIη := (integrable_rnDeriv_mul_log_iff hEη.1).mpr hEη.2
  have hlinμ : Integrable (fun x => (Real.log B.toReal+1)*(μ.rnDeriv m x).toReal) m :=
    Measure.integrable_toReal_rnDeriv.const_mul _
  have hlinη : Integrable (fun x => (Real.log B.toReal+1)*(η.rnDeriv m x).toReal) m :=
    Measure.integrable_toReal_rnDeriv.const_mul _
  have H := integral_mono_ae (hIη.sub hlinη) (hIμ.sub hlinμ) hpoint
  simp only [Pi.sub_apply] at H
  rw [integral_sub hIη hlinη,integral_sub hIμ hlinμ,
    integral_const_mul,integral_const_mul,
    Measure.integral_toReal_rnDeriv hEη.1,Measure.integral_toReal_rnDeriv hE.1,
    probReal_univ,probReal_univ,mul_one] at H
  refine ⟨hEη,?_⟩
  rw [entropyReal_eq_integral_density hEη.1,entropyReal_eq_integral_density hE.1]
  linarith
end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_BoundedEndpointTube
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
namespace WeakHessian
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

def boundedEndpointTube (o : X) (R : ℝ) : Set (Curve X) :=
  {γ | IsGeodesic γ ∧ dist (γ timeZero) o ≤ R ∧ dist (γ timeOne) o ≤ R}

omit [MeasurableSpace X] [BorelSpace X] in
lemma isClosed_boundedEndpointTube (o : X) (R : ℝ) : IsClosed (boundedEndpointTube o R) :=
  isClosed_isGeodesic.inter
    ((isClosed_le ((continuous_eval_const timeZero).dist continuous_const) continuous_const).inter
      (isClosed_le ((continuous_eval_const timeOne).dist continuous_const) continuous_const))

omit [MeasurableSpace X] [BorelSpace X] in
lemma boundedEndpointTube_length_le {o : X} {R : ℝ} {γ : Curve X}
    (hγ : γ ∈ boundedEndpointTube o R) : dist (γ timeZero) (γ timeOne) ≤ 2*R := by
  have H := dist_triangle (γ timeZero) o (γ timeOne)
  rw [dist_comm o (γ timeOne)] at H
  linarith [hγ.2.1,hγ.2.2]

omit [MeasurableSpace X] [BorelSpace X] in
lemma boundedEndpointTube_range {o : X} {R : ℝ} {γ : Curve X}
    (hγ : γ ∈ boundedEndpointTube o R) (t : Time) : γ t ∈ Metric.closedBall o (3*R) := by
  have H := hγ.1 t timeZero
  have htime : |(t:ℝ)-(timeZero:ℝ)| ≤ 1 := by
    change |(t:ℝ)-0| ≤ 1
    simpa only [sub_zero,abs_of_nonneg t.property.1] using t.property.2
  have hend := boundedEndpointTube_length_le hγ
  have hdist : dist (γ t) (γ timeZero) ≤ 2*R := by
    rw [H]
    exact (mul_le_of_le_one_left dist_nonneg htime).trans hend
  rw [Metric.mem_closedBall]
  exact (dist_triangle _ _ _).trans (by linarith [hγ.2.1])

omit [MeasurableSpace X] [BorelSpace X] in
lemma isCompact_boundedEndpointTube [ProperSpace X] (o : X) (R : ℝ≥0) :
    IsCompact (boundedEndpointTube o R) := by
  apply isCompact_curve_family _ (isClosed_boundedEndpointTube o R)
    (Metric.closedBall o (3*(R:ℝ))) (isCompact_closedBall _ _) (2*R)
  · exact fun γ hγ t => boundedEndpointTube_range hγ t
  · intro γ hγ
    apply LipschitzWith.of_dist_le_mul
    intro s t
    rw [hγ.1 s t]
    rw [Subtype.dist_eq,Real.dist_eq,mul_comm]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast boundedEndpointTube_length_le hγ) (abs_nonneg _)

lemma isCompact_probability_supported {Y : Type*} [MetricSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] {T : Set Y} (hT : IsCompact T) :
    IsCompact {π : ProbabilityMeasure Y | (π:Measure Y) Tᶜ = 0} := by
  have H := isCompact_setOfPred_probabilityMeasure_mass_eq_compl_isCompact_le
    (u := fun _ : ℕ => (0:ℝ≥0)) (K := fun _ => T) tendsto_const_nhds (fun _ => hT)
    (Or.inl inferInstance)
  convert H using 1
  all_goals try with_reducible_and_instances rfl
  ext π
  simp only [mem_ofPred_eq,nonpos_iff_eq_zero,forall_const]
  change (π:Measure Y) Tᶜ = 0 ↔ ((π:Measure Y) Tᶜ).toNNReal = 0
  simp only [ENNReal.toNNReal_eq_zero_iff,measure_ne_top,or_false]

lemma isCompact_midpoint_constraints {T : Set (Curve X)} (hT : IsCompact T)
    (μ₀ μ₁ : ProbabilityMeasure X) (f : Curve X →ᵇ ℝ) (c : ℝ) (t : Time) :
    IsCompact {μ : ProbabilityMeasure X | ∃ π : ProbabilityMeasure (Curve X),
      (π:Measure (Curve X)) Tᶜ = 0 ∧
      π.map (continuous_eval_const timeZero).aemeasurable = μ₀ ∧
      π.map (continuous_eval_const timeOne).aemeasurable = μ₁ ∧
      (∫ γ, f γ ∂(π:Measure (Curve X))) ≤ c ∧
      μ = π.map (continuous_eval_const t).aemeasurable} := by
  let S : Set (ProbabilityMeasure (Curve X)) := {π |
      (π:Measure (Curve X)) Tᶜ = 0 ∧
      π.map (continuous_eval_const timeZero).aemeasurable = μ₀ ∧
      π.map (continuous_eval_const timeOne).aemeasurable = μ₁ ∧
      (∫ γ, f γ ∂(π:Measure (Curve X))) ≤ c}
  have hc : IsCompact S := by
    apply (isCompact_probability_supported hT).inter_right
    exact (isClosed_eq (ProbabilityMeasure.continuous_map (continuous_eval_const timeZero)) continuous_const).inter
      ((isClosed_eq (ProbabilityMeasure.continuous_map (continuous_eval_const timeOne)) continuous_const).inter
        (isClosed_le (ProbabilityMeasure.continuous_integral_boundedContinuousFunction f) continuous_const))
  convert hc.image (ProbabilityMeasure.continuous_map (continuous_eval_const t)) using 1
  all_goals try with_reducible_and_instances rfl
  ext μ
  simp only [mem_ofPred_eq,mem_image,S]
  constructor
  · rintro ⟨π,hπ,h0,h1,hcost,rfl⟩
    exact ⟨π,⟨hπ,h0,h1,hcost⟩,rfl⟩
  · rintro ⟨π,⟨hπ,h0,h1,hcost⟩,rfl⟩
    exact ⟨π,hπ,h0,h1,hcost,rfl⟩

def clippedEndpointCost (R : ℝ≥0) : Curve X →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun γ => min ((dist (γ timeZero) (γ timeOne))^2) ((2*(R:ℝ))^2),
      (((continuous_eval_const timeZero).dist (continuous_eval_const timeOne)).pow 2).min continuous_const⟩
    ((2*(R:ℝ))^2) (by
      intro γ η
      change |min ((dist (γ timeZero) (γ timeOne))^2) ((2*(R:ℝ))^2) -
        min ((dist (η timeZero) (η timeOne))^2) ((2*(R:ℝ))^2)| ≤ _
      have hγ : 0 ≤ min ((dist (γ timeZero) (γ timeOne))^2) ((2*(R:ℝ))^2) := le_min (sq_nonneg _) (sq_nonneg _)
      have hη : 0 ≤ min ((dist (η timeZero) (η timeOne))^2) ((2*(R:ℝ))^2) := le_min (sq_nonneg _) (sq_nonneg _)
      exact abs_le.mpr ⟨by linarith [min_le_right ((dist (η timeZero) (η timeOne))^2) ((2*(R:ℝ))^2)],
        by linarith [min_le_right ((dist (γ timeZero) (γ timeOne))^2) ((2*(R:ℝ))^2)]⟩)

omit [MeasurableSpace X] [BorelSpace X] in
lemma clippedEndpointCost_nonneg (R : ℝ≥0) (γ : Curve X) : 0 ≤ clippedEndpointCost R γ :=
  le_min (sq_nonneg _) (sq_nonneg _)

omit [MeasurableSpace X] [BorelSpace X] in
lemma clippedEndpointCost_eq {o : X} {R : ℝ≥0} {γ : Curve X}
    (hγ : γ ∈ boundedEndpointTube o R) :
    clippedEndpointCost R γ = (dist (γ timeZero) (γ timeOne))^2 := by
  change min _ _ = _
  apply min_eq_left
  exact pow_le_pow_left₀ dist_nonneg (boundedEndpointTube_length_le hγ) 2

variable [SecondCountableTopology X]

lemma endpointCost_eq_clipped_integral (π : Measure (Curve X)) [IsFiniteMeasure π]
    {o : X} {R : ℝ≥0} (hs : π (boundedEndpointTube o R)ᶜ = 0) :
    QuadraticTransportCost (endpointCoupling π) =
      ENNReal.ofReal (∫ γ, clippedEndpointCost R γ ∂π) := by
  have hmem : ∀ᵐ γ ∂π, γ ∈ boundedEndpointTube o R := by
    exact ae_iff.mpr hs
  have hm : Measurable (fun γ : Curve X => (γ timeZero,γ timeOne)) :=
    (continuous_eval_const timeZero).measurable.prodMk (continuous_eval_const timeOne).measurable
  rw [QuadraticTransportCost,endpointCoupling,lintegral_map (measurable_fst.edist measurable_snd |>.pow_const 2) hm]
  rw [ofReal_integral_eq_lintegral_ofReal ((clippedEndpointCost R).integrable π)
    (ae_of_all _ (clippedEndpointCost_nonneg R))]
  apply lintegral_congr_ae
  filter_upwards [hmem] with γ hγ
  rw [clippedEndpointCost_eq hγ,edist_dist,ENNReal.ofReal_pow dist_nonneg]

def optimalTimeLaws (μ₀ μ₁ : ProbabilityMeasure X) (t : Time) : Set (ProbabilityMeasure X) :=
  {μ | ∃ π : ProbabilityMeasure (Curve X),
    (∀ᵐ γ ∂(π:Measure (Curve X)), IsGeodesic γ) ∧
    IsOptimalCoupling (endpointCoupling (π:Measure (Curve X))) μ₀ μ₁ ∧
    μ = π.map (continuous_eval_const t).aemeasurable}

omit [SecondCountableTopology X] in
lemma optimalPlan_supported_tube (π : ProbabilityMeasure (Curve X))
    {μ₀ μ₁ : ProbabilityMeasure X} {o : X} {R : ℝ≥0}
    (hgeo : ∀ᵐ γ ∂(π:Measure (Curve X)), IsGeodesic γ)
    (hends : IsCoupling (endpointCoupling (π:Measure (Curve X))) μ₀ μ₁)
    (h₀ : (μ₀:Measure X) (Metric.closedBall o R)ᶜ = 0)
    (h₁ : (μ₁:Measure X) (Metric.closedBall o R)ᶜ = 0) :
    (π:Measure (Curve X)) (boundedEndpointTube o R)ᶜ = 0 := by
  have he₀ : ∀ᵐ γ ∂(π:Measure (Curve X)), dist (γ timeZero) o ≤ R := by
    apply ae_of_ae_map (f := fun γ : Curve X => γ timeZero)
      (p := fun x => dist x o ≤ R) (continuous_eval_const timeZero).measurable.aemeasurable
    change ∀ᵐ x ∂interpolation (π:Measure (Curve X)) timeZero, dist x o ≤ R
    rw [hends.interpolation_endpoints.1]
    exact ae_iff.mpr h₀
  have he₁ : ∀ᵐ γ ∂(π:Measure (Curve X)), dist (γ timeOne) o ≤ R := by
    apply ae_of_ae_map (f := fun γ : Curve X => γ timeOne)
      (p := fun x => dist x o ≤ R) (continuous_eval_const timeOne).measurable.aemeasurable
    change ∀ᵐ x ∂interpolation (π:Measure (Curve X)) timeOne, dist x o ≤ R
    rw [hends.interpolation_endpoints.2]
    exact ae_iff.mpr h₁
  apply ae_iff.mp
  filter_upwards [hgeo,he₀,he₁] with γ hg h0 h1
  exact ⟨hg,h0,h1⟩

theorem isCompact_optimalTimeLaws [ProperSpace X]
    {μ₀ μ₁ : ProbabilityMeasure X} (o : X) (R : ℝ≥0)
    (h₀ : (μ₀:Measure X) (Metric.closedBall o R)ᶜ = 0)
    (h₁ : (μ₁:Measure X) (Metric.closedBall o R)ᶜ = 0) (t : Time) :
    IsCompact (optimalTimeLaws μ₀ μ₁ t) := by
  by_cases hne : (optimalTimeLaws μ₀ μ₁ t).Nonempty
  · obtain ⟨μ,π₀,hgeo₀,hopt₀,hμ⟩ := hne
    let c := ∫ γ, clippedEndpointCost R γ ∂(π₀:Measure (Curve X))
    have hc : 0 ≤ c := integral_nonneg (clippedEndpointCost_nonneg R)
    have hπs := optimalPlan_supported_tube π₀ hgeo₀ hopt₀.1 h₀ h₁
    have hcost₀ := endpointCost_eq_clipped_integral (π₀:Measure (Curve X)) hπs
    have hset : optimalTimeLaws μ₀ μ₁ t =
        {μ : ProbabilityMeasure X | ∃ π : ProbabilityMeasure (Curve X),
          (π:Measure (Curve X)) (boundedEndpointTube o R)ᶜ = 0 ∧
          π.map (continuous_eval_const timeZero).aemeasurable = μ₀ ∧
          π.map (continuous_eval_const timeOne).aemeasurable = μ₁ ∧
          (∫ γ, clippedEndpointCost R γ ∂(π:Measure (Curve X))) ≤ c ∧
          μ = π.map (continuous_eval_const t).aemeasurable} := by
      ext η
      constructor
      · rintro ⟨π,hg,ho,rfl⟩
        have hs := optimalPlan_supported_tube π hg ho.1 h₀ h₁
        refine ⟨π,hs,?_,?_,?_,rfl⟩
        · apply Subtype.ext
          exact ho.1.interpolation_endpoints.1
        · apply Subtype.ext
          exact ho.1.interpolation_endpoints.2
        · apply (ENNReal.ofReal_le_ofReal_iff hc).mp
          rw [← endpointCost_eq_clipped_integral (π:Measure (Curve X)) hs,← hcost₀]
          exact ho.2 _ hopt₀.1
      · rintro ⟨π,hs,h0,h1,hcost,rfl⟩
        have hend : IsCoupling (endpointCoupling (π:Measure (Curve X))) μ₀ μ₁ := by
          have H := endpointCoupling_couples (π:Measure (Curve X))
          have he0 : interpolation (π:Measure (Curve X)) timeZero = (μ₀:Measure X) := congrArg Subtype.val h0
          have he1 : interpolation (π:Measure (Curve X)) timeOne = (μ₁:Measure X) := congrArg Subtype.val h1
          rwa [he0,he1] at H
        refine ⟨π,?_,⟨hend,?_⟩,rfl⟩
        · exact (ae_iff.mpr hs).mono fun γ hγ => hγ.1
        · intro q hq
          apply le_trans ?_ (hopt₀.2 q hq)
          rw [endpointCost_eq_clipped_integral (π:Measure (Curve X)) hs,hcost₀]
          exact ENNReal.ofReal_le_ofReal hcost
    rw [hset]
    exact isCompact_midpoint_constraints (isCompact_boundedEndpointTube o R) μ₀ μ₁
      (clippedEndpointCost R) c t
  · rw [Set.not_nonempty_iff_eq_empty.mp hne]
    exact isCompact_empty

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_BoundedRnRestriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
namespace WeakHessian
open MeasureTheory Filter Set
open scoped ENNReal NNReal

variable {X : Type*} [MeasurableSpace X]

lemma exists_bounded_rn_restriction (μ δ : Measure X)
    [IsFiniteMeasure μ] [IsFiniteMeasure δ] (hac : μ ≪ δ)
    {r : ℝ≥0∞} (hr : r < μ univ) :
    ∃ (A : Set X) (n : ℕ), MeasurableSet A ∧ 0 < n ∧ r < μ A ∧
      μ.restrict A ≤ (n : ℝ≥0∞) • δ := by
  let A : ℕ → Set X := fun n => {x | μ.rnDeriv δ x ≤ (n+1 : ℕ)}
  have hA n : MeasurableSet (A n) := measurableSet_le (μ.measurable_rnDeriv δ) measurable_const
  have hmono : Monotone A := by
    intro i j hij x hx
    change μ.rnDeriv δ x ≤ ((i+1 : ℕ) : ℝ≥0∞) at hx
    change μ.rnDeriv δ x ≤ ((j+1 : ℕ) : ℝ≥0∞)
    exact hx.trans (by exact_mod_cast Nat.add_le_add_right hij 1)
  have hfull : μ (⋃ n, A n) = μ univ := by
    apply measure_congr
    filter_upwards [hac.ae_le (μ.rnDeriv_lt_top δ)] with x hx
    apply propext
    change x ∈ ⋃ n, A n ↔ x ∈ (univ : Set X)
    simp only [mem_iUnion,mem_univ,iff_true]
    change ∃ n, μ.rnDeriv δ x ≤ ((n+1 : ℕ) : ℝ≥0∞)
    obtain ⟨n,hn⟩ := ENNReal.exists_nat_gt hx.ne
    exact ⟨n,hn.le.trans (by exact_mod_cast Nat.le_succ n)⟩
  rw [hmono.measure_iUnion] at hfull
  obtain ⟨n,hn⟩ := lt_iSup_iff.mp (hr.trans_le hfull.ge)
  refine ⟨A n,n+1,hA n,Nat.succ_pos n,hn,?_⟩
  calc
    μ.restrict (A n) = (δ.restrict (A n)).withDensity (μ.rnDeriv δ) := by
      rw [← restrict_withDensity (hA n),μ.withDensity_rnDeriv_eq δ hac]
    _ ≤ (δ.restrict (A n)).withDensity (fun _ => (n+1 : ℕ)) := by
      apply withDensity_mono
      exact (ae_restrict_mem (hA n)).mono (fun x hx => hx)
    _ = ((n+1 : ℕ) : ℝ≥0∞) • δ.restrict (A n) := withDensity_const _
    _ ≤ _ := smul_le_smul_left _ Measure.restrict_le_self

lemma exists_bounded_rn_subrestriction (μ δ : Measure X)
    [IsFiniteMeasure μ] [IsFiniteMeasure δ] {P : Set X} (hP : MeasurableSet P)
    (hac : μ.restrict P ≪ δ) {r : ℝ≥0∞} (hr : r < μ P) :
    ∃ (A : Set X) (n : ℕ), MeasurableSet A ∧ A ⊆ P ∧ 0 < n ∧ r < μ A ∧
      μ.restrict A ≤ (n : ℝ≥0∞) • δ := by
  obtain ⟨A,n,hA,hn,hrA,hdom⟩ := exists_bounded_rn_restriction (μ.restrict P) δ hac
    (by simpa using hr)
  refine ⟨A ∩ P,n,hA.inter hP,inter_subset_right,hn,?_,?_⟩
  · simpa only [Measure.restrict_apply hA] using hrA
  · simpa only [Measure.restrict_restrict hA] using hdom

end WeakHessian
end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Geodesics_GeodesicPlanSupportedBall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
namespace WeakHessian
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

lemma geodesic_plan_supported_ball (π : Measure (Curve X))
    (hg : ∀ᵐ γ ∂π, IsGeodesic γ) (o : X) (R : ℝ)
    (h₀ : interpolation π timeZero (Metric.closedBall o R)ᶜ = 0)
    (h₁ : interpolation π timeOne (Metric.closedBall o R)ᶜ = 0) (t : Time) :
    interpolation π t (Metric.closedBall o (3*R))ᶜ = 0 := by
  have h0 : ∀ᵐ γ ∂π, dist (γ timeZero) o ≤ R := by
    apply ae_of_ae_map (f := fun γ : Curve X => γ timeZero)
      (p := fun x => dist x o ≤ R) (continuous_eval_const timeZero).measurable.aemeasurable
    exact ae_iff.mpr h₀
  have h1 : ∀ᵐ γ ∂π, dist (γ timeOne) o ≤ R := by
    apply ae_of_ae_map (f := fun γ : Curve X => γ timeOne)
      (p := fun x => dist x o ≤ R) (continuous_eval_const timeOne).measurable.aemeasurable
    exact ae_iff.mpr h₁
  apply ae_iff.mp
  apply (ae_map_iff (continuous_eval_const t).measurable.aemeasurable
    (measurableSet_le (continuous_id.dist continuous_const).measurable measurable_const)).mpr
  filter_upwards [hg,h0,h1] with γ hγ hγ0 hγ1
  exact boundedEndpointTube_range ⟨hγ,hγ0,hγ1⟩ t

lemma scaled_CD_spreading_constant {a q c d : ℝ≥0∞}
    (_hq : q ≠ 0) (_hqt : q ≠ ∞) (hc : c ≠ 0) (hct : c ≠ ∞)
    (hd : d ≠ 0) (hdt : d ≠ ∞) :
    a / ((d*q)⁻¹*(d*c)) = a*q/c := by
  rw [ENNReal.mul_inv (Or.inl hd) (Or.inl hdt)]
  have he : d⁻¹*q⁻¹*(d*c) = q⁻¹*c := by
    calc
      d⁻¹*q⁻¹*(d*c) = (d⁻¹*d)*(q⁻¹*c) := by ac_rfl
      _ = q⁻¹*c := by rw [ENNReal.inv_mul_cancel hd hdt,one_mul]
  rw [he,div_eq_mul_inv,ENNReal.mul_inv (Or.inr hct) (Or.inr hc),inv_inv]
  rw [div_eq_mul_inv,mul_assoc]

lemma CD_cap_support_cancel {a C q b : ℝ≥0∞}
    (ha : a ≠ 0) (hat : a ≠ ∞) (hC : C ≠ 0) (hCt : C ≠ ∞) :
    b*C/a*(a*q/C) = b*q := by
  simp only [div_eq_mul_inv]
  calc
    b*C*a⁻¹*(a*q*C⁻¹) = b*q*(C*C⁻¹)*(a⁻¹*a) := by ac_rfl
    _ = b*q := by rw [ENNReal.mul_inv_cancel hC hCt,ENNReal.inv_mul_cancel ha hat,mul_one,mul_one]

lemma isClosed_probability_dominated (ν : Measure X) [IsFiniteMeasure ν] :
    IsClosed {μ : ProbabilityMeasure X | (μ:Measure X) ≤ ν} := by
  have he : {μ : ProbabilityMeasure X | (μ:Measure X) ≤ ν} =
      cappedExcess ν ⁻¹' Iic 0 := by
    ext μ
    change (μ:Measure X) ≤ ν ↔ cappedExcess ν μ ≤ 0
    constructor
    · intro h
      rw [(cappedExcess_eq_zero_iff ν μ).mpr h]
    · intro h
      exact (cappedExcess_eq_zero_iff ν μ).mp (le_antisymm h bot_le)
  rw [he]
  exact (cappedExcess_lowerSemicontinuous ν).isClosed_preimage 0

lemma exists_dominated_of_approximations (ν : Measure X) [IsFiniteMeasure ν]
    {S : Set (ProbabilityMeasure X)} (hc : IsCompact S)
    (h : ∀ b : ℝ≥0∞, 1 < b → b ≠ ∞ → ∃ μ ∈ S, (μ:Measure X) ≤ b • ν) :
    ∃ μ ∈ S, (μ:Measure X) ≤ ν := by
  let b : ℕ → ℝ≥0∞ := fun n => 1+((n+1:ℕ):ℝ≥0∞)⁻¹
  have hb n : 1 < b n := by
    simpa only [b,add_zero] using
      (ENNReal.add_lt_add_left (a := 1) (b := 0) (c := ((n+1:ℕ):ℝ≥0∞)⁻¹)
        (by simp) (ENNReal.inv_pos.mpr (by simp)))
  have hbt n : b n ≠ ∞ := by simp [b]
  have hbf n : IsFiniteMeasure (b n • ν) := by
    constructor
    change b n * ν univ < ∞
    exact ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr (hbt n)) (measure_lt_top _ _)
  let T : ℕ → Set (ProbabilityMeasure X) := fun n => S ∩ {μ | (μ:Measure X) ≤ b n • ν}
  have hcl n : IsClosed (T n) := by
    let := hbf n
    exact hc.isClosed.inter (isClosed_probability_dominated _)
  have hne n : (T n).Nonempty := by
    obtain ⟨μ,hμ,hμb⟩ := h (b n) (hb n) (hbt n)
    exact ⟨μ,hμ,hμb⟩
  have hmono n : T (n+1) ⊆ T n := by
    intro μ hμ
    change μ ∈ S ∧ (μ:Measure X) ≤ b (n+1) • ν at hμ
    change μ ∈ S ∧ (μ:Measure X) ≤ b n • ν
    refine ⟨hμ.1,hμ.2.trans ?_⟩
    intro A
    change b (n+1)*ν A ≤ b n*ν A
    apply mul_le_mul' _ le_rfl
    apply add_le_add le_rfl
    apply ENNReal.inv_le_inv.mpr
    exact_mod_cast Nat.le_succ (n+1)
  have hc0 : IsCompact (T 0) := hc.of_isClosed_subset (hcl 0) inter_subset_left
  obtain ⟨μ,hμ⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed T hmono hne hc0 hcl
  refine ⟨μ,(mem_iInter.mp hμ 0).1,?_⟩
  have hblim : Tendsto b atTop (𝓝 1) := by
    simpa only [b,Function.comp_def,add_zero] using
      (tendsto_const_nhds.add (ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)))
  intro A
  have H : ∀ n, (μ:Measure X) A ≤ b n*ν A := fun n => (mem_iInter.mp hμ n).2 A
  have Hlim := (ENNReal.continuous_mul_const (measure_ne_top ν A)).tendsto 1 |>.comp hblim
  simpa only [one_mul] using ge_of_tendsto Hlim (Eventually.of_forall H)

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_CompressionRate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Filter
open Set Filter MeasureTheory InformationTheory
open Set Filter
open scoped Topology
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set Filter Topology

namespace WeakHessian
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

def compressionRate (K N : ℝ) : ℝ := (N-1)*Real.sqrt (|K|/(N-1))

lemma compressionRate_nonneg {K N : ℝ} (hN : 1 < N) : 0 ≤ compressionRate K N := by
  exact mul_nonneg (sub_nonneg.mpr hN.le) (Real.sqrt_nonneg _)

lemma midpoint_cap_factor {K N D : ℝ} (hN : 1 < N) :
    ((2:ℝ≥0∞)*midpointTauLower K N D)^N =
      ENNReal.ofReal (Real.exp (-compressionRate K N*D)) := by
  have hNp : 0 < N := by linarith
  have hp : 0 ≤ 1/N := by positivity
  have hq : 0 ≤ (N-1)/N := div_nonneg (by linarith) hNp.le
  have hs := midpointSigmaLower_pos K (N-1) D
  rw [midpointTauLower,
    ENNReal.ofReal_rpow_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2) hp,
    ENNReal.ofReal_rpow_of_nonneg hs.le hq]
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _)]
  rw [show (2:ℝ≥0∞) = ENNReal.ofReal (2:ℝ) by norm_num,
    ← ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_rpow_of_nonneg (by positivity) hNp.le]
  congr 1
  rw [Real.rpow_def_of_pos (by positivity)]
  congr 1
  rw [Real.log_mul (by norm_num) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_rpow (by norm_num : (0:ℝ) < 1/2),Real.log_rpow hs]
  simp only [midpointSigmaLower, one_div, Real.log_inv, Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (Real.exp_ne_zero _), Real.log_exp]
  simp only [compressionRate]
  field_simp
  ring

lemma midpoint_cap_eq {K N D : ℝ} (hN : 1 < N) (C : ℝ≥0∞) :
    C/((2:ℝ≥0∞)*midpointTauLower K N D)^N =
      C*ENNReal.ofReal (Real.exp (compressionRate K N*D)) := by
  rw [midpoint_cap_factor hN,div_eq_mul_inv]
  congr 1
  rw [← ENNReal.ofReal_inv_of_pos (Real.exp_pos _),← Real.exp_neg]
  congr 2
  ring

end WeakHessian
end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Transport_PlanEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter

attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory InformationTheory
open Set Filter
open scoped Topology
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable

open Set Filter Topology Bornology
open scoped InnerProductSpace


open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set Filter Topology


namespace WeakHessian
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

lemma integrable_squared_distance_of_cost [SecondCountableTopology X] {q : Measure (X×X)}
    (hq : QuadraticTransportCost q ≠ ∞) : Integrable (fun p : X×X => dist p.1 p.2^2) q := by
  apply (lintegral_ofReal_ne_top_iff_integrable
    (measurable_fst.dist measurable_snd |>.pow_const 2).aestronglyMeasurable
    (ae_of_all _ fun _ => sq_nonneg _)).mp
  simpa only [QuadraticTransportCost,edist_dist,ENNReal.ofReal_pow dist_nonneg] using hq

omit [MeasurableSpace X] [BorelSpace X] in
lemma quadratic_triangle_rigidity {A : Type*} [MeasurableSpace A] {q : Measure A}
    (x y z : A → X)
    (hx : Integrable (fun a => dist (x a) (y a)^2) q)
    (hy : Integrable (fun a => dist (y a) (z a)^2) q)
    (hz : Integrable (fun a => dist (x a) (z a)^2) q)
    (he : (∫ a, dist (x a) (z a)^2 ∂q) ≥
      2*((∫ a, dist (x a) (y a)^2 ∂q)+(∫ a, dist (y a) (z a)^2 ∂q))) :
    ∀ᵐ a ∂q, dist (x a) (y a) = dist (y a) (z a) ∧
      dist (x a) (z a) = 2*dist (x a) (y a) := by
  have hnon : ∀ a, 0 ≤ 2*(dist (x a) (y a)^2+dist (y a) (z a)^2)-dist (x a) (z a)^2 := by
    intro a
    have ht := dist_triangle (x a) (y a) (z a)
    have hd := dist_nonneg (x := x a) (y := z a)
    nlinarith [sq_nonneg (dist (x a) (y a)-dist (y a) (z a))]
  have hadd : Integrable (fun a => dist (x a) (y a)^2+dist (y a) (z a)^2) q := hx.add hy
  have htw : Integrable (fun a => 2*(dist (x a) (y a)^2+dist (y a) (z a)^2)) q := hadd.const_mul 2
  have hi := htw.sub hz
  have hi0 : (∫ a, 2*(dist (x a) (y a)^2+dist (y a) (z a)^2)-dist (x a) (z a)^2 ∂q) = 0 := by
    apply le_antisymm
    · rw [integral_sub htw hz, integral_const_mul, integral_add hx hy]
      linarith
    · exact integral_nonneg hnon
  have hae := (integral_eq_zero_iff_of_nonneg hnon hi).mp hi0
  filter_upwards [hae] with a ha
  have ht := dist_triangle (x a) (y a) (z a)
  have hd := dist_nonneg (x := x a) (y := z a)
  have hx0 := dist_nonneg (x := x a) (y := y a)
  have hy0 := dist_nonneg (x := y a) (y := z a)
  dsimp only [Pi.zero_apply] at ha
  have heq : dist (x a) (y a) = dist (y a) (z a) := by
    nlinarith [sq_nonneg (dist (x a) (z a)),sq_nonneg (dist (x a) (y a)-dist (y a) (z a))]
  refine ⟨heq,?_⟩
  nlinarith [sq_nonneg (dist (x a) (z a)-2*dist (x a) (y a))]

omit [MeasurableSpace X] [BorelSpace X] in
lemma joinCurve_isGeodesic {γ η : Curve X} (hjoin : γ timeOne = η timeZero)
    (hγ : IsGeodesic γ) (hη : IsGeodesic η)
    (hlen : dist (γ timeZero) (γ timeOne) = dist (η timeZero) (η timeOne))
    (hend : dist (γ timeZero) (η timeOne) = 2*dist (γ timeZero) (γ timeOne)) :
    IsGeodesic (joinCurve γ η hjoin) := by
  let L : ℝ≥0 := 2*nndist (γ timeZero) (γ timeOne)
  have hγlen : dist (γ timeZero) (γ timeOne) = ((1/2:ℝ)-0)*(L:ℝ) := by
    dsimp [L]; ring
  have hηlen : dist (η timeZero) (η timeOne) = ((1:ℝ)-1/2)*(L:ℝ) := by
    rw [← hlen]; dsimp [L]; ring
  have hgl := hγ.stretch_lipschitzWith (0:ℝ) (1/2) (by norm_num) hγlen
  have hel := hη.stretch_lipschitzWith (1/2:ℝ) 1 (by norm_num) hηlen
  have heq : evalReal γ (((1/2:ℝ)-0)/(1/2-0)) = evalReal η (((1/2:ℝ)-1/2)/(1-1/2)) := by
    norm_num only [sub_zero,sub_self,zero_div,div_self (by norm_num : (1/2:ℝ) ≠ 0)]
    simpa only [evalReal_one,evalReal_zero] using hjoin
  have hl := lipschitzWith_if_le (1/2:ℝ) hgl hel heq
  have hj (t : Time) : joinCurve γ η hjoin t =
      if (t:ℝ) ≤ 1/2 then evalReal γ (((t:ℝ)-0)/(1/2-0)) else
        evalReal η (((t:ℝ)-1/2)/(1-1/2)) := by
    split_ifs with ht
    · rw [joinCurve_apply_left _ _ _ t ht]; congr 1; ring
    · rw [joinCurve_apply_right _ _ _ t (le_of_not_ge ht)]; congr 1; ring
  apply isGeodesic_of_dist_le
  intro s t
  rw [joinCurve_zero,joinCurve_one,hend,hj s,hj t]
  convert hl.dist_le_mul (s:ℝ) (t:ℝ) using 1
  all_goals try with_reducible_and_instances rfl
  dsimp [L]
  simp only [Real.dist_eq]
  ring

variable [SecondCountableTopology X]

def planEnergy (π : Measure (Curve X)) : ℝ := ∫ γ, dist (γ timeZero) (γ timeOne)^2 ∂π

omit [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] in
lemma plan_energy_measurable : Measurable (fun γ : Curve X => dist (γ timeZero) (γ timeOne)^2) :=
  ((continuous_eval_const timeZero).dist (continuous_eval_const timeOne)).measurable.pow_const 2

omit [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] in
lemma planEnergy_nonneg (π : Measure (Curve X)) : 0 ≤ planEnergy π :=
  integral_nonneg fun _ => sq_nonneg _

lemma planCost_eq_ofReal_energy {π : Measure (Curve X)}
    (hI : Integrable (fun γ => dist (γ timeZero) (γ timeOne)^2) π) :
    QuadraticTransportCost (endpointCoupling π) = ENNReal.ofReal (planEnergy π) := by
  rw [QuadraticTransportCost,endpointCoupling,
    lintegral_map (measurable_fst.edist measurable_snd |>.pow_const 2)
      ((continuous_eval_const timeZero).measurable.prodMk (continuous_eval_const timeOne).measurable)]
  rw [planEnergy,ofReal_integral_eq_lintegral_ofReal hI (ae_of_all _ fun _ => sq_nonneg _)]
  simp only [edist_dist,ENNReal.ofReal_pow dist_nonneg]

lemma integrable_plan_energy {π : Measure (Curve X)}
    (hπ : QuadraticTransportCost (endpointCoupling π) ≠ ∞) :
    Integrable (fun γ => dist (γ timeZero) (γ timeOne)^2) π := by
  have hi := integrable_squared_distance_of_cost hπ
  exact (integrable_map_measure
    (measurable_fst.dist measurable_snd |>.pow_const 2).aestronglyMeasurable
    ((continuous_eval_const timeZero).measurable.prodMk (continuous_eval_const timeOne).measurable).aemeasurable).mp hi
lemma exists_joinable_gluing [CompleteSpace X]
    (μ ν : Measure (Curve X)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hpush : interpolation μ timeOne = interpolation ν timeZero) :
    ∃ q : Measure (Joinable X), IsProbabilityMeasure q ∧
      q.map (fun p => p.1.1) = μ ∧ q.map (fun p => p.1.2) = ν := by
  let : Nonempty (Curve X) := nonempty_of_isProbabilityMeasure μ
  let E := {p : Curve X × Curve X | p.1 timeOne = p.2 timeZero}
  have hE : MeasurableSet E := isClosed_joinable.measurableSet
  obtain ⟨q,hqp,hq0,hq1,hqE⟩ := WeakHessianTransport.exists_fiber_gluing_supported μ ν
    (fun γ => γ timeOne) (fun γ => γ timeZero) (continuous_eval_const _).measurable
    (continuous_eval_const _).measurable hpush
  let := hqp
  let qs : Measure (Joinable X) := q.comap Subtype.val
  have hemb : MeasurableEmbedding (Subtype.val : Joinable X → Curve X × Curve X) :=
    MeasurableEmbedding.subtype_coe hE
  have hsupp : ∀ᵐ p ∂q, p ∈ range (Subtype.val : Joinable X → Curve X×Curve X) := by
    simpa only [Subtype.range_coe_subtype, mem_ofPred_eq] using hqE
  let : IsProbabilityMeasure qs := hemb.isProbabilityMeasure_comap hsupp
  have hqs : qs.map Subtype.val = q := by
    rw [hemb.map_comap, Measure.restrict_eq_self_of_ae_mem hsupp]
  refine ⟨qs,(by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)),?_,?_⟩
  · rw [← hq0, ← hqs, Measure.map_map measurable_fst hemb.measurable]; rfl
  · rw [← hq1, ← hqs, Measure.map_map measurable_snd hemb.measurable]; rfl

def halfCurve (γ : Curve X) : Curve X := γ.comp ⟨halfTime,continuous_halfTime⟩
def rightCurve (γ : Curve X) : Curve X := γ.comp ⟨rightTime,continuous_rightTime⟩
omit [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] in
lemma continuous_halfCurve : Continuous (halfCurve (X := X)) := ContinuousMap.continuous_precomp _
omit [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] in
lemma continuous_rightCurve : Continuous (rightCurve (X := X)) := ContinuousMap.continuous_precomp _

omit [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] in
lemma halfCurve_joinCurve (γ η : Curve X) (h : γ timeOne = η timeZero) :
    halfCurve (joinCurve γ η h) = γ := by
  ext t; exact joinCurve_halfTime γ η h t
omit [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] in
lemma rightCurve_joinCurve (γ η : Curve X) (h : γ timeOne = η timeZero) :
    rightCurve (joinCurve γ η h) = η := by
  ext t; exact joinCurve_rightTime γ η h t

theorem exists_optimal_geodesic_join [CompleteSpace X]
    (μ ν ρ : Measure (Curve X)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [IsProbabilityMeasure ρ]
    (hpush : interpolation μ timeOne = interpolation ν timeZero)
    (hgμ : ∀ᵐ γ ∂μ, IsGeodesic γ) (hgν : ∀ᵐ γ ∂ν, IsGeodesic γ)
    (hIμ : Integrable (fun γ => dist (γ timeZero) (γ timeOne)^2) μ)
    (hIν : Integrable (fun γ => dist (γ timeZero) (γ timeOne)^2) ν)
    (hIρ : Integrable (fun γ => dist (γ timeZero) (γ timeOne)^2) ρ)
    (hρ : IsOptimalCoupling (endpointCoupling ρ) (interpolation μ timeZero) (interpolation ν timeOne))
    (hbudget : 2*(planEnergy μ+planEnergy ν) ≤ planEnergy ρ) :
    ∃ π : Measure (Curve X), IsProbabilityMeasure π ∧
      (∀ᵐ γ ∂π, IsGeodesic γ) ∧
      IsOptimalCoupling (endpointCoupling π) (interpolation μ timeZero) (interpolation ν timeOne) ∧
      (∀ t : Time, interpolation π (halfTime t) = interpolation μ t) ∧
      (∀ t : Time, interpolation π (rightTime t) = interpolation ν t) ∧
      π.map halfCurve = μ ∧ π.map rightCurve = ν := by
  obtain ⟨q,hqp,hq0,hq1⟩ := exists_joinable_gluing μ ν hpush
  let := hqp
  have hfm : Measurable (fun p : Joinable X => p.1.1) := measurable_fst.comp measurable_subtype_coe
  have hsm : Measurable (fun p : Joinable X => p.1.2) := measurable_snd.comp measurable_subtype_coe
  have hjm : Measurable (joinMap (X := X)) := lipschitz_joinMap.continuous.measurable
  let π := q.map joinMap
  let : IsProbabilityMeasure π := by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  have hleft (t : Time) : interpolation π (halfTime t) = interpolation μ t := by
    change (q.map joinMap).map _ = _
    rw [Measure.map_map (continuous_eval_const _).measurable hjm, ← hq0]
    rw [interpolation,Measure.map_map (continuous_eval_const t).measurable hfm]
    congr 1; funext p; exact joinCurve_halfTime _ _ _ t
  have hright (t : Time) : interpolation π (rightTime t) = interpolation ν t := by
    change (q.map joinMap).map _ = _
    rw [Measure.map_map (continuous_eval_const _).measurable hjm, ← hq1]
    rw [interpolation,Measure.map_map (continuous_eval_const t).measurable hsm]
    congr 1; funext p; exact joinCurve_rightTime _ _ _ t
  have hcouple : IsCoupling (endpointCoupling π) (interpolation μ timeZero) (interpolation ν timeOne) := by
    convert endpointCoupling_couples π using 1
    · simpa only [halfTime_zero] using (hleft timeZero).symm
    · simpa only [rightTime_one] using (hright timeOne).symm
  let x : Joinable X → X := fun p => p.1.1 timeZero
  let y : Joinable X → X := fun p => p.1.1 timeOne
  let z : Joinable X → X := fun p => p.1.2 timeOne
  have hx : Integrable (fun p => dist (x p) (y p)^2) q := by
    have hi : Integrable (fun γ => dist (γ timeZero) (γ timeOne)^2) (q.map (fun p => p.1.1)) := by rwa [hq0]
    exact hi.comp_aemeasurable hfm.aemeasurable
  have hy : Integrable (fun p => dist (y p) (z p)^2) q := by
    have hi : Integrable (fun γ => dist (γ timeZero) (γ timeOne)^2) (q.map (fun p => p.1.2)) := by rwa [hq1]
    apply (hi.comp_aemeasurable hsm.aemeasurable).congr
    exact ae_of_all _ fun p => by dsimp only [Function.comp_def,y,z]; rw [p.2]
  have htw : Integrable (fun p => 2*(dist (x p) (y p)^2+dist (y p) (z p)^2)) q := (hx.add hy).const_mul 2
  have hle : ∀ p : Joinable X, dist (x p) (z p)^2 ≤ 2*(dist (x p) (y p)^2+dist (y p) (z p)^2) := by
    intro p
    have ht := dist_triangle (x p) (y p) (z p)
    have hd := dist_nonneg (x := x p) (y := z p)
    nlinarith [sq_nonneg (dist (x p) (y p)-dist (y p) (z p))]
  have hz : Integrable (fun p => dist (x p) (z p)^2) q := by
    apply htw.mono' (((continuous_eval_const timeZero).measurable.comp hfm).dist
      ((continuous_eval_const timeOne).measurable.comp hsm) |>.pow_const 2).aestronglyMeasurable
    exact ae_of_all _ fun p => by rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]; exact hle p
  have hIπ : Integrable (fun γ => dist (γ timeZero) (γ timeOne)^2) π := by
    apply (integrable_map_measure plan_energy_measurable.aestronglyMeasurable hjm.aemeasurable).mpr
    simpa only [Function.comp_def,joinMap,joinCurve_zero,joinCurve_one] using hz
  have heπ : planEnergy π = ∫ p, dist (x p) (z p)^2 ∂q := by
    rw [planEnergy,integral_map hjm.aemeasurable plan_energy_measurable.aestronglyMeasurable]
    simp only [joinMap,joinCurve_zero,joinCurve_one,x,z]
  have heμ : planEnergy μ = ∫ p, dist (x p) (y p)^2 ∂q := by
    rw [planEnergy,← hq0,integral_map hfm.aemeasurable plan_energy_measurable.aestronglyMeasurable]
  have heν : planEnergy ν = ∫ p, dist (y p) (z p)^2 ∂q := by
    rw [planEnergy,← hq1,integral_map hsm.aemeasurable plan_energy_measurable.aestronglyMeasurable]
    apply integral_congr_ae
    exact ae_of_all _ fun p => by dsimp only [y,z]; rw [p.2]
  have hoptLE : planEnergy ρ ≤ planEnergy π := by
    have H := hρ.2 (endpointCoupling π) hcouple
    rw [planCost_eq_ofReal_energy hIρ,planCost_eq_ofReal_energy hIπ] at H
    exact (ENNReal.ofReal_le_ofReal_iff (planEnergy_nonneg π)).mp H
  have hePoint := quadratic_triangle_rigidity x y z hx hy hz (by
    rw [heμ,heν] at hbudget
    rw [heπ] at hoptLE
    exact hbudget.trans hoptLE)
  have hg0 : ∀ᵐ p ∂q, IsGeodesic p.1.1 := by
    apply (ae_map_iff hfm.aemeasurable isClosed_isGeodesic.measurableSet).mp
    rwa [hq0]
  have hg1 : ∀ᵐ p ∂q, IsGeodesic p.1.2 := by
    apply (ae_map_iff hsm.aemeasurable isClosed_isGeodesic.measurableSet).mp
    rwa [hq1]
  have hgπ : ∀ᵐ γ ∂π, IsGeodesic γ := by
    apply (ae_map_iff hjm.aemeasurable isClosed_isGeodesic.measurableSet).mpr
    filter_upwards [hg0,hg1,hePoint] with p h0 h1 hp
    apply joinCurve_isGeodesic p.2 h0 h1 _ hp.2
    exact hp.1.trans (congrArg (fun a => dist a (p.1.2 timeOne)) p.2)
  have hEnergyLE : planEnergy π ≤ planEnergy ρ := by
    have H := integral_mono hz htw hle
    rw [integral_const_mul,integral_add hx hy,← heμ,← heν,← heπ] at H
    exact H.trans hbudget
  refine ⟨π,(by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)),hgπ,⟨hcouple,?_⟩,hleft,hright,?_,?_⟩
  · intro r hr
    apply le_trans _ (hρ.2 r hr)
    rw [planCost_eq_ofReal_energy hIπ,planCost_eq_ofReal_energy hIρ]
    exact ENNReal.ofReal_le_ofReal hEnergyLE
  · change (q.map joinMap).map halfCurve = μ
    rw [Measure.map_map continuous_halfCurve.measurable hjm, ← hq0]
    congr 1; funext p; exact halfCurve_joinCurve _ _ _
  · change (q.map joinMap).map rightCurve = ν
    rw [Measure.map_map continuous_rightCurve.measurable hjm, ← hq1]
    congr 1; funext p; exact rightCurve_joinCurve _ _ _

end WeakHessian
end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Transport_OptimalPlansShort
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Filter
open Set Filter MeasureTheory InformationTheory
open Set Filter
open scoped Topology
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set Filter Topology

namespace WeakHessian
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

variable {X : Type*} [MetricSpace X]

@[simp] lemma halfTime_one : halfTime timeOne = timeHalf := by
  apply Subtype.ext; norm_num [halfTime,timeOne,timeHalf]
@[simp] lemma rightTime_zero : rightTime timeZero = timeHalf := by
  apply Subtype.ext; norm_num [rightTime,timeZero,timeHalf]

lemma IsGeodesic.half_length {γ : Curve X} (hγ : IsGeodesic γ) :
    dist (halfCurve γ timeZero) (halfCurve γ timeOne) = dist (γ timeZero) (γ timeOne)/2 := by
  change dist (γ (halfTime timeZero)) (γ (halfTime timeOne)) = _
  rw [hγ]
  norm_num [halfTime,timeZero,timeOne]
  ring

lemma IsGeodesic.right_length {γ : Curve X} (hγ : IsGeodesic γ) :
    dist (rightCurve γ timeZero) (rightCurve γ timeOne) = dist (γ timeZero) (γ timeOne)/2 := by
  change dist (γ (rightTime timeZero)) (γ (rightTime timeOne)) = _
  rw [hγ]
  norm_num [rightTime,timeZero,timeOne]
  ring

lemma IsGeodesic.halfCurve {γ : Curve X} (hγ : IsGeodesic γ) : IsGeodesic (halfCurve γ) := by
  intro s t
  rw [hγ.half_length]
  change dist (γ (halfTime s)) (γ (halfTime t)) = _
  rw [hγ]
  have H := dist_halfTime s t
  change |(halfTime s:ℝ)-(halfTime t:ℝ)| = |(s:ℝ)-(t:ℝ)|/2 at H
  rw [H]; ring

lemma IsGeodesic.rightCurve {γ : Curve X} (hγ : IsGeodesic γ) : IsGeodesic (rightCurve γ) := by
  intro s t
  rw [hγ.right_length]
  change dist (γ (rightTime s)) (γ (rightTime t)) = _
  rw [hγ]
  have H := dist_rightTime s t
  change |(rightTime s:ℝ)-(rightTime t:ℝ)| = |(s:ℝ)-(t:ℝ)|/2 at H
  rw [H]; ring

variable [MeasurableSpace X] [BorelSpace X]

lemma interpolation_map_half (π : Measure (Curve X)) (t : Time) :
    interpolation (π.map halfCurve) t = interpolation π (halfTime t) := by
  rw [interpolation,Measure.map_map (continuous_eval_const t).measurable continuous_halfCurve.measurable]
  rfl
lemma interpolation_map_right (π : Measure (Curve X)) (t : Time) :
    interpolation (π.map rightCurve) t = interpolation π (rightTime t) := by
  rw [interpolation,Measure.map_map (continuous_eval_const t).measurable continuous_rightCurve.measurable]
  rfl

omit [MeasurableSpace X] [BorelSpace X] in
lemma integrable_plan_energy_half {π : Measure (Curve X)}
    (hg : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hI : Integrable (fun γ => dist (γ timeZero) (γ timeOne)^2) π) :
    Integrable (fun γ => dist (γ timeZero) (γ timeOne)^2) (π.map halfCurve) := by
  apply (integrable_map_measure plan_energy_measurable.aestronglyMeasurable continuous_halfCurve.measurable.aemeasurable).mpr
  apply (hI.div_const 4).congr
  filter_upwards [hg] with γ hγ
  dsimp only [Function.comp_def]
  rw [hγ.half_length]
  ring

omit [MeasurableSpace X] [BorelSpace X] in
lemma integrable_plan_energy_right {π : Measure (Curve X)}
    (hg : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hI : Integrable (fun γ => dist (γ timeZero) (γ timeOne)^2) π) :
    Integrable (fun γ => dist (γ timeZero) (γ timeOne)^2) (π.map rightCurve) := by
  apply (integrable_map_measure plan_energy_measurable.aestronglyMeasurable continuous_rightCurve.measurable.aemeasurable).mpr
  apply (hI.div_const 4).congr
  filter_upwards [hg] with γ hγ
  dsimp only [Function.comp_def]
  rw [hγ.right_length]
  ring

omit [MeasurableSpace X] [BorelSpace X] in
lemma planEnergy_half {π : Measure (Curve X)} (hg : ∀ᵐ γ ∂π, IsGeodesic γ) :
    planEnergy (π.map halfCurve) = planEnergy π/4 := by
  rw [planEnergy,integral_map continuous_halfCurve.measurable.aemeasurable plan_energy_measurable.aestronglyMeasurable]
  change _ = (∫ γ, dist (γ timeZero) (γ timeOne)^2 ∂π)/4
  rw [← integral_div]
  apply integral_congr_ae
  filter_upwards [hg] with γ hγ
  rw [hγ.half_length]; ring

omit [MeasurableSpace X] [BorelSpace X] in
lemma planEnergy_right {π : Measure (Curve X)} (hg : ∀ᵐ γ ∂π, IsGeodesic γ) :
    planEnergy (π.map rightCurve) = planEnergy π/4 := by
  rw [planEnergy,integral_map continuous_rightCurve.measurable.aemeasurable plan_energy_measurable.aestronglyMeasurable]
  change _ = (∫ γ, dist (γ timeZero) (γ timeOne)^2 ∂π)/4
  rw [← integral_div]
  apply integral_congr_ae
  filter_upwards [hg] with γ hγ
  rw [hγ.right_length]; ring

def OptimalPlansShort (μ₀ μ₁ : Measure X) (D : ℝ) : Prop :=
  ∀ π : Measure (Curve X), IsProbabilityMeasure π →
    (∀ᵐ γ ∂π, IsGeodesic γ) → IsOptimalCoupling (endpointCoupling π) μ₀ μ₁ →
      ∀ᵐ γ ∂π, dist (γ timeZero) (γ timeOne) ≤ D

variable [SecondCountableTopology X]

lemma optimalPlan_energy_le {μ ν : Measure (Curve X)}
    (hopt : IsOptimalCoupling (endpointCoupling μ) (interpolation ν timeZero) (interpolation ν timeOne))
    (hIν : Integrable (fun γ => dist (γ timeZero) (γ timeOne)^2) ν) :
    Integrable (fun γ => dist (γ timeZero) (γ timeOne)^2) μ ∧ planEnergy μ ≤ planEnergy ν := by
  have hcost := hopt.2 _ (endpointCoupling_couples ν)
  have hfin : QuadraticTransportCost (endpointCoupling μ) ≠ ∞ := by
    apply ne_top_of_le_ne_top _ hcost
    rw [planCost_eq_ofReal_energy hIν]
    exact ENNReal.ofReal_ne_top
  have hIμ := integrable_plan_energy hfin
  refine ⟨hIμ,?_⟩
  rw [planCost_eq_ofReal_energy hIμ,planCost_eq_ofReal_energy hIν] at hcost
  exact (ENNReal.ofReal_le_ofReal_iff (planEnergy_nonneg ν)).mp hcost

theorem OptimalPlansShort.halves [CompleteSpace X] {μ₀ μ₁ : Measure X} {D : ℝ}
    (hshort : OptimalPlansShort μ₀ μ₁ D)
    (π : Measure (Curve X)) [IsProbabilityMeasure π]
    (hg : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hopt : IsOptimalCoupling (endpointCoupling π) μ₀ μ₁)
    (hI : Integrable (fun γ => dist (γ timeZero) (γ timeOne)^2) π) :
    OptimalPlansShort μ₀ (interpolation π timeHalf) (D/2) ∧
    OptimalPlansShort (interpolation π timeHalf) μ₁ (D/2) := by
  let l := π.map halfCurve
  let r := π.map rightCurve
  let : IsProbabilityMeasure l := Measure.isProbabilityMeasure_map continuous_halfCurve.aemeasurable
  let : IsProbabilityMeasure r := Measure.isProbabilityMeasure_map continuous_rightCurve.aemeasurable
  have hgl : ∀ᵐ γ ∂l, IsGeodesic γ := by
    apply (ae_map_iff continuous_halfCurve.measurable.aemeasurable isClosed_isGeodesic.measurableSet).mpr
    exact hg.mono fun _ => IsGeodesic.halfCurve
  have hgr : ∀ᵐ γ ∂r, IsGeodesic γ := by
    apply (ae_map_iff continuous_rightCurve.measurable.aemeasurable isClosed_isGeodesic.measurableSet).mpr
    exact hg.mono fun _ => IsGeodesic.rightCurve
  have hIl : Integrable (fun γ => dist (γ timeZero) (γ timeOne)^2) l := integrable_plan_energy_half hg hI
  have hIr : Integrable (fun γ => dist (γ timeZero) (γ timeOne)^2) r := integrable_plan_energy_right hg hI
  have hl0 : interpolation l timeZero = μ₀ := by rw [interpolation_map_half,halfTime_zero,hopt.1.interpolation_endpoints.1]
  have hl1 : interpolation l timeOne = interpolation π timeHalf := by rw [interpolation_map_half,halfTime_one]
  have hr0 : interpolation r timeZero = interpolation π timeHalf := by rw [interpolation_map_right,rightTime_zero]
  have hr1 : interpolation r timeOne = μ₁ := by rw [interpolation_map_right,rightTime_one,hopt.1.interpolation_endpoints.2]
  have hel : planEnergy l = planEnergy π/4 := planEnergy_half hg
  have her : planEnergy r = planEnergy π/4 := planEnergy_right hg
  constructor
  · intro η hpη hgη hoη
    let := hpη
    have hoη' : IsOptimalCoupling (endpointCoupling η) (interpolation l timeZero) (interpolation l timeOne) := by rwa [hl0,hl1]
    obtain ⟨hIη,heη⟩ := optimalPlan_energy_le hoη' hIl
    have hpush : interpolation η timeOne = interpolation r timeZero := by rw [hoη.1.interpolation_endpoints.2,hr0]
    have hoπ : IsOptimalCoupling (endpointCoupling π) (interpolation η timeZero) (interpolation r timeOne) := by rwa [hoη.1.interpolation_endpoints.1,hr1]
    obtain ⟨ω,hpω,hgω,hoω,_,_,hlω,_⟩ := exists_optimal_geodesic_join η r π hpush hgη hgr hIη hIr hI hoπ (by rw [hel] at heη; rw [her]; linarith)
    let := hpω
    have hωshort := hshort ω hpω hgω (by simpa only [hoη.1.interpolation_endpoints.1,hr1] using hoω)
    rw [← hlω]
    apply (ae_map_iff continuous_halfCurve.measurable.aemeasurable
      (measurableSet_le ((continuous_eval_const timeZero).dist (continuous_eval_const timeOne)).measurable measurable_const)).mpr
    filter_upwards [hgω,hωshort] with γ hγ hb
    rw [hγ.half_length]
    linarith
  · intro η hpη hgη hoη
    let := hpη
    have hoη' : IsOptimalCoupling (endpointCoupling η) (interpolation r timeZero) (interpolation r timeOne) := by rwa [hr0,hr1]
    obtain ⟨hIη,heη⟩ := optimalPlan_energy_le hoη' hIr
    have hpush : interpolation l timeOne = interpolation η timeZero := by rw [hoη.1.interpolation_endpoints.1,hl1]
    have hoπ : IsOptimalCoupling (endpointCoupling π) (interpolation l timeZero) (interpolation η timeOne) := by rwa [hl0,hoη.1.interpolation_endpoints.2]
    obtain ⟨ω,hpω,hgω,hoω,_,_,_,hrω⟩ := exists_optimal_geodesic_join l η π hpush hgl hgη hIl hIη hI hoπ (by rw [her] at heη; rw [hel]; linarith)
    let := hpω
    have hωshort := hshort ω hpω hgω (by simpa only [hl0,hoη.1.interpolation_endpoints.2] using hoω)
    rw [← hrω]
    apply (ae_map_iff continuous_rightCurve.measurable.aemeasurable
      (measurableSet_le ((continuous_eval_const timeZero).dist (continuous_eval_const timeOne)).measurable measurable_const)).mpr
    filter_upwards [hgω,hωshort] with γ hγ hb
    rw [hγ.right_length]
    linarith

omit [SecondCountableTopology X] in
lemma OptimalPlansShort.subplan {μ₀ μ₁ : Measure X} {D : ℝ}
    (hshort : OptimalPlansShort μ₀ μ₁ D)
    (π : Measure (Curve X)) [IsProbabilityMeasure π]
    (hg : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hopt : IsOptimalCoupling (endpointCoupling π) μ₀ μ₁)
    (θ : Measure (Curve X)) (hθ : θ ≤ π) (hq : θ univ ≠ 0) :
    OptimalPlansShort (interpolation ((θ univ)⁻¹ • θ) timeZero)
      (interpolation ((θ univ)⁻¹ • θ) timeOne) D := by
  let : IsFiniteMeasure θ := isFiniteMeasure_of_le π hθ
  let q := θ univ
  have hqt : q ≠ ∞ := measure_ne_top _ _
  let θ' := q⁻¹ • θ
  have hcanc : q • θ' = θ := by
    dsimp only [θ']; rw [smul_smul,ENNReal.mul_inv_cancel hq hqt,one_smul]
  intro η hpη hgη hoη
  let := hpη
  let ξ := q • η
  have hξmass : ξ univ = θ univ := by simp [ξ,q]
  have hξend (t : Time) (h : interpolation η t = interpolation θ' t) :
      interpolation ξ t = interpolation θ t := by
    change (q • η).map _ = θ.map _
    rw [Measure.map_smul]
    change q • interpolation η t = _
    rw [h]
    change q • θ'.map _ = _
    rw [← Measure.map_smul,hcanc]
  have hξ0 := hξend timeZero hoη.1.interpolation_endpoints.1
  have hξ1 := hξend timeOne hoη.1.interpolation_endpoints.2
  have hcost : QuadraticTransportCost (endpointCoupling ξ) ≤ QuadraticTransportCost (endpointCoupling θ) := by
    have H := mul_le_mul' (le_refl q) (hoη.2 _ (endpointCoupling_couples θ'))
    have hs (ρ : Measure (Curve X)) : QuadraticTransportCost (endpointCoupling (q • ρ)) =
        q*QuadraticTransportCost (endpointCoupling ρ) := by
      simp only [QuadraticTransportCost,endpointCoupling,
        Measure.map_smul,
        lintegral_smul_measure,smul_eq_mul]
    rw [← hs η,← hs θ',hcanc] at H
    exact H
  have hgξ : ∀ᵐ γ ∂ξ, IsGeodesic γ := (Measure.AbsolutelyContinuous.rfl.smul_left _).ae_le hgη
  let ω := π-θ+ξ
  have hpω : IsProbabilityMeasure ω := replacement_probability _ _ _ hθ hξmass
  have H := hshort ω hpω (geodesic_plan_reroute hg hgξ) (hopt.reroute_plan hθ hξ0 hξ1 hcost)
  have hξω : ξ ≤ ω := by
    have H := add_le_add (show (0 : Measure (Curve X)) ≤ π-θ from bot_le) (le_refl ξ)
    simpa only [zero_add] using H
  exact (Measure.absolutelyContinuous_smul hq).ae_le ((Measure.absolutelyContinuous_of_le hξω).ae_le H)

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_ExcessRelocation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
namespace WeakHessian
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

omit [MetricSpace X] [BorelSpace X] in
lemma excess_relocation_le (μ ν ρ β : Measure X)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure β]
    (hρ : ρ ≤ μ-ν) (hmass : β univ = ρ univ) :
    ((μ-ρ+β)-ν) univ ≤ (μ-ν) univ := by
  let δ := μ-ν
  let : IsFiniteMeasure δ := isFiniteMeasure_of_le μ Measure.sub_le
  let : IsFiniteMeasure ρ := isFiniteMeasure_of_le δ hρ
  have hρμ : ρ ≤ μ := hρ.trans Measure.sub_le
  have hu : (μ-ρ+β)-ν ≤ δ-ρ+β := by
    apply Measure.sub_le_of_le_add
    apply Measure.le_of_add_le_add_left (μ := ρ)
    calc
      ρ+(μ-ρ+β) = μ+β := by rw [← add_assoc,add_comm ρ (μ-ρ),Measure.sub_add_cancel_of_le hρμ]
      _ ≤ (δ+ν)+β := add_le_add (measure_le_sub_add μ ν) le_rfl
      _ = (ρ+(δ-ρ)+ν)+β := by rw [add_comm ρ (δ-ρ),Measure.sub_add_cancel_of_le hρ]
      _ = ρ+(δ-ρ+β+ν) := by ac_rfl
  calc
    _ ≤ (δ-ρ+β) univ := hu univ
    _ = δ univ := by
      rw [Measure.add_apply,Measure.sub_apply MeasurableSet.univ hρ,hmass]
      exact tsub_add_cancel_of_le (hρ univ)

lemma cappedExcess_relocation_le (ν : Measure X) [IsFiniteMeasure ν]
    (μ η : ProbabilityMeasure X) (ρ β : Measure X) [IsFiniteMeasure β]
    (hρ : ρ ≤ (μ:Measure X)-ν) (hmass : β univ = ρ univ)
    (hη : (η:Measure X) = (μ:Measure X)-ρ+β) :
    cappedExcess ν η ≤ cappedExcess ν μ := by
  rw [cappedExcess_eq_positivePart,cappedExcess_eq_positivePart,hη]
  exact excess_relocation_le _ _ _ _ hρ hmass

lemma lower_dominance_of_cap_le (κ : Measure X) [IsFiniteMeasure κ]
    (μ η : ProbabilityMeasure X) (hκμ : κ ≤ (μ:Measure X))
    (hcap : cappedExcess κ η ≤ cappedExcess κ μ) : κ ≤ (η:Measure X) := by
  rw [cappedExcess_eq_positivePart,cappedExcess_eq_positivePart,
    Measure.sub_apply MeasurableSet.univ hκμ] at hcap
  simp only [measure_univ] at hcap
  have ht : κ univ ≤ 1 := by simpa using hκμ univ
  have hb := congrArg (fun ν : Measure X => ν univ)
    (measure_positive_negative_balance (η:Measure X) κ)
  simp only [Measure.add_apply, measure_univ] at hb
  have hh : 1+(κ-(η:Measure X)) univ ≤ 1 := by
    rw [hb]
    exact (add_le_add le_rfl hcap).trans_eq (add_tsub_cancel_of_le ht)
  have hz : (κ-(η:Measure X)) univ = 0 := by
    exact le_antisymm ((ENNReal.add_le_add_iff_left (by simp : (1:ℝ≥0∞) ≠ ∞)).mp (by simpa using hh)) bot_le
  have hz' : κ-(η:Measure X)=0 := Measure.measure_univ_eq_zero.mp hz
  simpa only [hz',zero_add] using measure_le_sub_add κ (η:Measure X)

end WeakHessian

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Transport_CdEntropyPlanBounded
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter

attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology
open Set Filter MeasureTheory InformationTheory
open Set Filter
open scoped Topology

namespace WeakHessian
open MeasureTheory InformationTheory
open scoped ENNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

lemma cd_entropy_plan_bounded {m μ₀ μ₁ : Measure X}
    [IsProbabilityMeasure μ₀] [IsProbabilityMeasure μ₁]
    {K N : ℝ} (hN : 1 < N) (hcd : CurvatureDimension m K N)
    (hfinite : FiniteOnBoundedSets m)
    (hE₀ : FiniteEntropy m μ₀) (hE₁ : FiniteEntropy m μ₁)
    (o : X) {R : ℝ} (hR : 0 ≤ R)
    (hs₀ : ∀ᵐ x ∂μ₀, dist x o ≤ R) (hs₁ : ∀ᵐ x ∂μ₁, dist x o ≤ R) :
    ∃ π : Measure (Curve X), IsProbabilityMeasure π ∧ (∀ᵐ γ ∂π, IsGeodesic γ) ∧
      IsOptimalCoupling (endpointCoupling π) μ₀ μ₁ ∧
      ∀ t : Time, FiniteEntropy m (interpolation π t) ∧
        entropyReal m (interpolation π t) ≤ (1-(t:ℝ))*entropyReal m μ₀+(t:ℝ)*entropyReal m μ₁ -
          K/2*(t:ℝ)*(1-(t:ℝ))*(∫ γ, dist (γ timeZero) (γ timeOne)^2 ∂π) := by
  let : SigmaFinite m := sigmaFinite_of_finiteOnBoundedSets m hfinite o
  obtain ⟨π,hπ,hgeo,hopt,hτ⟩ := hcd μ₀ μ₁ inferInstance inferInstance
    (hasSecondMoment_of_ae_dist_le o R hs₀) (hasSecondMoment_of_ae_dist_le o R hs₁) hE₀.1 hE₁.1
  let : IsProbabilityMeasure π := hπ
  obtain ⟨hm₀,hm₁⟩ := hopt.1.interpolation_endpoints
  have hγ₀ : ∀ᵐ γ ∂π, dist (γ timeZero) o ≤ R := by
    have H : ∀ᵐ x ∂interpolation π timeZero, dist x o ≤ R := by simpa only [hm₀] using hs₀
    exact ae_of_ae_map (continuous_eval_const timeZero).measurable.aemeasurable H
  have hγ₁ : ∀ᵐ γ ∂π, dist (γ timeOne) o ≤ R := by
    have H : ∀ᵐ x ∂interpolation π timeOne, dist x o ≤ R := by simpa only [hm₁] using hs₁
    exact ae_of_ae_map (continuous_eval_const timeOne).measurable.aemeasurable H
  have hlen : ∀ᵐ γ ∂π, dist (γ timeZero) (γ timeOne) ≤ 2*R := by
    filter_upwards [hγ₀,hγ₁] with γ h0 h1
    have H := dist_triangle (γ timeZero) o (γ timeOne)
    rw [dist_comm o] at H
    linarith
  have htracks : ∀ᵐ γ ∂π, ∀ t : Time, γ t ∈ Metric.closedBall o (3*R+1) := by
    filter_upwards [hγ₀,hlen,hgeo] with γ h0 hL hg
    intro t
    have H := dist_triangle (γ t) (γ timeZero) o
    rw [hg,show (timeZero:ℝ)=0 from rfl,sub_zero,abs_of_nonneg t.2.1] at H
    have HH := mul_le_mul_of_nonneg_right t.2.2 (dist_nonneg (x := γ timeZero) (y := γ timeOne))
    simp only [one_mul] at HH
    change dist (γ t) o ≤ 3*R+1
    linarith
  have hs0Q : ∀ᵐ x ∂μ₀, x ∈ Metric.closedBall o (3*R+1) := hs₀.mono fun x hx => by
    change dist x o ≤ 3*R+1
    linarith
  have hs1Q : ∀ᵐ x ∂μ₁, x ∈ Metric.closedBall o (3*R+1) := hs₁.mono fun x hx => by
    change dist x o ≤ 3*R+1
    linarith
  let d : ℕ → ℝ := fun n => N+(n:ℝ)
  have hd : ∀ n, 1 < d n := fun n => by dsimp [d]; exact hN.trans_le (le_add_of_nonneg_right (Nat.cast_nonneg _))
  have hdlim : Tendsto (fun n => 1/d n) atTop (𝓝 0) := by
    simp only [one_div]
    apply tendsto_inv_atTop_zero.comp
    exact tendsto_atTop_add_const_left _ N tendsto_natCast_atTop_atTop
  refine ⟨π,hπ,hgeo,hopt,fun t => ?_⟩
  let : IsProbabilityMeasure (interpolation π t) := interpolation_probability π t
  have hst : ∀ᵐ x ∂interpolation π t, x ∈ Metric.closedBall o (3*R+1) := by
    exact (ae_map_iff (continuous_eval_const t).measurable.aemeasurable Metric.isClosed_closedBall.measurableSet).mpr
      (htracks.mono fun γ hγ => hγ t)
  apply cd_entropy_bound_on_finite_region
    (continuous_eval_const timeZero).measurable (continuous_eval_const timeOne).measurable
    hm₀ hm₁ hE₀ hE₁ Metric.isClosed_closedBall.measurableSet
    (hfinite _ Metric.isBounded_closedBall) hs0Q hs1Q hst
    ((continuous_eval_const timeZero).dist (continuous_eval_const timeOne)).measurable
    (Eventually.of_forall fun γ => dist_nonneg) (sq_nonneg (2*R))
    (hlen.mono fun γ hγ => pow_le_pow_left₀ dist_nonneg hγ 2) t.2.1 t.2.2 hd hdlim
  exact fun n => hτ (d n) (by dsimp [d]; exact le_add_of_nonneg_right (Nat.cast_nonneg _)) t
end WeakHessian

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Measure_OptimalTimeLawSupported
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter

attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory InformationTheory
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace WeakHessian
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

lemma optimalTimeLaw_supported_ball {μ₀ μ₁ μ : ProbabilityMeasure X} {t : Time}
    (hμ : μ ∈ optimalTimeLaws μ₀ μ₁ t) (o : X) (R : ℝ)
    (hb₀ : (μ₀:Measure X) (Metric.closedBall o R)ᶜ = 0)
    (hb₁ : (μ₁:Measure X) (Metric.closedBall o R)ᶜ = 0) :
    (μ:Measure X) (Metric.closedBall o (3*R))ᶜ = 0 := by
  obtain ⟨π,hgeo,hopt,hμ⟩ := hμ
  subst μ
  exact geodesic_plan_supported_ball (π:Measure (Curve X)) hgeo o R
    (by simpa only [hopt.1.interpolation_endpoints.1] using hb₀)
    (by simpa only [hopt.1.interpolation_endpoints.2] using hb₁) t

lemma endpointCost_eq_ofReal_integral [SecondCountableTopology X]
    (π : ProbabilityMeasure (Curve X)) {μ₀ μ₁ : ProbabilityMeasure X} (o : X) (R : ℝ≥0)
    (hg : ∀ᵐ γ ∂(π:Measure (Curve X)), IsGeodesic γ)
    (he : IsCoupling (endpointCoupling (π:Measure (Curve X))) μ₀ μ₁)
    (hb₀ : (μ₀:Measure X) (Metric.closedBall o R)ᶜ = 0)
    (hb₁ : (μ₁:Measure X) (Metric.closedBall o R)ᶜ = 0) :
    QuadraticTransportCost (endpointCoupling (π:Measure (Curve X))) =
      ENNReal.ofReal (∫ γ, dist (γ timeZero) (γ timeOne)^2 ∂(π:Measure (Curve X))) := by
  have hs := optimalPlan_supported_tube π hg he hb₀ hb₁
  rw [endpointCost_eq_clipped_integral (π:Measure (Curve X)) hs]
  congr 1
  apply integral_congr_ae
  exact (ae_iff.mpr hs).mono fun γ hγ => clippedEndpointCost_eq hγ

lemma optimal_cost_integral_eq [SecondCountableTopology X]
    (π η : ProbabilityMeasure (Curve X)) {μ₀ μ₁ : ProbabilityMeasure X} (o : X) (R : ℝ≥0)
    (hgπ : ∀ᵐ γ ∂(π:Measure (Curve X)), IsGeodesic γ)
    (hgη : ∀ᵐ γ ∂(η:Measure (Curve X)), IsGeodesic γ)
    (hπ : IsOptimalCoupling (endpointCoupling (π:Measure (Curve X))) μ₀ μ₁)
    (hη : IsOptimalCoupling (endpointCoupling (η:Measure (Curve X))) μ₀ μ₁)
    (hb₀ : (μ₀:Measure X) (Metric.closedBall o R)ᶜ = 0)
    (hb₁ : (μ₁:Measure X) (Metric.closedBall o R)ᶜ = 0) :
    (∫ γ, dist (γ timeZero) (γ timeOne)^2 ∂(π:Measure (Curve X))) =
      (∫ γ, dist (γ timeZero) (γ timeOne)^2 ∂(η:Measure (Curve X))) := by
  apply (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg fun _ => sq_nonneg _) (integral_nonneg fun _ => sq_nonneg _)).mp
  rw [← endpointCost_eq_ofReal_integral π o R hgπ hπ.1 hb₀ hb₁,
    ← endpointCost_eq_ofReal_integral η o R hgη hη.1 hb₀ hb₁]
  exact le_antisymm (hπ.2 _ hη.1) (hη.2 _ hπ.1)

end WeakHessian

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Transport_RerouteFiniteSubplanShort
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Filter
open Set Filter MeasureTheory InformationTheory
open Set Filter
open scoped Topology
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set Filter Topology

namespace WeakHessian
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

lemma CurvatureDimension.reroute_finite_subplan_short {m : Measure X} [SigmaFinite m]
    {K N : ℝ} (hN : 1 < N) (hcd : CurvatureDimension m K N)
    (θ : Measure (Curve X)) [IsFiniteMeasure θ] (hq : θ univ ≠ 0)
    (o : X) {R : ℝ} (_ : 0 ≤ R) (D : ℝ≥0)
    (hshort : OptimalPlansShort (interpolation ((θ univ)⁻¹ • θ) timeZero)
      (interpolation ((θ univ)⁻¹ • θ) timeOne) D)
    (hb : ∀ᵐ γ ∂θ, dist (γ timeZero) o ≤ R ∧ dist (γ timeOne) o ≤ R)
    {C : ℝ≥0∞} (hd₀ : interpolation θ timeZero ≤ C • m)
    (hd₁ : interpolation θ timeOne ≤ C • m) :
    ∃ ξ : Measure (Curve X), IsFiniteMeasure ξ ∧ ξ univ = θ univ ∧
      (∀ᵐ γ ∂ξ, IsGeodesic γ) ∧
      interpolation ξ timeZero = interpolation θ timeZero ∧
      interpolation ξ timeOne = interpolation θ timeOne ∧
      QuadraticTransportCost (endpointCoupling ξ) ≤ QuadraticTransportCost (endpointCoupling θ) ∧
      ∀ B : Set X, MeasurableSet B → interpolation ξ timeHalf Bᶜ = 0 →
        ((2:ℝ≥0∞)*midpointTauLower K N D)^N / ((θ univ)⁻¹*C) ≤ m B := by
  let q := θ univ
  have hqt : q ≠ ∞ := measure_ne_top _ _
  let θ' : Measure (Curve X) := q⁻¹ • θ
  have hp : IsProbabilityMeasure θ' := by
    constructor
    change q⁻¹*θ univ = 1
    exact ENNReal.inv_mul_cancel hq hqt
  let := hp
  have hcanc : q • θ' = θ := by
    change q • (q⁻¹ • θ) = θ
    rw [smul_smul,ENNReal.mul_inv_cancel hq hqt,one_smul]
  let μ₀ := interpolation θ' timeZero
  let μ₁ := interpolation θ' timeOne
  let : IsProbabilityMeasure μ₀ := interpolation_probability θ' timeZero
  let : IsProbabilityMeasure μ₁ := interpolation_probability θ' timeOne
  have he (t : Time) : interpolation θ' t = q⁻¹ • interpolation θ t :=
    Measure.map_smul _ _ _
  have hd0 : μ₀ ≤ (q⁻¹*C) • m := by
    dsimp only [μ₀]
    rw [he,← smul_smul]
    exact smul_le_smul_left _ hd₀
  have hd1 : μ₁ ≤ (q⁻¹*C) • m := by
    dsimp only [μ₁]
    rw [he,← smul_smul]
    exact smul_le_smul_left _ hd₁
  have hac0 : μ₀ ≪ m := (Measure.absolutelyContinuous_of_le hd0).trans
    (Measure.AbsolutelyContinuous.rfl.smul_left _)
  have hac1 : μ₁ ≪ m := (Measure.absolutelyContinuous_of_le hd1).trans
    (Measure.AbsolutelyContinuous.rfl.smul_left _)
  have hb' : ∀ᵐ γ ∂θ', dist (γ timeZero) o ≤ R ∧ dist (γ timeOne) o ≤ R :=
    (Measure.AbsolutelyContinuous.rfl.smul_left _).ae_le hb
  have hb0 : ∀ᵐ x ∂μ₀, dist x o ≤ R :=
    (ae_map_iff (continuous_eval_const timeZero).measurable.aemeasurable
      (measurableSet_le (continuous_id.dist continuous_const).measurable measurable_const)).mpr
      (hb'.mono fun _ h => h.1)
  have hb1 : ∀ᵐ x ∂μ₁, dist x o ≤ R :=
    (ae_map_iff (continuous_eval_const timeOne).measurable.aemeasurable
      (measurableSet_le (continuous_id.dist continuous_const).measurable measurable_const)).mpr
      (hb'.mono fun _ h => h.2)
  obtain ⟨π,hπ,hgeo,hopt,hent⟩ := hcd μ₀ μ₁ inferInstance inferInstance
    (hasSecondMoment_of_ae_dist_le o R hb0) (hasSecondMoment_of_ae_dist_le o R hb1) hac0 hac1
  let := hπ
  obtain ⟨he0,he1⟩ := hopt.1.interpolation_endpoints
  have hlen : ∀ᵐ γ ∂π, dist (γ timeZero) (γ timeOne) ≤ D := hshort π hπ hgeo hopt
  let ξ := q • π
  have hξmass : ξ univ = θ univ := by simp [ξ,q]
  have hξfin : IsFiniteMeasure ξ := ⟨hξmass ▸ measure_lt_top θ univ⟩
  have hξend (t : Time) (ht : interpolation π t = interpolation θ' t) :
      interpolation ξ t = interpolation θ t := by
    change (q • π).map _ = _
    rw [Measure.map_smul]
    change q • interpolation π t = _
    rw [ht]
    change q • θ'.map (fun γ => γ t) = θ.map (fun γ => γ t)
    rw [← Measure.map_smul,hcanc]
  refine ⟨ξ,hξfin,hξmass,(Measure.AbsolutelyContinuous.rfl.smul_left _).ae_le hgeo,
    hξend timeZero he0,hξend timeOne he1,?_,?_⟩
  · have H := mul_le_mul' (le_refl q) (hopt.2 (endpointCoupling θ') (endpointCoupling_couples θ'))
    change q*QuadraticTransportCost (endpointCoupling π) ≤ q*QuadraticTransportCost (endpointCoupling θ') at H
    have hs (η : Measure (Curve X)) : QuadraticTransportCost (endpointCoupling (q • η)) =
        q*QuadraticTransportCost (endpointCoupling η) := by
      unfold QuadraticTransportCost endpointCoupling
      rw [Measure.map_smul q,
        lintegral_smul_measure,smul_eq_mul]
    rw [← hs π,← hs θ',hcanc] at H
    exact H
  · intro B hB hs
    have hs' : interpolation π timeHalf Bᶜ = 0 := by
      change (q • π).map _ Bᶜ = 0 at hs
      rw [Measure.map_smul,
        Measure.smul_apply,smul_eq_mul] at hs
      exact (mul_eq_zero.mp hs).resolve_left hq
    apply cd_midpoint_support_lower hN D.property hopt.1
      (hac0.ae_le (rnDeriv_le_of_le_smul hd0))
      (hac1.ae_le (rnDeriv_le_of_le_smul hd1)) hlen ?_ hB hs'
    simpa only [timeHalf, show (1 : ℝ)-1/2 = 1/2 by norm_num] using hent N le_rfl timeHalf

lemma CurvatureDimension.reroute_midpoint_restriction_short
    [SecondCountableTopology X] {m : Measure X} [SigmaFinite m]
    {K N : ℝ} (hN : 1 < N) (hcd : CurvatureDimension m K N)
    {μ₀ μ₁ μ : ProbabilityMeasure X} (hμ : μ ∈ optimalTimeLaws μ₀ μ₁ timeHalf)
    (o : X) (R : ℝ≥0)
    (hb₀ : (μ₀:Measure X) (Metric.closedBall o R)ᶜ = 0)
    (hb₁ : (μ₁:Measure X) (Metric.closedBall o R)ᶜ = 0)
    (D : ℝ≥0) (hshort : OptimalPlansShort (μ₀:Measure X) (μ₁:Measure X) D)
    {C : ℝ≥0∞} (hC : C ≠ 0) (hCt : C ≠ ∞)
    (hd₀ : (μ₀:Measure X) ≤ C • m) (hd₁ : (μ₁:Measure X) ≤ C • m)
    {A : Set X} (hA : MeasurableSet A) (hq : (μ:Measure X) A ≠ 0)
    {d : ℝ≥0∞} (hd : d ≠ 0) (hdt : d ≠ ∞) (hd1 : d ≤ 1) :
    ∃ (β : Measure X) (η : ProbabilityMeasure X), IsFiniteMeasure β ∧
      β univ = d*(μ:Measure X) A ∧ η ∈ optimalTimeLaws μ₀ μ₁ timeHalf ∧
      (η:Measure X) = (μ:Measure X)-d • (μ:Measure X).restrict A+β ∧
      β (Metric.closedBall o (3*(R:ℝ)))ᶜ = 0 ∧
      ∀ B : Set X, MeasurableSet B → β Bᶜ = 0 →
        ((2:ℝ≥0∞)*midpointTauLower K N D)^N*(μ:Measure X) A/C ≤ m B := by
  obtain ⟨π,hgeo,hopt,hμeq⟩ := hμ
  have heμ : (μ:Measure X) = interpolation (π:Measure (Curve X)) timeHalf :=
    congrArg Subtype.val hμeq
  let θ : Measure (Curve X) := d • (π:Measure (Curve X)).restrict ((fun γ => γ timeHalf) ⁻¹' A)
  have hscale : d • (π:Measure (Curve X)) ≤ (π:Measure (Curve X)) := by
    intro S
    change d*(π:Measure (Curve X)) S ≤ (π:Measure (Curve X)) S
    simpa using mul_le_mul' hd1 (le_refl ((π:Measure (Curve X)) S))
  have hθ : θ ≤ (π:Measure (Curve X)) :=
    (smul_le_smul_left d Measure.restrict_le_self).trans hscale
  let : IsFiniteMeasure θ := isFiniteMeasure_of_le (π:Measure (Curve X)) hθ
  have hθmass : θ univ = d*(μ:Measure X) A := by
    rw [heμ,interpolation,Measure.map_apply (continuous_eval_const timeHalf).measurable hA]
    simp [θ]
  have hθ0 : θ univ ≠ 0 := by rw [hθmass]; exact mul_ne_zero hd hq
  have hθb : ∀ᵐ γ ∂θ, dist (γ timeZero) o ≤ R ∧ dist (γ timeOne) o ≤ R := by
    have H := optimalPlan_supported_tube π hgeo hopt.1 hb₀ hb₁
    exact (Measure.absolutelyContinuous_of_le hθ).ae_le ((ae_iff.mpr H).mono fun _ h => h.2)
  have hθend (t : Time) : interpolation θ t ≤ d • interpolation (π:Measure (Curve X)) t := by
    dsimp only [θ,interpolation]

    rw [Measure.map_smul]
    exact smul_le_smul_left d (Measure.map_mono Measure.restrict_le_self (continuous_eval_const t).measurable)
  have hde0 : interpolation θ timeZero ≤ (d*C) • m := by
    calc
      _ ≤ d • interpolation (π:Measure (Curve X)) timeZero := hθend _
      _ = d • (μ₀:Measure X) := by rw [hopt.1.interpolation_endpoints.1]
      _ ≤ d • (C • m) := smul_le_smul_left d hd₀
      _ = _ := smul_smul _ _ _
  have hde1 : interpolation θ timeOne ≤ (d*C) • m := by
    calc
      _ ≤ d • interpolation (π:Measure (Curve X)) timeOne := hθend _
      _ = d • (μ₁:Measure X) := by rw [hopt.1.interpolation_endpoints.2]
      _ ≤ d • (C • m) := smul_le_smul_left d hd₁
      _ = _ := smul_smul _ _ _
  obtain ⟨ξ,hξfin,hξmass,hξgeo,hξ0,hξ1,hξcost,hξspread⟩ :=
    hcd.reroute_finite_subplan_short hN θ hθ0 o R.property D
      (hshort.subplan (π:Measure (Curve X)) hgeo hopt θ hθ hθ0) hθb hde0 hde1
  let := hξfin
  let ω := (π:Measure (Curve X))-θ+ξ
  let : IsProbabilityMeasure ω := replacement_probability _ _ _ hθ hξmass
  let ηπ : ProbabilityMeasure (Curve X) := ⟨ω,(by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩
  let η := ηπ.map (continuous_eval_const timeHalf).aemeasurable
  let β := interpolation ξ timeHalf
  have hβfin : IsFiniteMeasure β := Measure.isFiniteMeasure_map ξ _
  have hξb0 : interpolation ξ timeZero (Metric.closedBall o R)ᶜ = 0 := by
    rw [hξ0]
    apply le_antisymm _ bot_le
    calc
      _ ≤ d*interpolation (π:Measure (Curve X)) timeZero (Metric.closedBall o R)ᶜ := hθend _ _
      _ = 0 := by rw [hopt.1.interpolation_endpoints.1,hb₀,mul_zero]
  have hξb1 : interpolation ξ timeOne (Metric.closedBall o R)ᶜ = 0 := by
    rw [hξ1]
    apply le_antisymm _ bot_le
    calc
      _ ≤ d*interpolation (π:Measure (Curve X)) timeOne (Metric.closedBall o R)ᶜ := hθend _ _
      _ = 0 := by rw [hopt.1.interpolation_endpoints.2,hb₁,mul_zero]
  refine ⟨β,η,hβfin,?_,?_,?_,geodesic_plan_supported_ball ξ hξgeo o R hξb0 hξb1 timeHalf,?_⟩
  · dsimp [β,interpolation]
    rw [Measure.map_apply_of_aemeasurable (continuous_eval_const timeHalf).measurable.aemeasurable MeasurableSet.univ]
    simpa only [preimage_univ] using hξmass.trans hθmass
  · exact ⟨ηπ,geodesic_plan_reroute hgeo hξgeo,hopt.reroute_plan hθ hξ0 hξ1 hξcost,rfl⟩
  · change (ω.map (fun γ => γ timeHalf)) = _
    rw [show ω = (π:Measure (Curve X))-θ+ξ from rfl,
      Measure.map_add _ _ (continuous_eval_const timeHalf).measurable,
      map_sub_of_le _ _ hθ (continuous_eval_const timeHalf).measurable]
    have heθ : interpolation θ timeHalf = d • (μ:Measure X).restrict A := by
      change Measure.map (fun γ : Curve X => γ timeHalf) (d • (π:Measure (Curve X)).restrict _) = _
      rw [Measure.map_smul]
      rw [← interpolation,interpolation_restricted _ _ hA,← heμ]
    change interpolation (π:Measure (Curve X)) timeHalf - interpolation θ timeHalf + β = _
    rw [heθ,heμ]
  · intro B hB hβB
    have H := hξspread B hB hβB
    rw [hθmass,scaled_CD_spreading_constant hq (measure_ne_top _ _) hC hCt hd hdt] at H
    exact H

theorem CurvatureDimension.exists_bounded_midpoint_preserving_caps_short
    [SecondCountableTopology X] [ProperSpace X] {m : Measure X} [SigmaFinite m]
    {K N : ℝ} (hN : 1 < N) (hcd : CurvatureDimension m K N)
    (hfin : FiniteOnBoundedSets m) {μ₀ μ₁ : ProbabilityMeasure X}
    (o : X) (R : ℝ≥0)
    (hb₀ : (μ₀:Measure X) (Metric.closedBall o R)ᶜ = 0)
    (hb₁ : (μ₁:Measure X) (Metric.closedBall o R)ᶜ = 0)
    (D : ℝ≥0) (hshort : OptimalPlansShort (μ₀:Measure X) (μ₁:Measure X) D)
    {C : ℝ≥0∞} (hC : C ≠ 0) (hCt : C ≠ ∞)
    (hd₀ : (μ₀:Measure X) ≤ C • m) (hd₁ : (μ₁:Measure X) ≤ C • m)
    {I : Type*} (W : I → Measure X)
    (hW : ∀ i, W i ≤ (C/((2:ℝ≥0∞)*midpointTauLower K N D)^N) •
      m.restrict (Metric.closedBall o (3*(R:ℝ))))
    (μref : ProbabilityMeasure X) (href : μref ∈ optimalTimeLaws μ₀ μ₁ timeHalf)
    {b : ℝ≥0∞} (hb : 1 < b) (hbt : b ≠ ∞) :
    ∃ μ ∈ optimalTimeLaws μ₀ μ₁ timeHalf,
      (μ:Measure X) ≤ (b*C/((2:ℝ≥0∞)*midpointTauLower K N D)^N) •
        m.restrict (Metric.closedBall o (3*(R:ℝ))) ∧
      ∀ i, cappedExcess (W i) μ ≤ cappedExcess (W i) μref := by
  let a : ℝ≥0∞ := ((2:ℝ≥0∞)*midpointTauLower K N D)^N
  have ha0 : a ≠ 0 := (ENNReal.rpow_pos
    (ENNReal.mul_pos_iff.mpr ⟨by norm_num,midpointTauLower_pos _ _ _⟩)
    (ENNReal.mul_ne_top (by simp) (midpointTauLower_ne_top hN))).ne'
  have hat : a ≠ ∞ := ENNReal.rpow_ne_top_of_ne_zero
    (mul_ne_zero (by norm_num) (midpointTauLower_pos _ _ _).ne')
    (ENNReal.mul_ne_top (by simp) (midpointTauLower_ne_top hN))
  let Q := Metric.closedBall o (3*(R:ℝ))
  have hQ : MeasurableSet Q := Metric.isClosed_closedBall.measurableSet
  let ν := (b*C/a) • m.restrict Q
  have hνfin : IsFiniteMeasure ν := by
    constructor
    change (b*C/a)*(m.restrict Q) univ < ∞
    rw [Measure.restrict_apply_univ]
    exact ENNReal.mul_lt_top
      (lt_top_iff_ne_top.mpr (ENNReal.mul_ne_top (ENNReal.mul_ne_top hbt hCt) (ENNReal.inv_ne_top.mpr ha0)))
      (hfin Q Metric.isBounded_closedBall)
  let := hνfin
  have hWV (i : I) : W i ≤ ν := by
    apply (hW i).trans
    have hc : C/a ≤ b*C/a := by
      apply mul_le_mul' _ le_rfl
      simpa only [one_mul] using mul_le_mul' hb.le (le_refl C)
    intro A
    exact mul_le_mul' hc (le_refl ((m.restrict Q) A))
  let S : Set (ProbabilityMeasure X) := optimalTimeLaws μ₀ μ₁ timeHalf ∩
    {μ | ∀ i, cappedExcess (W i) μ ≤ cappedExcess (W i) μref}
  have hSc : IsCompact S := by
    apply (isCompact_optimalTimeLaws o R hb₀ hb₁ timeHalf).inter_right
    convert isClosed_iInter (fun i =>
      (cappedExcess_lowerSemicontinuous (W i)).isClosed_preimage (cappedExcess (W i) μref)) using 1
    all_goals try with_reducible_and_instances rfl
    ext μ
    simp
  obtain ⟨μ,hμ,hdμ⟩ : ∃ μ ∈ S, (μ:Measure X) ≤ ν := by
    apply exists_dominated_of_compact_rerouting (S := S) ν ⟨μref,href,fun _ => le_rfl⟩ hSc
    intro μ hμS P hP hsur
    have hμ := hμS.1
    let δ := (μ:Measure X)-ν
    let : IsFiniteMeasure δ := isFiniteMeasure_of_le (μ:Measure X) Measure.sub_le
    have hmass : (μ:Measure X) P ≠ 0 := ne_of_gt (hsur.trans_le hP.surplus_le_mass)
    have hb0 : b ≠ 0 := (zero_lt_one.trans hb).ne'
    have hsmall : (μ:Measure X) P/b < (μ:Measure X) P := by
      apply (ENNReal.div_lt_iff (Or.inl hb0) (Or.inl hbt)).mpr
      simpa only [one_mul,mul_comm] using ENNReal.mul_lt_mul_left hmass (measure_ne_top _ _) hb
    obtain ⟨A,n,hA,hAP,hn,hAmass,hAdom⟩ := exists_bounded_rn_subrestriction
      (μ:Measure X) δ hP.measurableSet hP.mass_ac hsmall
    have hn0 : (n:ℝ≥0∞) ≠ 0 := by exact_mod_cast hn.ne'
    have hnt : (n:ℝ≥0∞) ≠ ∞ := by simp
    let d : ℝ≥0∞ := (n:ℝ≥0∞)⁻¹
    have hd : d ≠ 0 := ENNReal.inv_ne_zero.mpr hnt
    have hdt : d ≠ ∞ := ENNReal.inv_ne_top.mpr hn0
    have hd1 : d ≤ 1 := ENNReal.inv_le_one.mpr (by exact_mod_cast hn)
    have hA0 : (μ:Measure X) A ≠ 0 := ne_of_gt (bot_le.trans_lt hAmass)
    obtain ⟨β,η,hβfin,hβmass,hη,hηeq,hβQ,hspread⟩ :=
      hcd.reroute_midpoint_restriction_short hN hμ o R hb₀ hb₁ D hshort hC hCt hd₀ hd₁ hA hA0 hd hdt hd1
    let ρ := d • (μ:Measure X).restrict A
    have hρ : ρ ≤ δ := by
      calc
        _ ≤ d • ((n:ℝ≥0∞) • δ) := smul_le_smul_left d hAdom
        _ = δ := by rw [smul_smul,show d*(n:ℝ≥0∞)=1 from ENNReal.inv_mul_cancel hn0 hnt,one_smul]
    have hηS : η ∈ S := by
      refine ⟨hη,fun i => ?_⟩
      let : IsFiniteMeasure (W i) := isFiniteMeasure_of_le ν (hWV i)
      let := hβfin
      have hρW : ρ ≤ (μ:Measure X)-W i := by
        apply hρ.trans
        apply Measure.sub_le_of_le_add
        exact (measure_le_sub_add (μ:Measure X) (W i)).trans (add_le_add le_rfl (hWV i))
      apply (cappedExcess_relocation_le (W i) μ η ρ β hρW _ hηeq).trans (hμS.2 i)
      simpa [ρ,Measure.smul_apply] using hβmass
    refine ⟨ρ,β,η,hβfin,hρ,?_,hηS,hηeq,?_⟩
    · simpa [ρ,Measure.smul_apply] using hβmass
    · intro B hB hβB
      have hsupport : β (B ∩ Q)ᶜ = 0 := by
        rw [compl_inter]
        exact measure_union_null hβB hβQ
      have H := hspread (B ∩ Q) (hB.inter hQ) hsupport
      calc
        ν P + ((μ:Measure X)-ν) univ = (μ:Measure X) P := hP.exact_mass.symm
        _ ≤ b*(μ:Measure X) A := by
          have H' := mul_le_mul' hAmass.le (le_refl b)
          rw [ENNReal.div_mul_cancel hb0 hbt] at H'
          simpa only [mul_comm] using H'
        _ = (b*C/a)*(a*(μ:Measure X) A/C) := (CD_cap_support_cancel ha0 hat hC hCt).symm
        _ ≤ (b*C/a)*m (B ∩ Q) := mul_le_mul' le_rfl H
        _ = ν B := by simp only [ν,Measure.smul_apply,smul_eq_mul,Measure.restrict_apply hB]
  exact ⟨μ,hμ.1,hdμ,hμ.2⟩

theorem CurvatureDimension.exists_sharp_midpoint_preserving_caps_short
    [SecondCountableTopology X] [ProperSpace X] {m : Measure X} [SigmaFinite m]
    {K N : ℝ} (hN : 1 < N) (hcd : CurvatureDimension m K N)
    (hfin : FiniteOnBoundedSets m) {μ₀ μ₁ : ProbabilityMeasure X}
    (o : X) (R : ℝ≥0)
    (hb₀ : (μ₀:Measure X) (Metric.closedBall o R)ᶜ = 0)
    (hb₁ : (μ₁:Measure X) (Metric.closedBall o R)ᶜ = 0)
    (D : ℝ≥0) (hshort : OptimalPlansShort (μ₀:Measure X) (μ₁:Measure X) D)
    {C : ℝ≥0∞} (hC : C ≠ 0) (hCt : C ≠ ∞)
    (hd₀ : (μ₀:Measure X) ≤ C • m) (hd₁ : (μ₁:Measure X) ≤ C • m)
    {I : Type*} (W : I → Measure X)
    (hW : ∀ i, W i ≤ (C/((2:ℝ≥0∞)*midpointTauLower K N D)^N) •
      m.restrict (Metric.closedBall o (3*(R:ℝ))))
    (μref : ProbabilityMeasure X) (href : μref ∈ optimalTimeLaws μ₀ μ₁ timeHalf) :
    ∃ μ ∈ optimalTimeLaws μ₀ μ₁ timeHalf,
      (μ:Measure X) ≤ (C/((2:ℝ≥0∞)*midpointTauLower K N D)^N) •
        m.restrict (Metric.closedBall o (3*(R:ℝ))) ∧
      ∀ i, cappedExcess (W i) μ ≤ cappedExcess (W i) μref := by
  let a : ℝ≥0∞ := ((2:ℝ≥0∞)*midpointTauLower K N D)^N
  have ha0 : a ≠ 0 := (ENNReal.rpow_pos
    (ENNReal.mul_pos_iff.mpr ⟨by norm_num,midpointTauLower_pos _ _ _⟩)
    (ENNReal.mul_ne_top (by simp) (midpointTauLower_ne_top hN))).ne'
  let ν := (C/a) • m.restrict (Metric.closedBall o (3*(R:ℝ)))
  have hνfin : IsFiniteMeasure ν := by
    constructor
    change (C/a)*(m.restrict (Metric.closedBall o (3*(R:ℝ)))) univ < ∞
    rw [Measure.restrict_apply_univ]
    exact ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr (ENNReal.div_ne_top hCt ha0))
      (hfin _ Metric.isBounded_closedBall)
  let := hνfin
  let S : Set (ProbabilityMeasure X) := optimalTimeLaws μ₀ μ₁ timeHalf ∩
    {μ | ∀ i, cappedExcess (W i) μ ≤ cappedExcess (W i) μref}
  have hSc : IsCompact S := by
    apply (isCompact_optimalTimeLaws o R hb₀ hb₁ timeHalf).inter_right
    convert isClosed_iInter (fun i =>
      (cappedExcess_lowerSemicontinuous (W i)).isClosed_preimage (cappedExcess (W i) μref)) using 1
    all_goals try with_reducible_and_instances rfl
    ext μ
    simp
  obtain ⟨μ,hμ,hdμ⟩ : ∃ μ ∈ S, (μ:Measure X) ≤ ν := by
    apply exists_dominated_of_approximations ν hSc
    intro b hb hbt
    obtain ⟨μ,hμ,hμdom,hcaps⟩ := hcd.exists_bounded_midpoint_preserving_caps_short
      hN hfin o R hb₀ hb₁ D hshort hC hCt hd₀ hd₁ W hW μref href hb hbt
    refine ⟨μ,⟨hμ,hcaps⟩,?_⟩
    simpa only [ν,smul_smul,div_eq_mul_inv,mul_assoc] using hμdom
  exact ⟨μ,hμ.1,hdμ,hμ.2⟩

theorem CurvatureDimension.exists_sharp_midpoint_above_lower_short
    [SecondCountableTopology X] [ProperSpace X] {m : Measure X} [SigmaFinite m]
    {K N : ℝ} (hN : 1 < N) (hcd : CurvatureDimension m K N)
    (hfin : FiniteOnBoundedSets m) {μ₀ μ₁ : ProbabilityMeasure X}
    (o : X) (R : ℝ≥0)
    (hb₀ : (μ₀:Measure X) (Metric.closedBall o R)ᶜ = 0)
    (hb₁ : (μ₁:Measure X) (Metric.closedBall o R)ᶜ = 0)
    (D : ℝ≥0) (hshort : OptimalPlansShort (μ₀:Measure X) (μ₁:Measure X) D)
    {C : ℝ≥0∞} (hC : C ≠ 0) (hCt : C ≠ ∞)
    (hd₀ : (μ₀:Measure X) ≤ C • m) (hd₁ : (μ₁:Measure X) ≤ C • m)
    (κ : Measure X)
    (hκcap : κ ≤ (C/((2:ℝ≥0∞)*midpointTauLower K N D)^N) •
      m.restrict (Metric.closedBall o (3*(R:ℝ))))
    (μref : ProbabilityMeasure X) (href : μref ∈ optimalTimeLaws μ₀ μ₁ timeHalf)
    (hκref : κ ≤ (μref:Measure X)) :
    ∃ μ ∈ optimalTimeLaws μ₀ μ₁ timeHalf,
      (μ:Measure X) ≤ (C/((2:ℝ≥0∞)*midpointTauLower K N D)^N) •
        m.restrict (Metric.closedBall o (3*(R:ℝ))) ∧ κ ≤ (μ:Measure X) := by
  let : IsFiniteMeasure κ := isFiniteMeasure_of_le (μref:Measure X) hκref
  obtain ⟨μ,hμ,hdμ,hcaps⟩ := hcd.exists_sharp_midpoint_preserving_caps_short
    hN hfin o R hb₀ hb₁ D hshort hC hCt hd₀ hd₁ (fun _ : Unit => κ) (fun _ => hκcap) μref href
  exact ⟨μ,hμ,hdμ,lower_dominance_of_cap_le κ μref μ hκref (hcaps ())⟩

theorem CurvatureDimension.exists_entropy_improving_sharp_midpoint_short
    [SecondCountableTopology X] [ProperSpace X] {m : Measure X} [SigmaFinite m]
    {K N : ℝ} (hN : 1 < N) (hcd : CurvatureDimension m K N)
    (hfin : FiniteOnBoundedSets m) {μ₀ μ₁ : ProbabilityMeasure X}
    (o : X) (R : ℝ≥0)
    (hb₀ : (μ₀:Measure X) (Metric.closedBall o R)ᶜ = 0)
    (hb₁ : (μ₁:Measure X) (Metric.closedBall o R)ᶜ = 0)
    (D : ℝ≥0) (hshort : OptimalPlansShort (μ₀:Measure X) (μ₁:Measure X) D)
    {C : ℝ≥0∞} (hC : C ≠ 0) (hCt : C ≠ ∞)
    (hd₀ : (μ₀:Measure X) ≤ C • m) (hd₁ : (μ₁:Measure X) ≤ C • m)
    (μref : ProbabilityMeasure X) (href : μref ∈ optimalTimeLaws μ₀ μ₁ timeHalf)
    (hEref : FiniteEntropy m (μref:Measure X)) :
    ∃ μ ∈ optimalTimeLaws μ₀ μ₁ timeHalf,
      (μ:Measure X) ≤ (C/((2:ℝ≥0∞)*midpointTauLower K N D)^N) •
        m.restrict (Metric.closedBall o (3*(R:ℝ))) ∧
      FiniteEntropy m (μ:Measure X) ∧ entropyReal m (μ:Measure X) ≤ entropyReal m (μref:Measure X) := by
  let a : ℝ≥0∞ := ((2:ℝ≥0∞)*midpointTauLower K N D)^N
  have ha0 : a ≠ 0 := (ENNReal.rpow_pos
    (ENNReal.mul_pos_iff.mpr ⟨by norm_num,midpointTauLower_pos _ _ _⟩)
    (ENNReal.mul_ne_top (by simp) (midpointTauLower_ne_top hN))).ne'
  have hat : a ≠ ∞ := ENNReal.rpow_ne_top_of_ne_zero
    (mul_ne_zero (by norm_num) (midpointTauLower_pos _ _ _).ne')
    (ENNReal.mul_ne_top (by simp) (midpointTauLower_ne_top hN))
  let B := C/a
  have hB : B ≠ 0 := ENNReal.div_ne_zero.mpr ⟨hC,hat⟩
  have hBt : B ≠ ∞ := ENNReal.div_ne_top hCt ha0
  let Q := Metric.closedBall o (3*(R:ℝ))
  have hQ : MeasurableSet Q := Metric.isClosed_closedBall.measurableSet
  let : IsFiniteMeasure (m.restrict Q) := ⟨by simpa only [Measure.restrict_apply_univ] using hfin Q Metric.isBounded_closedBall⟩
  have hsref : ∀ᵐ x ∂(μref:Measure X), x ∈ Q :=
    ae_iff.mpr (optimalTimeLaw_supported_ball href o R hb₀ hb₁)
  have hErefQ := (finiteEntropy_restrict_reference_iff hQ hsref).mpr hEref
  let κ := (m.restrict Q).withDensity (fun x => min ((μref:Measure X).rnDeriv (m.restrict Q) x) B)
  have hκcap : κ ≤ B • m.restrict Q := by
    rw [← withDensity_const]
    exact withDensity_mono (ae_of_all _ fun x => min_le_right _ _)
  have hκref : κ ≤ (μref:Measure X) := by
    rw [← Measure.withDensity_rnDeriv_eq (μref:Measure X) (m.restrict Q) hErefQ.1]
    exact withDensity_mono (ae_of_all _ fun x => min_le_left _ _)
  obtain ⟨μ,hμ,hdμ,hκμ⟩ := hcd.exists_sharp_midpoint_above_lower_short hN hfin o R hb₀ hb₁
    D hshort hC hCt hd₀ hd₁ κ hκcap μref href hκref
  obtain ⟨hEμQ,hent⟩ := entropyReal_le_of_density_capping (μref:Measure X) (μ:Measure X)
    hErefQ hB hBt hdμ hκμ
  have hsμ : ∀ᵐ x ∂(μ:Measure X), x ∈ Q :=
    ae_iff.mpr (optimalTimeLaw_supported_ball hμ o R hb₀ hb₁)
  have hEμ := (finiteEntropy_restrict_reference_iff hQ hsμ).mp hEμQ
  refine ⟨μ,hμ,hdμ,hEμ,?_⟩
  rwa [entropyReal_restrict_reference hQ hEμ.1 hsμ,
    entropyReal_restrict_reference hQ hEref.1 hsref] at hent

theorem CurvatureDimension.exists_entropy_bounded_midpoint_short
    [SecondCountableTopology X] [ProperSpace X] {m : Measure X} [SigmaFinite m]
    {K N : ℝ} (hN : 1 < N) (hcd : CurvatureDimension m K N)
    (hfin : FiniteOnBoundedSets m) (μ₀ μ₁ : ProbabilityMeasure X)
    (o : X) (R : ℝ≥0)
    (hb₀ : (μ₀:Measure X) (Metric.closedBall o R)ᶜ = 0)
    (hb₁ : (μ₁:Measure X) (Metric.closedBall o R)ᶜ = 0)
    (D : ℝ≥0) (hshort : OptimalPlansShort (μ₀:Measure X) (μ₁:Measure X) D)
    {C : ℝ≥0∞} (hC : C ≠ 0) (hCt : C ≠ ∞)
    (hd₀ : (μ₀:Measure X) ≤ C • m) (hd₁ : (μ₁:Measure X) ≤ C • m)
    (hE₀ : FiniteEntropy m (μ₀:Measure X)) (hE₁ : FiniteEntropy m (μ₁:Measure X)) :
    ∃ π : ProbabilityMeasure (Curve X),
      (∀ᵐ γ ∂(π:Measure (Curve X)), IsGeodesic γ) ∧
      IsOptimalCoupling (endpointCoupling (π:Measure (Curve X))) μ₀ μ₁ ∧
      interpolation (π:Measure (Curve X)) timeHalf ≤
        (C/((2:ℝ≥0∞)*midpointTauLower K N D)^N) • m.restrict (Metric.closedBall o (3*(R:ℝ))) ∧
      FiniteEntropy m (interpolation (π:Measure (Curve X)) timeHalf) ∧
      entropyReal m (interpolation (π:Measure (Curve X)) timeHalf) ≤
        (entropyReal m (μ₀:Measure X)+entropyReal m (μ₁:Measure X))/2 -
          K/8*(∫ γ, dist (γ timeZero) (γ timeOne)^2 ∂(π:Measure (Curve X))) := by
  obtain ⟨π,hp,hg,ho,hE⟩ := cd_entropy_plan_bounded hN hcd hfin hE₀ hE₁ o R.2
    (ae_iff.mpr hb₀) (ae_iff.mpr hb₁)
  let := hp
  let πp : ProbabilityMeasure (Curve X) := ⟨π,hp⟩
  let μref : ProbabilityMeasure X := πp.map (f := (fun γ => γ timeHalf)) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  have href : μref ∈ optimalTimeLaws μ₀ μ₁ timeHalf := ⟨πp,hg,ho,rfl⟩
  obtain ⟨μ,hμ,hdμ,hEμ,hentμ⟩ := hcd.exists_entropy_improving_sharp_midpoint_short
    hN hfin o R hb₀ hb₁ D hshort hC hCt hd₀ hd₁ μref href (hE timeHalf).1
  obtain ⟨η,hgη,hoη,hμeq⟩ := hμ
  have hcost := optimal_cost_integral_eq πp η o R hg hgη ho hoη hb₀ hb₁
  have hbound := hentμ.trans (hE timeHalf).2
  rw [hμeq] at hdμ hEμ hbound
  refine ⟨η,hgη,hoη,hdμ,hEμ,?_⟩
  change entropyReal m (interpolation (η:Measure (Curve X)) timeHalf) ≤ _ at hbound
  change (∫ γ, dist (γ timeZero) (γ timeOne)^2 ∂π) = _ at hcost
  rw [hcost] at hbound
  convert hbound using 1
  all_goals try with_reducible_and_instances rfl
  dsimp only [timeHalf]
  ring

end WeakHessian
end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Entropy_EntropyCell
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Filter
open Set Filter MeasureTheory InformationTheory
open Set Filter
open scoped Topology
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set Filter Topology

namespace WeakHessian
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

universe u
variable {X : Type u} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [SecondCountableTopology X]

omit [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] in
lemma integrable_plan_energy_of_length {π : Measure (Curve X)} [IsFiniteMeasure π] {D : ℝ}
    (hD : ∀ᵐ γ ∂π, dist (γ timeZero) (γ timeOne) ≤ D) :
    Integrable (fun γ => dist (γ timeZero) (γ timeOne)^2) π := by
  apply (integrable_const (D^2)).mono' plan_energy_measurable.aestronglyMeasurable
  filter_upwards [hD] with γ hγ
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ dist_nonneg hγ 2

omit [MetricSpace X] [BorelSpace X] [SecondCountableTopology X] in
lemma dominated_mono_constant {μ m : Measure X} {A B : ℝ≥0∞}
    (h : μ ≤ A • m) (hAB : A ≤ B) : μ ≤ B • m := by
  intro S
  exact (h S).trans (mul_le_mul' hAB le_rfl)

structure EntropyCell (m : Measure X) (K N : ℝ) where
  leftLaw : ProbabilityMeasure X
  rightLaw : ProbabilityMeasure X
  center : X
  radius : ℝ≥0
  length : ℝ≥0
  cap : ℝ≥0∞
  cap_pos : cap ≠ 0
  cap_finite : cap ≠ ∞
  left_supported : (leftLaw:Measure X) (Metric.closedBall center radius)ᶜ = 0
  right_supported : (rightLaw:Measure X) (Metric.closedBall center radius)ᶜ = 0
  left_dominated : (leftLaw:Measure X) ≤ cap • m
  right_dominated : (rightLaw:Measure X) ≤ cap • m
  left_entropy : FiniteEntropy m (leftLaw:Measure X)
  right_entropy : FiniteEntropy m (rightLaw:Measure X)
  short : OptimalPlansShort (leftLaw:Measure X) (rightLaw:Measure X) length

structure CellPlan {m : Measure X} {K N : ℝ} (c : EntropyCell m K N) where
  law : ProbabilityMeasure (Curve X)
  geodesic : ∀ᵐ γ ∂(law:Measure (Curve X)), IsGeodesic γ
  optimal : IsOptimalCoupling (endpointCoupling (law:Measure (Curve X))) c.leftLaw c.rightLaw

structure CDEnvironment (m : Measure X) (K N : ℝ) : Prop where
  dimension : 1 < N
  cd : CurvatureDimension m K N
  finite_bounded : FiniteOnBoundedSets m

variable {m : Measure X} {K N : ℝ}

namespace EntropyCell

def nextCap (c : EntropyCell m K N) : ℝ≥0∞ :=
  c.cap*ENNReal.ofReal (Real.exp (compressionRate K N*c.length))

omit [BorelSpace X] [SecondCountableTopology X] in
lemma nextCap_pos (c : EntropyCell m K N) : c.nextCap ≠ 0 :=
  mul_ne_zero c.cap_pos (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
omit [BorelSpace X] [SecondCountableTopology X] in
lemma nextCap_finite (c : EntropyCell m K N) : c.nextCap ≠ ∞ :=
  ENNReal.mul_ne_top c.cap_finite ENNReal.ofReal_ne_top
omit [BorelSpace X] [SecondCountableTopology X] in
lemma cap_le_nextCap (env : CDEnvironment m K N) (c : EntropyCell m K N) : c.cap ≤ c.nextCap := by
  have H : (1:ℝ≥0∞) ≤ ENNReal.ofReal (Real.exp (compressionRate K N*c.length)) := by
    exact_mod_cast ENNReal.ofReal_le_ofReal (Real.one_le_exp_iff.mpr (mul_nonneg (compressionRate_nonneg env.dimension) c.length.property))
  simpa only [nextCap, mul_one] using mul_le_mul' (le_refl c.cap) H

end EntropyCell

namespace CellPlan
omit [BorelSpace X] [SecondCountableTopology X] in
lemma integrable_energy {c : EntropyCell m K N} (p : CellPlan c) :
    Integrable (fun γ => dist (γ timeZero) (γ timeOne)^2) (p.law:Measure (Curve X)) :=
  integrable_plan_energy_of_length (c.short _ inferInstance p.geodesic p.optimal)
end CellPlan

structure CellMidpoint {m : Measure X} {K N : ℝ} (c : EntropyCell m K N) extends CellPlan c where
  dominated : interpolation (law:Measure (Curve X)) timeHalf ≤ c.nextCap • m
  finite_entropy : FiniteEntropy m (interpolation (law:Measure (Curve X)) timeHalf)
  entropy_bound : entropyReal m (interpolation (law:Measure (Curve X)) timeHalf) ≤
    (entropyReal m (c.leftLaw:Measure X)+entropyReal m (c.rightLaw:Measure X))/2 -
      K/8*planEnergy (law:Measure (Curve X))

variable [ProperSpace X] [SigmaFinite m]

lemma CDEnvironment.midpoint_nonempty (env : CDEnvironment m K N) (c : EntropyCell m K N) :
    Nonempty (CellMidpoint c) := by
  obtain ⟨π,hg,ho,hd,hE,he⟩ := env.cd.exists_entropy_bounded_midpoint_short env.dimension env.finite_bounded
    c.leftLaw c.rightLaw c.center c.radius c.left_supported c.right_supported c.length c.short
    c.cap_pos c.cap_finite c.left_dominated c.right_dominated c.left_entropy c.right_entropy
  rw [midpoint_cap_eq env.dimension] at hd
  have hd' : interpolation (π:Measure (Curve X)) timeHalf ≤ c.nextCap • m :=
    hd.trans (smul_le_smul_left c.nextCap Measure.restrict_le_self)
  exact ⟨⟨⟨π,hg,ho⟩,hd',hE,he⟩⟩

noncomputable def CDEnvironment.midpoint (env : CDEnvironment m K N) (c : EntropyCell m K N) :
    CellMidpoint c := Classical.choice (env.midpoint_nonempty c)

omit [SigmaFinite m]

namespace CellMidpoint
variable {c : EntropyCell m K N}
def middle (p : CellMidpoint c) : ProbabilityMeasure X :=
  p.law.map (continuous_eval_const timeHalf).aemeasurable

omit [ProperSpace X] [SecondCountableTopology X] in
lemma middle_supported (p : CellMidpoint c) :
    (p.middle:Measure X) (Metric.closedBall c.center (3*(c.radius:ℝ)))ᶜ = 0 :=
  geodesic_plan_supported_ball (p.law:Measure (Curve X)) p.geodesic c.center c.radius
    (by rw [p.optimal.1.interpolation_endpoints.1]; exact c.left_supported)
    (by rw [p.optimal.1.interpolation_endpoints.2]; exact c.right_supported) timeHalf

lemma short_halves (p : CellMidpoint c) :
    OptimalPlansShort (c.leftLaw:Measure X) (p.middle:Measure X) ((c.length:ℝ)/2) ∧
    OptimalPlansShort (p.middle:Measure X) (c.rightLaw:Measure X) ((c.length:ℝ)/2) :=
  c.short.halves (p.law:Measure (Curve X)) p.geodesic p.optimal p.toCellPlan.integrable_energy

def leftCell (p : CellMidpoint c) (env : CDEnvironment m K N) : EntropyCell m K N where
  leftLaw := c.leftLaw
  rightLaw := p.middle
  center := c.center
  radius := 3*c.radius
  length := c.length/2
  cap := c.nextCap
  cap_pos := c.nextCap_pos
  cap_finite := c.nextCap_finite
  left_supported := measure_mono_null (compl_subset_compl.mpr (Metric.closedBall_subset_closedBall (by
    change (c.radius:ℝ) ≤ (3:ℝ)*(c.radius:ℝ); linarith [c.radius.property]))) c.left_supported
  right_supported := by simpa only [NNReal.coe_mul,NNReal.coe_ofNat] using p.middle_supported
  left_dominated := dominated_mono_constant c.left_dominated (c.cap_le_nextCap env)
  right_dominated := p.dominated
  left_entropy := c.left_entropy
  right_entropy := p.finite_entropy
  short := by simpa only [NNReal.coe_div,NNReal.coe_ofNat] using p.short_halves.1

def rightCell (p : CellMidpoint c) (env : CDEnvironment m K N) : EntropyCell m K N where
  leftLaw := p.middle
  rightLaw := c.rightLaw
  center := c.center
  radius := 3*c.radius
  length := c.length/2
  cap := c.nextCap
  cap_pos := c.nextCap_pos
  cap_finite := c.nextCap_finite
  left_supported := by simpa only [NNReal.coe_mul,NNReal.coe_ofNat] using p.middle_supported
  right_supported := measure_mono_null (compl_subset_compl.mpr (Metric.closedBall_subset_closedBall (by
    change (c.radius:ℝ) ≤ (3:ℝ)*(c.radius:ℝ); linarith [c.radius.property]))) c.right_supported
  left_dominated := p.dominated
  right_dominated := dominated_mono_constant c.right_dominated (c.cap_le_nextCap env)
  left_entropy := p.finite_entropy
  right_entropy := c.right_entropy
  short := by simpa only [NNReal.coe_div,NNReal.coe_ofNat] using p.short_halves.2

end CellMidpoint
end WeakHessian
end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Geodesics_Join
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Filter
open Set Filter MeasureTheory InformationTheory
open Set Filter
open scoped Topology
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set Filter Topology

namespace WeakHessian
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

universe u
variable {X : Type u} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [SecondCountableTopology X] [ProperSpace X]
variable {m : Measure X} [SigmaFinite m] {K N : ℝ}

namespace CellMidpoint
variable {c : EntropyCell m K N} (p : CellMidpoint c) (env : CDEnvironment m K N)

omit [SigmaFinite m] in
lemma exists_join (l : CellPlan (p.leftCell env)) (r : CellPlan (p.rightCell env)) :
    ∃ q : CellPlan c,
      (∀ t, interpolation (q.law:Measure (Curve X)) (halfTime t) = interpolation (l.law:Measure (Curve X)) t) ∧
      (∀ t, interpolation (q.law:Measure (Curve X)) (rightTime t) = interpolation (r.law:Measure (Curve X)) t) ∧
      (q.law:Measure (Curve X)).map halfCurve = (l.law:Measure (Curve X)) ∧
      (q.law:Measure (Curve X)).map rightCurve = (r.law:Measure (Curve X)) := by
  have hl0 : interpolation (l.law:Measure (Curve X)) timeZero = (c.leftLaw:Measure X) :=
    l.optimal.1.interpolation_endpoints.1
  have hl1 : interpolation (l.law:Measure (Curve X)) timeOne = (p.middle:Measure X) :=
    l.optimal.1.interpolation_endpoints.2
  have hr0 : interpolation (r.law:Measure (Curve X)) timeZero = (p.middle:Measure X) :=
    r.optimal.1.interpolation_endpoints.1
  have hr1 : interpolation (r.law:Measure (Curve X)) timeOne = (c.rightLaw:Measure X) :=
    r.optimal.1.interpolation_endpoints.2
  have hlopt : IsOptimalCoupling (endpointCoupling (l.law:Measure (Curve X)))
      (interpolation ((p.law:Measure (Curve X)).map halfCurve) timeZero)
      (interpolation ((p.law:Measure (Curve X)).map halfCurve) timeOne) := by
    rw [interpolation_map_half,interpolation_map_half,halfTime_zero,halfTime_one,p.optimal.1.interpolation_endpoints.1]
    exact l.optimal
  have hropt : IsOptimalCoupling (endpointCoupling (r.law:Measure (Curve X)))
      (interpolation ((p.law:Measure (Curve X)).map rightCurve) timeZero)
      (interpolation ((p.law:Measure (Curve X)).map rightCurve) timeOne) := by
    rw [interpolation_map_right,interpolation_map_right,rightTime_zero,rightTime_one,p.optimal.1.interpolation_endpoints.2]
    exact r.optimal
  have hel := (optimalPlan_energy_le hlopt (integrable_plan_energy_half p.geodesic p.toCellPlan.integrable_energy)).2
  have her := (optimalPlan_energy_le hropt (integrable_plan_energy_right p.geodesic p.toCellPlan.integrable_energy)).2
  rw [planEnergy_half p.geodesic] at hel
  rw [planEnergy_right p.geodesic] at her
  obtain ⟨q,hqp,hqg,hqo,hql,hqr,hqlm,hqrm⟩ := exists_optimal_geodesic_join
    (l.law:Measure (Curve X)) (r.law:Measure (Curve X)) (p.law:Measure (Curve X))
    (hl1.trans hr0.symm) l.geodesic r.geodesic l.integrable_energy r.integrable_energy
    p.toCellPlan.integrable_energy (by simpa only [hl0,hr1] using p.optimal) (by linarith)
  have hqo' : IsOptimalCoupling (endpointCoupling q) c.leftLaw c.rightLaw := by
    rwa [hl0,hr1] at hqo
  exact ⟨⟨⟨q,hqp⟩,hqg,hqo'⟩,hql,hqr,hqlm,hqrm⟩

noncomputable def join (l : CellPlan (p.leftCell env)) (r : CellPlan (p.rightCell env)) :
    CellPlan c := Classical.choose (p.exists_join env l r)

omit [SigmaFinite m] in
lemma join_half (l : CellPlan (p.leftCell env)) (r : CellPlan (p.rightCell env)) (t : Time) :
    interpolation ((p.join env l r).law:Measure (Curve X)) (halfTime t) =
      interpolation (l.law:Measure (Curve X)) t := (Classical.choose_spec (p.exists_join env l r)).1 t

omit [SigmaFinite m] in
lemma join_right (l : CellPlan (p.leftCell env)) (r : CellPlan (p.rightCell env)) (t : Time) :
    interpolation ((p.join env l r).law:Measure (Curve X)) (rightTime t) =
      interpolation (r.law:Measure (Curve X)) t := (Classical.choose_spec (p.exists_join env l r)).2.1 t

end CellMidpoint

namespace CDEnvironment
variable (env : CDEnvironment m K N)

noncomputable def build : (n : ℕ) → (c : EntropyCell m K N) → CellPlan c
  | 0,c => (env.midpoint c).toCellPlan
  | n+1,c => (env.midpoint c).join env
    (build n ((env.midpoint c).leftCell env))
    (build n ((env.midpoint c).rightCell env))

lemma build_half (n : ℕ) (c : EntropyCell m K N) (t : Time) :
    interpolation ((env.build (n+1) c).law:Measure (Curve X)) (halfTime t) =
      interpolation ((env.build n ((env.midpoint c).leftCell env)).law:Measure (Curve X)) t :=
  (env.midpoint c).join_half env _ _ t

lemma build_right (n : ℕ) (c : EntropyCell m K N) (t : Time) :
    interpolation ((env.build (n+1) c).law:Measure (Curve X)) (rightTime t) =
      interpolation ((env.build n ((env.midpoint c).rightCell env)).law:Measure (Curve X)) t :=
  (env.midpoint c).join_right env _ _ t

lemma build_stable (n k : ℕ) (hnk : n ≤ k) (c : EntropyCell m K N) (t : Time)
    (ht : t ∈ dyadicTimes n) :
    interpolation ((env.build k c).law:Measure (Curve X)) t =
      interpolation ((env.build n c).law:Measure (Curve X)) t := by
  induction n generalizing k c t with
  | zero =>
    rcases ht with rfl | ht
    · rw [(env.build k c).optimal.1.interpolation_endpoints.1,
        (env.build 0 c).optimal.1.interpolation_endpoints.1]
    · have H : t = timeOne := ht
      rw [H,(env.build k c).optimal.1.interpolation_endpoints.2,
        (env.build 0 c).optimal.1.interpolation_endpoints.2]
  | succ n ih =>
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    rcases ht with ⟨s,hs,rfl⟩ | ⟨s,hs,rfl⟩
    · rw [env.build_half,env.build_half]
      exact ih k (by omega) _ s hs
    · rw [env.build_right,env.build_right]
      exact ih k (by omega) _ s hs

end CDEnvironment
end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_Law
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Filter
open Set Filter MeasureTheory InformationTheory
open Set Filter
open scoped Topology
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set Filter Topology

namespace WeakHessian
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

universe u
variable {X : Type u} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [SecondCountableTopology X] [ProperSpace X]
variable {m : Measure X} [SigmaFinite m] {K N : ℝ}

def lawAt (π : ProbabilityMeasure (Curve X)) (t : Time) : ProbabilityMeasure X :=
  π.map (continuous_eval_const t).aemeasurable

omit [SecondCountableTopology X] [ProperSpace X] in
lemma continuous_lawAt_plan (t : Time) : Continuous (fun π : ProbabilityMeasure (Curve X) => lawAt π t) :=
  ProbabilityMeasure.continuous_map (continuous_eval_const t)

def cellPlanFamily (c : EntropyCell m K N) : Set (ProbabilityMeasure (Curve X)) :=
  {π | (∀ᵐ γ ∂(π:Measure (Curve X)), IsGeodesic γ) ∧
    IsOptimalCoupling (endpointCoupling (π:Measure (Curve X))) c.leftLaw c.rightLaw}

omit [SigmaFinite m] in
lemma isCompact_cellPlanFamily (c : EntropyCell m K N) (p : CellPlan c) :
    IsCompact (cellPlanFamily c) := by
  let cost := ∫ γ, clippedEndpointCost c.radius γ ∂(p.law:Measure (Curve X))
  have hc : 0 ≤ cost := integral_nonneg (clippedEndpointCost_nonneg c.radius)
  have hps := optimalPlan_supported_tube p.law p.geodesic p.optimal.1 c.left_supported c.right_supported
  have hcostp := endpointCost_eq_clipped_integral (p.law:Measure (Curve X)) hps
  have he : cellPlanFamily c = {π : ProbabilityMeasure (Curve X) |
      (π:Measure (Curve X)) (boundedEndpointTube c.center c.radius)ᶜ = 0 ∧
      lawAt π timeZero = c.leftLaw ∧ lawAt π timeOne = c.rightLaw ∧
      (∫ γ, clippedEndpointCost c.radius γ ∂(π:Measure (Curve X))) ≤ cost} := by
    ext π
    constructor
    · rintro ⟨hg,ho⟩
      have hs := optimalPlan_supported_tube π hg ho.1 c.left_supported c.right_supported
      refine ⟨hs,Subtype.ext ho.1.interpolation_endpoints.1,Subtype.ext ho.1.interpolation_endpoints.2,?_⟩
      apply (ENNReal.ofReal_le_ofReal_iff hc).mp
      rw [← endpointCost_eq_clipped_integral (π:Measure (Curve X)) hs,← hcostp]
      exact ho.2 _ p.optimal.1
    · rintro ⟨hs,h0,h1,hcost⟩
      have hend : IsCoupling (endpointCoupling (π:Measure (Curve X))) c.leftLaw c.rightLaw := by
        have H := endpointCoupling_couples (π:Measure (Curve X))
        have h0' : interpolation (π:Measure (Curve X)) timeZero = (c.leftLaw:Measure X) := congrArg Subtype.val h0
        have h1' : interpolation (π:Measure (Curve X)) timeOne = (c.rightLaw:Measure X) := congrArg Subtype.val h1
        rwa [h0',h1'] at H
      refine ⟨(ae_iff.mpr hs).mono (fun γ hγ => hγ.1),hend,?_⟩
      intro q hq
      apply le_trans ?_ (p.optimal.2 q hq)
      rw [endpointCost_eq_clipped_integral (π:Measure (Curve X)) hs,hcostp]
      exact ENNReal.ofReal_le_ofReal hcost
  rw [he]
  apply (isCompact_probability_supported (isCompact_boundedEndpointTube c.center c.radius)).inter_right
  exact (isClosed_eq (continuous_lawAt_plan timeZero) continuous_const).inter
    ((isClosed_eq (continuous_lawAt_plan timeOne) continuous_const).inter
      (isClosed_le (ProbabilityMeasure.continuous_integral_boundedContinuousFunction _) continuous_const))

namespace CDEnvironment
variable (env : CDEnvironment m K N)

def stablePlanFamily (c : EntropyCell m K N) (n : ℕ) : Set (ProbabilityMeasure (Curve X)) :=
  cellPlanFamily c ∩ {π | ∀ t ∈ dyadicTimes n, lawAt π t = lawAt (env.build n c).law t}

lemma stablePlanFamily_closed (c : EntropyCell m K N) (n : ℕ) :
    IsClosed (env.stablePlanFamily c n) := by
  apply (isCompact_cellPlanFamily c (env.build 0 c)).isClosed.inter
  have he : {π : ProbabilityMeasure (Curve X) | ∀ t ∈ dyadicTimes n,
      lawAt π t = lawAt (env.build n c).law t} =
      ⋂ t : Time, ⋂ (_ : t ∈ dyadicTimes n), {π | lawAt π t = lawAt (env.build n c).law t} := by
    ext π; simp only [mem_ofPred_eq,mem_iInter]
  rw [he]
  exact isClosed_iInter fun t => isClosed_iInter fun _ => isClosed_eq (continuous_lawAt_plan t) continuous_const

lemma exists_stable_plan (c : EntropyCell m K N) :
    ∃ p : CellPlan c, ∀ n t, t ∈ dyadicTimes n →
      interpolation (p.law:Measure (Curve X)) t = interpolation ((env.build n c).law:Measure (Curve X)) t := by
  have hmono (n : ℕ) : env.stablePlanFamily c (n+1) ⊆ env.stablePlanFamily c n := by
    intro π hπ
    refine ⟨hπ.1,fun t ht => ?_⟩
    rw [hπ.2 t (monotone_dyadicTimes (Nat.le_succ n) ht)]
    exact Subtype.ext (env.build_stable n (n+1) (Nat.le_succ n) c t ht)
  have hne (n : ℕ) : (env.stablePlanFamily c n).Nonempty :=
    ⟨(env.build n c).law,⟨(env.build n c).geodesic,(env.build n c).optimal⟩,fun _ _ => rfl⟩
  have hc : IsCompact (env.stablePlanFamily c 0) :=
    (isCompact_cellPlanFamily c (env.build 0 c)).of_isClosed_subset (env.stablePlanFamily_closed c 0) inter_subset_left
  obtain ⟨π,hπ⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (env.stablePlanFamily c) hmono hne hc (env.stablePlanFamily_closed c)
  have hπs := mem_iInter.mp hπ
  refine ⟨⟨π,(hπs 0).1.1,(hπs 0).1.2⟩,fun n t ht => ?_⟩
  exact congrArg Subtype.val ((hπs n).2 t ht)

noncomputable def limitPlan (c : EntropyCell m K N) : CellPlan c :=
  Classical.choose (env.exists_stable_plan c)

end CDEnvironment
end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_GammaRepresentativePairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile190
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

def BoundedLipschitzRepresentative (m : Measure X) (u : X → ℝ) : Prop :=
  ∃ v : X → ℝ,GloballyLipschitz v ∧ BoundedFunction v ∧ v =ᵐ[m] u

end WeakHessian

end
end InlinedFile190

end OAI
end


