-- Prove2me | Definitions.Def_OAIQ2Rw000
-- name    : OAIQ2Rw000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-25T22:07:24.87699+00:00
-- url     : https://prove2.me/theorems/1923200d-9571-4a2c-be76-9d6af828dc36
-- title:
--   Definitions bundle OAIQ2Rw000 of the split of OpenAI, Invariant-projection counterexamples for every irrational rotation
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ContinuousCircleWeight.main_theorem`, carved from OpenAI's openai/math development (OpenAI, *Invariant-projection counterexamples for every irrational rotation*, OpenAI Math Release, September 27, 2026, result family 293, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 478 declarations of OpenAI's Lean: 138 definitions, 5 inductive types or structures, 15 instances and 320 theorems. The definitions and types are `OAI.CircleConcentration.X`, `OAI.CircleConcentration.bump`, `OAI.CircleConcentration.moveCorrection`, `OAI.CircleConcentration.moveTerm`, `OAI.CircleConcentration.movedDrop`, `OAI.CircleConcentration.orbitMin`, `OAI.CircleConcentration.orbitRadius`, `OAI.CircleConcentration.partition`, `OAI.CircleConcentration.partitionDenom`, `OAI.CircleConcentration.supportRadius`, `OAI.CircleCoupling.CoordinateParameters`, `OAI.CircleCoupling.CoordinateParameters.Sample`, `OAI.CircleCoupling.CoordinateParameters.bottomLabel`, `OAI.CircleCoupling.CoordinateParameters.law`, `OAI.CircleCoupling.CoordinateParameters.marginEvent`, `OAI.CircleCoupling.CoordinateParameters.prob`, `OAI.CircleCoupling.CoordinateParameters.tagEvent`, `OAI.CircleCoupling.CoordinateParameters.topLabel`, `OAI.CircleCoupling.CoordinateParameters.untaggedMargin`, `OAI.CircleCoupling.CoordinateParameters.width`, `OAI.CircleCoupling.CoordinateParameters.ρ`, `OAI.CircleCoupling.CoordinateParameters.σ`, `OAI.CircleCoupling.CoordinateParameters.τ`, `OAI.CircleCoupling.DigitSystem`, `OAI.CircleCoupling.DigitSystem.Sample`, `OAI.CircleCoupling.DigitSystem.Samples`, `OAI.CircleCoupling.DigitSystem.coordinateMargin`, `OAI.CircleCoupling.DigitSystem.coordinateTag`, `OAI.CircleCoupling.DigitSystem.coordinateUntaggedMargin`, `OAI.CircleCoupling.DigitSystem.crossingDigit`, `OAI.CircleCoupling.DigitSystem.crossingWidth`, `OAI.CircleCoupling.DigitSystem.endpoint`, `OAI.CircleCoupling.DigitSystem.error`, `OAI.CircleCoupling.DigitSystem.law`, `OAI.CircleCoupling.DigitSystem.observe`, `OAI.CircleCoupling.DigitSystem.oneTagEvent`, `OAI.CircleCoupling.DigitSystem.probability`, `OAI.CircleCoupling.DigitSystem.radix`, `OAI.CircleCoupling.DigitSystem.supported`, `OAI.CircleCoupling.LabelledDigits` and 103 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `RotationWeights_ActualDigits`, `RotationWeights_Concentration`, `RotationWeights_ConditionalBounds`, `RotationWeights_CoordinateLaws`, `RotationWeights_CouplingMoments`, `RotationWeights_CrossingEstimates`, `RotationWeights_DigitCouplings`, `RotationWeights_Discrepancy`, `RotationWeights_EndpointMoments`, `RotationWeights_FiniteSampling`, `RotationWeights_FourierSampling`, `RotationWeights_MeasurableWeight`, `RotationWeights_NestedAngles`, `RotationWeights_PhaseWeights`, `RotationWeights_Polar`, `RotationWeights_ProductSampling`, `RotationWeights_RadixDigits`, `RotationWeights_ReturnSamples`, `RotationWeights_Rounding`, `RotationWeights_SamplingBounds`, `RotationWeights_SamplingStage`, `RotationWeights_TaggedEvents`, `RotationWeights_TrialBounds`, `RotationWeights_WeakSampling`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ2Rw002`; the proof of `OAI.ContinuousCircleWeight.borel_weight_transport`.
-- source:
--   OpenAI, Invariant-projection counterexamples for every irrational rotation, OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 293; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Invariant-projection-counterexamples-for-every-irrational-rotation-September-27-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ2_Rot.Compat
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
/-- Mathlib's newer name for `measurable_pi_lambda` (with `f` implicit). -/
theorem Measurable.of_eval {δ ι : Type*} {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {f : δ → ∀ i, π i}
    (h : ∀ i, Measurable fun a => f a i) : Measurable f := measurable_pi_lambda f h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_Polar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CirclePolar

universe uH

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ComplexInnerProductSpace
open MeasureTheory Filter Set

open Set
open scoped ComplexInnerProductSpace
section
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
abbrev Op := H →L[ℂ] H

def absOp (A : Op (H := H)) : Op (H := H) := CFC.sqrt (star A * A)

def closedRange (A : Op (H := H)) : Submodule ℂ H := A.toLinearMap.range.topologicalClosure

instance instCompleteSpaceSubtypeMemSubmoduleComplexClosedRange (A : Op (H := H)) : CompleteSpace (closedRange A) :=
  inferInstanceAs (CompleteSpace A.toLinearMap.range.topologicalClosure)

def intoRange (A : Op (H := H)) : H →ₗ[ℂ] closedRange A :=
  A.toLinearMap.codRestrict _ (fun x ↦ A.toLinearMap.range.le_topologicalClosure ⟨x,rfl⟩)

def polarCore (A : Op (H := H)) : closedRange (absOp A) →L[ℂ] H :=
  A.toLinearMap.extendOfNorm (intoRange (absOp A))

def polar (A : Op (H := H)) : Op (H := H) :=
  (polarCore A).comp (closedRange (absOp A)).orthogonalProjectionOnto

end



end CirclePolar

end

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_WeakSampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

universe uX uκ uP uι

namespace ContinuousCircleWeight
open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ComplexInnerProductSpace
open MeasureTheory Filter Set
open Set
open scoped ComplexInnerProductSpace
open Set
open scoped ComplexInnerProductSpace

open MeasureTheory Set Filter Topology Algebra Submodule
open scoped BigOperators ComplexConjugate

variable {X : Type uX} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X]
  [BorelSpace X]

namespace Sampling

abbrev CircleX := AddCircle (1 : ℝ)

variable {ι : Type uι} [Fintype ι]

def torusFourier (a : ι → ℤ) : C(ι → CircleX, ℂ) where
  toFun x := ∏ i, fourier (a i) (x i)
  continuous_toFun := by fun_prop

@[simp] theorem torusFourier_apply (a : ι → ℤ) (x : ι → CircleX) :
    torusFourier a x = ∏ i, fourier (a i) (x i) := rfl

@[simp] theorem torusFourier_zero : torusFourier (0 : ι → ℤ) = 1 := by
  ext x
  simp

def characterCurve (q : ι → ℤ) : C(CircleX, ι → CircleX) where
  toFun x i := q i • x
  continuous_toFun := by fun_prop

end Sampling
end ContinuousCircleWeight

end

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_FourierSampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

universe uι uκ uE

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ComplexInnerProductSpace
open MeasureTheory Filter Set
open Set
open scoped ComplexInnerProductSpace
open Set
open scoped ComplexInnerProductSpace

namespace ContinuousCircleWeight
open MeasureTheory Set Filter Topology
open scoped BigOperators ComplexConjugate
namespace Sampling

def geometricFourierSum (H : ℕ) : C(CircleX, ℂ) := ∑ p ∈ Finset.range H, fourier (p : ℤ)

def fejerKernel (H : ℕ) : C(CircleX, ℝ) :=
  ⟨fun x => ‖geometricFourierSum H x‖ ^ 2 / H, by fun_prop⟩

@[simp] lemma geometricFourierSum_apply (H : ℕ) (x : CircleX) :
    geometricFourierSum H x = ∑ p ∈ Finset.range H, fourier (p : ℤ) x := by
  simp [geometricFourierSum]

@[simp] lemma fejerKernel_apply (H : ℕ) (x : CircleX) :
    fejerKernel H x = ‖geometricFourierSum H x‖ ^ 2 / H := by
  rfl

lemma periodic_integral_bounds {f : ℝ → ℝ} (hp : Function.Periodic f 1)
    (hi : ∀ a b, IntervalIntegrable f volume a b) (hn : ∀ x, 0 ≤ f x)
    {a b : ℝ} (hab : a ≤ b) :
    (b - a - 1) * (∫ x in a..a+1, f x) ≤ ∫ x in a..b, f x ∧
    (∫ x in a..b, f x) ≤ (b - a + 1) * (∫ x in a..a+1, f x) := by
  let n : ℕ := ⌊b - a⌋₊
  have hnl : (n : ℝ) ≤ b - a := Nat.floor_le (sub_nonneg.mpr hab)
  have hnu : b - a < (n : ℝ) + 1 := Nat.lt_floor_add_one _
  have hm : 0 ≤ ∫ x in a..a+1, f x :=
    intervalIntegral.integral_nonneg (by linarith) (fun x _ => hn x)
  have he (k : ℕ) : (∫ x in a..a+k, f x) = k * ∫ x in a..a+1, f x := by
    simpa using hp.intervalIntegral_add_zsmul_eq (k : ℤ) a hi
  have hlo : (∫ x in a..a+n, f x) ≤ ∫ x in a..b, f x :=
    intervalIntegral.integral_mono_interval le_rfl (by have := Nat.cast_nonneg (α := ℝ) n; linarith) (by linarith)
      (ae_of_all _ hn) (hi a b)
  have hup : (∫ x in a..b, f x) ≤ ∫ x in a..a+(n+1 : ℕ), f x :=
    intervalIntegral.integral_mono_interval le_rfl hab (by push_cast; linarith)
      (ae_of_all _ hn) (hi a _)
  rw [he n] at hlo
  rw [he (n+1)] at hup
  push_cast at hup
  constructor
  · exact le_trans (mul_le_mul_of_nonneg_right (by linarith) hm) hlo
  · exact le_trans hup (mul_le_mul_of_nonneg_right (by linarith) hm)

def intervalLaw (a b : ℝ) : Measure ℝ :=
  (ENNReal.ofReal (b-a))⁻¹ • volume.restrict (Ioc a b)

lemma intervalLaw_probability {a b : ℝ} (hab : a < b) :
    IsProbabilityMeasure (intervalLaw a b) := by
  constructor
  simp only [intervalLaw, Measure.smul_apply, Measure.restrict_apply_univ,
    Real.volume_Ioc, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (by simpa using sub_pos.mpr hab) ENNReal.ofReal_ne_top

lemma integral_intervalLaw {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) {a b : ℝ} (hab : a ≤ b) :
    (∫ x, f x ∂intervalLaw a b) = (b-a)⁻¹ • ∫ x in a..b, f x := by
  rw [intervalLaw, integral_smul_measure, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hab), intervalIntegral.integral_of_le hab]

lemma intervalIntegrable_circle_comp {f : CircleX → ℝ}
    (hf : Integrable f (volume : Measure CircleX)) (a b : ℝ) :
    IntervalIntegrable (fun x : ℝ => f x) volume a b := by
  have hp : Function.Periodic (fun x : ℝ => f x) 1 := by
    intro x
    simp only [AddCircle.coe_add_period]
  apply hp.intervalIntegrable₀ (by norm_num)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  have hmp := AddCircle.measurePreserving_mk (1 : ℝ) 0
  simpa only [zero_add, Function.comp_def, IntegrableOn] using
    (hmp.integrable_comp hf.aestronglyMeasurable).mpr hf

lemma circle_scaled_integral_bounds {f : CircleX → ℝ}
    (hf : Integrable f (volume : Measure CircleX)) (hn : ∀ x, 0 ≤ f x)
    {a b c : ℝ} (hab : a < b) (hc : 0 < c) :
    (1 - 1/(c*(b-a))) * (∫ x, f x) ≤
      (∫ x, f ((c*x : ℝ) : CircleX) ∂intervalLaw a b) ∧
    (∫ x, f ((c*x : ℝ) : CircleX) ∂intervalLaw a b) ≤
      (1 + 1/(c*(b-a))) * (∫ x, f x) := by
  have hlen : 0 < b-a := sub_pos.mpr hab
  have hp : Function.Periodic (fun x : ℝ => f x) 1 := by
    intro x
    simp only [AddCircle.coe_add_period]
  have h := periodic_integral_bounds hp (intervalIntegrable_circle_comp hf)
    (fun x => hn x) (mul_le_mul_of_nonneg_left hab.le hc.le)
  rw [AddCircle.intervalIntegral_preimage] at h
  rw [integral_intervalLaw _ hab.le,
    intervalIntegral.integral_comp_mul_left (fun x : ℝ => f (x : CircleX)) hc.ne']
  simp only [smul_eq_mul]
  constructor
  · have ht := mul_le_mul_of_nonneg_left h.1 (by positivity : 0 ≤ (b-a)⁻¹*c⁻¹)
    convert! ht using 1 <;> field_simp
  · have ht := mul_le_mul_of_nonneg_left h.2 (by positivity : 0 ≤ (b-a)⁻¹*c⁻¹)
    convert! ht using 1 <;> field_simp

def phasePair (c d : ℝ) (t : ℝ) : CircleX × CircleX :=
  (((c*t : ℝ) : CircleX), ((d*t : ℝ) : CircleX))

end Sampling
end ContinuousCircleWeight

end

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_PhaseWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CircleSampling

universe uE

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ComplexInnerProductSpace
open MeasureTheory Filter Set
open Set
open scoped ComplexInnerProductSpace
open Set
open scoped ComplexInnerProductSpace
open MeasureTheory Set Filter Topology
open scoped BigOperators ComplexConjugate

abbrev CircleX := AddCircle (1 : ℝ)

instance instIsProbabilityMeasureCircleXVolume : IsProbabilityMeasure (volume : Measure CircleX) := by
  rw [AddCircle.volume_eq_smul_haarAddCircle]
  norm_num
  infer_instance

lemma volume_singleton_zero (s : CircleX) : volume ({s} : Set CircleX) = 0 := by
  rw [← Metric.closedBall_zero, AddCircle.volume_closedBall]
  norm_num

def repr (x : CircleX) : ℝ := (AddCircle.measurableEquivIco 1 0 x).val
lemma measurable_repr : Measurable repr :=
  measurable_subtype_coe.comp (AddCircle.measurableEquivIco 1 0).measurable
lemma repr_mem (x : CircleX) : repr x ∈ Ico 0 1 := by
  simpa only [repr, zero_add] using (AddCircle.measurableEquivIco 1 0 x).property
lemma repr_coe {s : ℝ} (hs : s ∈ Ico 0 1) : repr (s : CircleX) = s := by
  exact congrArg Subtype.val (AddCircle.equivIco_coe_eq (by simpa using hs))
lemma coe_repr (x : CircleX) : (repr x : CircleX) = x :=
  AddCircle.coe_equivIco

lemma integral_repr {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) : ∫ x : CircleX, f (repr x) = ∫ s in Ioc 0 1, f s := by
  rw [← AddCircle.integral_preimage (1 : ℝ) 0]
  simp only [zero_add]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc,
    ae_restrict_of_ae (show ∀ᵐ s : ℝ, s ≠ 1 from by simp [ae_iff])] with s hs hne
  rw [repr_coe ⟨le_of_lt hs.1, lt_of_le_of_ne hs.2 hne⟩]

def delta (s : ℝ) : ℝ := min s (1-s)
def weight (ℓ α s t : ℝ) : ℝ :=
  if α ≤ delta s ∧ 0 < t ∧ t < ℓ * delta s then 1 / (ℓ * delta s) else 0
def uPos (ℓ α : ℝ) (s t : CircleX) : ℝ := weight ℓ α (repr s) (repr t)
def uNeg (ℓ α : ℝ) (s t : CircleX) : ℝ := uPos ℓ α (s-t) t

lemma measurable_delta : Measurable delta := by unfold delta; fun_prop
lemma measurable_weight (ℓ α : ℝ) : Measurable (fun z : ℝ × ℝ ↦ weight ℓ α z.1 z.2) := by
  unfold weight
  exact Measurable.ite ((measurableSet_le measurable_const (measurable_delta.comp measurable_fst)).inter
    ((measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_lt measurable_snd (measurable_const.mul (measurable_delta.comp measurable_fst)))))
    (measurable_const.div (measurable_const.mul (measurable_delta.comp measurable_fst))) measurable_const
lemma measurable_uPos (ℓ α : ℝ) : Measurable (Function.uncurry (uPos ℓ α)) :=
  (measurable_weight ℓ α).comp ((measurable_repr.comp measurable_fst).prodMk
    (measurable_repr.comp measurable_snd))
lemma measurable_uNeg (ℓ α : ℝ) : Measurable (Function.uncurry (uNeg ℓ α)) :=
  (measurable_uPos ℓ α).comp ((measurable_fst.sub measurable_snd).prodMk measurable_snd)

lemma weight_bounds {ℓ α : ℝ} (hℓ : 0 < ℓ) (hα : 0 < α) (s t : ℝ) :
    0 ≤ weight ℓ α s t ∧ weight ℓ α s t ≤ 1 / (ℓ * α) := by
  unfold weight
  split_ifs with h
  · have hd : 0 < ℓ * delta s := mul_pos hℓ (lt_of_lt_of_le hα h.1)
    exact ⟨le_of_lt (one_div_pos.mpr hd),
      one_div_le_one_div_of_le (mul_pos hℓ hα) (mul_le_mul_of_nonneg_left h.1 hℓ.le)⟩
  · exact ⟨le_rfl, (one_div_pos.mpr (mul_pos hℓ hα)).le⟩

lemma delta_lipschitz (s t : ℝ) : |delta s - delta t| ≤ |s-t| := by
  rw [abs_le]
  have h1 := le_abs_self (s-t)
  have h2 := neg_abs_le (s-t)
  unfold delta
  simp only [min_def]
  split_ifs <;> constructor <;> linarith
lemma delta_pos {s : ℝ} (hs : s ∈ Ioo 0 1) : 0 < delta s := by
  exact lt_min hs.1 (sub_pos.mpr hs.2)
lemma delta_le_half (s : ℝ) : delta s ≤ 1/2 := by
  unfold delta
  rcases le_total s (1/2) with h | h
  · exact le_trans (min_le_left _ _) h
  · exact le_trans (min_le_right _ _) (by linarith)

lemma weight_integral_t {ℓ α s : ℝ} (hℓ : 0 < ℓ) (hℓ1 : ℓ < 1) (hα : 0 < α) :
    (∫ t in Ioc 0 1, weight ℓ α s t) = if α ≤ delta s then 1 else 0 := by
  by_cases h : α ≤ delta s
  · have hd : 0 < ℓ * delta s := mul_pos hℓ (lt_of_lt_of_le hα h)
    have hd1 : ℓ * delta s < 1 := by
      have := delta_le_half s
      nlinarith
    have he : (fun t ↦ weight ℓ α s t) = (Ioo 0 (ℓ * delta s)).indicator
        (fun _ ↦ 1 / (ℓ * delta s)) := by
      ext t
      simp only [weight, h, true_and, indicator, mem_Ioo]
    rw [he, integral_indicator measurableSet_Ioo, Measure.restrict_restrict measurableSet_Ioo]
    have hs : Ioo 0 (ℓ * delta s) ∩ Ioc 0 1 = Ioo 0 (ℓ * delta s) := by
      apply inter_eq_left.mpr
      intro t ht
      exact ⟨ht.1, le_of_lt (lt_trans ht.2 hd1)⟩
    rw [hs, integral_const]
    simp only [Measure.real, Measure.restrict_apply_univ, Real.volume_Ioo, sub_zero,
      ENNReal.toReal_ofReal hd.le, smul_eq_mul, ite_eq_left h]
    exact mul_one_div_cancel hd.ne'
  · simp [weight, h]

lemma uPos_integral_t {ℓ α : ℝ} (hℓ : 0 < ℓ) (hℓ1 : ℓ < 1) (hα : 0 < α)
    (s : CircleX) : (∫ t, uPos ℓ α s t) = if α ≤ delta (repr s) then 1 else 0 := by
  change (∫ t : CircleX, weight ℓ α (repr s) (repr t)) = _
  rw [integral_repr]
  exact weight_integral_t hℓ hℓ1 hα

lemma integral_uPos {ℓ α : ℝ} (hℓ : 0 < ℓ) (hℓ1 : ℓ < 1)
    (hα : 0 < α) (hα2 : α ≤ 1/2) :
    (∫ s : CircleX, ∫ t : CircleX, uPos ℓ α s t) = 1 - 2 * α := by
  simp_rw [uPos_integral_t hℓ hℓ1 hα]
  change (∫ s : CircleX, (fun r ↦ if α ≤ delta r then (1 : ℝ) else 0) (repr s)) = _
  rw [integral_repr (fun r : ℝ ↦ if α ≤ delta r then (1 : ℝ) else 0)]
  have he : (fun s : ℝ ↦ if α ≤ delta s then (1 : ℝ) else 0) = (Icc α (1-α)).indicator (fun _ ↦ 1) := by
    ext s
    simp [delta, indicator, mem_Icc, le_sub_comm]
  rw [he, integral_indicator measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc]
  have hs : Icc α (1-α) ∩ Ioc 0 1 = Icc α (1-α) := by
    apply inter_eq_left.mpr
    intro s hs
    exact ⟨lt_of_lt_of_le hα hs.1, le_trans hs.2 (by linarith)⟩
  rw [hs, integral_const]
  simp [Measure.real, Real.volume_Icc, show 0 ≤ (1-α)-α by linarith]
  ring

lemma integrable_uPos {ℓ α : ℝ} (hℓ : 0 < ℓ) (hα : 0 < α) :
    Integrable (Function.uncurry (uPos ℓ α)) (volume.prod volume) := by
  apply Integrable.of_bound (measurable_uPos ℓ α).aestronglyMeasurable (1 / (ℓ * α))
  filter_upwards [] with z
  rcases weight_bounds hℓ hα (repr z.1) (repr z.2) with ⟨h0, hB⟩
  simpa only [Function.uncurry, uPos, Real.norm_eq_abs, abs_of_nonneg h0] using hB

lemma integrable_uNeg {ℓ α : ℝ} (hℓ : 0 < ℓ) (hα : 0 < α) :
    Integrable (Function.uncurry (uNeg ℓ α)) (volume.prod volume) := by
  apply Integrable.of_bound (measurable_uNeg ℓ α).aestronglyMeasurable (1 / (ℓ * α))
  filter_upwards [] with z
  rcases weight_bounds hℓ hα (repr (z.1-z.2)) (repr z.2) with ⟨h0, hB⟩
  simpa only [Function.uncurry, uNeg, uPos, Real.norm_eq_abs, abs_of_nonneg h0] using hB

lemma integral_uNeg {ℓ α : ℝ} (hℓ : 0 < ℓ) (hℓ1 : ℓ < 1)
    (hα : 0 < α) (hα2 : α ≤ 1/2) :
    (∫ s : CircleX, ∫ t : CircleX, uNeg ℓ α s t) = 1 - 2 * α := by
  rw [integral_integral_swap (integrable_uNeg hℓ hα)]
  have he (t : CircleX) : (∫ s : CircleX, uNeg ℓ α s t) = ∫ s : CircleX, uPos ℓ α s t :=
    integral_sub_right_eq_self (fun s ↦ uPos ℓ α s t) t
  simp_rw [he]
  rw [← integral_integral_swap (integrable_uPos hℓ hα)]
  exact integral_uPos hℓ hℓ1 hα hα2

lemma uNeg_unwrapped {ℓ α a b : ℝ} (hℓ : 0 < ℓ) (hℓ1 : ℓ < 1) (hα : 0 < α)
    (ha : a ∈ Ico 0 1) (hb : b ∈ Ico 0 1) :
    uNeg ℓ α (a : CircleX) (b : CircleX) = weight ℓ α (a-b) b := by
  unfold uNeg uPos
  rw [repr_coe hb, ← AddCircle.coe_sub]
  by_cases hba : b ≤ a
  · rw [repr_coe ⟨sub_nonneg.mpr hba, by linarith [ha.2, hb.1]⟩]
  · have hab : a < b := lt_of_not_ge hba
    have hr : repr ((a-b : ℝ) : CircleX) = a-b+1 := by
      rw [← AddCircle.coe_add_period 1 (a-b), repr_coe ⟨by linarith [ha.1, hb.2], by linarith⟩]
    rw [hr]
    have hn1 : ¬(α ≤ delta (a-b) ∧ 0 < b ∧ b < ℓ * delta (a-b)) := by
      intro h
      have := min_le_left (a-b) (1-(a-b))
      change delta (a-b) ≤ a-b at this
      linarith [h.1]
    have hn2 : ¬(α ≤ delta (a-b+1) ∧ 0 < b ∧ b < ℓ * delta (a-b+1)) := by
      intro h
      have hd : delta (a-b+1) ≤ b-a := by
        exact (min_le_right _ _).trans_eq (by ring)
      have := mul_le_mul_of_nonneg_left hd hℓ.le
      have := mul_le_mul_of_nonneg_left (show b-a ≤ b by linarith [ha.1]) hℓ.le
      nlinarith [h.2.1, h.2.2]
    simp only [weight, ite_eq_right hn1, ite_eq_right hn2]

lemma integral_delta_small {r : ℝ} (hr : 0 < r) :
    (∫ s : CircleX, if delta (repr s) < r then (1 : ℝ) else 0) ≤ 2*r := by
  have hm : Measurable (fun s : CircleX ↦ if delta (repr s) < r then (1 : ℝ) else 0) :=
    Measurable.ite (measurableSet_lt (measurable_delta.comp measurable_repr) measurable_const)
      measurable_const measurable_const
  have hm' : Measurable (fun s : CircleX ↦ if r ≤ delta (repr s) then (1 : ℝ) else 0) :=
    Measurable.ite (measurableSet_le measurable_const (measurable_delta.comp measurable_repr))
      measurable_const measurable_const
  have hi' : Integrable (fun s : CircleX ↦ if r ≤ delta (repr s) then (1 : ℝ) else 0) := by
    apply Integrable.of_bound hm'.aestronglyMeasurable 1
    exact ae_of_all _ fun s ↦ by split_ifs <;> norm_num
  by_cases hr2 : r ≤ 1/2
  · have he := integral_uPos (ℓ := 1/2) (α := r) (by norm_num) (by norm_num) hr hr2
    simp_rw [uPos_integral_t (ℓ := 1/2) (α := r) (by norm_num) (by norm_num) hr] at he
    have hf : (fun s : CircleX ↦ if delta (repr s) < r then (1 : ℝ) else 0) =
        (fun s ↦ 1 - (if r ≤ delta (repr s) then (1 : ℝ) else 0)) := by
      funext s
      by_cases h : r ≤ delta (repr s) <;> simp [h, not_lt_of_ge, lt_of_not_ge]
    rw [hf, integral_sub (integrable_const 1) hi', he]
    simp only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul]
    linarith
  · have hi : Integrable (fun s : CircleX ↦ if delta (repr s) < r then (1 : ℝ) else 0) := by
      apply Integrable.of_bound hm.aestronglyMeasurable 1
      exact ae_of_all _ fun s ↦ by split_ifs <;> norm_num
    have hu := integral_mono hi (integrable_const (1 : ℝ)) (fun s ↦ by split_ifs <;> norm_num)
    simp only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul] at hu
    linarith



end CircleSampling

end

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_Discrepancy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CircleSampling

universe uX uY uΩ

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ComplexInnerProductSpace
open MeasureTheory Filter Set
open Set
open scoped ComplexInnerProductSpace
open Set
open scoped ComplexInnerProductSpace
open MeasureTheory Set Filter Topology
open scoped BigOperators ComplexConjugate

section
def negLower (α s : ℝ) : ℝ := max 0 (s-1+α)
def negUpper (ℓ α s : ℝ) : ℝ :=
  min 1 (min (s-α) (min (ℓ*s/(1+ℓ)) (ℓ*(1-s)/(1-ℓ))))

lemma neg_support_strict {ℓ α s t : ℝ} (hℓ : 0<ℓ) (hℓ1 : ℓ<1) :
    (0<t ∧ t<1 ∧ α<delta (s-t) ∧ t<ℓ*delta (s-t)) ↔
      t ∈ Ioo (negLower α s) (negUpper ℓ α s) := by
  have hp : 0<1+ℓ := by linarith
  have hm : 0<1-ℓ := by linarith
  simp only [negLower,negUpper,mem_Ioo,max_lt_iff,lt_min_iff,
    delta, mul_min_of_nonneg _ _ hℓ.le,lt_div_iff₀ hp,lt_div_iff₀ hm]
  constructor
  · rintro ⟨ht0,ht1,⟨hα1,hα2⟩,⟨ha,hb⟩⟩
    refine ⟨⟨ht0,by linarith⟩,ht1,by linarith,?_,?_⟩ <;> nlinarith
  · rintro ⟨⟨ht0,ha⟩,ht1,hb,hc,hd⟩
    refine ⟨ht0,ht1,⟨by linarith,by linarith⟩,?_,?_⟩ <;> nlinarith

def negArcLeft (ℓ α s r : ℝ) : Set ℝ :=
  Ioo (negLower α s) (min (negUpper ℓ α s) (min (s-1+1/(ℓ*r)) (s-1/2)))
def negArcRight (ℓ α s r : ℝ) : Set ℝ :=
  Ioo (max (negLower α s) (max (s-1/(ℓ*r)) (s-1/2))) (negUpper ℓ α s)

lemma negative_superlevel_intervals {ℓ α s t r : ℝ}
    (hℓ : 0<ℓ) (hℓ1 : ℓ<1) (hα : 0<α) (hr : 0<r)
    (ht : t∈Ico 0 1) (hne1 : t≠s-α) (hne2 : t≠s-1+α)
    (hne3 : t≠s-1/2) :
    r < weight ℓ α (s-t) t ↔ t∈negArcLeft ℓ α s r ∪ negArcRight ℓ α s r := by
  have hdc : α ≤ delta (s-t) ↔ α < delta (s-t) := by
    constructor
    · intro h
      obtain ⟨h1,h2⟩ := le_min_iff.mp h
      apply lt_min
      · exact lt_of_le_of_ne h1 (by intro he; apply hne1; linarith)
      · exact lt_of_le_of_ne h2 (by intro he; apply hne2; linarith)
    · exact le_of_lt
  have hrℓ : 0<ℓ*r := mul_pos hℓ hr
  have hinv {d : ℝ} (hd : 0<d) : r<1/(ℓ*d) ↔ d<1/(ℓ*r) := by
    rw [lt_div_iff₀ (mul_pos hℓ hd),lt_div_iff₀ hrℓ]
    constructor <;> intro h <;> nlinarith
  have hw : r<weight ℓ α (s-t) t ↔
      (0<t ∧ t<1 ∧ α<delta (s-t) ∧ t<ℓ*delta (s-t)) ∧
        delta (s-t)<1/(ℓ*r) := by
    unfold weight
    split_ifs with h
    · rw [hinv (lt_of_lt_of_le hα h.1)]
      simp only [h.2.1,ht.2,hdc.mp h.1,h.2.2,true_and]
    · constructor
      · exact fun h0 ↦ (not_lt_of_ge hr.le h0).elim
      · rintro ⟨⟨h0,_,ha,hb⟩,_⟩
        exact (h ⟨ha.le,h0,hb⟩).elim
  rw [hw,neg_support_strict hℓ hℓ1]
  simp only [negArcLeft,negArcRight,mem_union,mem_Ioo,max_lt_iff,lt_min_iff]
  obtain ht' | ht' : t<s-1/2 ∨ s-1/2<t := lt_or_gt_of_ne hne3
  · have he : delta (s-t)=1-(s-t) := by
      apply min_eq_right
      linarith
    rw [he]
    constructor
    · rintro ⟨⟨ha,hb⟩,hc⟩
      exact Or.inl ⟨ha,hb,by linarith,ht'⟩
    · rintro (⟨ha,hb,hc,_⟩ | ⟨⟨_,_,hc⟩,_⟩)
      · exact ⟨⟨ha,hb⟩,by linarith⟩
      · linarith
  · have he : delta (s-t)=s-t := by
      apply min_eq_left
      linarith
    rw [he]
    constructor
    · rintro ⟨⟨ha,hb⟩,hc⟩
      exact Or.inr ⟨⟨ha,by linarith,ht'⟩,hb⟩
    · rintro (⟨_,_,_,hc⟩ | ⟨⟨ha,hc,_⟩,hb⟩)
      · linarith
      · exact ⟨⟨ha,hb⟩,by linarith⟩

lemma negArcs_disjoint (ℓ α s r : ℝ) :
    Disjoint (negArcLeft ℓ α s r) (negArcRight ℓ α s r) := by
  apply disjoint_left.mpr
  intro t ht hu
  have ht' : t < s-1/2 := ht.2.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hu' : s-1/2 < t := ((le_max_right _ _).trans (le_max_right _ _)).trans_lt hu.1
  exact (lt_asymm ht' hu')

lemma preimage_repr_interval {a b : ℝ} (ha : 0≤a) (hb : b≤1) :
    repr ⁻¹' Ioo a b = ((↑) : ℝ → CircleX) '' Ioo a b := by
  ext x
  constructor
  · intro hx
    exact ⟨repr x,hx,coe_repr x⟩
  · rintro ⟨t,ht,rfl⟩
    change repr (t : CircleX) ∈ Ioo a b
    rw [repr_coe ⟨ha.trans ht.1.le,ht.2.trans_le hb⟩]
    exact ht

lemma repr_ne_ae (a : ℝ) : ∀ᵐ t : CircleX, repr t ≠ a := by
  have h : ∀ᵐ t : CircleX, t ≠ (a : CircleX) := by
    rw [ae_iff]
    simpa using volume_singleton_zero (a : CircleX)
  filter_upwards [h] with t ht he
  apply ht
  rw [← coe_repr t,he]

lemma uNeg_superlevel_ae {ℓ α r : ℝ} (hℓ : 0<ℓ) (hℓ1 : ℓ<1)
    (hα : 0<α) (hr : 0<r) (s : CircleX) :
    {t | r<uNeg ℓ α s t} =ᵐ[volume]
      repr ⁻¹' (negArcLeft ℓ α (repr s) r ∪ negArcRight ℓ α (repr s) r) := by
  filter_upwards [repr_ne_ae (repr s-α),repr_ne_ae (repr s-1+α),
    repr_ne_ae (repr s-1/2)] with t h1 h2 h3
  apply propext
  have hu := uNeg_unwrapped hℓ hℓ1 hα (repr_mem s) (repr_mem t)
  rw [coe_repr,coe_repr] at hu
  change (r<uNeg ℓ α s t) ↔ _
  rw [hu]
  exact negative_superlevel_intervals hℓ hℓ1 hα hr (repr_mem t) h1 h2 h3

lemma interval_image_ball (a b : ℝ) :
    ((↑) : ℝ → CircleX) '' Ioo a b = Metric.ball (((a+b)/2 : ℝ) : CircleX) ((b-a)/2) := by
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    rw [Metric.mem_ball, dist_eq_norm, ← AddCircle.coe_sub]
    apply lt_of_le_of_lt (QuotientAddGroup.norm_mk_le_norm)
    rw [Real.norm_eq_abs, abs_lt]
    constructor <;> linarith [ht.1, ht.2]
  · intro hx
    obtain ⟨t⟩ := x
    change (t : CircleX) ∈ Metric.ball (((a+b)/2 : ℝ) : CircleX) ((b-a)/2) at hx
    change (t : CircleX) ∈ ((↑) : ℝ → CircleX) '' Ioo a b
    rw [Metric.mem_ball, dist_eq_norm, ← AddCircle.coe_sub, AddCircle.norm_eq] at hx
    simp only [inv_one, one_mul, mul_one] at hx
    let u : ℝ := t - (round (t - (a+b)/2) : ℤ)
    refine ⟨u, ?_, ?_⟩
    · rw [mem_Ioo]
      have hu : |u - (a+b)/2| < (b-a)/2 := by
        convert! hx using 1
        congr 1
        dsimp [u]
        ring
      rw [abs_lt] at hu
      dsimp [u] at *
      constructor <;> linarith [hu.1, hu.2]
    · dsimp [u]
      have hz (z : ℤ) : ((z : ℝ) : CircleX) = 0 := by
        apply (AddCircle.coe_eq_zero_iff 1).mpr
        exact ⟨z, by simp⟩
      rw [hz, sub_zero]

def IsTwoArcs (A : Set CircleX) : Prop :=
  ∃ (c d : CircleX) (r q : ℝ),
    Disjoint (Metric.ball c r) (Metric.ball d q) ∧
    A =ᵐ[volume] (Metric.ball c r ∪ Metric.ball d q : Set CircleX)

lemma uNeg_isTwoArcs {ℓ α r : ℝ} (hℓ : 0<ℓ) (hℓ1 : ℓ<1)
    (hα : 0<α) (hr : 0<r) (s : CircleX) :
    IsTwoArcs {t | r<uNeg ℓ α s t} := by
  let a := negLower α (repr s)
  let b := min (negUpper ℓ α (repr s)) (min (repr s-1+1/(ℓ*r)) (repr s-1/2))
  let c := max (negLower α (repr s)) (max (repr s-1/(ℓ*r)) (repr s-1/2))
  let d := negUpper ℓ α (repr s)
  have hA : repr ⁻¹' negArcLeft ℓ α (repr s) r =
      Metric.ball (((a+b)/2 : ℝ) : CircleX) ((b-a)/2) := by
    change repr ⁻¹' Ioo a b = _
    rw [preimage_repr_interval (show 0≤a from le_max_left _ _)
      (show b≤1 from (min_le_left _ _).trans (min_le_left _ _)),interval_image_ball]
  have hB : repr ⁻¹' negArcRight ℓ α (repr s) r =
      Metric.ball (((c+d)/2 : ℝ) : CircleX) ((d-c)/2) := by
    change repr ⁻¹' Ioo c d = _
    rw [preimage_repr_interval (show 0≤c from (le_max_left _ _).trans (le_max_left _ _))
      (show d≤1 from min_le_left _ _),interval_image_ball]
  refine ⟨(((a+b)/2 : ℝ) : CircleX),(((c+d)/2 : ℝ) : CircleX),(b-a)/2,(d-c)/2,?_,?_⟩
  · rw [←hA,←hB]
    exact Disjoint.preimage repr (negArcs_disjoint ℓ α (repr s) r)
  · rw [←hA,←hB,←preimage_union]
    exact uNeg_superlevel_ae hℓ hℓ1 hα hr s

lemma uPos_isTwoArcs {ℓ α r : ℝ} (hℓ : 0<ℓ) (hℓ1 : ℓ<1)
    (_hα : 0<α) (hr : 0<r) (s : CircleX) :
    IsTwoArcs {t | r<uPos ℓ α s t} := by
  classical
  by_cases h : α≤delta (repr s) ∧ r<1/(ℓ*delta (repr s))
  · let b := ℓ*delta (repr s)
    have hb1 : b<1 := by
      have hd := delta_le_half (repr s)
      dsimp [b]
      nlinarith
    have he : {t | r<uPos ℓ α s t} = repr ⁻¹' Ioo 0 b := by
      ext t
      simp only [uPos,weight,mem_ofPred_eq,mem_preimage,mem_Ioo]
      split_ifs with ht
      · exact iff_of_true h.2 ht.2
      · constructor
        · exact fun hh ↦ (not_lt_of_ge hr.le hh).elim
        · exact fun hh ↦ (ht ⟨h.1,hh⟩).elim
    refine ⟨(((0+b)/2 : ℝ) : CircleX),0,(b-0)/2,0,?_,?_⟩
    · simp
    · rw [he,preimage_repr_interval le_rfl hb1.le,interval_image_ball]
      simp only [Metric.ball_zero,union_empty]
      exact Filter.EventuallyEq.rfl
  · have he : {t | r<uPos ℓ α s t} = ∅ := by
      ext t
      simp only [uPos,weight,mem_ofPred_eq,mem_empty_iff_false,iff_false]
      split_ifs with ht
      · exact fun hr' ↦ h ⟨ht.1,hr'⟩
      · exact not_lt_of_ge hr.le
    refine ⟨0,0,0,0,by simp,?_⟩
    simp only [he,Metric.ball_zero,union_empty]
    exact Filter.EventuallyEq.rfl


end



end CircleSampling

end

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_ProductSampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

universe uΩ uι uκ

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ComplexInnerProductSpace
open MeasureTheory Filter Set
open Set
open scoped ComplexInnerProductSpace
open Set
open scoped ComplexInnerProductSpace
open MeasureTheory Set Filter Topology
open scoped BigOperators ComplexConjugate

namespace CircleSampling
open ContinuousCircleWeight.Sampling

def orientedWeight (positive : Bool) (ℓ α : ℝ) (s t : CircleX) : ℝ :=
  if positive then uPos ℓ α s t else uNeg ℓ α s t

lemma measurable_orientedWeight (positive : Bool) (ℓ α : ℝ) :
    Measurable (Function.uncurry (orientedWeight positive ℓ α)) := by
  cases positive <;> first | exact measurable_uNeg ℓ α | exact measurable_uPos ℓ α

lemma orientedWeight_bounds (positive : Bool) {ℓ α : ℝ} (hℓ : 0<ℓ) (hα : 0<α)
    (s t : CircleX) : 0≤orientedWeight positive ℓ α s t ∧
      orientedWeight positive ℓ α s t≤1/(ℓ*α) := by
  cases positive <;> exact weight_bounds hℓ hα _ _

lemma orientedWeight_isTwoArcs (positive : Bool) {ℓ α r : ℝ} (hℓ : 0<ℓ)
    (hℓ1 : ℓ<1) (hα : 0<α) (s : CircleX) (hr : 0<r) :
    IsTwoArcs {t | r<orientedWeight positive ℓ α s t} := by
  cases positive
  · exact uNeg_isTwoArcs hℓ hℓ1 hα hr s
  · exact uPos_isTwoArcs hℓ hℓ1 hα hr s

lemma orientedWeight_mean (positive : Bool) {ℓ α : ℝ} (hℓ : 0<ℓ)
    (hℓ1 : ℓ<1) (hα : 0<α) (hα2 : α≤1/2) :
    (∫ s : CircleX, ∫ t : CircleX, orientedWeight positive ℓ α s t)=1-2*α := by
  cases positive
  · exact integral_uNeg hℓ hℓ1 hα hα2
  · exact integral_uPos hℓ hℓ1 hα hα2

lemma bounded_integrable {Ω : Type uΩ} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] {f : Ω → ℝ} (hf : Measurable f) {B : ℝ}
    (hb : ∀ x, 0≤f x ∧ f x≤B) : Integrable f μ := by
  apply Integrable.of_bound hf.aestronglyMeasurable B
  exact ae_of_all _ fun x ↦ by rw [Real.norm_eq_abs,abs_of_nonneg (hb x).1]; exact (hb x).2

lemma bounded_pair_integrable {Ω : Type uΩ} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] {f g : Ω → ℝ} (hf : Measurable f) (hg : Measurable g) {B : ℝ}
    (hB : 0≤B) (hfb : ∀ x, 0≤f x ∧ f x≤B) (hgb : ∀ x, 0≤g x ∧ g x≤B) :
    Integrable (fun x ↦ f x*g x) μ := by
  apply bounded_integrable μ (hf.mul hg)
  exact fun x ↦ ⟨mul_nonneg (hfb x).1 (hgb x).1,
    (mul_le_mul (hfb x).2 (hgb x).2 (hgb x).1 hB).trans_eq (pow_two B).symm⟩

lemma trial_mean_lower {a b c ℓ α A : ℝ} (hab : a<b) (hc : 0<c)
    (hℓ : 0<ℓ) (hℓ1 : ℓ<1) (hα : 0<α) (hα2 : α≤1/2)
    (positive : Bool) (hA : A≤1-1/(c*(b-a))) :
    A*(1-2*α) ≤ ∫ z : CircleX × ℝ,
      orientedWeight positive ℓ α z.1 ((c*z.2 : ℝ) : CircleX)
      ∂(volume.prod (intervalLaw a b)) := by
  let := intervalLaw_probability hab
  let u := orientedWeight positive ℓ α
  have hm : Measurable (Function.uncurry u) := measurable_orientedWeight positive ℓ α
  have hb := orientedWeight_bounds positive hℓ hα
  have htrial : Measurable (fun z : CircleX × ℝ ↦ u z.1 ((c*z.2 : ℝ) : CircleX)) :=
    hm.comp (measurable_fst.prodMk ((AddCircle.continuous_mk' 1).measurable.comp (measurable_const.mul measurable_snd)))
  have hit := bounded_integrable (volume.prod (intervalLaw a b)) htrial
    (fun z ↦ hb z.1 _)
  have hiu := bounded_integrable (volume.prod volume) hm (fun z ↦ hb z.1 z.2)
  rw [integral_prod _ hit]
  have hle (s : CircleX) : A*(∫ t : CircleX, u s t) ≤
      ∫ γ, u s ((c*γ : ℝ) : CircleX) ∂intervalLaw a b := by
    have hm' : Measurable (u s) := hm.comp (measurable_const.prodMk measurable_id)
    have hnon : 0≤∫ t : CircleX, u s t := integral_nonneg fun t ↦ (hb s t).1
    exact (mul_le_mul_of_nonneg_right hA hnon).trans
      (circle_scaled_integral_bounds (bounded_integrable volume hm' (hb s))
        (fun t ↦ (hb s t).1) hab hc).1
  have h := integral_mono (hiu.integral_prod_left.const_mul A) hit.integral_prod_left hle
  dsimp only [Function.uncurry,u] at h
  rw [integral_const_mul,orientedWeight_mean positive hℓ hℓ1 hα hα2] at h
  exact h

end CircleSampling

open MeasureTheory Set Filter
open scoped BigOperators ENNReal
namespace CircleSampling

section
variable {ι : Type uι} {κ : Type uκ} {Ω : Type uΩ} [Fintype ι] [Fintype κ] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]

def productAverage (u : κ → Ω → ℝ) (z : ι → Ω) : ℝ :=
  (Fintype.card κ : ℝ)⁻¹ * ∑ n, ∏ i, u n (z i)

lemma measurable_productTerm (u : Ω → ℝ) (hu : Measurable u) :
    Measurable (fun z : ι → Ω ↦ ∏ i, u (z i)) := by
  exact Finset.measurable_prod _ fun i _ ↦ hu.comp (measurable_pi_apply i)

lemma integrable_productTerm (u : Ω → ℝ) (hu : Measurable u) (B : ℝ)
    (hB : ∀ x, ‖u x‖≤B) :
    Integrable (fun z : ι → Ω ↦ ∏ i, u (z i)) (Measure.pi (fun _ : ι ↦ μ)) := by
  apply Integrable.of_bound (measurable_productTerm u hu).aestronglyMeasurable (B^(Fintype.card ι))
  apply ae_of_all
  intro z
  simpa only [norm_prod,Finset.prod_const,Finset.card_univ] using
    Finset.prod_le_prod (s := (Finset.univ : Finset ι)) (fun i _ ↦ norm_nonneg (u (z i))) (fun i _ ↦ hB (z i))

lemma integral_productAverage (u : κ → Ω → ℝ) (hu : ∀ n, Measurable (u n))
    (B : ℝ) (hB : ∀ n x, ‖u n x‖≤B) :
    ∫ z, productAverage (ι := ι) u z ∂Measure.pi (fun _ : ι ↦ μ) =
      (Fintype.card κ : ℝ)⁻¹ * ∑ n, (∫ x, u n x ∂μ)^(Fintype.card ι) := by
  unfold productAverage
  rw [integral_const_mul,integral_finsetSum]
  · simp_rw [integral_fintype_prod_eq_pow]
  · intro n _
    exact integrable_productTerm μ (u n) (hu n) B (hB n)

omit [MeasurableSpace Ω] in
lemma productAverage_sq (u : κ → Ω → ℝ) (z : ι → Ω) :
    (productAverage (ι := ι) u z)^2 =
      ((Fintype.card κ : ℝ)⁻¹)^2 * ∑ n, ∑ k, ∏ i, (u n (z i)*u k (z i)) := by
  unfold productAverage
  rw [mul_pow,pow_two (∑ n, ∏ i, u n (z i)),Finset.sum_mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro n _
  apply Finset.sum_congr rfl
  intro k _
  rw [← Finset.prod_mul_distrib]

lemma integral_productAverage_sq (u : κ → Ω → ℝ) (hu : ∀ n, Measurable (u n))
    (B : ℝ) (hB : ∀ n x, ‖u n x‖≤B) :
    ∫ z, (productAverage (ι := ι) u z)^2 ∂Measure.pi (fun _ : ι ↦ μ) =
      ((Fintype.card κ : ℝ)⁻¹)^2 *
        ∑ n, ∑ k, (∫ x, u n x*u k x ∂μ)^(Fintype.card ι) := by
  simp_rw [productAverage_sq]
  rw [integral_const_mul,integral_finsetSum]
  · congr 1
    apply Finset.sum_congr rfl
    intro n _
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro k _
      exact integral_fintype_prod_eq_pow (fun x ↦ u n x*u k x)
    · intro k _
      apply integrable_productTerm μ _ ((hu n).mul (hu k)) (B^2)
      intro x
      simp only [Pi.mul_apply,norm_mul,pow_two]
      exact mul_le_mul (hB n x) (hB k x) (norm_nonneg _) ((norm_nonneg _).trans (hB n x))
  · intro n _
    apply integrable_finsetSum
    intro k _
    apply integrable_productTerm μ _ ((hu n).mul (hu k)) (B^2)
    intro x
    simp only [Pi.mul_apply,norm_mul,pow_two]
    exact mul_le_mul (hB n x) (hB k x) (norm_nonneg _) ((norm_nonneg _).trans (hB n x))

lemma productAverage_integrable (u : κ → Ω → ℝ) (hu : ∀ n, Measurable (u n))
    (B : ℝ) (hB : ∀ n x, ‖u n x‖≤B) :
    Integrable (productAverage (ι := ι) u) (Measure.pi (fun _ : ι ↦ μ)) := by
  apply Integrable.const_mul
  exact integrable_finsetSum _ fun n _ ↦ integrable_productTerm μ (u n) (hu n) B (hB n)

lemma productAverage_sq_integrable (u : κ → Ω → ℝ) (hu : ∀ n, Measurable (u n))
    (B : ℝ) (hB : ∀ n x, ‖u n x‖≤B) :
    Integrable (fun z ↦ (productAverage (ι := ι) u z)^2) (Measure.pi (fun _ : ι ↦ μ)) := by
  simp_rw [productAverage_sq]
  apply Integrable.const_mul
  apply integrable_finsetSum
  intro n _
  apply integrable_finsetSum
  intro k _
  apply integrable_productTerm μ _ ((hu n).mul (hu k)) (B^2)
  intro x
  simp only [Pi.mul_apply,norm_mul,pow_two]
  exact mul_le_mul (hB n x) (hB k x) (norm_nonneg _) ((norm_nonneg _).trans (hB n x))

lemma productAverage_first_bound [Nonempty κ] (u : κ → Ω → ℝ) (hu : ∀ n, Measurable (u n))
    (B : ℝ) (hB : ∀ n x, ‖u n x‖≤B) (a : ℝ) (ha : 0≤a)
    (hmean : ∀ n, a≤∫ x, u n x ∂μ) :
    a^(Fintype.card ι) ≤ ∫ z, productAverage (ι := ι) u z ∂Measure.pi (fun _ : ι ↦ μ) := by
  rw [integral_productAverage μ u hu B hB]
  have hc : (Fintype.card κ : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hsum : ∑ _ : κ, a^(Fintype.card ι) ≤ ∑ n : κ, (∫ x, u n x ∂μ)^(Fintype.card ι) :=
    Finset.sum_le_sum fun n _ ↦ pow_le_pow_left₀ ha (hmean n) _
  have h := mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr (Nat.cast_nonneg (Fintype.card κ)))
  simpa [Finset.sum_const,Finset.card_univ, nsmul_eq_mul,← mul_assoc,hc] using h

lemma productAverage_second_bound [Nonempty κ] (u : κ → Ω → ℝ) (hu : ∀ n, Measurable (u n))
    (B : ℝ) (hB : ∀ n x, ‖u n x‖≤B) (b c : ℝ) (hb : 0≤b) (_hc : 0≤c)
    (hu0 : ∀ n x, 0≤u n x)
    (hpair : ∀ n k, n≠k → (∫ x, u n x*u k x ∂μ)≤b)
    (hdiag : ∀ n, (∫ x, (u n x)^2 ∂μ)≤c) :
    (∫ z, (productAverage (ι := ι) u z)^2 ∂Measure.pi (fun _ : ι ↦ μ)) ≤
      b^(Fintype.card ι) + (Fintype.card κ : ℝ)⁻¹*c^(Fintype.card ι) := by
  classical
  rw [integral_productAverage_sq μ u hu B hB]
  have hp : ∀ n k, (∫ x, u n x*u k x ∂μ)^(Fintype.card ι) ≤
      b^(Fintype.card ι) + if n=k then c^(Fintype.card ι) else 0 := by
    intro n k
    have hnon : 0≤∫ x, u n x*u k x ∂μ := integral_nonneg fun x ↦ mul_nonneg (hu0 n x) (hu0 k x)
    by_cases h : n=k
    · subst k
      simp only [ite_true]
      have hle := pow_le_pow_left₀ hnon (show (∫ x, u n x*u n x ∂μ)≤c by simpa [pow_two] using hdiag n) (Fintype.card ι)
      exact hle.trans (le_add_of_nonneg_left (pow_nonneg hb _))
    · simpa only [ite_eq_right h,add_zero] using pow_le_pow_left₀ hnon (hpair n k h) (Fintype.card ι)
  have hs : (∑ n : κ, ∑ k : κ, (∫ x, u n x*u k x ∂μ)^(Fintype.card ι)) ≤
      ∑ n : κ, ∑ k : κ, (b^(Fintype.card ι) + if n=k then c^(Fintype.card ι) else 0) :=
    Finset.sum_le_sum fun n _ ↦ Finset.sum_le_sum fun k _ ↦ hp n k
  have h := mul_le_mul_of_nonneg_left hs (sq_nonneg (Fintype.card κ : ℝ)⁻¹)
  have hcard : (Fintype.card κ : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  apply h.trans_eq
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
    Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  field_simp [hcard]

lemma productAverage_error_bound [Nonempty κ] (u : κ → Ω → ℝ) (hu : ∀ n, Measurable (u n))
    (B : ℝ) (hB : ∀ n x, ‖u n x‖≤B) (a b c : ℝ) (ha : 0≤a) (hb : 0≤b) (hc : 0≤c)
    (hu0 : ∀ n x, 0≤u n x)
    (hmean : ∀ n, a≤∫ x, u n x ∂μ)
    (hpair : ∀ n k, n≠k → (∫ x, u n x*u k x ∂μ)≤b)
    (hdiag : ∀ n, (∫ x, (u n x)^2 ∂μ)≤c) :
    (∫ z, (productAverage (ι := ι) u z-1)^2 ∂Measure.pi (fun _ : ι ↦ μ)) ≤
      b^(Fintype.card ι)+(Fintype.card κ : ℝ)⁻¹*c^(Fintype.card ι)-2*a^(Fintype.card ι)+1 := by
  have h1 := productAverage_first_bound (ι := ι) μ u hu B hB a ha hmean
  have h2 := productAverage_second_bound (ι := ι) μ u hu B hB b c hb hc hu0 hpair hdiag
  have hi := productAverage_integrable (ι := ι) μ u hu B hB
  have hi2 := productAverage_sq_integrable (ι := ι) μ u hu B hB
  have he : (fun z : ι → Ω ↦ (productAverage u z-1)^2) =
      (fun z ↦ ((productAverage u z)^2-2*productAverage u z)+1) := by funext z; ring
  rw [he]
  have hsub : Integrable (fun z : ι → Ω ↦ (productAverage u z)^2-2*productAverage u z) (Measure.pi (fun _ : ι ↦ μ)) := hi2.sub (hi.const_mul 2)
  rw [integral_add hsub (integrable_const 1)]
  have hmul : Integrable (fun z : ι → Ω ↦ 2*productAverage u z) (Measure.pi (fun _ : ι ↦ μ)) := hi.const_mul 2
  rw [integral_sub hi2 hmul,integral_const_mul]
  simp only [integral_const,Measure.real,measure_univ,ENNReal.toReal_one,smul_eq_mul,one_mul]
  linarith
end
open ContinuousCircleWeight.Sampling
variable {ι : Type uι} {κ : Type uκ} [Fintype ι] [Fintype κ] [Nonempty κ]

def idealAverage (positive : Bool) (ℓ α : ℝ) (c : κ → ℝ) (s : ι → CircleX) (γ : ι → ℝ) : ℝ :=
  (Fintype.card κ : ℝ)⁻¹ * ∑ n, ∏ i, orientedWeight positive ℓ α (s i) ((c n*γ i : ℝ) : CircleX)

end CircleSampling

end

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_SamplingBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CircleSampling

universe uκ uι

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ComplexInnerProductSpace
open MeasureTheory Filter Set
open Set
open scoped ComplexInnerProductSpace
open Set
open scoped ComplexInnerProductSpace
open MeasureTheory Set Filter Topology
open scoped BigOperators ComplexConjugate
open MeasureTheory Set Filter
open scoped BigOperators ENNReal
open Filter Set
open scoped Topology
section

def scaleEll (m : ℕ) : ℝ := (m:ℝ)^(-(3:ℝ)/5)
def scaleAlpha (m : ℕ) : ℝ := (m:ℝ)^(-(2:ℝ))
def scaleDiscrepancy (m : ℕ) : ℝ := 18*(m:ℝ)^(-(70:ℝ))
def offError (m : ℕ) : ℝ := (2*scaleEll m/(1-scaleEll m))^2 +
  2*(1+scaleEll m)*scaleAlpha m + 4*(1/(scaleEll m*scaleAlpha m))^2*scaleDiscrepancy m

def samplingError (m : ℕ) : ℝ := (1+offError m)^m+(1/2:ℝ)^m -
  2*(1-3*scaleAlpha m)^m+1

lemma rpow_scale_mul (x : ℝ) (hx : 0 < x) (a b : ℝ) : x^a*x^b=x^(a+b) :=
  (Real.rpow_add hx _ _).symm
lemma rpow_scale_sq (x : ℝ) (hx : 0≤x) (a : ℝ) : (x^a)^2=x^(a*2) := by
  rw [← Real.rpow_natCast,← Real.rpow_mul hx]; norm_num
lemma scale_product {m : ℕ} (hm : 0 < m) : scaleEll m*scaleAlpha m=(m:ℝ)^(-(13:ℝ)/5) := by
  have hx : (0:ℝ) < m := by exact_mod_cast hm
  rw [scaleEll,scaleAlpha,rpow_scale_mul _ hx]; norm_num
lemma mass_offError {m : ℕ} (hm : 0 < m) :
    (m:ℝ)*offError m =
      4*(m:ℝ)^(-(1:ℝ)/5)/(1-scaleEll m)^2 +
      2*(1+scaleEll m)*(m:ℝ)^(-(1:ℝ)) + 72*(m:ℝ)^(-(319:ℝ)/5) := by
  have hx : (0:ℝ) < m := by exact_mod_cast hm
  have h₁ : (m:ℝ)*(scaleEll m)^2=(m:ℝ)^(-(1:ℝ)/5) := by
    rw [scaleEll,rpow_scale_sq _ hx.le]
    conv_lhs => arg 1; rw [← Real.rpow_one (m:ℝ)]
    rw [rpow_scale_mul _ hx]; norm_num
  have h₂ : (m:ℝ)*scaleAlpha m=(m:ℝ)^(-(1:ℝ)) := by
    rw [scaleAlpha]
    conv_lhs => arg 1; rw [← Real.rpow_one (m:ℝ)]
    rw [rpow_scale_mul _ hx]; norm_num
  have h₃ : (m:ℝ)*(1/(scaleEll m*scaleAlpha m))^2*(m:ℝ)^(-(70:ℝ)) =
      (m:ℝ)^(-(319:ℝ)/5) := by
    rw [scale_product hm,one_div,← Real.rpow_neg hx.le,rpow_scale_sq _ hx.le]
    conv_lhs => arg 1; arg 1; rw [← Real.rpow_one (m:ℝ)]
    rw [rpow_scale_mul _ hx,rpow_scale_mul _ hx]; norm_num
  calc
    (m:ℝ)*offError m = 4*((m:ℝ)*(scaleEll m)^2)/(1-scaleEll m)^2 +
        2*(1+scaleEll m)*((m:ℝ)*scaleAlpha m) +
        72*((m:ℝ)*(1/(scaleEll m*scaleAlpha m))^2*(m:ℝ)^(-(70:ℝ))) := by
      unfold offError scaleDiscrepancy
      simp only [div_pow]
      ring
    _ = _ := by rw [h₁,h₂,h₃]

lemma tendsto_nat_rpow_neg {a : ℝ} (ha : 0 < a) :
    Tendsto (fun m : ℕ => (m:ℝ)^(-a)) atTop (𝓝 0) :=
  (tendsto_rpow_neg_atTop ha).comp tendsto_natCast_atTop_atTop
lemma tendsto_scaleEll : Tendsto scaleEll atTop (𝓝 0) := by
  change Tendsto (fun m : ℕ => (m:ℝ)^(-(3:ℝ)/5)) atTop (𝓝 0)
  simpa only [neg_div] using tendsto_nat_rpow_neg (a:=3/5) (by norm_num)
lemma tendsto_scaleAlpha : Tendsto scaleAlpha atTop (𝓝 0) :=
  tendsto_nat_rpow_neg (by norm_num : (0:ℝ)<2)
lemma tendsto_mass_offError : Tendsto (fun m : ℕ => (m:ℝ)*offError m) atTop (𝓝 0) := by
  have ha := tendsto_nat_rpow_neg (by norm_num : (0:ℝ)<1/5)
  have hb := tendsto_nat_rpow_neg (by norm_num : (0:ℝ)<1)
  have hc := tendsto_nat_rpow_neg (by norm_num : (0:ℝ)<319/5)
  have h₁ : Tendsto (fun m : ℕ => 4*(m:ℝ)^(-(1:ℝ)/5)/(1-scaleEll m)^2) atTop (𝓝 0) := by
    convert (ha.const_mul (4:ℝ)).div ((tendsto_const_nhds.sub tendsto_scaleEll).pow 2)
        (by norm_num : (1-(0:ℝ))^2 ≠ 0) using 1
    · ext m; simp only [Pi.div_apply, neg_div]
    · norm_num
  have h₂ : Tendsto (fun m : ℕ => 2*(1+scaleEll m)*(m:ℝ)^(-(1:ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero] using ((tendsto_const_nhds.add tendsto_scaleEll).const_mul 2).mul hb
  have h₃ : Tendsto (fun m : ℕ => 72*(m:ℝ)^(-(319:ℝ)/5)) atTop (𝓝 0) := by
    simpa only [neg_div,mul_zero] using hc.const_mul 72
  have h := (h₁.add h₂).add h₃
  simp only [zero_add] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0:ℕ)] with m hm
  simpa only [neg_div] using (mass_offError hm).symm
lemma tendsto_mass_alpha : Tendsto (fun m : ℕ => (m:ℝ)*scaleAlpha m) atTop (𝓝 0) := by
  apply (tendsto_nat_rpow_neg (by norm_num : (0:ℝ)<1)).congr'
  filter_upwards [eventually_gt_atTop (0:ℕ)] with m hm
  have hx : (0:ℝ) < m := by exact_mod_cast hm
  rw [scaleAlpha]
  conv_rhs => arg 1; rw [← Real.rpow_one (m:ℝ)]
  rw [rpow_scale_mul _ hx]; norm_num
lemma tendsto_samplingError : Tendsto samplingError atTop (𝓝 0) := by
  have ho := Real.tendsto_one_add_pow_exp_of_tendsto tendsto_mass_offError
  have ha : Tendsto (fun m : ℕ => (m:ℝ)*(-3*scaleAlpha m)) atTop (𝓝 0) := by
    simpa only [mul_assoc,mul_comm,mul_left_comm,mul_zero,zero_mul] using tendsto_mass_alpha.const_mul (-3)
  have hl := Real.tendsto_one_add_pow_exp_of_tendsto ha
  have hd := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤1/2)
    (by norm_num : (1/2:ℝ)<1)
  have hh := ((ho.add hd).sub (hl.const_mul 2)).add_const 1
  change Tendsto (fun m => (1+offError m)^m+(1/2:ℝ)^m - 2*(1-3*scaleAlpha m)^m+1) atTop (𝓝 0)
  convert hh using 1
  · ext m; congr 3; ring
  · norm_num
end
open Filter Set
open scoped Topology
section
lemma eventually_rpow_linear_gap (a b C d : ℝ) (hab : b<a) :
    ∀ᶠ m : ℕ in atTop, C*(m:ℝ)^d*(m:ℝ)^(b*(m:ℝ)) ≤ (m:ℝ)^(a*(m:ℝ)) := by
  have hm : Tendsto (fun m : ℕ => (m:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have he : Tendsto (fun m : ℕ => (a-b)*(m:ℝ)) atTop atTop :=
    hm.const_mul_atTop (sub_pos.mpr hab)
  filter_upwards [hm.eventually_ge_atTop (max 1 C),he.eventually_ge_atTop (d+1)] with m hmin hd
  have hm1 : 1 ≤ (m:ℝ) := (le_max_left _ _).trans hmin
  have hm0 : 0 < (m:ℝ) := lt_of_lt_of_le zero_lt_one hm1
  have hc : C ≤ (m:ℝ) := (le_max_right _ _).trans hmin
  have hpos : 0 ≤ (m:ℝ)^d*(m:ℝ)^(b*(m:ℝ)) := by positivity
  calc
    C*(m:ℝ)^d*(m:ℝ)^(b*(m:ℝ)) ≤ (m:ℝ)*(m:ℝ)^d*(m:ℝ)^(b*(m:ℝ)) := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (by positivity)) (by positivity)
    _ = (m:ℝ)^(1+d+b*(m:ℝ)) := by rw [Real.rpow_add hm0,Real.rpow_add hm0,Real.rpow_one]
    _ ≤ (m:ℝ)^(a*(m:ℝ)) := Real.rpow_le_rpow_of_exponent_le hm1 (by nlinarith)
open Filter Set
open scoped Topology
lemma inv_scaleEll {m : ℕ} (hm : 0 < m) : (scaleEll m)⁻¹ = (m:ℝ)^((3:ℝ)/5) := by
  have hx : (0:ℝ) < m := by exact_mod_cast hm
  rw [scaleEll, ← Real.rpow_neg hx.le]
  congr 1
  ring
lemma inv_scaleAlpha {m : ℕ} (hm : 0 < m) : (scaleAlpha m)⁻¹ = (m:ℝ)^2 := by
  have hx : (0:ℝ) < m := by exact_mod_cast hm
  rw [scaleAlpha, ← Real.rpow_neg hx.le, neg_neg, Real.rpow_ofNat]
lemma scaleAlpha_pos {m : ℕ} (hm : 0 < m) : 0 < scaleAlpha m := by
  unfold scaleAlpha
  positivity
lemma diagonal_estimate {m : ℕ} (hm : 2 ≤ m) :
    2*((2/scaleEll m)*Real.log (1/(2*scaleAlpha m))) ≤
      8*(m:ℝ)^((3:ℝ)/5)*Real.log m := by
  have hm0 : 0 < m := by omega
  have hx : (0:ℝ) < m := by exact_mod_cast hm0
  have ha := scaleAlpha_pos hm0
  have ht : 0 < 1/(2*scaleAlpha m) := by positivity
  have harg : 1/(2*scaleAlpha m) ≤ (m:ℝ)^2 := by
    rw [one_div,mul_inv_rev, inv_scaleAlpha hm0]
    nlinarith [sq_nonneg (m:ℝ)]
  have hl := Real.log_le_log ht harg
  rw [Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  rw [div_eq_mul_inv,inv_scaleEll hm0]
  calc
    2*(2*(m:ℝ)^((3:ℝ)/5)*Real.log (1/(2*scaleAlpha m))) ≤
      2*(2*(m:ℝ)^((3:ℝ)/5)*(2*Real.log m)) := by gcongr
    _ = _ := by ring
lemma eventually_diagonal_small : ∀ᶠ m : ℕ in atTop,
    2*((2/scaleEll m)*Real.log (1/(2*scaleAlpha m))) ≤
      (1/2)*(m:ℝ)^((69:ℝ)/100) := by
  have hlim : Tendsto (fun m : ℕ => Real.log (m:ℝ)/(m:ℝ)^((9:ℝ)/100)) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop (by norm_num : (0:ℝ) < 9/100)).tendsto_div_nhds_zero.comp
      tendsto_natCast_atTop_atTop
  filter_upwards [hlim.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1/16)),
    eventually_ge_atTop (2:ℕ)] with m hratio hm
  have hm0 : 0 < m := by omega
  have hx : (0:ℝ) < m := by exact_mod_cast hm0
  have hp : 0 < (m:ℝ)^((9:ℝ)/100) := Real.rpow_pos_of_pos hx _
  have hlog := (div_lt_iff₀ hp).mp hratio
  apply (diagonal_estimate hm).trans
  calc
    8*(m:ℝ)^((3:ℝ)/5)*Real.log m ≤
      8*(m:ℝ)^((3:ℝ)/5)*((1/16)*(m:ℝ)^((9:ℝ)/100)) := by gcongr
    _ = (1/2)*((m:ℝ)^((3:ℝ)/5)*(m:ℝ)^((9:ℝ)/100)) := by ring
    _ = _ := by rw [rpow_scale_mul _ hx]; norm_num
end
section
open Filter Set
open scoped Topology
lemma eventually_sampling_marginal (K : ℕ) : ∀ᶠ m : ℕ in atTop,
    ∀ c : ℝ, (m:ℝ)^((7:ℝ)/10*m)/2 ≤ c →
      0 < c ∧ 1/(c*(2/((m:ℝ)*K)-1/((m:ℝ)*K))) ≤ scaleAlpha m := by
  by_cases hK : K = 0
  · subst K
    filter_upwards [eventually_ge_atTop (1:ℕ)] with m hm c hc
    have hx : (0:ℝ) < m := Nat.cast_pos.mpr (by omega)
    refine ⟨(by positivity : 0 < (m:ℝ)^((7:ℝ)/10*m)/2).trans_le hc,?_⟩
    simpa using (scaleAlpha_pos (by omega : 0 < m)).le
  have hKpos : (0:ℝ) < K := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hK)
  have hg := eventually_rpow_linear_gap (7/10) 0 (2*K) 3 (by norm_num)
  filter_upwards [hg,eventually_ge_atTop (1:ℕ)] with m hg hm c hc
  have hm0 : 0 < m := by omega
  have hx : (0:ℝ) < m := Nat.cast_pos.mpr hm0
  have ha := scaleAlpha_pos hm0
  have hQ : 0 < (m:ℝ)^((7:ℝ)/10*m)/2 := by positivity
  have hcpos := hQ.trans_le hc
  refine ⟨hcpos,?_⟩
  have hg' : 2*(K:ℝ)*(m:ℝ)^3 ≤ (m:ℝ)^((7:ℝ)/10*m) := by
    simpa only [zero_mul,Real.rpow_zero,mul_one,Real.rpow_ofNat] using hg
  have hwidth : 2/((m:ℝ)*K)-1/((m:ℝ)*K) = 1/((m:ℝ)*K) := by ring
  rw [hwidth]
  apply (div_le_iff₀ (by positivity : 0 < c*(1/((m:ℝ)*K)))).mpr
  have hinv := inv_scaleAlpha hm0
  have hmul : scaleAlpha m*(m:ℝ)^2 = 1 := by rw [← hinv]; exact mul_inv_cancel₀ ha.ne'
  have hlarge : (m:ℝ)*K ≤ scaleAlpha m*c := by
    have hh := mul_le_mul_of_nonneg_left hg' ha.le
    have hhh := mul_le_mul_of_nonneg_left hc ha.le
    have hid : scaleAlpha m*(2*(K:ℝ)*(m:ℝ)^3) = 2*((m:ℝ)*K) := by
      calc
        _ = 2*((m:ℝ)*K)*(scaleAlpha m*(m:ℝ)^2) := by ring
        _ = _ := by rw [hmul,mul_one]
    rw [hid] at hh
    nlinarith
  have hh : (1:ℝ) ≤ (scaleAlpha m*c)/((m:ℝ)*K) := (le_div_iff₀ (mul_pos hx hKpos)).mpr (by simpa only [one_mul] using hlarge)
  simpa only [div_eq_mul_inv, mul_assoc, one_mul] using hh
end
section
open ContinuousCircleWeight.Sampling
open Filter Set MeasureTheory
open scoped Topology

def IdealNumerics (K m : ℕ) : Prop :=
  2 ≤ m ∧ scaleEll m < 1 ∧ scaleAlpha m ≤ 1/3 ∧
  2*((2/scaleEll m)*Real.log (1/(2*scaleAlpha m))) ≤ (1/2)*(m:ℝ)^((69:ℝ)/100) ∧
  ∀ c : ℝ, (m:ℝ)^((7:ℝ)/10*m)/2 ≤ c →
    0 < c ∧ 1/(c*(2/((m:ℝ)*K)-1/((m:ℝ)*K))) ≤ scaleAlpha m

lemma eventually_IdealNumerics (K : ℕ) : ∀ᶠ m : ℕ in atTop, IdealNumerics K m := by
  filter_upwards [eventually_ge_atTop (2:ℕ),
    tendsto_scaleEll.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1)),
    tendsto_scaleAlpha.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1/3)),
    eventually_diagonal_small,eventually_sampling_marginal K] with m hm hℓ hα hd hmean
  exact ⟨hm,hℓ,hα.le,hd,hmean⟩

end
section
open ContinuousCircleWeight.Sampling
variable {ι : Type uι} {κ : Type uκ} [Fintype ι] [Fintype κ] [Nonempty κ]
omit [Nonempty κ] in
lemma measurable_idealAverage (positive : Bool) (ℓ α : ℝ) (c : κ → ℝ) :
    Measurable (fun z : (ι → CircleX) × (ι → ℝ) => idealAverage positive ℓ α c z.1 z.2) := by
  unfold idealAverage
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro n _
  apply Finset.measurable_prod
  intro i _
  have hm : Measurable (fun z : (ι → CircleX) × (ι → ℝ) =>
      (z.1 i, ((c n*z.2 i:ℝ):CircleX))) := by fun_prop
  exact (measurable_orientedWeight positive ℓ α).comp hm

lemma idealAverage_bounds (positive : Bool) {ℓ α : ℝ} (hℓ : 0 < ℓ) (hα : 0 < α)
    (c : κ → ℝ) (s : ι → CircleX) (γ : ι → ℝ) :
    0 ≤ idealAverage positive ℓ α c s γ ∧
    idealAverage positive ℓ α c s γ ≤ (1/(ℓ*α))^(Fintype.card ι) := by
  have hw i n := orientedWeight_bounds positive hℓ hα (s i) ((c n*γ i:ℝ):CircleX)
  have hcp : (0:ℝ) < Fintype.card κ := Nat.cast_pos.mpr Fintype.card_pos
  unfold idealAverage
  constructor
  · exact mul_nonneg (inv_nonneg.mpr hcp.le) (Finset.sum_nonneg fun n _ => Finset.prod_nonneg fun i _ => (hw i n).1)
  · calc
      _ ≤ (Fintype.card κ:ℝ)⁻¹ * ∑ _n : κ, (1/(ℓ*α))^(Fintype.card ι) := by
        gcongr
        calc
          _ ≤ ∏ _i : ι, (1/(ℓ*α)) := Finset.prod_le_prod (fun i _ => (hw i _).1) (fun i _ => (hw i _).2)
          _ = _ := by simp
      _ = _ := by simp [nsmul_eq_mul,hcp.ne']

def idealEnergy (positive : Bool) (ℓ α : ℝ) (c : κ → ℝ) (γ : ι → ℝ) : ℝ :=
  ∫ s : ι → CircleX, (idealAverage positive ℓ α c s γ-1)^2 ∂Measure.pi (fun _ => volume)

omit [Nonempty κ] in
lemma idealEnergy_nonneg (positive : Bool) (ℓ α : ℝ) (c : κ → ℝ) (γ : ι → ℝ) :
    0 ≤ idealEnergy positive ℓ α c γ := integral_nonneg fun _ => sq_nonneg _

omit [Nonempty κ] in
lemma measurable_idealEnergy (positive : Bool) (ℓ α : ℝ) (c : κ → ℝ) :
    Measurable (idealEnergy (ι:=ι) positive ℓ α c) := by
  unfold idealEnergy
  exact ((((measurable_idealAverage positive ℓ α c).comp measurable_swap).sub measurable_const).pow_const 2).stronglyMeasurable.integral_prod_right.measurable

lemma idealEnergy_le (positive : Bool) {ℓ α : ℝ} (hℓ : 0 < ℓ) (hα : 0 < α)
    (c : κ → ℝ) (γ : ι → ℝ) :
    idealEnergy (ι:=ι) positive ℓ α c γ ≤ ((1/(ℓ*α))^(Fintype.card ι)+1)^2 := by
  have hb (s : ι → CircleX) : (idealAverage positive ℓ α c s γ-1)^2 ≤
      ((1/(ℓ*α))^(Fintype.card ι)+1)^2 := by
    have h := idealAverage_bounds positive hℓ hα c s γ
    rw [← sq_abs (idealAverage positive ℓ α c s γ-1)]
    apply (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr
    rw [abs_le]
    constructor <;> linarith [pow_nonneg (by positivity : 0 ≤ 1/(ℓ*α)) (Fintype.card ι)]
  have h := integral_mono_of_nonneg (Filter.Eventually.of_forall fun s => sq_nonneg (idealAverage positive ℓ α c s γ-1))
    (integrable_const (μ:=Measure.pi (fun _ : ι => (volume : Measure CircleX))) (((1/(ℓ*α))^(Fintype.card ι)+1)^2)) (Filter.Eventually.of_forall hb)
  simpa [idealEnergy] using h

lemma idealEnergy_integrable (positive : Bool) {ℓ α : ℝ} (hℓ : 0 < ℓ) (hα : 0 < α)
    (c : κ → ℝ) (μ : Measure (ι → ℝ)) [IsFiniteMeasure μ] :
    Integrable (idealEnergy (ι:=ι) positive ℓ α c) μ := by
  apply Integrable.of_bound (measurable_idealEnergy positive ℓ α c).aestronglyMeasurable
    (((1/(ℓ*α))^(Fintype.card ι)+1)^2)
  filter_upwards [] with γ
  rw [Real.norm_eq_abs,abs_of_nonneg (idealEnergy_nonneg positive ℓ α c γ)]
  exact idealEnergy_le positive hℓ hα c γ
end
open ContinuousCircleWeight.Sampling
open Set MeasureTheory

def phaseFailure (b : ℝ) (c : ℝ) : Set ℝ :=
  {γ | ¬ (b < 1-repr ((c*γ:ℝ):CircleX) ∧ 1-repr ((c*γ:ℝ):CircleX) < 1-b)}


end CircleSampling

end

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_TrialBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CircleSampling

universe uι uX uκ uτ

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ComplexInnerProductSpace
open MeasureTheory Filter Set
open Set
open scoped ComplexInnerProductSpace
open Set
open scoped ComplexInnerProductSpace
open MeasureTheory Set Filter Topology
open scoped BigOperators ComplexConjugate
open MeasureTheory Set Filter
open scoped BigOperators ENNReal
open Filter Set
open scoped Topology
open Filter Set
open scoped Topology

open Set MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter Set
open scoped Topology
section

def phaseUnionBound (m : ℕ) : ℝ :=
  3*(2*(10:ℝ)^((9:ℝ)/10)*(m:ℝ)^(-(11:ℝ)/200))^m

lemma tendsto_phaseUnionBound : Tendsto phaseUnionBound atTop (𝓝 0) := by
  have hx : Tendsto (fun m : ℕ => (m:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hb : Tendsto (fun m : ℕ => 2*(10:ℝ)^((9:ℝ)/10)*(m:ℝ)^(-(11:ℝ)/200)) atTop (𝓝 0) := by
    simpa only [mul_zero, neg_div, Function.comp_apply] using (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 11/200)).comp hx |>.const_mul (2*(10:ℝ)^((9:ℝ)/10))
  apply squeeze_zero' (Eventually.of_forall (fun m => by unfold phaseUnionBound; positivity))
    (g := fun m => 3*(1/2:ℝ)^m)
  · filter_upwards [hb.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1/2))] with m hm
    unfold phaseUnionBound
    gcongr
  · simpa only [mul_zero] using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
      (by norm_num : (1/2:ℝ) < 1)).const_mul 3

lemma eventually_phase_failure_small : ∀ᶠ m : ℕ in atTop, 10*(m:ℝ)^(-(19:ℝ)/20) ≤ 1 := by
  have hx : Tendsto (fun m : ℕ => (m:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hb : Tendsto (fun m : ℕ => 10*(m:ℝ)^(-(19:ℝ)/20)) atTop (𝓝 0) := by
    simpa only [mul_zero, neg_div, Function.comp_apply] using (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 19/20)).comp hx |>.const_mul 10
  filter_upwards [hb.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1))] with m hm
  exact hm.le
open ContinuousCircleWeight.Sampling
open scoped Classical ENNReal

end
open Set MeasureTheory
open scoped ENNReal Classical
section
lemma finite_threshold_bound {X : Type uX} {τ : Type uτ} [MeasurableSpace X] [Fintype τ]
    (μ : Measure X) [IsProbabilityMeasure μ] (E : τ → X → ℝ)
    (hE0 : ∀ t x, 0 ≤ E t x) (hEi : ∀ t, Integrable (E t) μ)
    {ε δ : ℝ} (hδ : 0 < δ) (hE : ∀ t, ∫ x, E t x ∂μ ≤ ε) :
    μ {x | ∃ t, δ ≤ E t x} ≤ ENNReal.ofReal ((Fintype.card τ:ℝ)*(ε/δ)) := by
  have hb (t : τ) : μ {x | δ ≤ E t x} ≤ ENNReal.ofReal (ε/δ) := by
    have h := (mul_meas_ge_le_integral_of_nonneg (Filter.Eventually.of_forall (hE0 t)) (hEi t) δ).trans (hE t)
    have h' : μ.real {x | δ ≤ E t x} ≤ ε/δ := (le_div_iff₀ hδ).mpr (by simpa only [mul_comm] using h)
    rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
    exact ENNReal.ofReal_le_ofReal h'
  calc
    _ = μ (⋃ t, {x | δ ≤ E t x}) := by congr 1; ext x; simp
    _ ≤ ∑ t, μ {x | δ ≤ E t x} := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _t : τ, ENNReal.ofReal (ε/δ) := Finset.sum_le_sum (fun t _ => hb t)
    _ = _ := by simp [ENNReal.ofReal_mul (Nat.cast_nonneg _),nsmul_eq_mul]

lemma exists_good_finite_family {X : Type uX} {τ : Type uτ} [MeasurableSpace X] [Fintype τ]
    (μ : Measure X) [IsProbabilityMeasure μ] (E : τ → X → ℝ)
    (hE0 : ∀ t x, 0 ≤ E t x) (hEi : ∀ t, Integrable (E t) μ)
    {ε δ B : ℝ} (hδ : 0 < δ) (hB : 0 ≤ B)
    (hE : ∀ t, ∫ x, E t x ∂μ ≤ ε) (bad : Set X) (hbad : μ bad ≤ ENNReal.ofReal B)
    (hbudget : B+(Fintype.card τ:ℝ)*(ε/δ) < 1) {P : X → Prop} (hP : ∀ᵐ x ∂μ, P x) :
    ∃ x, P x ∧ x ∉ bad ∧ ∀ t, E t x < δ := by
  have hε : 0 ≤ (Fintype.card τ:ℝ)*(ε/δ) := by
    by_cases hn : Nonempty τ
    · let := hn
      have heps := (integral_nonneg (hE0 (Classical.choice hn))).trans (hE (Classical.choice hn))
      positivity
    · have : IsEmpty τ := not_nonempty_iff.mp hn
      simp
  have hu := finite_threshold_bound μ E hE0 hEi hδ hE
  have hsmall : μ (bad ∪ {x | ∃ t, δ ≤ E t x} ∪ {x | ¬P x}) < 1 := by
    calc
      _ ≤ μ bad + μ {x | ∃ t, δ ≤ E t x} + μ {x | ¬P x} :=
        (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
      _ ≤ ENNReal.ofReal B + ENNReal.ofReal ((Fintype.card τ:ℝ)*(ε/δ)) + 0 :=
        add_le_add (add_le_add hbad hu) (le_of_eq (ae_iff.mp hP))
      _ < 1 := by
        rw [add_zero,← ENNReal.ofReal_add hB hε]
        exact (ENNReal.ofReal_lt_one).mpr hbudget
  by_contra! h
  have heq : bad ∪ {x | ∃ t, δ ≤ E t x} ∪ {x | ¬P x} = Set.univ := by
    ext x
    simp only [mem_union,mem_ofPred_eq,mem_univ,iff_true]
    by_cases hp : P x
    · by_cases hb : x∈bad
      · exact Or.inl (Or.inl hb)
      · exact Or.inl (Or.inr (h x hp hb))
    · exact Or.inr hp
  rw [heq,measure_univ] at hsmall
  exact (lt_irrefl _) hsmall
end
open ContinuousCircleWeight.Sampling Filter
open scoped Topology
lemma eventually_trial_budget (T : ℕ) {δ : ℝ} (_hδ : 0 < δ) :
    ∀ᶠ m : ℕ in atTop, phaseUnionBound m+(T:ℝ)*(samplingError m/δ) < 1 := by
  have h := tendsto_phaseUnionBound.add ((tendsto_samplingError.div_const δ).const_mul (T:ℝ))
  norm_num only [zero_div,mul_zero,add_zero] at h
  exact h.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1))


end CircleSampling

end

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_FiniteSampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CircleSampling

universe uι uκ uP uτ

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ComplexInnerProductSpace
open MeasureTheory Filter Set
open Set
open scoped ComplexInnerProductSpace
open Set
open scoped ComplexInnerProductSpace
open MeasureTheory Set Filter Topology
open scoped BigOperators ComplexConjugate
open MeasureTheory Set Filter
open scoped BigOperators ENNReal
open Filter Set
open scoped Topology
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped ENNReal Classical

open Filter
open scoped Topology
section

open ContinuousCircleWeight.Sampling
open scoped Topology
abbrev PhaseCube (r : ℕ) := Fin r → Set.Icc (0:ℝ) 1
end

open Set Filter
open scoped Topology

open ContinuousCircleWeight.Sampling
open scoped Topology


end CircleSampling

end

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_ReturnSamples
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CircleSampling

universe uV

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ComplexInnerProductSpace
open MeasureTheory Filter Set
open Set
open scoped ComplexInnerProductSpace
open Set
open scoped ComplexInnerProductSpace
open MeasureTheory Set Filter Topology
open scoped BigOperators ComplexConjugate
open MeasureTheory Set Filter
open scoped BigOperators ENNReal
open Filter Set
open scoped Topology
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped ENNReal Classical
open Filter
open scoped Topology
open Set Filter
open scoped Topology

section
open scoped Topology

lemma cube_interval_eventually {m : ℕ} (γ : PhaseCube m) {a b : ℝ}
    (hγ : ∀ i, (γ i:ℝ)∈Set.Ioo a b) :
    ∀ᶠ β : PhaseCube m in 𝓝 γ, ∀ i, (β i:ℝ)∈Set.Ioo a b := by
  apply Filter.eventually_all.mpr
  intro i
  exact (continuous_subtype_val.continuousAt.comp (continuous_apply i).continuousAt : ContinuousAt (fun β : PhaseCube m => (β i:ℝ)) γ).eventually
    (Ioo_mem_nhds (hγ i).1 (hγ i).2)
end

open Set Topology
section

lemma rotation_syndetic {θ : ℝ} (hθ : Irrational θ) {O : Set CircleX}
    (hO : IsOpen O) (hne : O.Nonempty) :
    ∃ L : ℕ, 0 < L ∧ ∀ a : ℤ, ∃ n : ℤ,
      a ≤ n ∧ n < a+L ∧ n • (θ:CircleX) ∈ O := by
  classical
  have hd : DenseRange (fun n : ℤ => n • (θ:CircleX)) :=
    AddCircle.denseRange_zsmul_coe_iff.mpr (by simpa using hθ)
  let U : ℤ → Set CircleX := fun n => (fun x => x+n•(θ:CircleX)) ⁻¹' O
  have hU : ∀ n, IsOpen (U n) := fun n => hO.preimage (by fun_prop)
  have hc : (univ : Set CircleX) ⊆ ⋃ n, U n := by
    intro x _
    obtain ⟨y,hy⟩ := hne
    have ho : IsOpen ((fun z : CircleX => x+z) ⁻¹' O) := hO.preimage (by fun_prop)
    obtain ⟨n,hn⟩ := hd.exists_mem_open ho ⟨y-x,by simpa using hy⟩
    exact mem_iUnion.mpr ⟨n,hn⟩
  obtain ⟨S,hS⟩ := isCompact_univ.elim_finite_subcover U hU hc
  let B : ℕ := S.sup Int.natAbs
  refine ⟨2*B+1,by omega,?_⟩
  intro a
  obtain ⟨k,hk,hx⟩ := mem_iUnion₂.mp (hS (mem_univ ((a+B)•(θ:CircleX))))
  have hb : k.natAbs ≤ B := Finset.le_sup (f := Int.natAbs) hk
  have hkle : k ≤ (B:ℤ) := (Int.le_natAbs (a:=k)).trans (by exact_mod_cast hb)
  have hkge : -(B:ℤ) ≤ k := by
    have hab : |k| ≤ (B:ℤ) := by
      simpa only [Int.natCast_natAbs] using (show (k.natAbs:ℤ) ≤ B by exact_mod_cast hb)
    exact (abs_le.mp hab).1
  refine ⟨a+B+k,by omega,by push_cast; omega,?_⟩
  simpa only [U,mem_preimage,add_zsmul] using hx

lemma return_samples {θ : ℝ} (hθ : Irrational θ) {O : Set CircleX}
    (hO : IsOpen O) (hne : O.Nonempty) :
    ∃ L : ℕ, 0 < L ∧ ∀ (a : ℤ) (P : ℕ), ∃ S : Finset ℤ,
      S.card=P ∧ ∀ n ∈ S, a ≤ n ∧ n < a+P*L ∧ n•(θ:CircleX) ∈ O := by
  classical
  obtain ⟨L,hL,hret⟩ := rotation_syndetic hθ hO hne
  refine ⟨L,hL,?_⟩
  intro a P
  choose n hn using (fun j : Fin P => hret (a+(j:ℤ)*L))
  have hinj : Function.Injective n := by
    intro j k he
    apply Fin.ext
    by_contra hne
    rcases lt_or_gt_of_ne hne with hjk | hkj
    · have hcast : (j:ℤ)+1 ≤ (k:ℤ) := by exact_mod_cast hjk
      have hmul := mul_le_mul_of_nonneg_right hcast (show (0:ℤ) ≤ L by positivity)
      have hj := (hn j).2.1
      have hk := (hn k).1
      rw [he] at hj
      nlinarith
    · have hcast : (k:ℤ)+1 ≤ (j:ℤ) := by exact_mod_cast hkj
      have hmul := mul_le_mul_of_nonneg_right hcast (show (0:ℤ) ≤ L by positivity)
      have hj := (hn j).1
      have hk := (hn k).2.1
      rw [he] at hj
      nlinarith
  refine ⟨Finset.univ.image n,by simp [Finset.card_image_of_injective _ hinj],?_⟩
  intro k hk
  obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hk
  refine ⟨?_,?_,(hn j).2.2⟩
  · have hz : (0:ℤ) ≤ (j:ℤ)*L := by positivity
    exact le_trans (by omega) (hn j).1
  · have hcast : (j:ℤ)+1 ≤ (P:ℤ) := by exact_mod_cast j.isLt
    have hmul := mul_le_mul_of_nonneg_right hcast (show (0:ℤ) ≤ L by positivity)
    have hj := (hn j).2.1
    nlinarith
end

open scoped BigOperators
section

lemma finite_separated_subset {V : Type uV} [DecidableEq V] (C : Finset V) (R : V → V → Prop) [DecidableRel R]
    (hsym : ∀ ⦃a b⦄, R a b → R b a) (hrefl : ∀ a, R a a) (D : ℕ)
    (hdeg : ∀ a∈C, (C.filter (R a)).card ≤ D) :
    ∃ S : Finset V, S⊆C ∧ (∀ a∈S, ∀ b∈S, a≠b → ¬R a b) ∧ C.card ≤ S.card*D := by
  classical
  let A := C.powerset.filter (fun S ↦ ∀ a∈S, ∀ b∈S, a≠b → ¬R a b)
  have hA : A.Nonempty := ⟨∅,by simp [A]⟩
  obtain ⟨S,hS,hmax⟩ := Finset.exists_max_image A Finset.card hA
  simp only [A, Finset.mem_filter, Finset.mem_powerset] at hS
  obtain ⟨hSC, hsep⟩ := hS
  have hcover : C⊆S.biUnion (fun a ↦ C.filter (R a)) := by
    intro b hb
    by_contra hnot
    have hno : ∀ a∈S, ¬R a b := by
      intro a ha hab
      exact hnot (Finset.mem_biUnion.mpr ⟨a,ha,Finset.mem_filter.mpr ⟨hb,hab⟩⟩)
    have hbS : b∉S := fun h ↦ hno b h (hrefl b)
    have hins : insert b S∈A := by
      simp only [A, Finset.mem_filter, Finset.mem_powerset]
      refine ⟨Finset.insert_subset hb hSC,?_⟩
      intro a ha c hc hac
      by_cases hab : a=b
      · subst a
        have hcS : c∈S := Finset.mem_of_mem_insert_of_ne hc (Ne.symm hac)
        exact fun h ↦ hno c hcS (hsym h)
      · have haS : a∈S := Finset.mem_of_mem_insert_of_ne ha hab
        by_cases hcb : c=b
        · subst c
          exact hno a haS
        · have hcS : c∈S := Finset.mem_of_mem_insert_of_ne hc hcb
          exact hsep a haS c hcS hac
    have hle := hmax (insert b S) hins
    rw [Finset.card_insert_of_notMem hbS] at hle
    omega
  refine ⟨S,hSC,hsep,?_⟩
  calc
    C.card ≤ (S.biUnion (fun a ↦ C.filter (R a))).card := Finset.card_le_card hcover
    _ ≤ ∑ a∈S, (C.filter (R a)).card := Finset.card_biUnion_le
    _ ≤ ∑ _a∈S, D := Finset.sum_le_sum fun a ha ↦ hdeg a (hSC ha)
    _ = S.card*D := by simp


open Finset
lemma linear_filter_card (C : Finset ℤ) (a b : ℤ) (hb : b ≠ 0) (R : ℕ) :
    (C.filter (fun n => |a+b*n| ≤ (R:ℤ))).card ≤ 2*R+1 := by
  classical
  let S := C.filter (fun n => |a+b*n| ≤ (R:ℤ))
  have hinj : Function.Injective (fun n : ℤ => a+b*n) := by
    intro m n h
    exact mul_left_cancel₀ hb (add_left_cancel h)
  calc
    S.card = (S.image (fun n => a+b*n)).card := (Finset.card_image_of_injective S hinj).symm
    _ ≤ (Finset.Icc (-(R:ℤ)) R).card := by
      apply Finset.card_le_card
      intro k hk
      obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hk
      exact Finset.mem_Icc.mpr (abs_le.mp (Finset.mem_filter.mp hn).2)
    _ = 2*R+1 := by simp; omega

lemma separated_integer_samples (C : Finset ℤ) (H R : ℕ)
    (hC : ∀ n ∈ C, (R:ℤ) < |n|) :
    ∃ S : Finset ℤ, S ⊆ C ∧
      (∀ n ∈ S, ∀ n' ∈ S, n ≠ n' → ∀ v v' : ℤ,
        |v| ≤ H → |v'| ≤ H → (v ≠ 0 ∨ v' ≠ 0) → (R:ℤ) < |v*n+v'*n'|) ∧
      C.card ≤ S.card*(1+(2*H+1)^2*(2*R+1)) := by
  classical
  let V : Finset ℤ := (Finset.Icc (-(H:ℤ)) H).erase 0
  let E : ℤ → ℤ → Prop := fun n n' => n=n' ∨ ∃ v ∈ V, ∃ v' ∈ V, |v*n+v'*n'| ≤ (R:ℤ)
  have hsym : ∀ ⦃n n'⦄, E n n' → E n' n := by
    intro n n' h
    rcases h with h | ⟨v,hv,v',hv',hh⟩
    · exact Or.inl h.symm
    · exact Or.inr ⟨v',hv',v,hv,by simpa [add_comm] using hh⟩
  have hcardV : V.card ≤ 2*H+1 := by
    exact (card_erase_le).trans (by simp; omega)
  have hdeg : ∀ n ∈ C, (C.filter (E n)).card ≤ 1+(2*H+1)^2*(2*R+1) := by
    intro n _
    have hsub : C.filter (E n) ⊆ {n} ∪ V.biUnion (fun v => V.biUnion (fun v' =>
        C.filter (fun n' => |v*n+v'*n'| ≤ (R:ℤ)))) := by
      intro n' hn'
      obtain ⟨hh,h⟩ := Finset.mem_filter.mp hn'
      rcases h with he | ⟨v,hv,v',hv',hne⟩
      · exact mem_union_left _ (mem_singleton.mpr he.symm)
      · exact mem_union_right _ (mem_biUnion.mpr ⟨v,hv,mem_biUnion.mpr ⟨v',hv',Finset.mem_filter.mpr ⟨hh,hne⟩⟩⟩)
    calc
      _ ≤ ({n} ∪ V.biUnion (fun v => V.biUnion (fun v' => C.filter (fun n' => |v*n+v'*n'| ≤ (R:ℤ))))).card := Finset.card_le_card hsub
      _ ≤ 1+V.card*(V.card*(2*R+1)) := by
        apply (Finset.card_union_le _ _).trans
        simp only [Finset.card_singleton]
        apply Nat.add_le_add_left
        apply card_biUnion_le.trans
        calc
          _ ≤ ∑ v ∈ V, (V.card*(2*R+1)) := by
            apply sum_le_sum
            intro v _
            apply card_biUnion_le.trans
            calc
              _ ≤ ∑ _ ∈ V, (2*R+1) := sum_le_sum (fun v' hv' =>
                linear_filter_card C (v*n) v' (ne_of_mem_erase hv') R)
              _ = _ := by simp
          _ = _ := by simp
      _ ≤ _ := by nlinarith [Nat.mul_self_le_mul_self hcardV]
  obtain ⟨S,hSC,hs,hcard⟩ := finite_separated_subset C E hsym (fun _ => Or.inl rfl) _ hdeg
  refine ⟨S,hSC,?_,hcard⟩
  intro n hn n' hn' hne v v' hv hv' hnonzero
  by_cases hz : v=0
  · subst v
    have hv'0 : v' ≠ 0 := hnonzero.resolve_left (not_ne_iff.mpr rfl)
    have hge : (1:ℤ) ≤ |v'| := by exact Int.one_le_abs hv'0
    have hh := hC n' (hSC hn')
    simpa only [zero_mul,zero_add,abs_mul] using hh.trans_le (by nlinarith [abs_nonneg n'])
  by_cases hz' : v'=0
  · subst v'
    have hge : (1:ℤ) ≤ |v| := Int.one_le_abs hz
    have hh := hC n (hSC hn)
    simpa only [zero_mul,add_zero,abs_mul] using hh.trans_le (by nlinarith [abs_nonneg n])
  by_contra hh
  apply hs n hn n' hn' hne
  exact Or.inr ⟨v,Finset.mem_erase.mpr ⟨hz,Finset.mem_Icc.mpr (abs_le.mp hv)⟩,
    v',Finset.mem_erase.mpr ⟨hz',Finset.mem_Icc.mpr (abs_le.mp hv')⟩,le_of_not_gt hh⟩
end

section
open Set Filter
open scoped Topology

lemma separated_return_samples {θ : ℝ} (hθ : Irrational θ) {O : Set CircleX}
    (hO : IsOpen O) (hne : O.Nonempty) :
    ∃ L : ℕ, 0 < L ∧ ∀ (H R : ℕ) (Q T : ℝ),
      (R:ℝ) < Q/2 →
      (⌈Q/2⌉:ℝ) + (⌈T*(1+(2*H+1)^2*(2*R+1))⌉₊:ℝ)*L ≤ Q →
      ∃ S : Finset ℤ, T ≤ (S.card:ℝ) ∧
        (∀ n ∈ S, Q/2 ≤ (n:ℝ) ∧ (n:ℝ) ≤ Q ∧ n•(θ:CircleX) ∈ O) ∧
        (∀ n ∈ S, ∀ n' ∈ S, n ≠ n' → ∀ v v' : ℤ,
          |v| ≤ H → |v'| ≤ H → (v ≠ 0 ∨ v' ≠ 0) → (R:ℤ) < |v*n+v'*n'|) := by
  classical
  obtain ⟨L,hL,hret⟩ := return_samples hθ hO hne
  refine ⟨L,hL,?_⟩
  intro H R Q T hQR hlen
  let D := 1+(2*H+1)^2*(2*R+1)
  let P := ⌈T*(D:ℝ)⌉₊
  obtain ⟨C,hC,hmem⟩ := hret ⌈Q/2⌉ P
  have ha : Q/2 ≤ (⌈Q/2⌉:ℝ) := Int.le_ceil _
  have hn (n : ℤ) (hn : n∈C) : Q/2 ≤ (n:ℝ) ∧ (n:ℝ) ≤ Q ∧ n•(θ:CircleX)∈O := by
    obtain ⟨hlo,hhi,ho⟩ := hmem n hn
    refine ⟨ha.trans (by exact_mod_cast hlo),?_,ho⟩
    apply le_trans _ hlen
    exact_mod_cast hhi.le
  have hcR : ∀ n∈C, (R:ℤ) < |n| := by
    intro n hn'
    have hh : (R:ℝ)<(n:ℝ) := hQR.trans_le (hn n hn').1
    exact lt_of_lt_of_le (by exact_mod_cast hh) (le_abs_self n)
  obtain ⟨S,hSC,hsep,hcard⟩ := separated_integer_samples C H R hcR
  refine ⟨S,?_,fun n hn' => hn n (hSC hn'),hsep⟩
  have hp : T*(D:ℝ) ≤ (P:ℝ) := Nat.le_ceil _
  have hcount : (P:ℝ) ≤ (S.card:ℝ)*D := by exact_mod_cast (hC ▸ hcard)
  have hD : (0:ℝ)<D := by dsimp [D]; positivity
  exact (mul_le_mul_iff_left₀ hD).mp (hp.trans hcount)
end

open Set Filter
open scoped Topology
lemma greedy_degree_bound {m K : ℕ} (hm : 1 ≤ m) (hK : K ≤ m) :
    1+(2*m^300+1)^2*(2*(m*K*m^1000)+1) ≤ 28*m^1602 := by
  have h300 : 1 ≤ m^300 := one_le_pow₀ hm
  have h1002 : 1 ≤ m^1002 := one_le_pow₀ hm
  have h1602 : 1 ≤ m^1602 := one_le_pow₀ hm
  have hR : m*K*m^1000 ≤ m^1002 := by
    calc
      m*K*m^1000 ≤ m*m*m^1000 := by gcongr
      _ = m^1002 := by ring
  calc
    1+(2*m^300+1)^2*(2*(m*K*m^1000)+1) ≤ 1+(3*m^300)^2*(3*m^1002) := by
      gcongr  <;> omega
    _ = 1+27*m^1602 := by ring
    _ ≤ 28*m^1602 := by omega

lemma eventually_sampling_length (L K : ℕ) (hL : 0 < L) :
    ∀ᶠ m : ℕ in atTop,
      (m*K*m^1000:ℝ) < (m:ℝ)^((7:ℝ)/10*m)/2 ∧
      (⌈(m:ℝ)^((7:ℝ)/10*m)/2⌉:ℝ) +
        (⌈(m:ℝ)^((69:ℝ)/100*m)*(1+(2*m^300+1)^2*(2*(m*K*m^1000)+1))⌉₊:ℝ)*L ≤
          (m:ℝ)^((7:ℝ)/10*m) := by
  have hg := eventually_rpow_linear_gap (7/10) (69/100) (168*L) 1602 (by norm_num)
  filter_upwards [hg,eventually_ge_atTop (max 1 K)] with m hg hmK
  have hm : 1 ≤ m := (le_max_left _ _).trans hmK
  have hK : K ≤ m := (le_max_right _ _).trans hmK
  have hx : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hx0 : (0:ℝ) < m := lt_of_lt_of_le zero_lt_one hx
  let T : ℝ := (m:ℝ)^((69:ℝ)/100*m)
  let Q : ℝ := (m:ℝ)^((7:ℝ)/10*m)
  let D : ℝ := 1+(2*(m:ℝ)^300+1)^2*(2*((m:ℝ)*K*(m:ℝ)^1000)+1)
  have hT : 1 ≤ T := Real.one_le_rpow hx (by positivity)
  have hD : 1 ≤ D := by dsimp [D]; exact le_add_of_nonneg_right (by positivity)
  have hL' : (1:ℝ) ≤ L := by exact_mod_cast hL
  have hdegree : D ≤ 28*(m:ℝ)^1602 := by
    have hh : ((1+(2*m^300+1)^2*(2*(m*K*m^1000)+1):ℕ):ℝ) ≤ ((28*m^1602:ℕ):ℝ) := Nat.cast_le.mpr (greedy_degree_bound hm hK)
    simpa only [D, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] using hh
  have hg' : 168*(L:ℝ)*(m:ℝ)^1602*T ≤ Q := by
    simpa only [Real.rpow_ofNat] using hg
  have hTDL : 6*(T*D*L) ≤ Q := by
    calc
      6*(T*D*L) ≤ 6*(T*(28*(m:ℝ)^1602)*L) := by gcongr
      _ = 168*(L:ℝ)*(m:ℝ)^1602*T := by ring
      _ ≤ Q := hg'
  have hR : (m:ℝ)*K*(m:ℝ)^1000 ≤ (m:ℝ)^1602 := by
    have hK' : (K:ℝ) ≤ m := Nat.cast_le.mpr hK
    calc
      (m:ℝ)*K*(m:ℝ)^1000 ≤ (m:ℝ)*(m:ℝ)*(m:ℝ)^1000 := by gcongr
      _ = (m:ℝ)^1002 := by ring
      _ ≤ (m:ℝ)^1602 := pow_le_pow_right₀ hx (by omega)
  have hp : (0:ℝ) < (m:ℝ)^1602 := by positivity
  have hQ : 6*(m:ℝ)^1602 ≤ Q := by
    calc
      6*(m:ℝ)^1602 ≤ 168*(L:ℝ)*(m:ℝ)^1602*1 := by nlinarith
      _ ≤ 168*(L:ℝ)*(m:ℝ)^1602*T := by gcongr
      _ ≤ Q := hg'
  refine ⟨by dsimp [Q] at hQ; nlinarith,?_⟩
  change (⌈Q/2⌉:ℝ)+(⌈T*D⌉₊:ℝ)*L ≤ Q
  have hceilQ : (⌈Q/2⌉:ℝ) ≤ Q/2+1 := (Int.ceil_lt_add_one _).le
  have hceilT : (⌈T*D⌉₊:ℝ) ≤ T*D+1 := (Nat.ceil_lt_add_one (show 0 ≤ T*D by positivity)).le
  have hTD : 1 ≤ T*D := one_le_mul_of_one_le_of_one_le hT hD
  have hTDL1 : (L:ℝ) ≤ T*D*L := by nlinarith
  have hbound := mul_le_mul_of_nonneg_right hceilT (show (0:ℝ) ≤ L by positivity)
  nlinarith

lemma eventually_separated_returns {θ : ℝ} (hθ : Irrational θ) {O : Set CircleX}
    (hO : IsOpen O) (hne : O.Nonempty) (K : ℕ) :
    ∀ᶠ m : ℕ in atTop, ∃ S : Finset ℤ,
      (m:ℝ)^((69:ℝ)/100*m) ≤ (S.card:ℝ) ∧
      (∀ n ∈ S, (m:ℝ)^((7:ℝ)/10*m)/2 ≤ (n:ℝ) ∧
        (n:ℝ) ≤ (m:ℝ)^((7:ℝ)/10*m) ∧ n•(θ:CircleX)∈O) ∧
      (∀ n ∈ S, ∀ n' ∈ S, n ≠ n' → ∀ v v' : ℤ,
        |v| ≤ m^300 → |v'| ≤ m^300 → (v ≠ 0 ∨ v' ≠ 0) →
          (m*K*m^1000:ℤ) < |v*n+v'*n'|) := by
  obtain ⟨L,hL,hs⟩ := separated_return_samples hθ hO hne
  filter_upwards [eventually_sampling_length L K hL] with m hm
  have hh := hs (m^300) (m*K*m^1000) ((m:ℝ)^((7:ℝ)/10*m)) ((m:ℝ)^((69:ℝ)/100*m))
    (by simpa only [Nat.cast_mul, Nat.cast_pow] using hm.1)
    (by simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat] using hm.2)
  simpa only [Nat.cast_mul, Nat.cast_pow] using hh


end CircleSampling

end

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_SamplingStage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

universe uτ

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ComplexInnerProductSpace
open MeasureTheory Filter Set
open Set
open scoped ComplexInnerProductSpace
open Set
open scoped ComplexInnerProductSpace
open MeasureTheory Set Filter Topology
open scoped BigOperators ComplexConjugate
open MeasureTheory Set Filter
open scoped BigOperators ENNReal
open Filter Set
open scoped Topology
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped ENNReal Classical
open Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Topology
open scoped BigOperators

open scoped BigOperators
namespace ContinuousCircleWeight

def shiftedPolynomial (K : ℕ) (a : Fin (2 * K + 1) → ℂ) : Polynomial ℂ :=
  ∑ i, Polynomial.monomial i.val (a i)

@[simp] theorem coeff_shiftedPolynomial (K : ℕ) (a : Fin (2 * K + 1) → ℂ)
    (i : Fin (2 * K + 1)) : (shiftedPolynomial K a).coeff i = a i := by
  classical
  simp only [shiftedPolynomial, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
  simp only [Fin.val_inj]
  simp

abbrev CoefficientPair (K : ℕ) :=
  (Fin (2 * K + 1) → ℂ) × (Fin (2 * K + 1) → ℂ)

def lowProduct (K : ℕ) (a : CoefficientPair K) : Fin (2 * K + 1) → ℂ :=
  fun n => (shiftedPolynomial K a.1 * shiftedPolynomial K a.2).coeff n

def centerIndex (K : ℕ) : Fin (2 * K + 1) := ⟨K, by omega⟩

end ContinuousCircleWeight

namespace CircleSampling
open Filter Set
open scoped Topology

def nextWindow (m : ℕ) : ℕ := ⌈(m:ℝ)^((3:ℝ)/4*m)⌉₊
def kappa (j : ℕ) : ℝ := 1/(100*((j:ℝ)+1))

lemma kappa_pos (j : ℕ) : 0 < kappa j := by unfold kappa; positivity

lemma exists_exponential_budget (j K : ℕ) {ε : ℝ} (hε : 0 < ε) (L0 : ℝ) :
    ∃ L : ℝ, 1 ≤ L ∧ L0 ≤ L ∧ (2*(K:ℝ)+1)*3*Real.exp (-L/10000) ≤ ε/((j:ℝ)+1) := by
  have ht : Tendsto (fun L : ℝ => (2*(K:ℝ)+1)*3*Real.exp (-L/10000)) atTop (𝓝 0) := by
    have he := Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.atTop_div_const (show (0:ℝ)<10000 by norm_num))
    simpa only [Function.comp_def, id_eq, neg_div, mul_zero] using he.const_mul ((2*(K:ℝ)+1)*3)
  have hpos : 0 < ε/((j:ℝ)+1) := div_pos hε (by positivity)
  obtain ⟨L,h1,h2,hb⟩ := ((eventually_ge_atTop (1:ℝ)).and
    ((eventually_ge_atTop L0).and (ht.eventually_lt_const hpos))).exists
  exact ⟨L,h1,h2,hb.le⟩

lemma exists_bridge_budget (j : ℕ) (L : ℝ) :
    ∃ G : ℝ, 1 ≤ G ∧ L ≤ kappa (j+1)*Real.sqrt G := by
  have ht : Tendsto (fun G : ℝ => kappa (j+1)*Real.sqrt G) atTop atTop :=
    Real.tendsto_sqrt_atTop.const_mul_atTop (kappa_pos _)
  obtain ⟨G,hG,hL⟩ := ((eventually_ge_atTop (1:ℝ)).and (ht.eventually_ge_atTop L)).exists
  exact ⟨G,hG,hL⟩

lemma eventually_nextWindow_superlinear (C : ℝ) :
    ∀ᶠ m : ℕ in atTop, C*(m:ℝ) < nextWindow m := by
  filter_upwards [eventually_rpow_linear_gap ((3:ℝ)/4) 0 (C+1) 1 (by norm_num),
    eventually_ge_atTop (1:ℕ)] with m hg hm
  have hmR : 0 < (m:ℝ) := by exact_mod_cast hm
  have hh : (C+1)*(m:ℝ) ≤ (m:ℝ)^((3:ℝ)/4*m) := by simpa using hg
  exact (by nlinarith : C*(m:ℝ)<(m:ℝ)^((3:ℝ)/4*m)).trans_le (Nat.le_ceil _)

lemma eventually_nextWindow_overlap (G : ℝ) :
    ∀ᶠ m : ℕ in atTop, G*(nextWindow m:ℝ) < (m:ℝ)^((4:ℝ)/5*m) := by
  filter_upwards [eventually_rpow_linear_gap ((4:ℝ)/5) ((3:ℝ)/4) (2*|G|+1) 0 (by norm_num),
    eventually_ge_atTop (1:ℕ)] with m hg hm
  have hm1 : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hr : 1 ≤ (m:ℝ)^((3:ℝ)/4*m) := Real.one_le_rpow hm1 (by positivity)
  have hc : (nextWindow m:ℝ) < (m:ℝ)^((3:ℝ)/4*m)+1 := Nat.ceil_lt_add_one (by positivity)
  have hc0 : 0 ≤ (nextWindow m:ℝ) := Nat.cast_nonneg _
  have habs := le_abs_self G
  have hh : (2*|G|+1)*(m:ℝ)^((3:ℝ)/4*m) ≤ (m:ℝ)^((4:ℝ)/5*m) := by simpa using hg
  have hc' : (nextWindow m:ℝ) ≤ 2*(m:ℝ)^((3:ℝ)/4*m) := by linarith
  calc
    G*(nextWindow m:ℝ) ≤ |G| *(nextWindow m:ℝ) := mul_le_mul_of_nonneg_right habs hc0
    _ ≤ |G| *(2*(m:ℝ)^((3:ℝ)/4*m)) := mul_le_mul_of_nonneg_left hc' (abs_nonneg G)
    _ < (2*|G|+1)*(m:ℝ)^((3:ℝ)/4*m) := by nlinarith
    _ ≤ (m:ℝ)^((4:ℝ)/5*m) := hh

def StageNumerics (j K : ℕ) (G L Gnext : ℝ) (m : ℕ) : Prop :=
  200 ≤ m ∧ 2^(j+1) ≤ m ∧ K ≤ m ∧ 4*G ≤ (m:ℝ) ∧
  L ≤ kappa j*(m:ℝ)^((1:ℝ)/40) ∧
  Gnext*(nextWindow m:ℝ) < (m:ℝ)^((4:ℝ)/5*m) ∧
  2*K < nextWindow m ∧ m < nextWindow m ∧
  (m:ℝ)^(-(19:ℝ)/20) ≤ 1/4

lemma eventually_StageNumerics (j K : ℕ) (G L Gnext : ℝ) :
    ∀ᶠ m : ℕ in atTop, StageNumerics j K G L Gnext m := by
  have ht : Tendsto (fun m : ℕ => (m:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hp : Tendsto (fun m : ℕ => kappa j*(m:ℝ)^((1:ℝ)/40)) atTop atTop :=
    ((tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/40)).comp ht).const_mul_atTop (kappa_pos j)
  have hb : Tendsto (fun m : ℕ => (m:ℝ)^(-(19:ℝ)/20)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, neg_div] using (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<19/20)).comp ht
  filter_upwards [eventually_ge_atTop (max 200 (max (2^(j+1)) K)), ht.eventually_ge_atTop (4*G),
    hp.eventually_ge_atTop L, eventually_nextWindow_overlap Gnext, eventually_nextWindow_superlinear 2,
    hb.eventually_lt_const (by norm_num : (0:ℝ)<1/4)] with m hm hG hL hov hnext hb
  have hK : K ≤ m := (le_max_right _ _).trans ((le_max_right _ _).trans hm)
  have hm0 : 0 ≤ (m:ℝ) := Nat.cast_nonneg _
  refine ⟨(le_max_left _ _).trans hm,(le_max_left _ _).trans ((le_max_right _ _).trans hm),hK,hG,hL,hov,?_,?_,hb.le⟩
  · have : 2*(K:ℝ) < nextWindow m := lt_of_le_of_lt (by exact_mod_cast Nat.mul_le_mul_left 2 hK) hnext
    exact_mod_cast this
  · have : (m:ℝ) < nextWindow m := by linarith
    exact_mod_cast this
end CircleSampling

end

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_NestedAngles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CircleSampling

universe uS

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ComplexInnerProductSpace
open MeasureTheory Filter Set
open Set
open scoped ComplexInnerProductSpace
open Set
open scoped ComplexInnerProductSpace
open MeasureTheory Set Filter Topology
open scoped BigOperators ComplexConjugate
open MeasureTheory Set Filter
open scoped BigOperators ENNReal
open Filter Set
open scoped Topology
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped ENNReal Classical
open Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Topology
open scoped BigOperators
open scoped BigOperators

open Set
section

def enumeratedRat (n : ℕ) : ℝ := ((Encodable.decode (α := ℚ) n).getD 0:ℚ)

lemma closed_interval_avoiding (r : ℝ) {a b : ℝ} (hab : a<b) :
    ∃ d e : ℝ, d<e ∧ Icc d e ⊆ Ioo a b ∧ r∉Icc d e := by
  by_cases hr : r ≤ (a+b)/2
  · refine ⟨(a+3*b)/4,(a+7*b)/8,by linarith,?_,?_⟩
    · intro x hx; constructor <;> linarith [hx.1,hx.2]
    · intro hr'; linarith [hr'.1]
  · refine ⟨(7*a+b)/8,(3*a+b)/4,by linarith,?_,?_⟩
    · intro x hx; constructor <;> linarith [hx.1,hx.2]
    · intro hr'; linarith [hr'.2]


def extendPrefix (d : ℕ) (old block : ℕ → ℕ) (i : ℕ) : ℕ :=
  if i≤ d then old i else block (i-d)
lemma extendPrefix_old (d : ℕ) (old block : ℕ → ℕ) {i : ℕ} (hi : i≤ d) :
    extendPrefix d old block i=old i := ite_eq_left hi
lemma extendPrefix_block (d : ℕ) (old block : ℕ → ℕ) (h0 : block 0=old d) (k : ℕ) :
    extendPrefix d old block (d+k)=block k := by
  by_cases hk : k=0
  · subst k; simp [extendPrefix,h0]
  · rw [extendPrefix,ite_eq_right (by omega),Nat.add_sub_cancel_left]
lemma extendPrefix_pos (d m : ℕ) (old block : ℕ → ℕ)
    (ho : ∀ i≤ d,0< old i) (hb : ∀ i≤ m,0< block i) {i : ℕ} (hi : i≤ d+m) :
    0< extendPrefix d old block i := by
  by_cases h : i≤ d
  · rw [extendPrefix_old d old block h]; exact ho i h
  · rw [extendPrefix,ite_eq_right h]; exact hb _ (by omega)
lemma extendPrefix_dvd (d m : ℕ) (old block : ℕ → ℕ) (h0 : block 0=old d)
    (ho : ∀ i< d,old i∣old (i+1)) (hb : ∀ i< m,block i∣block (i+1)) {i : ℕ} (hi : i< d+m) :
    extendPrefix d old block i∣extendPrefix d old block (i+1) := by
  by_cases h : i< d
  · rw [extendPrefix_old d old block (by omega),extendPrefix_old d old block (by omega)]
    exact ho i h
  · have he : i=d+(i-d) := by omega
    rw [he,extendPrefix_block d old block h0]
    rw [show d+(i-d)+1=d+((i-d)+1) by omega,extendPrefix_block d old block h0]
    exact hb _ (by omega)
lemma extendPrefix_lt (d m : ℕ) (old block : ℕ → ℕ) (h0 : block 0=old d)
    (ho : ∀ i< d,old i< old (i+1)) (hb : ∀ i< m,block i< block (i+1)) {i : ℕ} (hi : i< d+m) :
    extendPrefix d old block i< extendPrefix d old block (i+1) := by
  by_cases h : i< d
  · rw [extendPrefix_old d old block (by omega),extendPrefix_old d old block (by omega)]
    exact ho i h
  · have he : i=d+(i-d) := by omega
    rw [he,extendPrefix_block d old block h0]
    rw [show d+(i-d)+1=d+((i-d)+1) by omega,extendPrefix_block d old block h0]
    exact hb _ (by omega)
end

open Set
section
def positiveArc (h : CircleX) (r : ℝ) : Set CircleX :=
  {x | x-h ∈ ((↑) : ℝ → CircleX) '' Ioo 0 r}

open Set Filter MeasureTheory ContinuousCircleWeight ContinuousCircleWeight.Sampling
open scoped Topology

structure ScaleState where
  K : ℕ
  d : ℕ
  G : ℝ
  E : ℝ
  Lprev : ℝ
  a : ℝ
  b : ℝ
  q : ℕ → ℕ

structure ScaleState.Valid (s : ScaleState) : Prop where
  Kpos : 0 < s.K
  Gge : 1 ≤ s.G
  Ege : 0 ≤ s.E
  Lge : 1 ≤ s.Lprev
  qzero : s.q 0=1
  qpos : ∀ i≤ s.d, 0 < s.q i
  qdvd : ∀ i< s.d, s.q i∣s.q (i+1)
  qlt : ∀ i< s.d, s.q i< s.q (i+1)
  ab : s.a< s.b

def gridTolerance (j : ℕ) (s : ScaleState) : ℝ :=
  1/(10*((j:ℝ)+1)^2*(1+(s.d:ℝ))*(s.q s.d:ℝ))
def gridPoint (s : ScaleState) (a : Fin (s.q s.d)) : CircleX := ((a.val:ℝ)/(s.q s.d:ℝ):ℝ)

def CoefficientBudget (j : ℕ) (s : ScaleState) (ε : ℝ) : Prop :=
  ∀ A : CoefficientPair s.K,
    (∀ i, ‖A.1 i‖ ≤ Real.exp (((s.K:ℝ)+1)*s.E)) →
    (∀ i, ‖A.2 i‖ ≤ Real.exp (((s.K:ℝ)+1)*s.E)) →
    1/((j:ℝ)+1) ≤ ‖A.1 (centerIndex s.K)‖ →
    1/((j:ℝ)+1) ≤ ‖A.2 (centerIndex s.K)‖ →
    ∃ n : Fin (2*s.K+1), ε≤‖lowProduct s.K A n‖

structure ScaleStep (j : ℕ) (s : ScaleState) where
  ε : ℝ
  L : ℝ
  Gnext : ℝ
  εpos : 0 < ε
  coefficients : CoefficientBudget j s ε
  Lge : 1 ≤ L
  Lprev : s.Lprev ≤ L
  exponential : (2*(s.K:ℝ)+1)*3*Real.exp (-L/10000) ≤ ε/((j:ℝ)+1)
  Gge : 1 ≤ Gnext
  bridge : L ≤ kappa (j+1)*Real.sqrt Gnext
  m : ℕ
  numeric : StageNumerics j s.K s.G L Gnext m
  samples : Fin (s.q s.d) → Finset ℤ
  samples_nonempty : ∀ t, (samples t).Nonempty
  samples_bounds : ∀ t n, n∈samples t →
    (m:ℝ)^((7:ℝ)/10*m)/2 ≤ (n:ℝ) ∧ (n:ℝ) ≤ (m:ℝ)^((7:ℝ)/10*m)
  q : ℕ → ℕ
  qzero : q 0=s.q s.d
  qpos : ∀ i≤ m, 0 < q i
  qratio : ∀ i< m, q i∣q (i+1) ∧ 100*(m:ℝ) < (q (i+1):ℝ)/q i
  a : ℝ
  b : ℝ
  ab : a< b
  interval : Icc a b ⊆ Ioo s.a s.b
  avoid : enumeratedRat j∉Icc a b
  phases : ∀ θ∈Icc a b, ∀ i : Fin m,
    Int.fract ((q (i+1):ℝ)*θ)∈Ioo (1/((m:ℝ)*s.K)) (2/((m:ℝ)*s.K))
  cover : ∀ θ∈Icc a b, ∀ k : ℤ,
    ((m:ℝ)*s.K)/4 ≤ |(k:ℝ)| → |(k:ℝ)| ≤ (m:ℝ)^((4:ℝ)/5*m) →
    (m:ℝ)/20 ≤ ((Finset.univ.filter fun i : Fin m =>
      Int.fract ((q (i+1):ℝ)*θ) ∉ phaseFailure ((m:ℝ)^(-(19:ℝ)/20)) k).card:ℝ)
  orbits : ∀ θ∈Icc a b, ∀ t n, n∈samples t → n•(θ:CircleX)∈positiveArc (gridPoint s t) (gridTolerance j s)
  energies : ∀ θ∈Icc a b, ∀ t (positive : Bool),
    (∫ x : CircleX, (idealAverage positive (scaleEll m) (scaleAlpha m)
      (fun n : samples t => (n.val:ℝ))
      (characterCurve (fun i : Fin m => (q (i+1):ℤ)) x)
      (fun i => Int.fract ((q (i+1):ℝ)*θ))-1)^2) < 1/((j:ℝ)+1)^2

def ScaleStep.C {j : ℕ} {s : ScaleState} (t : ScaleStep j s) : ℝ := max t.L ((s.K:ℝ)^2)

def ScaleStep.next {j : ℕ} {s : ScaleState} (t : ScaleStep j s) : ScaleState where
  K := nextWindow t.m
  d := s.d+t.m
  G := t.Gnext
  E := s.E+t.C*t.m
  Lprev := t.L
  a := t.a
  b := t.b
  q := extendPrefix s.d s.q t.q

lemma ScaleStep.mpos {j : ℕ} {s : ScaleState} (t : ScaleStep j s) : 0 < t.m :=
  lt_of_lt_of_le (by norm_num) t.numeric.1

lemma ScaleStep.qstrict {j : ℕ} {s : ScaleState} (t : ScaleStep j s) {i : ℕ} (hi : i< t.m) :
    t.q i< t.q (i+1) := by
  have hp : 0 < (t.q i:ℝ) := Nat.cast_pos.mpr (t.qpos i hi.le)
  have hm : 1 ≤ (t.m:ℝ) := by exact_mod_cast t.mpos
  have hh : 1 < (t.q (i+1):ℝ)/t.q i := by linarith [(t.qratio i hi).2]
  have hh' : (t.q i:ℝ)< t.q (i+1) := by simpa using (lt_div_iff₀ hp).mp hh
  exact_mod_cast hh'

lemma ScaleStep.next_valid {j : ℕ} {s : ScaleState} (t : ScaleStep j s) (hs : s.Valid) : t.next.Valid := by
  refine ⟨?_,t.Gge,?_,t.Lge,?_,?_,?_,?_,t.ab⟩
  · have hh := t.numeric.2.2.2.2.2.2.1
    change 0 < nextWindow t.m
    omega
  · change 0≤ s.E+t.C*t.m
    have hC : 0 ≤ t.C := by
      change 0 ≤ max t.L ((s.K:ℝ)^2)
      exact le_trans (show (0:ℝ) ≤ t.L by linarith [t.Lge]) (le_max_left t.L ((s.K:ℝ)^2))
    exact add_nonneg hs.Ege (mul_nonneg hC (Nat.cast_nonneg _))
  · change extendPrefix s.d s.q t.q 0=1
    rw [extendPrefix_old _ _ _ (Nat.zero_le _),hs.qzero]
  · intro i hi
    exact extendPrefix_pos s.d t.m s.q t.q hs.qpos t.qpos hi
  · intro i hi
    exact extendPrefix_dvd s.d t.m s.q t.q t.qzero hs.qdvd (fun i hi => (t.qratio i hi).1) hi
  · intro i hi
    exact extendPrefix_lt s.d t.m s.q t.q t.qzero hs.qlt (fun _ hi => t.qstrict hi) hi

end

open Set


end CircleSampling

end

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_MeasurableWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CircleModel

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ComplexInnerProductSpace
open MeasureTheory Filter Set
open Set
open scoped ComplexInnerProductSpace
open Set
open scoped ComplexInnerProductSpace
open MeasureTheory Set Filter Topology
open scoped BigOperators ComplexConjugate
open MeasureTheory Set Filter
open scoped BigOperators ENNReal
open Filter Set
open scoped Topology
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped ENNReal Classical
open Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Topology
open scoped BigOperators
open scoped BigOperators
open Set
open Set
open Set

open Set MeasureTheory Filter
open scoped BigOperators ENNReal Topology Classical
section
abbrev CircleX := AddCircle (1:ℝ)
def repr (x : CircleX) : ℝ := (AddCircle.measurableEquivIco 1 0 x).val
lemma repr_mem (x : CircleX) : repr x ∈ Ico 0 1 := by
  simpa [repr] using (AddCircle.measurableEquivIco 1 0 x).property
lemma repr_mk (x : ℝ) : repr (x : CircleX) = Int.fract x := by
  change (AddCircle.equivIco 1 0 (x : CircleX)).val = _
  simpa only [div_one,mul_one] using AddCircle.coe_equivIco_mk_apply (p := (1:ℝ)) x
lemma measurable_repr : Measurable repr :=
  measurable_subtype_coe.comp (AddCircle.measurableEquivIco 1 0).measurable

def Xi (q : ℕ → ℕ) (i : ℕ) (x : CircleX) : ℝ := repr (q i • x)
def beta (q : ℕ → ℕ) (θ : CircleX) (i : ℕ) : ℝ := Xi q i θ
def shift (θ : CircleX) (k : ℤ) (x : CircleX) : CircleX := x+k•θ

def floorTerm (q : ℕ → ℕ) (θ : CircleX) (k : ℤ) (x : CircleX) (i : ℕ) : ℤ :=
  ⌊Xi q i x + k*beta q θ i⌋

def good0 (q : ℕ → ℕ) (θ : CircleX) : Set CircleX :=
  {x | ∀ k : ℤ, (Function.support (floorTerm q θ k x)).Finite}

def good (q : ℕ → ℕ) (θ : CircleX) : Set CircleX :=
  {x | ∀ a : ℤ, shift θ a x ∈ good0 q θ}

lemma shift_zero (θ : CircleX) (x : CircleX) : shift θ 0 x=x := by simp [shift]

lemma good_subset_good0 (q : ℕ → ℕ) (θ : CircleX) : good q θ ⊆ good0 q θ := by
  intro x hx
  simpa [shift_zero] using hx 0

lemma floorTerm_zero (q : ℕ → ℕ) (θ : CircleX) (x : CircleX) (i : ℕ) :
    floorTerm q θ 0 x i = 0 := by
  simp only [floorTerm,Int.cast_zero,zero_mul,add_zero]
  exact Int.floor_eq_iff.mpr (by simpa [Xi] using repr_mem (q i • x))

lemma floorTerm_mono (q : ℕ → ℕ) (θ : CircleX) (x : CircleX) (i : ℕ) :
    Monotone fun k : ℤ ↦ floorTerm q θ k x i := by
  intro k l h
  apply Int.floor_mono
  gcongr
  exact (repr_mem _).1

def exponent (q : ℕ → ℕ) (θ : CircleX) (c : ℕ → ℝ) (k : ℤ) (x : CircleX) : ℝ :=
  ∑' i, c i * (floorTerm q θ k x i : ℝ)

def cocycle (q : ℕ → ℕ) (θ : CircleX) (c : ℕ → ℝ) (k : ℤ) (x : CircleX) : ℝ :=
  if x ∈ good q θ then Real.exp (-exponent q θ c k x) else 1

lemma summable_exponent {q : ℕ → ℕ} {θ : CircleX} (c : ℕ → ℝ) (k : ℤ) {x : CircleX}
    (hx : x∈good q θ) : Summable (fun i ↦ c i*(floorTerm q θ k x i:ℝ)) := by
  apply summable_of_hasFiniteSupport
  apply (good_subset_good0 q θ hx k).subset
  intro i hi
  contrapose! hi
  simp only [Function.mem_support] at *
  simp [hi]

lemma cocycle_pos (q : ℕ → ℕ) (θ : CircleX) (c : ℕ → ℝ) (k : ℤ) (x : CircleX) :
    0<cocycle q θ c k x := by
  unfold cocycle
  split_ifs
  · exact Real.exp_pos _
  · norm_num

lemma cocycle_zero (q : ℕ → ℕ) (θ : CircleX) (c : ℕ → ℝ) (x : CircleX) :
    cocycle q θ c 0 x = 1 := by
  simp [cocycle,exponent,floorTerm_zero]

lemma cocycle_antitone (q : ℕ → ℕ) (θ : CircleX) (c : ℕ → ℝ) (hc : ∀ i, 0≤c i) (x : CircleX) :
    Antitone fun k : ℤ ↦ cocycle q θ c k x := by
  intro k l hkl
  unfold cocycle
  split_ifs with hx
  · apply Real.exp_le_exp.mpr
    apply _root_.neg_le_neg
    exact (summable_exponent c k hx).tsum_le_tsum (fun i ↦ mul_le_mul_of_nonneg_left
      (by exact_mod_cast floorTerm_mono q θ x i hkl) (hc i)) (summable_exponent c l hx)
  · exact le_rfl


lemma measurable_Xi (q : ℕ → ℕ) (i : ℕ) : Measurable (Xi q i) :=
  measurable_repr.comp (continuous_id.nsmul (q i)).measurable

lemma measurable_floorTerm (q : ℕ → ℕ) (θ : CircleX) (k : ℤ) (i : ℕ) :
    Measurable (fun x ↦ floorTerm q θ k x i) :=
  ((measurable_Xi q i).add_const _).floor

lemma finite_support_iff (f : ℕ → ℤ) : (Function.support f).Finite ↔ ∃ N, ∀ i≥N, f i=0 := by
  constructor
  · intro hf
    obtain ⟨N,hN⟩ := hf.bddAbove
    refine ⟨N+1,fun i hi ↦ ?_⟩
    by_contra h
    have := hN h
    omega
  · rintro ⟨N,hN⟩
    apply (Finset.finite_toSet (Finset.range N)).subset
    intro i hi
    simp only [Finset.mem_coe,Finset.mem_range]
    by_contra! h
    exact hi (hN i h)

lemma measurableSet_good0 (q : ℕ → ℕ) (θ : CircleX) : MeasurableSet (good0 q θ) := by
  change MeasurableSet {x | ∀ k : ℤ, (Function.support (floorTerm q θ k x)).Finite}
  simp only [finite_support_iff,Set.ofPred_forall,Set.ofPred_exists]
  exact MeasurableSet.iInter fun k ↦ MeasurableSet.iUnion fun N ↦
    MeasurableSet.iInter fun i ↦ MeasurableSet.iInter fun (_h : N ≤ i) ↦
      (measurable_floorTerm q θ k i) (measurableSet_singleton 0)

lemma measurableSet_good (q : ℕ → ℕ) (θ : CircleX) : MeasurableSet (good q θ) := by
  change MeasurableSet {x | ∀ a : ℤ, shift θ a x ∈ good0 q θ}
  simp only [Set.ofPred_forall]
  exact MeasurableSet.iInter fun a : ℤ ↦
    (continuous_id.add continuous_const).measurable (measurableSet_good0 q θ)

lemma measurable_exponent (q : ℕ → ℕ) (θ : CircleX) (c : ℕ → ℝ) (k : ℤ) :
    Measurable (exponent q θ c k) :=
  Measurable.tsum fun i ↦ measurable_const.mul ((continuous_of_discreteTopology : Continuous (fun n : ℤ ↦ (n : ℝ))).measurable.comp (measurable_floorTerm q θ k i))

lemma measurable_cocycle (q : ℕ → ℕ) (θ : CircleX) (c : ℕ → ℝ) (k : ℤ) :
    Measurable (cocycle q θ c k) :=
  ((measurable_exponent q θ c k).neg.exp).piecewise (measurableSet_good q θ) measurable_const

end
open Set MeasureTheory Filter
open scoped BigOperators

lemma floorTerm_ordered {q : ℕ → ℕ} {θ : CircleX} (k : ℤ) {x y : CircleX} {i : ℕ}
    (h : Xi q i x ≤ Xi q i y) : floorTerm q θ k x i ≤ floorTerm q θ k y i :=
  Int.floor_mono (by linarith)

lemma cocycle_ratio_exp {q : ℕ → ℕ} {θ : CircleX} (c : ℕ → ℝ) (k : ℤ) {x y : CircleX}
    (hx : x∈good q θ) (hy : y∈good q θ) :
    cocycle q θ c k y/cocycle q θ c k x = Real.exp (exponent q θ c k x-exponent q θ c k y) := by
  simp only [cocycle,ite_eq_left hx,ite_eq_left hy,←Real.exp_sub]
  congr 1
  ring

lemma floor_crossing {s t a : ℝ} (hs : s∈Ico 0 1) (ht : t∈Ico 0 1)
    (hlo : s<1-Int.fract a) (hhi : 1-Int.fract a≤t) : ⌊t+a⌋=⌊s+a⌋+1 := by
  have ha : a=Int.fract a+(⌊a⌋:ℝ) := by rw [Int.fract]; ring
  have hs0 : ⌊s+Int.fract a⌋=0 := Int.floor_eq_iff.mpr (by
    push_cast; constructor <;> linarith [Int.fract_nonneg a,hs.1])
  have ht1 : ⌊t+Int.fract a⌋=1 := Int.floor_eq_iff.mpr (by
    push_cast; constructor <;> linarith [Int.fract_lt_one a,ht.2])
  rw [ha,←add_assoc,←add_assoc,Int.floor_add_intCast,Int.floor_add_intCast,hs0,ht1]
  omega

lemma cocycle_ratio_crossing {q : ℕ → ℕ} {θ : CircleX} (c : ℕ → ℝ) (hc : ∀ i,0≤c i)
    (k : ℤ) {x y : CircleX} (hx : x∈good q θ) (hy : y∈good q θ)
    (hxy : ∀ i,Xi q i x≤Xi q i y) (i : ℕ)
    (hlo : Xi q i x<1-Int.fract ((k:ℝ)*beta q θ i))
    (hhi : 1-Int.fract ((k:ℝ)*beta q θ i)≤Xi q i y) :
    cocycle q θ c k y/cocycle q θ c k x ≤ Real.exp (-c i) := by
  have hcross : floorTerm q θ k y i=floorTerm q θ k x i+1 :=
    floor_crossing (repr_mem _) (repr_mem _) hlo hhi
  have hs : Summable (fun a => c a*((floorTerm q θ k y a:ℝ)-(floorTerm q θ k x a:ℝ))) := by
    simpa only [mul_sub] using (summable_exponent c k hy).sub (summable_exponent c k hx)
  have hn : ∀ a,0≤c a*((floorTerm q θ k y a:ℝ)-(floorTerm q θ k x a:ℝ)) := by
    intro a
    exact mul_nonneg (hc a) (sub_nonneg.mpr (Int.cast_le.mpr (floorTerm_ordered k (hxy a))))
  have hb := hs.le_tsum i (fun a _ => hn a)
  have he : (∑' a,c a*((floorTerm q θ k y a:ℝ)-(floorTerm q θ k x a:ℝ))) =
      exponent q θ c k y-exponent q θ c k x := by
    simp only [mul_sub,exponent,(summable_exponent c k hy).tsum_sub (summable_exponent c k hx)]
  rw [he,hcross,Int.cast_add,Int.cast_one] at hb
  rw [cocycle_ratio_exp c k hx hy]
  exact Real.exp_le_exp.mpr (by nlinarith)


end CircleModel

end

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_DigitCouplings
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CircleCoupling

universe uκ uD

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ComplexInnerProductSpace
open MeasureTheory Filter Set
open Set
open scoped ComplexInnerProductSpace
open Set
open scoped ComplexInnerProductSpace
open MeasureTheory Set Filter Topology
open scoped BigOperators ComplexConjugate
open MeasureTheory Set Filter
open scoped BigOperators ENNReal
open Filter Set
open scoped Topology
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped ENNReal Classical
open Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Topology
open scoped BigOperators
open scoped BigOperators
open Set
open Set
open Set
open Set MeasureTheory Filter
open scoped BigOperators ENNReal Topology Classical
open MeasureTheory Set Filter
open scoped ENNReal Topology
open MeasureTheory Set
open MeasureTheory Filter Set
open scoped Topology BoundedContinuousFunction
open MeasureTheory Set Filter Topology TopologicalSpace

open MeasureTheory Set
open scoped ENNReal BigOperators Classical
section

instance labelMeasurableSpace {κ : Type uκ} : MeasurableSpace (Option κ) := ⊤
instance labelMeasurableSingleton {κ : Type uκ} : MeasurableSingletonClass (Option κ) := ⟨by intro a; trivial⟩

def uniformOn {D : Type uD} [MeasurableSpace D] (S : Finset D) (hs : S.Nonempty) : Measure D :=
  (PMF.uniformOfFinset S hs).toMeasure
instance instIsProbabilityMeasureUniformOn {D : Type uD} [MeasurableSpace D] (S : Finset D) (hs : S.Nonempty) :
    IsProbabilityMeasure (uniformOn S hs) := by unfold uniformOn; infer_instance

lemma uniformOn_singleton {D : Type uD} [MeasurableSpace D] [MeasurableSingletonClass D]
    (S : Finset D) (hs : S.Nonempty) (d : D) :
    uniformOn S hs {d} = if d ∈ S then (S.card : ℝ≥0∞)⁻¹ else 0 := by
  classical
  simp [uniformOn, PMF.toMeasure_apply_singleton, PMF.uniformOfFinset_apply]

def labelled {κ : Type uκ} {D : Type uD} [MeasurableSpace κ] [MeasurableSpace D]
    (a : Option κ) (μ : Measure (D × D)) : Measure (Option κ × (D × D)) :=
  Measure.map (fun z => (a,z)) μ

def mixture {κ : Type uκ} {D : Type uD} [Fintype κ] [MeasurableSpace κ] [MeasurableSpace D]
    (p : κ → ℝ≥0∞) (p₀ : ℝ≥0∞) (μ₀ : Measure (D × D))
    (μ : κ → Measure (D × D)) : Measure (Option κ × (D × D)) :=
  p₀ • labelled none μ₀ + ∑ a, p a • labelled (some a) (μ a)

lemma labelled_univ {κ : Type uκ} {D : Type uD} [MeasurableSpace κ] [MeasurableSpace D]
    (a : Option κ) (μ : Measure (D × D)) : labelled a μ univ = μ univ := by
  rw [labelled, Measure.map_apply (show Measurable (fun z : D × D => (a,z)) from measurable_const.prodMk measurable_id) MeasurableSet.univ]
  simp

lemma mixture_probability {κ : Type uκ} {D : Type uD} [Fintype κ] [MeasurableSpace κ] [MeasurableSpace D]
    (p : κ → ℝ≥0∞) (p₀ : ℝ≥0∞) (μ₀ : Measure (D × D))
    (μ : κ → Measure (D × D)) [IsProbabilityMeasure μ₀] [∀ a, IsProbabilityMeasure (μ a)]
    (hp : p₀ + ∑ a, p a = 1) : IsProbabilityMeasure (mixture p p₀ μ₀ μ) := by
  constructor
  simpa [mixture, Measure.add_apply, Measure.sum_apply, Measure.smul_apply, labelled_univ,
    measure_univ] using hp

lemma labelled_fiber {κ : Type uκ} {D : Type uD} [MeasurableSpace κ] [MeasurableSpace D]
    [MeasurableSingletonClass D] (a : Option κ) (μ : Measure (D × D))
    (f : D × D → D) (hf : Measurable f) (d : D) :
    labelled a μ {ω | f ω.2 = d} = μ (f ⁻¹' {d}) := by
  change labelled a μ ((fun ω => f ω.2) ⁻¹' {d}) = _
  unfold labelled
  exact Measure.map_apply (show Measurable (fun z : D × D => (a,z)) from
    measurable_const.prodMk measurable_id) ((hf.comp measurable_snd) (measurableSet_singleton d))

lemma labelled_fiber_label {κ : Type uκ} {D : Type uD} [MeasurableSpace κ] [MeasurableSpace D]
    [MeasurableSingletonClass κ] [MeasurableSingletonClass D]
    (a b : Option κ) (μ : Measure (D × D))
    (f : D × D → D) (hf : Measurable f) (d : D) :
    labelled a μ {ω | f ω.2 = d ∧ ω.1 = b} = if a = b then μ (f ⁻¹' {d}) else 0 := by
  classical
  have hm : MeasurableSet {ω : Option κ × (D × D) | f ω.2 = d ∧ ω.1 = b} :=
    ((hf.comp measurable_snd) (measurableSet_singleton d)).inter
      (measurable_fst (measurableSet_singleton b))
  rw [labelled, Measure.map_apply (show Measurable (fun z : D × D => (a,z)) from measurable_const.prodMk measurable_id) hm]
  by_cases hab : a = b
  · simp only [hab, ↓reduceIte]
    congr 1
    ext z
    simp
  · simp only [hab, ↓reduceIte]
    have : (fun z => (a,z)) ⁻¹' {ω : Option κ × (D × D) | f ω.2 = d ∧ ω.1 = b} = ∅ := by
      ext z; simp [hab]
    rw [this,measure_empty]

lemma mixture_fiber {κ : Type uκ} {D : Type uD} [Fintype κ] [MeasurableSpace κ] [MeasurableSpace D]
    [MeasurableSingletonClass D]
    (p : κ → ℝ≥0∞) (p₀ : ℝ≥0∞) (μ₀ : Measure (D × D))
    (μ : κ → Measure (D × D)) (f : D × D → D) (hf : Measurable f) (d : D) :
    mixture p p₀ μ₀ μ {ω | f ω.2 = d} =
      p₀ * μ₀ (f ⁻¹' {d}) + ∑ a, p a * μ a (f ⁻¹' {d}) := by
  simp [mixture,Measure.add_apply,Measure.smul_apply,
    labelled_fiber _ _ f hf d]

lemma mixture_fiber_label {κ : Type uκ} {D : Type uD} [Fintype κ] [MeasurableSpace κ] [MeasurableSpace D]
    [MeasurableSingletonClass κ] [MeasurableSingletonClass D]
    (p : κ → ℝ≥0∞) (p₀ : ℝ≥0∞) (μ₀ : Measure (D × D))
    (μ : κ → Measure (D × D)) (f : D × D → D) (hf : Measurable f) (d : D) (a : κ) :
    mixture p p₀ μ₀ μ {ω | f ω.2 = d ∧ ω.1 = some a} = p a * μ a (f ⁻¹' {d}) := by
  classical
  simp [mixture,Measure.add_apply,Measure.smul_apply,
    labelled_fiber_label _ _ _ f hf d]

lemma prod_fiber_fst {D : Type uD} [MeasurableSpace D] [MeasurableSingletonClass D]
    (μ ν : Measure D) [IsProbabilityMeasure ν] (d : D) :
    (μ.prod ν) (Prod.fst ⁻¹' {d}) = μ {d} := by
  rw [show Prod.fst ⁻¹' {d} = ({d} : Set D) ×ˢ univ by ext z; simp,
    Measure.prod_prod,measure_univ,mul_one]

lemma prod_fiber_snd {D : Type uD} [MeasurableSpace D] [MeasurableSingletonClass D]
    (μ ν : Measure D) [IsProbabilityMeasure μ] [SFinite ν] (d : D) :
    (μ.prod ν) (Prod.snd ⁻¹' {d}) = ν {d} := by
  rw [show Prod.snd ⁻¹' {d} = (univ : Set D) ×ˢ {d} by ext z; simp,
    Measure.prod_prod,measure_univ,one_mul]


def lowerDigits (l a : ℕ) (ha : a < l) : Finset (Fin l) := Finset.Iio ⟨a,ha⟩
def upperDigits (l b : ℕ) (hb : b < l) : Finset (Fin l) := Finset.Ici ⟨b,hb⟩

lemma lowerDigits_nonempty (l a : ℕ) (ha : a < l) (hpos : 0 < a) :
    (lowerDigits l a ha).Nonempty := by
  exact ⟨⟨0,lt_trans hpos ha⟩,by simpa [lowerDigits,Fin.lt_def] using hpos⟩
lemma upperDigits_nonempty (l b : ℕ) (hb : b < l) :
    (upperDigits l b hb).Nonempty := by
  exact ⟨⟨b,hb⟩,by simp [upperDigits]⟩

@[simp] lemma card_lowerDigits (l a : ℕ) (ha : a < l) : (lowerDigits l a ha).card = a := by
  simp [lowerDigits]
@[simp] lemma card_upperDigits (l b : ℕ) (hb : b < l) : (upperDigits l b hb).card = l-b := by
  simp [upperDigits]
@[simp] lemma mem_lowerDigits (l a : ℕ) (ha : a < l) (d : Fin l) :
    d ∈ lowerDigits l a ha ↔ d.val < a := by simp [lowerDigits,Fin.lt_def]
@[simp] lemma mem_upperDigits (l b : ℕ) (hb : b < l) (d : Fin l) :
    d ∈ upperDigits l b hb ↔ b ≤ d.val := by simp [upperDigits,Fin.le_def]

def rectangle (l a b : ℕ) (ha : a < l) (hp : 0 < a) (hb : b < l) :
    Measure (Fin l × Fin l) :=
  (uniformOn (lowerDigits l a ha) (lowerDigits_nonempty l a ha hp)).prod
    (uniformOn (upperDigits l b hb) (upperDigits_nonempty l b hb))
instance rectangle_probability (l a b : ℕ) (ha : a < l) (hp : 0 < a) (hb : b < l) :
    IsProbabilityMeasure (rectangle l a b ha hp hb) := by unfold rectangle; infer_instance

lemma rectangle_fst_singleton (l a b : ℕ) (ha : a < l) (hp : 0 < a) (hb : b < l) (d : Fin l) :
    rectangle l a b ha hp hb (Prod.fst ⁻¹' {d}) = if d.val < a then (a : ℝ≥0∞)⁻¹ else 0 := by
  simp [rectangle,prod_fiber_fst,uniformOn_singleton]
lemma rectangle_snd_singleton (l a b : ℕ) (ha : a < l) (hp : 0 < a) (hb : b < l) (d : Fin l) :
    rectangle l a b ha hp hb (Prod.snd ⁻¹' {d}) = if b ≤ d.val then ((l-b : ℕ) : ℝ≥0∞)⁻¹ else 0 := by
  simp [rectangle,prod_fiber_snd,uniformOn_singleton]

lemma uniformOn_ae_mem {D : Type uD} [MeasurableSpace D] [MeasurableSingletonClass D]
    (S : Finset D) (hs : S.Nonempty) : ∀ᵐ d ∂uniformOn S hs, d ∈ S := by
  apply ae_iff.mpr
  change (uniformOn S hs) (↑S)ᶜ = 0
  rw [uniformOn,(PMF.uniformOfFinset S hs).toMeasure_apply_eq_zero_iff (S.measurableSet.compl),
    PMF.support_uniformOfFinset]
  exact disjoint_compl_right

lemma rectangle_ae (l a b : ℕ) (ha : a < l) (hp : 0 < a) (hb : b < l) :
    ∀ᵐ z ∂rectangle l a b ha hp hb, z.1.val < a ∧ b ≤ z.2.val := by
  have hx := uniformOn_ae_mem (lowerDigits l a ha) (lowerDigits_nonempty l a ha hp)
  have hy := uniformOn_ae_mem (upperDigits l b hb) (upperDigits_nonempty l b hb)
  unfold rectangle
  apply (Measure.ae_prod_iff_ae_ae (by measurability)).mpr
  filter_upwards [hx] with x hxx
  filter_upwards [hy] with y hyy
  exact ⟨(mem_lowerDigits _ _ _ _).mp hxx,(mem_upperDigits _ _ _ _).mp hyy⟩

def diagonal (l : ℕ) [NeZero l] : Measure (Fin l × Fin l) :=
  Measure.map (fun d => (d,d)) (PMF.uniformOfFintype (Fin l)).toMeasure
instance diagonal_probability (l : ℕ) [NeZero l] : IsProbabilityMeasure (diagonal l) := by
  unfold diagonal
  exact Measure.isProbabilityMeasure_map (by fun_prop : Measurable (fun d : Fin l => (d,d))).aemeasurable

lemma diagonal_fiber_fst (l : ℕ) [NeZero l] (d : Fin l) :
    diagonal l (Prod.fst ⁻¹' {d}) = (l : ℝ≥0∞)⁻¹ := by
  rw [diagonal,Measure.map_apply (by fun_prop) (measurable_fst (measurableSet_singleton d))]
  change (PMF.uniformOfFintype (Fin l)).toMeasure {d} = _
  simp [PMF.uniformOfFintype_apply]
lemma diagonal_fiber_snd (l : ℕ) [NeZero l] (d : Fin l) :
    diagonal l (Prod.snd ⁻¹' {d}) = (l : ℝ≥0∞)⁻¹ := by
  rw [diagonal,Measure.map_apply (by fun_prop) (measurable_snd (measurableSet_singleton d))]
  change (PMF.uniformOfFintype (Fin l)).toMeasure {d} = _
  simp [PMF.uniformOfFintype_apply]

def components (l t u r : ℕ) (ht : 0<t ∧ t<l) (hu : 0<u ∧ u<l) (hr : 0<r ∧ r<l) :
    Fin 5 → Measure (Fin l × Fin l) :=
  ![rectangle l (l-t) (l-t) (by omega) (by omega) (by omega),
    rectangle l t t ht.2 ht.1 ht.2,
    rectangle l (l-u) (l-u) (by omega) (by omega) (by omega),
    rectangle l u u hu.2 hu.1 hu.2,
    rectangle l r (l-r) hr.2 hr.1 (by omega)]
instance components_probability (l t u r : ℕ) (ht : 0<t ∧ t<l) (hu : 0<u ∧ u<l)
    (hr : 0<r ∧ r<l) (i : Fin 5) : IsProbabilityMeasure (components l t u r ht hu hr i) := by
  fin_cases i <;> dsimp [components] <;> infer_instance

def sixWeights (p q τ : ℝ≥0∞) : Fin 5 → ℝ≥0∞ := ![p,p,q,q,τ]
lemma sum_sixWeights (p q τ : ℝ≥0∞) : ∑ a, sixWeights p q τ a = 2*p+2*q+τ := by
  simp [sixWeights,Fin.sum_univ_succ]
  ring

def sixLaw (l t u r : ℕ) [NeZero l] (ht : 0<t ∧ t<l) (hu : 0<u ∧ u<l)
    (hr : 0<r ∧ r<l) (p q τ : ℝ≥0∞) : Measure (Option (Fin 5) × (Fin l × Fin l)) :=
  mixture (sixWeights p q τ) (1-(2*p+2*q+τ)) (diagonal l) (components l t u r ht hu hr)

lemma sixLaw_probability (l t u r : ℕ) [NeZero l] (ht : 0<t ∧ t<l) (hu : 0<u ∧ u<l)
    (hr : 0<r ∧ r<l) (p q τ : ℝ≥0∞) (hp : 2*p+2*q+τ ≤ 1) :
    IsProbabilityMeasure (sixLaw l t u r ht hu hr p q τ) := by
  apply mixture_probability
  rw [sum_sixWeights,tsub_add_cancel_of_le hp]

lemma sixLaw_top_t (l t u r : ℕ) [NeZero l] (ht : 0<t ∧ t<l) (hu : 0<u ∧ u<l)
    (hr : 0<r ∧ r<l) (p q τ : ℝ≥0∞) (d : Fin l) (hd : d.val < l-t) :
    sixLaw l t u r ht hu hr p q τ {ω | ω.2.1 = d ∧ ω.1 = some (0 : Fin 5)} =
      p * ((l-t : ℕ) : ℝ≥0∞)⁻¹ := by
  rw [sixLaw,mixture_fiber_label _ _ _ _ Prod.fst measurable_fst]
  simp [sixWeights,components,rectangle_fst_singleton,hd]

lemma sixLaw_bottom_t (l t u r : ℕ) [NeZero l] (ht : 0<t ∧ t<l) (hu : 0<u ∧ u<l)
    (hr : 0<r ∧ r<l) (p q τ : ℝ≥0∞) (d : Fin l) (hd : t ≤ d.val) :
    sixLaw l t u r ht hu hr p q τ {ω | ω.2.2 = d ∧ ω.1 = some (1 : Fin 5)} =
      p * ((l-t : ℕ) : ℝ≥0∞)⁻¹ := by
  rw [sixLaw,mixture_fiber_label _ _ _ _ Prod.snd measurable_snd]
  simp [sixWeights,components,rectangle_snd_singleton,hd]

lemma sixLaw_top_u (l t u r : ℕ) [NeZero l] (ht : 0<t ∧ t<l) (hu : 0<u ∧ u<l)
    (hr : 0<r ∧ r<l) (p q τ : ℝ≥0∞) (d : Fin l) (hd : d.val < l-u) :
    sixLaw l t u r ht hu hr p q τ {ω | ω.2.1 = d ∧ ω.1 = some (2 : Fin 5)} =
      q * ((l-u : ℕ) : ℝ≥0∞)⁻¹ := by
  rw [sixLaw,mixture_fiber_label _ _ _ _ Prod.fst measurable_fst]
  simp [sixWeights,components,rectangle_fst_singleton,hd]

lemma sixLaw_bottom_u (l t u r : ℕ) [NeZero l] (ht : 0<t ∧ t<l) (hu : 0<u ∧ u<l)
    (hr : 0<r ∧ r<l) (p q τ : ℝ≥0∞) (d : Fin l) (hd : u ≤ d.val) :
    sixLaw l t u r ht hu hr p q τ {ω | ω.2.2 = d ∧ ω.1 = some (3 : Fin 5)} =
      q * ((l-u : ℕ) : ℝ≥0∞)⁻¹ := by
  rw [sixLaw,mixture_fiber_label _ _ _ _ Prod.snd measurable_snd]
  simp [sixWeights,components,rectangle_snd_singleton,hd]

end

lemma mixture_fiber_real {κ : Type uκ} {D : Type uD} [Fintype κ] [MeasurableSpace κ] [MeasurableSpace D]
    [MeasurableSingletonClass D]
    (p : κ → ℝ≥0∞) (p₀ : ℝ≥0∞) (μ₀ : Measure (D × D))
    (μ : κ → Measure (D × D)) [IsFiniteMeasure μ₀] [∀ i, IsFiniteMeasure (μ i)]
    (hp : ∀ i, p i ≠ ∞) (hp₀ : p₀ ≠ ∞)
    (f : D × D → D) (hf : Measurable f) (d : D) :
    (mixture p p₀ μ₀ μ).real {ω | f ω.2 = d} =
      p₀.toReal * μ₀.real (f ⁻¹' {d}) + ∑ a, (p a).toReal * (μ a).real (f ⁻¹' {d}) := by
  rw [measureReal_def,mixture_fiber _ _ _ _ f hf]
  rw [ENNReal.toReal_add (ENNReal.mul_ne_top hp₀ (measure_ne_top _ _))
    (ENNReal.sum_ne_top.mpr (fun i _ => ENNReal.mul_ne_top (hp i) (measure_ne_top _ _))),
    ENNReal.toReal_sum (fun i _ => ENNReal.mul_ne_top (hp i) (measure_ne_top _ _))]
  simp [ENNReal.toReal_mul,measureReal_def]

lemma rectangle_fst_real (l a b : ℕ) (ha : a < l) (hp : 0 < a) (hb : b < l) (d : Fin l) :
    (rectangle l a b ha hp hb).real (Prod.fst ⁻¹' {d}) =
      if d.val < a then (a : ℝ)⁻¹ else 0 := by
  rw [measureReal_def,rectangle_fst_singleton]
  split_ifs <;> simp only [ENNReal.toReal_inv, ENNReal.toReal_natCast, ENNReal.toReal_zero]
lemma rectangle_snd_real (l a b : ℕ) (ha : a < l) (hp : 0 < a) (hb : b < l) (d : Fin l) :
    (rectangle l a b ha hp hb).real (Prod.snd ⁻¹' {d}) =
      if b ≤ d.val then ((l-b : ℕ) : ℝ)⁻¹ else 0 := by
  rw [measureReal_def,rectangle_snd_singleton]
  split_ifs <;> simp only [ENNReal.toReal_inv, ENNReal.toReal_natCast, ENNReal.toReal_zero]

lemma sixLaw_fiber_real_le (l t u r : ℕ) [NeZero l] (ht : 0<t ∧ t<l) (hu : 0<u ∧ u<l)
    (hr : 0<r ∧ r<l) (p q τ : ℝ≥0∞) (hp : 2*p+2*q+τ ≤ 1)
    (f : Fin l × Fin l → Fin l) (hf : Measurable f) (d : Fin l)
    (hdiag : (diagonal l).real (f ⁻¹' {d}) = (l : ℝ)⁻¹)
    (M : Fin 5 → ℝ) (hM : ∀ i, (components l t u r ht hu hr i).real (f ⁻¹' {d}) ≤ M i) :
    (sixLaw l t u r ht hu hr p q τ).real {ω | f ω.2 = d} ≤
      (l : ℝ)⁻¹ + ∑ i, (sixWeights p q τ i).toReal * M i := by
  have hweight (i : Fin 5) : sixWeights p q τ i ≤ 1 := by
    apply le_trans (Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ _))
    rwa [sum_sixWeights]
  have hrem : 1-(2*p+2*q+τ) ≤ (1 : ℝ≥0∞) := tsub_le_self
  rw [sixLaw,mixture_fiber_real _ _ _ _
    (fun i => ne_top_of_le_ne_top ENNReal.one_ne_top (hweight i))
    (ne_top_of_le_ne_top ENNReal.one_ne_top hrem) f hf,hdiag]
  apply add_le_add
  · have hrem' : (1-(2*p+2*q+τ)).toReal ≤ 1 := by
      simpa using ENNReal.toReal_mono ENNReal.one_ne_top hrem
    convert mul_le_mul_of_nonneg_right hrem' (by positivity : 0 ≤ (l : ℝ)⁻¹) using 1; ring
  · exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hM i) ENNReal.toReal_nonneg)


end CircleCoupling

end

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_CouplingMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CircleCoupling

universe uD uA uι uΩ

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ComplexInnerProductSpace
open MeasureTheory Filter Set
open Set
open scoped ComplexInnerProductSpace
open Set
open scoped ComplexInnerProductSpace
open MeasureTheory Set Filter Topology
open scoped BigOperators ComplexConjugate
open MeasureTheory Set Filter
open scoped BigOperators ENNReal
open Filter Set
open scoped Topology
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped ENNReal Classical
open Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Topology
open scoped BigOperators
open scoped BigOperators
open Set
open Set
open Set
open Set MeasureTheory Filter
open scoped BigOperators ENNReal Topology Classical
open MeasureTheory Set Filter
open scoped ENNReal Topology
open MeasureTheory Set
open MeasureTheory Filter Set
open scoped Topology BoundedContinuousFunction
open MeasureTheory Set Filter Topology TopologicalSpace
open MeasureTheory Set
open scoped ENNReal BigOperators Classical
open MeasureTheory Set
open scoped BigOperators ENNReal Classical
section


def digitEndpoint {D : Type uD} (e : Bool) (z : D × D) : D := if e then z.2 else z.1
lemma digitEndpoint_measurable {D : Type uD} [MeasurableSpace D] (e : Bool) :
    Measurable (digitEndpoint (D := D) e) := by
  cases e
  · exact measurable_fst
  · exact measurable_snd

lemma diagonal_endpoint_real (l : ℕ) [NeZero l] (e : Bool) (d : Fin l) :
    (diagonal l).real (digitEndpoint e ⁻¹' {d}) = (l : ℝ)⁻¹ := by
  cases e
  · change ((diagonal l) (Prod.fst ⁻¹' {d})).toReal = _
    rw [diagonal_fiber_fst]; simp
  · change ((diagonal l) (Prod.snd ⁻¹' {d})).toReal = _
    rw [diagonal_fiber_snd]; simp

lemma rectangle_endpoint_density_bound (l a b : ℕ) (ha : a < l) (hp : 0 < a) (hb : b < l)
    (e : Bool) (M : ℝ) (hM : 0 ≤ M)
    (hA : (l : ℝ) * (a : ℝ)⁻¹ ≤ M) (hB : (l : ℝ) * ((l-b : ℕ) : ℝ)⁻¹ ≤ M)
    (d : Fin l) : (l : ℝ) * (rectangle l a b ha hp hb).real (digitEndpoint e ⁻¹' {d}) ≤ M := by
  cases e
  · change (l : ℝ) * (rectangle l a b ha hp hb).real (Prod.fst ⁻¹' {d}) ≤ M
    rw [rectangle_fst_real]
    split_ifs <;> simp_all
  · change (l : ℝ) * (rectangle l a b ha hp hb).real (Prod.snd ⁻¹' {d}) ≤ M
    rw [rectangle_snd_real]
    split_ifs <;> simp_all

lemma sixComponents_density_bound (l t u r : ℕ) [NeZero l]
    (ht : 0 < t ∧ t < l) (hu : 0 < u ∧ u < l) (hr : 0 < r ∧ r < l)
    (a b m : ℝ) (ha : 0 < a) (hb : 0 < b) (hm : 0 < m)
    (htlo : (l : ℝ)*a/3 ≤ (t : ℝ)) (hthi : (t : ℝ) ≤ (l : ℝ)/2)
    (hulo : (l : ℝ)*b/3 ≤ (u : ℝ)) (huhi : (u : ℝ) ≤ (l : ℝ)/2)
    (hrlo : (l : ℝ)/(2*m) ≤ (r : ℝ)) (_hrhi : (r : ℝ) ≤ (l : ℝ)/2)
    (e : Bool) : ∀ i d, (l : ℝ) * (components l t u r ht hu hr i).real
      (digitEndpoint e ⁻¹' {d}) ≤ (![3/a,3/a,3/b,3/b,2*m] : Fin 5 → ℝ) i := by
  have bound (n : ℕ) (hn : 0 < n) (w : ℝ) (hw : 0 < w) (hnw : (l : ℝ)*w/3 ≤ n) :
      (l : ℝ)*(n : ℝ)⁻¹ ≤ 3/w := by
    rw [← div_eq_mul_inv,div_le_div_iff₀ (by exact_mod_cast hn) hw]
    linarith
  have ht1 := bound t ht.1 a ha htlo
  have hu1 := bound u hu.1 b hb hulo
  have ht2 := bound (l-t) (by omega) a ha (by rw [Nat.cast_sub ht.2.le]; linarith)
  have hu2 := bound (l-u) (by omega) b hb (by rw [Nat.cast_sub hu.2.le]; linarith)
  have hr1 : (l : ℝ)*(r : ℝ)⁻¹ ≤ 2*m := by
    rw [← div_eq_mul_inv,div_le_iff₀ (by exact_mod_cast hr.1)]
    have hh := (div_le_iff₀ (by positivity : 0 < 2*m)).mp hrlo
    nlinarith
  intro i d
  fin_cases i
  all_goals dsimp [components]
  · exact rectangle_endpoint_density_bound l (l-t) (l-t) (by omega) (by omega) (by omega) e
      (3/a) (by positivity) ht2 (by simpa [Nat.sub_sub_self ht.2.le] using ht1) d
  · exact rectangle_endpoint_density_bound l t t ht.2 ht.1 ht.2 e (3/a) (by positivity) ht1 ht2 d
  · exact rectangle_endpoint_density_bound l (l-u) (l-u) (by omega) (by omega) (by omega) e
      (3/b) (by positivity) hu2 (by simpa [Nat.sub_sub_self hu.2.le] using hu1) d
  · exact rectangle_endpoint_density_bound l u u hu.2 hu.1 hu.2 e (3/b) (by positivity) hu1 hu2 d
  · exact rectangle_endpoint_density_bound l r (l-r) hr.2 hr.1 (by omega) e (2*m) (by positivity)
      hr1 (by simpa [Nat.sub_sub_self hr.2.le] using hr1) d

end
open MeasureTheory Set
open scoped ENNReal
section

lemma fiber_failure_bound {Ω : Type uΩ} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (F S : Set Ω) (hS : MeasurableSet S)
    (c : ℝ) (_hc : 0 ≤ c) (hc' : c ≤ 1)
    (hhit : c * μ.real F ≤ μ.real (F ∩ S)) :
    μ (F ∩ Sᶜ) ≤ ENNReal.ofReal (1-c) * μ F := by
  apply (ENNReal.toReal_le_toReal (measure_ne_top _ _)
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))).mp
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sub_nonneg.mpr hc')]
  change μ.real (F ∩ Sᶜ) ≤ (1-c) * μ.real F
  have hsum := measureReal_sdiff_add_inter (μ := μ) (s := F) hS
  rw [sdiff_eq] at hsum
  nlinarith

lemma fiber_failure_of_density_bounds {Ω : Type uΩ} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (F S : Set Ω) (hS : MeasurableSet S)
    (r B : ℝ) (hr : 0 ≤ r) (hB : 0 < B) (hrB : r ≤ B)
    (htotal : μ.real F ≤ B) (hhit : r ≤ μ.real (F ∩ S)) :
    μ (F ∩ Sᶜ) ≤ ENNReal.ofReal (1-r/B) * μ F := by
  apply fiber_failure_bound μ F S hS (r/B) (div_nonneg hr hB.le)
    ((div_le_one hB).mpr hrB)
  exact (mul_le_mul_of_nonneg_left htotal (div_nonneg hr hB.le)).trans
    (by simpa [div_mul_cancel₀ _ hB.ne'] using hhit)

lemma fiber_failure_tenth {Ω : Type uΩ} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (F S : Set Ω) (hS : MeasurableSet S)
    (ρ l : ℝ) (hρ : 0 ≤ ρ) (hρ' : ρ ≤ 1) (hl : 0 < l)
    (htotal : μ.real F ≤ 10/l) (hhit : ρ/l ≤ μ.real (F ∩ S)) :
    μ (F ∩ Sᶜ) ≤ ENNReal.ofReal (1-ρ/10) * μ F := by
  have h := fiber_failure_of_density_bounds μ F S hS (ρ/l) (10/l)
    (div_nonneg hρ hl.le) (div_pos (by norm_num) hl)
    (div_le_div_of_nonneg_right (by linarith : ρ ≤ 10) hl.le) htotal hhit
  simpa [div_div_div_cancel_right₀ hl.ne'] using h
end

lemma sixLaw_density_ten (l t u r : ℕ) [NeZero l]
    (ht : 0 < t ∧ t < l) (hu : 0 < u ∧ u < l) (hr : 0 < r ∧ r < l)
    (a b m κ ρ σ τ : ℝ) (ha : 0 < a) (hb : 0 < b) (hm : 0 < m)
    (hκ : κ ≤ 1/100) (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) (hτ : 0 ≤ τ)
    (htlo : (l : ℝ)*a/3 ≤ (t : ℝ)) (hthi : (t : ℝ) ≤ (l : ℝ)/2)
    (hulo : (l : ℝ)*b/3 ≤ (u : ℝ)) (huhi : (u : ℝ) ≤ (l : ℝ)/2)
    (hrlo : (l : ℝ)/(2*m) ≤ (r : ℝ)) (hrhi : (r : ℝ) ≤ (l : ℝ)/2)
    (hρα : ρ/a ≤ κ) (hσb : σ/b ≤ κ) (hτm : τ ≤ 1/m)
    (hprob : 2*ENNReal.ofReal ρ+2*ENNReal.ofReal σ+ENNReal.ofReal τ ≤ 1)
    (e : Bool) (d : Fin l) :
    (sixLaw l t u r ht hu hr (ENNReal.ofReal ρ) (ENNReal.ofReal σ) (ENNReal.ofReal τ)).real
      {ω | digitEndpoint e ω.2 = d} ≤ 10/l := by
  have hl : (0 : ℝ) < l := Nat.cast_pos.mpr (NeZero.pos l)
  let M : Fin 5 → ℝ := ![3/a,3/a,3/b,3/b,2*m]
  have hM := sixComponents_density_bound l t u r ht hu hr a b m ha hb hm
    htlo hthi hulo huhi hrlo hrhi e
  have hh := sixLaw_fiber_real_le l t u r ht hu hr (ENNReal.ofReal ρ) (ENNReal.ofReal σ)
    (ENNReal.ofReal τ) hprob (digitEndpoint e) (digitEndpoint_measurable e) d
    (diagonal_endpoint_real l e d) (fun i => M i/l)
    (fun i => by apply (le_div_iff₀ hl).mpr; simpa [mul_comm,M] using hM i d)
  apply hh.trans
  simp only [M,sixWeights,Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,
    Fin.sum_univ_zero,add_zero,ENNReal.toReal_ofReal hρ,
    ENNReal.toReal_ofReal hσ,ENNReal.toReal_ofReal hτ]
  have hτ' : τ*m ≤ 1 := by have := (le_div_iff₀ hm).mp hτm; nlinarith
  have hsum : 1 + 6*(ρ/a)+6*(σ/b)+2*(τ*m) ≤ 10 := by linarith
  calc
    _ = (1+6*(ρ/a)+6*(σ/b)+2*(τ*m))/l := by ring
    _ ≤ _ := div_le_div_of_nonneg_right hsum hl.le

lemma sixLaw_top_t_failure (l t u r : ℕ) [NeZero l]
    (ht : 0<t ∧ t<l) (hu : 0<u ∧ u<l) (hr : 0<r ∧ r<l)
    (ρ σ τ : ℝ) (hρ : 0 ≤ ρ) (hρ' : ρ ≤ 1)
    (hp : 2*ENNReal.ofReal ρ+2*ENNReal.ofReal σ+ENNReal.ofReal τ ≤ 1)
    (d : Fin l) (hd : d.val < l-t)
    (hbound : (sixLaw l t u r ht hu hr (ENNReal.ofReal ρ) (ENNReal.ofReal σ) (ENNReal.ofReal τ)).real
      {ω | ω.2.1 = d} ≤ 10/l) :
    sixLaw l t u r ht hu hr (ENNReal.ofReal ρ) (ENNReal.ofReal σ) (ENNReal.ofReal τ)
      ({ω | ω.2.1=d} ∩ {ω | ω.1=some (0 : Fin 5)}ᶜ) ≤ ENNReal.ofReal (1-ρ/10) *
    sixLaw l t u r ht hu hr (ENNReal.ofReal ρ) (ENNReal.ofReal σ) (ENNReal.ofReal τ) {ω | ω.2.1=d} := by
  let μ := sixLaw l t u r ht hu hr (ENNReal.ofReal ρ) (ENNReal.ofReal σ) (ENNReal.ofReal τ)
  let : IsProbabilityMeasure μ := sixLaw_probability l t u r ht hu hr _ _ _ hp
  apply fiber_failure_tenth μ _ _ (by measurability) ρ l hρ hρ' (by exact_mod_cast NeZero.pos l) hbound
  change ρ/(l : ℝ) ≤ (μ {ω | ω.2.1=d ∧ ω.1=some (0 : Fin 5)}).toReal
  rw [show μ {ω | ω.2.1=d ∧ ω.1=some (0 : Fin 5)} =
    ENNReal.ofReal ρ * ((l-t : ℕ) : ℝ≥0∞)⁻¹ from sixLaw_top_t l t u r ht hu hr _ _ _ d hd]
  simp only [ENNReal.toReal_mul,ENNReal.toReal_ofReal hρ,ENNReal.toReal_inv,ENNReal.toReal_natCast]
  rw [← div_eq_mul_inv]
  apply div_le_div_of_nonneg_left hρ (by exact_mod_cast Nat.sub_pos_of_lt ht.2)
  exact_mod_cast Nat.sub_le l t

lemma sixLaw_bottom_t_failure (l t u r : ℕ) [NeZero l]
    (ht : 0<t ∧ t<l) (hu : 0<u ∧ u<l) (hr : 0<r ∧ r<l)
    (ρ σ τ : ℝ) (hρ : 0 ≤ ρ) (hρ' : ρ ≤ 1)
    (hp : 2*ENNReal.ofReal ρ+2*ENNReal.ofReal σ+ENNReal.ofReal τ ≤ 1)
    (d : Fin l) (hd : t ≤ d.val)
    (hbound : (sixLaw l t u r ht hu hr (ENNReal.ofReal ρ) (ENNReal.ofReal σ) (ENNReal.ofReal τ)).real
      {ω | ω.2.2 = d} ≤ 10/l) :
    sixLaw l t u r ht hu hr (ENNReal.ofReal ρ) (ENNReal.ofReal σ) (ENNReal.ofReal τ)
      ({ω | ω.2.2=d} ∩ {ω | ω.1=some (1 : Fin 5)}ᶜ) ≤ ENNReal.ofReal (1-ρ/10) *
    sixLaw l t u r ht hu hr (ENNReal.ofReal ρ) (ENNReal.ofReal σ) (ENNReal.ofReal τ) {ω | ω.2.2=d} := by
  let μ := sixLaw l t u r ht hu hr (ENNReal.ofReal ρ) (ENNReal.ofReal σ) (ENNReal.ofReal τ)
  let : IsProbabilityMeasure μ := sixLaw_probability l t u r ht hu hr _ _ _ hp
  apply fiber_failure_tenth μ _ _ (by measurability) ρ l hρ hρ' (by exact_mod_cast NeZero.pos l) hbound
  change ρ/(l : ℝ) ≤ (μ {ω | ω.2.2=d ∧ ω.1=some (1 : Fin 5)}).toReal
  rw [show μ {ω | ω.2.2=d ∧ ω.1=some (1 : Fin 5)} =
    ENNReal.ofReal ρ * ((l-t : ℕ) : ℝ≥0∞)⁻¹ from sixLaw_bottom_t l t u r ht hu hr _ _ _ d hd]
  simp only [ENNReal.toReal_mul,ENNReal.toReal_ofReal hρ,ENNReal.toReal_inv,ENNReal.toReal_natCast]
  rw [← div_eq_mul_inv]
  apply div_le_div_of_nonneg_left hρ (by exact_mod_cast Nat.sub_pos_of_lt ht.2)
  exact_mod_cast Nat.sub_le l t

lemma sixLaw_top_u_failure (l t u r : ℕ) [NeZero l]
    (ht : 0<t ∧ t<l) (hu : 0<u ∧ u<l) (hr : 0<r ∧ r<l)
    (ρ σ τ : ℝ) (hσ : 0 ≤ σ) (hσ' : σ ≤ 1)
    (hp : 2*ENNReal.ofReal ρ+2*ENNReal.ofReal σ+ENNReal.ofReal τ ≤ 1)
    (d : Fin l) (hd : d.val < l-u)
    (hbound : (sixLaw l t u r ht hu hr (ENNReal.ofReal ρ) (ENNReal.ofReal σ) (ENNReal.ofReal τ)).real
      {ω | ω.2.1 = d} ≤ 10/l) :
    sixLaw l t u r ht hu hr (ENNReal.ofReal ρ) (ENNReal.ofReal σ) (ENNReal.ofReal τ)
      ({ω | ω.2.1=d} ∩ {ω | ω.1=some (2 : Fin 5)}ᶜ) ≤ ENNReal.ofReal (1-σ/10) *
    sixLaw l t u r ht hu hr (ENNReal.ofReal ρ) (ENNReal.ofReal σ) (ENNReal.ofReal τ) {ω | ω.2.1=d} := by
  let μ := sixLaw l t u r ht hu hr (ENNReal.ofReal ρ) (ENNReal.ofReal σ) (ENNReal.ofReal τ)
  let : IsProbabilityMeasure μ := sixLaw_probability l t u r ht hu hr _ _ _ hp
  apply fiber_failure_tenth μ _ _ (by measurability) σ l hσ hσ' (by exact_mod_cast NeZero.pos l) hbound
  change σ/(l : ℝ) ≤ (μ {ω | ω.2.1=d ∧ ω.1=some (2 : Fin 5)}).toReal
  rw [show μ {ω | ω.2.1=d ∧ ω.1=some (2 : Fin 5)} =
    ENNReal.ofReal σ * ((l-u : ℕ) : ℝ≥0∞)⁻¹ from sixLaw_top_u l t u r ht hu hr _ _ _ d hd]
  simp only [ENNReal.toReal_mul,ENNReal.toReal_ofReal hσ,ENNReal.toReal_inv,ENNReal.toReal_natCast]
  rw [← div_eq_mul_inv]
  apply div_le_div_of_nonneg_left hσ (by exact_mod_cast Nat.sub_pos_of_lt hu.2)
  exact_mod_cast Nat.sub_le l u

lemma sixLaw_bottom_u_failure (l t u r : ℕ) [NeZero l]
    (ht : 0<t ∧ t<l) (hu : 0<u ∧ u<l) (hr : 0<r ∧ r<l)
    (ρ σ τ : ℝ) (hσ : 0 ≤ σ) (hσ' : σ ≤ 1)
    (hp : 2*ENNReal.ofReal ρ+2*ENNReal.ofReal σ+ENNReal.ofReal τ ≤ 1)
    (d : Fin l) (hd : u ≤ d.val)
    (hbound : (sixLaw l t u r ht hu hr (ENNReal.ofReal ρ) (ENNReal.ofReal σ) (ENNReal.ofReal τ)).real
      {ω | ω.2.2 = d} ≤ 10/l) :
    sixLaw l t u r ht hu hr (ENNReal.ofReal ρ) (ENNReal.ofReal σ) (ENNReal.ofReal τ)
      ({ω | ω.2.2=d} ∩ {ω | ω.1=some (3 : Fin 5)}ᶜ) ≤ ENNReal.ofReal (1-σ/10) *
    sixLaw l t u r ht hu hr (ENNReal.ofReal ρ) (ENNReal.ofReal σ) (ENNReal.ofReal τ) {ω | ω.2.2=d} := by
  let μ := sixLaw l t u r ht hu hr (ENNReal.ofReal ρ) (ENNReal.ofReal σ) (ENNReal.ofReal τ)
  let : IsProbabilityMeasure μ := sixLaw_probability l t u r ht hu hr _ _ _ hp
  apply fiber_failure_tenth μ _ _ (by measurability) σ l hσ hσ' (by exact_mod_cast NeZero.pos l) hbound
  change σ/(l : ℝ) ≤ (μ {ω | ω.2.2=d ∧ ω.1=some (3 : Fin 5)}).toReal
  rw [show μ {ω | ω.2.2=d ∧ ω.1=some (3 : Fin 5)} =
    ENNReal.ofReal σ * ((l-u : ℕ) : ℝ≥0∞)⁻¹ from sixLaw_bottom_u l t u r ht hu hr _ _ _ d hd]
  simp only [ENNReal.toReal_mul,ENNReal.toReal_ofReal hσ,ENNReal.toReal_inv,ENNReal.toReal_natCast]
  rw [← div_eq_mul_inv]
  apply div_le_div_of_nonneg_left hσ (by exact_mod_cast Nat.sub_pos_of_lt hu.2)
  exact_mod_cast Nat.sub_le l u



end CircleCoupling

end

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_CoordinateLaws
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

universe uκ uD

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ComplexInnerProductSpace
open MeasureTheory Filter Set
open Set
open scoped ComplexInnerProductSpace
open Set
open scoped ComplexInnerProductSpace
open MeasureTheory Set Filter Topology
open scoped BigOperators ComplexConjugate
open MeasureTheory Set Filter
open scoped BigOperators ENNReal
open Filter Set
open scoped Topology
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped ENNReal Classical
open Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Topology
open scoped BigOperators
open scoped BigOperators
open Set
open Set
open Set
open Set MeasureTheory Filter
open scoped BigOperators ENNReal Topology Classical
open MeasureTheory Set Filter
open scoped ENNReal Topology
open MeasureTheory Set
open MeasureTheory Filter Set
open scoped Topology BoundedContinuousFunction
open MeasureTheory Set Filter Topology TopologicalSpace
open MeasureTheory Set
open scoped ENNReal BigOperators Classical
open MeasureTheory Set
open scoped BigOperators ENNReal Classical
open MeasureTheory Set
open scoped ENNReal
open MeasureTheory Set
open scoped ENNReal NNReal
namespace CircleCoupling

def roundedWidth (l : ℕ) (w : ℝ) : ℕ := ⌊w*l/2⌋₊
def roundedTag (l : ℕ) (m : ℝ) : ℕ := ⌊(l : ℝ)/m⌋₊
def crossingProbability (κ w m : ℝ) : ℝ := κ*Real.sqrt (w/m)

lemma width_rounding (l : ℕ) (m w : ℝ) (hm : 200 ≤ m)
    (hl : 100*m ≤ l) (hwlo : 1/m ≤ w) (hwhi : w ≤ 1/4) :
    0 < roundedWidth l w ∧ roundedWidth l w < l ∧
      (l:ℝ)*w/3 ≤ roundedWidth l w ∧ (roundedWidth l w:ℝ) ≤ (l:ℝ)*w/2 := by
  have hm0 : 0 < m := by linarith
  have hl0 : (0:ℝ) < l := by linarith
  have hw0 : 0 < w := lt_of_lt_of_le (by positivity) hwlo
  have hwl : 100 ≤ w*l := by
    have hh := mul_le_mul_of_nonneg_left hl hw0.le
    have hh' : 1 ≤ w*m := (div_le_iff₀ hm0).mp hwlo
    nlinarith
  have hfloor := Nat.floor_le (show 0 ≤ w*l/2 by positivity)
  have hlow := Nat.lt_floor_add_one (w*l/2)
  change (roundedWidth l w : ℝ)  ≤  w*l/2 at hfloor
  change w*l/2  <  (roundedWidth l w : ℝ)+1 at hlow
  have hthird : (l:ℝ)*w/3 ≤ roundedWidth l w := by nlinarith
  refine ⟨?_,?_,hthird,by nlinarith⟩
  · have : (0:ℝ) < roundedWidth l w := lt_of_lt_of_le (by positivity) hthird
    exact_mod_cast this
  · have : (roundedWidth l w:ℝ) < l := by nlinarith
    exact_mod_cast this

lemma tag_rounding (l : ℕ) (m : ℝ) (hm : 200 ≤ m) (hl : 100*m ≤ l) :
    0 < roundedTag l m ∧ roundedTag l m < l ∧
      (l:ℝ)/(2*m) ≤ roundedTag l m ∧ (roundedTag l m:ℝ) ≤ (l:ℝ)/m := by
  have hm0 : 0 < m := by linarith
  have hl0 : (0:ℝ) < l := by linarith
  have hdiv : 100 ≤ (l:ℝ)/m := (le_div_iff₀ hm0).mpr hl
  have hfloor := Nat.floor_le (show 0 ≤ (l:ℝ)/m by positivity)
  have hlow := Nat.lt_floor_add_one ((l:ℝ)/m)
  change (roundedTag l m : ℝ)  ≤  (l:ℝ)/m at hfloor
  change (l:ℝ)/m  <  (roundedTag l m : ℝ)+1 at hlow
  have hhalf : (l:ℝ)/(2*m) = ((l:ℝ)/m)/2 := by ring
  refine ⟨?_,?_,?_,hfloor⟩
  · have : (0:ℝ) < roundedTag l m := by linarith
    exact_mod_cast this
  · have hlt : (l:ℝ)/m  <  l := (div_lt_iff₀ hm0).mpr (by nlinarith)
    exact_mod_cast hfloor.trans_lt hlt
  · rw [hhalf]; linarith

lemma crossingProbability_nonneg {κ w m : ℝ} (hκ : 0 ≤ κ) :
    0 ≤ crossingProbability κ w m := mul_nonneg hκ (Real.sqrt_nonneg _)

lemma crossingProbability_div_le {κ w m : ℝ} (hκ : 0 ≤ κ) (hm : 0 < m) (hw : 1/m ≤ w) :
    crossingProbability κ w m/w ≤ κ := by
  have hw0 : 0 < w := lt_of_lt_of_le (by positivity) hw
  have hwm : 1 ≤ w*m := (div_le_iff₀ hm).mp hw
  have hroot : Real.sqrt (w/m) ≤ w := by
    apply (Real.sqrt_le_left hw0.le).mpr
    apply (div_le_iff₀ hm).mpr
    nlinarith [mul_le_mul_of_nonneg_left hwm hw0.le]
  apply (div_le_iff₀ hw0).mpr
  exact mul_le_mul_of_nonneg_left hroot hκ

lemma crossingProbability_le_kappa {κ w m : ℝ} (hκ : 0 ≤ κ) (hm : 1 ≤ m) (hw : w ≤ 1) :
    crossingProbability κ w m ≤ κ := by
  have hm0 : 0 < m := by linarith
  have hr : Real.sqrt (w/m) ≤ 1 := (Real.sqrt_le_one).mpr ((div_le_one hm0).mpr (hw.trans hm))
  simpa [crossingProbability] using mul_le_mul_of_nonneg_left hr hκ

lemma six_probabilities_le_one (κ a b m : ℝ) (hκ0 : 0 ≤ κ) (hκ : κ ≤ 1/100)
    (hm : 200 ≤ m) (ha : a ≤ 1/4) (hb : b ≤ 1/4)
    (τ : ℝ) (hτ0 : 0 ≤ τ) (hτ : τ ≤ 1/m) :
    2*ENNReal.ofReal (crossingProbability κ a m)+
      2*ENNReal.ofReal (crossingProbability κ b m)+ENNReal.ofReal τ ≤ 1 := by
  have hhρ := crossingProbability_le_kappa hκ0 (by linarith : 1 ≤ m) (by linarith : a ≤ 1)
  have hhσ := crossingProbability_le_kappa hκ0 (by linarith : 1 ≤ m) (by linarith : b ≤ 1)
  have hτ' : τ ≤ 1/200 := hτ.trans ((div_le_div_iff_of_pos_left (by norm_num) (by linarith) (by norm_num)).mpr hm)
  have hρ0 := crossingProbability_nonneg (w := a) (m := m) hκ0
  have hσ0 := crossingProbability_nonneg (w := b) (m := m) hκ0
  rw [← ENNReal.ofReal_ofNat 2,← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_mul (by norm_num),← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) hτ0]
  exact ENNReal.ofReal_le_one.mpr (by linarith)

structure CoordinateParameters where
  l : ℕ
  m : ℕ
  κ : ℝ
  a : ℝ
  b : ℝ
  hm : 200 ≤ m
  hl : 100*m ≤ l
  hκ0 : 0 ≤ κ
  hκ : κ ≤ 1/100
  ha : 1/(m:ℝ) ≤ a ∧ a ≤ 1/4
  hb : 1/(m:ℝ) ≤ b ∧ b ≤ 1/4
namespace CoordinateParameters
variable (P : CoordinateParameters)
instance instNeZeroNatL : NeZero P.l := ⟨by have := P.hm; have := P.hl; omega⟩
lemma m_pos : (0:ℝ)<P.m := by exact_mod_cast lt_of_lt_of_le (by norm_num : 0<200) P.hm
lemma a_pos : 0<P.a := lt_of_lt_of_le (by have := P.m_pos; positivity) P.ha.1
lemma b_pos : 0<P.b := lt_of_lt_of_le (by have := P.m_pos; positivity) P.hb.1
lemma width_a : 0 < roundedWidth P.l P.a ∧ roundedWidth P.l P.a < P.l ∧
    (P.l:ℝ)*P.a/3 ≤ roundedWidth P.l P.a ∧ (roundedWidth P.l P.a:ℝ) ≤ (P.l:ℝ)*P.a/2 := width_rounding P.l P.m P.a (by exact_mod_cast P.hm) (by exact_mod_cast P.hl) P.ha.1 P.ha.2
lemma width_b : 0 < roundedWidth P.l P.b ∧ roundedWidth P.l P.b < P.l ∧
    (P.l:ℝ)*P.b/3 ≤ roundedWidth P.l P.b ∧ (roundedWidth P.l P.b:ℝ) ≤ (P.l:ℝ)*P.b/2 := width_rounding P.l P.m P.b (by exact_mod_cast P.hm) (by exact_mod_cast P.hl) P.hb.1 P.hb.2
lemma tag_bounds : 0 < roundedTag P.l P.m ∧ roundedTag P.l P.m < P.l ∧
    (P.l:ℝ)/(2*P.m) ≤ roundedTag P.l P.m ∧ (roundedTag P.l P.m:ℝ) ≤ (P.l:ℝ)/P.m := tag_rounding P.l P.m (by exact_mod_cast P.hm) (by exact_mod_cast P.hl)
def ρ : ℝ := crossingProbability P.κ P.a P.m
def σ : ℝ := crossingProbability P.κ P.b P.m
def τ (tagged : Bool) : ℝ := if tagged then 1/(P.m:ℝ) else 0
lemma ρ_nonneg : 0 ≤ P.ρ := crossingProbability_nonneg P.hκ0
lemma σ_nonneg : 0 ≤ P.σ := crossingProbability_nonneg P.hκ0
lemma τ_nonneg (tagged : Bool) : 0 ≤ P.τ tagged := by unfold τ; split <;> positivity
lemma τ_le (tagged : Bool) : P.τ tagged ≤ 1/(P.m:ℝ) := by unfold τ; split <;> first | rfl | positivity
lemma ρ_le_one : P.ρ ≤ 1 := (crossingProbability_le_kappa P.hκ0 (by exact_mod_cast (by have := P.hm; omega : 1≤P.m)) (by linarith [P.ha.2])).trans (by linarith [P.hκ])
lemma σ_le_one : P.σ ≤ 1 := (crossingProbability_le_kappa P.hκ0 (by exact_mod_cast (by have := P.hm; omega : 1≤P.m)) (by linarith [P.hb.2])).trans (by linarith [P.hκ])
lemma probabilities (tagged : Bool) : 2*ENNReal.ofReal P.ρ+2*ENNReal.ofReal P.σ+ENNReal.ofReal (P.τ tagged) ≤ 1 :=
  six_probabilities_le_one P.κ P.a P.b P.m P.hκ0 P.hκ (by exact_mod_cast P.hm) P.ha.2 P.hb.2
    (P.τ tagged) (P.τ_nonneg tagged) (P.τ_le tagged)

abbrev Sample := Option (Fin 5) × (Fin P.l × Fin P.l)
def law (tagged : Bool) : Measure P.Sample :=
  sixLaw P.l (roundedWidth P.l P.a) (roundedWidth P.l P.b) (roundedTag P.l P.m)
    ⟨P.width_a.1,P.width_a.2.1⟩ ⟨P.width_b.1,P.width_b.2.1⟩ ⟨P.tag_bounds.1,P.tag_bounds.2.1⟩
    (ENNReal.ofReal P.ρ) (ENNReal.ofReal P.σ) (ENNReal.ofReal (P.τ tagged))
instance instIsProbabilityMeasureSampleLaw (tagged : Bool) : IsProbabilityMeasure (P.law tagged) :=
  sixLaw_probability _ _ _ _ _ _ _ _ _ _ (P.probabilities tagged)

lemma rounded_width_a_half : (roundedWidth P.l P.a:ℝ) ≤ (P.l:ℝ)/2 := by
  have hl : (0:ℝ) ≤ P.l := Nat.cast_nonneg _
  calc
    _ ≤ (P.l:ℝ)*P.a/2 := P.width_a.2.2.2
    _ ≤ _ := by nlinarith [P.ha.2]
lemma rounded_width_b_half : (roundedWidth P.l P.b:ℝ) ≤ (P.l:ℝ)/2 := by
  have hl : (0:ℝ) ≤ P.l := Nat.cast_nonneg _
  calc
    _ ≤ (P.l:ℝ)*P.b/2 := P.width_b.2.2.2
    _ ≤ _ := by nlinarith [P.hb.2]
lemma rounded_tag_half : (roundedTag P.l P.m:ℝ) ≤ (P.l:ℝ)/2 := by
  apply P.tag_bounds.2.2.2.trans
  exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by norm_num) (by exact_mod_cast (by have := P.hm; omega : 2≤P.m))

lemma law_density_ten (tagged e : Bool) (d : Fin P.l) :
    (P.law tagged).real {ω | digitEndpoint e ω.2=d} ≤ 10/(P.l:ℝ) := by
  apply sixLaw_density_ten _ _ _ _ _ _ _ _ _ _ _ _ _ _ P.a_pos P.b_pos P.m_pos
    P.hκ P.ρ_nonneg P.σ_nonneg (P.τ_nonneg tagged) P.width_a.2.2.1 P.rounded_width_a_half
    P.width_b.2.2.1 P.rounded_width_b_half P.tag_bounds.2.2.1 P.rounded_tag_half
    (crossingProbability_div_le P.hκ0 P.m_pos P.ha.1) (crossingProbability_div_le P.hκ0 P.m_pos P.hb.1)
    (P.τ_le tagged) (P.probabilities tagged)
end CoordinateParameters
lemma ae_labelled {κ : Type uκ} {D : Type uD} [MeasurableSpace κ] [MeasurableSpace D]
    (a : Option κ) (μ : Measure (D × D)) (P : Option κ × (D × D) → Prop)
    (hP : MeasurableSet {z | P z}) (h : ∀ᵐ z ∂μ, P (a,z)) :
    ∀ᵐ z ∂labelled a μ, P z := by
  exact (ae_map_iff (by fun_prop) hP).mpr h

lemma ae_mixture {κ : Type uκ} {D : Type uD} [Fintype κ] [MeasurableSpace κ] [MeasurableSpace D]
    (p : κ → ℝ≥0∞) (p₀ : ℝ≥0∞) (μ₀ : Measure (D × D)) (μ : κ → Measure (D × D))
    (P : Option κ × (D × D) → Prop) (hP : MeasurableSet {z | P z})
    (h₀ : ∀ᵐ z ∂μ₀, P (none,z)) (h : ∀ a, ∀ᵐ z ∂μ a, P (some a,z)) :
    ∀ᵐ z ∂mixture p p₀ μ₀ μ, P z := by
  rw [mixture,ae_add_measure_iff,ae_finsetSum_measure_iff]
  exact ⟨Measure.ae_smul_measure (ae_labelled _ _ _ hP h₀) _,fun a _ =>
    Measure.ae_smul_measure (ae_labelled _ _ _ hP (h a)) _⟩

def supportCondition (l t u r : ℕ) (z : Option (Fin 5) × (Fin l × Fin l)) : Prop :=
  match z.1 with
  | none => z.2.1 = z.2.2
  | some a => if a=0 then z.2.1.val < l-t ∧ l-t ≤ z.2.2.val
    else if a=1 then z.2.1.val < t ∧ t ≤ z.2.2.val
    else if a=2 then z.2.1.val < l-u ∧ l-u ≤ z.2.2.val
    else if a=3 then z.2.1.val < u ∧ u ≤ z.2.2.val
    else z.2.1.val < r ∧ l-r ≤ z.2.2.val

lemma sixLaw_support (l t u r : ℕ) [NeZero l] (ht : 0 < t ∧ t < l)
    (hu : 0 < u ∧ u < l) (hr : 0 < r ∧ r < l) (p q τ : ℝ≥0∞) :
    ∀ᵐ z ∂sixLaw l t u r ht hu hr p q τ, supportCondition l t u r z := by
  apply ae_mixture _ _ _ _ _ (by measurability)
  · unfold diagonal
    apply (ae_map_iff (by fun_prop) (by measurability)).mpr
    exact ae_of_all _ (fun _ => rfl)
  · intro a
    fin_cases a <;> dsimp [supportCondition,components] <;>
      apply rectangle_ae

namespace CoordinateParameters
variable (P : CoordinateParameters)
lemma law_support (tagged : Bool) :
    ∀ᵐ z ∂P.law tagged, supportCondition P.l (roundedWidth P.l P.a)
      (roundedWidth P.l P.b) (roundedTag P.l P.m) z :=
  sixLaw_support _ _ _ _ _ _ _ _ _ _
lemma law_order (tagged : Bool) : ∀ᵐ z ∂P.law tagged, z.2.1 ≤ z.2.2 := by
  filter_upwards [P.law_support tagged] with z hz
  have htag : 2*roundedTag P.l P.m ≤ P.l := by
    have h := P.rounded_tag_half
    have : (2:ℝ)*(roundedTag P.l P.m:ℝ) ≤ P.l := by linarith
    exact_mod_cast this
  rcases z with ⟨a,x,y⟩
  cases a with
  | none => exact le_of_eq hz
  | some a =>
    fin_cases a <;> simp [supportCondition] at hz <;>
      change x.val ≤ y.val <;> omega

lemma top_a_failure (tagged : Bool) (d : Fin P.l)
    (hd : d.val < P.l-roundedWidth P.l P.a) :
    P.law tagged ({z | z.2.1=d} ∩ {z | z.1=some (0:Fin 5)}ᶜ) ≤
      ENNReal.ofReal (1-P.ρ/10)*P.law tagged {z | z.2.1=d} :=
  sixLaw_top_t_failure _ _ _ _ _ _ _ _ _ _ P.ρ_nonneg P.ρ_le_one
    (P.probabilities tagged) d hd (P.law_density_ten tagged false d)
lemma bottom_a_failure (tagged : Bool) (d : Fin P.l)
    (hd : roundedWidth P.l P.a ≤ d.val) :
    P.law tagged ({z | z.2.2=d} ∩ {z | z.1=some (1:Fin 5)}ᶜ) ≤
      ENNReal.ofReal (1-P.ρ/10)*P.law tagged {z | z.2.2=d} :=
  sixLaw_bottom_t_failure _ _ _ _ _ _ _ _ _ _ P.ρ_nonneg P.ρ_le_one
    (P.probabilities tagged) d hd (P.law_density_ten tagged true d)
lemma top_b_failure (tagged : Bool) (d : Fin P.l)
    (hd : d.val < P.l-roundedWidth P.l P.b) :
    P.law tagged ({z | z.2.1=d} ∩ {z | z.1=some (2:Fin 5)}ᶜ) ≤
      ENNReal.ofReal (1-P.σ/10)*P.law tagged {z | z.2.1=d} :=
  sixLaw_top_u_failure _ _ _ _ _ _ _ _ _ _ P.σ_nonneg P.σ_le_one
    (P.probabilities tagged) d hd (P.law_density_ten tagged false d)
lemma bottom_b_failure (tagged : Bool) (d : Fin P.l)
    (hd : roundedWidth P.l P.b ≤ d.val) :
    P.law tagged ({z | z.2.2=d} ∩ {z | z.1=some (3:Fin 5)}ᶜ) ≤
      ENNReal.ofReal (1-P.σ/10)*P.law tagged {z | z.2.2=d} :=
  sixLaw_bottom_u_failure _ _ _ _ _ _ _ _ _ _ P.σ_nonneg P.σ_le_one
    (P.probabilities tagged) d hd (P.law_density_ten tagged true d)
end CoordinateParameters
end CircleCoupling

end

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_RadixDigits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CircleDigits

universe uι uX

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ComplexInnerProductSpace
open MeasureTheory Filter Set
open Set
open scoped ComplexInnerProductSpace
open Set
open scoped ComplexInnerProductSpace
open MeasureTheory Set Filter Topology
open scoped BigOperators ComplexConjugate
open MeasureTheory Set Filter
open scoped BigOperators ENNReal
open Filter Set
open scoped Topology
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped ENNReal Classical
open Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Topology
open scoped BigOperators
open scoped BigOperators
open Set
open Set
open Set
open Set MeasureTheory Filter
open scoped BigOperators ENNReal Topology Classical
open MeasureTheory Set Filter
open scoped ENNReal Topology
open MeasureTheory Set
open MeasureTheory Filter Set
open scoped Topology BoundedContinuousFunction
open MeasureTheory Set Filter Topology TopologicalSpace
open MeasureTheory Set
open scoped ENNReal BigOperators Classical
open MeasureTheory Set
open scoped BigOperators ENNReal Classical
open MeasureTheory Set
open scoped ENNReal
open MeasureTheory Set
open scoped ENNReal NNReal

open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology
section
abbrev CircleX := AddCircle (1 : ℝ)

def denominator (b : ℕ → ℕ) (n : ℕ) : ℕ := ∏ i∈Finset.range n, b i

@[simp] lemma denominator_zero (b : ℕ → ℕ) : denominator b 0 = 1 := by simp [denominator]
@[simp] lemma denominator_succ (b : ℕ → ℕ) (n : ℕ) :
    denominator b (n+1) = denominator b n * b n := by simp [denominator,Finset.prod_range_succ]

lemma denominator_pos {b : ℕ → ℕ} (hb : ∀ i, 2≤b i) (n : ℕ) : 0<denominator b n := by
  exact Finset.prod_pos fun i _ ↦ lt_of_lt_of_le (by norm_num) (hb i)

lemma denominator_geometric {b : ℕ → ℕ} (hb : ∀ i, 2≤b i) (n : ℕ) :
    2^n ≤ denominator b n := by
  induction n with
  | zero => simp
  | succ n hn => rw [denominator_succ,pow_succ]; exact Nat.mul_le_mul hn (hb n)

lemma denominator_inv_bound {b : ℕ → ℕ} (hb : ∀ i, 2≤b i) (n : ℕ) :
    (denominator b n : ℝ)⁻¹ ≤ (1/2 : ℝ)^n := by
  rw [one_div,inv_pow]
  apply (inv_le_inv₀ (by exact_mod_cast denominator_pos hb n) (by positivity)).mpr
  exact_mod_cast denominator_geometric hb n

abbrev Digits (b : ℕ → ℕ) := ∀ i, Fin (b i)

def digitTerm (b : ℕ → ℕ) (d : Digits b) (i : ℕ) : ℝ := (d i : ℝ)/denominator b (i+1)

def expansion (b : ℕ → ℕ) (d : Digits b) : ℝ := ∑' i, digitTerm b d i

def endpoint (b : ℕ → ℕ) (d : Digits b) : CircleX := (expansion b d : CircleX)

lemma digitTerm_nonneg (b : ℕ → ℕ) (d : Digits b) (i : ℕ) : 0≤digitTerm b d i := by
  unfold digitTerm; positivity

lemma digitTerm_le_inverse {b : ℕ → ℕ} (hb : ∀ i, 2≤b i) (d : Digits b) (i : ℕ) :
    digitTerm b d i ≤ (denominator b i : ℝ)⁻¹ := by
  have hq : (0:ℝ)<denominator b i := by exact_mod_cast denominator_pos hb i
  have hbi : (0:ℝ)<b i := by exact_mod_cast lt_of_lt_of_le (by norm_num : 0<2) (hb i)
  rw [digitTerm,denominator_succ,Nat.cast_mul,div_le_iff₀ (mul_pos hq hbi)]
  rw [inv_mul_cancel_left₀ hq.ne']
  exact_mod_cast (d i).isLt.le

lemma digitTerm_summable {b : ℕ → ℕ} (hb : ∀ i, 2≤b i) (d : Digits b) :
    Summable (digitTerm b d) := by
  apply Summable.of_nonneg_of_le (digitTerm_nonneg b d)
    (fun i ↦ (digitTerm_le_inverse hb d i).trans (denominator_inv_bound hb i))
  exact summable_geometric_of_lt_one (by norm_num) (by norm_num)

lemma digitTerm_le_telescope {b : ℕ → ℕ} (hb : ∀ i, 2≤b i) (d : Digits b) (i : ℕ) :
    digitTerm b d i ≤ (denominator b i : ℝ)⁻¹-(denominator b (i+1) : ℝ)⁻¹ := by
  have hq : (0:ℝ)<denominator b i := by exact_mod_cast denominator_pos hb i
  have hbi : (0:ℝ)<b i := by exact_mod_cast lt_of_lt_of_le (by norm_num : 0<2) (hb i)
  rw [digitTerm,denominator_succ,Nat.cast_mul,div_le_iff₀ (mul_pos hq hbi)]
  have h : (d i : ℝ) ≤ (b i : ℝ)-1 := by
    have hh : (d i : ℝ)+1≤(b i : ℝ) := by exact_mod_cast (d i).isLt
    linarith
  rw [sub_mul,inv_mul_cancel_left₀ hq.ne']
  rw [inv_mul_cancel₀ (mul_ne_zero hq.ne' hbi.ne')]
  exact h

lemma expansion_tail_bound {b : ℕ → ℕ} (hb : ∀ i, 2≤b i) (d : Digits b) (n : ℕ) :
    0≤expansion b d-∑ i∈Finset.range n, digitTerm b d i ∧
    expansion b d-∑ i∈Finset.range n, digitTerm b d i ≤ (denominator b n : ℝ)⁻¹ := by
  have hsum := (digitTerm_summable hb d).sum_add_tsum_nat_add n
  change _ = expansion b d at hsum
  rw [← hsum,add_sub_cancel_left]
  refine ⟨tsum_nonneg fun i ↦ digitTerm_nonneg b d (i+n),?_⟩
  apply le_of_tendsto (((digitTerm_summable hb d).comp_injective (add_left_injective n)).hasSum.tendsto_sum_nat)
  apply Eventually.of_forall
  intro m
  calc
    ∑ i∈Finset.range m, digitTerm b d (i+n) ≤
      ∑ i∈Finset.range m, ((denominator b (i+n) : ℝ)⁻¹-(denominator b (i+n+1) : ℝ)⁻¹) :=
        Finset.sum_le_sum fun i _ ↦ digitTerm_le_telescope hb d (i+n)
    _ = (denominator b n : ℝ)⁻¹-(denominator b (m+n) : ℝ)⁻¹ := by
      simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
        Finset.sum_range_sub' (fun i ↦ (denominator b (i+n) : ℝ)⁻¹) m
    _ ≤ _ := sub_le_self _ (by positivity)

lemma measurable_digitTerm (b : ℕ → ℕ) (i : ℕ) : Measurable (fun d : Digits b ↦ digitTerm b d i) := by
  exact ((measurable_of_finite (fun x : Fin (b i) ↦ (x : ℝ))).comp (measurable_pi_apply i)).div_const _

lemma measurable_expansion (b : ℕ → ℕ) : Measurable (expansion b) :=
  Measurable.tsum fun i ↦ measurable_digitTerm b i

lemma measurable_endpoint (b : ℕ → ℕ) : Measurable (endpoint b) :=
  (AddCircle.continuous_mk' 1).measurable.comp (measurable_expansion b)



variable (b : ℕ → ℕ)

def digitLaw (i : ℕ) [NeZero (b i)] : Measure (Fin (b i)) := (PMF.uniformOfFintype (Fin (b i))).toMeasure

instance instIsProbabilityMeasureFinDigitLaw (i : ℕ) [NeZero (b i)] : IsProbabilityMeasure (digitLaw b i) := by
  unfold digitLaw; infer_instance

def uniformDigits [∀ i, NeZero (b i)] : Measure (Digits b) := Measure.infinitePi (fun i ↦ digitLaw b i)
instance instIsProbabilityMeasureDigitsUniformDigits [∀ i, NeZero (b i)] : IsProbabilityMeasure (uniformDigits b) := by
  unfold uniformDigits; infer_instance

omit b in
def character (k : ℤ) : AddChar CircleX ℂ where
  toFun := fourier k
  map_zero_eq_one' := fourier_eval_zero k
  map_add_eq_mul' x y := by simp [fourier_apply,smul_add,AddCircle.toCircle_add]

end


def prefixNumeral (b : ℕ → ℕ) (d : Digits b) : ℕ → ℕ
  | 0 => 0
  | n+1 => b n * prefixNumeral b d n + d n

def scaledTail (b : ℕ → ℕ) (d : Digits b) (n : ℕ) : ℝ :=
  denominator b n * expansion b d - prefixNumeral b d n

def gridFree (b : ℕ → ℕ) : Set CircleX := {x | ∀ n, denominator b n • x  ≠  0}

lemma prefixNumeral_sum {b : ℕ → ℕ} (hb : ∀ i, 2 ≤ b i) (d : Digits b) (n : ℕ) :
    ∑ i∈Finset.range n, digitTerm b d i = prefixNumeral b d n / (denominator b n : ℝ) := by
  induction n with
  | zero => simp [prefixNumeral]
  | succ n hn =>
    rw [Finset.sum_range_succ,hn]
    simp only [prefixNumeral,denominator_succ,digitTerm,Nat.cast_add,Nat.cast_mul]
    have hq : (denominator b n : ℝ) ≠ 0 := by exact_mod_cast (denominator_pos hb n).ne'
    have hb' : (b n : ℝ) ≠ 0 := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0<2) (hb n)).ne'
    field_simp

lemma scaledTail_bounds {b : ℕ → ℕ} (hb : ∀ i, 2 ≤ b i) (d : Digits b) (n : ℕ) :
    0 ≤ scaledTail b d n ∧ scaledTail b d n ≤ 1 := by
  have h := expansion_tail_bound hb d n
  rw [prefixNumeral_sum hb] at h
  have hq : (0:ℝ)<denominator b n := by exact_mod_cast denominator_pos hb n
  have he : scaledTail b d n = denominator b n * (expansion b d-prefixNumeral b d n/(denominator b n : ℝ)) := by
    unfold scaledTail; field_simp
  rw [he]
  exact ⟨mul_nonneg hq.le h.1, (mul_le_mul_of_nonneg_left h.2 hq.le).trans_eq (mul_inv_cancel₀ hq.ne')⟩

lemma scaledTail_coe {b : ℕ → ℕ} (d : Digits b) (n : ℕ) :
    ((scaledTail b d n : ℝ) : CircleX) = denominator b n • endpoint b d := by
  simp only [scaledTail,AddCircle.coe_sub,← nsmul_eq_mul,AddCircle.coe_nsmul,endpoint]
  have h : ((prefixNumeral b d n : ℝ) : CircleX) = 0 := by
    rw [show (prefixNumeral b d n : ℝ) = prefixNumeral b d n • (1:ℝ) by simp, AddCircle.coe_nsmul, AddCircle.coe_period, smul_zero]
  rw [h,sub_zero]

lemma scaledTail_lt_one {b : ℕ → ℕ} (hb : ∀ i, 2 ≤ b i) (d : Digits b)
    (hd : endpoint b d ∈ gridFree b) (n : ℕ) : scaledTail b d n<1 := by
  apply lt_of_le_of_ne (scaledTail_bounds hb d n).2
  intro he
  apply hd n
  rw [← scaledTail_coe d n,he]
  exact_mod_cast (AddCircle.coe_period (1:ℝ))

lemma scaledTail_repr {b : ℕ → ℕ} (hb : ∀ i, 2 ≤ b i) (d : Digits b)
    (hd : endpoint b d ∈ gridFree b) (n : ℕ) :
    ((AddCircle.measurableEquivIco 1 0 (denominator b n • endpoint b d)).val : ℝ) =
      scaledTail b d n := by
  rw [← scaledTail_coe d n]
  change (AddCircle.equivIco 1 0 ((scaledTail b d n : ℝ) : CircleX)).val = _
  rw [AddCircle.coe_equivIco_mk_apply]
  simp only [div_one,mul_one]
  exact Int.fract_eq_self.mpr ⟨(scaledTail_bounds hb d n).1,scaledTail_lt_one hb d hd n⟩

lemma scaledTail_recurrence (b : ℕ → ℕ) (d : Digits b) (n : ℕ) :
    (b n : ℝ)*scaledTail b d n = (d n : ℝ)+scaledTail b d (n+1) := by
  simp only [scaledTail,prefixNumeral,denominator_succ,Nat.cast_add,Nat.cast_mul]
  ring

lemma digit_interval {b : ℕ → ℕ} (hb : ∀ i, 2 ≤ b i) (d : Digits b)
    (hd : endpoint b d ∈ gridFree b) (n : ℕ) :
    (d n : ℝ)/(b n : ℝ)  ≤  scaledTail b d n ∧
    scaledTail b d n < ((d n : ℝ)+1)/(b n : ℝ) := by
  have hpos : (0:ℝ)<b n := by exact_mod_cast lt_of_lt_of_le (by norm_num : 0<2) (hb n)
  rw [div_le_iff₀ hpos,lt_div_iff₀ hpos,mul_comm (scaledTail b d n),scaledTail_recurrence]
  exact ⟨le_add_of_nonneg_right (scaledTail_bounds hb d (n+1)).1,
    add_lt_add_right (scaledTail_lt_one hb d hd (n+1)) _⟩

lemma scaledTail_tsum {b : ℕ → ℕ} (hb : ∀ i, 2 ≤ b i) (d : Digits b) (n : ℕ) :
    scaledTail b d n = (denominator b n : ℝ) * ∑' i, digitTerm b d (i+n) := by
  have h := (digitTerm_summable hb d).sum_add_tsum_nat_add n
  rw [prefixNumeral_sum hb] at h
  change _ = expansion b d at h
  rw [scaledTail,← h,mul_add]
  have hq : (denominator b n : ℝ) ≠ 0 := by exact_mod_cast (denominator_pos hb n).ne'
  rw [mul_div_cancel₀ _ hq]
  ring

lemma scaledTail_mono {b : ℕ → ℕ} (hb : ∀ i, 2 ≤ b i) {d e : Digits b}
    (hde : ∀ i, d i ≤ e i) (n : ℕ) : scaledTail b d n ≤ scaledTail b e n := by
  rw [scaledTail_tsum hb,scaledTail_tsum hb]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply ((digitTerm_summable hb d).comp_injective (add_left_injective n)).tsum_le_tsum _
    ((digitTerm_summable hb e).comp_injective (add_left_injective n))
  intro i
  exact div_le_div_of_nonneg_right (by exact_mod_cast hde (i+n)) (by positivity)



end CircleDigits

end

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_EndpointMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

universe uX uι uD uΩ

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ComplexInnerProductSpace
open MeasureTheory Filter Set
open Set
open scoped ComplexInnerProductSpace
open Set
open scoped ComplexInnerProductSpace
open MeasureTheory Set Filter Topology
open scoped BigOperators ComplexConjugate
open MeasureTheory Set Filter
open scoped BigOperators ENNReal
open Filter Set
open scoped Topology
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped ENNReal Classical
open Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Topology
open scoped BigOperators
open scoped BigOperators
open Set
open Set
open Set
open Set MeasureTheory Filter
open scoped BigOperators ENNReal Topology Classical
open MeasureTheory Set Filter
open scoped ENNReal Topology
open MeasureTheory Set
open MeasureTheory Filter Set
open scoped Topology BoundedContinuousFunction
open MeasureTheory Set Filter Topology TopologicalSpace
open MeasureTheory Set
open scoped ENNReal BigOperators Classical
open MeasureTheory Set
open scoped BigOperators ENNReal Classical
open MeasureTheory Set
open scoped ENNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology

open Set MeasureTheory Topology
open scoped symmDiff
namespace CircleCoupling

open CircleDigits

structure DigitSystem where
  b₀ : ℕ
  hb₀ : 2 ≤ b₀
  coord : ℕ → CoordinateParameters
namespace DigitSystem
variable (S : DigitSystem)
def radix : ℕ → ℕ | 0 => S.b₀ | n+1 => (S.coord n).l
lemma radix_ge_two (n : ℕ) : 2 ≤ S.radix n := by
  cases n with
  | zero => exact S.hb₀
  | succ n => have := (S.coord n).hl; have := (S.coord n).hm; change 2 ≤ (S.coord n).l; omega
instance instNeZeroNatRadix (n : ℕ) : NeZero (S.radix n) := ⟨by have := S.radix_ge_two n; omega⟩
abbrev Sample (n : ℕ) := Option (Fin 5) × (Fin (S.radix n) × Fin (S.radix n))
abbrev Samples := ∀ n, S.Sample n

def law (tagged : ℕ → Bool) : (n : ℕ) → Measure (S.Sample n)
  | 0 => labelled none (diagonal (S.radix 0))
  | n+1 => (S.coord n).law (tagged n)
instance instIsProbabilityMeasureSampleLaw (tagged : ℕ → Bool) (n : ℕ) : IsProbabilityMeasure (S.law tagged n) := by
  cases n with
  | zero => change IsProbabilityMeasure (Measure.map _ _); exact Measure.isProbabilityMeasure_map (measurable_const.prodMk measurable_id).aemeasurable
  | succ n => exact (show IsProbabilityMeasure ((S.coord n).law (tagged n)) from inferInstance)
def probability (tagged : ℕ → Bool) : Measure S.Samples := Measure.infinitePi (S.law tagged)
instance instIsProbabilityMeasureSamplesProbability (tagged : ℕ → Bool) : IsProbabilityMeasure (S.probability tagged) := by unfold probability; infer_instance

def observe (e : ℕ → Bool) (ω : S.Samples) : Digits S.radix := fun i => digitEndpoint (e i) (ω i).2
def endpoint (e : ℕ → Bool) (ω : S.Samples) : CircleDigits.CircleX := CircleDigits.endpoint S.radix (S.observe e ω)

def error (tagged : ℕ → Bool) : ℕ → ℝ
  | 0 => 0
  | n+1 => (60*(S.coord n).κ^2+10*(if tagged n then 1 else 0))/(S.coord n).m

lemma ae_digit_order (tagged : ℕ → Bool) :
    ∀ᵐ ω ∂S.probability tagged, ∀ i, (ω i).2.1 ≤ (ω i).2.2 := by
  rw [ae_all_iff]
  intro i
  have h : ∀ᵐ z ∂S.law tagged i, z.2.1 ≤ z.2.2 := by
    cases i with
    | zero =>
      apply ae_labelled _ _ _ (by measurability)
      unfold diagonal
      apply (ae_map_iff (by fun_prop) (by measurability)).mpr
      exact ae_of_all _ (fun _ => le_rfl)
    | succ n => exact (S.coord n).law_order (tagged n)
  exact (measurePreserving_eval_infinitePi (S.law tagged) i).quasiMeasurePreserving.ae h

end DigitSystem
end CircleCoupling

end

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_ConditionalBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

universe uD uΩ uι uT uX uY

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ComplexInnerProductSpace
open MeasureTheory Filter Set
open Set
open scoped ComplexInnerProductSpace
open Set
open scoped ComplexInnerProductSpace
open MeasureTheory Set Filter Topology
open scoped BigOperators ComplexConjugate
open MeasureTheory Set Filter
open scoped BigOperators ENNReal
open Filter Set
open scoped Topology
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped ENNReal Classical
open Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Topology
open scoped BigOperators
open scoped BigOperators
open Set
open Set
open Set
open Set MeasureTheory Filter
open scoped BigOperators ENNReal Topology Classical
open MeasureTheory Set Filter
open scoped ENNReal Topology
open MeasureTheory Set
open MeasureTheory Filter Set
open scoped Topology BoundedContinuousFunction
open MeasureTheory Set Filter Topology TopologicalSpace
open MeasureTheory Set
open scoped ENNReal BigOperators Classical
open MeasureTheory Set
open scoped BigOperators ENNReal Classical
open MeasureTheory Set
open scoped ENNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology
open Set MeasureTheory Topology
open scoped symmDiff

open MeasureTheory Set
open scoped ENNReal BigOperators
namespace CircleCoupling

lemma measure_le_of_singletons {D : Type uD} [MeasurableSpace D] [Countable D]
    [MeasurableSingletonClass D] {μ ν : Measure D}
    (h : ∀ d, μ {d} ≤ ν {d}) : μ ≤ ν := by
  rw [← Measure.sum_smul_dirac μ, ← Measure.sum_smul_dirac ν]
  apply Measure.le_iff.mpr
  intro s hs
  simp only [Measure.sum_apply _ hs, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.tsum_le_tsum (fun d => mul_le_mul' (h d) le_rfl)

lemma map_restrict_le_of_fibers {Ω : Type uΩ} {D : Type uD} [MeasurableSpace Ω]
    [MeasurableSpace D] [Countable D] [MeasurableSingletonClass D]
    (μ : Measure Ω) (f : Ω → D) (hf : Measurable f) (H : Set Ω)
    (δ : ℝ≥0∞)
    (h : ∀ d, μ ((f ⁻¹' {d}) ∩ H) ≤ δ * μ (f ⁻¹' {d})) :
    Measure.map f (μ.restrict H) ≤ δ • Measure.map f μ := by
  apply measure_le_of_singletons
  intro d
  simpa only [Measure.map_apply hf (measurableSet_singleton d),
    Measure.restrict_apply (hf (measurableSet_singleton d)),
    Measure.smul_apply, smul_eq_mul] using h d

lemma independent_fiber_failures {ι : Type uι} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type uΩ} {D : ι → Type uD} [∀ i, MeasurableSpace (Ω i)] [∀ i, MeasurableSpace (D i)]
    (μ : ∀ i, Measure (Ω i)) [∀ i, SigmaFinite (μ i)]
    (f : ∀ i, Ω i → D i) (d : ∀ i, D i) (H : ∀ i, Set (Ω i))
    (A : Finset ι) (c : ι → ℝ≥0∞)
    (h : ∀ i ∈ A, μ i ((f i ⁻¹' {d i}) ∩ H i) ≤ c i * μ i (f i ⁻¹' {d i})) :
    (Measure.pi μ) {ω | (∀ i, f i (ω i) = d i) ∧ ∀ i ∈ A, ω i ∈ H i} ≤
      (∏ i ∈ A, c i) * (Measure.pi μ) {ω | ∀ i, f i (ω i) = d i} := by
  classical
  have hset : {ω | (∀ i, f i (ω i) = d i) ∧ ∀ i ∈ A, ω i ∈ H i} =
      univ.pi (fun i => (f i ⁻¹' {d i}) ∩ if i ∈ A then H i else univ) := by
    ext ω
    simp only [mem_ofPred_eq, Set.mem_pi, mem_univ, forall_const, mem_inter_iff,
      mem_preimage, mem_singleton_iff]
    constructor
    · rintro ⟨hf,hH⟩ i
      exact ⟨hf i, by split_ifs with hi; exact hH i hi; trivial⟩
    · intro hp
      exact ⟨fun i => (hp i).1, fun i hi => by simpa [hi] using (hp i).2⟩
  have hset' : {ω | ∀ i, f i (ω i) = d i} = univ.pi (fun i => f i ⁻¹' {d i}) := by
    ext ω
    simp
  rw [hset,hset',Measure.pi_pi,Measure.pi_pi]
  calc
    _ ≤ ∏ i, (if i ∈ A then c i else 1) * μ i (f i ⁻¹' {d i}) := by
      apply Finset.prod_le_prod'
      intro i _
      by_cases hi : i ∈ A
      · simpa [hi] using h i hi
      · simp [hi]
    _ = _ := by rw [Finset.prod_mul_distrib]; congr 1; simp

lemma independent_selected_failures {ι : Type uι} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type uΩ} {D : ι → Type uD} [∀ i, MeasurableSpace (Ω i)] [∀ i, MeasurableSpace (D i)]
    [∀ i, Countable (D i)] [∀ i, MeasurableSingletonClass (D i)]
    (μ : ∀ i, Measure (Ω i)) [∀ i, SigmaFinite (μ i)]
    (f : ∀ i, Ω i → D i) (hf : ∀ i, Measurable (f i))
    (H : Set (∀ i, Ω i)) (bad : ∀ i, Set (Ω i))
    (A : (∀ i, D i) → Finset ι) (c : ι → ℝ≥0∞) (δ : ℝ≥0∞)
    (hlocal : ∀ d i, i ∈ A d →
      μ i ((f i ⁻¹' {d i}) ∩ bad i) ≤ c i * μ i (f i ⁻¹' {d i}))
    (hprod : ∀ d, (∃ ω ∈ H, (fun i => f i (ω i)) = d) → (∏ i∈A d, c i) ≤ δ)
    (hbad : ∀ ω ∈ H, ∀ i ∈ A (fun i => f i (ω i)), ω i ∈ bad i) :
    Measure.map (fun ω i => f i (ω i)) ((Measure.pi μ).restrict H) ≤
      δ • Measure.map (fun ω i => f i (ω i)) (Measure.pi μ) := by
  apply map_restrict_le_of_fibers _ _ (Measurable.of_eval (fun i => (hf i).comp (measurable_pi_apply i)))
  intro d
  change (Measure.pi μ) (((fun ω : ∀ i, Ω i => fun i => f i (ω i)) ⁻¹' {d}) ∩ H) ≤
    δ * (Measure.pi μ) ((fun ω : ∀ i, Ω i => fun i => f i (ω i)) ⁻¹' {d})
  by_cases hex : ∃ ω ∈ H, (fun i => f i (ω i)) = d
  swap
  · have hempty : ((fun ω i => f i (ω i)) ⁻¹' {d}) ∩ H = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      rintro ω ⟨he,hω⟩
      exact hex ⟨ω,hω,he⟩
    rw [hempty,measure_empty]
    exact bot_le
  have hs : ((fun ω i => f i (ω i)) ⁻¹' {d}) ∩ H ⊆
      {ω | (∀ i, f i (ω i) = d i) ∧ ∀ i ∈ A d, ω i ∈ bad i} := by
    rintro ω ⟨hd,hω⟩
    have he : (fun i => f i (ω i)) = d := hd
    exact ⟨fun i => congrFun he i, by simpa only [← he] using hbad ω hω⟩
  apply (measure_mono hs).trans
  apply (independent_fiber_failures μ f d bad (A d) c (hlocal d)).trans
  have hset : {ω : ∀ i, Ω i | ∀ i, f i (ω i) = d i} = (fun ω i => f i (ω i)) ⁻¹' {d} := by
    ext ω
    simp only [mem_ofPred_eq, mem_preimage, mem_singleton_iff, funext_iff]
  rw [hset]
  exact mul_le_mul' (hprod d hex) le_rfl

lemma full_tail_domination {T : Type uT} {Ω : Type uΩ} {D : Type uD} [MeasurableSpace T]
    [MeasurableSpace Ω] [MeasurableSpace D]
    (ν : Measure T) (μ : Measure Ω) [SFinite μ]
    (f : Ω → D) (hf : Measurable f) (H : Set (T × Ω)) (hH : MeasurableSet H)
    (δ : ℝ≥0∞)
    (hsection : ∀ t, Measure.map f (μ.restrict {ω | (t,ω) ∈ H}) ≤
      δ • Measure.map f μ) :
    Measure.map (fun z : T × Ω => (z.1,f z.2)) ((ν.prod μ).restrict H) ≤
      δ • Measure.map (fun z : T × Ω => (z.1,f z.2)) (ν.prod μ) := by
  have hF : Measurable (fun z : T × Ω => (z.1,f z.2)) :=
    measurable_fst.prodMk (hf.comp measurable_snd)
  apply Measure.le_iff.mpr
  intro s hs
  rw [Measure.map_apply hF hs,Measure.restrict_apply (hF hs),Measure.smul_apply,
    Measure.map_apply hF hs,Measure.prod_apply ((hF hs).inter hH),
    Measure.prod_apply (hF hs)]
  simp only [smul_eq_mul]
  calc
    _ ≤ ∫⁻ t, δ * μ ((fun ω => (t,f ω)) ⁻¹' s) ∂ν := by
      apply lintegral_mono
      intro t
      have hst : MeasurableSet (Prod.mk t ⁻¹' s) :=
        (measurable_const.prodMk measurable_id) hs
      have hh := hsection t (Prod.mk t ⁻¹' s)
      rw [Measure.map_apply hf hst,Measure.restrict_apply (hf hst),
        Measure.smul_apply,Measure.map_apply hf hst] at hh
      exact hh
    _ = _ := by
      exact lintegral_const_mul δ (show Measurable (fun t => μ ((fun ω => (t,f ω)) ⁻¹' s)) from
        measurable_measure_prodMk_left (ν := μ) (hF hs))


lemma map_domination {X : Type uX} {Y : Type uY} [MeasurableSpace X] [MeasurableSpace Y]
    (f : X → Y) (hf : Measurable f) {μ ν : Measure X} (δ : ℝ≥0∞)
    (h : μ ≤ δ • ν) : Measure.map f μ ≤ δ • Measure.map f ν := by
  rw [← Measure.map_smul]
  exact Measure.map_mono h hf

lemma selected_failures_endpoint {ι : Type uι} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type uΩ} {D : ι → Type uD} [∀ i, MeasurableSpace (Ω i)] [∀ i, MeasurableSpace (D i)]
    [∀ i, Countable (D i)] [∀ i, MeasurableSingletonClass (D i)]
    {T : Type uT} {Y : Type uY} [MeasurableSpace T] [MeasurableSpace Y]
    (ν : Measure T) (μ : ∀ i, Measure (Ω i)) [∀ i, SigmaFinite (μ i)]
    (f : ∀ i, Ω i → D i) (hf : ∀ i, Measurable (f i))
    (E : T × (∀ i, D i) → Y) (hE : Measurable E)
    (H : Set (T × (∀ i, Ω i))) (hH : MeasurableSet H) (bad : ∀ i, Set (Ω i))
    (A : T → (∀ i, D i) → Finset ι) (c : ι → ℝ≥0∞) (δ : ℝ≥0∞)
    (hlocal : ∀ t d i, i ∈ A t d →
      μ i ((f i ⁻¹' {d i}) ∩ bad i) ≤ c i * μ i (f i ⁻¹' {d i}))
    (hprod : ∀ t d, (∃ ω, (t,ω) ∈ H ∧ (fun i => f i (ω i)) = d) →
      (∏ i ∈ A t d, c i) ≤ δ)
    (hbad : ∀ t ω, (t,ω) ∈ H → ∀ i ∈ A t (fun i => f i (ω i)), ω i ∈ bad i) :
    Measure.map (fun z : T × (∀ i, Ω i) => E (z.1,fun i => f i (z.2 i)))
      ((ν.prod (Measure.pi μ)).restrict H) ≤
      δ • Measure.map (fun z : T × (∀ i, Ω i) => E (z.1,fun i => f i (z.2 i)))
        (ν.prod (Measure.pi μ)) := by
  have hf' : Measurable (fun ω : ∀ i, Ω i => fun i => f i (ω i)) :=
    Measurable.of_eval (fun i => (hf i).comp (measurable_pi_apply i))
  have hsection (t : T) := independent_selected_failures μ f hf {ω | (t,ω) ∈ H}
    bad (A t) c δ (hlocal t) (hprod t) (hbad t)
  have hdom := full_tail_domination ν (Measure.pi μ) _ hf' H hH δ hsection
  have hh := map_domination E hE δ hdom
  have hG : Measurable (fun z : T × (∀ i, Ω i) => (z.1,fun i => f i (z.2 i))) :=
    measurable_fst.prodMk (hf'.comp measurable_snd)
  rw [Measure.map_map hE hG,Measure.map_map hE hG] at hh
  exact hh

lemma failure_power_exponential (ρ m : ℝ) (n : ℕ)
    (hρ : 0 ≤ ρ) (hρ' : ρ ≤ 1) (hcard : m/40 ≤ (n : ℝ)) :
    (ENNReal.ofReal (1-ρ/10)) ^ n ≤ ENNReal.ofReal (Real.exp (-m*ρ/400)) := by
  rw [← ENNReal.ofReal_pow (by linarith : 0 ≤ 1-ρ/10)]
  apply ENNReal.ofReal_le_ofReal
  calc
    (1-ρ/10)^n ≤ (Real.exp (-ρ/10))^n := by
      apply pow_le_pow_left₀ (by linarith)
      have h := Real.add_one_le_exp (-ρ/10)
      linarith
    _ = Real.exp ((n : ℝ)*(-ρ/10)) := (Real.exp_nat_mul _ n).symm
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)

end CircleCoupling
open MeasureTheory Set
open scoped ENNReal
namespace CircleCoupling
lemma infinitePi_split {ι : Type uι} {Ω : ι → Type uΩ}
    [∀ i, MeasurableSpace (Ω i)] (μ : ∀ i, Measure (Ω i))
    [∀ i, IsProbabilityMeasure (μ i)] (p : ι → Prop) [DecidablePred p] :
    Measure.map (MeasurableEquiv.piEquivPiSubtypeProd Ω p).symm
      ((Measure.infinitePi fun i : {i // p i} => μ i).prod
        (Measure.infinitePi fun i : {i // ¬p i} => μ i)) = Measure.infinitePi μ := by
  classical
  apply Measure.eq_infinitePi
  intro s t ht
  rw [Measure.map_apply (by fun_prop) (.pi (Finset.countable_toSet _) fun i _ => ht i)]
  have hset : (MeasurableEquiv.piEquivPiSubtypeProd Ω p).symm ⁻¹' Set.pi (s : Set ι) t =
      (Set.pi ((s.subtype p) : Set {i // p i}) (fun i => t i)) ×ˢ
      (Set.pi ((s.subtype (fun i => ¬p i)) : Set {i // ¬p i}) (fun i => t i)) := by
    ext z
    simp only [mem_preimage, Set.mem_pi, mem_prod, Finset.mem_coe, Finset.mem_subtype]
    constructor
    · intro hz
      constructor
      · rintro ⟨i,hi⟩ his
        simpa [MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, hi]
          using hz i his
      · rintro ⟨i,hi⟩ his
        simpa [MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, hi]
          using hz i his
    · rintro ⟨hx,hy⟩ i his
      by_cases hi : p i
      · simpa [MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, hi]
          using hx ⟨i,hi⟩ his
      · simpa [MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, hi]
          using hy ⟨i,hi⟩ his
  rw [hset, Measure.prod_prod, Measure.infinitePi_pi, Measure.infinitePi_pi]
  · rw [Finset.prod_subtype_eq_prod_filter (fun i : ι => μ i (t i)),
      Finset.prod_subtype_eq_prod_filter (fun i : ι => μ i (t i))]
    exact Finset.prod_filter_mul_prod_filter_not s p (fun i => μ i (t i))
  · intro i hi; exact ht i
  · intro i hi; exact ht i

def glue {ι : Type uι} (Ω : ι → Type uΩ) (I : Finset ι) [DecidablePred (· ∈ I)]
    (z : (∀ i : {i // i ∉ I}, Ω i) × (∀ i : I, Ω i)) : ∀ i, Ω i :=
  fun i => if hi : i ∈ I then z.2 ⟨i,hi⟩ else z.1 ⟨i,hi⟩

lemma measurable_glue {ι : Type uι} (Ω : ι → Type uΩ) [∀ i, MeasurableSpace (Ω i)]
    (I : Finset ι) [DecidablePred (· ∈ I)] : Measurable (glue Ω I) := by
  apply Measurable.of_eval
  intro i
  dsimp [glue]
  split_ifs <;> fun_prop

lemma map_glue {ι : Type uι} {Ω : ι → Type uΩ} [∀ i, MeasurableSpace (Ω i)]
    (μ : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)]
    (I : Finset ι) [DecidablePred (· ∈ I)] :
    Measure.map (glue Ω I)
      ((Measure.infinitePi (fun i : {i // i ∉ I} => μ i)).prod (Measure.pi (fun i : I => μ i))) =
      Measure.infinitePi μ := by
  classical
  let e := MeasurableEquiv.piEquivPiSubtypeProd Ω (· ∈ I)
  have he : glue Ω I = e.symm ∘ Prod.swap := by
    funext z i
    simp [glue,e,MeasurableEquiv.piEquivPiSubtypeProd,Equiv.piEquivPiSubtypeProd]
  rw [he,← Measure.map_map e.symm.measurable measurable_swap,Measure.prod_swap]
  rw [← Measure.infinitePi_eq_pi (fun i : I => μ i)]
  exact infinitePi_split μ (· ∈ I)

lemma observe_glue {ι : Type uι} {Ω : ι → Type uΩ} {D : ι → Type uD} (I : Finset ι)
    [DecidablePred (· ∈ I)] (f : ∀ i, Ω i → D i)
    (z : (∀ i : {i // i ∉ I}, Ω i) × (∀ i : I, Ω i)) :
    (fun i => f i (glue Ω I z i)) =
      glue D I (fun i : {i // i ∉ I} => f i (z.1 i),fun i : I => f i (z.2 i)) := by
  funext i
  dsimp [glue]
  split_ifs <;> rfl

lemma infinite_selected_failures {ι : Type uι} {Ω : ι → Type uΩ} {D : ι → Type uD}
    [∀ i, MeasurableSpace (Ω i)] [∀ i, MeasurableSpace (D i)]
    [∀ i, Countable (D i)] [∀ i, MeasurableSingletonClass (D i)]
    {Y : Type uY} [MeasurableSpace Y]
    (μ : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)]
    (I : Finset ι) (f : ∀ i, Ω i → D i) (hf : ∀ i, Measurable (f i))
    (E : (∀ i, D i) → Y) (hE : Measurable E)
    (H : Set (∀ i, Ω i)) (hH : MeasurableSet H) (bad : ∀ i : I, Set (Ω i))
    (A : (∀ i, D i) → Finset I) (c : I → ℝ≥0∞) (δ : ℝ≥0∞)
    (hlocal : ∀ d i, i ∈ A d →
      μ i ((f i ⁻¹' {d i}) ∩ bad i) ≤ c i * μ i (f i ⁻¹' {d i}))
    (hprod : ∀ ω, ω ∈ H → (∏ i ∈ A (fun i => f i (ω i)), c i) ≤ δ)
    (hbad : ∀ ω, ω ∈ H → ∀ i ∈ A (fun i => f i (ω i)), ω i ∈ bad i) :
    Measure.map (fun ω => E (fun i => f i (ω i))) ((Measure.infinitePi μ).restrict H) ≤
      δ • Measure.map (fun ω => E (fun i => f i (ω i))) (Measure.infinitePi μ) := by
  classical
  let T := ∀ i : {i // i ∉ I}, Ω i
  let ν : Measure T := Measure.infinitePi (fun i : {i // i ∉ I} => μ i)
  let o : (∀ i, Ω i) → (∀ i, D i) := fun ω i => f i (ω i)
  have ho : Measurable o := Measurable.of_eval (fun i => (hf i).comp (measurable_pi_apply i))
  let g : T × (∀ i : I, D i) → (∀ i, D i) :=
    fun z => glue D I (fun i : {i // i ∉ I} => f i (z.1 i),z.2)
  have hg : Measurable g := (measurable_glue D I).comp
    ((Measurable.of_eval (fun i : {i // i ∉ I} => (hf i).comp ((measurable_pi_apply i).comp measurable_fst))).prodMk measurable_snd)
  have hh := selected_failures_endpoint ν (fun i : I => μ i) (fun i : I => f i)
    (fun i => hf i) (E ∘ g) (hE.comp hg) ((glue Ω I) ⁻¹' H)
    ((measurable_glue Ω I) hH) bad (fun t d => A (g (t,d))) c δ
    (by
      intro t d i hi
      have hh := hlocal (g (t,d)) i hi
      simpa [g,glue,i.property] using hh)
    (by
      intro t d hd
      obtain ⟨ω,hω,hfd⟩ := hd
      have hh := hprod (glue Ω I (t,ω)) hω
      rw [observe_glue,hfd] at hh
      exact hh)
    (by
      intro t ω hω i hi
      have hh := hbad (glue Ω I (t,ω)) hω i
      rw [observe_glue] at hh
      simpa [glue,i.property] using hh hi)
  have hid : (fun z : T × (∀ i : I, Ω i) => (E ∘ g) (z.1, fun i => f i (z.2 i))) =
      (E ∘ o) ∘ glue Ω I := by
    funext z
    dsimp [Function.comp_def,o,g]
    rw [observe_glue]
  rw [hid,← Measure.map_map (hE.comp ho) (measurable_glue Ω I),
    ← Measure.restrict_map (measurable_glue Ω I) hH,
    show Measure.map (glue Ω I) (ν.prod (Measure.pi (fun i : I => μ i))) = Measure.infinitePi μ from map_glue μ I,
    ← Measure.map_map (hE.comp ho) (measurable_glue Ω I),
    show Measure.map (glue Ω I) (ν.prod (Measure.pi (fun i : I => μ i))) = Measure.infinitePi μ from map_glue μ I] at hh
  exact hh

end CircleCoupling
namespace CircleDigits
lemma digit_interval_weak {b : ℕ → ℕ} (hb : ∀ i, 2 ≤ b i) (d : Digits b) (n : ℕ) :
    (d n : ℝ)/(b n : ℝ) ≤ scaledTail b d n ∧
    scaledTail b d n ≤ ((d n : ℝ)+1)/(b n : ℝ) := by
  have hpos : (0:ℝ)<b n := by exact_mod_cast lt_of_lt_of_le (by norm_num : 0<2) (hb n)
  rw [div_le_iff₀ hpos,le_div_iff₀ hpos,mul_comm (scaledTail b d n),scaledTail_recurrence]
  exact ⟨le_add_of_nonneg_right (scaledTail_bounds hb d (n+1)).1,
    add_le_add_right (scaledTail_bounds hb d (n+1)).2 _⟩
lemma measurable_prefixNumeral (b : ℕ → ℕ) (n : ℕ) : Measurable (fun d : Digits b => prefixNumeral b d n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    simp only [prefixNumeral]
    exact (measurable_const.mul ih).add ((measurable_of_countable (fun x : Fin (b n) => x.val)).comp (measurable_pi_apply n))
lemma measurable_scaledTail (b : ℕ → ℕ) (n : ℕ) : Measurable (fun d : Digits b => scaledTail b d n) :=
  (measurable_const.mul (measurable_expansion b)).sub ((measurable_of_countable (fun x : ℕ => (x:ℝ))).comp (measurable_prefixNumeral b n))
end CircleDigits

end

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_CrossingEstimates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ComplexInnerProductSpace
open MeasureTheory Filter Set
open Set
open scoped ComplexInnerProductSpace
open Set
open scoped ComplexInnerProductSpace
open MeasureTheory Set Filter Topology
open scoped BigOperators ComplexConjugate
open MeasureTheory Set Filter
open scoped BigOperators ENNReal
open Filter Set
open scoped Topology
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped ENNReal Classical
open Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Topology
open scoped BigOperators
open scoped BigOperators
open Set
open Set
open Set
open Set MeasureTheory Filter
open scoped BigOperators ENNReal Topology Classical
open MeasureTheory Set Filter
open scoped ENNReal Topology
open MeasureTheory Set
open MeasureTheory Filter Set
open scoped Topology BoundedContinuousFunction
open MeasureTheory Set Filter Topology TopologicalSpace
open MeasureTheory Set
open scoped ENNReal BigOperators Classical
open MeasureTheory Set
open scoped BigOperators ENNReal Classical
open MeasureTheory Set
open scoped ENNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology
open Set MeasureTheory Topology
open scoped symmDiff
open MeasureTheory Set
open scoped ENNReal BigOperators
open MeasureTheory Set
open scoped ENNReal
namespace CircleCoupling

section

section

section
lemma digit_below_threshold {l t d : ℕ} {w u z : ℝ}
    (hl : 0<l) (ht : t ≤ l) (_hw : 0<w) (htu : (t:ℝ) ≤ (l:ℝ)*w/2)
    (hu : u ≤ 1-w) (hz : (d:ℝ)/(l:ℝ) ≤ z) (hzu : z<u) : d < l-t := by
  have hl' : (0:ℝ)<l := by exact_mod_cast hl
  by_contra h
  have hdl : ((l-t:ℕ):ℝ) ≤ d := by exact_mod_cast (Nat.le_of_not_gt h)
  rw [Nat.cast_sub ht] at hdl
  have hdz := (div_le_iff₀ hl').mp hz
  have hzu' := mul_lt_mul_of_pos_right hzu hl'
  have hun := mul_le_mul_of_nonneg_right hu hl'.le
  nlinarith [mul_pos hl' _hw]
lemma digit_above_threshold {l t d : ℕ} {w u z : ℝ}
    (hl : 0<l) (_hw : 0<w) (htu : (t:ℝ) ≤ (l:ℝ)*w/2)
    (hu : w ≤ u) (hz : z ≤ ((d:ℝ)+1)/(l:ℝ)) (hzu : u≤z) : t ≤ d := by
  have hl' : (0:ℝ)<l := by exact_mod_cast hl
  by_contra h
  have hdt : (d:ℝ)+1 ≤ t := by exact_mod_cast (Nat.add_one_le_iff.mpr (Nat.lt_of_not_ge h))
  have hdz := (le_div_iff₀ hl').mp hz
  have hzu' := mul_le_mul_of_nonneg_right hzu hl'.le
  have hun := mul_le_mul_of_nonneg_right hu hl'.le
  nlinarith [mul_pos hl' _hw]
lemma top_forces_above {l t d : ℕ} {w u z : ℝ}
    (hl : 0<l) (ht : t ≤ l) (_hw : 0<w) (htu : (t:ℝ) ≤ (l:ℝ)*w/2)
    (hu : u ≤ 1-w) (hz : (d:ℝ)/(l:ℝ) ≤ z) (hdt : l-t ≤ d) : u < z := by
  have hl' : (0:ℝ)<l := by exact_mod_cast hl
  have hdl : ((l-t:ℕ):ℝ) ≤ d := by exact_mod_cast hdt
  rw [Nat.cast_sub ht] at hdl
  have hdz := (div_le_iff₀ hl').mp hz
  have hun := mul_le_mul_of_nonneg_right hu hl'.le
  by_contra h
  have huz := mul_le_mul_of_nonneg_right (le_of_not_gt h) hl'.le
  nlinarith [mul_pos hl' _hw]
lemma bottom_forces_below {l t d : ℕ} {w u z : ℝ}
    (hl : 0<l) (_hw : 0<w) (htu : (t:ℝ) ≤ (l:ℝ)*w/2)
    (hu : w ≤ u) (hz : z ≤ ((d:ℝ)+1)/(l:ℝ)) (hdt : d<t) : z < u := by
  have hl' : (0:ℝ)<l := by exact_mod_cast hl
  have hdl : (d:ℝ)+1 ≤ t := by exact_mod_cast (Nat.add_one_le_iff.mpr hdt)
  have hdz := (le_div_iff₀ hl').mp hz
  have hun := mul_le_mul_of_nonneg_right hu hl'.le
  by_contra h
  have huz := mul_le_mul_of_nonneg_right (le_of_not_gt h) hl'.le
  nlinarith [mul_pos hl' _hw]
open CircleDigits
abbrev LabelledDigits (b : ℕ → ℕ) := ∀ n, Option (Fin 5) × (Fin (b n) × Fin (b n))
def selectedBelow (b : ℕ → ℕ) (I : Finset ℕ) (u : ℕ → ℝ) (d : Digits b) : Finset I := by
  classical
  exact Finset.univ.filter (fun i => scaledTail b d i < u i)
def selectedAbove (b : ℕ → ℕ) (I : Finset ℕ) (u : ℕ → ℝ) (d : Digits b) : Finset I := by
  classical
  exact Finset.univ.filter (fun i => u i ≤ scaledTail b d i)

lemma crossing_top_domination {b : ℕ → ℕ} (hb : ∀ i, 2 ≤ b i)
    (μ : ∀ i, Measure (Option (Fin 5) × (Fin (b i) × Fin (b i))))
    [∀ i, IsProbabilityMeasure (μ i)] (I : Finset ℕ) (t : ℕ → ℕ) (u w : ℕ → ℝ)
    (top : Fin 5) (ρ m : ℝ) (hρ : 0≤ρ) (hρ1 : ρ≤1)
    (ht : ∀ i ∈ I, t i ≤ b i) (hw : ∀ i ∈ I, 0<w i)
    (hround : ∀ i ∈ I, (t i:ℝ) ≤ (b i:ℝ)*w i/2)
    (hu : ∀ i ∈ I, u i ≤ 1-w i)
    (hlocal : ∀ i ∈ I, ∀ d : Fin (b i), d.val < b i-t i →
      μ i ({z | z.2.1=d} ∩ {z | z.1=some top}ᶜ) ≤ ENNReal.ofReal (1-ρ/10)*μ i {z | z.2.1=d})
    (H : Set (LabelledDigits b)) (hH : MeasurableSet H)
    (hcard : ∀ ω ∈ H, m/40 ≤ ((selectedBelow b I u (fun i => (ω i).2.1)).card:ℝ))
    (hsupport : ∀ ω ∈ H, ∀ i ∈ I, (ω i).1=some top → b i-t i ≤ (ω i).2.2.val)
    (hnocross : ∀ ω ∈ H, ∀ i ∈ I, ¬(scaledTail b (fun i => (ω i).2.1) i < u i ∧
      u i ≤ scaledTail b (fun i => (ω i).2.2) i)) :
    Measure.map (fun ω => endpoint b (fun i => (ω i).2.1)) ((Measure.infinitePi μ).restrict H) ≤
      ENNReal.ofReal (Real.exp (-m*ρ/400)) •
        Measure.map (fun ω => endpoint b (fun i => (ω i).2.1)) (Measure.infinitePi μ) := by
  classical
  apply infinite_selected_failures μ I (fun _ z => z.2.1) (fun _ => by fun_prop)
    (endpoint b) (measurable_endpoint b) H hH
    (fun _ => {z | z.1=some top}ᶜ) (selectedBelow b I u)
    (fun _ => ENNReal.ofReal (1-ρ/10))
  · intro d i hi
    have hi' : scaledTail b d i < u i := (Finset.mem_filter.mp hi).2
    have hh := hlocal i i.property (d i) (digit_below_threshold
      (by have := hb i; omega) (ht i i.property) (hw i i.property)
      (hround i i.property) (hu i i.property) (digit_interval_weak hb d i).1 hi')
    simpa only [Set.preimage,Set.mem_singleton_iff] using hh
  · intro ω hω
    rw [Finset.prod_const]
    exact failure_power_exponential ρ m _ hρ hρ1 (hcard ω hω)
  · intro ω hω i hi hlabel
    have hx : scaledTail b (fun i => (ω i).2.1) i < u i := (Finset.mem_filter.mp hi).2
    apply hnocross ω hω i i.property
    refine ⟨hx,le_of_lt ?_⟩
    exact top_forces_above (by have := hb i; omega) (ht i i.property) (hw i i.property)
      (hround i i.property) (hu i i.property) (digit_interval_weak hb (fun i => (ω i).2.2) i).1
      (hsupport ω hω i i.property hlabel)

lemma crossing_bottom_domination {b : ℕ → ℕ} (hb : ∀ i, 2 ≤ b i)
    (μ : ∀ i, Measure (Option (Fin 5) × (Fin (b i) × Fin (b i))))
    [∀ i, IsProbabilityMeasure (μ i)] (I : Finset ℕ) (t : ℕ → ℕ) (u w : ℕ → ℝ)
    (bottom : Fin 5) (ρ m : ℝ) (hρ : 0≤ρ) (hρ1 : ρ≤1)
    (hw : ∀ i ∈ I, 0<w i) (hround : ∀ i ∈ I, (t i:ℝ) ≤ (b i:ℝ)*w i/2)
    (hu : ∀ i ∈ I, w i ≤ u i)
    (hlocal : ∀ i ∈ I, ∀ d : Fin (b i), t i ≤ d.val →
      μ i ({z | z.2.2=d} ∩ {z | z.1=some bottom}ᶜ) ≤ ENNReal.ofReal (1-ρ/10)*μ i {z | z.2.2=d})
    (H : Set (LabelledDigits b)) (hH : MeasurableSet H)
    (hcard : ∀ ω ∈ H, m/40 ≤ ((selectedAbove b I u (fun i => (ω i).2.2)).card:ℝ))
    (hsupport : ∀ ω ∈ H, ∀ i ∈ I, (ω i).1=some bottom → (ω i).2.1.val<t i)
    (hnocross : ∀ ω ∈ H, ∀ i ∈ I, ¬(scaledTail b (fun i => (ω i).2.1) i < u i ∧
      u i ≤ scaledTail b (fun i => (ω i).2.2) i)) :
    Measure.map (fun ω => endpoint b (fun i => (ω i).2.2)) ((Measure.infinitePi μ).restrict H) ≤
      ENNReal.ofReal (Real.exp (-m*ρ/400)) •
        Measure.map (fun ω => endpoint b (fun i => (ω i).2.2)) (Measure.infinitePi μ) := by
  classical
  apply infinite_selected_failures μ I (fun _ z => z.2.2) (fun _ => by fun_prop)
    (endpoint b) (measurable_endpoint b) H hH
    (fun _ => {z | z.1=some bottom}ᶜ) (selectedAbove b I u)
    (fun _ => ENNReal.ofReal (1-ρ/10))
  · intro d i hi
    have hi' : u i ≤ scaledTail b d i := (Finset.mem_filter.mp hi).2
    have hh := hlocal i i.property (d i) (digit_above_threshold
      (by have := hb i; omega) (hw i i.property)
      (hround i i.property) (hu i i.property) (digit_interval_weak hb d i).2 hi')
    simpa only [Set.preimage,Set.mem_singleton_iff] using hh
  · intro ω hω
    rw [Finset.prod_const]
    exact failure_power_exponential ρ m _ hρ hρ1 (hcard ω hω)
  · intro ω hω i hi hlabel
    have hy : u i ≤ scaledTail b (fun i => (ω i).2.2) i := (Finset.mem_filter.mp hi).2
    apply hnocross ω hω i i.property
    refine ⟨?_,hy⟩
    exact bottom_forces_below (by have := hb i; omega) (hw i i.property)
      (hround i i.property) (hu i i.property) (digit_interval_weak hb (fun i => (ω i).2.1) i).2
      (hsupport ω hω i i.property hlabel)
end
open CircleDigits
lemma measurable_selectedBelow_card (b : ℕ → ℕ) (I : Finset ℕ) (u : ℕ → ℝ) :
    Measurable (fun d : Digits b => (selectedBelow b I u d).card) := by
  classical
  have he : (fun d : Digits b => (selectedBelow b I u d).card) =
      fun d => ∑ i : I, if scaledTail b d i < u i then 1 else 0 := by
    funext d
    simp only [selectedBelow,Finset.card_filter]
  rw [he]
  apply Finset.measurable_sum
  intro i _
  exact Measurable.ite (measurableSet_lt (measurable_scaledTail b i) measurable_const)
    measurable_const measurable_const

def noCross (b : ℕ → ℕ) (I : Finset ℕ) (u : ℕ → ℝ) : Set (LabelledDigits b) :=
  {ω | ∀ i ∈ I, ¬(scaledTail b (fun k => (ω k).2.1) i < u i ∧
    u i ≤ scaledTail b (fun k => (ω k).2.2) i)}
lemma measurableSet_noCross (b : ℕ → ℕ) (I : Finset ℕ) (u : ℕ → ℝ) :
    MeasurableSet (noCross b I u) := by
  simp only [noCross,Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iInter
  intro _
  exact ((measurableSet_lt ((measurable_scaledTail b i).comp (by fun_prop)) measurable_const).inter
    (measurableSet_le measurable_const ((measurable_scaledTail b i).comp (by fun_prop)))).compl

lemma selected_card_sum {b : ℕ → ℕ} (I : Finset ℕ) (u : ℕ → ℝ) (ω : LabelledDigits b)
    (horder : ∀ i ∈ I, scaledTail b (fun k => (ω k).2.1) i ≤ scaledTail b (fun k => (ω k).2.2) i)
    (hno : ω ∈ noCross b I u) :
    (selectedBelow b I u (fun k => (ω k).2.1)).card +
      (selectedAbove b I u (fun k => (ω k).2.2)).card = I.card := by
  classical
  have he : selectedAbove b I u (fun k => (ω k).2.2) =
      Finset.univ.filter (fun i : I => ¬scaledTail b (fun k => (ω k).2.1) i < u i) := by
    ext i
    simp only [selectedAbove,Finset.mem_filter,Finset.mem_univ,true_and,not_lt]
    constructor
    · intro hi
      by_contra hh
      exact hno i i.property ⟨lt_of_not_ge hh,hi⟩
    · intro hi
      exact hi.trans (horder i i.property)
  rw [he]
  simpa only [selectedBelow,Finset.card_univ,Fintype.card_coe] using
    Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset I))
      (p := fun i => scaledTail b (fun k => (ω k).2.1) i < u i)

end
open CircleDigits

lemma conditional_crossing_estimates {b : ℕ → ℕ} (hb : ∀ i, 2 ≤ b i)
    (μ : ∀ i, Measure (Option (Fin 5) × (Fin (b i) × Fin (b i))))
    [∀ i, IsProbabilityMeasure (μ i)] (I : Finset ℕ) (t : ℕ → ℕ) (u w : ℕ → ℝ)
    (top bottom : Fin 5) (ρ m : ℝ) (hρ : 0≤ρ) (hρ1 : ρ≤1)
    (hI : m/20 ≤ (I.card:ℝ)) (ht : ∀ i ∈ I, t i ≤ b i) (hw : ∀ i ∈ I, 0<w i)
    (hround : ∀ i ∈ I, (t i:ℝ) ≤ (b i:ℝ)*w i/2)
    (hu : ∀ i ∈ I, w i ≤ u i ∧ u i ≤ 1-w i)
    (htop : ∀ i ∈ I, ∀ d : Fin (b i), d.val < b i-t i →
      μ i ({z | z.2.1=d} ∩ {z | z.1=some top}ᶜ) ≤ ENNReal.ofReal (1-ρ/10)*μ i {z | z.2.1=d})
    (hbottom : ∀ i ∈ I, ∀ d : Fin (b i), t i ≤ d.val →
      μ i ({z | z.2.2=d} ∩ {z | z.1=some bottom}ᶜ) ≤ ENNReal.ofReal (1-ρ/10)*μ i {z | z.2.2=d})
    (G : Set (LabelledDigits b)) (hG : MeasurableSet G) (hae : ∀ᵐ ω ∂Measure.infinitePi μ, ω ∈ G)
    (horder : ∀ ω ∈ G, ∀ i ∈ I,
      scaledTail b (fun k => (ω k).2.1) i ≤ scaledTail b (fun k => (ω k).2.2) i)
    (hst : ∀ ω ∈ G, ∀ i ∈ I, (ω i).1=some top → b i-t i ≤ (ω i).2.2.val)
    (hsb : ∀ ω ∈ G, ∀ i ∈ I, (ω i).1=some bottom → (ω i).2.1.val<t i) :
    ∃ H₁ H₂ : Set (LabelledDigits b), MeasurableSet H₁ ∧ MeasurableSet H₂ ∧
      Disjoint H₁ H₂ ∧ H₁ ∪ H₂ = noCross b I u ∧
      H₁ = noCross b I u ∩ {ω | (I.card:ℝ)/2 ≤ ((selectedBelow b I u (fun i => (ω i).2.1)).card:ℝ)} ∧
      Measure.map (fun ω => endpoint b (fun i => (ω i).2.1)) ((Measure.infinitePi μ).restrict H₁) ≤
        ENNReal.ofReal (Real.exp (-m*ρ/400)) •
          Measure.map (fun ω => endpoint b (fun i => (ω i).2.1)) (Measure.infinitePi μ) ∧
      Measure.map (fun ω => endpoint b (fun i => (ω i).2.2)) ((Measure.infinitePi μ).restrict H₂) ≤
        ENNReal.ofReal (Real.exp (-m*ρ/400)) •
          Measure.map (fun ω => endpoint b (fun i => (ω i).2.2)) (Measure.infinitePi μ) := by
  classical
  let A : Set (LabelledDigits b) := {ω | (I.card:ℝ)/2 ≤
    ((selectedBelow b I u (fun k => (ω k).2.1)).card:ℝ)}
  have hA : MeasurableSet A := measurableSet_le measurable_const
    ((measurable_of_countable (fun n : ℕ => (n:ℝ))).comp
      ((measurable_selectedBelow_card b I u).comp (show Measurable (fun ω : LabelledDigits b => fun k => (ω k).2.1) from by fun_prop)))
  let N := noCross b I u
  have hN := measurableSet_noCross b I u
  let H₁ := N ∩ A
  let H₂ := N \ A
  have h₁ : MeasurableSet H₁ := hN.inter hA
  have h₂ : MeasurableSet H₂ := hN.diff hA
  have he (H : Set (LabelledDigits b)) :
      (Measure.infinitePi μ).restrict H = (Measure.infinitePi μ).restrict (H ∩ G) := by
    apply Measure.restrict_congr_set
    filter_upwards [hae] with ω hω
    change (ω ∈ H) = (ω ∈ H ∩ G)
    apply propext
    exact ⟨fun h => ⟨h,hω⟩,fun h => h.1⟩
  refine ⟨H₁,H₂,h₁,h₂,disjoint_left.mpr (by intro ω h₁ h₂; exact h₂.2 h₁.2),
    Set.inter_union_sdiff N A,rfl,?_,?_⟩
  · rw [he]
    apply crossing_top_domination hb μ I t u w top ρ m hρ hρ1 ht hw hround
      (fun i hi => (hu i hi).2) htop (H₁ ∩ G) (h₁.inter hG)
    · intro ω hω
      have ha : (I.card:ℝ)/2 ≤ ((selectedBelow b I u (fun k => (ω k).2.1)).card:ℝ) := hω.1.2
      linarith
    · intro ω hω i hi
      exact hst ω hω.2 i hi
    · intro ω hω
      exact hω.1.1
  · rw [he]
    apply crossing_bottom_domination hb μ I t u w bottom ρ m hρ hρ1 hw hround
      (fun i hi => (hu i hi).1) hbottom (H₂ ∩ G) (h₂.inter hG)
    · intro ω hω
      have ha : ((selectedBelow b I u (fun k => (ω k).2.1)).card:ℝ) < (I.card:ℝ)/2 :=
        lt_of_not_ge hω.1.2
      have hs := selected_card_sum I u ω (horder ω hω.2) hω.1.1
      have hs' : ((selectedBelow b I u (fun k => (ω k).2.1)).card:ℝ) +
        ((selectedAbove b I u (fun k => (ω k).2.2)).card:ℝ) = I.card := by exact_mod_cast hs
      linarith
    · intro ω hω i hi
      exact hsb ω hω.2 i hi
    · intro ω hω
      exact hω.1.1
end
namespace CoordinateParameters
variable (P : CoordinateParameters)
def width (e : Bool) : ℝ := if e then P.b else P.a
def prob (e : Bool) : ℝ := if e then P.σ else P.ρ
def topLabel (e : Bool) : Fin 5 := if e then 2 else 0
def bottomLabel (e : Bool) : Fin 5 := if e then 3 else 1
lemma width_pos (e : Bool) : 0<P.width e := by cases e <;> first | exact P.a_pos | exact P.b_pos
lemma width_round (e : Bool) : 0 < roundedWidth P.l (P.width e) ∧ roundedWidth P.l (P.width e) < P.l ∧
    (P.l:ℝ)*P.width e/3 ≤ roundedWidth P.l (P.width e) ∧
    (roundedWidth P.l (P.width e):ℝ) ≤ (P.l:ℝ)*P.width e/2 := by
  cases e <;> first | exact P.width_a | exact P.width_b
lemma prob_le_one (e : Bool) : P.prob e≤1 := by cases e <;> first | exact P.ρ_le_one | exact P.σ_le_one
lemma top_failure (tagged e : Bool) (d : Fin P.l)
    (hd : d.val < P.l-roundedWidth P.l (P.width e)) :
    P.law tagged ({z | z.2.1=d} ∩ {z | z.1=some (topLabel e)}ᶜ) ≤
      ENNReal.ofReal (1-P.prob e/10)*P.law tagged {z | z.2.1=d} := by
  cases e
  · exact P.top_a_failure tagged d hd
  · exact P.top_b_failure tagged d hd
lemma bottom_failure (tagged e : Bool) (d : Fin P.l)
    (hd : roundedWidth P.l (P.width e) ≤ d.val) :
    P.law tagged ({z | z.2.2=d} ∩ {z | z.1=some (bottomLabel e)}ᶜ) ≤
      ENNReal.ofReal (1-P.prob e/10)*P.law tagged {z | z.2.2=d} := by
  cases e
  · exact P.bottom_a_failure tagged d hd
  · exact P.bottom_b_failure tagged d hd
lemma top_support (e : Bool) (z : P.Sample)
    (hz : supportCondition P.l (roundedWidth P.l P.a) (roundedWidth P.l P.b) (roundedTag P.l P.m) z)
    (hlabel : z.1=some (topLabel e)) : P.l-roundedWidth P.l (P.width e) ≤ z.2.2.val := by
  cases e <;> simp only [topLabel,Bool.false_eq_true,↓reduceIte] at hlabel
  · have h := hz
    simp [supportCondition,hlabel] at h
    change P.l - roundedWidth P.l P.a ≤ _
    omega
  · have h := hz
    simp [supportCondition,hlabel] at h
    change P.l - roundedWidth P.l P.b ≤ _
    omega
lemma bottom_support (e : Bool) (z : P.Sample)
    (hz : supportCondition P.l (roundedWidth P.l P.a) (roundedWidth P.l P.b) (roundedTag P.l P.m) z)
    (hlabel : z.1=some (bottomLabel e)) : z.2.1.val < roundedWidth P.l (P.width e) := by
  cases e <;> simp only [bottomLabel,Bool.false_eq_true,↓reduceIte] at hlabel
  · have h := hz
    simp [supportCondition,hlabel] at h
    exact h.1
  · have h := hz
    simp [supportCondition,hlabel] at h
    exact h.1
end CoordinateParameters
namespace DigitSystem
open CircleDigits CoordinateParameters
variable (S : DigitSystem)
def crossingWidth (e : Bool) : ℕ → ℝ | 0 => 1 | n+1 => (S.coord n).width e
def crossingDigit (e : Bool) : ℕ → ℕ | 0 => 0 | n+1 => roundedWidth (S.coord n).l ((S.coord n).width e)
def supported : Set S.Samples := {ω | (∀ i, (ω i).2.1 ≤ (ω i).2.2) ∧ ∀ n,
  supportCondition (S.coord n).l (roundedWidth (S.coord n).l (S.coord n).a)
    (roundedWidth (S.coord n).l (S.coord n).b) (roundedTag (S.coord n).l (S.coord n).m) (ω (n+1))}
lemma measurableSet_supported : MeasurableSet S.supported := by
  simp only [supported,Set.ofPred_and,Set.ofPred_forall]
  apply MeasurableSet.inter
  · exact MeasurableSet.iInter (fun n => ((Set.to_countable {z : S.Sample n | z.2.1 ≤ z.2.2}).measurableSet).preimage (measurable_pi_apply n))
  · exact MeasurableSet.iInter (fun n => ((Set.to_countable {z : S.Sample (n+1) | supportCondition (S.coord n).l (roundedWidth (S.coord n).l (S.coord n).a) (roundedWidth (S.coord n).l (S.coord n).b) (roundedTag (S.coord n).l (S.coord n).m) z}).measurableSet).preimage (measurable_pi_apply (n+1)))
lemma ae_supported (tagged : ℕ → Bool) : ∀ᵐ ω ∂S.probability tagged, ω ∈ S.supported := by
  have hs : ∀ᵐ ω ∂S.probability tagged, ∀ n,
      supportCondition (S.coord n).l (roundedWidth (S.coord n).l (S.coord n).a)
        (roundedWidth (S.coord n).l (S.coord n).b) (roundedTag (S.coord n).l (S.coord n).m) (ω (n+1)) := by
    rw [ae_all_iff]
    intro n
    exact (measurePreserving_eval_infinitePi (S.law tagged) (n+1)).quasiMeasurePreserving.ae
      ((S.coord n).law_support (tagged n))
  filter_upwards [S.ae_digit_order tagged,hs] with ω hω hs
  exact ⟨hω,hs⟩
end DigitSystem
end CircleCoupling
namespace CircleCoupling.DigitSystem
open CircleDigits CoordinateParameters
variable (S : DigitSystem)

lemma actual_crossing_estimates (tagged : ℕ → Bool) (e : Bool) (I : Finset ℕ)
    (h0 : 0 ∉ I) (u : ℕ → ℝ) (m ρ : ℝ) (hρ : 0≤ρ) (hρ1 : ρ≤1)
    (hI : m/20 ≤ (I.card:ℝ))
    (hcommon : ∀ n, n+1 ∈ I → (S.coord n).prob e=ρ)
    (hu : ∀ i ∈ I, S.crossingWidth e i ≤ u i ∧ u i ≤ 1-S.crossingWidth e i) :
    ∃ H₁ H₂ : Set S.Samples, MeasurableSet H₁ ∧ MeasurableSet H₂ ∧
      Disjoint H₁ H₂ ∧ H₁ ∪ H₂ = noCross S.radix I u ∧
      H₁ = noCross S.radix I u ∩ {ω | (I.card:ℝ)/2 ≤
        ((selectedBelow S.radix I u (fun i => (ω i).2.1)).card:ℝ)} ∧
      Measure.map (S.endpoint (fun _ => false)) ((S.probability tagged).restrict H₁) ≤
        ENNReal.ofReal (Real.exp (-m*ρ/400)) •
          Measure.map (S.endpoint (fun _ => false)) (S.probability tagged) ∧
      Measure.map (S.endpoint (fun _ => true)) ((S.probability tagged).restrict H₂) ≤
        ENNReal.ofReal (Real.exp (-m*ρ/400)) •
          Measure.map (S.endpoint (fun _ => true)) (S.probability tagged) := by
  apply conditional_crossing_estimates S.radix_ge_two (S.law tagged) I
    (S.crossingDigit e) u (S.crossingWidth e) (topLabel e) (bottomLabel e) ρ m hρ hρ1 hI
  · intro i hi
    cases i with
    | zero => exact False.elim (h0 hi)
    | succ n => exact (S.coord n).width_round e |>.2.1.le
  · intro i hi
    cases i with
    | zero => exact False.elim (h0 hi)
    | succ n => exact (S.coord n).width_pos e
  · intro i hi
    cases i with
    | zero => exact False.elim (h0 hi)
    | succ n => exact (S.coord n).width_round e |>.2.2.2
  · exact hu
  · intro i hi d hd
    cases i with
    | zero => exact False.elim (h0 hi)
    | succ n =>
      have hh := (S.coord n).top_failure (tagged n) e d hd
      rw [hcommon n hi] at hh
      exact hh
  · intro i hi d hd
    cases i with
    | zero => exact False.elim (h0 hi)
    | succ n =>
      have hh := (S.coord n).bottom_failure (tagged n) e d hd
      rw [hcommon n hi] at hh
      exact hh
  · exact S.measurableSet_supported
  · exact S.ae_supported tagged
  · intro ω hω i _
    exact scaledTail_mono S.radix_ge_two hω.1 i
  · intro ω hω i hi hlabel
    cases i with
    | zero => exact False.elim (h0 hi)
    | succ n => exact (S.coord n).top_support e _ (hω.2 n) hlabel
  · intro ω hω i hi hlabel
    cases i with
    | zero => exact False.elim (h0 hi)
    | succ n => exact (S.coord n).bottom_support e _ (hω.2 n) hlabel
end CircleCoupling.DigitSystem

end

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_ActualDigits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

universe uX

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ComplexInnerProductSpace
open MeasureTheory Filter Set
open Set
open scoped ComplexInnerProductSpace
open Set
open scoped ComplexInnerProductSpace
open MeasureTheory Set Filter Topology
open scoped BigOperators ComplexConjugate
open MeasureTheory Set Filter
open scoped BigOperators ENNReal
open Filter Set
open scoped Topology
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped ENNReal Classical
open Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Topology
open scoped BigOperators
open scoped BigOperators
open Set
open Set
open Set
open Set MeasureTheory Filter
open scoped BigOperators ENNReal Topology Classical
open MeasureTheory Set Filter
open scoped ENNReal Topology
open MeasureTheory Set
open MeasureTheory Filter Set
open scoped Topology BoundedContinuousFunction
open MeasureTheory Set Filter Topology TopologicalSpace
open MeasureTheory Set
open scoped ENNReal BigOperators Classical
open MeasureTheory Set
open scoped BigOperators ENNReal Classical
open MeasureTheory Set
open scoped ENNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology
open Set MeasureTheory Topology
open scoped symmDiff
open MeasureTheory Set
open scoped ENNReal BigOperators
open MeasureTheory Set
open scoped ENNReal

namespace CircleDigits
open Filter Set
open scoped Topology BigOperators

def hybrid {b : ℕ → ℕ} (d e : Digits b) (D : ℕ) : Digits b := fun i => if i<D then e i else d i
end CircleDigits

end

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_TaggedEvents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

universe uι uX uΩ

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ComplexInnerProductSpace
open MeasureTheory Filter Set
open Set
open scoped ComplexInnerProductSpace
open Set
open scoped ComplexInnerProductSpace
open MeasureTheory Set Filter Topology
open scoped BigOperators ComplexConjugate
open MeasureTheory Set Filter
open scoped BigOperators ENNReal
open Filter Set
open scoped Topology
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped ENNReal Classical
open Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Topology
open scoped BigOperators
open scoped BigOperators
open Set
open Set
open Set
open Set MeasureTheory Filter
open scoped BigOperators ENNReal Topology Classical
open MeasureTheory Set Filter
open scoped ENNReal Topology
open MeasureTheory Set
open MeasureTheory Filter Set
open scoped Topology BoundedContinuousFunction
open MeasureTheory Set Filter Topology TopologicalSpace
open MeasureTheory Set
open scoped ENNReal BigOperators Classical
open MeasureTheory Set
open scoped BigOperators ENNReal Classical
open MeasureTheory Set
open scoped ENNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology
open Set MeasureTheory Topology
open scoped symmDiff
open MeasureTheory Set
open scoped ENNReal BigOperators
open MeasureTheory Set
open scoped ENNReal

open MeasureTheory Set
open scoped BigOperators ENNReal
namespace CircleCoupling

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace CoordinateParameters
variable (P : CoordinateParameters)

def tagEvent : Set P.Sample := {z | z.1=some (4 : Fin 5)}
def marginEvent : Set P.Sample := {z | ((z.2.1.val:ℝ)+1)/(P.l:ℝ) ≤ 1-2/(P.m:ℝ) ∧
    2/(P.m:ℝ) ≤ (z.2.2.val:ℝ)/(P.l:ℝ)}
def untaggedMargin : Set P.Sample := P.tagEventᶜ ∩ P.marginEvent

lemma tag_forces_margin {z : P.Sample}
    (hz : supportCondition P.l (roundedWidth P.l P.a) (roundedWidth P.l P.b) (roundedTag P.l P.m) z)
    (ht : z∈P.tagEvent) : z∈P.marginEvent := by
  have ht' : z.1=some (4:Fin 5) := ht
  simp only [supportCondition,ht'] at hz
  norm_num at hz
  have hl : (0:ℝ)<P.l := by exact_mod_cast (NeZero.pos P.l)
  have hm := P.m_pos
  have h3 : (3:ℝ) ≤ P.m := by exact_mod_cast (by have := P.hm; omega : 3 ≤ P.m)
  have hx : (z.2.1.val:ℝ)+1 ≤ roundedTag P.l P.m := by exact_mod_cast hz.1
  have hy : (P.l:ℝ)-(roundedTag P.l P.m:ℝ) ≤ z.2.2.val := by
    have hh : (P.l:ℝ) ≤ (z.2.2.val:ℝ)+(roundedTag P.l P.m:ℝ) := by exact_mod_cast hz.2
    linarith
  have hb := P.tag_bounds.2.2.2
  constructor
  · apply (div_le_div_of_nonneg_right hx hl.le).trans
    rw [div_le_iff₀ hl]
    have hh : (P.l:ℝ)/P.m ≤ (1-2/(P.m:ℝ))*P.l := by
      apply (div_le_iff₀ hm).mpr
      field_simp
      nlinarith
    exact hb.trans hh
  · rw [le_div_iff₀ hl]
    have hh : (2/(P.m:ℝ))*P.l ≤ (P.l:ℝ)-(P.l:ℝ)/P.m := by
      calc
        _ = (2*P.l)/(P.m:ℝ) := by ring
        _ ≤ ((P.l:ℝ)*P.m-P.l)/P.m := div_le_div_of_nonneg_right (by nlinarith) hm.le
        _ = _ := by field_simp
    linarith

end CoordinateParameters
end CircleCoupling

namespace CircleCoupling.DigitSystem
open MeasureTheory Set
open scoped BigOperators
variable (S : DigitSystem)

def coordinateTag : (n : ℕ) → Set (S.Sample n)
  | 0 => ∅
  | n+1 => (S.coord n).tagEvent

def coordinateMargin : (n : ℕ) → Set (S.Sample n)
  | 0 => Set.univ
  | n+1 => (S.coord n).marginEvent

def coordinateUntaggedMargin (n : ℕ) : Set (S.Sample n) :=
  (S.coordinateTag n)ᶜ ∩ S.coordinateMargin n

def oneTagEvent (I : Finset ℕ) : Set S.Samples :=
  ⋃ i∈I, Set.pi (I:Set ℕ) (fun k => if k=i then S.coordinateTag k else S.coordinateUntaggedMargin k)

lemma oneTagEvent_margins {I : Finset ℕ} {ω : S.Samples}
    (hw : ω∈S.supported) (hω : ω∈S.oneTagEvent I) :
    (∃ i∈I, ω i∈S.coordinateTag i) ∧ ∀ i∈I, ω i∈S.coordinateMargin i := by
  obtain ⟨a,ha,h⟩ := Set.mem_iUnion₂.mp hω
  have hat : ω a∈S.coordinateTag a := by simpa using h a ha
  refine ⟨⟨a,ha,hat⟩,?_⟩
  intro i hi
  by_cases hia : i=a
  · subst i
    cases a with
    | zero => exact Set.mem_univ _
    | succ n => exact (S.coord n).tag_forces_margin (hw.2 n) hat
  · have hg : ω i∈S.coordinateUntaggedMargin i := by simpa [hia] using h i hi
    exact hg.2
end CircleCoupling.DigitSystem

end

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_Rounding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CircleRounding

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ComplexInnerProductSpace
open MeasureTheory Filter Set
open Set
open scoped ComplexInnerProductSpace
open Set
open scoped ComplexInnerProductSpace
open MeasureTheory Set Filter Topology
open scoped BigOperators ComplexConjugate
open MeasureTheory Set Filter
open scoped BigOperators ENNReal
open Filter Set
open scoped Topology
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped ENNReal Classical
open Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Topology
open scoped BigOperators
open scoped BigOperators
open Set
open Set
open Set
open Set MeasureTheory Filter
open scoped BigOperators ENNReal Topology Classical
open MeasureTheory Set Filter
open scoped ENNReal Topology
open MeasureTheory Set
open MeasureTheory Filter Set
open scoped Topology BoundedContinuousFunction
open MeasureTheory Set Filter Topology TopologicalSpace
open MeasureTheory Set
open scoped ENNReal BigOperators Classical
open MeasureTheory Set
open scoped BigOperators ENNReal Classical
open MeasureTheory Set
open scoped ENNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology
open Set MeasureTheory Topology
open scoped symmDiff
open MeasureTheory Set
open scoped ENNReal BigOperators
open MeasureTheory Set
open scoped ENNReal
open MeasureTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Set
open scoped ENNReal NNReal BigOperators

section
open Set MeasureTheory
open scoped ENNReal
abbrev X := AddCircle (1:ℝ)
def repr (x : X) : ℝ := (AddCircle.measurableEquivIco 1 0 x).val
lemma repr_mem (x : X) : repr x∈Ico 0 1 := by
  simpa [repr] using (AddCircle.measurableEquivIco 1 0 x).property
lemma coe_repr (x : X) : (repr x:X)=x := by
  exact (AddCircle.measurableEquivIco 1 0).symm_apply_apply x
lemma repr_mk (t : ℝ) : repr (t:X)=Int.fract t := by
  change (AddCircle.equivIco 1 0 (t:X)).val=_
  simpa only [div_one,mul_one] using AddCircle.coe_equivIco_mk_apply (p:=(1:ℝ)) t
lemma repr_zero : repr 0=0 := by simpa using repr_mk 0

def intervalRamp (δ s : ℝ) : ℝ := min 0 ((s-δ)/(2*δ))+max 0 ((s-(1-δ))/(2*δ))
lemma intervalRamp_continuous (δ : ℝ) : Continuous (intervalRamp δ) := by
  unfold intervalRamp
  fun_prop
lemma intervalRamp_monotone {δ : ℝ} (hδ : 0<δ) : Monotone (intervalRamp δ) := by
  intro s t hst
  apply add_le_add
  · exact min_le_min le_rfl (div_le_div_of_nonneg_right (sub_le_sub_right hst δ) (by positivity))
  · exact max_le_max le_rfl (div_le_div_of_nonneg_right (sub_le_sub_right hst (1-δ)) (by positivity))
lemma intervalRamp_zero {δ : ℝ} (hδ : 0<δ) (hδ1 : δ<1) : intervalRamp δ 0=-(1/2:ℝ) := by
  unfold intervalRamp
  rw [min_eq_right (by apply div_nonpos_of_nonpos_of_nonneg <;> linarith),max_eq_left (by apply div_nonpos_of_nonpos_of_nonneg <;> linarith)]
  field_simp
  ring
lemma intervalRamp_one {δ : ℝ} (hδ : 0<δ) (hδ1 : δ<1) : intervalRamp δ 1=(1/2:ℝ) := by
  unfold intervalRamp
  rw [min_eq_left (by apply div_nonneg <;> linarith),max_eq_right (by apply div_nonneg <;> linarith)]
  field_simp
  ring
lemma intervalRamp_bounds {δ s : ℝ} (hδ : 0<δ) (hδ1 : δ<1) (hs : s∈Icc 0 1) :
    -(1/2:ℝ) ≤ intervalRamp δ s ∧ intervalRamp δ s ≤ 1/2 := by
  rw [←intervalRamp_zero hδ hδ1,←intervalRamp_one hδ hδ1]
  exact ⟨intervalRamp_monotone hδ hs.1,intervalRamp_monotone hδ hs.2⟩
lemma intervalRamp_middle {δ s : ℝ} (hδ : 0<δ) (hs : δ ≤ s ∧ s ≤ 1-δ) : intervalRamp δ s=0 := by
  unfold intervalRamp
  rw [min_eq_left (div_nonneg (sub_nonneg.mpr hs.1) (by positivity)),max_eq_left (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hs.2) (by positivity))]
  ring

def periodicCorrector (δ : ℝ) : X → ℝ := AddCircle.liftIco 1 0 (fun s => intervalRamp δ s-s)
lemma periodicCorrector_continuous {δ : ℝ} (hδ : 0<δ) (hδ1 : δ<1) : Continuous (periodicCorrector δ) := by
  apply AddCircle.liftIco_zero_continuous
  · simp only [intervalRamp_zero hδ hδ1,intervalRamp_one hδ hδ1]; ring
  · exact ((intervalRamp_continuous δ).sub continuous_id).continuousOn
lemma periodicCorrector_repr (δ : ℝ) (x : X) : periodicCorrector δ x=intervalRamp δ (repr x)-repr x := by
  conv_lhs => rw [←coe_repr x]
  exact AddCircle.liftIco_zero_coe_apply (repr_mem x)

def roundedDrop (δ β c : ℝ) (x : X) : ℝ := c*(β+periodicCorrector δ (x+(β:X))-periodicCorrector δ x)
def correction (δ c : ℝ) (x : X) : ℝ := c*intervalRamp δ (repr x)
lemma roundedDrop_continuous {δ : ℝ} (hδ : 0<δ) (hδ1 : δ<1) (β c : ℝ) : Continuous (roundedDrop δ β c) := by
  unfold roundedDrop
  exact continuous_const.mul ((continuous_const.add ((periodicCorrector_continuous hδ hδ1).comp (continuous_id.add continuous_const))).sub (periodicCorrector_continuous hδ hδ1))
lemma repr_add (x : X) (β : ℝ) : repr (x+(β:X))=Int.fract (repr x+β) := by
  calc
    _ = repr ((repr x+β:ℝ):X) := by rw [AddCircle.coe_add,coe_repr]
    _ = _ := repr_mk _

lemma roundedDrop_formula (δ β c : ℝ) (x : X) :
    roundedDrop δ β c x=c*((Int.floor (repr x+β):ℤ)+intervalRamp δ (repr (x+(β:X)))-intervalRamp δ (repr x)) := by
  rw [roundedDrop,periodicCorrector_repr,periodicCorrector_repr]
  have hh := repr_add x β
  rw [Int.fract] at hh
  congr 1
  linarith
lemma roundedDrop_nonneg {δ β c : ℝ} (hδ : 0<δ) (hδ1 : δ<1) (hβ : 0 ≤ β) (hβ1 : β<1) (hc : 0 ≤ c) (x : X) :
    0 ≤ roundedDrop δ β c x := by
  rw [roundedDrop_formula]
  apply mul_nonneg hc
  have hx := repr_mem x
  have hy := repr_mem (x+(β:X))
  have hf0 : 0 ≤ Int.floor (repr x+β) := Int.floor_nonneg.mpr (by linarith [hx.1])
  have hf1 : Int.floor (repr x+β) ≤ 1 := by
    rw [Int.floor_le_iff]; norm_num; linarith [hx.2]
  have hb := intervalRamp_bounds hδ hδ1 ⟨hx.1,hx.2.le⟩
  have hb' := intervalRamp_bounds hδ hδ1 ⟨hy.1,hy.2.le⟩
  rcases (show Int.floor (repr x+β)=0 ∨ Int.floor (repr x+β)=1 by omega) with he | he
  · have hxy : repr x ≤ repr (x+(β:X)) := by rw [repr_add,Int.fract,he]; norm_num; linarith
    have hh := intervalRamp_monotone hδ hxy
    rw [he]; norm_num; linarith
  · rw [he]; norm_num; linarith
end

open Set MeasureTheory
open scoped ENNReal
lemma roundedDrop_zero {δ β : ℝ} (hδ : 0<δ) (hδ1 : δ<1) (hβ : δ ≤ β) (hβ1 : β ≤ 1-δ) (c : ℝ) :
    roundedDrop δ β c 0=c/2 := by
  have hb0 : 0 ≤ β := hδ.le.trans hβ
  have hb1 : β<1 := by linarith
  rw [roundedDrop_formula,repr_zero,zero_add,Int.floor_eq_zero_iff.mpr ⟨hb0,hb1⟩]
  simp only [Int.cast_zero,zero_add]
  rw [repr_mk,Int.fract_eq_self.mpr ⟨hb0,hb1⟩,intervalRamp_middle hδ ⟨hβ,hβ1⟩,intervalRamp_zero hδ hδ1]
  ring


end CircleRounding

end

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_Concentration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CircleConcentration

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ComplexInnerProductSpace
open MeasureTheory Filter Set
open Set
open scoped ComplexInnerProductSpace
open Set
open scoped ComplexInnerProductSpace
open MeasureTheory Set Filter Topology
open scoped BigOperators ComplexConjugate
open MeasureTheory Set Filter
open scoped BigOperators ENNReal
open Filter Set
open scoped Topology
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped ENNReal Classical
open Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Topology
open scoped BigOperators
open scoped BigOperators
open Set
open Set
open Set
open Set MeasureTheory Filter
open scoped BigOperators ENNReal Topology Classical
open MeasureTheory Set Filter
open scoped ENNReal Topology
open MeasureTheory Set
open MeasureTheory Filter Set
open scoped Topology BoundedContinuousFunction
open MeasureTheory Set Filter Topology TopologicalSpace
open MeasureTheory Set
open scoped ENNReal BigOperators Classical
open MeasureTheory Set
open scoped BigOperators ENNReal Classical
open MeasureTheory Set
open scoped ENNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology
open Set MeasureTheory Topology
open scoped symmDiff
open MeasureTheory Set
open scoped ENNReal BigOperators
open MeasureTheory Set
open scoped ENNReal
open MeasureTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Set
open scoped ENNReal NNReal BigOperators

section
open Set Filter MeasureTheory
open scoped Topology ENNReal
abbrev X := AddCircle (1:ℝ)
def orbitMin (θ : X) (j : ℕ) (x : X) : ℝ :=
  (Finset.range (j+1)).inf' (by simp) (fun b => dist (x+b • θ) 0)
lemma orbitMin_continuous (θ : X) (j : ℕ) : Continuous (orbitMin θ j) := by
  unfold orbitMin
  exact (Continuous.finset_inf'_apply (f := fun b : ℕ => fun x : X => dist (x+b • θ) 0) (by simp : (Finset.range (j+1)).Nonempty) (fun _ _ => by fun_prop))
lemma orbitMin_nonneg (θ : X) (j : ℕ) (x : X) : 0 ≤ orbitMin θ j x :=
  Finset.le_inf' _ _ (fun _ _ => dist_nonneg)
lemma orbitMin_le (θ : X) (j b : ℕ) (hb : b≤j) (x : X) : orbitMin θ j x ≤ dist (x+b • θ) 0 :=
  Finset.inf'_le _ (Finset.mem_range.mpr (by omega))
lemma orbitMin_max (θ : X) (j : ℕ) : ∃ x : X, ∀ y, orbitMin θ j y ≤ orbitMin θ j x := by
  obtain ⟨x,_,hx⟩ := isCompact_univ.exists_isMaxOn (Set.univ_nonempty : (Set.univ:Set X).Nonempty) (orbitMin_continuous θ j).continuousOn
  exact ⟨x,fun y => hx (Set.mem_univ y)⟩
def orbitRadius (θ : X) (j : ℕ) : ℝ := orbitMin θ j (Classical.choose (orbitMin_max θ j))
lemma orbitMin_le_radius (θ : X) (j : ℕ) (x : X) : orbitMin θ j x ≤ orbitRadius θ j :=
  Classical.choose_spec (orbitMin_max θ j) x
lemma orbitRadius_nonneg (θ : X) (j : ℕ) : 0 ≤ orbitRadius θ j := orbitMin_nonneg _ _ _
lemma finite_orbit_cover (θ : X) (hd : DenseRange (fun n : ℕ => n • θ)) {ε : ℝ} (hε : 0<ε) :
    ∃ N : ℕ, ∀ x : X, ∃ b≤N, dist (x+b • θ) 0<ε := by
  have hx : ∀ x : X, ∃ b : ℕ, dist (x+b • θ) 0<ε := by
    intro x
    obtain ⟨b,hb⟩ := hd.exists_dist_lt (-x) hε
    refine ⟨b,?_⟩
    rw [dist_eq_norm] at hb ⊢
    rw [show -x-b • θ=-(x+b • θ) by abel,norm_neg] at hb
    simpa using hb
  obtain ⟨s,hs⟩ := isCompact_univ.elim_finite_subcover (fun b : ℕ => {x : X | dist (x+b • θ) 0<ε})
    (fun _ => isOpen_lt (by fun_prop) continuous_const) (by simpa only [subset_def,mem_univ,mem_iUnion,mem_ofPred_eq,true_implies] using hx)
  refine ⟨s.sup id,fun x => ?_⟩
  obtain ⟨b,hb,hx⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
  exact ⟨b,Finset.le_sup (f:=id) hb,hx⟩
lemma orbitRadius_tendsto (θ : X) (hd : DenseRange (fun n : ℕ => n • θ)) : Tendsto (orbitRadius θ) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha; exact Eventually.of_forall (fun j => ha.trans_le (orbitRadius_nonneg θ j))
  · intro ε hε
    obtain ⟨N,hN⟩ := finite_orbit_cover θ hd hε
    filter_upwards [eventually_ge_atTop N] with j hj
    obtain ⟨b,hb,hx⟩ := hN (Classical.choose (orbitMin_max θ j))
    exact (orbitMin_le θ j b (hb.trans hj) _).trans_lt hx

def supportRadius (θ : X) (j : ℕ) : ℝ := orbitRadius θ j+1/((j:ℝ)+1)
lemma orbitRadius_lt_supportRadius (θ : X) (j : ℕ) : orbitRadius θ j<supportRadius θ j := by
  unfold supportRadius
  have : (0:ℝ)<1/((j:ℝ)+1) := by positivity
  linarith
lemma supportRadius_pos (θ : X) (j : ℕ) : 0<supportRadius θ j := (orbitRadius_nonneg θ j).trans_lt (orbitRadius_lt_supportRadius θ j)
lemma supportRadius_tendsto (θ : X) (hd : DenseRange (fun n : ℕ => n • θ)) : Tendsto (supportRadius θ) atTop (𝓝 0) := by
  change Tendsto (fun j : ℕ => orbitRadius θ j+1/((j:ℝ)+1)) atTop (𝓝 0)
  simpa only [add_zero] using (orbitRadius_tendsto θ hd).add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ))
def bump (θ : X) (j : ℕ) (x : X) : ℝ := max 0 (1-dist x 0/supportRadius θ j)
lemma bump_continuous (θ : X) (j : ℕ) : Continuous (bump θ j) := by unfold bump; fun_prop
lemma bump_nonneg (θ : X) (j : ℕ) (x : X) : 0≤bump θ j x := le_max_left _ _
lemma bump_le_one (θ : X) (j : ℕ) (x : X) : bump θ j x≤1 := by
  apply max_le (by norm_num)
  have := div_nonneg (dist_nonneg (x:=x) (y:=0)) (supportRadius_pos θ j).le
  linarith
lemma bump_zero (θ : X) (j : ℕ) : bump θ j 0=1 := by simp [bump]
lemma bump_eq_zero (θ : X) (j : ℕ) (x : X) (hx : supportRadius θ j ≤ dist x 0) : bump θ j x=0 := by
  apply max_eq_left
  have hh : (1:ℝ)≤dist x 0/supportRadius θ j := (le_div_iff₀ (supportRadius_pos θ j)).mpr (by simpa using hx)
  linarith
lemma bump_pos (θ : X) (j : ℕ) (x : X) (hx : dist x 0<supportRadius θ j) : 0<bump θ j x := by
  apply lt_max_of_lt_right
  have := (div_lt_one (supportRadius_pos θ j)).mpr hx
  linarith

def partitionDenom (θ : X) (j : ℕ) (x : X) : ℝ := ∑ b∈Finset.range (j+1), bump θ j (x+b • θ)
lemma partitionDenom_continuous (θ : X) (j : ℕ) : Continuous (partitionDenom θ j) := by
  apply continuous_finsetSum
  intro b _
  exact (bump_continuous θ j).comp (continuous_id.add continuous_const)
lemma partitionDenom_pos (θ : X) (j : ℕ) (x : X) : 0<partitionDenom θ j x := by
  apply Finset.sum_pos' (fun _ _ => bump_nonneg _ _ _)
  obtain ⟨b,hb,he⟩ := Finset.exists_mem_eq_inf' (by simp : (Finset.range (j+1)).Nonempty) (fun b => dist (x+b • θ) 0)
  refine ⟨b,hb,bump_pos θ j _ ?_⟩
  rw [←he]
  exact (orbitMin_le_radius θ j x).trans_lt (orbitRadius_lt_supportRadius θ j)
lemma partitionDenom_le (θ : X) (j : ℕ) (x : X) : partitionDenom θ j x ≤ (j:ℝ)+1 := by
  calc
    _ ≤ ∑ _b∈Finset.range (j+1), (1:ℝ) := Finset.sum_le_sum (fun b _=>bump_le_one θ j _)
    _ = _ := by simp

def partition (θ : X) (j b : ℕ) (x : X) : ℝ := bump θ j (x+b • θ)/partitionDenom θ j x
lemma partition_continuous (θ : X) (j b : ℕ) : Continuous (partition θ j b) :=
  ((bump_continuous θ j).comp (continuous_id.add continuous_const)).div (partitionDenom_continuous θ j) (fun x => ne_of_gt (partitionDenom_pos θ j x))
lemma partition_nonneg (θ : X) (j b : ℕ) (x : X) : 0≤partition θ j b x := div_nonneg (bump_nonneg _ _ _) (partitionDenom_pos _ _ _).le
lemma partition_zero_lower (θ : X) (j : ℕ) : 1/((j:ℝ)+1)≤partition θ j 0 0 := by
  simp only [partition,zero_nsmul,add_zero,bump_zero]
  exact one_div_le_one_div_of_le (partitionDenom_pos θ j 0) (partitionDenom_le θ j 0)
end

open Set Filter MeasureTheory
open scoped Topology ENNReal

def moveTerm (θ : X) (j b : ℕ) (h : X → ℝ) (x : X) : ℝ := partition θ j b x*h x
def movedDrop (θ : X) (j : ℕ) (h : X → ℝ) (x : X) : ℝ :=
  ∑ b∈Finset.range (j+1),moveTerm θ j b h (x-b • θ)
def moveCorrection (θ : X) (j : ℕ) (h : X → ℝ) (x : X) : ℝ :=
  -(∑ b∈Finset.range (j+1), ∑ r∈Finset.range b,moveTerm θ j b h (x-(r+1) • θ))
lemma moveTerm_continuous (θ : X) (j b : ℕ) {h : X → ℝ} (hc : Continuous h) : Continuous (moveTerm θ j b h) :=
  (partition_continuous θ j b).mul hc
lemma movedDrop_continuous (θ : X) (j : ℕ) {h : X → ℝ} (hc : Continuous h) : Continuous (movedDrop θ j h) := by
  apply continuous_finsetSum
  intro b _
  exact (moveTerm_continuous θ j b hc).comp (continuous_id.sub continuous_const)
lemma moveTerm_nonneg (θ : X) (j b : ℕ) {h : X → ℝ} (hh : ∀ x,0≤h x) (x : X) : 0≤ moveTerm θ j b h x :=
  mul_nonneg (partition_nonneg θ j b x) (hh x)
lemma movedDrop_nonneg (θ : X) (j : ℕ) {h : X → ℝ} (hh : ∀ x,0≤h x) (x : X) : 0≤ movedDrop θ j h x :=
  Finset.sum_nonneg (fun _ _ => moveTerm_nonneg _ _ _ hh _)
lemma movedDrop_zero_off (θ : X) (j : ℕ) (h : X → ℝ) (x : X) (hx : supportRadius θ j ≤ dist x 0) : movedDrop θ j h x=0 := by
  apply Finset.sum_eq_zero
  intro b _
  simp only [moveTerm,partition,sub_add_cancel,bump_eq_zero θ j x hx,zero_div,zero_mul]
lemma movedDrop_zero_lower (θ : X) (j : ℕ) {h : X → ℝ} (hh : ∀ x,0≤h x) : h 0/((j:ℝ)+1)≤ movedDrop θ j h 0 := by
  calc
    h 0/((j:ℝ)+1) = (1/((j:ℝ)+1))*h 0 := by ring
    _ ≤ partition θ j 0 0*h 0 := mul_le_mul_of_nonneg_right (partition_zero_lower θ j) (hh 0)
    _ = moveTerm θ j 0 h (0-0 • θ) := by simp [moveTerm]
    _ ≤ movedDrop θ j h 0 := Finset.single_le_sum (f := fun b => moveTerm θ j b h (0-b • θ)) (fun _ _ => moveTerm_nonneg θ j _ hh _) (by simp : 0∈Finset.range (j+1))


end CircleConcentration

end

end OAI
end


