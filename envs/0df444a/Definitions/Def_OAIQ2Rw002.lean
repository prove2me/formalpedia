-- Prove2me | Definitions.Def_OAIQ2Rw002
-- name    : OAIQ2Rw002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-25T22:12:08.873977+00:00
-- url     : https://prove2.me/theorems/945f86ca-c6a0-49f6-8ac3-b7e01c0f7541
-- title:
--   Definitions bundle OAIQ2Rw002 of the split of OpenAI, Invariant-projection counterexamples for every irrational rotation
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ContinuousCircleWeight.main_theorem`, carved from OpenAI's openai/math development (OpenAI, *Invariant-projection counterexamples for every irrational rotation*, OpenAI Math Release, September 27, 2026, result family 293, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 314 declarations of OpenAI's Lean: 89 definitions, 2 inductive types or structures, 1 instance and 222 theorems. The definitions and types are `OAI.CircleSampling.ActualSamples`, `OAI.CircleSampling.ConvolutionMasks`, `OAI.CircleSampling.ModelProjectionField`, `OAI.CircleSampling.actualCoordinate`, `OAI.CircleSampling.actualPairLaw`, `OAI.CircleSampling.actualSystem`, `OAI.CircleSampling.blockCoordinates`, `OAI.CircleSampling.blockEnd`, `OAI.CircleSampling.blockG`, `OAI.CircleSampling.blockH`, `OAI.CircleSampling.blockLength`, `OAI.CircleSampling.blockRange`, `OAI.CircleSampling.blockScale`, `OAI.CircleSampling.blockW`, `OAI.CircleSampling.blocks`, `OAI.CircleSampling.bridgeSize`, `OAI.CircleSampling.bridgeWidth`, `OAI.CircleSampling.chosenScaleStep`, `OAI.CircleSampling.circleProbability`, `OAI.CircleSampling.coefficientCap`, `OAI.CircleSampling.concentratedDrop`, `OAI.CircleSampling.convolutionError`, `OAI.CircleSampling.convolutionMasks`, `OAI.CircleSampling.coordinateBlock`, `OAI.CircleSampling.coordinateDrop`, `OAI.CircleSampling.coordinatePhase`, `OAI.CircleSampling.coordinateRadix`, `OAI.CircleSampling.crossingBudget`, `OAI.CircleSampling.crossingThreshold`, `OAI.CircleSampling.dropSize`, `OAI.CircleSampling.endpointBad`, `OAI.CircleSampling.finalWeight`, `OAI.CircleSampling.firstEndpoint`, `OAI.CircleSampling.frequency`, `OAI.CircleSampling.futureBad`, `OAI.CircleSampling.graphBad`, `OAI.CircleSampling.hybridEndpoint`, `OAI.CircleSampling.initialScaleState`, `OAI.CircleSampling.integerDrop`, `OAI.CircleSampling.lastEndpoint` and 51 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `RotationWeights_ActualDigits`, `RotationWeights_ContinuousWeight`, `RotationWeights_Convolution`, `RotationWeights_Discrepancy`, `RotationWeights_FiniteSampling`, `RotationWeights_FourierSampling`, `RotationWeights_GraphTransfer`, `RotationWeights_LaurentCoefficients`, `RotationWeights_LogarithmicDrops`, `RotationWeights_Main`, `RotationWeights_NestedAngles`, `RotationWeights_OrbitBounds`, `RotationWeights_Parameters`, `RotationWeights_PhaseWeights`, `RotationWeights_ProductSampling`, `RotationWeights_ProjectionIdentity`, `RotationWeights_RationalGraphs`, `RotationWeights_ReturnSamples`, `RotationWeights_SamplingBounds`, `RotationWeights_SamplingStage`, `RotationWeights_TaggedEvents`, `RotationWeights_TailBounds`, `RotationWeights_Thresholds`, `RotationWeights_TrialBounds`, `RotationWeights_WeakSampling`.
--
--   **Imports.** It imports the published bundle `Def_ContinuousCircleWeight`; the bundles `OAIQ2Rw000` and `OAIQ2Rw001` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI.CircleSampling.integrated_retained_bound` and `OAI.CircleSampling.model_no_strict_projection`; the proofs of `OAI.CircleSampling.integrated_retained_bound`, `OAI.CircleSampling.model_no_strict_projection` and `OAI.ContinuousCircleWeight.main_theorem`.
-- source:
--   OpenAI, Invariant-projection counterexamples for every irrational rotation, OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 293; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Invariant-projection-counterexamples-for-every-irrational-rotation-September-27-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_ContinuousCircleWeight
import Definitions.Def_OAIQ2Rw000
import Definitions.Def_OAIQ2Rw001

section
-- module Solutions.OAIQ2_Rot.RotationWeights_WeakSampling
attribute [-instance] _root_.OAI.CircleCoupling.labelMeasurableSpace
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

variable {ι : Type uι} [Fintype ι]

theorem torusFourier_add (a b : ι → ℤ) :
    torusFourier (a + b) = torusFourier a * torusFourier b := by
  ext x
  simp only [torusFourier_apply, Pi.add_apply, fourier_add, ContinuousMap.mul_apply]
  exact Finset.prod_mul_distrib

theorem torusFourier_neg (a : ι → ℤ) :
    torusFourier (-a) = star (torusFourier a) := by
  ext x
  change (∏ i, fourier (-a i) (x i)) = conj (∏ i, fourier (a i) (x i))
  simp only [fourier_neg, map_prod]

attribute [local instance] OAI.ContinuousCircleWeight.Sampling.instFactLtRealOfNat_solutions
def torusFourierSubalgebra : StarSubalgebra ℂ C(ι → CircleX, ℂ) where
  toSubalgebra := Algebra.adjoin ℂ (range torusFourier)
  star_mem' := by
    change Algebra.adjoin ℂ (range (torusFourier (ι := ι))) ≤
      star (Algebra.adjoin ℂ (range (torusFourier (ι := ι))))
    refine adjoin_le ?_
    rintro - ⟨a, rfl⟩
    exact subset_adjoin ⟨-a, torusFourier_neg a⟩

theorem torusFourierSubalgebra_coe :
    Subalgebra.toSubmodule (torusFourierSubalgebra (ι := ι)).toSubalgebra =
      span ℂ (range (torusFourier (ι := ι))) := by
  apply adjoin_eq_span_of_subset
  refine Subset.trans ?_ Submodule.subset_span
  intro x hx
  refine Submonoid.closure_induction (fun _ => id) ⟨0, torusFourier_zero⟩ ?_ hx
  rintro - - - - ⟨a, rfl⟩ ⟨b, rfl⟩
  exact ⟨a + b, torusFourier_add a b⟩

theorem torusFourier_single [DecidableEq ι] (i : ι) (x : ι → CircleX) :
    torusFourier (Pi.single i (1 : ℤ)) x = fourier 1 (x i) := by
  rw [torusFourier_apply, Finset.prod_eq_single i]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

theorem torusFourierSubalgebra_separatesPoints :
    (torusFourierSubalgebra (ι := ι)).SeparatesPoints := by
  classical
  intro x y hxy
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hxy
  refine ⟨_, ⟨torusFourier (Pi.single i 1), subset_adjoin ⟨_, rfl⟩, rfl⟩, ?_⟩
  change torusFourier (Pi.single i 1) x ≠ torusFourier (Pi.single i 1) y
  rw [torusFourier_single, torusFourier_single, fourier_one, fourier_one]
  intro h
  apply hi
  exact AddCircle.injective_toCircle (by norm_num) (Subtype.coe_injective h)

theorem span_torusFourier_closure_eq_top :
    (span ℂ (range (torusFourier (ι := ι)))).topologicalClosure = ⊤ := by
  rw [← torusFourierSubalgebra_coe]
  exact congrArg (Subalgebra.toSubmodule ∘ StarSubalgebra.toSubalgebra)
    (ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints
      torusFourierSubalgebra torusFourierSubalgebra_separatesPoints)

theorem integral_fourier (n : ℤ) :
    (∫ x : CircleX, fourier n x ∂AddCircle.haarAddCircle) = if n = 0 then 1 else 0 := by
  have h := congrFun (fourierCoeff_fourier (T := (1 : ℝ)) n) 0
  simpa [fourierCoeff, Pi.single_apply, eq_comm] using h

def circleHaar : ProbabilityMeasure CircleX :=
  ⟨AddCircle.haarAddCircle, inferInstance⟩

def torusHaar : ProbabilityMeasure (ι → CircleX) :=
  ⟨Measure.pi (fun _ => AddCircle.haarAddCircle), inferInstance⟩

theorem integral_torusFourier (a : ι → ℤ) :
    (∫ x, torusFourier a x ∂(torusHaar (ι := ι) : Measure (ι → CircleX))) =
      if a = 0 then 1 else 0 := by
  classical
  change (∫ x : ι → CircleX, ∏ i, fourier (a i) (x i)
    ∂Measure.pi (fun _ => AddCircle.haarAddCircle)) = _
  rw [integral_fintype_prod_eq_prod]
  simp_rw [integral_fourier]
  split_ifs with ha
  · subst a
    simp
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp ha
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simpa using hi

omit [Fintype ι] in
theorem fourier_sum (s : Finset ι) (a : ι → ℤ) (x : CircleX) :
    fourier (∑ i ∈ s, a i) x = ∏ i ∈ s, fourier (a i) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, fourier_add, ih]

theorem torusFourier_curve (a q : ι → ℤ) (x : CircleX) :
    torusFourier a (characterCurve q x) = fourier (∑ i, a i * q i) x := by
  rw [fourier_sum]
  apply Finset.prod_congr rfl
  intro i _
  simp only [characterCurve, ContinuousMap.coe_mk, fourier_apply, mul_zsmul]

def curveLaw (q : ι → ℤ) : ProbabilityMeasure (ι → CircleX) :=
  circleHaar.map (f := characterCurve q) (characterCurve q).continuous.measurable.aemeasurable

theorem integral_curveLaw (q : ι → ℤ) (f : C(ι → CircleX, ℂ)) :
    (∫ x, f x ∂(curveLaw q : Measure (ι → CircleX))) =
      ∫ x : CircleX, f (characterCurve q x) ∂AddCircle.haarAddCircle := by
  exact integral_map (characterCurve q).continuous.measurable.aemeasurable
    f.continuous.aestronglyMeasurable

theorem integral_curveLaw_torusFourier (q a : ι → ℤ) :
    (∫ x, torusFourier a x ∂(curveLaw q : Measure (ι → CircleX))) =
      if ∑ i, a i * q i = 0 then 1 else 0 := by
  rw [integral_curveLaw]
  simp_rw [torusFourier_curve]
  exact integral_fourier _

theorem eventually_sum_ne_zero_of_separated [LinearOrder ι]
    {κ : Type uκ} {l : Filter κ} (q : κ → ι → ℝ)
    (hq : ∀ n i, q n i ≠ 0)
    (hsep : ∀ i j, i < j → Tendsto (fun n => q n i / q n j) l (𝓝 0))
    (a : ι → ℝ) (ha : a ≠ 0) :
    ∀ᶠ n in l, ∑ i, a i * q n i ≠ 0 := by
  classical
  let s : Finset ι := Finset.univ.filter (fun i => a i ≠ 0)
  have hs : s.Nonempty := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp ha
    exact ⟨i, by simpa [s] using hi⟩
  let j := s.max' hs
  have hj : a j ≠ 0 := (Finset.mem_filter.mp (Finset.max'_mem s hs)).2
  have hlim (i : ι) : Tendsto (fun n => a i * q n i / q n j) l
      (𝓝 (if i = j then a j else 0)) := by
    by_cases hi : i = j
    · subst i
      simpa [hq] using (tendsto_const_nhds (x := a j) (f := l))
    · rw [ite_eq_right hi]
      by_cases hai : a i = 0
      · simpa [hai] using (tendsto_const_nhds (x := (0 : ℝ)) (f := l))
      · have his : i ∈ s := by simp [s, hai]
        have hij : i < j := lt_of_le_of_ne (Finset.le_max' s i his) hi
        simpa only [mul_zero, mul_div_assoc] using (hsep i j hij).const_mul (a i)
  have hsum := tendsto_finsetSum Finset.univ (fun i _ => hlim i)
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true] at hsum
  filter_upwards [hsum.eventually_ne hj] with n hn
  intro he
  apply hn
  rw [← Finset.sum_div, he, zero_div]

theorem curveLaw_tendsto_of_nonresonance {κ : Type uκ} {l : Filter κ}
    {q : κ → ι → ℤ}
    (h : ∀ a : ι → ℤ, a ≠ 0 → ∀ᶠ n in l, ∑ i, a i * q n i ≠ 0) :
    Tendsto (fun n => curveLaw (q n)) l (𝓝 (torusHaar (ι := ι))) := by
  apply probability_tendsto_of_dense_span l (Set.range torusFourier)
    span_torusFourier_closure_eq_top
  rintro _ ⟨a, rfl⟩
  simp_rw [integral_curveLaw_torusFourier, integral_torusFourier]
  by_cases ha : a = 0
  · subst a
    simpa using (tendsto_const_nhds (x := (1 : ℂ)))
  · rw [ite_eq_right ha]
    apply tendsto_const_nhds.congr'
    filter_upwards [h a ha] with n hn
    simp [hn]

theorem curveLaw_tendsto_of_separated [LinearOrder ι]
    {κ : Type uκ} {l : Filter κ} {q : κ → ι → ℤ}
    (hq : ∀ n i, q n i ≠ 0)
    (hsep : ∀ i j, i < j →
      Tendsto (fun n => (q n i : ℝ) / q n j) l (𝓝 0)) :
    Tendsto (fun n => curveLaw (q n)) l (𝓝 (torusHaar (ι := ι))) := by
  apply curveLaw_tendsto_of_nonresonance
  intro a ha
  have har : (fun i => (a i : ℝ)) ≠ 0 := by
    intro he
    apply ha
    ext i
    have hh : (a i : ℝ) = 0 := congrFun he i
    change a i = 0
    exact_mod_cast hh
  have hqr : ∀ n i, (q n i : ℝ) ≠ 0 := by
    intro n i
    exact_mod_cast hq n i
  filter_upwards [eventually_sum_ne_zero_of_separated
    (fun n i => (q n i : ℝ)) hqr hsep (fun i => (a i : ℝ)) har] with n hn
  exact_mod_cast hn

theorem curveLaw_tendsto_of_successiveRatios {κ : Type uκ} {l : Filter κ} {r : ℕ}
    (q : κ → ℕ → ℤ) (hq : ∀ n i, i < r → 0 < q n i)
    (hsep : ∀ i, i + 1 < r →
      Tendsto (fun n => (q n (i + 1) : ℝ) / q n i) l atTop) :
    Tendsto (fun n => curveLaw (fun i : Fin r => q n i)) l (𝓝 (torusHaar (ι := Fin r))) := by
  apply curveLaw_tendsto_of_separated
  · intro n i
    exact ne_of_gt (hq n i i.isLt)
  · intro i j hij
    apply separated_of_successive (fun n i => (q n i : ℝ)) _ hsep i j hij j.isLt
    intro n i hi
    exact_mod_cast ne_of_gt (hq n i hi)

theorem circle_approximation_with_parameters
    {P : Type uP} [MetricSpace P] [CompactSpace P] [MeasurableSpace P] [BorelSpace P]
    {κ : Type uκ} {l : Filter κ} [l.IsCountablyGenerated] {r : ℕ}
    (q : κ → ℕ → ℤ) (hq : ∀ n i, i < r → 0 < q n i)
    (hsep : ∀ i, i + 1 < r →
      Tendsto (fun n => (q n (i + 1) : ℝ) / q n i) l atTop)
    {bs : κ → P} {b : P} (hb : Tendsto bs l (𝓝 b))
    (Φ : ((Fin r → CircleX) × P) → ℂ) (hΦ : Measurable Φ)
    (hc : ∀ᵐ z ∂(withParameter (torusHaar (ι := Fin r)) b : Measure _), ContinuousAt Φ z)
    (M : ℝ) (hM : ∀ z, ‖Φ z‖ ≤ M) :
    Tendsto (fun n => ∫ x : CircleX, Φ (characterCurve (fun i : Fin r => q n i) x, bs n)
      ∂AddCircle.haarAddCircle) l
      (𝓝 (∫ s, Φ (s, b) ∂(torusHaar (ι := Fin r) : Measure _))) := by
  have hν := probability_tendsto_withParameter (curveLaw_tendsto_of_successiveRatios q hq hsep) hb
  have h := tendsto_integral_complex_of_weak_of_ae_continuous
    (fun n => withParameter (curveLaw (fun i : Fin r => q n i)) (bs n))
    (withParameter (torusHaar (ι := Fin r)) b) hν Φ hΦ hc M hM
  have heq (ν : ProbabilityMeasure (Fin r → CircleX)) (b : P) :
      (∫ z, Φ z ∂(withParameter ν b : Measure _)) = ∫ s, Φ (s, b) ∂(ν : Measure _) :=
    integral_map (measurable_id.prodMk measurable_const).aemeasurable hΦ.aestronglyMeasurable
  simp_rw [heq] at h
  have heq' (n : κ) : (∫ s, Φ (s, bs n) ∂(curveLaw (fun i : Fin r => q n i) : Measure _)) =
      ∫ x : CircleX, Φ (characterCurve (fun i : Fin r => q n i) x, bs n)
        ∂AddCircle.haarAddCircle :=
    integral_map (characterCurve _).continuous.measurable.aemeasurable
      (hΦ.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  simpa only [heq'] using h

end Sampling
end ContinuousCircleWeight

end

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_FourierSampling
attribute [-instance] _root_.OAI.CircleCoupling.labelMeasurableSpace
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

lemma fejerKernel_nonneg (H : ℕ) (x : CircleX) : 0 ≤ fejerKernel H x := by
  rw [fejerKernel_apply]; positivity

lemma integral_fourier_exact (n : ℤ) :
    (∫ x : CircleX, fourier n x ∂AddCircle.haarAddCircle) = if n = 0 then 1 else 0 := by
  have h := congrFun (fourierCoeff_fourier (T := (1 : ℝ)) n) 0
  simpa [fourierCoeff, Pi.single_apply, eq_comm] using h

lemma fejerKernel_complex_expansion (H : ℕ) (x : CircleX) :
    (fejerKernel H x : ℂ) = (H : ℂ)⁻¹ *
      ∑ p ∈ Finset.range H, ∑ q ∈ Finset.range H, fourier ((p : ℤ) - q) x := by
  rw [fejerKernel_apply, Complex.ofReal_div, Complex.ofReal_pow,
    ← Complex.mul_conj', geometricFourierSum_apply]
  simp only [map_sum]
  rw [Finset.sum_mul_sum]
  simp_rw [← fourier_neg, ← fourier_add, ← sub_eq_add_neg]
  simp only [Complex.ofReal_natCast, div_eq_mul_inv, mul_comm]

lemma integral_fejerKernel {H : ℕ} (hH : 0 < H) :
    (∫ x : CircleX, fejerKernel H x ∂AddCircle.haarAddCircle) = 1 := by
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  simp_rw [fejerKernel_complex_expansion]
  have hi (n : ℤ) : Integrable (fun x : CircleX => fourier n x) AddCircle.haarAddCircle :=
    Integrable.of_bound (fourier _).continuous.aestronglyMeasurable 1
      (ae_of_all _ (fun x => by simp [fourier_apply, Circle.norm_coe]))
  have hs (p : ℕ) : Integrable (fun x : CircleX => ∑ q ∈ Finset.range H,
      fourier ((p : ℤ) - q) x) AddCircle.haarAddCircle :=
    integrable_finsetSum _ (fun _ _ => hi _)
  rw [integral_const_mul, integral_finsetSum _ (fun _ _ => hs _)]
  simp_rw [integral_finsetSum _ (fun _ _ => hi _), integral_fourier_exact]
  simp only [sub_eq_zero, Int.natCast_inj]
  simp
  rw [Finset.filter_eq_self.mpr (fun a ha => Finset.mem_range.mp ha)]
  simp [hH.ne']

lemma fourier_nat_eq_pow (p : ℕ) (x : CircleX) :
    fourier (p : ℤ) x = fourier 1 x ^ p := by
  induction p with
  | zero => simp
  | succ p ih => rw [Nat.cast_add, Nat.cast_one, fourier_add, ih, pow_succ]

lemma geometricFourierSum_mul (H : ℕ) (x : CircleX) :
    geometricFourierSum H x * (fourier 1 x - 1) = fourier (H : ℤ) x - 1 := by
  simp_rw [geometricFourierSum_apply, fourier_nat_eq_pow]
  exact geom_sum_mul _ _

lemma fejerKernel_mul_chord_sq_le (H : ℕ) (x : CircleX) :
    fejerKernel H x * ‖fourier 1 x - 1‖ ^ 2 ≤ 4 / H := by
  have h := congrArg norm (geometricFourierSum_mul H x)
  rw [norm_mul] at h
  have hn : ‖fourier (H : ℤ) x - 1‖ ≤ 2 := by
    simpa only [fourier_apply, Circle.norm_coe, norm_one, one_add_one_eq_two] using norm_sub_le (fourier (H : ℤ) x) (1 : ℂ)
  rw [fejerKernel_apply]
  have hs : ‖geometricFourierSum H x‖ ^ 2 * ‖fourier 1 x - 1‖ ^ 2 ≤ 4 := by
    rw [← mul_pow, h]
    nlinarith [norm_nonneg (fourier (H : ℤ) x - 1)]
  simpa only [div_mul_eq_mul_div] using div_le_div_of_nonneg_right hs (Nat.cast_nonneg H : (0 : ℝ) ≤ H)

lemma fourier_one_chord_lower (x : CircleX) :
    4 * ‖x‖ ≤ ‖fourier 1 x - 1‖ := by
  let y : ℝ := (AddCircle.equivIco (1 : ℝ) (-(1 / 2 : ℝ)) x).val
  have hy : |y| ≤ 1 / 2 := by
    have he := (AddCircle.equivIco (1 : ℝ) (-(1 / 2 : ℝ)) x).property
    change -(1 / 2 : ℝ) ≤ y ∧ y < -(1 / 2 : ℝ) + 1 at he
    rw [abs_le]; constructor <;> linarith [he.1, he.2]
  have hc : (y : CircleX) = x := AddCircle.coe_equivIco
  have hn : ‖(y : CircleX)‖ = |y| :=
    (AddCircle.norm_coe_eq_abs_iff (1 : ℝ) (by norm_num)).mpr (by simpa using hy)
  rw [← hc, hn, fourier_coe_apply]
  have he : (2 * Real.pi * Complex.I * (1 : ℤ) * y / (1 : ℝ) : ℂ) =
      Complex.I * (2 * Real.pi * y : ℝ) := by push_cast; ring
  rw [he, Complex.norm_exp_I_mul_ofReal_sub_one]
  have hyπ : 0 ≤ Real.pi * |y| := mul_nonneg Real.pi_pos.le (abs_nonneg y)
  have hle : Real.pi * |y| ≤ Real.pi / 2 := by nlinarith [Real.pi_pos]
  have hs := Real.mul_le_sin hyπ hle
  have hs' : 2 * |y| ≤ Real.sin (Real.pi * |y|) := by
    convert hs using 1; field_simp
  have ha : |Real.pi * y| ≤ Real.pi := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_pos]
  have he' : 2 * Real.pi * y / 2 = Real.pi * y := by ring
  rw [he', Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
    Real.abs_sin_eq_sin_abs_of_abs_le_pi ha, abs_mul, abs_of_pos Real.pi_pos]
  linarith

lemma fejerKernel_le_of_norm_ge {H : ℕ} (hH : 0 < H)
    {δ : ℝ} (hδ : 0 < δ) {x : CircleX} (hx : δ ≤ ‖x‖) :
    fejerKernel H x ≤ 1 / (4 * H * δ ^ 2) := by
  have hc := fourier_one_chord_lower x
  have hk := fejerKernel_mul_chord_sq_le H x
  have hn := fejerKernel_nonneg H x
  have hH' : (0 : ℝ) < H := Nat.cast_pos.mpr hH
  have hs : 16 * δ ^ 2 ≤ ‖fourier 1 x - 1‖ ^ 2 := by
    nlinarith [norm_nonneg x, norm_nonneg (fourier 1 x - 1)]
  have hprod : fejerKernel H x * (16 * δ ^ 2) ≤ 4 / H :=
    (mul_le_mul_of_nonneg_left hs hn).trans hk
  apply (le_div_iff₀ (by positivity : 0 < 4 * (H : ℝ) * δ ^ 2)).mpr
  have hm := (le_div_iff₀ hH').mp hprod
  nlinarith

lemma fourier_eval_sub (n : ℤ) (x t : CircleX) :
    fourier n (x - t) = fourier n x * fourier (-n) t := by
  simp only [fourier_apply, sub_eq_add_neg, zsmul_add, zsmul_neg, neg_zsmul,
    AddCircle.toCircle_add, Circle.coe_mul]

lemma fejerKernel_le (H : ℕ) (x : CircleX) : fejerKernel H x ≤ H := by
  have hs : ‖geometricFourierSum H x‖ ≤ H := by
    rw [geometricFourierSum_apply]
    calc
      _ ≤ ∑ p ∈ Finset.range H, ‖fourier (p : ℤ) x‖ := norm_sum_le _ _
      _ = H := by simp [fourier_apply, Circle.norm_coe]
  by_cases hH : H = 0
  · simp [hH]
  · rw [fejerKernel_apply, div_le_iff₀ (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hH))]
    nlinarith [norm_nonneg (geometricFourierSum H x)]

lemma integrable_fejer_mul (H : ℕ) {f : CircleX → ℝ}
    (hf : Integrable f AddCircle.haarAddCircle) (x : CircleX) :
    Integrable (fun t => fejerKernel H (x - t) * f t) AddCircle.haarAddCircle := by
  apply hf.bdd_mul (c := (H : ℝ)) (by fun_prop : Continuous (fun t : CircleX => fejerKernel H (x - t))).aestronglyMeasurable
  exact ae_of_all _ (fun t => by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (fejerKernel_nonneg H _)] using
      fejerKernel_le H (x - t))

def fejerApprox (H : ℕ) (f : CircleX → ℝ) (x : CircleX) : ℝ :=
  ∫ t, fejerKernel H (x - t) * f t ∂AddCircle.haarAddCircle

lemma fejerApprox_complex_expansion (H : ℕ) {f : CircleX → ℝ}
    (hf : Integrable f AddCircle.haarAddCircle) (x : CircleX) :
    (fejerApprox H f x : ℂ) = (H : ℂ)⁻¹ *
      ∑ p ∈ Finset.range H, ∑ q ∈ Finset.range H,
        fourier ((p : ℤ) - q) x * fourierCoeff (fun t => (f t : ℂ)) ((p : ℤ) - q) := by
  have hf' : Integrable (fun t => (f t : ℂ)) AddCircle.haarAddCircle := hf.ofReal
  have hi (n : ℤ) : Integrable (fun t => fourier n (x - t) * (f t : ℂ))
      AddCircle.haarAddCircle := by
    apply hf'.bdd_mul (c := 1) (by fun_prop : Continuous (fun t : CircleX => fourier n (x - t))).aestronglyMeasurable
    exact ae_of_all _ (fun t => by simp [fourier_apply, Circle.norm_coe])
  have he (n : ℤ) : (∫ t, fourier n (x - t) * (f t : ℂ) ∂AddCircle.haarAddCircle) =
      fourier n x * fourierCoeff (fun t => (f t : ℂ)) n := by
    simp_rw [fourier_eval_sub, mul_assoc]
    rw [integral_const_mul]
    rfl
  rw [fejerApprox, ← integral_complex_ofReal]
  simp_rw [Complex.ofReal_mul, fejerKernel_complex_expansion,
    mul_assoc, Finset.sum_mul]
  rw [integral_const_mul, integral_finsetSum (Finset.range H) (fun p _ =>
    integrable_finsetSum (Finset.range H) (fun q _ => hi ((p : ℤ) - q)))]
  simp_rw [integral_finsetSum (Finset.range H) (fun q _ => hi _), he]

lemma fejerApprox_nonneg (H : ℕ) {f : CircleX → ℝ} (hf : ∀ t, 0 ≤ f t)
    (x : CircleX) : 0 ≤ fejerApprox H f x := by
  exact integral_nonneg (fun t => mul_nonneg (fejerKernel_nonneg H _) (hf t))

lemma fejerApprox_le_one {H : ℕ} (hH : 0 < H) {f : CircleX → ℝ}
    (hf : Integrable f AddCircle.haarAddCircle) (hf1 : ∀ t, f t ≤ 1) (x : CircleX) :
    fejerApprox H f x ≤ 1 := by
  have hk : Integrable (fun t : CircleX => fejerKernel H t) AddCircle.haarAddCircle :=
    Integrable.of_bound (fejerKernel H).continuous.aestronglyMeasurable H
      (ae_of_all _ (fun t => by
        simpa only [Real.norm_eq_abs, abs_of_nonneg (fejerKernel_nonneg H _)] using
          fejerKernel_le H t))
  calc
    _ ≤ ∫ t : CircleX, fejerKernel H (x - t) ∂AddCircle.haarAddCircle :=
      integral_mono (integrable_fejer_mul H hf x) (hk.comp_sub_left x)
        (fun t => by simpa using mul_le_mul_of_nonneg_left (hf1 t) (fejerKernel_nonneg H _))
    _ = 1 := by rw [integral_sub_left_eq_self, integral_fejerKernel hH]

lemma fejerApprox_local_error {H : ℕ} (hH : 0 < H) {δ : ℝ} (hδ : 0 < δ)
    {f : CircleX → ℝ} (hf : Integrable f AddCircle.haarAddCircle)
    (hbound : ∀ t, 0 ≤ f t ∧ f t ≤ 1) (x : CircleX)
    (hloc : ∀ t, ‖x - t‖ < δ → f t = f x) :
    |fejerApprox H f x - f x| ≤ 1 / (4 * H * δ ^ 2) := by
  have hk : Integrable (fun t : CircleX => fejerKernel H t) AddCircle.haarAddCircle :=
    Integrable.of_bound (fejerKernel H).continuous.aestronglyMeasurable H
      (ae_of_all _ (fun t => by
        simpa only [Real.norm_eq_abs, abs_of_nonneg (fejerKernel_nonneg H _)] using
          fejerKernel_le H t))
  have he : fejerApprox H f x - f x =
      ∫ t, fejerKernel H (x - t) * (f t - f x) ∂AddCircle.haarAddCircle := by
    simp_rw [mul_sub]
    rw [integral_sub (integrable_fejer_mul H hf x) ((hk.comp_sub_left x).mul_const _),
      integral_mul_const, integral_sub_left_eq_self, integral_fejerKernel hH, one_mul]
    rfl
  rw [he, ← Real.norm_eq_abs]
  apply (norm_integral_le_integral_norm _).trans
  have hb (t : CircleX) : ‖fejerKernel H (x - t) * (f t - f x)‖ ≤
      1 / (4 * H * δ ^ 2) := by
    by_cases ht : ‖x - t‖ < δ
    · rw [hloc t ht, sub_self, mul_zero, norm_zero]; positivity
    · have hd : |f t - f x| ≤ 1 := by rw [abs_le]; constructor <;> linarith [(hbound t).1, (hbound t).2, (hbound x).1, (hbound x).2]
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (fejerKernel_nonneg H _), Real.norm_eq_abs]
      exact (mul_le_mul_of_nonneg_left hd (fejerKernel_nonneg H _)).trans
        (by simpa using fejerKernel_le_of_norm_ge hH hδ (le_of_not_gt ht))
  calc
    _ ≤ ∫ _t : CircleX, 1 / (4 * (H : ℝ) * δ ^ 2) ∂AddCircle.haarAddCircle :=
      integral_mono ((integrable_fejer_mul H (hf.sub (integrable_const _)) x).norm)
        (integrable_const _) hb
    _ = _ := by simp

def doubleFourier (v w : ℤ) (z : CircleX × CircleX) : ℂ :=
  fourier v z.1 * fourier w z.2

lemma doubleFourier_norm (v w : ℤ) (z : CircleX × CircleX) :
    ‖doubleFourier v w z‖ = 1 := by
  simp [doubleFourier, fourier_apply, Circle.norm_coe]

lemma integrable_doubleFourier (v w : ℤ) (η : Measure (CircleX × CircleX))
    [IsFiniteMeasure η] : Integrable (doubleFourier v w) η := by
  apply Integrable.of_bound (by unfold doubleFourier; fun_prop : Continuous (doubleFourier v w)).aestronglyMeasurable 1
  exact ae_of_all _ (fun z => (doubleFourier_norm v w z).le)

lemma finite_doubleFourier_error {ι : Type uι} (s : Finset ι) (c : ι → ℂ)
    (v w : ι → ℤ) (η : Measure (CircleX × CircleX)) [IsFiniteMeasure η]
    (ε : ℝ) (hmom : ∀ i ∈ s,
      ‖(∫ z, doubleFourier (v i) (w i) z ∂η) -
        (if v i = 0 ∧ w i = 0 then 1 else 0)‖ ≤ ε) :
    ‖(∫ z, ∑ i ∈ s, c i * doubleFourier (v i) (w i) z ∂η) -
      ∑ i ∈ s, (if v i = 0 ∧ w i = 0 then c i else 0)‖ ≤
        ε * ∑ i ∈ s, ‖c i‖ := by
  classical
  rw [integral_finsetSum s (fun i _ => (integrable_doubleFourier _ _ η).const_mul _)]
  simp_rw [integral_const_mul]
  have he : (∑ i ∈ s, c i * ∫ z, doubleFourier (v i) (w i) z ∂η) -
      ∑ i ∈ s, (if v i = 0 ∧ w i = 0 then c i else 0) =
      ∑ i ∈ s, c i * ((∫ z, doubleFourier (v i) (w i) z ∂η) -
        (if v i = 0 ∧ w i = 0 then 1 else 0)) := by
    simp_rw [mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero]
  rw [he]
  calc
    _ ≤ ∑ i ∈ s, ‖c i * ((∫ z, doubleFourier (v i) (w i) z ∂η) -
        (if v i = 0 ∧ w i = 0 then 1 else 0))‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ s, ‖c i‖ * ε := Finset.sum_le_sum (fun i hi => by
      rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hmom i hi) (norm_nonneg _))
    _ = _ := by rw [← Finset.sum_mul, mul_comm]

lemma finite_product_fourier_error {ι : Type uι} {κ : Type uκ} (s : Finset ι) (t : Finset κ)
    (a : ι → ℂ) (b : κ → ℂ) (v : ι → ℤ) (w : κ → ℤ)
    (η : Measure (CircleX × CircleX)) [IsFiniteMeasure η]
    (ε : ℝ) (hmom : ∀ i ∈ s, ∀ k ∈ t,
      ‖(∫ z, doubleFourier (v i) (w k) z ∂η) -
        (if v i = 0 ∧ w k = 0 then 1 else 0)‖ ≤ ε) :
    ‖(∫ z, (∑ i ∈ s, a i * fourier (v i) z.1) *
        (∑ k ∈ t, b k * fourier (w k) z.2) ∂η) -
      (∑ i ∈ s, if v i = 0 then a i else 0) *
        (∑ k ∈ t, if w k = 0 then b k else 0)‖ ≤
      ε * (∑ i ∈ s, ‖a i‖) * ∑ k ∈ t, ‖b k‖ := by
  classical
  have h := finite_doubleFourier_error (s.product t) (fun ik => a ik.1 * b ik.2)
    (fun ik => v ik.1) (fun ik => w ik.2) η ε
    (fun ik hik => hmom ik.1 (Finset.mem_product.mp hik).1 ik.2 (Finset.mem_product.mp hik).2)
  have hi (i : ι) (k : κ) (z : CircleX × CircleX) :
      (a i * b k) * doubleFourier (v i) (w k) z =
      (a i * fourier (v i) z.1) * (b k * fourier (w k) z.2) := by
    unfold doubleFourier; ring
  have hz (i : ι) (k : κ) :
      (if v i = 0 ∧ w k = 0 then a i * b k else 0) =
      (if v i = 0 then a i else 0) * (if w k = 0 then b k else 0) := by
    split_ifs <;> simp_all
  simp only [hi, hz, norm_mul] at h
  simp only [Finset.product_eq_sprod, Finset.sum_product] at h
  simp_rw [← Finset.sum_mul_sum] at h
  simpa only [mul_assoc] using h

lemma fourierCoeff_norm_le_one {f : CircleX → ℂ}
    (hf : Integrable f AddCircle.haarAddCircle) (hb : ∀ x, ‖f x‖ ≤ 1) (n : ℤ) :
    ‖fourierCoeff f n‖ ≤ 1 := by
  unfold fourierCoeff
  calc
    _ ≤ ∫ x, ‖fourier (-n) x • f x‖ ∂AddCircle.haarAddCircle := norm_integral_le_integral_norm _
    _ ≤ ∫ _x : CircleX, (1 : ℝ) ∂AddCircle.haarAddCircle :=
      integral_mono ((hf.fourier_smul _).norm) (integrable_const _) (fun x => by
        simpa only [norm_smul, fourier_apply, Circle.norm_coe, one_mul] using hb x)
    _ = 1 := by simp

def fejerCoefficient (H : ℕ) (f : CircleX → ℝ) (i : Fin H × Fin H) : ℂ :=
  (H : ℂ)⁻¹ * fourierCoeff (fun t => (f t : ℂ)) (fejerFrequency i)

lemma fejerApprox_fin_expansion (H : ℕ) {f : CircleX → ℝ}
    (hf : Integrable f AddCircle.haarAddCircle) (x : CircleX) :
    (fejerApprox H f x : ℂ) = ∑ i : Fin H × Fin H,
      fejerCoefficient H f i * fourier (fejerFrequency i) x := by
  rw [fejerApprox_complex_expansion H hf]
  simp only [Fintype.sum_prod_type, fejerCoefficient, fejerFrequency]
  simp_rw [mul_assoc, mul_comm (fourierCoeff _ _) (fourier _ _), ← Finset.mul_sum]
  congr 1
  have hs (p : ℕ) : (∑ q : Fin H, fourier ((p : ℤ) - (q : ℕ)) x *
      fourierCoeff (fun t => (f t : ℂ)) ((p : ℤ) - (q : ℕ))) =
      ∑ q ∈ Finset.range H, fourier ((p : ℤ) - q) x *
      fourierCoeff (fun t => (f t : ℂ)) ((p : ℤ) - q) :=
    Fin.sum_univ_eq_sum_range (fun q : ℕ => fourier ((p : ℤ) - q) x *
      fourierCoeff (fun t => (f t : ℂ)) ((p : ℤ) - q)) H
  simp_rw [hs]
  exact (Fin.sum_univ_eq_sum_range (fun p : ℕ => ∑ q ∈ Finset.range H,
    fourier ((p : ℤ) - q) x * fourierCoeff (fun t => (f t : ℂ)) ((p : ℤ) - q)) H).symm

lemma fejerCoefficient_zero_sum {H : ℕ} (hH : 0 < H) (f : CircleX → ℝ) :
    (∑ i : Fin H × Fin H, if fejerFrequency i = 0 then fejerCoefficient H f i else 0) =
      ∫ t, (f t : ℂ) ∂AddCircle.haarAddCircle := by
  simp only [Fintype.sum_prod_type, fejerFrequency, fejerCoefficient, sub_eq_zero,
    Int.natCast_inj, Fin.val_inj]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, sub_self,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast hH.ne'), one_mul]
  simp [fourierCoeff]

lemma fejerCoefficient_norm_sum_le {H : ℕ} (hH : 0 < H) {f : CircleX → ℝ}
    (hf : Integrable f AddCircle.haarAddCircle) (hb : ∀ t, |f t| ≤ 1) :
    (∑ i : Fin H × Fin H, ‖fejerCoefficient H f i‖) ≤ H := by
  have hf' : Integrable (fun t => (f t : ℂ)) AddCircle.haarAddCircle := hf.ofReal
  have hcoef (i : Fin H × Fin H) : ‖fejerCoefficient H f i‖ ≤ (H : ℝ)⁻¹ := by
    unfold fejerCoefficient
    rw [norm_mul, norm_inv, Complex.norm_natCast]
    simpa using mul_le_mul_of_nonneg_left (fourierCoeff_norm_le_one hf'
      (fun t => by simpa using hb t) (fejerFrequency i)) (inv_nonneg.mpr (Nat.cast_nonneg H))
  calc
    _ ≤ ∑ _i : Fin H × Fin H, (H : ℝ)⁻¹ := Finset.sum_le_sum (fun i _ => hcoef i)
    _ = (H : ℝ) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod,
        Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul]
      rw [mul_assoc, mul_inv_cancel₀ (by exact_mod_cast hH.ne'), mul_one]

lemma fejer_product_fourier_error {H : ℕ} (hH : 0 < H)
    {f g : CircleX → ℝ} (hf : Integrable f AddCircle.haarAddCircle)
    (hg : Integrable g AddCircle.haarAddCircle)
    (hfb : ∀ x, |f x| ≤ 1) (hgb : ∀ x, |g x| ≤ 1)
    (η : Measure (CircleX × CircleX)) [IsProbabilityMeasure η]
    {ε : ℝ} (hε : 0 ≤ ε)
    (hmom : ∀ v w : ℤ, |v| < H → |w| < H → ¬(v = 0 ∧ w = 0) →
      ‖∫ z, doubleFourier v w z ∂η‖ ≤ ε) :
    ‖(∫ z, (fejerApprox H f z.1 : ℂ) * (fejerApprox H g z.2 : ℂ) ∂η) -
      (∫ t, (f t : ℂ) ∂AddCircle.haarAddCircle) *
      (∫ t, (g t : ℂ) ∂AddCircle.haarAddCircle)‖ ≤ H ^ 2 * ε := by
  classical
  have hm (i k : Fin H × Fin H) :
      ‖(∫ z, doubleFourier (fejerFrequency i) (fejerFrequency k) z ∂η) -
        (if fejerFrequency i = 0 ∧ fejerFrequency k = 0 then 1 else 0)‖ ≤ ε := by
    by_cases hz : fejerFrequency i = 0 ∧ fejerFrequency k = 0
    · simpa [hz.1, hz.2, doubleFourier, fourier_zero, measure_univ] using hε
    · simpa [hz] using hmom _ _ (fejerFrequency_abs_lt i) (fejerFrequency_abs_lt k) hz
  have h := finite_product_fourier_error Finset.univ Finset.univ
    (fejerCoefficient H f) (fejerCoefficient H g) fejerFrequency fejerFrequency η ε
    (fun i _ k _ => hm i k)
  simp_rw [← fejerApprox_fin_expansion H hf, ← fejerApprox_fin_expansion H hg,
    fejerCoefficient_zero_sum hH] at h
  refine h.trans ?_
  calc
    _ ≤ ε * (H : ℝ) * H := mul_le_mul
      (mul_le_mul_of_nonneg_left (fejerCoefficient_norm_sum_le hH hf hfb) hε)
      (fejerCoefficient_norm_sum_le hH hg hgb)
      (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) (by positivity)
    _ = _ := by ring

lemma continuous_fejerApprox (H : ℕ) {f : CircleX → ℝ}
    (hf : Integrable f AddCircle.haarAddCircle) : Continuous (fejerApprox H f) := by
  have he : fejerApprox H f = fun x =>
      (∑ i : Fin H × Fin H, fejerCoefficient H f i * fourier (fejerFrequency i) x).re := by
    funext x
    rw [← fejerApprox_fin_expansion H hf x]
    rfl
  rw [he]
  exact Complex.continuous_re.comp (continuous_finsetSum _
    (fun i _ => continuous_const.mul (fourier (fejerFrequency i)).continuous))

lemma fejer_unsmoothed_error {H : ℕ} (hH : 0 < H) {δ : ℝ} (hδ : 0 < δ)
    {f g : CircleX → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hfb : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (hgb : ∀ x, 0 ≤ g x ∧ g x ≤ 1)
    (Bf Bg : Set CircleX) (hBf : MeasurableSet Bf) (hBg : MeasurableSet Bg)
    (hfloc : ∀ x ∉ Bf, ∀ t, ‖x - t‖ < δ → f t = f x)
    (hgloc : ∀ x ∉ Bg, ∀ t, ‖x - t‖ < δ → g t = g x)
    (η : Measure (CircleX × CircleX)) [IsProbabilityMeasure η] :
    |(∫ z, f z.1 * g z.2 ∂η) -
      (∫ z, fejerApprox H f z.1 * fejerApprox H g z.2 ∂η)| ≤
      η.real (Prod.fst ⁻¹' Bf) + η.real (Prod.snd ⁻¹' Bg) + 2 / (4 * H * δ ^ 2) := by
  have hfi : Integrable f AddCircle.haarAddCircle :=
    Integrable.of_bound hf.aestronglyMeasurable 1
      (ae_of_all _ (fun x => by simpa [Real.norm_eq_abs, abs_of_nonneg (hfb x).1] using (hfb x).2))
  have hgi : Integrable g AddCircle.haarAddCircle :=
    Integrable.of_bound hg.aestronglyMeasurable 1
      (ae_of_all _ (fun x => by simpa [Real.norm_eq_abs, abs_of_nonneg (hgb x).1] using (hgb x).2))
  have hF (x : CircleX) : 0 ≤ fejerApprox H f x ∧ fejerApprox H f x ≤ 1 :=
    ⟨fejerApprox_nonneg H (fun t => (hfb t).1) x,
      fejerApprox_le_one hH hfi (fun t => (hfb t).2) x⟩
  have hG (x : CircleX) : 0 ≤ fejerApprox H g x ∧ fejerApprox H g x ≤ 1 :=
    ⟨fejerApprox_nonneg H (fun t => (hgb t).1) x,
      fejerApprox_le_one hH hgi (fun t => (hgb t).2) x⟩
  have hir : Integrable (fun z : CircleX × CircleX => f z.1 * g z.2) η :=
    Integrable.of_bound ((hf.comp measurable_fst).mul (hg.comp measurable_snd)).aestronglyMeasurable 1
      (ae_of_all _ (fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hfb z.1).1 (hgb z.2).1)]
        exact (mul_le_of_le_one_left (hgb z.2).1 (hfb z.1).2).trans (hgb z.2).2))
  have his : Integrable (fun z : CircleX × CircleX =>
      fejerApprox H f z.1 * fejerApprox H g z.2) η :=
    Integrable.of_bound (((continuous_fejerApprox H hfi).comp continuous_fst).mul
      ((continuous_fejerApprox H hgi).comp continuous_snd)).aestronglyMeasurable 1
      (ae_of_all _ (fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hF z.1).1 (hG z.2).1)]
        exact (mul_le_of_le_one_left (hG z.2).1 (hF z.1).2).trans (hG z.2).2))
  have hdefect (u : CircleX → ℝ) (hu : Integrable u AddCircle.haarAddCircle)
      (hb : ∀ x, 0 ≤ u x ∧ u x ≤ 1) (B : Set CircleX)
      (hloc : ∀ x ∉ B, ∀ t, ‖x-t‖ < δ → u t = u x) (x : CircleX) :
      |u x - fejerApprox H u x| ≤ B.indicator (fun _ => (1 : ℝ)) x +
        1 / (4 * H * δ ^ 2) := by
    by_cases hx : x ∈ B
    · rw [Set.indicator_of_mem hx]
      have hnonneg := fejerApprox_nonneg H (fun t => (hb t).1) x
      have hone := fejerApprox_le_one hH hu (fun t => (hb t).2) x
      have : |u x - fejerApprox H u x| ≤ 1 := by rw [abs_le]; constructor <;> linarith [(hb x).1, (hb x).2]
      exact this.trans (le_add_of_nonneg_right (by positivity))
    · rw [Set.indicator_of_notMem hx, zero_add, abs_sub_comm]
      exact fejerApprox_local_error hH hδ hu hb x (hloc x hx)
  have hpoint (z : CircleX × CircleX) :
      |f z.1 * g z.2 - fejerApprox H f z.1 * fejerApprox H g z.2| ≤
      (Prod.fst ⁻¹' Bf).indicator (fun _ => (1 : ℝ)) z +
      (Prod.snd ⁻¹' Bg).indicator (fun _ => (1 : ℝ)) z + 2 / (4 * H * δ ^ 2) := by
    have he : f z.1 * g z.2 - fejerApprox H f z.1 * fejerApprox H g z.2 =
      (f z.1 - fejerApprox H f z.1) * g z.2 +
      fejerApprox H f z.1 * (g z.2 - fejerApprox H g z.2) := by ring
    have hb := abs_add_le ((f z.1 - fejerApprox H f z.1) * g z.2)
      (fejerApprox H f z.1 * (g z.2 - fejerApprox H g z.2))
    rw [← he, abs_mul, abs_mul, abs_of_nonneg (hgb z.2).1,
      abs_of_nonneg (hF z.1).1] at hb
    have hb1 := mul_le_mul_of_nonneg_left (hgb z.2).2 (abs_nonneg (f z.1 - fejerApprox H f z.1))
    have hb2 := mul_le_mul_of_nonneg_right (hF z.1).2 (abs_nonneg (g z.2 - fejerApprox H g z.2))
    have h1 := hdefect f hfi hfb Bf hfloc z.1
    have h2 := hdefect g hgi hgb Bg hgloc z.2
    change |f z.1 * g z.2 - fejerApprox H f z.1 * fejerApprox H g z.2| ≤
      Bf.indicator (fun _ => (1 : ℝ)) z.1 + Bg.indicator (fun _ => (1 : ℝ)) z.2 +
      2 / (4 * H * δ ^ 2)
    have hsum := hb.trans (add_le_add hb1 hb2)
    simp only [mul_one, one_mul] at hsum
    exact hsum.trans (by convert add_le_add h1 h2 using 1; ring)
  have hi1 : Integrable ((Prod.fst ⁻¹' Bf).indicator (fun _ => (1 : ℝ))) η :=
    (integrable_const _).indicator (hBf.preimage measurable_fst)
  have hi2 : Integrable ((Prod.snd ⁻¹' Bg).indicator (fun _ => (1 : ℝ))) η :=
    (integrable_const _).indicator (hBg.preimage measurable_snd)
  rw [← integral_sub hir his]
  refine (abs_integral_le_integral_abs).trans ((integral_mono
    (hir.sub his).norm ((hi1.add hi2).add (integrable_const _)) hpoint).trans ?_)
  rw [integral_add' (hi1.add hi2) (integrable_const _), integral_add' hi1 hi2]
  rw [integral_indicator_const 1 (hBf.preimage measurable_fst),
    integral_indicator_const 1 (hBg.preimage measurable_snd)]
  simp only [Measure.real, integral_const, measure_univ,
    ENNReal.toReal_one, smul_eq_mul, mul_one, one_mul, le_refl]

def arcBoundary (c : CircleX) (r δ : ℝ) : Set CircleX :=
  Metric.closedBall c (r + δ) \ Metric.ball c (r - δ)

lemma measurableSet_arcBoundary (c : CircleX) (r δ : ℝ) :
    MeasurableSet (arcBoundary c r δ) :=
  Metric.isClosed_closedBall.measurableSet.diff Metric.isOpen_ball.measurableSet

lemma haarAddCircle_one_eq_volume :
    (AddCircle.haarAddCircle : Measure CircleX) = volume := by
  simpa using (AddCircle.volume_eq_smul_haarAddCircle (T := (1 : ℝ))).symm

lemma arcBoundary_measure_le (c : CircleX) (r : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) :
    (AddCircle.haarAddCircle : Measure CircleX).real (arcBoundary c r δ) ≤ 4 * δ := by
  rw [haarAddCircle_one_eq_volume, arcBoundary, measureReal_sdiff
    (Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall (by linarith)))
    Metric.isOpen_ball.measurableSet]
  rw [← measureReal_congr (AddCircle.closedBall_ae_eq_ball (x := c) (ε := r - δ))]
  simp only [Measure.real, AddCircle.volume_closedBall, ENNReal.toReal_ofReal']
  simp only [min_def, max_def]
  split_ifs <;> linarith

lemma arc_indicator_locally_constant (c : CircleX) (r : ℝ) {δ : ℝ} (hδ : 0 < δ)
    (x : CircleX) (hx : x ∉ arcBoundary c r δ) (t : CircleX) (ht : ‖x - t‖ < δ) :
    (Metric.ball c r).indicator (fun _ => (1 : ℝ)) t =
      (Metric.ball c r).indicator (fun _ => (1 : ℝ)) x := by
  classical
  rw [← dist_eq_norm] at ht
  have hd := abs_dist_sub_le x t c
  rw [abs_le] at hd
  by_cases hi : dist x c < r - δ
  · have hix : x ∈ Metric.ball c r := by rw [Metric.mem_ball]; linarith
    have hit : t ∈ Metric.ball c r := by rw [Metric.mem_ball]; linarith [hd.2]
    rw [Set.indicator_of_mem hix, Set.indicator_of_mem hit]
  · have ho : r + δ < dist x c := by
      simp only [arcBoundary, Set.mem_sdiff, Metric.mem_closedBall, Metric.mem_ball,
        not_and, not_lt] at hx
      exact lt_of_not_ge (fun h => hi (lt_of_not_ge (hx h)))
    have hox : x ∉ Metric.ball c r := by rw [Metric.mem_ball, not_lt]; linarith
    have hot : t ∉ Metric.ball c r := by rw [Metric.mem_ball, not_lt]; linarith [hd.2]
    rw [Set.indicator_of_notMem hox, Set.indicator_of_notMem hot]

lemma arc_rectangle_discrepancy {H : ℕ} (hH : 0 < H) {δ : ℝ} (hδ : 0 < δ)
    (c d : CircleX) (r s : ℝ) (η : Measure (CircleX × CircleX))
    [IsProbabilityMeasure η] {C ε : ℝ} (hC : 0 ≤ C) (hε : 0 ≤ ε)
    (hfst : ∀ B : Set CircleX, MeasurableSet B →
      η.real (Prod.fst ⁻¹' B) ≤ C * AddCircle.haarAddCircle.real B)
    (hsnd : ∀ B : Set CircleX, MeasurableSet B →
      η.real (Prod.snd ⁻¹' B) ≤ C * AddCircle.haarAddCircle.real B)
    (hmom : ∀ v w : ℤ, |v| < H → |w| < H → ¬(v = 0 ∧ w = 0) →
      ‖∫ z, doubleFourier v w z ∂η‖ ≤ ε) :
    |η.real (Metric.ball c r ×ˢ Metric.ball d s) -
      AddCircle.haarAddCircle.real (Metric.ball c r) *
      AddCircle.haarAddCircle.real (Metric.ball d s)| ≤
      8 * C * δ + 2 / (4 * H * δ ^ 2) + H ^ 2 * ε := by
  classical
  let f := (Metric.ball c r).indicator (fun _ => (1 : ℝ))
  let g := (Metric.ball d s).indicator (fun _ => (1 : ℝ))
  have hf : Measurable f := measurable_const.indicator Metric.isOpen_ball.measurableSet
  have hg : Measurable g := measurable_const.indicator Metric.isOpen_ball.measurableSet
  have hfb (x) : 0 ≤ f x ∧ f x ≤ 1 := by
    dsimp [f, Set.indicator]; split_ifs <;> norm_num
  have hgb (x) : 0 ≤ g x ∧ g x ≤ 1 := by
    dsimp [g, Set.indicator]; split_ifs <;> norm_num
  have hfi : Integrable f AddCircle.haarAddCircle :=
    (integrable_const _).indicator Metric.isOpen_ball.measurableSet
  have hgi : Integrable g AddCircle.haarAddCircle :=
    (integrable_const _).indicator Metric.isOpen_ball.measurableSet
  have h1 := fejer_unsmoothed_error hH hδ hf hg hfb hgb
    (arcBoundary c r δ) (arcBoundary d s δ) (measurableSet_arcBoundary ..)
    (measurableSet_arcBoundary ..) (arc_indicator_locally_constant c r hδ)
    (arc_indicator_locally_constant d s hδ) η
  have h2 := fejer_product_fourier_error hH hfi hgi
    (fun x => by rw [abs_of_nonneg (hfb x).1]; exact (hfb x).2)
    (fun x => by rw [abs_of_nonneg (hgb x).1]; exact (hgb x).2) η hε hmom
  simp only [← Complex.ofReal_mul, integral_complex_ofReal, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs] at h2
  have hm1 := (hfst _ (measurableSet_arcBoundary c r δ)).trans
    (mul_le_mul_of_nonneg_left (arcBoundary_measure_le c r hδ.le) hC)
  have hm2 := (hsnd _ (measurableSet_arcBoundary d s δ)).trans
    (mul_le_mul_of_nonneg_left (arcBoundary_measure_le d s hδ.le) hC)
  have hsum := (abs_sub_le (∫ z, f z.1 * g z.2 ∂η)
    (∫ z, fejerApprox H f z.1 * fejerApprox H g z.2 ∂η)
    ((∫ t, f t ∂AddCircle.haarAddCircle) * ∫ t, g t ∂AddCircle.haarAddCircle)).trans
      (add_le_add h1 h2)
  have hprod : (fun z : CircleX × CircleX => f z.1 * g z.2) =
      (Metric.ball c r ×ˢ Metric.ball d s).indicator (fun _ => (1 : ℝ)) := by
    funext z
    by_cases hzc : z.1 ∈ Metric.ball c r <;>
      by_cases hzd : z.2 ∈ Metric.ball d s <;> simp [f, g, hzc, hzd]
  rw [hprod, integral_indicator_const 1 (Metric.isOpen_ball.measurableSet.prod Metric.isOpen_ball.measurableSet)] at hsum
  dsimp [f, g] at hsum
  rw [integral_indicator_const 1 Metric.isOpen_ball.measurableSet,
    integral_indicator_const 1 Metric.isOpen_ball.measurableSet] at hsum
  simp only [smul_eq_mul, mul_one] at hsum
  linarith

def phasePairLaw (a b c d : ℝ) : Measure (CircleX × CircleX) :=
  (intervalLaw a b).map (phasePair c d)

lemma continuous_phasePair (c d : ℝ) : Continuous (phasePair c d) := by
  unfold phasePair
  fun_prop

lemma phasePairLaw_probability {a b : ℝ} (hab : a < b) (c d : ℝ) :
    IsProbabilityMeasure (phasePairLaw a b c d) := by
  let := intervalLaw_probability hab
  unfold phasePairLaw
  exact Measure.isProbabilityMeasure_map (continuous_phasePair c d).aemeasurable

lemma integral_phasePairLaw {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : CircleX × CircleX → E) {a b c d : ℝ}
    (hf : AEStronglyMeasurable f (phasePairLaw a b c d)) :
    (∫ z, f z ∂phasePairLaw a b c d) = ∫ t, f (phasePair c d t) ∂intervalLaw a b := by
  exact integral_map (continuous_phasePair c d).aemeasurable hf

lemma phasePairLaw_marginal_fst {a b c d : ℝ} (hab : a < b) (hc : 0 < c)
    (B : Set CircleX) (hB : MeasurableSet B) :
    (phasePairLaw a b c d).real (Prod.fst ⁻¹' B) ≤
      (1 + 1/(c*(b-a))) * (volume : Measure CircleX).real B := by
  classical
  let f := B.indicator (fun _ => (1 : ℝ))
  have hfi : Integrable f (volume : Measure CircleX) := (integrable_const _).indicator hB
  have hfn : ∀ x, 0 ≤ f x := by intro x; dsimp [f, Set.indicator]; split_ifs <;> norm_num
  have h := (circle_scaled_integral_bounds hfi hfn hab hc).2
  have he : (∫ z, (Prod.fst ⁻¹' B).indicator (fun _ => (1 : ℝ)) z
      ∂phasePairLaw a b c d) = ∫ t, f ((c*t : ℝ) : CircleX) ∂intervalLaw a b := by
    rw [integral_phasePairLaw _ ((measurable_const.indicator (hB.preimage measurable_fst)).aestronglyMeasurable)]
    rfl
  rw [integral_indicator_const 1 (hB.preimage measurable_fst)] at he
  dsimp [f] at h
  rw [integral_indicator_const 1 hB] at h
  simp only [smul_eq_mul, mul_one] at he h
  rw [he]
  exact h

lemma phasePairLaw_marginal_snd {a b c d : ℝ} (hab : a < b) (hd : 0 < d)
    (B : Set CircleX) (hB : MeasurableSet B) :
    (phasePairLaw a b c d).real (Prod.snd ⁻¹' B) ≤
      (1 + 1/(d*(b-a))) * (volume : Measure CircleX).real B := by
  classical
  let f := B.indicator (fun _ => (1 : ℝ))
  have hfi : Integrable f (volume : Measure CircleX) := (integrable_const _).indicator hB
  have hfn : ∀ x, 0 ≤ f x := by intro x; dsimp [f, Set.indicator]; split_ifs <;> norm_num
  have h := (circle_scaled_integral_bounds hfi hfn hab hd).2
  have he : (∫ z, (Prod.snd ⁻¹' B).indicator (fun _ => (1 : ℝ)) z
      ∂phasePairLaw a b c d) = ∫ t, f ((d*t : ℝ) : CircleX) ∂intervalLaw a b := by
    rw [integral_phasePairLaw _ ((measurable_const.indicator (hB.preimage measurable_snd)).aestronglyMeasurable)]
    rfl
  rw [integral_indicator_const 1 (hB.preimage measurable_snd)] at he
  dsimp [f] at h
  rw [integral_indicator_const 1 hB] at h
  simp only [smul_eq_mul, mul_one] at he h
  rw [he]
  exact h

lemma phasePair_fourier (c d t : ℝ) (v w : ℤ) :
    fourier v (phasePair c d t).1 * fourier w (phasePair c d t).2 =
      Complex.exp ((2 * Real.pi * ((v : ℝ)*c+(w : ℝ)*d) : ℝ) * Complex.I * t) := by
  simp only [phasePair, fourier_coe_apply, Complex.ofReal_one, div_one, ← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma intervalLaw_exponential_bound {a b ω : ℝ} (hab : a < b) (hω : ω ≠ 0) :
    ‖∫ t : ℝ, Complex.exp ((2 * Real.pi * ω : ℝ) * Complex.I * t)
      ∂intervalLaw a b‖ ≤ 1/(Real.pi*|ω| *(b-a)) := by
  have hc : (2 * Real.pi * ω : ℂ) * Complex.I ≠ 0 := by
    exact mul_ne_zero (by exact_mod_cast mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hω) Complex.I_ne_zero
  rw [integral_intervalLaw _ hab.le]
  simp_rw [Complex.ofReal_mul, Complex.ofReal_ofNat]
  rw [integral_exp_mul_complex hc, norm_smul, norm_div]
  have hn (x : ℝ) : ‖Complex.exp (2 * (Real.pi : ℂ) * ω * Complex.I * x)‖ = 1 := by
    have he : 2 * (Real.pi : ℂ) * ω * Complex.I * x =
        ((2 * Real.pi * ω * x : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [he, Complex.norm_exp_ofReal_mul_I]
  have hnum := (norm_sub_le (Complex.exp (2 * (Real.pi : ℂ) * ω * Complex.I * b))
    (Complex.exp (2 * (Real.pi : ℂ) * ω * Complex.I * a)))
  rw [hn b, hn a] at hnum
  simp only [norm_mul, Complex.norm_ofNat, Complex.norm_real,
    Complex.norm_I, mul_one, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
    norm_inv, Real.norm_eq_abs, abs_of_pos (sub_pos.mpr hab)]
  calc
    _ ≤ (b-a)⁻¹ * ((1+1)/(2*Real.pi*|ω|)) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hnum (by positivity)) (by positivity)
    _ = _ := by field_simp; ring

lemma phasePairLaw_fourier_bound {a b c d : ℝ} (hab : a < b) (v w : ℤ)
    (hfreq : (v : ℝ)*c+(w : ℝ)*d ≠ 0) :
    ‖∫ z, fourier v z.1 * fourier w z.2 ∂phasePairLaw a b c d‖ ≤
      1/(Real.pi*|(v : ℝ)*c+(w : ℝ)*d| *(b-a)) := by
  rw [integral_phasePairLaw _ (by fun_prop)]
  simp_rw [phasePair_fourier]
  exact intervalLaw_exponential_bound hab hfreq

lemma separated_phase_rectangle_bound {a b c d C R : ℝ}
    (hab : a < b) (hc : 0 < c) (hd : 0 < d) (hR : 0 < R)
    (hC0 : 0 ≤ C) (hCc : 1 + 1/(c*(b-a)) ≤ C)
    (hCd : 1 + 1/(d*(b-a)) ≤ C) {H : ℕ} (hH : 0 < H)
    (hsep : ∀ v w : ℤ, |v| < H → |w| < H → ¬(v = 0 ∧ w = 0) →
      R ≤ |(v : ℝ)*c + (w : ℝ)*d|)
    {δ : ℝ} (hδ : 0 < δ) (x y : CircleX) (r s : ℝ) :
    |(phasePairLaw a b c d).real (Metric.ball x r ×ˢ Metric.ball y s) -
      volume.real (Metric.ball x r) * volume.real (Metric.ball y s)| ≤
      8*C*δ + 2/(4*H*δ^2) + H^2/(Real.pi*R*(b-a)) := by
  let := phasePairLaw_probability hab c d
  have hε : 0 ≤ 1/(Real.pi*R*(b-a)) := by positivity
  have hfst (B : Set CircleX) (hB : MeasurableSet B) :
      (phasePairLaw a b c d).real (Prod.fst ⁻¹' B) ≤
        C*AddCircle.haarAddCircle.real B := by
    rw [haarAddCircle_one_eq_volume]
    exact (phasePairLaw_marginal_fst hab hc B hB).trans
      (mul_le_mul_of_nonneg_right hCc ENNReal.toReal_nonneg)
  have hsnd (B : Set CircleX) (hB : MeasurableSet B) :
      (phasePairLaw a b c d).real (Prod.snd ⁻¹' B) ≤
        C*AddCircle.haarAddCircle.real B := by
    rw [haarAddCircle_one_eq_volume]
    exact (phasePairLaw_marginal_snd hab hd B hB).trans
      (mul_le_mul_of_nonneg_right hCd ENNReal.toReal_nonneg)
  have hmom (v w : ℤ) (hv : |v| < H) (hw : |w| < H) (hne : ¬(v=0 ∧ w=0)) :
      ‖∫ z, doubleFourier v w z ∂phasePairLaw a b c d‖ ≤
        1/(Real.pi*R*(b-a)) := by
    have hfpos : 0 < |(v : ℝ)*c+(w : ℝ)*d| := hR.trans_le (hsep v w hv hw hne)
    exact (phasePairLaw_fourier_bound hab v w (abs_pos.mp hfpos)).trans
      (one_div_le_one_div_of_le (by positivity)
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hsep v w hv hw hne)
          Real.pi_pos.le) (sub_nonneg.mpr hab.le)))
  have h := arc_rectangle_discrepancy hH hδ x y r s (phasePairLaw a b c d)
    hC0 hε hfst hsnd hmom
  rw [haarAddCircle_one_eq_volume] at h
  simpa only [mul_one_div] using h

end Sampling
end ContinuousCircleWeight

end

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_PhaseWeights
attribute [-instance] _root_.OAI.CircleCoupling.labelMeasurableSpace
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

lemma weight_sq_integral_t {ℓ α s : ℝ} (hℓ : 0 < ℓ) (hℓ1 : ℓ < 1) (hα : 0 < α) :
    (∫ t in Ioc 0 1, (weight ℓ α s t)^2) =
      if α ≤ delta s then 1 / (ℓ * delta s) else 0 := by
  have he : (fun t ↦ (weight ℓ α s t)^2) =
      (fun t ↦ (1 / (ℓ * delta s)) * weight ℓ α s t) := by
    ext t
    unfold weight
    split_ifs <;> ring
  rw [he, integral_const_mul, weight_integral_t hℓ hℓ1 hα]
  split_ifs <;> simp

lemma integral_inv_delta {ℓ α : ℝ} (hℓ : 0 < ℓ) (hα : 0 < α) (hα2 : α ≤ 1/2) :
    (∫ s in Icc α (1-α), 1 / (ℓ * delta s)) =
      (2 / ℓ) * Real.log (1 / (2*α)) := by
  have hab : α ≤ 1-α := by linarith
  have hc : ContinuousOn (fun s : ℝ ↦ 1 / (ℓ * delta s)) (Icc α (1-α)) := by
    apply continuousOn_const.div (continuousOn_const.mul ((continuous_id.min (continuous_const.sub continuous_id)).continuousOn))
    intro s hs
    change ℓ * min s (1-s) ≠ 0
    exact ne_of_gt (mul_pos hℓ (lt_min (lt_of_lt_of_le hα hs.1) (by linarith [hs.2])))
  have hi : IntervalIntegrable (fun s : ℝ ↦ 1 / (ℓ * delta s)) volume α (1-α) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr hc.integrableOn_Icc
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab,
    ← intervalIntegral.integral_add_adjacent_intervals
      (hi.mono_set (by rw [uIcc_of_le hα2, uIcc_of_le hab]; exact Icc_subset_Icc le_rfl (by linarith)))
      (hi.mono_set (by rw [uIcc_of_le (by linarith : (1:ℝ)/2 ≤ 1-α), uIcc_of_le hab]; exact Icc_subset_Icc hα2 le_rfl))]
  have he1 : (∫ s in α..(1:ℝ)/2, 1 / (ℓ * delta s)) =
      (1/ℓ) * (∫ s in α..(1:ℝ)/2, 1/s) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le hα2] at hs
    simp only [delta, min_eq_left (by linarith [hs.2] : s ≤ 1-s)]
    simp [one_div, mul_inv_rev, mul_comm]
  have he2 : (∫ s in (1:ℝ)/2..1-α, 1 / (ℓ * delta s)) =
      (1/ℓ) * (∫ s in α..(1:ℝ)/2, 1/s) := by
    calc
      _ = ∫ s in (1:ℝ)/2..1-α, (1/ℓ) * (1/(1-s)) := by
        apply intervalIntegral.integral_congr
        intro s hs
        rw [uIcc_of_le (by linarith : (1:ℝ)/2 ≤ 1-α)] at hs
        simp only [delta, min_eq_right (by linarith [hs.1] : 1-s ≤ s)]
        simp [one_div, mul_inv_rev, mul_comm]
      _ = _ := by
        rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_sub_left]
        congr 2 <;> ring
  rw [he1, he2, integral_one_div_of_pos hα (by norm_num)]
  rw [show (1:ℝ)/2/α = 1/(2*α) by ring]
  ring

lemma integral_uPos_sq {ℓ α : ℝ} (hℓ : 0 < ℓ) (hℓ1 : ℓ < 1)
    (hα : 0 < α) (hα2 : α ≤ 1/2) :
    (∫ s : CircleX, ∫ t : CircleX, (uPos ℓ α s t)^2) =
      (2 / ℓ) * Real.log (1 / (2*α)) := by
  simp_rw [uPos]
  have he (s : ℝ) : (∫ t : CircleX, (weight ℓ α s (repr t))^2) =
      if α ≤ delta s then 1/(ℓ*delta s) else 0 := by
    rw [integral_repr (fun t ↦ (weight ℓ α s t)^2), weight_sq_integral_t hℓ hℓ1 hα]
  simp_rw [he]
  rw [integral_repr (fun s : ℝ ↦ if α ≤ delta s then 1/(ℓ*delta s) else 0)]
  have hf : (fun s : ℝ ↦ if α ≤ delta s then 1/(ℓ*delta s) else 0) =
      (Icc α (1-α)).indicator (fun s ↦ 1/(ℓ*delta s)) := by
    ext s
    simp [delta, indicator, mem_Icc, le_sub_comm]
  rw [hf, integral_indicator measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc,
    inter_eq_left.mpr (show Icc α (1-α) ⊆ Ioc 0 1 from fun s hs ↦
      ⟨lt_of_lt_of_le hα hs.1, le_trans hs.2 (by linarith)⟩)]
  exact integral_inv_delta hℓ hα hα2

lemma integral_uNeg_sq {ℓ α : ℝ} (hℓ : 0 < ℓ) (hℓ1 : ℓ < 1)
    (hα : 0 < α) (hα2 : α ≤ 1/2) :
    (∫ s : CircleX, ∫ t : CircleX, (uNeg ℓ α s t)^2) =
      (2 / ℓ) * Real.log (1 / (2*α)) := by
  have hip : Integrable (fun z : CircleX × CircleX ↦ (uPos ℓ α z.1 z.2)^2) (volume.prod volume) := by
    apply Integrable.of_bound ((measurable_uPos ℓ α).pow_const 2).aestronglyMeasurable ((1/(ℓ*α))^2)
    exact ae_of_all _ fun z ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (weight_bounds hℓ hα _ _).1 (weight_bounds hℓ hα _ _).2 2
  have hin : Integrable (fun z : CircleX × CircleX ↦ (uNeg ℓ α z.1 z.2)^2) (volume.prod volume) := by
    apply Integrable.of_bound ((measurable_uNeg ℓ α).pow_const 2).aestronglyMeasurable ((1/(ℓ*α))^2)
    exact ae_of_all _ fun z ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (weight_bounds hℓ hα _ _).1 (weight_bounds hℓ hα _ _).2 2
  rw [integral_integral_swap hin]
  have he (t : CircleX) : (∫ s : CircleX, (uNeg ℓ α s t)^2) = ∫ s : CircleX, (uPos ℓ α s t)^2 :=
    integral_sub_right_eq_self (fun s ↦ (uPos ℓ α s t)^2) t
  simp_rw [he]
  rw [← integral_integral_swap hip]
  exact integral_uPos_sq hℓ hℓ1 hα hα2

lemma uNeg_integral_real {ℓ α : ℝ} (hℓ : 0 < ℓ) (hℓ1 : ℓ < 1) (hα : 0 < α)
    (s : CircleX) : (∫ t : CircleX, uNeg ℓ α s t) =
      ∫ t in Ioc 0 1, weight ℓ α (repr s-t) t := by
  rw [← AddCircle.integral_preimage (1 : ℝ) 0]
  simp only [zero_add]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc,
    ae_restrict_of_ae (show ∀ᵐ t : ℝ, t ≠ 1 from by simp [ae_iff])] with t ht hne
  nth_rw 1 [← coe_repr s]
  exact uNeg_unwrapped hℓ hℓ1 hα (repr_mem s) ⟨le_of_lt ht.1, lt_of_le_of_ne ht.2 hne⟩

lemma negative_weight_upper {ℓ α s : ℝ} (hℓ : 0 < ℓ) (hℓ1 : ℓ < 1)
    (hα : 0 < α) (hs : 0 < delta s) (t : ℝ) :
    weight ℓ α (s-t) t ≤ (Ioo 0 (ℓ * delta s / (1-ℓ))).indicator
      (fun _ ↦ (1+ℓ) / (ℓ * delta s)) t := by
  unfold weight
  split_ifs with h
  · have hd : 0 < delta (s-t) := lt_of_lt_of_le hα h.1
    have hlip := delta_lipschitz s (s-t)
    rw [show s-(s-t)=t by ring, abs_of_pos h.2.1, abs_le] at hlip
    have ht : t < ℓ * delta s / (1-ℓ) := by
      apply (lt_div_iff₀ (sub_pos.mpr hℓ1)).mpr
      nlinarith [mul_le_mul_of_nonneg_left hlip.1 hℓ.le, h.2.2]
    rw [indicator_of_mem (show t ∈ Ioo 0 (ℓ * delta s / (1-ℓ)) from ⟨h.2.1, ht⟩)]
    apply (div_le_div_iff₀ (mul_pos hℓ hd) (mul_pos hℓ hs)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hlip.2 hℓ.le,
      mul_lt_mul_of_pos_left h.2.2 hℓ]
  · apply indicator_nonneg
    intro _ _
    exact div_nonneg (by linarith) (mul_nonneg hℓ.le hs.le)

lemma negative_weight_lower {ℓ α s : ℝ} (hℓ : 0 < ℓ) (hℓ1 : ℓ < 1)
    (hα : 0 < α) (hs : 0 < delta s) (hcut : (1+ℓ)*α ≤ delta s) (t : ℝ) :
    (Ioo 0 (ℓ * delta s / (1+ℓ))).indicator
      (fun _ ↦ (1-ℓ) / (ℓ * delta s)) t ≤ weight ℓ α (s-t) t := by
  by_cases ht : t ∈ Ioo 0 (ℓ * delta s / (1+ℓ))
  · rw [indicator_of_mem ht]
    have hb : t * (1+ℓ) < ℓ * delta s := (lt_div_iff₀ (by linarith : 0 < 1+ℓ)).mp ht.2
    have hlip := delta_lipschitz s (s-t)
    rw [show s-(s-t)=t by ring, abs_of_pos ht.1, abs_le] at hlip
    have hct : α ≤ delta (s-t) := by nlinarith
    have hd : 0 < delta (s-t) := lt_of_lt_of_le hα hct
    have hsup : t < ℓ * delta (s-t) := by nlinarith
    rw [weight, ite_eq_left ⟨hct, ht.1, hsup⟩]
    apply (div_le_div_iff₀ (mul_pos hℓ hs) (mul_pos hℓ hd)).mpr
    have hbound : (1-ℓ)*delta (s-t) ≤ delta s := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hbound hℓ.le]
  · rw [indicator_of_notMem ht]
    exact (weight_bounds hℓ hα _ _).1

lemma integrable_negative_weight {ℓ α : ℝ} (hℓ : 0 < ℓ) (hα : 0 < α) (s : ℝ) :
    IntegrableOn (fun t ↦ weight ℓ α (s-t) t) (Ioc 0 1) := by
  apply Integrable.of_bound ((measurable_weight ℓ α).comp
    ((measurable_const.sub measurable_id).prodMk measurable_id)).aestronglyMeasurable (1/(ℓ*α))
  exact ae_of_all _ fun t ↦ by
    change ‖weight ℓ α (s-t) t‖ ≤ 1/(ℓ*α)
    rw [Real.norm_eq_abs, abs_of_nonneg (weight_bounds hℓ hα _ _).1]
    exact (weight_bounds hℓ hα _ _).2

lemma negative_density_upper {ℓ α s : ℝ} (hℓ : 0 < ℓ) (hℓ1 : ℓ < 1)
    (hα : 0 < α) (hs : 0 < delta s) :
    (∫ t in Ioc 0 1, weight ℓ α (s-t) t) ≤ (1+ℓ)/(1-ℓ) := by
  let R := ℓ * delta s / (1-ℓ)
  let C := (1+ℓ)/(ℓ*delta s)
  have hR : 0 < R := div_pos (mul_pos hℓ hs) (sub_pos.mpr hℓ1)
  have hC : 0 ≤ C := div_nonneg (by linarith) (mul_nonneg hℓ.le hs.le)
  have hi : Integrable ((Ioo 0 R).indicator (fun _ : ℝ ↦ C)) :=
    (integrableOn_const (μ := volume) (s := Ioo 0 R) (C := C) (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)).integrable_indicator measurableSet_Ioo
  calc
    _ ≤ ∫ t in Ioc 0 1, (Ioo 0 R).indicator (fun _ : ℝ ↦ C) t :=
      integral_mono (integrable_negative_weight hℓ hα s) hi.restrict
        (negative_weight_upper hℓ hℓ1 hα hs)
    _ ≤ ∫ t : ℝ, (Ioo 0 R).indicator (fun _ : ℝ ↦ C) t :=
      integral_mono_measure Measure.restrict_le_self
        (ae_of_all _ (indicator_nonneg fun _ _ ↦ hC)) hi
    _ = _ := by
      rw [integral_indicator measurableSet_Ioo, integral_const]
      simp only [Measure.real, Measure.restrict_apply_univ, Real.volume_Ioo, sub_zero,
        ENNReal.toReal_ofReal hR.le, smul_eq_mul]
      dsimp [R, C]
      field_simp

lemma negative_density_lower {ℓ α s : ℝ} (hℓ : 0 < ℓ) (hℓ1 : ℓ < 1)
    (hα : 0 < α) (hs : 0 < delta s) (hcut : (1+ℓ)*α ≤ delta s) :
    (1-ℓ)/(1+ℓ) ≤ ∫ t in Ioc 0 1, weight ℓ α (s-t) t := by
  let R := ℓ * delta s / (1+ℓ)
  let C := (1-ℓ)/(ℓ*delta s)
  have hR : 0 < R := div_pos (mul_pos hℓ hs) (by linarith)
  have hR1 : R ≤ 1 := by
    apply (div_le_one (by linarith : 0 < 1+ℓ)).mpr
    nlinarith [delta_le_half s]
  have hi : Integrable ((Ioo 0 R).indicator (fun _ : ℝ ↦ C)) :=
    (integrableOn_const (μ := volume) (s := Ioo 0 R) (C := C) (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)).integrable_indicator measurableSet_Ioo
  calc
    _ = ∫ t in Ioc 0 1, (Ioo 0 R).indicator (fun _ : ℝ ↦ C) t := by
      rw [integral_indicator measurableSet_Ioo, Measure.restrict_restrict measurableSet_Ioo,
        inter_eq_left.mpr (show Ioo 0 R ⊆ Ioc 0 1 from fun _ ht ↦ ⟨ht.1, ht.2.le.trans hR1⟩),
        integral_const]
      simp only [Measure.real, Measure.restrict_apply_univ, Real.volume_Ioo, sub_zero,
        ENNReal.toReal_ofReal hR.le, smul_eq_mul]
      dsimp [R, C]
      field_simp
    _ ≤ _ := integral_mono hi.restrict (integrable_negative_weight hℓ hα s)
      (negative_weight_lower hℓ hℓ1 hα hs hcut)

lemma uNeg_mean_bounds {ℓ α : ℝ} (hℓ : 0 < ℓ) (hα : 0 < α) (s : CircleX) :
    0 ≤ (∫ t : CircleX, uNeg ℓ α s t) ∧
      (∫ t : CircleX, uNeg ℓ α s t) ≤ 1/(ℓ*α) := by
  have hm : Measurable (fun t ↦ uNeg ℓ α s t) :=
    (measurable_uNeg ℓ α).comp (measurable_const.prodMk measurable_id)
  have hi : Integrable (fun t ↦ uNeg ℓ α s t) := by
    apply Integrable.of_bound hm.aestronglyMeasurable (1/(ℓ*α))
    exact ae_of_all _ fun t ↦ by
      change ‖weight ℓ α (repr (s-t)) (repr t)‖ ≤ _
      rw [Real.norm_eq_abs, abs_of_nonneg (weight_bounds hℓ hα _ _).1]
      exact (weight_bounds hℓ hα _ _).2
  refine ⟨integral_nonneg (fun t ↦ (weight_bounds hℓ hα _ _).1), ?_⟩
  simpa only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul] using
    integral_mono hi (integrable_const (1/(ℓ*α))) (fun t ↦ (weight_bounds hℓ hα _ _).2)

lemma integral_uNeg_mean_sq {ℓ α : ℝ} (hℓ : 0 < ℓ) (hℓ1 : ℓ < 1)
    (hα : 0 < α) (hα2 : α ≤ 1/2) :
    (∫ s : CircleX, (∫ t : CircleX, uNeg ℓ α s t)^2) ≤
      1 + (2*ℓ/(1-ℓ))^2 + 2*(1+ℓ)*α := by
  let g : CircleX → ℝ := fun s ↦ ∫ t : CircleX, uNeg ℓ α s t
  let C : ℝ := 2*ℓ/(1-ℓ)
  let r : ℝ := (1+ℓ)*α
  let b : CircleX → ℝ := fun s ↦ if delta (repr s) < r then 1 else 0
  have hC : 0 ≤ C := div_nonneg (by positivity) (by linarith)
  have hr : 0 < r := mul_pos (by linarith) hα
  have hgi : Integrable g := (integrable_uNeg hℓ hα).integral_prod_left
  have hgb (s : CircleX) := uNeg_mean_bounds hℓ hα s
  have hgs : Integrable (fun s ↦ (g s)^2) := by
    apply Integrable.of_bound (hgi.aestronglyMeasurable.pow 2) ((1/(ℓ*α))^2)
    exact ae_of_all _ fun s ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (hgb s).1 (hgb s).2 2
  have hbi : Integrable b := by
    have hm : Measurable b := Measurable.ite
      (measurableSet_lt (measurable_delta.comp measurable_repr) measurable_const)
      measurable_const measurable_const
    apply Integrable.of_bound hm.aestronglyMeasurable 1
    exact ae_of_all _ fun s ↦ by dsimp [b]; split_ifs <;> norm_num
  have hv : (fun s ↦ (g s-1)^2) = (fun s ↦ (g s)^2 - 2*g s + 1) := by
    funext s; ring
  have hvi : Integrable (fun s ↦ (g s-1)^2) := by
    rw [hv]
    exact (hgs.sub (hgi.const_mul 2)).add (integrable_const 1)
  have hbound : ∀ᵐ s : CircleX, (g s-1)^2 ≤ C^2 + b s := by
    filter_upwards [show ∀ᵐ s : CircleX, s ≠ 0 from by simpa [ae_iff] using volume_singleton_zero (0 : CircleX)] with s hs
    have hsp : 0 < repr s := by
      by_contra! h
      have hz : repr s = 0 := le_antisymm h (repr_mem s).1
      have := coe_repr s
      simp only [hz, AddCircle.coe_zero] at this
      exact hs this.symm
    have hd : 0 < delta (repr s) := delta_pos ⟨hsp, (repr_mem s).2⟩
    have hu := negative_density_upper hℓ hℓ1 hα hd
    rw [← uNeg_integral_real hℓ hℓ1 hα s] at hu
    change g s ≤ _ at hu
    have heU : (1+ℓ)/(1-ℓ) = 1+C := by dsimp [C]; field_simp [ne_of_gt (sub_pos.mpr hℓ1)]; ring
    rw [heU] at hu
    by_cases hb : delta (repr s) < r
    · simp only [b, ite_eq_left hb]
      rcases le_total (g s) 1 with hl | hl
      · nlinarith [(hgb s).1, sq_nonneg C]
      · nlinarith
    · simp only [b, ite_eq_right hb, add_zero]
      have hl := negative_density_lower hℓ hℓ1 hα hd (le_of_not_gt hb)
      rw [← uNeg_integral_real hℓ hℓ1 hα s] at hl
      change _ ≤ g s at hl
      have hL : 1-C ≤ (1-ℓ)/(1+ℓ) := by
        have hc : 2*ℓ/(1+ℓ) ≤ C := by
          exact div_le_div_of_nonneg_left (by positivity) (by linarith) (by linarith)
        have he : (1-ℓ)/(1+ℓ) = 1 - 2*ℓ/(1+ℓ) := by
          field_simp [ne_of_gt (show 0 < 1+ℓ by linarith)]
          ring
        rw [he]
        linarith
      have hlo := hL.trans hl
      nlinarith [sq_nonneg (g s-1-C), sq_nonneg (g s-1+C)]
  have hive := integral_mono_ae hvi ((integrable_const (C^2)).add hbi) hbound
  change (∫ s : CircleX, (g s-1)^2) ≤ ∫ s : CircleX, C^2+b s at hive
  rw [integral_add (integrable_const (C^2)) hbi,
    integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul] at hive
  have hbmass : ∫ s : CircleX, b s ≤ 2*r := integral_delta_small hr
  have hgm : ∫ s : CircleX, g s = 1-2*α := integral_uNeg hℓ hℓ1 hα hα2
  rw [hv] at hive
  rw [integral_add (show Integrable (fun s : CircleX ↦ (g s)^2 - 2*g s) volume from
      hgs.sub (hgi.const_mul 2)) (integrable_const 1),
    integral_sub hgs (hgi.const_mul 2), integral_const_mul, hgm,
    integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul] at hive
  change (∫ s : CircleX, (g s)^2) ≤ _
  dsimp [C, r] at hive hbmass
  linarith



end CircleSampling

end

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_Discrepancy
attribute [-instance] _root_.OAI.CircleCoupling.labelMeasurableSpace
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


lemma prod_eventuallyEq_of_marginals {μ : Measure (CircleX × CircleX)}
    (hμ1 : Measure.map Prod.fst μ ≪ (volume : Measure CircleX))
    (hμ2 : Measure.map Prod.snd μ ≪ (volume : Measure CircleX))
    {A A' B B' : Set CircleX} (hA : A =ᵐ[volume] A') (hB : B =ᵐ[volume] B') :
    A ×ˢ B =ᵐ[μ] A' ×ˢ B' := by
  filter_upwards [ae_of_ae_map measurable_fst.aemeasurable (hμ1.ae_le hA),
    ae_of_ae_map measurable_snd.aemeasurable (hμ2.ae_le hB)] with z hz1 hz2
  apply propext
  change (z.1∈A ∧ z.2∈B) ↔ (z.1∈A' ∧ z.2∈B')
  rw [show (z.1∈A)=(z.1∈A') from hz1,show (z.2∈B)=(z.2∈B') from hz2]

lemma measureReal_two_unions (μ : Measure (CircleX × CircleX)) [IsFiniteMeasure μ]
    {A B C D : Set CircleX} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hC : MeasurableSet C) (hD : MeasurableSet D) (hAB : Disjoint A B) (hCD : Disjoint C D) :
    μ.real ((A∪B) ×ˢ (C∪D)) =
      (μ.real (A×ˢC)+μ.real (A×ˢD)) + (μ.real (B×ˢC)+μ.real (B×ˢD)) := by
  rw [union_prod, measureReal_union (disjoint_prod_of_left _ _ hAB) (hB.prod (hC.union hD)),
    prod_union,measureReal_union (disjoint_prod_of_right _ _ hCD) (hA.prod hD),
    prod_union,measureReal_union (disjoint_prod_of_right _ _ hCD) (hB.prod hD)]

lemma twoArcs_rectangle_discrepancy {μ ν : Measure (CircleX × CircleX)}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ1 : Measure.map Prod.fst μ ≪ (volume : Measure CircleX))
    (hμ2 : Measure.map Prod.snd μ ≪ (volume : Measure CircleX))
    (hν1 : Measure.map Prod.fst ν ≪ (volume : Measure CircleX))
    (hν2 : Measure.map Prod.snd ν ≪ (volume : Measure CircleX))
    {ε : ℝ} (hdisc : ∀ c d : CircleX, ∀ r q : ℝ,
      |μ.real (Metric.ball c r ×ˢ Metric.ball d q) -
       ν.real (Metric.ball c r ×ˢ Metric.ball d q)| ≤ ε)
    {A B : Set CircleX} (hA : IsTwoArcs A) (hB : IsTwoArcs B) :
    |μ.real (A×ˢB)-ν.real (A×ˢB)| ≤ 4*ε := by
  obtain ⟨c,d,r,q,hcd,hA⟩ := hA
  obtain ⟨e,f,s,t,hef,hB⟩ := hB
  rw [measureReal_congr (prod_eventuallyEq_of_marginals hμ1 hμ2 hA hB),
    measureReal_congr (prod_eventuallyEq_of_marginals hν1 hν2 hA hB),
    measureReal_two_unions μ measurableSet_ball measurableSet_ball measurableSet_ball
      measurableSet_ball hcd hef,
    measureReal_two_unions ν measurableSet_ball measurableSet_ball measurableSet_ball
      measurableSet_ball hcd hef]
  have h1 := abs_le.mp (hdisc c e r s)
  have h2 := abs_le.mp (hdisc c f r t)
  have h3 := abs_le.mp (hdisc d e q s)
  have h4 := abs_le.mp (hdisc d f q t)
  rw [abs_le]
  constructor <;> linarith

end



end CircleSampling

end

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_ProductSampling
attribute [-instance] _root_.OAI.CircleCoupling.labelMeasurableSpace
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

namespace ContinuousCircleWeight.Sampling

lemma phasePairLaw_fst_ac {a b c d : ℝ} (hab : a<b) (hc : 0<c) :
    Measure.map Prod.fst (phasePairLaw a b c d) ≪ (volume : Measure CircleX) := by
  let := phasePairLaw_probability hab c d
  apply Measure.AbsolutelyContinuous.mk
  intro A hA h0
  rw [Measure.map_apply measurable_fst hA]
  apply (measureReal_eq_zero_iff (by finiteness)).mp
  apply le_antisymm _ measureReal_nonneg
  have h := phasePairLaw_marginal_fst (d := d) hab hc A hA
  simpa [Measure.real,h0] using h

lemma phasePairLaw_snd_ac {a b c d : ℝ} (hab : a<b) (hd : 0<d) :
    Measure.map Prod.snd (phasePairLaw a b c d) ≪ (volume : Measure CircleX) := by
  let := phasePairLaw_probability hab c d
  apply Measure.AbsolutelyContinuous.mk
  intro A hA h0
  rw [Measure.map_apply measurable_snd hA]
  apply (measureReal_eq_zero_iff (by finiteness)).mp
  apply le_antisymm _ measureReal_nonneg
  have h := phasePairLaw_marginal_snd (c := c) hab hd A hA
  simpa [Measure.real,h0] using h

lemma product_weight_discrepancy {a b c d B ε : ℝ} (hab : a<b) (hc : 0<c) (hd : 0<d)
    (hB : 0≤B) {u : CircleX → ℝ} (hu : Measurable u)
    (hu0 : ∀ t, 0≤u t) (huB : ∀ t, u t≤B)
    (harc : ∀ r>0, CircleSampling.IsTwoArcs {t | r<u t})
    (hdisc : ∀ x y : CircleX, ∀ r s : ℝ,
      |(phasePairLaw a b c d).real (Metric.ball x r ×ˢ Metric.ball y s) -
        volume.real (Metric.ball x r)*volume.real (Metric.ball y s)| ≤ ε) :
    |(∫ γ, u ((c*γ : ℝ) : CircleX)*u ((d*γ : ℝ) : CircleX) ∂intervalLaw a b) -
      (∫ t, u t)^2| ≤ 4*B^2*ε := by
  let := phasePairLaw_probability hab c d
  let μ := phasePairLaw a b c d
  let ν := (volume : Measure CircleX).prod (volume : Measure CircleX)
  have hν1 : Measure.map Prod.fst ν ≪ (volume : Measure CircleX) := by
    dsimp [ν]
    rw [Measure.map_fst_prod,measure_univ,one_smul]
  have hν2 : Measure.map Prod.snd ν ≪ (volume : Measure CircleX) := by
    dsimp [ν]
    rw [Measure.map_snd_prod,measure_univ,one_smul]
  have h := CircleSampling.superlevel_discrepancy (μ := μ) (ν := ν) hB
    (hu.comp measurable_fst) (hu.comp measurable_snd)
    (fun z ↦ hu0 z.1) (fun z ↦ huB z.1) (fun z ↦ hu0 z.2) (fun z ↦ huB z.2)
    (ε := 4*ε) (by
      intro r hr s hs
      change |μ.real ({t | r<u t} ×ˢ {t | s<u t}) -
        ν.real ({t | r<u t} ×ˢ {t | s<u t})| ≤ _
      apply CircleSampling.twoArcs_rectangle_discrepancy (phasePairLaw_fst_ac hab hc)
        (phasePairLaw_snd_ac hab hd) hν1 hν2 ?_ (harc r hr.1) (harc s hs.1)
      intro x y r s
      simpa only [ν,Measure.real,Measure.prod_prod,ENNReal.toReal_mul] using hdisc x y r s)
  have hμ : (∫ z, u z.1*u z.2 ∂μ) =
      ∫ γ, u ((c*γ : ℝ) : CircleX)*u ((d*γ : ℝ) : CircleX) ∂intervalLaw a b := by
    apply integral_phasePairLaw
    exact ((hu.comp measurable_fst).mul (hu.comp measurable_snd)).aestronglyMeasurable
  have hν : (∫ z, u z.1*u z.2 ∂ν)=(∫ t, u t)^2 := by
    rw [show (∫ z, u z.1*u z.2 ∂ν)=(∫ t, u t)*(∫ t, u t) from integral_prod_mul u u]
    ring
  change |(∫ z, u z.1*u z.2 ∂μ) - (∫ z, u z.1*u z.2 ∂ν)| ≤ B^2*(4*ε) at h
  rw [hμ,hν] at h
  convert! h using 1; ring

end ContinuousCircleWeight.Sampling

namespace CircleSampling
open ContinuousCircleWeight.Sampling

lemma orientedWeight_sq (positive : Bool) {ℓ α : ℝ} (hℓ : 0<ℓ)
    (hℓ1 : ℓ<1) (hα : 0<α) (hα2 : α≤1/2) :
    (∫ s : CircleX, ∫ t : CircleX, (orientedWeight positive ℓ α s t)^2)=
      (2/ℓ)*Real.log (1/(2*α)) := by
  cases positive
  · exact integral_uNeg_sq hℓ hℓ1 hα hα2
  · exact integral_uPos_sq hℓ hℓ1 hα hα2

lemma orientedWeight_mean_sq (positive : Bool) {ℓ α : ℝ} (hℓ : 0<ℓ)
    (hℓ1 : ℓ<1) (hα : 0<α) (hα2 : α≤1/2) :
    (∫ s : CircleX, (∫ t : CircleX, orientedWeight positive ℓ α s t)^2) ≤
      1+(2*ℓ/(1-ℓ))^2+2*(1+ℓ)*α := by
  cases positive
  · exact integral_uNeg_mean_sq hℓ hℓ1 hα hα2
  · have he : (fun s : CircleX ↦ (∫ t : CircleX, uPos ℓ α s t)^2)=
        (fun s : CircleX ↦ ∫ t : CircleX, uPos ℓ α s t) := by
      ext s
      rw [uPos_integral_t hℓ hℓ1 hα]
      split_ifs <;> norm_num
    change (∫ s : CircleX, (∫ t : CircleX, uPos ℓ α s t)^2) ≤ _
    rw [he,integral_uPos hℓ hℓ1 hα hα2]
    nlinarith [sq_nonneg (2*ℓ/(1-ℓ))]

lemma bounded_sq_integrable {Ω : Type uΩ} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] {f : Ω → ℝ} (hf : Measurable f) {B : ℝ}
    (hb : ∀ x, 0≤f x ∧ f x≤B) : Integrable (fun x ↦ (f x)^2) μ := by
  apply bounded_integrable μ (hf.pow_const 2)
  exact fun x ↦ ⟨sq_nonneg _,pow_le_pow_left₀ (hb x).1 (hb x).2 2⟩

lemma trial_sq_upper {a b c ℓ α D : ℝ} (hab : a<b) (hc : 0<c)
    (hℓ : 0<ℓ) (hℓ1 : ℓ<1) (hα : 0<α) (hα2 : α≤1/2)
    (positive : Bool) (hD : 1+1/(c*(b-a))≤D) :
    (∫ z : CircleX × ℝ, (orientedWeight positive ℓ α z.1 ((c*z.2 : ℝ) : CircleX))^2
      ∂(volume.prod (intervalLaw a b))) ≤ D*((2/ℓ)*Real.log (1/(2*α))) := by
  let := intervalLaw_probability hab
  let u := orientedWeight positive ℓ α
  have hm : Measurable (Function.uncurry u) := measurable_orientedWeight positive ℓ α
  have hb := orientedWeight_bounds positive hℓ hα
  have htrial : Measurable (fun z : CircleX × ℝ ↦ u z.1 ((c*z.2 : ℝ) : CircleX)) :=
    hm.comp (measurable_fst.prodMk ((AddCircle.continuous_mk' 1).measurable.comp (measurable_const.mul measurable_snd)))
  have hit := bounded_sq_integrable (volume.prod (intervalLaw a b)) htrial (fun z ↦ hb z.1 _)
  have hiu := bounded_sq_integrable (volume.prod volume) hm (fun z ↦ hb z.1 z.2)
  rw [integral_prod _ hit]
  have hle (s : CircleX) : (∫ γ, (u s ((c*γ : ℝ) : CircleX))^2 ∂intervalLaw a b) ≤
      D*(∫ t : CircleX, (u s t)^2) := by
    have hm' : Measurable (u s) := hm.comp (measurable_const.prodMk measurable_id)
    have hnon : 0≤∫ t : CircleX, (u s t)^2 := integral_nonneg fun t ↦ sq_nonneg _
    exact (circle_scaled_integral_bounds (bounded_sq_integrable volume hm' (hb s))
      (fun t ↦ sq_nonneg _) hab hc).2.trans (mul_le_mul_of_nonneg_right hD hnon)
  have h := integral_mono hit.integral_prod_left (hiu.integral_prod_left.const_mul D) hle
  dsimp only [Function.uncurry,u] at h
  rw [integral_const_mul,orientedWeight_sq positive hℓ hℓ1 hα hα2] at h
  exact h

lemma trial_pair_upper {a b c d ℓ α ε : ℝ} (hab : a<b) (hc : 0<c) (hd : 0<d)
    (hℓ : 0<ℓ) (hℓ1 : ℓ<1) (hα : 0<α) (hα2 : α≤1/2)
    (positive : Bool)
    (hdisc : ∀ x y : CircleX, ∀ r s : ℝ,
      |(phasePairLaw a b c d).real (Metric.ball x r ×ˢ Metric.ball y s) -
        volume.real (Metric.ball x r)*volume.real (Metric.ball y s)| ≤ ε) :
    (∫ z : CircleX × ℝ,
      orientedWeight positive ℓ α z.1 ((c*z.2 : ℝ) : CircleX)*
      orientedWeight positive ℓ α z.1 ((d*z.2 : ℝ) : CircleX)
      ∂(volume.prod (intervalLaw a b))) ≤
      1+(2*ℓ/(1-ℓ))^2+2*(1+ℓ)*α+4*(1/(ℓ*α))^2*ε := by
  let := intervalLaw_probability hab
  let u := orientedWeight positive ℓ α
  have hm : Measurable (Function.uncurry u) := measurable_orientedWeight positive ℓ α
  have hb := orientedWeight_bounds positive hℓ hα
  have hB : 0≤1/(ℓ*α) := by positivity
  have htrial (c : ℝ) : Measurable (fun z : CircleX × ℝ ↦ u z.1 ((c*z.2 : ℝ) : CircleX)) :=
    hm.comp (measurable_fst.prodMk ((AddCircle.continuous_mk' 1).measurable.comp (measurable_const.mul measurable_snd)))
  have hit := bounded_pair_integrable (volume.prod (intervalLaw a b)) (htrial c) (htrial d) hB
    (fun z ↦ hb z.1 _) (fun z ↦ hb z.1 _)
  have hiu := bounded_integrable (volume.prod volume) hm (fun z ↦ hb z.1 z.2)
  have hmean : ∀ s : CircleX, 0≤(∫ t : CircleX, u s t) ∧ (∫ t : CircleX, u s t)≤1/(ℓ*α) := by
    intro s
    refine ⟨integral_nonneg (fun t ↦ (hb s t).1),?_⟩
    have h := integral_mono (bounded_integrable volume (hm.comp (measurable_const.prodMk measurable_id)) (hb s))
      (integrable_const (1/(ℓ*α))) (fun t ↦ (hb s t).2)
    simpa using h
  have hig : Integrable (fun s : CircleX ↦ (∫ t : CircleX, u s t)^2) volume := by
    apply Integrable.of_bound (hiu.integral_prod_left.aestronglyMeasurable.pow 2) ((1/(ℓ*α))^2)
    exact ae_of_all _ fun s ↦ by
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (hmean s).1 (hmean s).2 2
  rw [integral_prod _ hit]
  have hle (s : CircleX) : (∫ γ, u s ((c*γ : ℝ) : CircleX)*u s ((d*γ : ℝ) : CircleX) ∂intervalLaw a b) ≤
      (∫ t : CircleX, u s t)^2+4*(1/(ℓ*α))^2*ε := by
    have h := product_weight_discrepancy hab hc hd hB (hm.comp (measurable_const.prodMk measurable_id))
      (fun t ↦ (hb s t).1) (fun t ↦ (hb s t).2)
      (fun r hr ↦ orientedWeight_isTwoArcs positive hℓ hℓ1 hα s hr) hdisc
    have := (abs_le.mp h).2
    dsimp only [Function.comp_apply,Function.uncurry_apply_pair,id_eq] at this
    linarith
  have h := integral_mono hit.integral_prod_left (hig.add (integrable_const _)) hle
  dsimp only [Pi.add_apply] at h
  rw [integral_add hig (integrable_const _)] at h
  simp only [integral_const,Measure.real,measure_univ,ENNReal.toReal_one,one_smul] at h
  have hg := orientedWeight_mean_sq positive hℓ hℓ1 hα hα2
  dsimp only [u] at h
  linarith

end CircleSampling

open MeasureTheory Set Filter
open scoped BigOperators ENNReal
namespace CircleSampling

open ContinuousCircleWeight.Sampling
variable {ι : Type uι} {κ : Type uκ} [Fintype ι] [Fintype κ] [Nonempty κ]

lemma ideal_error_bound {a b ℓ α A D ε : ℝ} (hab : a<b)
    (hℓ : 0<ℓ) (hℓ1 : ℓ<1) (hα : 0<α) (hα2 : α≤1/2)
    (hA : 0≤A) (hD : 0≤D) (hε : 0≤ε) (positive : Bool) (c : κ → ℝ)
    (hc : ∀ n, 0<c n) (hA' : ∀ n, A≤1-1/(c n*(b-a)))
    (hD' : ∀ n, 1+1/(c n*(b-a))≤D)
    (hdisc : ∀ n k, n≠k → ∀ x y : CircleX, ∀ r s : ℝ,
      |(phasePairLaw a b (c n) (c k)).real (Metric.ball x r ×ˢ Metric.ball y s) -
        volume.real (Metric.ball x r)*volume.real (Metric.ball y s)| ≤ ε) :
    (∫ γ : ι → ℝ, ∫ s : ι → CircleX,
      (idealAverage positive ℓ α c s γ-1)^2 ∂Measure.pi (fun _ ↦ volume)
      ∂Measure.pi (fun _ ↦ intervalLaw a b)) ≤
      (1+(2*ℓ/(1-ℓ))^2+2*(1+ℓ)*α+4*(1/(ℓ*α))^2*ε)^(Fintype.card ι) +
      (Fintype.card κ : ℝ)⁻¹*(D*((2/ℓ)*Real.log (1/(2*α))))^(Fintype.card ι) -
      2*(A*(1-2*α))^(Fintype.card ι)+1 := by
  let := intervalLaw_probability hab
  let μ := (volume : Measure CircleX).prod (intervalLaw a b)
  let u := fun n (z : CircleX × ℝ) ↦ orientedWeight positive ℓ α z.1 ((c n*z.2 : ℝ) : CircleX)
  have hu (n : κ) : Measurable (u n) :=
    (measurable_orientedWeight positive ℓ α).comp
      (measurable_fst.prodMk ((AddCircle.continuous_mk' 1).measurable.comp (measurable_const.mul measurable_snd)))
  have hu0 (n : κ) (z) : 0≤u n z := (orientedWeight_bounds positive hℓ hα _ _).1
  have huB (n : κ) (z) : ‖u n z‖≤1/(ℓ*α) := by
    rw [Real.norm_eq_abs,abs_of_nonneg (hu0 n z)]
    exact (orientedWeight_bounds positive hℓ hα _ _).2
  have hdiag0 : 0≤D*((2/ℓ)*Real.log (1/(2*α))) := by
    apply mul_nonneg hD
    apply mul_nonneg (by positivity)
    apply Real.log_nonneg
    exact (le_div_iff₀ (by positivity)).mpr (by linarith)
  have h := productAverage_error_bound (ι := ι) μ u hu (1/(ℓ*α)) huB
    (A*(1-2*α)) (1+(2*ℓ/(1-ℓ))^2+2*(1+ℓ)*α+4*(1/(ℓ*α))^2*ε)
    (D*((2/ℓ)*Real.log (1/(2*α)))) (mul_nonneg hA (by linarith)) (by positivity) hdiag0 hu0
    (fun n ↦ trial_mean_lower hab (hc n) hℓ hℓ1 hα hα2 positive (hA' n))
    (fun n k hnk ↦ trial_pair_upper hab (hc n) (hc k) hℓ hℓ1 hα hα2 positive (hdisc n k hnk))
    (fun n ↦ trial_sq_upper hab (hc n) hℓ hℓ1 hα hα2 positive (hD' n))
  have hi := productAverage_integrable (ι := ι) μ u hu (1/(ℓ*α)) huB
  have hi2 := productAverage_sq_integrable (ι := ι) μ u hu (1/(ℓ*α)) huB
  have herror : Integrable (fun z : ι → CircleX × ℝ ↦ (productAverage u z-1)^2)
      (Measure.pi (fun _ : ι ↦ μ)) := by
    have heq : (fun z : ι → CircleX × ℝ ↦ (productAverage u z-1)^2) =
        (fun z ↦ productAverage u z ^ 2 - 2 * productAverage u z + 1) := by funext z; ring
    rw [heq]
    exact (hi2.sub (hi.const_mul 2)).add (integrable_const 1)
  let e := MeasurableEquiv.arrowProdEquivProdArrow CircleX ℝ ι
  have he := measurePreserving_arrowProdEquivProdArrow CircleX ℝ ι
    (fun _ ↦ volume) (fun _ ↦ intervalLaw a b)
  have he' := MeasurePreserving.symm e he
  have hf : (fun z : (ι → CircleX)×(ι → ℝ) ↦ (idealAverage positive ℓ α c z.1 z.2-1)^2) =
      (fun z ↦ (productAverage u (e.symm z)-1)^2) := rfl
  have hif : Integrable (fun z : (ι → CircleX)×(ι → ℝ) ↦ (idealAverage positive ℓ α c z.1 z.2-1)^2)
      ((Measure.pi (fun _ : ι ↦ (volume : Measure CircleX))).prod (Measure.pi (fun _ : ι ↦ intervalLaw a b))) := by
    rw [hf]
    exact he'.integrable_comp_of_integrable herror
  have hint := he'.integral_comp e.symm.measurableEmbedding (fun z ↦ (productAverage (ι := ι) u z-1)^2)
  rw [← hint] at h
  change (∫ z : (ι → CircleX)×(ι → ℝ), (idealAverage positive ℓ α c z.1 z.2-1)^2
    ∂((Measure.pi (fun _ : ι ↦ (volume : Measure CircleX))).prod (Measure.pi (fun _ : ι ↦ intervalLaw a b)))) ≤ _ at h
  rw [integral_prod_symm _ hif] at h
  exact h

end CircleSampling

end

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_SamplingBounds
attribute [-instance] _root_.OAI.CircleCoupling.labelMeasurableSpace
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
open Filter Set
open scoped Topology
section
open ContinuousCircleWeight.Sampling
open Filter Set MeasureTheory
open scoped Topology
lemma sampling_discrepancy_numeric {m : ℕ} (hm : 1 ≤ m) {N : ℝ} (hN : 0 < N) :
    8*2*scaleDiscrepancy m/18 + 2/(4*((m^300:ℕ):ℝ)*((m:ℝ)^(-(70:ℝ)))^2) +
      ((m^300:ℕ):ℝ)^2/(Real.pi*(N*(m:ℝ)^1000)*(2/N-1/N)) ≤ scaleDiscrepancy m := by
  have hx1 : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hx : (0:ℝ) < m := zero_lt_one.trans_le hx1
  have he2 : 2/(4*((m^300:ℕ):ℝ)*((m:ℝ)^(-(70:ℝ)))^2) =
      (1/2)*(m:ℝ)^(-(160:ℝ)) := by
    rw [Nat.cast_pow, ← Real.rpow_natCast (m:ℝ) 300, rpow_scale_sq _ hx.le]
    norm_num only [Nat.cast_ofNat]
    have hprod : (m:ℝ)^(300:ℝ)*(m:ℝ)^(-(70:ℝ)*2)=(m:ℝ)^(160:ℝ) := by
      rw [rpow_scale_mul _ hx]; norm_num
    have hexp : -(70:ℝ)*2 = -(140:ℝ) := by norm_num
    rw [hexp] at hprod
    rw [mul_assoc, hprod, div_mul_eq_div_div, div_eq_mul_inv, ← Real.rpow_neg hx.le]
    ring
  have he3 : ((m^300:ℕ):ℝ)^2/(Real.pi*(N*(m:ℝ)^1000)*(2/N-1/N)) =
      (1/Real.pi)*(m:ℝ)^(-(400:ℝ)) := by
    have hden : Real.pi*(N*(m:ℝ)^1000)*(2/N-1/N) = Real.pi*(m:ℝ)^1000 := by
      field_simp
      ring
    rw [hden,Nat.cast_pow,← Real.rpow_natCast (m:ℝ) 300, rpow_scale_sq _ hx.le]
    rw [← Real.rpow_natCast (m:ℝ) 1000]
    norm_num only [Nat.cast_ofNat]
    calc
      (m:ℝ)^(600:ℝ)/(Real.pi*(m:ℝ)^(1000:ℝ)) =
          (1/Real.pi)*((m:ℝ)^(600:ℝ)/(m:ℝ)^(1000:ℝ)) := by ring
      _ = _ := by rw [← Real.rpow_sub hx]; norm_num
  have hle2 : (m:ℝ)^(-(160:ℝ)) ≤ (m:ℝ)^(-(70:ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
  have hle3 : (m:ℝ)^(-(400:ℝ)) ≤ (m:ℝ)^(-(70:ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
  have hpi : 1/Real.pi ≤ 1 := (div_le_one Real.pi_pos).mpr (by linarith [Real.pi_gt_three] : (1:ℝ) ≤ Real.pi)
  rw [he2,he3]
  have hp : 0 ≤ (m:ℝ)^(-(400:ℝ)) := Real.rpow_nonneg hx.le _
  have hmul := mul_le_mul_of_nonneg_right hpi hp
  unfold scaleDiscrepancy
  nlinarith [Real.rpow_nonneg hx.le (-(70:ℝ))]

lemma sampling_phase_discrepancy {m : ℕ} (hm : 1 ≤ m) {N c d : ℝ}
    (hN : 0 < N) (hc : 0 < c) (hd : 0 < d)
    (hmc : 1+1/(c*(2/N-1/N)) ≤ 2) (hmd : 1+1/(d*(2/N-1/N)) ≤ 2)
    (hsep : ∀ v w : ℤ, |v| ≤ (m^300:ℕ) → |w| ≤ (m^300:ℕ) →
      (v ≠ 0 ∨ w ≠ 0) → N*(m:ℝ)^1000 ≤ |(v:ℝ)*c+(w:ℝ)*d|)
    (x y : CircleX) (r s : ℝ) :
    |(phasePairLaw (1/N) (2/N) c d).real (Metric.ball x r ×ˢ Metric.ball y s) -
      volume.real (Metric.ball x r)*volume.real (Metric.ball y s)| ≤ scaleDiscrepancy m := by
  have hx : (0:ℝ) < m := Nat.cast_pos.mpr (by omega)
  have hab : 1/N < 2/N := (div_lt_div_iff_of_pos_right hN).mpr (by norm_num)
  have hh := separated_phase_rectangle_bound hab hc hd (by positivity : 0 < N*(m:ℝ)^1000)
    (by norm_num : (0:ℝ) ≤ 2) hmc hmd (H:=m^300) (by positivity)
    (fun v w hv hw hne => hsep v w hv.le hw.le (not_and_or.mp hne))
    (δ:=(m:ℝ)^(-(70:ℝ))) (by positivity) x y r s
  apply hh.trans
  have hn := sampling_discrepancy_numeric hm hN
  unfold scaleDiscrepancy at hn ⊢
  linarith only [hn]
end
section
open ContinuousCircleWeight.Sampling
open Filter Set MeasureTheory
open scoped Topology

lemma ideal_stage_error {m K : ℕ} (hK : 0 < K) (hn : IdealNumerics K m)
    {κ : Type uκ} [Fintype κ] [Nonempty κ] (positive : Bool) (c : κ → ℝ)
    (hcard : (m:ℝ)^((69:ℝ)/100*m) ≤ (Fintype.card κ:ℝ))
    (hc : ∀ n, (m:ℝ)^((7:ℝ)/10*m)/2 ≤ c n)
    (hsep : ∀ n k, n ≠ k → ∀ v w : ℤ,
      |v| ≤ (m^300:ℕ) → |w| ≤ (m^300:ℕ) → (v ≠ 0 ∨ w ≠ 0) →
      ((m:ℝ)*K)*(m:ℝ)^1000 ≤ |(v:ℝ)*c n+(w:ℝ)*c k|) :
    (∫ γ : Fin m → ℝ, ∫ s : Fin m → CircleX,
      (idealAverage positive (scaleEll m) (scaleAlpha m) c s γ-1)^2
      ∂Measure.pi (fun _ ↦ volume)
      ∂Measure.pi (fun _ ↦ intervalLaw (1/((m:ℝ)*K)) (2/((m:ℝ)*K)))) ≤ samplingError m := by
  obtain ⟨hm,hℓ1,hα3,hd,hmean⟩ := hn
  have hm0 : 0 < m := by omega
  have hx : (0:ℝ) < m := Nat.cast_pos.mpr hm0
  have hN : 0 < (m:ℝ)*K := mul_pos hx (Nat.cast_pos.mpr hK)
  have hℓ : 0 < scaleEll m := Real.rpow_pos_of_pos hx _
  have hα := scaleAlpha_pos hm0
  have hα2 : scaleAlpha m ≤ 1/2 := by linarith
  have hab : 1/((m:ℝ)*K) < 2/((m:ℝ)*K) := (div_lt_div_iff_of_pos_right hN).mpr (by norm_num)
  have hcm (n : κ) := hmean (c n) (hc n)
  have hD (n : κ) : 1+1/(c n*(2/((m:ℝ)*K)-1/((m:ℝ)*K))) ≤ 2 := by
    linarith [(hcm n).2]
  have hdisc (n k : κ) (hnk : n ≠ k) (x y : CircleX) (r s : ℝ) :=
    sampling_phase_discrepancy (by omega : 1 ≤ m) hN (hcm n).1 (hcm k).1
      (hD n) (hD k) (hsep n k hnk) x y r s
  have he := ideal_error_bound (ι:=Fin m) hab hℓ hℓ1 hα hα2
    (by linarith : 0 ≤ 1-scaleAlpha m) (by norm_num : (0:ℝ) ≤ 2)
    (by unfold scaleDiscrepancy; positivity) positive c (fun n => (hcm n).1)
    (fun n => by linarith [(hcm n).2]) hD hdisc
  simp only [Fintype.card_fin] at he
  have hdiag0 : 0 ≤ 2*((2/scaleEll m)*Real.log (1/(2*scaleAlpha m))) := by
    apply mul_nonneg (by norm_num)
    apply mul_nonneg (by positivity)
    exact Real.log_nonneg ((le_div_iff₀ (by positivity)).mpr (by linarith))
  have hdiag : (Fintype.card κ:ℝ)⁻¹ * (2*((2/scaleEll m)*Real.log (1/(2*scaleAlpha m))))^m ≤ (1/2:ℝ)^m := by
    have hpow : ((m:ℝ)^((69:ℝ)/100))^m = (m:ℝ)^((69:ℝ)/100*m) := by
      rw [← Real.rpow_natCast,← Real.rpow_mul hx.le]
    have hcpos : (0:ℝ) < Fintype.card κ := Nat.cast_pos.mpr Fintype.card_pos
    rw [mul_comm ((Fintype.card κ:ℝ)⁻¹), ← div_eq_mul_inv]
    apply (div_le_iff₀ hcpos).mpr
    calc
      (2*((2/scaleEll m)*Real.log (1/(2*scaleAlpha m))))^m ≤
        ((1/2)*(m:ℝ)^((69:ℝ)/100))^m := pow_le_pow_left₀ hdiag0 hd m
      _ = (1/2:ℝ)^m*(m:ℝ)^((69:ℝ)/100*m) := by rw [mul_pow,hpow]
      _ ≤ (1/2:ℝ)^m*(Fintype.card κ:ℝ) := by gcongr
  have hbase : 0 ≤ 1-3*scaleAlpha m := by linarith
  have hmeanpow : (1-3*scaleAlpha m)^m ≤ ((1-scaleAlpha m)*(1-2*scaleAlpha m))^m := by
    apply pow_le_pow_left₀ hbase _ m
    nlinarith [sq_nonneg (scaleAlpha m)]
  unfold samplingError
  have hoff : 1+(2*scaleEll m/(1-scaleEll m))^2+2*(1+scaleEll m)*scaleAlpha m+
      4*(1/(scaleEll m*scaleAlpha m))^2*scaleDiscrepancy m = 1+offError m := by
    unfold offError
    ring
  rw [hoff] at he
  linarith
end
open ContinuousCircleWeight.Sampling
open Set MeasureTheory

lemma measurableSet_phaseFailure (b c : ℝ) : MeasurableSet (phaseFailure b c) := by
  apply MeasurableSet.compl
  exact (measurableSet_lt measurable_const (measurable_const.sub
    (measurable_repr.comp ((AddCircle.continuous_mk' 1).measurable.comp (measurable_const.mul measurable_id))))).inter
    (measurableSet_lt (measurable_const.sub
      (measurable_repr.comp ((AddCircle.continuous_mk' 1).measurable.comp (measurable_const.mul measurable_id)))) measurable_const)

lemma phaseFailure_norm (b c γ : ℝ) (hγ : γ ∈ phaseFailure b c) :
    ‖((c*γ:ℝ):CircleX)‖ ≤ b := by
  let x : CircleX := ((c*γ:ℝ):CircleX)
  have h1 : ‖x‖ ≤ repr x := by
    calc
      ‖x‖ = ‖((repr x:ℝ):CircleX)‖ := by rw [coe_repr]
      _ ≤ ‖repr x‖ := QuotientAddGroup.norm_mk_le_norm
      _ = repr x := Real.norm_of_nonneg (repr_mem x).1
  have hx : ((repr x-1:ℝ):CircleX)=x := by
    rw [AddCircle.coe_sub,coe_repr]
    simp
  have h2 : ‖x‖ ≤ 1-repr x := by
    calc
      ‖x‖ = ‖((repr x-1:ℝ):CircleX)‖ := by rw [hx]
      _ ≤ ‖repr x-1‖ := QuotientAddGroup.norm_mk_le_norm
      _ = 1-repr x := by
        rw [Real.norm_eq_abs,abs_of_nonpos (by linarith [(repr_mem x).2])]; ring
  change ¬ (b < 1-repr x ∧ 1-repr x < 1-b) at hγ
  by_contra hb
  have hb' : b < ‖x‖ := lt_of_not_ge hb
  exact hγ ⟨hb'.trans_le h2,by linarith [hb'.trans_le h1]⟩

lemma interval_phase_ball_bound {a b c r : ℝ} (hab : a < b) (hc : 0 < c)
    (hr : 0 ≤ r) :
    (intervalLaw a b).real {γ | ‖((c*γ:ℝ):CircleX)‖ ≤ r} ≤
      (1+1/(c*(b-a)))*(2*r) := by
  have h := phasePairLaw_marginal_fst (d:=0) hab hc (Metric.closedBall (0:CircleX) r)
    measurableSet_closedBall
  rw [Measure.real,phasePairLaw,Measure.map_apply (continuous_phasePair c 0).measurable
    (measurableSet_closedBall.preimage measurable_fst)] at h
  have heq : (phasePair c 0 ⁻¹' (Prod.fst ⁻¹' Metric.closedBall (0:CircleX) r)) =
      {γ | ‖((c*γ:ℝ):CircleX)‖ ≤ r} := by ext γ; simp [phasePair,Metric.mem_closedBall,dist_zero_right]
  rw [heq] at h
  apply h.trans
  gcongr
  rw [Measure.real,AddCircle.volume_closedBall]
  rw [ENNReal.toReal_ofReal (le_min (by norm_num : (0:ℝ) ≤ 1) (mul_nonneg (by norm_num) hr))]
  exact min_le_right _ _

lemma phase_failure_probability {N b c : ℝ} (hN : 0 < N) (hb : 0 ≤ b)
    (hc : N/4 ≤ |c|) :
    intervalLaw (1/N) (2/N) (phaseFailure b c) ≤ ENNReal.ofReal (10*b) := by
  have hab : 1/N < 2/N := (div_lt_div_iff_of_pos_right hN).mpr (by norm_num)
  let := intervalLaw_probability hab
  have hc0 : 0 < |c| := (by positivity : 0 < N/4).trans_le hc
  have hnorm (γ : ℝ) : ‖((c*γ:ℝ):CircleX)‖=‖((|c| *γ:ℝ):CircleX)‖ := by
    rcases le_total 0 c with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_nonpos h,neg_mul,AddCircle.coe_neg,norm_neg]
  have hsub : phaseFailure b c ⊆ {γ | ‖((|c| *γ:ℝ):CircleX)‖ ≤ b} := by
    intro γ hγ
    rw [Set.mem_ofPred_eq,← hnorm]
    exact phaseFailure_norm b c γ hγ
  have hC : 1+1/(|c| *(2/N-1/N)) ≤ 5 := by
    have hh : 2/N-1/N = 1/N := by ring
    rw [hh]
    have hden : (1/4:ℝ) ≤ |c| *(1/N) := by
      have hh : (1/4:ℝ) ≤ |c| /N := (le_div_iff₀ hN).mpr (by linarith only [hc])
      simpa only [div_eq_mul_inv, mul_comm, mul_one, one_mul] using hh
    have hle := one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 1/4) hden
    norm_num only [one_div_div, div_one] at hle
    linarith only [hle]
  have hμ : (intervalLaw (1/N) (2/N)).real (phaseFailure b c) ≤ 10*b := by
    calc
      _ ≤ (intervalLaw (1/N) (2/N)).real {γ | ‖((|c| *γ:ℝ):CircleX)‖ ≤ b} :=
        ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)
      _ ≤ (1+1/(|c| *(2/N-1/N)))*(2*b) := interval_phase_ball_bound hab hc0 hb
      _ ≤ 5*(2*b) := mul_le_mul_of_nonneg_right hC (by positivity)
      _ = 10*b := by ring
  rw [← ENNReal.ofReal_toReal (measure_ne_top (intervalLaw (1/N) (2/N)) (phaseFailure b c))]
  exact ENNReal.ofReal_le_ofReal hμ


end CircleSampling

end

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_TrialBounds
attribute [-instance] _root_.OAI.CircleCoupling.labelMeasurableSpace
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

lemma phase_union_numeric {m : ℕ} (hm : 0 < m)
    (hp : 10*(m:ℝ)^(-(19:ℝ)/20) ≤ 1) :
    3*(m:ℝ)^((4:ℝ)/5*m)*2^m*(10*(m:ℝ)^(-(19:ℝ)/20))^(m-m/20) ≤
      phaseUnionBound m := by
  have hx : (0:ℝ) < m := Nat.cast_pos.mpr hm
  have hp0 : 0 < 10*(m:ℝ)^(-(19:ℝ)/20) := by positivity
  have hpow : (10*(m:ℝ)^(-(19:ℝ)/20))^(m-m/20) ≤
      (10*(m:ℝ)^(-(19:ℝ)/20))^((9:ℝ)/10*m) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_ge hp0 hp (phase_failure_count_lower m)
  calc
    _ ≤ 3*(m:ℝ)^((4:ℝ)/5*m)*2^m*(10*(m:ℝ)^(-(19:ℝ)/20))^((9:ℝ)/10*m) := by gcongr
    _ = phaseUnionBound m := by
      unfold phaseUnionBound
      rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 10) (Real.rpow_nonneg hx.le _)]
      rw [← Real.rpow_mul hx.le, ← Real.rpow_natCast (2:ℝ) m]
      rw [← Real.rpow_natCast (2*(10:ℝ)^((9:ℝ)/10)*(m:ℝ)^(-(11:ℝ)/200)) m]
      rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) (by positivity)]
      rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 10), ← Real.rpow_mul hx.le]
      have he : (m:ℝ)^((4:ℝ)/5*m)*(m:ℝ)^(-(19:ℝ)/20*((9:ℝ)/10*m)) =
          (m:ℝ)^(-(11:ℝ)/200*m) := by
        rw [← Real.rpow_add hx]
        congr 1
        ring
      calc
        _ = 3*(2:ℝ)^(m:ℝ)*(10:ℝ)^((9:ℝ)/10*m)*
            ((m:ℝ)^((4:ℝ)/5*m)*(m:ℝ)^(-(19:ℝ)/20*((9:ℝ)/10*m))) := by ring
        _ = _ := by rw [he]; ring

open ContinuousCircleWeight.Sampling
open scoped Classical ENNReal

lemma phase_few_successes_subset (m : ℕ) (b c : ℝ) :
    {γ : Fin m → ℝ | (((Finset.univ.filter fun i => γ i ∉ phaseFailure b c).card:ℕ):ℝ) < (m:ℝ)/20} ⊆
      {γ | m-m/20 ≤ (Finset.univ.filter fun i => γ i ∈ phaseFailure b c).card} := by
  intro γ hγ
  have hsum := Finset.card_filter_add_card_filter_not (s:=Finset.univ)
    (fun i : Fin m => γ i ∈ phaseFailure b c)
  simp only [Finset.card_univ,Fintype.card_fin] at hsum
  have hle : (Finset.univ.filter fun i : Fin m => γ i ∉ phaseFailure b c).card ≤ m/20 := by
    apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 20)).mpr
    have hreal : ((Finset.univ.filter fun i : Fin m => γ i ∉ phaseFailure b c).card:ℝ)*20 ≤ (m:ℝ) := by
      change ((Finset.univ.filter fun i : Fin m => γ i ∉ phaseFailure b c).card:ℝ) < (m:ℝ)/20 at hγ
      linarith
    exact_mod_cast hreal
  change m-m/20 ≤ _
  omega

lemma phase_cover_union_bound {m K : ℕ} (hm : 0 < m) (hK : 0 < K)
    (hp : 10*(m:ℝ)^(-(19:ℝ)/20) ≤ 1) (S : Finset ℤ)
    (hS : (S.card:ℝ) ≤ 3*(m:ℝ)^((4:ℝ)/5*m))
    (hc : ∀ k∈S, ((m:ℝ)*K)/4 ≤ |(k:ℝ)|) :
    Measure.pi (fun _ : Fin m => intervalLaw (1/((m:ℝ)*K)) (2/((m:ℝ)*K)))
      {γ | ∃ k∈S, (((Finset.univ.filter fun i => γ i ∉ phaseFailure ((m:ℝ)^(-(19:ℝ)/20)) k).card:ℕ):ℝ) < (m:ℝ)/20}
      ≤ ENNReal.ofReal (phaseUnionBound m) := by
  let N : ℝ := (m:ℝ)*K
  let b : ℝ := (m:ℝ)^(-(19:ℝ)/20)
  let μ : Measure ℝ := intervalLaw (1/N) (2/N)
  have hN : 0 < N := mul_pos (Nat.cast_pos.mpr hm) (Nat.cast_pos.mpr hK)
  have hb : 0 ≤ b := Real.rpow_nonneg (Nat.cast_nonneg _) _
  let : IsProbabilityMeasure μ := intervalLaw_probability ((div_lt_div_iff_of_pos_right hN).mpr (by norm_num))
  let A (k : ℤ) : Set (Fin m → ℝ) :=
    {γ | m-m/20 ≤ (Finset.univ.filter fun i => γ i ∈ phaseFailure b k).card}
  have hbound (k : ℤ) (hk : k∈S) : Measure.pi (fun _ : Fin m => μ) (A k) ≤
      (2:ℝ≥0∞)^m*(ENNReal.ofReal (10*b))^(m-m/20) := by
    have he := product_many_failures_exp_bound (fun _ : Fin m => μ) Finset.univ
      (fun _ => phaseFailure b k) (fun _ => measurableSet_phaseFailure _ _) (m-m/20)
      (ENNReal.ofReal (10*b)) (fun _ _ => phase_failure_probability hN hb (hc k hk))
    simpa only [Measure.infinitePi_eq_pi,Finset.card_univ,Fintype.card_fin] using he
  have hcover : {γ : Fin m → ℝ | ∃ k∈S,
      (((Finset.univ.filter fun i => γ i ∉ phaseFailure b k).card:ℕ):ℝ) < (m:ℝ)/20} ⊆ ⋃ k∈S, A k := by
    rintro γ ⟨k,hk,hγ⟩
    exact mem_iUnion.mpr ⟨k,mem_iUnion.mpr ⟨hk,phase_few_successes_subset m b k hγ⟩⟩
  change Measure.pi (fun _ : Fin m => μ) _ ≤ _
  calc
    _ ≤ Measure.pi (fun _ : Fin m => μ) (⋃ k∈S, A k) := measure_mono hcover
    _ ≤ ∑ k∈S, Measure.pi (fun _ : Fin m => μ) (A k) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _k∈S, (2:ℝ≥0∞)^m*(ENNReal.ofReal (10*b))^(m-m/20) :=
      Finset.sum_le_sum hbound
    _ = ENNReal.ofReal ((S.card:ℝ)*2^m*(10*b)^(m-m/20)) := by
      simp only [Finset.sum_const,nsmul_eq_mul]
      have he : ENNReal.ofReal ((S.card:ℝ)*2^m*(10*b)^(m-m/20)) =
          (S.card:ℝ≥0∞)*2^m*(ENNReal.ofReal (10*b))^(m-m/20) := by
        conv_lhs => rw [ENNReal.ofReal_mul (by positivity)]
        conv_lhs => lhs; rw [ENNReal.ofReal_mul (by positivity)]
        rw [ENNReal.ofReal_natCast,ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 2),
          ENNReal.ofReal_ofNat,ENNReal.ofReal_pow (by positivity)]
      rw [he,mul_assoc]
    _ ≤ ENNReal.ofReal (3*(m:ℝ)^((4:ℝ)/5*m)*2^m*(10*b)^(m-m/20)) := by
      apply ENNReal.ofReal_le_ofReal
      gcongr
    _ ≤ ENNReal.ofReal (phaseUnionBound m) := ENNReal.ofReal_le_ofReal (phase_union_numeric hm hp)
end
section
open ContinuousCircleWeight.Sampling
open MeasureTheory Set
lemma intervalLaw_ae_inner (a b : ℝ) : ∀ᵐ x ∂intervalLaw a b, x ∈ Ioo a b := by
  have h : ∀ᵐ x ∂volume.restrict (Ioc a b), x ∈ Ioo a b := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc,ae_restrict_of_ae (volume.ae_ne b)] with x hx hxb
    exact ⟨hx.1,hx.2.lt_of_ne hxb⟩
  exact Measure.ae_smul_measure h _
lemma intervalLaw_ae_phase {a b c : ℝ} (hc : c ≠ 0) :
    ∀ᵐ x ∂intervalLaw a b, ((c*x:ℝ):CircleX) ≠ 0 := by
  have h : ∀ᵐ x ∂(volume : Measure ℝ), ∀ k : ℤ, x ≠ (k:ℝ)/c :=
    ae_all_iff.mpr fun k => volume.ae_ne _
  have h' := Measure.ae_smul_measure (ae_restrict_of_ae (s:=Ioc a b) h) (ENNReal.ofReal (b-a))⁻¹
  filter_upwards [h'] with x hx heq
  obtain ⟨k,hk⟩ := (AddCircle.coe_eq_zero_iff 1).mp heq
  apply hx k
  apply (eq_div_iff hc).mpr
  simpa [zsmul_eq_mul,mul_comm] using hk.symm
end
section
open ContinuousCircleWeight.Sampling MeasureTheory Set
lemma pi_intervalLaw_ae_all_integerPhases {ι : Type uι} [Fintype ι]
    {a b : ℝ} (hab : a < b) :
    ∀ᵐ γ : ι → ℝ ∂Measure.pi (fun _ => intervalLaw a b),
      (∀ i, γ i ∈ Ioo a b) ∧ ∀ k : ℤ, k ≠ 0 → ∀ i, ((k*γ i:ℝ):CircleX) ≠ 0 := by
  let := intervalLaw_probability hab
  have h1 : ∀ᵐ γ : ι → ℝ ∂Measure.pi (fun _ => intervalLaw a b), ∀ i, γ i ∈ Ioo a b := by
    apply ae_all_iff.mpr
    intro i
    exact (measurePreserving_eval (fun _ : ι => intervalLaw a b) i).quasiMeasurePreserving.ae (intervalLaw_ae_inner a b)
  have h2 : ∀ᵐ γ : ι → ℝ ∂Measure.pi (fun _ => intervalLaw a b), ∀ k : ℤ, k ≠ 0 → ∀ i, ((k*γ i:ℝ):CircleX) ≠ 0 := by
    apply ae_all_iff.mpr
    intro k
    by_cases hk : k=0
    · exact Filter.Eventually.of_forall (by simp [hk])
    apply ae_all_iff.mpr
    intro _
    apply ae_all_iff.mpr
    intro i
    exact (measurePreserving_eval (fun _ : ι => intervalLaw a b) i).quasiMeasurePreserving.ae
      (intervalLaw_ae_phase (by exact_mod_cast hk))
  exact h1.and h2
end
open Set MeasureTheory
open scoped ENNReal Classical
open ContinuousCircleWeight.Sampling Filter
open scoped Topology

lemma exists_ideal_trial {m K : ℕ} (hK : 0 < K) (hn : IdealNumerics K m)
    {τ : Type uτ} [Fintype τ] {κ : τ → Type uκ} [∀ t, Fintype (κ t)] [∀ t, Nonempty (κ t)]
    (positive : τ → Bool) (c : ∀ t, κ t → ℝ)
    (hcard : ∀ t, (m:ℝ)^((69:ℝ)/100*m) ≤ (Fintype.card (κ t):ℝ))
    (hc : ∀ t n, (m:ℝ)^((7:ℝ)/10*m)/2 ≤ c t n)
    (hsep : ∀ t n k, n ≠ k → ∀ v w : ℤ,
      |v| ≤ (m^300:ℕ) → |w| ≤ (m^300:ℕ) → (v ≠ 0 ∨ w ≠ 0) →
      ((m:ℝ)*K)*(m:ℝ)^1000 ≤ |(v:ℝ)*c t n+(w:ℝ)*c t k|)
    (hp : 10*(m:ℝ)^(-(19:ℝ)/20) ≤ 1) (S : Finset ℤ)
    (hS : (S.card:ℝ) ≤ 3*(m:ℝ)^((4:ℝ)/5*m))
    (hcS : ∀ k∈S, ((m:ℝ)*K)/4 ≤ |(k:ℝ)|)
    {δ : ℝ} (hδ : 0 < δ)
    (hbudget : phaseUnionBound m+(Fintype.card τ:ℝ)*(samplingError m/δ) < 1) :
    ∃ γ : Fin m → ℝ,
      (∀ i, γ i ∈ Set.Ioo (1/((m:ℝ)*K)) (2/((m:ℝ)*K))) ∧
      (∀ k : ℤ, k ≠ 0 → ∀ i, ((k*γ i:ℝ):CircleX) ≠ 0) ∧
      (∀ k∈S, (m:ℝ)/20 ≤ (((Finset.univ.filter fun i => γ i ∉ phaseFailure ((m:ℝ)^(-(19:ℝ)/20)) k).card:ℕ):ℝ)) ∧
      ∀ t, idealEnergy (positive t) (scaleEll m) (scaleAlpha m) (c t) γ < δ := by
  have hm : 0 < m := by have := hn.1; omega
  have hN : 0 < (m:ℝ)*K := mul_pos (Nat.cast_pos.mpr hm) (Nat.cast_pos.mpr hK)
  have hab : 1/((m:ℝ)*K) < 2/((m:ℝ)*K) := (div_lt_div_iff_of_pos_right hN).mpr (by norm_num)
  let μ := Measure.pi (fun _ : Fin m => intervalLaw (1/((m:ℝ)*K)) (2/((m:ℝ)*K)))
  let := intervalLaw_probability hab
  let E (t : τ) : (Fin m → ℝ) → ℝ := idealEnergy (κ:=κ t) (positive t) (scaleEll m) (scaleAlpha m) (c t)
  let bad := {γ : Fin m → ℝ | ∃ k∈S,
    (((Finset.univ.filter fun i => γ i ∉ phaseFailure ((m:ℝ)^(-(19:ℝ)/20)) k).card:ℕ):ℝ) < (m:ℝ)/20}
  have hℓ : 0 < scaleEll m := Real.rpow_pos_of_pos (Nat.cast_pos.mpr hm) _
  have hα := scaleAlpha_pos hm
  obtain ⟨γ,hγ,hgood,hE⟩ := exists_good_finite_family μ E
    (fun t => idealEnergy_nonneg (positive t) _ _ (c t))
    (fun t => idealEnergy_integrable (positive t) hℓ hα (c t) μ)
    hδ (by unfold phaseUnionBound; positivity)
    (fun t => ideal_stage_error hK hn (positive t) (c t) (hcard t) (hc t) (hsep t))
    bad (phase_cover_union_bound hm hK hp S hS hcS) hbudget
    (pi_intervalLaw_ae_all_integerPhases (ι:=Fin m) hab)
  refine ⟨γ,hγ.1,hγ.2,?_,hE⟩
  intro k hk
  exact le_of_not_gt (fun h => hgood ⟨k,hk,h⟩)


end CircleSampling

end

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_FiniteSampling
attribute [-instance] _root_.OAI.CircleCoupling.labelMeasurableSpace
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

section
open scoped Topology
lemma continuousAt_repr {x : CircleX} (hx : x ≠ 0) : ContinuousAt repr x :=
  continuous_subtype_val.continuousAt.comp (AddCircle.continuousAt_equivIco 1 0 (by simpa using hx))
lemma continuous_delta : Continuous delta := by unfold delta; fun_prop
lemma repr_pos {x : CircleX} (hx : x ≠ 0) : 0 < repr x := by
  apply (repr_mem x).1.lt_of_ne'
  intro h
  apply hx
  rw [← coe_repr x,h]
  simp

lemma continuousAt_weight {ℓ α s t : ℝ} (hℓ : 0 < ℓ) (hα : 0 < α)
    (hαs : α ≠ delta s) (ht : 0 < t) (hst : t ≠ ℓ*delta s) :
    ContinuousAt (fun z : ℝ × ℝ => weight ℓ α z.1 z.2) (s,t) := by
  have hd := (continuous_delta.comp continuous_fst).continuousAt (x:=(s,t))
  have ht' := continuous_snd.continuousAt (x:=(s,t))
  by_cases ha : α ≤ delta s
  · have had : α < delta s := lt_of_le_of_ne ha hαs
    have hea : ∀ᶠ z : ℝ × ℝ in 𝓝 (s,t), α ≤ delta z.1 := by
      filter_upwards [hd.eventually (lt_mem_nhds had)] with z hz
      exact hz.le
    have het : ∀ᶠ z : ℝ × ℝ in 𝓝 (s,t), 0 < z.2 := ht'.eventually (lt_mem_nhds ht)
    by_cases hb : t < ℓ*delta s
    · have heb : ∀ᶠ z : ℝ × ℝ in 𝓝 (s,t), z.2 < ℓ*delta z.1 :=
        (ht'.sub (hd.const_mul ℓ)).eventually (gt_mem_nhds (by linarith : t-ℓ*delta s < 0))
          |>.mono fun z h => by change z.2-ℓ*delta z.1 < 0 at h; linarith
      have heq : (fun z : ℝ × ℝ => weight ℓ α z.1 z.2) =ᶠ[𝓝 (s,t)]
          (fun z => 1/(ℓ*delta z.1)) := by
        filter_upwards [hea,het,heb] with z ha ht hb
        simp only [weight,ha,ht,hb,and_self,ite_true]
      exact (continuousAt_const.div (hd.const_mul ℓ)
        (mul_pos hℓ (hα.trans_le ha)).ne').congr_of_eventuallyEq heq
    · have hb' : ℓ*delta s < t := lt_of_le_of_ne (le_of_not_gt hb) (Ne.symm hst)
      have heb : ∀ᶠ z : ℝ × ℝ in 𝓝 (s,t), ℓ*delta z.1 < z.2 := by
        filter_upwards [(ht'.sub (hd.const_mul ℓ)).eventually (lt_mem_nhds (sub_pos.mpr hb'))] with z hz
        exact sub_pos.mp hz
      have heq : (fun z : ℝ × ℝ => weight ℓ α z.1 z.2) =ᶠ[𝓝 (s,t)] (fun _ => (0:ℝ)) := by
        filter_upwards [heb] with z hz
        simp [weight,not_lt_of_ge hz.le]
      exact continuousAt_const.congr_of_eventuallyEq heq
  · have ha' : delta s < α := lt_of_not_ge ha
    have heq : (fun z : ℝ × ℝ => weight ℓ α z.1 z.2) =ᶠ[𝓝 (s,t)] (fun _ => (0:ℝ)) := by
      filter_upwards [hd.eventually (gt_mem_nhds ha')] with z hz
      change delta z.1 < α at hz
      simp [weight,not_le_of_gt hz]
    exact continuousAt_const.congr_of_eventuallyEq heq

lemma ae_repr_ne (r : ℝ) : ∀ᵐ s : CircleX, repr s ≠ r := by
  have he : ∀ᵐ s : CircleX, s ≠ (r:CircleX) := by
    rw [ae_iff]
    simpa only [not_not,Set.ofPred_eq_eq_singleton] using volume_singleton_zero (r:CircleX)
  filter_upwards [he] with s hs heq
  exact hs (by rw [← coe_repr s,heq])
lemma ae_delta_ne (r : ℝ) : ∀ᵐ s : CircleX, delta (repr s) ≠ r := by
  filter_upwards [ae_repr_ne r,ae_repr_ne (1-r)] with s hs ht h
  unfold delta at h
  rcases le_total (repr s) (1-repr s) with hle | hle
  · exact hs (by rwa [min_eq_left hle] at h)
  · exact ht (by rw [min_eq_right hle] at h; linarith)

lemma ae_continuousAt_uPos {ℓ α : ℝ} (hℓ : 0 < ℓ) (hα : 0 < α)
    {t : CircleX} (ht : t ≠ 0) :
    ∀ᵐ s : CircleX, ContinuousAt (Function.uncurry (uPos ℓ α)) (s,t) := by
  have he : ∀ᵐ s : CircleX, s ≠ 0 := by
    rw [ae_iff]
    simpa only [not_not,Set.ofPred_eq_eq_singleton] using volume_singleton_zero (0:CircleX)
  filter_upwards [he,ae_delta_ne α,ae_delta_ne (repr t/ℓ)] with s hs hαs hts
  have hst : repr t ≠ ℓ*delta (repr s) := by
    intro h
    apply hts
    apply (eq_div_iff hℓ.ne').mpr
    linarith only [h]
  have hcmap : ContinuousAt (fun z : CircleX × CircleX => (repr z.1,repr z.2)) (s,t) :=
    ((continuousAt_repr hs).comp (f:=Prod.fst) (x:=(s,t)) continuousAt_fst).prodMk
      ((continuousAt_repr ht).comp (f:=Prod.snd) (x:=(s,t)) continuousAt_snd)
  exact (continuousAt_weight hℓ hα hαs.symm (repr_pos ht) hst).comp (f:=fun z : CircleX × CircleX => (repr z.1,repr z.2)) (x:=(s,t)) hcmap

lemma ae_continuousAt_uNeg {ℓ α : ℝ} (hℓ : 0 < ℓ) (hα : 0 < α)
    {t : CircleX} (ht : t ≠ 0) :
    ∀ᵐ s : CircleX, ContinuousAt (Function.uncurry (uNeg ℓ α)) (s,t) := by
  have h := (measurePreserving_sub_right volume t).quasiMeasurePreserving.ae (ae_continuousAt_uPos hℓ hα ht)
  filter_upwards [h] with s hs
  exact hs.comp (f:=fun z : CircleX × CircleX => (z.1-z.2,z.2)) (x:=(s,t))
    ((continuousAt_fst.sub continuousAt_snd).prodMk continuousAt_snd)
end

section
open ContinuousCircleWeight ContinuousCircleWeight.Sampling Filter
open scoped Topology
variable {ι : Type uι} {κ : Type uκ} [Fintype ι] [Fintype κ] [Nonempty κ]
lemma ae_continuousAt_orientedWeight (positive : Bool) {ℓ α : ℝ} (hℓ : 0 < ℓ) (hα : 0 < α)
    {t : CircleX} (ht : t ≠ 0) :
    ∀ᵐ s : CircleX, ContinuousAt (Function.uncurry (orientedWeight positive ℓ α)) (s,t) := by
  cases positive
  · exact ae_continuousAt_uNeg hℓ hα ht
  · exact ae_continuousAt_uPos hℓ hα ht

omit [Nonempty κ] in
lemma ae_continuousAt_idealAverage (positive : Bool) {ℓ α : ℝ} (hℓ : 0 < ℓ) (hα : 0 < α)
    (c : κ → ℝ) (γ : ι → ℝ) (hγ : ∀ n i, ((c n*γ i:ℝ):CircleX) ≠ 0) :
    ∀ᵐ s : ι → CircleX ∂Measure.pi (fun _ => volume),
      ContinuousAt (fun z : (ι → CircleX) × (ι → ℝ) => idealAverage positive ℓ α c z.1 z.2) (s,γ) := by
  have hh : ∀ᵐ s : ι → CircleX ∂Measure.pi (fun _ => volume), ∀ n i,
      ContinuousAt (Function.uncurry (orientedWeight positive ℓ α)) (s i,((c n*γ i:ℝ):CircleX)) := by
    apply ae_all_iff.mpr
    intro n
    apply ae_all_iff.mpr
    intro i
    exact (measurePreserving_eval (fun _ : ι => (volume : Measure CircleX)) i).quasiMeasurePreserving.ae
      (ae_continuousAt_orientedWeight positive hℓ hα (hγ n i))
  filter_upwards [hh] with s hs
  unfold idealAverage
  apply ContinuousAt.const_mul
  apply tendsto_finsetSum
  intro n _
  apply tendsto_finsetProd
  intro i _
  have hm : Continuous (fun z : (ι → CircleX) × (ι → ℝ) => (z.1 i,((c n*z.2 i:ℝ):CircleX))) := by fun_prop
  exact (hs n i).comp (f:=fun z : (ι → CircleX) × (ι → ℝ) => (z.1 i,((c n*z.2 i:ℝ):CircleX))) (x:=(s,γ)) hm.continuousAt

lemma squared_ideal_test_bound (positive : Bool) {ℓ α : ℝ} (hℓ : 0 < ℓ) (hα : 0 < α)
    (c : κ → ℝ) (s : ι → CircleX) (γ : ι → ℝ) :
    ‖Complex.ofReal ((idealAverage positive ℓ α c s γ-1)^2)‖ ≤ ((1/(ℓ*α))^(Fintype.card ι)+1)^2 := by
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _),← sq_abs (idealAverage positive ℓ α c s γ-1)]
  apply (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr
  rw [abs_le]
  have h := idealAverage_bounds positive hℓ hα c s γ
  constructor <;> linarith [pow_nonneg (by positivity : 0 ≤ 1/(ℓ*α)) (Fintype.card ι)]

lemma ideal_sampling_tendsto {P : Type uP} [MetricSpace P] [CompactSpace P]
    [MeasurableSpace P] [BorelSpace P] {r : ℕ}
    (q : ℕ → ℕ → ℤ) (hq : ∀ n i, i < r → 0 < q n i)
    (hsep : ∀ i, i+1 < r → Tendsto (fun n => (q n (i+1):ℝ)/q n i) atTop atTop)
    {bs : ℕ → P} {b : P} (hb : Tendsto bs atTop (𝓝 b))
    (β : P → Fin r → ℝ) (hβ : Continuous β)
    (positive : Bool) {ℓ α : ℝ} (hℓ : 0 < ℓ) (hα : 0 < α)
    (c : κ → ℝ) (hphase : ∀ n i, ((c n*β b i:ℝ):CircleX) ≠ 0) :
    Tendsto (fun n => ∫ x : CircleX,
      (idealAverage positive ℓ α c (characterCurve (fun i : Fin r => q n i) x) (β (bs n))-1)^2)
      atTop (𝓝 (idealEnergy positive ℓ α c (β b))) := by
  have hvol : (AddCircle.haarAddCircle : Measure CircleX) = volume := by
    simpa using (AddCircle.volume_eq_smul_haarAddCircle (T:=(1:ℝ))).symm
  have htorus : (torusHaar (ι:=Fin r) : Measure (Fin r → CircleX)) = Measure.pi (fun _ => volume) := by
    change Measure.pi (fun _ => AddCircle.haarAddCircle) = _
    simp_rw [hvol]
  let Φ := fun z : (Fin r → CircleX) × P => Complex.ofReal ((idealAverage positive ℓ α c z.1 (β z.2)-1)^2)
  have hΦ : Measurable Φ := by
    exact Complex.measurable_ofReal.comp
      (((measurable_idealAverage positive ℓ α c).comp
        (measurable_fst.prodMk (hβ.measurable.comp measurable_snd))).sub measurable_const |>.pow_const 2)
  have hc : ∀ᵐ z ∂(withParameter (torusHaar (ι:=Fin r)) b : Measure _), ContinuousAt Φ z := by
    rw [withParameter,ProbabilityMeasure.toMeasure_map]
    apply ae_map_iff (measurable_id.prodMk measurable_const).aemeasurable (measurableSet_of_continuousAt Φ) |>.mpr
    rw [htorus]
    change ∀ᵐ s ∂Measure.pi (fun _ : Fin r => (volume : Measure CircleX)), ContinuousAt Φ (s,b)
    filter_upwards [ae_continuousAt_idealAverage positive hℓ hα c (β b) hphase] with s hs
    have hm := hs.comp (f:=fun z : (Fin r → CircleX) × P => (z.1,β z.2)) (x:=(s,b))
      (continuous_fst.prodMk (hβ.comp continuous_snd)).continuousAt
    exact Complex.continuous_ofReal.continuousAt.comp ((hm.sub continuousAt_const).pow 2)
  have ht := circle_approximation_with_parameters q hq hsep hb Φ hΦ hc
    (((1/(ℓ*α))^r+1)^2) (fun z => by simpa only [Φ,Fintype.card_fin] using squared_ideal_test_bound positive hℓ hα c z.1 (β z.2))
  have ht' := Complex.continuous_re.continuousAt.tendsto.comp ht
  simpa only [Function.comp_def,Φ,integral_complex_ofReal,Complex.ofReal_re,idealEnergy,htorus,hvol] using ht'
end

open Filter
open scoped Topology
section

open ContinuousCircleWeight.Sampling
open scoped Topology
lemma sampling_finite_accuracy {r : ℕ} {κ : Type uκ} [Fintype κ] [Nonempty κ]
    (positive : Bool) {ℓ α : ℝ} (hℓ : 0 < ℓ) (hα : 0 < α)
    (c : κ → ℝ) (γ : PhaseCube r)
    (hphase : ∀ n i, ((c n*(γ i:ℝ):ℝ):CircleX) ≠ 0)
    {η : ℝ} (hη : idealEnergy positive ℓ α c (fun i => (γ i:ℝ)) < η) :
    ∃ M : ℕ, ∃ δ : ℝ, 0 < δ ∧ ∀ (q : ℕ → ℤ) (β : PhaseCube r),
      (∀ i, i < r → 0 < q i) →
      (∀ i, i+1 < r → (M:ℝ) ≤ (q (i+1):ℝ)/q i) →
      dist β γ < δ →
      (∫ x : CircleX, (idealAverage positive ℓ α c (characterCurve (fun i : Fin r => q i) x)
        (fun i => (β i:ℝ))-1)^2) < η := by
  apply finite_accuracy_of_sequential γ _ hη
  intro q hq hsep bs hb
  exact ideal_sampling_tendsto q hq hsep hb (fun β : PhaseCube r => fun i => (β i:ℝ))
    (by fun_prop) positive hℓ hα c hphase
end

open Set Filter
open scoped Topology

open ContinuousCircleWeight.Sampling
open scoped Topology
lemma realize_finite_sampling {m : ℕ} {τ : Type uτ} [Fintype τ]
    {κ : τ → Type uκ} [∀ t, Fintype (κ t)] [∀ t, Nonempty (κ t)]
    (positive : τ → Bool) {ℓ α : ℝ} (hℓ : 0 < ℓ) (hα : 0 < α)
    (c : ∀ t, κ t → ℝ) (γ : PhaseCube m)
    (hγ : ∀ i, (γ i:ℝ)∈Set.Ioo 0 1)
    (hphase : ∀ t n i, ((c t n*(γ i:ℝ):ℝ):CircleX) ≠ 0)
    {η : ℝ} (hE : ∀ t, idealEnergy (positive t) ℓ α (c t) (fun i => (γ i:ℝ)) < η)
    {U : Set (PhaseCube m)} (hU : U∈𝓝 γ)
    {a b : ℝ} (hab : a < b) {p : ℕ} (hp : 0 < p) (M : ℝ) :
    ∃ q : ℕ → ℕ, q 0=p ∧ (∀ i ≤ m, 0 < q i) ∧
      (∀ i < m, q i ∣ q (i+1) ∧ M < (q (i+1):ℝ)/q i) ∧
      ∃ d e : ℝ, d < e ∧ Set.Icc d e ⊆ Set.Ioo a b ∧
        ∀ θ∈Set.Icc d e, fractionalCube m q θ∈U ∧
          ∀ t, (∫ x : CircleX, (idealAverage (positive t) ℓ α (c t)
            (characterCurve (fun i : Fin m => (q (i+1):ℤ)) x)
            (fun i => Int.fract ((q (i+1):ℝ)*θ))-1)^2) < η := by
  classical
  choose Mt δ hδ hacc using fun t => sampling_finite_accuracy (positive t) hℓ hα (c t) γ (hphase t) (hE t)
  let K := Finset.univ.sup Mt
  have hK (t : τ) : Mt t ≤ K := Finset.le_sup (f:=Mt) (Finset.mem_univ t)
  have hboth : (U∩{β : PhaseCube m | ∀ t, dist β γ < δ t})∈𝓝 γ := by
    apply Filter.inter_mem hU
    exact Filter.eventually_all.mpr (fun t => Metric.ball_mem_nhds γ (hδ t))
  obtain ⟨q,hq0,hqp,hqM,d,e,hde,hsub,hβ⟩ := realize_phase_neighborhood γ hγ hboth hab hp (max M (K:ℝ))
  refine ⟨q,hq0,hqp,?_,d,e,hde,hsub,?_⟩
  · intro i hi
    exact ⟨(hqM i hi).1,lt_of_le_of_lt (le_max_left _ _) (hqM i hi).2⟩
  · intro θ hθ
    refine ⟨(hβ θ hθ).1,?_⟩
    intro t
    apply hacc t (fun i => (q (i+1):ℤ)) (fractionalCube m q θ)
    · intro i hi
      exact_mod_cast hqp (i+1) (by omega)
    · intro i hi
      push_cast
      calc
        (Mt t:ℝ) ≤ K := Nat.cast_le.mpr (hK t)
        _ ≤ max M (K:ℝ) := le_max_right _ _
        _ ≤ (q (i+1+1):ℝ)/q (i+1) := (hqM (i+1) (by omega)).2.le
    · exact (hβ θ hθ).2 t


end CircleSampling

end

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_ReturnSamples
attribute [-instance] _root_.OAI.CircleCoupling.labelMeasurableSpace
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
lemma phase_success_eventually {m : ℕ} (γ : PhaseCube m) {k : ℤ} {i : Fin m} {b : ℝ}
    (hne : ((k*(γ i:ℝ):ℝ):CircleX) ≠ 0) (hgood : (γ i:ℝ) ∉ phaseFailure b k) :
    ∀ᶠ β : PhaseCube m in 𝓝 γ, (β i:ℝ) ∉ phaseFailure b k := by
  have heval : ContinuousAt (fun β : PhaseCube m => (β i:ℝ)) γ :=
    continuous_subtype_val.continuousAt.comp (continuous_apply i).continuousAt
  have hc : ContinuousAt (fun β : PhaseCube m => repr ((k*(β i:ℝ):ℝ):CircleX)) γ :=
    (continuousAt_repr hne).comp (f:=fun β : PhaseCube m => ((k*(β i:ℝ):ℝ):CircleX))
      ((AddCircle.continuous_mk' 1).continuousAt.comp (continuousAt_const.mul heval))
  have hh : b < 1-repr ((k*(γ i:ℝ):ℝ):CircleX) ∧ 1-repr ((k*(γ i:ℝ):ℝ):CircleX) < 1-b :=
    by simpa [phaseFailure] using hgood
  have hc' : ContinuousAt (fun β : PhaseCube m => 1-repr ((k*(β i:ℝ):ℝ):CircleX)) γ := continuousAt_const.sub hc
  filter_upwards [hc'.eventually (Ioo_mem_nhds hh.1 hh.2)] with β hβ
  simpa [phaseFailure] using hβ

lemma phase_cover_eventually {m : ℕ} (γ : PhaseCube m) (S : Finset ℤ) (b : ℝ)
    (hphase : ∀ k∈S, ∀ i, ((k*(γ i:ℝ):ℝ):CircleX) ≠ 0) :
    ∀ᶠ β : PhaseCube m in 𝓝 γ, ∀ k∈S,
      (Finset.univ.filter fun i => (γ i:ℝ) ∉ phaseFailure b k).card ≤
      (Finset.univ.filter fun i => (β i:ℝ) ∉ phaseFailure b k).card := by
  classical
  have hs : ∀ k∈S, ∀ᶠ β : PhaseCube m in 𝓝 γ,
      ∀ i, (γ i:ℝ) ∉ phaseFailure b k → (β i:ℝ) ∉ phaseFailure b k := by
    intro k hk
    apply Filter.eventually_all.mpr
    intro i
    by_cases hi : (γ i:ℝ) ∉ phaseFailure b k
    · exact (phase_success_eventually γ (hphase k hk i) hi).mono (fun β hb _ => hb)
    · exact Filter.Eventually.of_forall (fun _ hi' => (hi hi').elim)
  filter_upwards [(Filter.eventually_all_finite S.finite_toSet).mpr hs] with β hβ k hk
  apply Finset.card_le_card
  intro i hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hβ k hk i (Finset.mem_filter.mp hi).2⟩

end

open Set Topology

open scoped BigOperators

open Set Filter
open scoped Topology


end CircleSampling

end

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_SamplingStage
attribute [-instance] _root_.OAI.CircleCoupling.labelMeasurableSpace
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

namespace CircleSampling
open Set Filter MeasureTheory ContinuousCircleWeight.Sampling
open scoped Topology

lemma exists_sampling_stage {τ : Type uτ} [Fintype τ]
    (O : τ → Set CircleX) (hO : ∀ t, IsOpen (O t)) (hne : ∀ t, (O t).Nonempty)
    {K : ℕ} (hK : 0 < K) {η : ℝ} (hη : 0 < η)
    (P : ℕ → Prop) (hP : ∀ᶠ m : ℕ in atTop, P m)
    {a b : ℝ} (hab : a < b) {p : ℕ} (hp : 0 < p) (M : ℕ → ℝ) :
    ∃ m : ℕ, P m ∧ 3 ≤ m ∧ ∃ S : τ → Finset ℤ,
      (∀ t, (S t).Nonempty) ∧
      (∀ t n, n∈S t → (m:ℝ)^((7:ℝ)/10*m)/2 ≤ (n:ℝ) ∧ (n:ℝ) ≤ (m:ℝ)^((7:ℝ)/10*m)) ∧
      ∃ q : ℕ → ℕ, q 0=p ∧ (∀ i ≤ m, 0 < q i) ∧
        (∀ i < m, q i ∣ q (i+1) ∧ M m < (q (i+1):ℝ)/q i) ∧
        ∃ d e : ℝ, d < e ∧ Icc d e ⊆ Ioo a b ∧ ∀ θ∈Icc d e,
          (∀ i : Fin m, Int.fract ((q (i+1):ℝ)*θ) ∈ Ioo (1/((m:ℝ)*K)) (2/((m:ℝ)*K))) ∧
          (∀ k : ℤ, ((m:ℝ)*K)/4 ≤ |(k:ℝ)| → |(k:ℝ)| ≤ (m:ℝ)^((4:ℝ)/5*m) →
            (m:ℝ)/20 ≤ ((Finset.univ.filter fun i : Fin m =>
              Int.fract ((q (i+1):ℝ)*θ) ∉ phaseFailure ((m:ℝ)^(-(19:ℝ)/20)) k).card:ℝ)) ∧
          (∀ t n, n∈S t → n•(θ:CircleX)∈O t) ∧
          ∀ t (positive : Bool),
            (∫ x : CircleX, (idealAverage positive (scaleEll m) (scaleAlpha m)
              (fun n : S t => (n.val:ℝ)) (characterCurve (fun i : Fin m => (q (i+1):ℤ)) x)
              (fun i => Int.fract ((q (i+1):ℝ)*θ))-1)^2) < η := by
  classical
  obtain ⟨θ0,hθirr,hθa,hθb⟩ := exists_irrational_btwn hab
  have hs : ∀ᶠ m : ℕ in atTop, ∀ t, ∃ S : Finset ℤ,
      (m:ℝ)^((69:ℝ)/100*m) ≤ (S.card:ℝ) ∧
      (∀ n∈S, (m:ℝ)^((7:ℝ)/10*m)/2 ≤ (n:ℝ) ∧ (n:ℝ) ≤ (m:ℝ)^((7:ℝ)/10*m) ∧ n•(θ0:CircleX)∈O t) ∧
      (∀ n∈S, ∀ n'∈S, n≠n' → ∀ v v' : ℤ, |v| ≤ m^300 → |v'| ≤ m^300 →
        (v≠0 ∨ v'≠0) → (m*K*m^1000:ℤ) < |v*n+v'*n'|) :=
    Filter.eventually_all.mpr (fun t => eventually_separated_returns hθirr (hO t) (hne t) K)
  obtain ⟨m,hmP,hm3,hmnum,hbudget,hps,hmS⟩ :=
    (hP.and ((eventually_ge_atTop (3:ℕ)).and ((eventually_IdealNumerics K).and
      ((eventually_trial_budget (Fintype.card (τ×Bool)) hη).and (eventually_phase_failure_small.and hs))))).exists
  have hm0 : 0 < m := by omega
  have hmR : 0 < (m:ℝ) := Nat.cast_pos.mpr hm0
  choose S hSc hSbounds hSsep using hmS
  have hSnon (t : τ) : (S t).Nonempty := by
    apply Finset.card_pos.mp
    have hh : (0:ℝ) < ((S t).card:ℝ) := (Real.rpow_pos_of_pos hmR _).trans_le (hSc t)
    exact_mod_cast hh
  let (t : τ) : Nonempty (S t) := (hSnon t).to_subtype
  have hcpos (t : τ) (n : S t) : (0:ℝ) < (n.val:ℝ) :=
    (div_pos (Real.rpow_pos_of_pos hmR _) (by norm_num)).trans_le (hSbounds t n n.property).1
  have hN2 : 2 < (m:ℝ)*K := by
    have hm3R : (3:ℝ) ≤ m := Nat.cast_le.mpr hm3
    have hKR : (1:ℝ) ≤ K := by exact_mod_cast (show (1:ℕ) ≤ K by omega)
    nlinarith
  have hN : 0 < (m:ℝ)*K := by linarith
  let R := (m:ℝ)^((4:ℝ)/5*m)
  have hR1 : 1 ≤ R := Real.one_le_rpow (by exact_mod_cast (show 1 ≤ m by omega)) (by positivity)
  obtain ⟨g,hg,hgphase,hgcover,hgE⟩ := exists_ideal_trial (κ:=fun t : τ×Bool => S t.1)
    hK hmnum Prod.snd (fun t n => (n.val:ℝ))
    (fun t => by simpa using hSc t.1)
    (fun t n => (hSbounds t.1 n n.property).1)
    (by
      intro t n n' hnn v w hv hw hvw
      have hne' : n.val≠n'.val := fun he => hnn (Subtype.ext he)
      have hv' : |v| ≤ (m:ℤ)^300 := by simpa only [Nat.cast_pow] using hv
      have hw' : |w| ≤ (m:ℤ)^300 := by simpa only [Nat.cast_pow] using hw
      have hh := (hSsep t.1 n n.property n' n'.property hne' v w hv' hw' hvw).le
      simpa only [Int.cast_add, Int.cast_mul, Int.cast_natCast, Int.cast_pow, Int.cast_abs] using
        (Int.cast_le (R := ℝ)).mpr hh)
    hps (phaseRange ((m:ℝ)*K) R) (phaseRange_bound hR1)
    (fun _ hk => phaseRange_lower hk) hη hbudget
  have hg01 (i : Fin m) : g i∈Ioo 0 1 := by
    refine ⟨lt_trans (one_div_pos.mpr hN) (hg i).1,lt_trans (hg i).2 ?_⟩
    exact (div_lt_one hN).mpr hN2
  let γ : PhaseCube m := fun i => ⟨g i,(hg01 i).1.le,(hg01 i).2.le⟩
  have hγ : ∀ i, (γ i:ℝ)∈Ioo 0 1 := hg01
  have hcover : ∀ᶠ β : PhaseCube m in 𝓝 γ, ∀ k∈phaseRange ((m:ℝ)*K) R,
      (m:ℝ)/20 ≤ ((Finset.univ.filter fun i => (β i:ℝ)∉phaseFailure ((m:ℝ)^(-(19:ℝ)/20)) k).card:ℝ) := by
    have hneK (k : ℤ) (hk : k∈phaseRange ((m:ℝ)*K) R) : k≠0 := by
      intro he
      have hh := phaseRange_lower hk
      rw [he] at hh
      norm_num at hh
      linarith
    filter_upwards [phase_cover_eventually γ (phaseRange ((m:ℝ)*K) R) ((m:ℝ)^(-(19:ℝ)/20))
      (fun k hk i => hgphase k (hneK k hk) i)] with β hβ k hk
    exact (hgcover k hk).trans (Nat.cast_le.mpr (hβ k hk))
  have hinterval : ∀ᶠ β : PhaseCube m in 𝓝 γ, ∀ i, (β i:ℝ)∈Ioo (1/((m:ℝ)*K)) (2/((m:ℝ)*K)) :=
    cube_interval_eventually γ hg
  have horbit : ∀ᶠ θ : ℝ in 𝓝 θ0, ∀ t n, n∈S t → n•(θ:CircleX)∈O t := by
    apply Filter.eventually_all.mpr
    intro t
    apply (Filter.eventually_all_finite (S t).finite_toSet).mpr
    intro n hn
    exact (show ContinuousAt (fun θ : ℝ => n•(θ:CircleX)) θ0 by fun_prop).eventually
      ((hO t).mem_nhds (hSbounds t n hn).2.2)
  obtain ⟨a',b',hθint,hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp (Filter.inter_mem (Ioo_mem_nhds hθa hθb) horbit)
  obtain ⟨q,hq0,hqp,hqM,d,e,hde,hdeSub,hreal⟩ := realize_finite_sampling (κ:=fun t : τ×Bool => S t.1)
    Prod.snd (Real.rpow_pos_of_pos hmR _) (scaleAlpha_pos hm0) (fun t n => (n.val:ℝ)) γ hγ
    (fun t n i => hgphase n (by exact_mod_cast (hcpos t.1 n).ne') i) hgE
    (hinterval.and hcover) (lt_trans hθint.1 hθint.2) hp (M m)
  refine ⟨m,hmP,hm3,S,hSnon,(fun t n hn => ⟨(hSbounds t n hn).1,(hSbounds t n hn).2.1⟩),
    q,hq0,hqp,hqM,d,e,hde,?_,?_⟩
  · exact fun θ hθ => (hsub (hdeSub hθ)).1
  · intro θ hθ
    refine ⟨(hreal θ hθ).1.1,?_,(hsub (hdeSub hθ)).2,?_⟩
    · intro k hk hkR
      exact (hreal θ hθ).1.2 k (mem_phaseRange hk hkR)
    · intro t positive
      exact (hreal θ hθ).2 (t,positive)
end CircleSampling

open scoped BigOperators
namespace ContinuousCircleWeight

theorem continuous_coeff_shiftedPolynomial (K n : ℕ) :
    Continuous (fun a : Fin (2 * K + 1) → ℂ => (shiftedPolynomial K a).coeff n) := by
  classical
  simp only [shiftedPolynomial, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
  apply continuous_finsetSum
  intro i _
  split_ifs <;> fun_prop

theorem continuous_lowProduct (K : ℕ) : Continuous (lowProduct K) := by
  apply continuous_pi
  intro n
  simp only [lowProduct, Polynomial.coeff_mul]
  apply continuous_finsetSum
  intro x _
  exact ((continuous_coeff_shiftedPolynomial K x.1).comp continuous_fst).mul
    ((continuous_coeff_shiftedPolynomial K x.2).comp continuous_snd)

theorem lowProduct_ne_zero (K : ℕ) (a : CoefficientPair K)
    (hA : a.1 (centerIndex K) ≠ 0) (hB : a.2 (centerIndex K) ≠ 0) :
    lowProduct K a ≠ 0 := by
  have hA' : (shiftedPolynomial K a.1).coeff K ≠ 0 := by
    change (shiftedPolynomial K a.1).coeff (centerIndex K) ≠ 0
    simpa only [coeff_shiftedPolynomial] using hA
  have hB' : (shiftedPolynomial K a.2).coeff K ≠ 0 := by
    change (shiftedPolynomial K a.2).coeff (centerIndex K) ≠ 0
    simpa only [coeff_shiftedPolynomial] using hB
  obtain ⟨n, hn, hcoeff⟩ := exists_nonzero_low_product_coefficient K _ _ hA' hB'
  intro hzero
  have := congr_fun hzero (⟨n, by omega⟩ : Fin (2 * K + 1))
  exact hcoeff this

theorem finite_coefficient_bound (K : ℕ) (δ D : ℝ) (hδ : 0 < δ) (hD : 0 ≤ D) :
    ∃ ε > 0, ∀ a : CoefficientPair K,
      (∀ i, ‖a.1 i‖ ≤ D) → (∀ i, ‖a.2 i‖ ≤ D) →
      δ ≤ ‖a.1 (centerIndex K)‖ → δ ≤ ‖a.2 (centerIndex K)‖ →
      ∃ n : Fin (2 * K + 1), ε ≤ ‖lowProduct K a n‖ := by
  let S : Set (CoefficientPair K) :=
    Metric.closedBall 0 D ∩
      {a | δ ≤ ‖a.1 (centerIndex K)‖} ∩ {a | δ ≤ ‖a.2 (centerIndex K)‖}
  have hSc : IsCompact S := by
    apply IsCompact.inter_right
    · apply IsCompact.inter_right (isCompact_closedBall _ _)
      exact isClosed_le continuous_const (by fun_prop)
    · exact isClosed_le continuous_const (by fun_prop)
  have hpositive : ∀ a ∈ S, 0 < ‖lowProduct K a‖ := by
    intro a ha
    apply norm_pos_iff.mpr
    apply lowProduct_ne_zero
    · intro hz
      have : δ ≤ ‖a.1 (centerIndex K)‖ := ha.1.2
      simp only [hz, norm_zero] at this
      linarith
    · intro hz
      have : δ ≤ ‖a.2 (centerIndex K)‖ := ha.2
      simp only [hz, norm_zero] at this
      linarith
  obtain ⟨ε, hε, hlower⟩ := hSc.exists_forall_le'
    (continuous_lowProduct K).norm.continuousOn hpositive
  refine ⟨ε, hε, ?_⟩
  intro a ha hb hca hcb
  have haS : a ∈ S := by
    refine ⟨⟨?_, hca⟩, hcb⟩
    rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, max_le_iff]
    exact ⟨(pi_norm_le_iff_of_nonneg hD).mpr ha, (pi_norm_le_iff_of_nonneg hD).mpr hb⟩
  obtain ⟨n, _, hn⟩ := Finset.exists_max_image Finset.univ (fun n => ‖lowProduct K a n‖)
    Finset.univ_nonempty
  refine ⟨n, (hlower a haS).trans ?_⟩
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
  exact fun i => hn i (Finset.mem_univ i)

end ContinuousCircleWeight

namespace CircleSampling
open Filter Set
open scoped Topology

lemma kappa_le (j : ℕ) : kappa j ≤ (1:ℝ)/100 := by
  unfold kappa
  apply one_div_le_one_div_of_le (by norm_num)
  nlinarith [Nat.cast_nonneg (α:=ℝ) j]

end CircleSampling

end

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_NestedAngles
attribute [-instance] _root_.OAI.CircleCoupling.labelMeasurableSpace
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

lemma enumeratedRat_encode (r : ℚ) : enumeratedRat (Encodable.encode r) = (r:ℝ) := by
  simp [enumeratedRat,Encodable.encodek]

lemma irrational_in_nested_intervals (a b : ℕ → ℝ)
    (hab : ∀ n, a n < b n) (hnest : ∀ n, Icc (a (n+1)) (b (n+1)) ⊆ Ioo (a n) (b n))
    (havoid : ∀ n, enumeratedRat n ∉ Icc (a (n+1)) (b (n+1))) :
    ∃ θ : ℝ, Irrational θ ∧ (∀ n, θ∈Icc (a n) (b n)) ∧ θ∈Ioo (a 0) (b 0) := by
  obtain ⟨θ,hθ⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (fun n => Icc (a n) (b n)) (fun n => (hnest n).trans Ioo_subset_Icc_self)
    (fun n => nonempty_Icc.mpr (hab n).le) isCompact_Icc (fun _ => isClosed_Icc)
  have hm : ∀ n, θ∈Icc (a n) (b n) := Set.mem_iInter.mp hθ
  refine ⟨θ,?_,hm,hnest 0 (hm 1)⟩
  rintro ⟨r,hr⟩
  apply havoid (Encodable.encode r)
  rw [enumeratedRat_encode,hr]
  exact hm _

end

open Set
section
lemma positiveArc_open (h : CircleX) (r : ℝ) : IsOpen (positiveArc h r) := by
  exact (QuotientAddGroup.isOpenMap_coe (Ioo 0 r) isOpen_Ioo).preimage (continuous_id.sub continuous_const)
lemma positiveArc_nonempty (h : CircleX) {r : ℝ} (hr : 0<r) : (positiveArc h r).Nonempty := by
  refine ⟨((r/2:ℝ):CircleX)+h,?_⟩
  change (((r/2:ℝ):CircleX)+h)-h ∈ ((↑) : ℝ → CircleX) '' Ioo 0 r
  rw [add_sub_cancel_right]
  exact ⟨r/2,⟨by linarith,by linarith⟩,rfl⟩

open Set Filter MeasureTheory ContinuousCircleWeight ContinuousCircleWeight.Sampling
open scoped Topology

lemma exists_scale_step (j : ℕ) (s : ScaleState) (hs : s.Valid) : Nonempty (ScaleStep j s) := by
  have hδ : 0 < 1/((j:ℝ)+1) := by positivity
  obtain ⟨ε,hε,hcoeff⟩ := finite_coefficient_bound s.K _ (Real.exp (((s.K:ℝ)+1)*s.E)) hδ (Real.exp_pos _).le
  obtain ⟨L,hL,hLp,hLb⟩ := exists_exponential_budget j s.K hε s.Lprev
  obtain ⟨G,hG,hGb⟩ := exists_bridge_budget j L
  have hr : 0 < gridTolerance j s := by
    unfold gridTolerance
    have hq : 0 < (s.q s.d:ℝ) := Nat.cast_pos.mpr (hs.qpos s.d le_rfl)
    positivity
  obtain ⟨m,hm,_,S,hSn,hSb,q,hq0,hqp,hqr,a,b,hab,hsub,hstage⟩ := exists_sampling_stage
    (fun t : Fin (s.q s.d) => positiveArc (gridPoint s t) (gridTolerance j s))
    (fun _ => positiveArc_open _ _) (fun _ => positiveArc_nonempty _ hr)
    hs.Kpos (show 0 < 1/((j:ℝ)+1)^2 by positivity)
    (StageNumerics j s.K s.G L G) (eventually_StageNumerics j s.K s.G L G)
    hs.ab (hs.qpos s.d le_rfl) (fun m => 100*(m:ℝ))
  obtain ⟨a',b',hab',hsub',havoid⟩ := closed_interval_avoiding (enumeratedRat j) hab
  have hinc : Icc a' b' ⊆ Icc a b := hsub'.trans Ioo_subset_Icc_self
  exact ⟨{
    ε := ε, L := L, Gnext := G, εpos := hε, coefficients := hcoeff,
    Lge := hL, Lprev := hLp, exponential := hLb, Gge := hG, bridge := hGb,
    m := m, numeric := hm, samples := S, samples_nonempty := hSn, samples_bounds := hSb,
    q := q, qzero := hq0, qpos := hqp, qratio := hqr,
    a := a', b := b', ab := hab', interval := hinc.trans hsub, avoid := havoid,
    phases := fun θ hθ => (hstage θ (hinc hθ)).1,
    cover := fun θ hθ => (hstage θ (hinc hθ)).2.1,
    orbits := fun θ hθ => (hstage θ (hinc hθ)).2.2.1,
    energies := fun θ hθ => (hstage θ (hinc hθ)).2.2.2 }⟩

def initialScaleState : ScaleState where
  K := 100
  d := 0
  G := 1
  E := 0
  Lprev := 1
  a := 0
  b := 1
  q := fun _ => 1
lemma initialScaleState_valid : initialScaleState.Valid := by
  constructor <;> simp [initialScaleState]

def chosenScaleStep (j : ℕ) (s : {s : ScaleState // s.Valid}) : ScaleStep j s.1 :=
  Classical.choice (exists_scale_step j s.1 s.2)
def scaleState : ℕ → {s : ScaleState // s.Valid} :=
  Nat.rec ⟨initialScaleState,initialScaleState_valid⟩
    (fun j s => ⟨(chosenScaleStep j s).next,(chosenScaleStep j s).next_valid s.2⟩)
def scaleStep (j : ℕ) : ScaleStep j (scaleState j).1 := chosenScaleStep j (scaleState j)

lemma exists_global_angle : ∃ θ : ℝ, 0< θ ∧ θ<1 ∧ Irrational θ ∧
    ∀ j,θ∈Icc (scaleStep j).a (scaleStep j).b := by
  obtain ⟨θ,hθ,hmem,h01⟩ := irrational_in_nested_intervals
    (fun j => (scaleState j).1.a) (fun j => (scaleState j).1.b)
    (fun j => (scaleState j).2.ab)
    (fun j => (scaleStep j).interval) (fun j => (scaleStep j).avoid)
  refine ⟨θ,h01.1,h01.2,hθ,?_⟩
  intro j
  exact hmem (j+1)
end

open Set


end CircleSampling

end

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_Parameters
attribute [-instance] _root_.OAI.CircleCoupling.labelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CircleSampling

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

section
open Set Filter MeasureTheory ContinuousCircleWeight.Sampling
open scoped Topology

def blockLength (j : ℕ) : ℕ := (scaleStep j).m
def blockEnd (j : ℕ) : ℕ := (scaleState j).1.d
def polynomialWindow (j : ℕ) : ℕ := (scaleState j).1.K
def dropSize (j : ℕ) : ℝ := (scaleStep j).C
def crossingBudget (j : ℕ) : ℝ := (scaleStep j).L
def bridgeSize (j : ℕ) : ℝ := (scaleState j).1.G
def frequency (i : ℕ) : ℕ := (scaleState i).1.q i

def blocks : BlockPartition where
  m := blockLength
  d := blockEnd
  zero := rfl
  step := fun _ => rfl
  positive := fun j => (scaleStep j).mpos

lemma blockEnd_strictMono : StrictMono blockEnd := blocks.strictMono
lemma blockEnd_ge (j : ℕ) : j≤blockEnd j := blocks.ge j
lemma state_prefix (j i : ℕ) (hi : i≤blockEnd j) : (scaleState (j+1)).1.q i=(scaleState j).1.q i :=
  extendPrefix_old _ _ _ hi
lemma frequency_eq_state {j i : ℕ} (hi : i≤blockEnd j) : frequency i=(scaleState j).1.q i :=
  diagonal_prefix_eq blockEnd (fun j => (scaleState j).1.q)
    blockEnd_strictMono.monotone blockEnd_ge state_prefix hi

lemma frequency_block (j : ℕ) {k : ℕ} (hk : k≤blockLength j) :
    frequency (blockEnd j+k)=(scaleStep j).q k := by
  rw [frequency_eq_state (j:=j+1) (show blockEnd j+k≤blockEnd (j+1) by
    change blockEnd j+k≤blockEnd j+blockLength j; omega)]
  exact extendPrefix_block _ _ _ (scaleStep j).qzero k
lemma frequency_zero : frequency 0=1 := rfl
lemma frequency_pos (i : ℕ) : 0 < frequency i := (scaleState i).2.qpos i (blockEnd_ge i)
lemma frequency_dvd (i : ℕ) : frequency i∣frequency (i+1) := by
  rw [frequency_eq_state (j:=i+1) (by have := blockEnd_ge (i+1); omega),frequency_eq_state (j:=i+1) (blockEnd_ge _)]
  exact (scaleState (i+1)).2.qdvd i (by change i<blockEnd (i+1); have := blockEnd_ge (i+1); omega)
lemma frequency_strictMono : StrictMono frequency := by
  apply strictMono_nat_of_lt_succ
  intro i
  rw [frequency_eq_state (j:=i+1) (by have := blockEnd_ge (i+1); omega),frequency_eq_state (j:=i+1) (blockEnd_ge _)]
  exact (scaleState (i+1)).2.qlt i (by change i<blockEnd (i+1); have := blockEnd_ge (i+1); omega)
lemma frequency_one_gt : 1<frequency 1 := by simpa [frequency_zero] using frequency_strictMono (by omega : 0<1)

lemma polynomialWindow_pos (j : ℕ) : 0<polynomialWindow j := (scaleState j).2.Kpos
lemma polynomialWindow_gt_length (j : ℕ) : blockLength j<polynomialWindow (j+1) :=
  (scaleStep j).numeric.2.2.2.2.2.2.2.1
lemma polynomialWindow_le_length (j : ℕ) : polynomialWindow j≤blockLength j :=
  (scaleStep j).numeric.2.2.1
lemma blockLength_strictMono : StrictMono blockLength :=
  strictMono_nat_of_lt_succ fun j => (polynomialWindow_gt_length j).trans_le (polynomialWindow_le_length (j+1))
lemma blockLength_ge (j : ℕ) : 200≤blockLength j := (scaleStep j).numeric.1
lemma crossingBudget_mono : Monotone crossingBudget :=
  monotone_nat_of_le_succ fun j => (scaleStep (j+1)).Lprev
lemma dropSize_ge_budget (j : ℕ) : crossingBudget j≤dropSize j := le_max_left _ _
lemma dropSize_nonneg (j : ℕ) : 0≤dropSize j :=
  (by change 0≤(scaleStep j).L; linarith [(scaleStep j).Lge] : 0≤crossingBudget j).trans (dropSize_ge_budget j)

lemma frequency_block_ratio (j : ℕ) {k : ℕ} (hk : k<blockLength j) :
    100*(blockLength j:ℝ) < (frequency (blockEnd j+k+1):ℝ)/frequency (blockEnd j+k) := by
  rw [show blockEnd j+k+1=blockEnd j+(k+1) by omega,
    frequency_block j (by omega),frequency_block j hk.le]
  exact ((scaleStep j).qratio k hk).2

lemma frequency_radix_bound (j : ℕ) {k : ℕ} (hk : k≤blockLength j) :
    100*(blockLength j:ℝ) < (frequency (blockEnd j+k+1):ℝ)/frequency (blockEnd j+k) := by
  by_cases hlt : k<blockLength j
  · exact frequency_block_ratio j hlt
  · have he : k=blockLength j := by omega
    subst k
    have h := frequency_block_ratio (j+1) (k:=0) (scaleStep (j+1)).mpos
    have hlen : (blockLength j:ℝ) ≤ blockLength (j+1) :=
      Nat.cast_le.mpr (blockLength_strictMono.monotone (Nat.le_succ j))
    change 100*(blockLength (j+1):ℝ) < (frequency (blockEnd j+blockLength j+1):ℝ)/frequency (blockEnd j+blockLength j) at h
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hlen (by norm_num)) h

def modelFrequency (i : ℕ) : ℕ := frequency (i+1)
def coordinateBlock (i : ℕ) : ℕ := blocks.number i
def coordinateDrop (i : ℕ) : ℝ := dropSize (coordinateBlock i)

def parameterAngle : ℝ := exists_global_angle.choose
lemma parameterAngle_spec : 0<parameterAngle ∧ parameterAngle<1 ∧ Irrational parameterAngle ∧
    ∀ j, parameterAngle∈Icc (scaleStep j).a (scaleStep j).b := exists_global_angle.choose_spec
lemma block_phase (j : ℕ) (i : Fin (blockLength j)) :
    Int.fract ((frequency (blockEnd j+i.val+1):ℝ)*parameterAngle)∈
      Ioo (1/((blockLength j:ℝ)*polynomialWindow j)) (2/((blockLength j:ℝ)*polynomialWindow j)) := by
  have hh := (scaleStep j).phases parameterAngle (parameterAngle_spec.2.2.2 j) i
  rw [show blockEnd j+i.val+1=blockEnd j+(i.val+1) by omega,frequency_block j (by omega)]
  exact hh
end

open Set Filter MeasureTheory
open scoped Topology BigOperators

def coordinatePhase (i : ℕ) : ℝ := Int.fract ((modelFrequency i:ℝ)*parameterAngle)

lemma coordinatePhase_block (j : ℕ) (i : Fin (blockLength j)) :
    coordinatePhase (blocks.equiv ⟨j,i⟩)∈
      Ioo (1/((blockLength j:ℝ)*polynomialWindow j)) (2/((blockLength j:ℝ)*polynomialWindow j)) :=
  block_phase j i
lemma coordinatePhase_pos (i : ℕ) : 0<coordinatePhase i := by
  obtain ⟨⟨j,k⟩,rfl⟩ := blocks.equiv.surjective i
  exact lt_trans (by
    have hm : 0<(blockLength j:ℝ) := Nat.cast_pos.mpr (scaleStep j).mpos
    have hK : 0<(polynomialWindow j:ℝ) := Nat.cast_pos.mpr (polynomialWindow_pos j)
    positivity) (coordinatePhase_block j k).1

lemma dropSize_ge_window_sq (j : ℕ) : (polynomialWindow j:ℝ)^2≤dropSize j := le_max_right _ _


end CircleSampling

end

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_OrbitBounds
attribute [-instance] _root_.OAI.CircleCoupling.labelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CircleSampling

universe uX uY uι

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
open CircleModel Set Filter MeasureTheory
open scoped Topology BigOperators

def modelAngle : CircleModel.CircleX := (parameterAngle : CircleModel.CircleX)
def modelGood : Set CircleModel.CircleX := CircleModel.good modelFrequency modelAngle
def modelF (k : ℤ) : CircleModel.CircleX → ℝ := CircleModel.cocycle modelFrequency modelAngle coordinateDrop k
def modelWeight : CircleModel.CircleX → ℝ := modelF 1

lemma model_beta (i : ℕ) : CircleModel.beta modelFrequency modelAngle i=coordinatePhase i := by
  unfold CircleModel.beta CircleModel.Xi modelAngle coordinatePhase
  rw [←AddCircle.coe_nsmul, nsmul_eq_mul,CircleModel.repr_mk]
lemma modelF_measurable (k : ℤ) : Measurable (modelF k) := CircleModel.measurable_cocycle _ _ _ _
lemma modelF_pos (k : ℤ) (x : CircleModel.CircleX) : 0 < modelF k x := CircleModel.cocycle_pos _ _ _ _ _
lemma modelF_zero (x : CircleModel.CircleX) : modelF 0 x=1 := CircleModel.cocycle_zero _ _ _ _
lemma modelF_antitone (x : CircleModel.CircleX) : Antitone (fun k => modelF k x) :=
  CircleModel.cocycle_antitone _ _ _ (fun i => dropSize_nonneg (coordinateBlock i)) x
lemma modelWeight_bounds (x : CircleModel.CircleX) : 0 < modelWeight x ∧ modelWeight x≤1 := by
  exact ⟨modelF_pos 1 x,by simpa only [modelWeight, modelF_zero] using modelF_antitone x (show (0:ℤ)≤1 by norm_num)⟩
end

open MeasureTheory Set Filter
open scoped ENNReal Topology

section
open ContinuousCircleWeight.Sampling MeasureTheory Set CircleModel
open scoped BigOperators

lemma stageEll_pos (j : ℕ) : 0 < scaleEll (blockLength j) :=
  Real.rpow_pos_of_pos (Nat.cast_pos.mpr (scaleStep j).mpos) _
lemma stageAlpha_pos (j : ℕ) : 0 < scaleAlpha (blockLength j) :=
  Real.rpow_pos_of_pos (Nat.cast_pos.mpr (scaleStep j).mpos) _

def stageFactor (positive : Bool) (j : ℕ) (n : ℤ) (i : Fin (blockLength j)) (x : CircleModel.CircleX) : ℝ :=
  orientedWeight positive (scaleEll (blockLength j)) (scaleAlpha (blockLength j))
    (((scaleStep j).q (i+1):ℤ) • x)
    (((n:ℝ)*Int.fract (((scaleStep j).q (i+1):ℝ)*parameterAngle):ℝ):CircleModel.CircleX)
def stageWeight (positive : Bool) (j : ℕ) (n : ℤ) (x : CircleModel.CircleX) : ℝ :=
  ∏ i : Fin (blockLength j), stageFactor positive j n i x

lemma stageFactor_measurable (positive : Bool) (j : ℕ) (n : ℤ) (i : Fin (blockLength j)) :
    Measurable (stageFactor positive j n i) :=
  (measurable_orientedWeight _ _ _).comp ((continuous_id.zsmul _).measurable.prodMk measurable_const)
lemma stageFactor_bounds (positive : Bool) (j : ℕ) (n : ℤ) (i : Fin (blockLength j)) (x : CircleModel.CircleX) :
    0 ≤ stageFactor positive j n i x ∧
      stageFactor positive j n i x ≤ 1/(scaleEll (blockLength j)*scaleAlpha (blockLength j)) :=
  orientedWeight_bounds positive (stageEll_pos j) (stageAlpha_pos j) _ _
lemma stageWeight_measurable (positive : Bool) (j : ℕ) (n : ℤ) : Measurable (stageWeight positive j n) := by
  unfold stageWeight
  exact Finset.measurable_prod _ (fun i _ => stageFactor_measurable _ _ _ i)
lemma stageWeight_bounds (positive : Bool) (j : ℕ) (n : ℤ) (x : CircleModel.CircleX) :
    0 ≤ stageWeight positive j n x ∧ stageWeight positive j n x ≤
      (1/(scaleEll (blockLength j)*scaleAlpha (blockLength j)))^(blockLength j) := by
  constructor
  · exact Finset.prod_nonneg (fun i _ => (stageFactor_bounds positive j n i x).1)
  · have h := Finset.prod_le_prod (s:=Finset.univ) (fun i _ => (stageFactor_bounds positive j n i x).1)
      (fun i _ => (stageFactor_bounds positive j n i x).2)
    simpa [stageWeight] using h
lemma stageWeight_memLp (positive : Bool) (j : ℕ) (n : ℤ) : MemLp (stageWeight positive j n) 2 := by
  apply MemLp.of_bound (stageWeight_measurable positive j n).aestronglyMeasurable
    ((1/(scaleEll (blockLength j)*scaleAlpha (blockLength j)))^(blockLength j))
  exact ae_of_all _ (fun x => by rw [Real.norm_of_nonneg (stageWeight_bounds positive j n x).1]; exact (stageWeight_bounds positive j n x).2)

instance stageSample_nonempty (j : ℕ) (t : Fin ((scaleState j).1.q (scaleState j).1.d)) :
    Nonempty ((scaleStep j).samples t) := (scaleStep j).samples_nonempty t |>.coe_sort

def stageDensity (positive : Bool) (j : ℕ) (t : Fin ((scaleState j).1.q (scaleState j).1.d)) : CircleModel.CircleX → ℝ :=
  finiteAverage (fun n : (scaleStep j).samples t => stageWeight positive j n.val)
end

open CircleModel Set MeasureTheory
open scoped BigOperators

def sampleBound (j : ℕ) : ℝ := (blockLength j:ℝ)^((7:ℝ)/10*blockLength j)
def oldGraphBad (j : ℕ) : Set CircleX :=
  ⋃ i : Fin (blockEnd j), {x | 1-(modelFrequency i:ℝ)*gridTolerance j (scaleState j).1  ≤  CircleModel.Xi modelFrequency i x}
def tailGraphBad (j : ℕ) : Set CircleX :=
  ⋃ i : {i : ℕ // blockEnd (j+1)  ≤  i}, {x | 1-sampleBound j*coordinatePhase i  ≤  CircleModel.Xi modelFrequency i x}
def graphBad (j : ℕ) : Set CircleX := oldGraphBad j ∪ tailGraphBad j


end CircleSampling

end

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_RationalGraphs
attribute [-instance] _root_.OAI.CircleCoupling.labelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

universe uι uX uY

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

namespace CircleSampling

open Set
lemma frequency_dvd_of_le {a b : ℕ} (h : a ≤ b) : frequency a ∣ frequency b := by
  induction b, h using Nat.le_induction with
  | base => exact dvd_rfl
  | succ b h ih => exact ih.trans (frequency_dvd b)
lemma rational_stage_index (D j : ℕ) (a : Fin (frequency (D+1))) (hj : D+1 ≤ blockEnd j) :
    ∃ t : Fin ((scaleState j).1.q (scaleState j).1.d),
      gridPoint (scaleState j).1 t=(((a.val:ℝ)/(frequency (D+1):ℝ):ℝ):CircleX) := by
  have hq : frequency (blockEnd j)=(scaleState j).1.q (scaleState j).1.d := frequency_eq_state (j:=j) le_rfl
  have hdiv := frequency_dvd_of_le hj
  rw [hq] at hdiv
  obtain ⟨t,ht⟩ := rational_grid_lift (frequency_pos (D+1)) ((scaleState j).2.qpos _ le_rfl) hdiv a
  exact ⟨t,congrArg (fun x : ℝ => (x:CircleX)) ht⟩
end CircleSampling

open MeasureTheory Set

end

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_GraphTransfer
attribute [-instance] _root_.OAI.CircleCoupling.labelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

universe uX uY uι uE

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

namespace CircleSampling

open MeasureTheory Set Filter
open scoped ENNReal Topology

def orbitEquiv (n : ℤ) : CircleX ≃ᵐ CircleX := MeasurableEquiv.addRight (n•modelAngle)

def stageGraph (j : ℕ) (t : Fin ((scaleState j).1.q (scaleState j).1.d)) : FiniteMeasure (CircleX×CircleX) :=
  ⟨finiteGraphAverage volume (fun n : (scaleStep j).samples t => stageWeight true j n.val)
    (fun n => orbitEquiv n.val), finiteGraphAverage_finite _ _ _
      (fun n => (stageWeight_memLp true j n.val).integrable (by norm_num))
      (fun n x => (stageWeight_bounds true j n.val x).1)⟩

def translation (h : CircleX) : C(CircleX,CircleX) := ⟨fun x => x+h,continuous_id.add continuous_const⟩

def rationalPoint (D : ℕ) (a : Fin (frequency (D+1))) : CircleX := (((a.val:ℝ)/(frequency (D+1):ℝ):ℝ):CircleX)
def rationalIndex (D : ℕ) (a : Fin (frequency (D+1))) (j : ℕ) :
    Fin ((scaleState (D+1+j)).1.q (scaleState (D+1+j)).1.d) :=
  (rational_stage_index D (D+1+j) a (le_trans (by omega) (blockEnd_ge _))).choose

def rationalGraph (D : ℕ) (a : Fin (frequency (D+1))) (j : ℕ) : FiniteMeasure (CircleX×CircleX) :=
  (stageGraph (D+1+j) (rationalIndex D a j)).restrict (Prod.fst ⁻¹' (graphBad (D+1+j))ᶜ)

def circleProbability : ProbabilityMeasure CircleX := ⟨volume,inferInstance⟩
end CircleSampling

open MeasureTheory Set Filter Topology TopologicalSpace

end

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_ProjectionIdentity
attribute [-instance] _root_.OAI.CircleCoupling.labelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

universe uX uE

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

namespace CircleSampling
open MeasureTheory Set Filter ContinuousCircleWeight
open scoped ComplexInnerProductSpace Topology ENNReal

attribute [local instance] OAI.CircleSampling.instMeasurableSpaceSubtypePreLpIntComplexMemAddSubgroupFiberHilbert
structure ModelProjectionField where
  p : CircleX → FiberOperator
  projection : ∀ x,IsStarProjection (p x)
  norm_le : ∀ x,‖p x‖ ≤ 1
  measurable : ∀ k : ℤ,Measurable (fun x => p x (lp.single 2 k 1))
  invariant : ∀ᵐ x, (1-p x)*fiberCocycleShift (fun k => modelF k x)
    (fun k => modelF_pos k x) (modelF_antitone x)*p x=0
  covariance : ∀ n : ℤ, ∀ᵐ x, p x*(fiberShift n).toContinuousLinearEquiv.toContinuousLinearMap=
    (fiberShift n).toContinuousLinearEquiv.toContinuousLinearMap*p (CircleModel.shift modelAngle n x)

def rationalCap (D : ℕ) : ℝ≥0 := ⟨Real.exp (∑ i∈Finset.range D,coordinateDrop i),(Real.exp_pos _).le⟩
end CircleSampling

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

namespace CircleSampling

section

section
open Set Filter MeasureTheory
open scoped Topology BigOperators

def coordinateRadix (i : ℕ) : ℕ := frequency (i+2)/frequency (i+1)
def bridgeWidth (j : ℕ) : ℝ := bridgeSize j/(blockLength j:ℝ)
def rangeWidth (j : ℕ) : ℝ := (blockLength j:ℝ)^(-(19:ℝ)/20)

lemma coordinateRadix_mul (i : ℕ) : coordinateRadix i*frequency (i+1)=frequency (i+2) :=
  Nat.div_mul_cancel (frequency_dvd (i+1))
lemma coordinateRadix_cast (i : ℕ) : (coordinateRadix i:ℝ)=(frequency (i+2):ℝ)/frequency (i+1) := by
  unfold coordinateRadix
  exact Nat.cast_div (frequency_dvd (i+1)) (Nat.cast_ne_zero.mpr (frequency_pos _).ne')
lemma coordinateBlock_equiv (x : Σ j, Fin (blocks.m j)) : coordinateBlock (blocks.equiv x)=x.1 := by
  exact blocks.number_eq (by change blockEnd x.1≤blockEnd x.1+x.2.val; omega)
    (by change blockEnd x.1+x.2.val<blockEnd x.1+blockLength x.1; exact Nat.add_lt_add_left x.2.isLt _)

lemma coordinateRadix_bound (i : ℕ) : 100*blockLength (coordinateBlock i)≤coordinateRadix i := by
  obtain ⟨⟨j,k⟩,rfl⟩ := blocks.equiv.surjective i
  rw [coordinateBlock_equiv]
  have hk : k.val<blockLength j := k.isLt
  have hh := frequency_radix_bound j (k:=k.val+1) (by omega)
  have he : blocks.equiv ⟨j,k⟩=blockEnd j+k.val := rfl
  have hc : (100*blockLength j:ℝ)≤coordinateRadix (blocks.equiv ⟨j,k⟩) := by
    rw [coordinateRadix_cast,he,show blockEnd j+k.val+2=blockEnd j+(k.val+1)+1 by omega,
      show blockEnd j+k.val+1=blockEnd j+(k.val+1) by omega]
    exact hh.le
  exact_mod_cast hc

lemma blockLength_ge_twoHundred (j : ℕ) : 200≤blockLength j := (scaleStep j).numeric.1
lemma bridgeSize_ge_one (j : ℕ) : 1≤bridgeSize j := (scaleState j).2.Gge
lemma bridgeWidth_bounds (j : ℕ) : 1/(blockLength j:ℝ)≤bridgeWidth j ∧ bridgeWidth j≤1/4 := by
  have hm : 0<(blockLength j:ℝ) := Nat.cast_pos.mpr (scaleStep j).mpos
  refine ⟨div_le_div_of_nonneg_right (bridgeSize_ge_one j) hm.le,?_⟩
  exact (div_le_iff₀ hm).mpr (by
    have hg := (scaleStep j).numeric.2.2.2.1
    change 4*bridgeSize j≤(blockLength j:ℝ) at hg
    linarith)
lemma rangeWidth_bounds (j : ℕ) : 1/(blockLength j:ℝ)≤rangeWidth j ∧ rangeWidth j≤1/4 := by
  refine ⟨?_,(scaleStep j).numeric.2.2.2.2.2.2.2.2⟩
  have hm : (1:ℝ)≤blockLength j := by exact_mod_cast (scaleStep j).mpos
  change _≤(blockLength j:ℝ)^(-(19:ℝ)/20)
  rw [one_div,←Real.rpow_neg_one]
  exact Real.rpow_le_rpow_of_exponent_le hm (by norm_num)

def stageTagged (j i : ℕ) : Bool := decide (coordinateBlock i=j)
end

open MeasureTheory Set Filter CircleCoupling
open scoped BigOperators ENNReal Topology

def actualCoordinate (i : ℕ) : CoordinateParameters where
  l := coordinateRadix i
  m := blockLength (coordinateBlock i)
  κ := kappa (coordinateBlock i)
  a := bridgeWidth (coordinateBlock i)
  b := rangeWidth (coordinateBlock i)
  hm := blockLength_ge_twoHundred _
  hl := coordinateRadix_bound i
  hκ0 := (kappa_pos _).le
  hκ := kappa_le _
  ha := bridgeWidth_bounds _
  hb := rangeWidth_bounds _
def actualSystem : DigitSystem where
  b₀ := frequency 1
  hb₀ := frequency_one_gt
  coord := actualCoordinate

lemma actual_radix_zero : actualSystem.radix 0=frequency 1 := rfl
lemma actual_radix_succ (i : ℕ) : actualSystem.radix (i+1)=coordinateRadix i := rfl
lemma actual_denominator (i : ℕ) : CircleDigits.denominator actualSystem.radix i=frequency i := by
  induction i with
  | zero => exact frequency_zero.symm
  | succ i ih =>
    rw [CircleDigits.denominator_succ,ih]
    cases i with
    | zero => simp only [actual_radix_zero,frequency_zero,one_mul]
    | succ i =>
      rw [actual_radix_succ,mul_comm]
      exact coordinateRadix_mul i

end

open MeasureTheory Set Filter CircleCoupling
open scoped BigOperators ENNReal Topology

def marginalConstant : ℝ := Real.exp (30*(∑' s,(kappa s)^2)+5)
end CircleSampling

namespace CircleSampling
open MeasureTheory Set Filter ContinuousCircleWeight CircleCoupling
open scoped Topology ENNReal ComplexInnerProductSpace

abbrev ActualSamples := actualSystem.Samples
def firstEndpoint : ActualSamples → CircleX := actualSystem.endpoint (fun _ => false)
def lastEndpoint : ActualSamples → CircleX := actualSystem.endpoint (fun _ => true)
def hybridEndpoint (D : ℕ) : ActualSamples → CircleX := actualSystem.endpoint (hybridChoice D)

def actualPairLaw (j : ℕ) (e : ℕ → Bool) : FiniteMeasure (CircleX×CircleX) :=
  ⟨Measure.map (fun ω => (firstEndpoint ω,actualSystem.endpoint e ω)) (actualSystem.probability (stageTagged j)),inferInstance⟩
end CircleSampling

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

namespace CircleSampling
open MeasureTheory Set CircleCoupling
open scoped BigOperators ENNReal

def blockCoordinates (j : ℕ) : Finset ℕ := Finset.Ico (blockEnd j+1) (blockEnd (j+1)+1)
lemma blockCoordinates_card (j : ℕ) : (blockCoordinates j).card=blockLength j := by
  rw [blockCoordinates,Nat.card_Ico]
  have h := blocks.step j
  change blockEnd (j+1)=blockEnd j+blockLength j at h
  omega
lemma blockCoordinates_zero (j : ℕ) : 0 ∉ blockCoordinates j := by simp [blockCoordinates]
lemma blockCoordinates_block (j n : ℕ) (hn : n+1 ∈ blockCoordinates j) : coordinateBlock n=j := by
  have hh := Finset.mem_Ico.mp hn
  exact blocks.number_eq (by change blockEnd j ≤ n; omega) (by change n<blockEnd (j+1); omega)

def stageTagEvent (j : ℕ) : Set actualSystem.Samples := actualSystem.oneTagEvent (blockCoordinates j)

lemma stageTagEvent_margins (j : ℕ) {ω : actualSystem.Samples} (hw : ω∈actualSystem.supported)
    (hω : ω∈stageTagEvent j) :
    (∃ n, n+1∈blockCoordinates j ∧ (ω (n+1)).1=some (4:Fin 5)) ∧
    ∀ n, n+1∈blockCoordinates j →
      (((ω (n+1)).2.1.val:ℝ)+1)/(coordinateRadix n:ℝ) ≤ 1-2/(blockLength j:ℝ) ∧
      2/(blockLength j:ℝ) ≤ ((ω (n+1)).2.2.val:ℝ)/(coordinateRadix n:ℝ) := by
  obtain ⟨⟨i,hi,hit⟩,hm⟩ := actualSystem.oneTagEvent_margins hw hω
  constructor
  · cases i with
    | zero => exact False.elim (blockCoordinates_zero j hi)
    | succ n => exact ⟨n,hi,hit⟩
  · intro n hn
    have hh := hm (n+1) hn
    change (((ω (n+1)).2.1.val:ℝ)+1)/(coordinateRadix n:ℝ) ≤ 1-2/(blockLength (coordinateBlock n):ℝ) ∧
      2/(blockLength (coordinateBlock n):ℝ) ≤ ((ω (n+1)).2.2.val:ℝ)/(coordinateRadix n:ℝ) at hh
    rwa [blockCoordinates_block j n hn] at hh
end CircleSampling

end

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_Thresholds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CircleSampling

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

section
open Set Filter
open scoped Topology

def blockScale (s : ℕ) : ℝ := (blockLength s:ℝ)*polynomialWindow s
def blockRange (s : ℕ) : ℝ := (blockLength s:ℝ)^((4:ℝ)/5*blockLength s)
lemma blockScale_pos (s : ℕ) : 0<blockScale s := mul_pos (Nat.cast_pos.mpr (scaleStep s).mpos) (Nat.cast_pos.mpr (polynomialWindow_pos s))
lemma blockRange_ge_length (s : ℕ) : (blockLength s:ℝ) ≤ blockRange s := by
  have hm : (200:ℝ) ≤ blockLength s := by exact_mod_cast blockLength_ge s
  calc
    _ = (blockLength s:ℝ)^(1:ℝ) := (Real.rpow_one _).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
lemma bridge_overlap (s : ℕ) : bridgeSize (s+1)*(polynomialWindow (s+1):ℝ)<blockRange s := by
  exact (scaleStep s).numeric.2.2.2.2.2.1
lemma exists_large_range (j : ℕ) {t : ℝ} (ht : blockScale j/4<t) :
    (∃ s : ℕ, j ≤ s ∧ blockScale s/4≤t ∧ t≤blockRange s) ∨
    (∃ s : ℕ, j < s ∧ bridgeSize s*(polynomialWindow s:ℝ)≤t ∧ t≤blockScale s/4) := by
  have hex : ∃ n : ℕ,t≤blockRange (j+n) := by
    obtain ⟨n,hn⟩ := exists_nat_ge t
    refine ⟨n,hn.trans ?_⟩
    have hmn : n≤blockLength (j+n) := (by omega : n≤j+n).trans (blockLength_strictMono.id_le _)
    exact (show (n:ℝ) ≤ (blockLength (j+n):ℝ) by exact_mod_cast hmn).trans (blockRange_ge_length _)
  let n := Nat.find hex
  have htop : t≤blockRange (j+n) := Nat.find_spec hex
  cases hn : n with
  | zero => exact Or.inl ⟨j,le_rfl,ht.le,by simpa [hn] using htop⟩
  | succ a =>
    have hprev : blockRange (j+a)<t := lt_of_not_ge (Nat.find_min hex (by omega : a<Nat.find hex))
    by_cases hscale : blockScale (j+n)/4≤t
    · exact Or.inl ⟨j+n,by omega,hscale,htop⟩
    · refine Or.inr ⟨j+n,by omega,?_,(lt_of_not_ge hscale).le⟩
      have hb : bridgeSize (j+n)*(polynomialWindow (j+n):ℝ) ≤ blockRange (j+a) := by
        simpa only [hn,Nat.add_succ] using (bridge_overlap (j+a)).le
      exact hb.trans hprev.le
end

section
open Set CircleCoupling CircleCoupling.CoordinateParameters ContinuousCircleWeight.Sampling
open scoped BigOperators

def crossingThreshold (k : ℤ) (i : ℕ) : ℝ := 1-Int.fract ((k:ℝ)*coordinatePhase (i-1))
def stageCrossingWidth (s : ℕ) (e : Bool) : ℝ := if e then rangeWidth s else bridgeWidth s
def stageCrossingProbability (s : ℕ) (e : Bool) : ℝ := crossingProbability (kappa s) (stageCrossingWidth s e) (blockLength s)

lemma coordinatePhase_bounds (i : ℕ) : coordinatePhase i ∈ Ioo (1/blockScale (coordinateBlock i)) (2/blockScale (coordinateBlock i)) := by
  obtain ⟨⟨j,k⟩,rfl⟩ := blocks.equiv.surjective i
  rw [coordinateBlock_equiv]
  exact coordinatePhase_block j k
lemma stageCrossingProbability_eq (s n : ℕ) (hn : n+1 ∈ blockCoordinates s) (e : Bool) :
    (actualSystem.coord n).prob e=stageCrossingProbability s e := by
  cases e <;> simp only [CoordinateParameters.prob,CoordinateParameters.ρ,CoordinateParameters.σ,
    actualSystem,actualCoordinate,stageCrossingProbability,stageCrossingWidth,Bool.false_eq_true,↓reduceIte,blockCoordinates_block s n hn]
lemma stageCrossingWidth_eq (s n : ℕ) (hn : n+1 ∈ blockCoordinates s) (e : Bool) :
    actualSystem.crossingWidth e (n+1)=stageCrossingWidth s e := by
  cases e <;> simp only [DigitSystem.crossingWidth,CoordinateParameters.width,
    actualSystem,actualCoordinate,stageCrossingWidth,Bool.false_eq_true,↓reduceIte,blockCoordinates_block s n hn]
lemma stageCrossingProbability_nonneg (s : ℕ) (e : Bool) : 0 ≤ stageCrossingProbability s e :=
  crossingProbability_nonneg (kappa_pos s).le
lemma stageCrossingProbability_le_one (s : ℕ) (e : Bool) : stageCrossingProbability s e ≤ 1 := by
  have hi : blockEnd s+1 ∈ blockCoordinates s := Finset.mem_Ico.mpr ⟨le_rfl,by have hm : 0 < blockLength s := (scaleStep s).mpos; change blockEnd s+1<blockEnd s+blockLength s+1; omega⟩
  rw [←stageCrossingProbability_eq s (blockEnd s) hi e]
  exact (actualSystem.coord (blockEnd s)).prob_le_one e
lemma stage_range_strength (s : ℕ) : crossingBudget s ≤ (blockLength s:ℝ)*stageCrossingProbability s true := by
  have hm : 0<(blockLength s:ℝ) := Nat.cast_pos.mpr (scaleStep s).mpos
  have hroot : Real.sqrt (rangeWidth s/(blockLength s:ℝ))=(blockLength s:ℝ)^(-(39:ℝ)/40) := by
    rw [Real.sqrt_eq_rpow,rangeWidth]
    conv_lhs => arg 1; rhs; rw [←Real.rpow_one (blockLength s:ℝ)]
    rw [←Real.rpow_sub hm,←Real.rpow_mul hm.le]
    norm_num
  have he : (blockLength s:ℝ)*stageCrossingProbability s true=kappa s*(blockLength s:ℝ)^((1:ℝ)/40) := by
    change (blockLength s:ℝ)*(kappa s*Real.sqrt (rangeWidth s/(blockLength s:ℝ)))=_
    rw [hroot]
    calc
      _ = kappa s*((blockLength s:ℝ)^(1:ℝ)*(blockLength s:ℝ)^(-(39:ℝ)/40)) := by rw [Real.rpow_one]; ring
      _ = _ := by rw [←Real.rpow_add hm]; norm_num
  rw [he]
  exact (scaleStep s).numeric.2.2.2.2.1
lemma stage_bridge_strength (s : ℕ) : crossingBudget s ≤ (blockLength (s+1):ℝ)*stageCrossingProbability (s+1) false := by
  have hm : 0<(blockLength (s+1):ℝ) := Nat.cast_pos.mpr (scaleStep (s+1)).mpos
  have hroot : Real.sqrt (bridgeWidth (s+1)/(blockLength (s+1):ℝ))=Real.sqrt (bridgeSize (s+1))/(blockLength (s+1):ℝ) := by
    rw [bridgeWidth,div_div,←pow_two,Real.sqrt_div (le_trans (by norm_num) (bridgeSize_ge_one _)),Real.sqrt_sq hm.le]
  have he : (blockLength (s+1):ℝ)*stageCrossingProbability (s+1) false=kappa (s+1)*Real.sqrt (bridgeSize (s+1)) := by
    change (blockLength (s+1):ℝ)*(kappa (s+1)*Real.sqrt (bridgeWidth (s+1)/(blockLength (s+1):ℝ)))=_
    rw [hroot]; field_simp
  rw [he]
  exact (scaleStep s).bridge

lemma bridge_thresholds (s : ℕ) (k : ℤ)
    (hklo : bridgeSize s*(polynomialWindow s:ℝ)≤|(k:ℝ)|) (hkhi : |(k:ℝ)| ≤blockScale s/4) :
    ∀ i∈blockCoordinates s, bridgeWidth s ≤ crossingThreshold k i ∧ crossingThreshold k i≤1-bridgeWidth s := by
  intro i hi
  have hi0 : i ≠ 0 := by intro hz; subst i; exact blockCoordinates_zero s hi
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi0
  have hn := blockCoordinates_block s n hi
  have hβ := coordinatePhase_bounds n
  rw [hn] at hβ
  have hm : 0<(blockLength s:ℝ) := Nat.cast_pos.mpr (scaleStep s).mpos
  have hK : 0<(polynomialWindow s:ℝ) := Nat.cast_pos.mpr (polynomialWindow_pos s)
  have hN := blockScale_pos s
  have hG : 0<bridgeSize s := lt_of_lt_of_le (by norm_num) (bridgeSize_ge_one s)
  have hka : 0 < |(k:ℝ)| := lt_of_lt_of_le (mul_pos hG hK) hklo
  apply threshold_bounds_of_abs (lt_of_lt_of_le (by positivity) (bridgeWidth_bounds s).1)
  · change bridgeWidth s ≤ |(k:ℝ)| *coordinatePhase n
    calc
      _ = bridgeSize s*(polynomialWindow s:ℝ)*(1/blockScale s) := by unfold bridgeWidth blockScale; field_simp
      _ ≤ |(k:ℝ)| *(1/blockScale s) := mul_le_mul_of_nonneg_right hklo (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left hβ.1.le hka.le
  · change |(k:ℝ)| *coordinatePhase n<1/2
    calc
      _ < |(k:ℝ)| *(2/blockScale s) := mul_lt_mul_of_pos_left hβ.2 hka
      _ ≤ (blockScale s/4)*(2/blockScale s) := mul_le_mul_of_nonneg_right hkhi (by positivity)
      _ = 1/2 := by field_simp; ring

lemma large_thresholds (s : ℕ) (k : ℤ) (hklo : blockScale s/4≤|(k:ℝ)|) (hkhi : |(k:ℝ)| ≤blockRange s) :
    ∃ I : Finset ℕ, I⊆blockCoordinates s ∧ (blockLength s:ℝ)/20≤(I.card:ℝ) ∧
      ∀ i∈I, rangeWidth s≤crossingThreshold k i ∧ crossingThreshold k i≤1-rangeWidth s := by
  let emb : Fin (blockLength s) ↪ ℕ := ⟨fun i => blockEnd s+i.val+1,by intro a b h; apply Fin.ext; dsimp at h; omega⟩
  let J := Finset.univ.filter fun i : Fin (blockLength s) => coordinatePhase (blockEnd s+i.val) ∉ phaseFailure (rangeWidth s) k
  refine ⟨J.map emb,?_,?_,?_⟩
  · intro i hi
    obtain ⟨a,ha,rfl⟩ := Finset.mem_map.mp hi
    exact Finset.mem_Ico.mpr ⟨by change blockEnd s+1≤blockEnd s+a.val+1; omega,by change blockEnd s+a.val+1<blockEnd s+blockLength s+1; have := a.isLt; omega⟩
  · rw [Finset.card_map]
    have hc := (scaleStep s).cover parameterAngle (parameterAngle_spec.2.2.2 s) k hklo hkhi
    have hJ : J=Finset.univ.filter (fun i : Fin (blockLength s) => Int.fract (((scaleStep s).q (i+1):ℝ)*parameterAngle) ∉ phaseFailure (rangeWidth s) k) := by
      ext i
      simp only [J,Finset.mem_filter,Finset.mem_univ,true_and]
      change (Int.fract (((frequency (blockEnd s+i.val+1)):ℝ)*parameterAngle) ∉ _) ↔ _
      rw [show blockEnd s+i.val+1=blockEnd s+(i.val+1) by omega,frequency_block s (by omega)]
    rw [hJ]
    exact hc
  · intro i hi
    obtain ⟨a,ha,rfl⟩ := Finset.mem_map.mp hi
    have hh := (Finset.mem_filter.mp ha).2
    have hh' : rangeWidth s < 1-Int.fract ((k:ℝ)*coordinatePhase (blockEnd s+a.val)) ∧
        1-Int.fract ((k:ℝ)*coordinatePhase (blockEnd s+a.val))<1-rangeWidth s := by
      have hr (x : ℝ) : repr (x:CircleX)=Int.fract x := by
        change (AddCircle.equivIco 1 0 (x:CircleX)).val=_
        simpa only [div_one,mul_one] using AddCircle.coe_equivIco_mk_apply (p:=(1:ℝ)) x
      simpa only [phaseFailure,Set.mem_ofPred_eq,not_not,hr] using hh
    change rangeWidth s ≤ 1-Int.fract ((k:ℝ)*coordinatePhase (blockEnd s+a.val+1-1)) ∧ 1-Int.fract ((k:ℝ)*coordinatePhase (blockEnd s+a.val+1-1))≤1-rangeWidth s
    simpa only [Nat.add_sub_cancel] using And.intro hh'.1.le hh'.2.le
end

section
open MeasureTheory Set Filter CircleCoupling CircleDigits
open scoped ENNReal

def regularSamples : Set ActualSamples := {ω | ω∈actualSystem.supported ∧
  firstEndpoint ω∈modelGood ∧ lastEndpoint ω∈modelGood ∧
  firstEndpoint ω∈gridFree actualSystem.radix ∧ lastEndpoint ω∈gridFree actualSystem.radix}
lemma actual_Xi_tail {ω : ActualSamples} (hω : ω∈regularSamples) (n : ℕ) :
    CircleModel.Xi modelFrequency n (firstEndpoint ω)=scaledTail actualSystem.radix (fun i => (ω i).2.1) (n+1) ∧
    CircleModel.Xi modelFrequency n (lastEndpoint ω)=scaledTail actualSystem.radix (fun i => (ω i).2.2) (n+1) := by
  constructor
  · change (AddCircle.measurableEquivIco 1 0 (frequency (n+1) • firstEndpoint ω)).val=_
    rw [←actual_denominator]
    exact scaledTail_repr actualSystem.radix_ge_two _ hω.2.2.2.1 _
  · change (AddCircle.measurableEquivIco 1 0 (frequency (n+1) • lastEndpoint ω)).val=_
    rw [←actual_denominator]
    exact scaledTail_repr actualSystem.radix_ge_two _ hω.2.2.2.2 _
lemma regular_order {ω : ActualSamples} (hω : ω∈regularSamples) (n : ℕ) :
    CircleModel.Xi modelFrequency n (firstEndpoint ω) ≤ CircleModel.Xi modelFrequency n (lastEndpoint ω) := by
  rw [(actual_Xi_tail hω n).1,(actual_Xi_tail hω n).2]
  exact scaledTail_mono actualSystem.radix_ge_two hω.1.1 _
lemma crossing_decay {ω : ActualSamples} (hω : ω∈regularSamples) (k : ℤ) (n : ℕ)
    (hlo : scaledTail actualSystem.radix (fun i => (ω i).2.1) (n+1)<crossingThreshold k (n+1))
    (hhi : crossingThreshold k (n+1) ≤ scaledTail actualSystem.radix (fun i => (ω i).2.2) (n+1)) :
    modelF k (lastEndpoint ω)/modelF k (firstEndpoint ω) ≤ Real.exp (-coordinateDrop n) := by
  apply CircleModel.cocycle_ratio_crossing coordinateDrop (fun i => dropSize_nonneg (coordinateBlock i)) k hω.2.1 hω.2.2.1 (regular_order hω) n
  · simpa only [model_beta,(actual_Xi_tail hω n).1,crossingThreshold,Nat.add_sub_cancel] using hlo
  · simpa only [model_beta,(actual_Xi_tail hω n).2,crossingThreshold,Nat.add_sub_cancel] using hhi

lemma stage_masks (j s : ℕ) (hjs : j ≤ s) (e : Bool) (k : ℤ) (I : Finset ℕ)
    (hI : I⊆blockCoordinates s) (hcard : (blockLength s:ℝ)/20 ≤ (I.card:ℝ))
    (hstrength : crossingBudget j ≤ (blockLength s:ℝ)*stageCrossingProbability s e)
    (hu : ∀ i∈I,stageCrossingWidth s e ≤ crossingThreshold k i ∧ crossingThreshold k i ≤ 1-stageCrossingWidth s e) :
    ∃ H₁ H₂ : Set ActualSamples,MeasurableSet H₁ ∧ MeasurableSet H₂ ∧
      Measure.map firstEndpoint ((actualSystem.probability (stageTagged j)).restrict H₁) ≤ ENNReal.ofReal (Real.exp (-crossingBudget j/400)) • Measure.map firstEndpoint (actualSystem.probability (stageTagged j)) ∧
      Measure.map lastEndpoint ((actualSystem.probability (stageTagged j)).restrict H₂) ≤ ENNReal.ofReal (Real.exp (-crossingBudget j/400)) • Measure.map lastEndpoint (actualSystem.probability (stageTagged j)) ∧
      ∀ ω∈regularSamples,ω∉H₁ → ω∉H₂ → modelF k (lastEndpoint ω)/modelF k (firstEndpoint ω) ≤ Real.exp (-crossingBudget j) := by
  have hzero : 0∉I := fun h => blockCoordinates_zero s (hI h)
  have hwidth : ∀ i∈I,actualSystem.crossingWidth e i ≤ crossingThreshold k i ∧ crossingThreshold k i ≤ 1-actualSystem.crossingWidth e i := by
    intro i hi
    have hi0 : i≠0 := fun hz => hzero (hz ▸ hi)
    obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi0
    rw [stageCrossingWidth_eq s n (hI hi) e]
    exact hu _ hi
  obtain ⟨H₁,H₂,hm₁,hm₂,hd,he,_,hd₁,hd₂⟩ := actualSystem.actual_crossing_estimates (stageTagged j) e I hzero (crossingThreshold k)
    (blockLength s) (stageCrossingProbability s e) (stageCrossingProbability_nonneg s e) (stageCrossingProbability_le_one s e)
    hcard (fun n hn => stageCrossingProbability_eq s n (hI hn) e) hwidth
  have hδ : ENNReal.ofReal (Real.exp (-(blockLength s:ℝ)*stageCrossingProbability s e/400)) ≤ ENNReal.ofReal (Real.exp (-crossingBudget j/400)) := by
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    linarith
  refine ⟨H₁,H₂,hm₁,hm₂,hd₁.trans (by gcongr; exact le_rfl),hd₂.trans (by gcongr; exact le_rfl),?_⟩
  intro ω hω h₁ h₂
  have hn : ω∉noCross actualSystem.radix I (crossingThreshold k) := by rw [←he]; exact fun h => h.elim h₁ h₂
  simp only [noCross,Set.mem_ofPred_eq,not_forall,Classical.not_not] at hn
  obtain ⟨i,hi,hcross⟩ := hn
  have hi0 : i≠0 := fun hz => hzero (hz ▸ hi)
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi0
  have hc := crossing_decay hω k n hcross.1 hcross.2
  apply hc.trans
  apply Real.exp_le_exp.mpr
  change -dropSize (coordinateBlock n) ≤ -crossingBudget j
  rw [blockCoordinates_block s n (hI hi)]
  exact neg_le_neg ((crossingBudget_mono hjs).trans (dropSize_ge_budget s))

lemma large_masks (j : ℕ) (k : ℤ) (hk : blockScale j/4< |(k:ℝ)|) :
    ∃ H₁ H₂ : Set ActualSamples,MeasurableSet H₁ ∧ MeasurableSet H₂ ∧
      Measure.map firstEndpoint ((actualSystem.probability (stageTagged j)).restrict H₁) ≤ ENNReal.ofReal (Real.exp (-crossingBudget j/400)) • Measure.map firstEndpoint (actualSystem.probability (stageTagged j)) ∧
      Measure.map lastEndpoint ((actualSystem.probability (stageTagged j)).restrict H₂) ≤ ENNReal.ofReal (Real.exp (-crossingBudget j/400)) • Measure.map lastEndpoint (actualSystem.probability (stageTagged j)) ∧
      ∀ ω∈regularSamples,ω∉H₁ → ω∉H₂ → modelF k (lastEndpoint ω)/modelF k (firstEndpoint ω) ≤ Real.exp (-crossingBudget j) := by
  rcases exists_large_range j hk with ⟨s,hjs,hlo,hhi⟩ | ⟨s,hjs,hlo,hhi⟩
  · obtain ⟨I,hI,hcard,hu⟩ := large_thresholds s k hlo hhi
    exact stage_masks j s hjs true k I hI hcard ((crossingBudget_mono hjs).trans (stage_range_strength s)) hu
  · have hs0 : s≠0 := by omega
    obtain ⟨a,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hs0
    apply stage_masks j (a+1) (by omega) false k (blockCoordinates (a+1)) (fun _ h => h)
    · rw [blockCoordinates_card]; nlinarith [show (0:ℝ) ≤ blockLength (a+1) from Nat.cast_nonneg _]
    · exact (crossingBudget_mono (by omega : j ≤ a)).trans (stage_bridge_strength a)
    · exact bridge_thresholds (a+1) k hlo hhi
end

open MeasureTheory Set CircleCoupling CircleDigits
open scoped ENNReal

lemma tagged_coordinate_extreme {ω : ActualSamples} (hω : ω∈regularSamples) {n : ℕ}
    (ht : (ω (n+1)).1=some (4:Fin 5)) :
    scaledTail actualSystem.radix (fun i => (ω i).2.1) (n+1)<1/(blockLength (coordinateBlock n):ℝ) ∧
    1-1/(blockLength (coordinateBlock n):ℝ) ≤ scaledTail actualSystem.radix (fun i => (ω i).2.2) (n+1) := by
  let P := actualSystem.coord n
  have hs := hω.1.2 n
  change supportCondition P.l (roundedWidth P.l P.a) (roundedWidth P.l P.b) (roundedTag P.l P.m) (ω (n+1)) at hs
  simp only [supportCondition,ht] at hs
  norm_num at hs
  have hl : (0:ℝ)<P.l := Nat.cast_pos.mpr (NeZero.pos P.l)
  have hm : (0:ℝ)<P.m := P.m_pos
  have hx := (digit_interval actualSystem.radix_ge_two (fun i => (ω i).2.1) hω.2.2.2.1 (n+1)).2
  have hy := (digit_interval actualSystem.radix_ge_two (fun i => (ω i).2.2) hω.2.2.2.2 (n+1)).1
  change _ < (((ω (n+1)).2.1.val:ℝ)+1)/(P.l:ℝ) at hx
  change ((ω (n+1)).2.2.val:ℝ)/(P.l:ℝ) ≤ _ at hy
  have ha : ((ω (n+1)).2.1.val:ℝ)+1 ≤ roundedTag P.l P.m := by exact_mod_cast hs.1
  have hb : (P.l:ℝ)-(roundedTag P.l P.m:ℝ) ≤ ((ω (n+1)).2.2.val:ℝ) := by
    have hh : (P.l:ℝ) ≤ ((ω (n+1)).2.2.val:ℝ)+(roundedTag P.l P.m:ℝ) := by
      exact_mod_cast (show P.l ≤ (ω (n+1)).2.2.val+roundedTag P.l P.m from hs.2)
    linarith
  have hr := P.tag_bounds.2.2.2
  change (roundedTag P.l P.m:ℝ) ≤ (P.l:ℝ)/P.m at hr
  constructor
  · change _ < 1/(P.m:ℝ)
    apply hx.trans_le
    rw [div_le_iff₀ hl]
    convert ha.trans hr using 1; ring
  · change 1-1/(P.m:ℝ) ≤ _
    apply le_trans _ hy
    rw [le_div_iff₀ hl]
    calc
      _ = (P.l:ℝ)-(P.l:ℝ)/P.m := by ring
      _ ≤ (P.l:ℝ)-(roundedTag P.l P.m:ℝ) := sub_le_sub_left hr _
      _ ≤ _ := hb

lemma short_ratio (j : ℕ) (k : ℤ) (hklo : (polynomialWindow j:ℝ)< |(k:ℝ)|) (hkhi : |(k:ℝ)| ≤ blockScale j/4)
    {ω : ActualSamples} (hω : ω∈regularSamples) (htag : ω∈stageTagEvent j) :
    modelF k (lastEndpoint ω)/modelF k (firstEndpoint ω) ≤ Real.exp (-crossingBudget j) := by
  obtain ⟨⟨n,hn,ht⟩,_⟩ := stageTagEvent_margins j hω.1 htag
  have hphase := coordinatePhase_bounds n
  have hblock := blockCoordinates_block j n hn
  rw [hblock] at hphase
  have hm : (0:ℝ)<blockLength j := Nat.cast_pos.mpr (scaleStep j).mpos
  have hK : (0:ℝ)<polynomialWindow j := Nat.cast_pos.mpr (polynomialWindow_pos j)
  have hk : 0< |(k:ℝ)| := hK.trans hklo
  have hlow : 1/(blockLength j:ℝ) ≤ |(k:ℝ)| * coordinatePhase n := by
    calc
      _ = (polynomialWindow j:ℝ)*(1/blockScale j) := by unfold blockScale; field_simp
      _ ≤ |(k:ℝ)| * (1/blockScale j) := mul_le_mul_of_nonneg_right hklo.le (by have := (blockScale_pos j).le; positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left hphase.1.le hk.le
  have hhigh : |(k:ℝ)| * coordinatePhase n<1/2 := by
    calc
      _ < |(k:ℝ)| * (2/blockScale j) := mul_lt_mul_of_pos_left hphase.2 hk
      _ ≤ (blockScale j/4)*(2/blockScale j) := mul_le_mul_of_nonneg_right hkhi (by have := (blockScale_pos j).le; positivity)
      _ = 1/2 := by have := (blockScale_pos j).ne'; field_simp; ring
  have hu := threshold_bounds_of_abs (by positivity : (0:ℝ)<1/(blockLength j:ℝ)) hlow hhigh
  have he := tagged_coordinate_extreme hω ht
  rw [hblock] at he
  have hc := crossing_decay hω k n (he.1.trans_le hu.1) (hu.2.trans he.2)
  apply hc.trans
  apply Real.exp_le_exp.mpr
  change -dropSize (coordinateBlock n) ≤ -crossingBudget j
  rw [hblock]
  exact neg_le_neg (dropSize_ge_budget j)


end CircleSampling

end

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_TailBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CircleSampling

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
open MeasureTheory Set
open scoped BigOperators ENNReal

section
open CircleModel Set
open scoped BigOperators

def coefficientCap (j : ℕ) : ℝ := Real.exp (((polynomialWindow j:ℝ)+1)*(scaleState j).1.E)
end

section
open CircleModel MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators

def futureBad (j : ℕ) (e : Bool) : Set CircleX := ⋃ s : ℕ, ⋃ a : Fin (blockLength (j+1+s)),
  {x | if e then Xi modelFrequency (blocks.equiv ⟨j+1+s,a⟩) x < 2*(polynomialWindow j:ℝ)/blockScale (j+1+s)
  else 1-2*(polynomialWindow j:ℝ)/blockScale (j+1+s) ≤ Xi modelFrequency (blocks.equiv ⟨j+1+s,a⟩) x}
end

section
open MeasureTheory Set Filter CircleCoupling
open scoped Topology ENNReal

def endpointBad (r : CircleX → ℝ) (j : ℕ) (e : Bool) : Set CircleX :=
  futureBad j e ∪ {x | (if e then 1-r x else r x)<1/((j:ℝ)+1)}
def projectionEvent (r : CircleX → ℝ) (j : ℕ) : Set ActualSamples :=
  stageTagEvent j \ (firstEndpoint ⁻¹' endpointBad r j false ∪ lastEndpoint ⁻¹' endpointBad r j true)
end

open MeasureTheory Set CircleCoupling CircleDigits CircleModel
open scoped ENNReal


end CircleSampling

end

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_LaurentCoefficients
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
open MeasureTheory Set
open scoped BigOperators ENNReal

namespace CircleSampling

section

section
open MeasureTheory Set Filter ContinuousCircleWeight
open scoped Topology ENNReal ComplexInnerProductSpace BigOperators

def modelColumn (P : ModelProjectionField) (x : CircleX) : FiberHilbert := P.p x (lp.single 2 0 1)
def modelComplement (P : ModelProjectionField) (x : CircleX) : FiberHilbert := (1-P.p x) (lp.single 2 0 1)
def modelDiagonal (P : ModelProjectionField) (x : CircleX) : ℝ := (modelColumn P x 0).re

def modelTerm (P : ModelProjectionField) (n : ℕ) (v : ℤ) (ω : ActualSamples) : ℂ :=
  (modelF ((n:ℤ)+v) (lastEndpoint ω)/modelF v (firstEndpoint ω):ℝ)*modelColumn P (firstEndpoint ω) v*starRingEnd ℂ (modelComplement P (lastEndpoint ω) ((n:ℤ)+v))
def modelRetained (P : ModelProjectionField) (j n : ℕ) (ω : ActualSamples) : ℂ :=
  ∑ v∈retainedIndices (polynomialWindow j) n,modelTerm P n v ω

def modelCoefficientPair (P : ModelProjectionField) (j : ℕ) (ω : ActualSamples) : CoefficientPair (polynomialWindow j) :=
  (laurentArray (polynomialWindow j) (fun v => (1/modelF v (firstEndpoint ω):ℝ)*modelColumn P (firstEndpoint ω) v),
   laurentArray (polynomialWindow j) (fun v => (modelF (-v) (lastEndpoint ω):ℂ)*starRingEnd ℂ (modelComplement P (lastEndpoint ω) (-v))))
end

open MeasureTheory Set Filter ContinuousCircleWeight
open scoped ENNReal ComplexInnerProductSpace BigOperators

end

open MeasureTheory Set Filter CircleCoupling CircleDigits
open scoped ENNReal

lemma all_masks (j : ℕ) (k : ℤ) (hk : (polynomialWindow j:ℝ)< |(k:ℝ)|) :
    ∃ H₁ H₂ : Set ActualSamples,MeasurableSet H₁ ∧ MeasurableSet H₂ ∧
      Measure.map firstEndpoint ((actualSystem.probability (stageTagged j)).restrict H₁) ≤ ENNReal.ofReal (Real.exp (-crossingBudget j/400)) • Measure.map firstEndpoint (actualSystem.probability (stageTagged j)) ∧
      Measure.map lastEndpoint ((actualSystem.probability (stageTagged j)).restrict H₂) ≤ ENNReal.ofReal (Real.exp (-crossingBudget j/400)) • Measure.map lastEndpoint (actualSystem.probability (stageTagged j)) ∧
      ∀ ω∈regularSamples,ω∈stageTagEvent j → ω∉H₁ → ω∉H₂ → modelF k (lastEndpoint ω)/modelF k (firstEndpoint ω) ≤ Real.exp (-crossingBudget j) := by
  by_cases hh : blockScale j/4< |(k:ℝ)|
  · obtain ⟨H₁,H₂,hm₁,hm₂,hd₁,hd₂,hc⟩ := large_masks j k hh
    exact ⟨H₁,H₂,hm₁,hm₂,hd₁,hd₂,fun ω hω _ h₁ h₂ => hc ω hω h₁ h₂⟩
  · refine ⟨∅,∅,MeasurableSet.empty,MeasurableSet.empty,by simp; exact bot_le,by simp; exact bot_le,?_⟩
    exact fun ω hω ht _ _ => short_ratio j k hk (le_of_not_gt hh) hω ht

def longIndex (j n : ℕ) (v : ℤ) : ℤ := if (polynomialWindow j:ℤ)< |v| then v else (n:ℤ)+v
lemma longIndex_long (j n : ℕ) (v : ℤ) (hv : v∉ContinuousCircleWeight.retainedIndices (polynomialWindow j) n) :
    (polynomialWindow j:ℝ)< |((longIndex j n v):ℝ)| := by
  rw [ContinuousCircleWeight.mem_retainedIndices] at hv
  have hh : (polynomialWindow j:ℤ)< |longIndex j n v| := by
    unfold longIndex
    split_ifs with h
    · exact h
    · push Not at hv
      exact hv (le_of_not_gt h)
  exact_mod_cast hh
end CircleSampling

end

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_Convolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CircleSampling

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
open MeasureTheory Set Filter ContinuousCircleWeight
open scoped ENNReal BigOperators

structure ConvolutionMasks (j n : ℕ) where
  left : ℤ → Set ActualSamples
  right : ℤ → Set ActualSamples
  left_measurable : ∀ v,MeasurableSet (left v)
  right_measurable : ∀ v,MeasurableSet (right v)
  left_dom : ∀ v,Measure.map firstEndpoint ((actualSystem.probability (stageTagged j)).restrict (left v)) ≤
    ENNReal.ofReal (Real.exp (-crossingBudget j/400)) • Measure.map firstEndpoint (actualSystem.probability (stageTagged j))
  right_dom : ∀ v,Measure.map lastEndpoint ((actualSystem.probability (stageTagged j)).restrict (right v)) ≤
    ENNReal.ofReal (Real.exp (-crossingBudget j/400)) • Measure.map lastEndpoint (actualSystem.probability (stageTagged j))
  decay : ∀ v,v∉retainedIndices (polynomialWindow j) n → ∀ ω∈regularSamples,ω∈stageTagEvent j →
    ω∉left v → ω∉right v → modelF (longIndex j n v) (lastEndpoint ω)/modelF (longIndex j n v) (firstEndpoint ω) ≤ Real.exp (-crossingBudget j)

lemma convolutionMasks_nonempty (j n : ℕ) : Nonempty (ConvolutionMasks j n) := by
  classical
  have hex (v : ℤ) : ∃ H₁ H₂ : Set ActualSamples,MeasurableSet H₁ ∧ MeasurableSet H₂ ∧
      Measure.map firstEndpoint ((actualSystem.probability (stageTagged j)).restrict H₁) ≤ ENNReal.ofReal (Real.exp (-crossingBudget j/400)) • Measure.map firstEndpoint (actualSystem.probability (stageTagged j)) ∧
      Measure.map lastEndpoint ((actualSystem.probability (stageTagged j)).restrict H₂) ≤ ENNReal.ofReal (Real.exp (-crossingBudget j/400)) • Measure.map lastEndpoint (actualSystem.probability (stageTagged j)) ∧
      (v∉retainedIndices (polynomialWindow j) n → ∀ ω∈regularSamples,ω∈stageTagEvent j → ω∉H₁ → ω∉H₂ → modelF (longIndex j n v) (lastEndpoint ω)/modelF (longIndex j n v) (firstEndpoint ω) ≤ Real.exp (-crossingBudget j)) := by
    by_cases hv : v∈retainedIndices (polynomialWindow j) n
    · exact ⟨∅,∅,MeasurableSet.empty,MeasurableSet.empty,by simp; exact bot_le,by simp; exact bot_le,fun h => False.elim (h hv)⟩
    · obtain ⟨A,B,hA,hB,hdA,hdB,hc⟩ := all_masks j _ (longIndex_long j n v hv)
      exact ⟨A,B,hA,hB,hdA,hdB,fun _ => hc⟩
  choose A B hA hB hdA hdB hc using hex
  exact ⟨⟨A,B,hA,hB,hdA,hdB,hc⟩⟩
def convolutionMasks (j n : ℕ) : ConvolutionMasks j n := Classical.choice (convolutionMasks_nonempty j n)

end

open MeasureTheory Set Filter ContinuousCircleWeight
open scoped ENNReal BigOperators Topology

def convolutionError (j : ℕ) : ℝ := Real.exp (-crossingBudget j)+2*Real.exp (-crossingBudget j/800)


end CircleSampling

end

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_ContinuousWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ContinuousCircleWeight

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
open MeasureTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Set
open scoped ENNReal NNReal BigOperators

open MeasureTheory Filter Set
open scoped Topology ENNReal BigOperators

lemma concentratedWeight_continuousAt_off {X : Type uX} [TopologicalSpace X] [T1Space X]
    (H : ℕ → X → ℝ) (z : X) (hc : ∀ i, Continuous (H i))
    (hlocal : LocallyFiniteOff H z) {x : X} (hx : x ≠ z) :
    ContinuousAt (concentratedWeight H z) x := by
  classical
  obtain ⟨s,hs⟩ := hlocal x hx
  have he : concentratedWeight H z =ᶠ[𝓝 x] (fun y ↦ Real.exp (-∑ i ∈ s, H i y)) := by
    filter_upwards [hs, isOpen_compl_singleton.mem_nhds hx] with y hy hyz
    change y ≠ z at hyz
    rw [concentratedWeight, ite_eq_right hyz]
    congr 2
    exact tsum_eq_sum (fun i hi ↦ hy i hi)
  exact ((continuous_finsetSum s (fun i _ ↦ hc i)).neg.rexp.continuousAt).congr_of_eventuallyEq he

lemma concentratedWeight_le_finite {X : Type uX} [TopologicalSpace X]
    (H : ℕ → X → ℝ) (z : X) (hH : ∀ i x, 0 ≤ H i x)
    (hlocal : LocallyFiniteOff H z) (s : Finset ℕ) (x : X) :
    concentratedWeight H z x ≤ Real.exp (-∑ i ∈ s, H i x) := by
  classical
  by_cases hx : x = z
  · simp only [concentratedWeight, ite_eq_left hx]
    exact (Real.exp_pos _).le
  rw [concentratedWeight, ite_eq_right hx]
  apply Real.exp_le_exp.mpr
  apply _root_.neg_le_neg
  exact Summable.sum_le_tsum s (fun i _ ↦ hH i x)
    (summable_of_hasFiniteSupport (finite_support_of_locallyFiniteOff H z hlocal hx))

theorem continuous_concentratedWeight {X : Type uX} [TopologicalSpace X] [T1Space X]
    (H : ℕ → X → ℝ) (z : X) (hc : ∀ i, Continuous (H i)) (hH : ∀ i x, 0 ≤ H i x)
    (hlocal : LocallyFiniteOff H z)
    (hdiv : ∀ B : ℝ, ∃ s : Finset ℕ, B < ∑ i ∈ s, H i z) :
    Continuous (concentratedWeight H z) := by
  classical
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x = z
  · subst x
    rw [ContinuousAt, Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨s,hs⟩ := hdiv (-Real.log ε)
    have he : Real.exp (-∑ i ∈ s, H i z) < ε := by
      rw [← Real.exp_log hε]
      exact Real.exp_lt_exp.mpr (by linarith)
    have hev : ∀ᶠ x in 𝓝 z, Real.exp (-∑ i ∈ s, H i x) < ε :=
      ((continuous_finsetSum s (fun i _ ↦ hc i)).neg.rexp.continuousAt).eventually (gt_mem_nhds he)
    filter_upwards [hev] with x hx
    rw [concentratedWeight_self, dist_zero_right, Real.norm_eq_abs]
    rw [abs_of_nonneg (concentratedWeight_bounds H z hH x).1]
    exact (concentratedWeight_le_finite H z hH hlocal s x).trans_lt hx
  · exact concentratedWeight_continuousAt_off H z hc hlocal hx



end ContinuousCircleWeight

end

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_LogarithmicDrops
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CircleSampling

universe uι

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
open MeasureTheory Filter Set
open scoped Topology ENNReal BigOperators

section
open CircleModel CircleRounding CircleConcentration ContinuousCircleWeight
open Set Filter MeasureTheory
open scoped Topology BigOperators ENNReal

def roundingWidth (j : ℕ) : ℝ := 1/(10*(blockLength j:ℝ)*polynomialWindow j)
lemma roundingWidth_pos (j : ℕ) : 0<roundingWidth j := by
  have hm : 0<(blockLength j:ℝ) := Nat.cast_pos.mpr (scaleStep j).mpos
  have hK : 0<(polynomialWindow j:ℝ) := Nat.cast_pos.mpr (polynomialWindow_pos j)
  unfold roundingWidth; positivity
lemma roundingWidth_lt_one (j : ℕ) : roundingWidth j<1 := by
  have hm : (1:ℝ)≤blockLength j := by exact_mod_cast (scaleStep j).mpos
  have hK : (1:ℝ)≤polynomialWindow j := by exact_mod_cast polynomialWindow_pos j
  rw [roundingWidth,div_lt_one (by positivity)]
  nlinarith
lemma phase_width_bounds (j : ℕ) (i : Fin (blockLength j)) :
    roundingWidth j≤coordinatePhase (blocks.equiv ⟨j,i⟩) ∧ coordinatePhase (blocks.equiv ⟨j,i⟩)≤1-roundingWidth j := by
  have hm : (200:ℝ)≤blockLength j := by exact_mod_cast blockLength_ge j
  have hK : (1:ℝ)≤polynomialWindow j := by exact_mod_cast polynomialWindow_pos j
  have hd : 0<(blockLength j:ℝ)*polynomialWindow j := by positivity
  have hp := coordinatePhase_block j i
  have he : roundingWidth j=(1/10:ℝ)/((blockLength j:ℝ)*polynomialWindow j) := by unfold roundingWidth; ring
  rw [he]
  constructor
  · exact (div_le_div_of_nonneg_right (by norm_num) hd.le).trans hp.1.le
  · have hh : 2/((blockLength j:ℝ)*polynomialWindow j)+(1/10:ℝ)/((blockLength j:ℝ)*polynomialWindow j)≤1 := by
      rw [←add_div,div_le_one hd]; nlinarith
    linarith [hp.2]

def smoothDrop (j : ℕ) (i : Fin (blockLength j)) (x : CircleModel.CircleX) : ℝ :=
  roundedDrop (roundingWidth j) (coordinatePhase (blocks.equiv ⟨j,i⟩)) (dropSize j)
    (modelFrequency (blocks.equiv ⟨j,i⟩) • x)
def smoothCorrection (j : ℕ) (i : Fin (blockLength j)) (x : CircleModel.CircleX) : ℝ :=
  correction (roundingWidth j) (dropSize j) (modelFrequency (blocks.equiv ⟨j,i⟩) • x)
def integerDrop (j : ℕ) (i : Fin (blockLength j)) (x : CircleModel.CircleX) : ℝ :=
  dropSize j * (floorTerm modelFrequency modelAngle 1 x (blocks.equiv ⟨j,i⟩):ℝ)
def concentratedDrop (j : ℕ) (i : Fin (blockLength j)) := movedDrop modelAngle j (smoothDrop j i)
def totalCorrection (j : ℕ) (i : Fin (blockLength j)) (x : CircleModel.CircleX) : ℝ :=
  smoothCorrection j i x+moveCorrection modelAngle j (smoothDrop j i) x

def blockH (j : ℕ) (x : CircleModel.CircleX) : ℝ := ∑ i,concentratedDrop j i x
def blockG (j : ℕ) (x : CircleModel.CircleX) : ℝ := ∑ i,integerDrop j i x
def blockW (j : ℕ) (x : CircleModel.CircleX) : ℝ := ∑ i,totalCorrection j i x

lemma smoothDrop_continuous (j : ℕ) (i : Fin (blockLength j)) : Continuous (smoothDrop j i) :=
  (roundedDrop_continuous (roundingWidth_pos j) (roundingWidth_lt_one j) _ _).comp (continuous_id.nsmul _)
lemma smoothDrop_nonneg (j : ℕ) (i : Fin (blockLength j)) (x : CircleModel.CircleX) : 0 ≤ smoothDrop j i x :=
  roundedDrop_nonneg (roundingWidth_pos j) (roundingWidth_lt_one j) (coordinatePhase_pos _).le
    (Int.fract_lt_one _) (dropSize_nonneg j) _
lemma concentratedDrop_continuous (j : ℕ) (i : Fin (blockLength j)) : Continuous (concentratedDrop j i) :=
  movedDrop_continuous _ _ (smoothDrop_continuous j i)
lemma concentratedDrop_nonneg (j : ℕ) (i : Fin (blockLength j)) (x : CircleModel.CircleX) : 0 ≤ concentratedDrop j i x :=
  movedDrop_nonneg _ _ (smoothDrop_nonneg j i) x
lemma blockH_continuous (j : ℕ) : Continuous (blockH j) := continuous_finsetSum _ (fun i _ => concentratedDrop_continuous j i)
lemma blockH_nonneg (j : ℕ) (x : CircleModel.CircleX) : 0 ≤ blockH j x := Finset.sum_nonneg (fun i _ => concentratedDrop_nonneg j i x)
lemma blockH_support (j : ℕ) (x : CircleModel.CircleX) (hx : supportRadius modelAngle j≤dist x 0) : blockH j x=0 :=
  Finset.sum_eq_zero (fun _i _ => movedDrop_zero_off _ _ _ _ hx)
lemma blockH_locallyFinite : LocallyFiniteOff blockH 0 := by
  apply locallyFiniteOff_of_shrinking_supports blockH 0 (supportRadius modelAngle) _ blockH_support
  apply supportRadius_tendsto
  rw [←denseRange_zsmul_iff_nsmul]
  simpa only [div_one,modelAngle] using (AddCircle.denseRange_zsmul_coe_iff (p := (1:ℝ))).mpr (by simpa using parameterAngle_spec.2.2.1)

lemma smoothDrop_zero (j : ℕ) (i : Fin (blockLength j)) : smoothDrop j i 0=dropSize j/2 := by
  unfold smoothDrop
  rw [smul_zero]
  exact roundedDrop_zero (roundingWidth_pos j) (roundingWidth_lt_one j) (phase_width_bounds j i).1 (phase_width_bounds j i).2 _
lemma blockH_zero_lower (j : ℕ) : (blockLength j:ℝ)*dropSize j/(2*((j:ℝ)+1))≤blockH j 0 := by
  calc
    _ = ∑ _i : Fin (blockLength j),(dropSize j/2)/((j:ℝ)+1) := by simp; field_simp
    _ ≤ _ := Finset.sum_le_sum (fun i _ => by
      change _ ≤ movedDrop modelAngle j (smoothDrop j i) 0
      rw [←smoothDrop_zero j i]
      exact movedDrop_zero_lower modelAngle j (smoothDrop_nonneg j i))

end
open CircleModel CircleRounding CircleConcentration ContinuousCircleWeight
open Set Filter MeasureTheory
open scoped Topology BigOperators ENNReal


end CircleSampling

end

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_Main
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
open MeasureTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory Filter Set
open scoped Topology ENNReal BigOperators
namespace CircleSampling

section
open CircleModel CircleRounding CircleConcentration ContinuousCircleWeight
open Set Filter MeasureTheory
open scoped Topology BigOperators ENNReal

lemma blockLength_ge_index (j : ℕ) : j+1≤blockLength j := by
  induction j with
  | zero => exact (by norm_num : 1≤200).trans (blockLength_ge 0)
  | succ j ih => exact (by omega : j+1+1 ≤ blockLength j+1).trans (blockLength_strictMono (Nat.lt_succ_self j))
lemma blockH_zero_half (j : ℕ) : (1/2:ℝ)≤blockH j 0 := by
  have hm : (j:ℝ)+1≤blockLength j := by exact_mod_cast blockLength_ge_index j
  have hK : (1:ℝ)≤polynomialWindow j := by exact_mod_cast polynomialWindow_pos j
  have hc : 1≤dropSize j := by nlinarith [dropSize_ge_window_sq j]
  have hj : 0<(j:ℝ)+1 := by positivity
  calc
    _ ≤ (blockLength j:ℝ)*dropSize j/(2*((j:ℝ)+1)) := by
      apply (le_div_iff₀ (by positivity)).mpr
      nlinarith [mul_le_mul hm hc (by positivity) (by positivity)]
    _ ≤ _ := blockH_zero_lower j
lemma blockH_diverges_zero : ∀ B : ℝ, ∃ s : Finset ℕ,B<∑ j∈s,blockH j 0 := by
  intro B
  obtain ⟨N,hN⟩ := exists_nat_gt (2*B)
  refine ⟨Finset.range N,?_⟩
  calc
    B < (N:ℝ)*(1/2) := by linarith
    _ = ∑ _j∈Finset.range N,(1/2:ℝ) := by simp
    _ ≤ _ := Finset.sum_le_sum (fun j _ => blockH_zero_half j)

def finalWeight : C(CircleModel.CircleX,ℝ) :=
  ⟨concentratedWeight blockH 0,continuous_concentratedWeight blockH 0 blockH_continuous blockH_nonneg blockH_locallyFinite blockH_diverges_zero⟩
end

open MeasureTheory Set Filter ContinuousCircleWeight
open scoped ComplexInnerProductSpace ENNReal

def modelBorel : RealBorel where
  f := modelWeight
  measurable := modelF_measurable 1
  bound := 1
  norm_le x := by
    simpa only [Real.norm_eq_abs,abs_of_pos (modelWeight_bounds x).1,NNReal.coe_one] using (modelWeight_bounds x).2

end CircleSampling

end

end OAI
end


