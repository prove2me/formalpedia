-- Prove2me | Definitions.Def_OAIQ3Ho002
-- name    : OAIQ3Ho002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T05:05:46.390602+00:00
-- url     : https://prove2.me/theorems/66603536-0bcd-4e80-82f0-2600caeaa9c0
-- title:
--   Definitions bundle OAIQ3Ho002 of the split of OpenAI, The hot spots conjecture for simply connected planar domains
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.StrictHotSpots.main_theorem`, carved from OpenAI's openai/math development (OpenAI, *The hot spots conjecture for simply connected planar domains*, OpenAI Math Release, September 24, 2026, result family 369, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 73 declarations of OpenAI's Lean: 14 definitions, 2 instances and 57 theorems. The definitions and types are `OAI.StrictHotSpots.Conformal.ClosedDiskChart.circleBoundaryHomeomorph`, `OAI.StrictHotSpots.Conformal.ClosedDiskChart.datumCorrection`, `OAI.StrictHotSpots.H10.greenOperator`, `OAI.StrictHotSpots.H10.weightedValue`, `OAI.StrictHotSpots.Hodge.e`, `OAI.StrictHotSpots.Hodge.eigenGradientField`, `OAI.StrictHotSpots.PhysicalHelmholtz.incl`, `OAI.StrictHotSpots.PlaneGreen.boundarySolution`, `OAI.StrictHotSpots.SubcriticalExtension.extension`, `OAI.StrictHotSpots.SubcriticalExtension.observe`, `OAI.StrictHotSpots.SubcriticalExtension.solve`, `OAI.StrictHotSpots.ambientSmooth`, `OAI.StrictHotSpots.planeApproxBump`, `OAI.StrictHotSpots.smoothTestToH10`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/HotSpots, in whole or in part: `HotSpots_BoundaryEnergy`, `HotSpots_ClosedChart`, `HotSpots_ClosedSolution`, `HotSpots_Conformal`, `HotSpots_DouglasEnergy`, `HotSpots_GreenOperator`, `HotSpots_GreenSolution`, `HotSpots_Multiplier`, `HotSpots_Poisson`, `HotSpots_Potentials`, `HotSpots_Sobolev`, `HotSpots_Trace`, `HotSpots_Variational`, `HotSpots_VectorEnergy`.
--
--   **Imports.** It imports the published bundle `Def_HotSpots`; the bundles `OAIQ3Ho000` and `OAIQ3Ho001` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ3Ho004`; the statements `OAI_StrictHotSpots_Conformal_ClosedDiskChart_lipschitzMultipliedGradient_null`, `OAI.StrictHotSpots.Conformal.ClosedDiskChart.subcritical`, `OAI.StrictHotSpots.PlaneGreen.boundarySolution_energy`, `OAI.StrictHotSpots.PlaneGreen.full_boundary_hilbert_embedding` and `OAI.StrictHotSpots.PlaneGreen.reciprocal_compact_support`; the proofs of `OAI.StrictHotSpots.Conformal.ClosedDiskChart.eq_zero_of_boundary_closedGradient`, `OAI_StrictHotSpots_Conformal_ClosedDiskChart_lipschitzMultipliedGradient_null`, `OAI.StrictHotSpots.H10.subcritical` and `OAI.StrictHotSpots.InteriorBoundarySign.exists_boundary_pos`.
-- source:
--   OpenAI, The hot spots conjecture for simply connected planar domains, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 369; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Strict-hot-spots-and-absence-of-interior-critical-points-on-smooth-simply-connected-planar-domains-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/HotSpots at commit adc7f12

import Mathlib
import Definitions.Def_HotSpots
import Definitions.Def_OAIQ3Ho000
import Definitions.Def_OAIQ3Ho001

section
-- module Solutions.OAIQ3_Hot.HotSpots_Sobolev
attribute [-instance] _root_.OAI.StrictHotSpots.Douglas.haar_nullSingleton _root_.OAI.StrictHotSpots.N1.innerProductSpace _root_.OAI.StrictHotSpots.PlaneGreen.diskFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section DouglasLipschitzBase
noncomputable section
section FullBoundaryCombinedLayer
section WeightedLayer



open Set MeasureTheory
open scoped ContDiff InnerProductSpace ENNReal NNReal
namespace StrictHotSpots


namespace H1
variable {Ω : Set Plane}

lemma grad_toH1 {v : Plane → ℝ} {g : Plane → Plane} (h : HasH1Gradient Ω v g) :
    grad h.toH1 = h.2.1.toLp g := rfl

end H1


lemma smoothTestToH1_value_norm {Ω : Set Plane} (hΩ : IsOpen Ω)
    (f : smoothTestSpace Ω) :
    ‖H1.value (smoothTestToH1 hΩ f)‖ =
      (eLpNorm (f : Plane → ℝ) 2 (volume.restrict Ω)).toReal := by
  rw [show smoothTestToH1 hΩ f =
    (HasH1Gradient.test hΩ f.property.1 f.property.2.1).toH1 from rfl,
    H1.value_toH1]
  exact Lp.norm_toLp _ _

lemma smoothTestToH1_grad_norm {Ω : Set Plane} (hΩ : IsOpen Ω)
    (f : smoothTestSpace Ω) :
    ‖H1.grad (smoothTestToH1 hΩ f)‖ =
      (eLpNorm (gradient (f : Plane → ℝ)) 2 (volume.restrict Ω)).toReal := by
  rw [show smoothTestToH1 hΩ f =
    (HasH1Gradient.test hΩ f.property.1 f.property.2.1).toH1 from rfl,
    H1.grad_toH1]
  exact Lp.norm_toLp _ _


instance H10.normedAddCommGroup {Ω : Set Plane} (hΩ : IsOpen Ω) :
    NormedAddCommGroup (H10 hΩ) := (h10Submodule hΩ).normedAddCommGroup

instance H10.completeSpace {Ω : Set Plane} (hΩ : IsOpen Ω) : CompleteSpace (H10 hΩ) :=
  (LinearMap.range (smoothTestToH1 hΩ)).isClosed_topologicalClosure.completeSpace_coe



lemma test_poincare_real {Ω : Set Plane} (hb : Bornology.IsBounded Ω)
    {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hs : tsupport f ⊆ Ω) :
    (eLpNorm f 2 (volume.restrict Ω)).toReal ≤
      ((eLpNormLESNormFDerivOneConst (volume : Measure Plane) 2 : ℝ≥0∞) *
      (volume Ω) ^ (1 / 2 : ℝ)).toReal *
      (eLpNorm (gradient f) 2 (volume.restrict Ω)).toReal := by
  have hA : (eLpNormLESNormFDerivOneConst (volume : Measure Plane) 2 : ℝ≥0∞) ≠ (∞ : ℝ≥0∞) :=
    ENNReal.coe_ne_top
  have hB : (volume Ω) ^ (1 / 2 : ℝ) ≠ (∞ : ℝ≥0∞) :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) hb.measure_lt_top.ne
  have hg := test_gradient_memLp (Ω := Ω) hf hc
  have h := ENNReal.toReal_mono
    (ENNReal.mul_ne_top (ENNReal.mul_ne_top hA hB) hg.eLpNorm_ne_top)
    (test_poincare_ennreal hf hc hs)
  rwa [ENNReal.toReal_mul] at h



lemma smoothTest_poincare {Ω : Set Plane} (hΩ : IsOpen Ω)
    (hb : Bornology.IsBounded Ω) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : smoothTestSpace Ω,
      ‖H1.value (smoothTestToH1 hΩ f)‖ ≤ C * ‖H1.grad (smoothTestToH1 hΩ f)‖ := by
  let A : ℝ≥0∞ := eLpNormLESNormFDerivOneConst (volume : Measure Plane) 2
  let B : ℝ≥0∞ := (volume Ω) ^ (1 / 2 : ℝ)
  let C := (A * B).toReal + 1
  refine ⟨C, add_pos_of_nonneg_of_pos ENNReal.toReal_nonneg zero_lt_one, ?_⟩
  intro f
  have hreal := test_poincare_real hb f.property.1 f.property.2.1 f.property.2.2
  rw [smoothTestToH1_value_norm, smoothTestToH1_grad_norm]
  apply hreal.trans
  exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) ENNReal.toReal_nonneg

namespace H10
variable {Ω : Set Plane} (hΩ : IsOpen Ω)

lemma norm_sq (u : H10 hΩ) : ‖u‖ ^ 2 = ‖value hΩ u‖ ^ 2 + ‖grad hΩ u‖ ^ 2 :=
  H1.norm_sq u.val

lemma poincare (hb : Bornology.IsBounded Ω) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : H10 hΩ, ‖value hΩ u‖ ≤ C * ‖grad hΩ u‖ := by
  obtain ⟨C, hC, htest⟩ := smoothTest_poincare hΩ hb
  have hsub : ∀ v ∈ ((smoothTestToH1 hΩ).range : Set (H1 Ω)),
      ‖H1.value v‖ ≤ C * ‖H1.grad v‖ := by
    rintro v ⟨f, rfl⟩
    exact htest f
  refine ⟨C, hC, fun u => ?_⟩
  exact norm_bound_on_closure H1.value H1.grad
    H1.value.continuous H1.grad.continuous C hsub u.property


lemma energy_coercive (hb : Bornology.IsBounded Ω) :
    @IsCoercive (H10 hΩ) (H10.normedAddCommGroup hΩ).toSeminormedAddCommGroup
      (H10.innerProductSpace hΩ).toNormedSpace (energy hΩ) := by
  obtain ⟨C, hC, hP⟩ := poincare hΩ hb
  have hD : 0 < C ^ 2 + 1 := by positivity
  refine ⟨1 / (C ^ 2 + 1), by positivity, fun u => ?_⟩
  have hsq := (sq_le_sq₀ (norm_nonneg (value hΩ u))
    (mul_nonneg hC.le (norm_nonneg (grad hΩ u)))).mpr (hP u)
  have hbound : ‖u‖ ^ 2 ≤ (C ^ 2 + 1) * ‖grad hΩ u‖ ^ 2 := by
    rw [norm_sq hΩ]
    nlinarith
  calc
    (1 / (C ^ 2 + 1)) * ‖u‖ * ‖u‖ = ‖u‖ ^ 2 / (C ^ 2 + 1) := by ring
    _ ≤ ‖grad hΩ u‖ ^ 2 := (div_le_iff₀ hD).mpr (by simpa [mul_comm] using hbound)
    _ = energy hΩ u u := (real_inner_self_eq_norm_sq _).symm



end H10
end StrictHotSpots




open Set Filter MeasureTheory InnerProductSpace NormedSpace
open scoped Topology ContDiff

namespace StrictHotSpots
namespace H1
lemma tendsto_of_value_grad {Ω : Set Plane} {ι : Type*} {l : Filter ι}
    {f : ι → H1 Ω} {g : H1 Ω}
    (hv : Tendsto (fun n => value (f n)) l (𝓝 (value g)))
    (hg : Tendsto (fun n => grad (f n)) l (𝓝 (grad g))) :
    Tendsto f l (𝓝 g) := by
  have h1 := (tendsto_iff_norm_sub_tendsto_zero.mp hv).pow 2
  have h2 := (tendsto_iff_norm_sub_tendsto_zero.mp hg).pow 2
  have hsq : Tendsto (fun n => ‖f n-g‖ ^ 2) l (𝓝 0) := by
    simpa only [norm_sq, map_sub, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_add] using h1.add h2
  have hr := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hr
end H1

end StrictHotSpots

open scoped Laplacian







end WeightedLayer

end FullBoundaryCombinedLayer

end

end DouglasLipschitzBase

end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_GreenOperator
attribute [-instance] _root_.OAI.StrictHotSpots.Douglas.haar_nullSingleton _root_.OAI.StrictHotSpots.N1.innerProductSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section DouglasLipschitzBase
noncomputable section
section FullBoundaryCombinedLayer
section WeightedLayer
open Set MeasureTheory
open scoped ContDiff InnerProductSpace ENNReal NNReal
open Set Filter MeasureTheory InnerProductSpace NormedSpace
open scoped Topology ContDiff
open scoped Laplacian
open Set MeasureTheory Filter InnerProductSpace Bornology
open scoped Topology Laplacian ContDiff RealInnerProductSpace
open scoped Convolution
open Set MeasureTheory Filter InnerProductSpace
open scoped Topology ContDiff Convolution Laplacian
open InnerProductSpace
open scoped Laplacian ContDiff

open Filter Set
open scoped Topology




open MeasureTheory Filter
open scoped Topology ENNReal





open MeasureTheory Filter Metric Set
open scoped Topology ENNReal


open MeasureTheory Filter Metric Set
open scoped Topology ENNReal


open MeasureTheory Filter Metric Set
open scoped Topology ENNReal



open MeasureTheory Filter
open scoped ENNReal Topology InnerProductSpace



open MeasureTheory Filter InnerProductSpace
open scoped ENNReal Topology







open scoped InnerProductSpace


open MeasureTheory Set Filter
open scoped ENNReal Topology InnerProductSpace


open MeasureTheory
open scoped InnerProductSpace ENNReal
namespace StrictHotSpots.H10
variable {Ω : Set Plane} (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
variable {ν : Measure Plane} {C : ℝ≥0∞} (hC : C ≠ (∞ : ℝ≥0∞))
  (hν : ν ≤ C • volume.restrict Ω)


def weightedValue : H10 hΩ →L[ℝ] Lp ℝ 2 ν :=
  (Lp.LpToLpOfMeasureLeSMul hC hν).comp (value hΩ)



def greenOperator : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν :=
  @DirichletOperator.green (H10 hΩ) (Lp ℝ 2 ν)
    (H10.normedAddCommGroup hΩ) (H10.innerProductSpace hΩ) (H10.completeSpace hΩ)
    inferInstance inferInstance inferInstance
    (energy hΩ) (energy_coercive hΩ hb) (weightedValue hΩ hC hν)

end StrictHotSpots.H10


open MeasureTheory Filter
open scoped ENNReal InnerProductSpace

end WeightedLayer


end FullBoundaryCombinedLayer

end

end DouglasLipschitzBase

end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_Variational
attribute [-instance] _root_.OAI.StrictHotSpots.N1.innerProductSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section DouglasLipschitzBase
noncomputable section

section H10InclusionCombinedLayer
open Set MeasureTheory Filter
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots

def smoothTestToH10 {Ω : Set Plane} (hΩ : IsOpen Ω) : smoothTestSpace Ω →ₗ[ℝ] H10 hΩ :=
  (smoothTestToH1 hΩ).codRestrict (h10Submodule hΩ)
    (fun f => Submodule.le_topologicalClosure _ (LinearMap.mem_range_self _ f))

end StrictHotSpots
end H10InclusionCombinedLayer


end

end DouglasLipschitzBase

end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_Trace
attribute [-instance] _root_.OAI.StrictHotSpots.N1.innerProductSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section DouglasLipschitzBase
noncomputable section
section NodalSmoothingCombinedLayer

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff
namespace StrictHotSpots.Nodal

lemma cutoff_norm_le (n : ℕ) (t : ℝ) : ‖cutoff n t‖ ≤ ‖t‖ := by
  change ‖t * Real.smoothTransition (((n:ℝ)+1)*t-1)‖ ≤ ‖t‖
  rw [norm_mul,Real.norm_of_nonneg (Real.smoothTransition.nonneg _)]
  exact mul_le_of_le_one_right (norm_nonneg t) (Real.smoothTransition.le_one _)

end StrictHotSpots.Nodal
end NodalSmoothingCombinedLayer

section BoundarySignLimitsCombinedLayer
open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace StrictHotSpots.Nodal
lemma cutoff_nonpos (n : ℕ) {t : ℝ} (h : t ≤ 0) : cutoff n t = 0 :=
  cutoff_zero n (lt_of_le_of_lt h (by positivity))
lemma cutoff_deriv_nonpos (n : ℕ) {t : ℝ} (h : t ≤ 0) : deriv (cutoff n) t = 0 := by
  have he : cutoff n =ᶠ[𝓝 t] (fun _ => (0:ℝ)) := by
    filter_upwards [gt_mem_nhds (show t < 1 / ((n:ℝ)+1) from lt_of_le_of_lt h (by positivity))] with y hy
    exact cutoff_zero n hy
  rw [he.deriv_eq]
  simp
lemma cutoff_tendsto (t : ℝ) : Tendsto (fun n => cutoff n t) atTop (𝓝 (if 0 < t then t else 0)) := by
  by_cases ht : 0 < t
  · rw [ite_eq_left ht]
    exact tendsto_const_nhds.congr' ((cutoff_eventually_eq ht).mono fun _ h => h.1.symm)
  · simp only [ite_eq_right ht,cutoff_nonpos _ (le_of_not_gt ht)]
    exact tendsto_const_nhds
lemma cutoff_deriv_tendsto (t : ℝ) :
    Tendsto (fun n => deriv (cutoff n) t) atTop (𝓝 (if 0 < t then (1:ℝ) else 0)) := by
  by_cases ht : 0 < t
  · rw [ite_eq_left ht]
    exact tendsto_const_nhds.congr' ((cutoff_eventually_eq ht).mono fun _ h => h.2.symm)
  · simp only [ite_eq_right ht,cutoff_deriv_nonpos _ (le_of_not_gt ht)]
    exact tendsto_const_nhds
end StrictHotSpots.Nodal
end BoundarySignLimitsCombinedLayer

section NodalRestrictionWeightedCombinedLayer

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff InnerProductSpace
namespace StrictHotSpots.Nodal

variable {Ω U : Set Plane} {u : Plane → ℝ}

lemma cutoff_memLp (hU : IsOpen U) (hu : HasH1Gradient Ω u (gradient u)) (n : ℕ) :
    MemLp (U.indicator (fun x => cutoff n (u x))) 2 (volume.restrict Ω) := by
  apply hu.1.mono
    (((cutoff_contDiff n).continuous.comp_aestronglyMeasurable hu.1.aestronglyMeasurable).indicator hU.measurableSet)
  exact Eventually.of_forall fun x => by
    by_cases hx : x ∈ U
    · simpa only [indicator_of_mem hx] using cutoff_norm_le n (u x)
    · simp only [indicator_of_notMem hx,norm_zero]; exact norm_nonneg _

lemma cutoff_hasH1Gradient (hΩ : IsOpen Ω) (hu : ContDiffOn ℝ ∞ u Ω)
    (hH : HasH1Gradient Ω u (gradient u))
    (hU : IsOpen U) (hf : ∀ x ∈ frontier U ∩ Ω, u x = 0) (n : ℕ) :
    HasH1Gradient Ω (U.indicator (fun x => cutoff n (u x)))
      (U.indicator (fun x => deriv (cutoff n) (u x) • gradient u x)) := by
  have heq : gradient (U.indicator (fun x => cutoff n (u x))) =ᵐ[volume.restrict Ω]
      U.indicator (fun x => deriv (cutoff n) (u x) • gradient u x) :=
    (ae_restrict_iff' hΩ.measurableSet).mpr (Eventually.of_forall fun x hx =>
      cutoff_indicator_gradient hΩ hu hU hf n hx)
  have hg := (memLp_congr_ae heq).mpr (cutoff_grad_memLp hU hH n)
  have hh := HasH1Gradient.of_contDiffOn hΩ (cutoff_indicator_contDiffOn hΩ hu hU hf n)
    (cutoff_memLp hU hH n) hg
  refine ⟨hh.1,cutoff_grad_memLp hU hH n,?_⟩
  intro φ hφ hc hs e
  rw [hh.2.2 φ hφ hc hs e]
  congr 1
  apply integral_congr_ae
  filter_upwards [heq] with x hx
  rw [hx]



lemma hasH1Gradient_indicator (hΩ : IsOpen Ω) (hu : ContDiffOn ℝ ∞ u Ω)
    (hH : HasH1Gradient Ω u (gradient u)) (hU : IsOpen U)
    (hf : ∀ x ∈ frontier U ∩ Ω, u x = 0) (hpos : ∀ x ∈ U, 0 < u x) :
    HasH1Gradient Ω (U.indicator u) (U.indicator (gradient u)) := by
  refine ⟨MemLp.indicator hU.measurableSet hH.1,
    MemLp.indicator hU.measurableSet hH.2.1,?_⟩
  intro φ hφ hc hs e
  let F (n : ℕ) := U.indicator (fun x => cutoff n (u x))
  let G (n : ℕ) := U.indicator (fun x => deriv (cutoff n) (u x) • gradient u x)
  have hmF (n : ℕ) := cutoff_memLp hU hH n
  have hmG (n : ℕ) := cutoff_grad_memLp hU hH n
  have hlimF (x : Plane) : Tendsto (fun n => F n x) atTop (𝓝 (U.indicator u x)) := by
    by_cases hx : x ∈ U
    · apply tendsto_const_nhds.congr'
      filter_upwards [cutoff_eventually_eq (hpos x hx)] with n hn
      simp only [F,indicator_of_mem hx,hn.1]
    · simpa only [F,indicator_of_notMem hx] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 0))
  have hlimG (x : Plane) : Tendsto (fun n => G n x) atTop (𝓝 (U.indicator (gradient u) x)) := by
    by_cases hx : x ∈ U
    · apply tendsto_const_nhds.congr'
      filter_upwards [cutoff_eventually_eq (hpos x hx)] with n hn
      simp only [G,indicator_of_mem hx,hn.2,one_smul]
    · simpa only [G,indicator_of_notMem hx] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:Plane)) atTop (𝓝 0))
  have hL := tendsto_integral_of_dominated_convergence (μ := volume.restrict Ω)
    (fun x => ‖u x‖ * ‖fderiv ℝ φ x e‖)
    (fun n => (hmF n).aestronglyMeasurable.mul (test_derivative_memLp hφ hc e).aestronglyMeasurable)
    (hH.1.norm.integrable_mul (test_derivative_memLp hφ hc e).norm)
    (fun n => Eventually.of_forall fun x => by
      simp only [Pi.mul_apply,norm_mul]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      by_cases hx : x ∈ U
      · simpa only [F,indicator_of_mem hx] using cutoff_norm_le n (u x)
      · simp only [indicator_of_notMem hx,norm_zero]; exact norm_nonneg _)
    (Eventually.of_forall fun x => (hlimF x).mul tendsto_const_nhds)
  obtain ⟨C,hC,hbd⟩ := cutoff_deriv_bound
  have hR := tendsto_integral_of_dominated_convergence (μ := volume.restrict Ω)
    (fun x => C * ‖gradient u x‖ * ‖e‖ * ‖φ x‖)
    (fun n => ((hmG n).aestronglyMeasurable.inner (aestronglyMeasurable_const (b := e))).mul
      (test_memLp hφ hc).aestronglyMeasurable)
    (((hH.2.1.norm.const_mul C).mul_const ‖e‖).integrable_mul (test_memLp hφ hc).norm)
    (fun n => Eventually.of_forall fun x => by
      simp only [Pi.mul_apply,norm_mul]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      apply le_trans (norm_inner_le_norm _ _) (mul_le_mul_of_nonneg_right ?_ (norm_nonneg e))
      by_cases hx : x ∈ U
      · simp only [indicator_of_mem hx,norm_smul]
        exact mul_le_mul_of_nonneg_right (hbd n (u x)) (norm_nonneg _)
      · simp only [indicator_of_notMem hx,norm_zero]
        exact mul_nonneg (le_trans zero_le_one hC) (norm_nonneg _))
    (Eventually.of_forall fun x => ((hlimG x).inner tendsto_const_nhds).mul tendsto_const_nhds)
  apply tendsto_nhds_unique hL
  convert hR.neg using 1
  ext n
  exact (cutoff_hasH1Gradient hΩ hu hH hU hf n).2.2 φ hφ hc hs e

lemma positive_set_open (hΩ : IsOpen Ω) (hu : ContinuousOn u Ω) :
    IsOpen (Ω ∩ {x | 0 < u x}) := by
  exact hu.isOpen_inter_preimage hΩ isOpen_Ioi

end StrictHotSpots.Nodal
end NodalRestrictionWeightedCombinedLayer

section SmoothZeroTraceCombinedLayer
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff InnerProductSpace
namespace StrictHotSpots

lemma positive_region_frontier_zero {Ω : Set Plane} {u : Plane → ℝ}
    (ho : IsOpen Ω) (hu : ContinuousOn u Ω) {x : Plane}
    (hx : x ∈ frontier (Ω ∩ {x | 0 < u x}) ∩ Ω) : u x = 0 := by
  have hc := hu.continuousAt (ho.mem_nhds hx.2)
  have hP := Nodal.positive_set_open ho hu
  have hn : x ∉ Ω ∩ {x | 0 < u x} := by simpa only [hP.interior_eq] using hx.1.2
  have hle : u x ≤ 0 := le_of_not_gt (fun hp => hn ⟨hx.2,hp⟩)
  apply le_antisymm hle
  by_contra hp
  have he : ∀ᶠ y in 𝓝 x, u y < 0 := hc.eventually (gt_mem_nhds (lt_of_not_ge hp))
  have hh := (mem_closure_iff_frequently.mp hx.1.1).and_eventually he
  obtain ⟨y,hy,huy⟩ := hh.exists
  exact (not_lt_of_gt hy.2) huy

lemma positive_part_gradient {Ω : Set Plane} {u : Plane → ℝ}
    (ho : IsOpen Ω) (hu : ContDiffOn ℝ ∞ u Ω)
    (hH : HasH1Gradient Ω u (gradient u)) :
    HasH1Gradient Ω ((Ω ∩ {x | 0 < u x}).indicator u)
      ((Ω ∩ {x | 0 < u x}).indicator (gradient u)) :=
  Nodal.hasH1Gradient_indicator ho hu hH (Nodal.positive_set_open ho hu.continuousOn)
    (fun _ hx => positive_region_frontier_zero ho hu.continuousOn hx) (fun _ hx => hx.2)

end StrictHotSpots
end SmoothZeroTraceCombinedLayer

section ContinuousZeroTraceCombinedLayer
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff InnerProductSpace
namespace StrictHotSpots
lemma positive_part_memH10_interior {Ω : Set Plane} {u : Plane → ℝ}
    (ho : IsOpen Ω) (hu : ContDiffOn ℝ ∞ u Ω) (hc : ContinuousOn u (closure Ω))
    (hH : HasH1Gradient Ω u (gradient u)) (hb : Bornology.IsBounded Ω)
    (hz : ∀ x ∈ frontier Ω, u x ≤ 0) :
    (positive_part_gradient ho hu hH).toH1 ∈ h10Submodule ho := by
  let P := Ω ∩ {x | 0 < u x}
  let hv := positive_part_gradient ho hu hH
  let f (n : ℕ) := BoundarySign.test_interior ho hu hc hb hz n
  have hvlim : Tendsto (fun n => H1.value (smoothTestToH1 ho (f n))) atTop (𝓝 (H1.value hv.toH1)) := by
    apply L2VectorLimits.tendsto_toLp_of_dominated
      (fun n => (HasH1Gradient.test ho (f n).property.1 (f n).property.2.1).1) hv.1 hH.1.norm
    · exact Eventually.of_forall fun n => by
        filter_upwards [ae_restrict_mem ho.measurableSet] with x hx
        change ‖BoundarySign.cut Ω u n x‖ ≤ ‖u x‖
        simpa only [BoundarySign.cut,indicator_of_mem hx] using Nodal.cutoff_norm_le n (u x)
    · filter_upwards [ae_restrict_mem ho.measurableSet] with x hx
      change Tendsto (fun n => BoundarySign.cut Ω u n x) atTop (𝓝 (P.indicator u x))
      simp only [BoundarySign.cut,indicator_of_mem hx]
      simpa only [P,indicator,mem_inter_iff,mem_ofPred_eq,hx,true_and] using Nodal.cutoff_tendsto (u x)
  obtain ⟨C,hC,hbd⟩ := Nodal.cutoff_deriv_bound
  have hglim : Tendsto (fun n => H1.grad (smoothTestToH1 ho (f n))) atTop (𝓝 (H1.grad hv.toH1)) := by
    apply L2VectorLimits.tendsto_toLp_of_dominated
      (fun n => (HasH1Gradient.test ho (f n).property.1 (f n).property.2.1).2.1)
      hv.2.1 (hH.2.1.norm.const_mul C)
    · exact Eventually.of_forall fun n => by
        filter_upwards [ae_restrict_mem ho.measurableSet] with x hx
        change ‖gradient (BoundarySign.cut Ω u n) x‖ ≤ C*‖gradient u x‖
        rw [BoundarySign.cut_gradient_interior ho hu n hx,norm_smul]
        exact mul_le_mul_of_nonneg_right (hbd n (u x)) (norm_nonneg _)
    · filter_upwards [ae_restrict_mem ho.measurableSet] with x hx
      change Tendsto (fun n => gradient (BoundarySign.cut Ω u n) x) atTop
        (𝓝 (P.indicator (gradient u) x))
      simp_rw [BoundarySign.cut_gradient_interior ho hu _ hx]
      simpa only [P,indicator,mem_inter_iff,mem_ofPred_eq,hx,true_and,ite_smul,one_smul,zero_smul] using
        (Nodal.cutoff_deriv_tendsto (u x)).smul_const (gradient u x)
  change hv.toH1 ∈ closure ((smoothTestToH1 ho).range : Set (H1 Ω))
  exact mem_closure_of_tendsto (H1.tendsto_of_value_grad hvlim hglim)
    (Eventually.of_forall fun n => ⟨f n,rfl⟩)

theorem interior_smooth_zero_trace_memH10 {Ω : Set Plane} {u : Plane → ℝ}
    (ho : IsOpen Ω) (hu : ContDiffOn ℝ ∞ u Ω) (hc : ContinuousOn u (closure Ω))
    (hH : HasH1Gradient Ω u (gradient u)) (hb : Bornology.IsBounded Ω)
    (hz : ∀ x ∈ frontier Ω, u x = 0) : hH.toH1 ∈ h10Submodule ho := by
  have hg : gradient (-u) = -gradient u := by
    funext x
    simp only [gradient,Pi.neg_apply,fderiv_neg,map_neg]
  have hn : HasH1Gradient Ω (-u) (gradient (-u)) := by
    simpa only [hg,neg_one_smul] using hH.smul (-1)
  let vp := positive_part_gradient ho hu hH
  let vn := positive_part_gradient ho hu.neg hn
  have hp := positive_part_memH10_interior ho hu hc hH hb (fun x hx => (hz x hx).le)
  have hq := positive_part_memH10_interior ho hu.neg hc.neg hn hb (fun x hx => by simp only [hz x hx,neg_zero,le_refl])
  have he : hH.toH1 = vp.toH1-vn.toH1 := by
    apply H1.value_injective ho
    rw [map_sub,H1.value_toH1,H1.value_toH1,H1.value_toH1]
    apply Lp.ext
    filter_upwards [hH.1.coeFn_toLp,vp.1.coeFn_toLp,vn.1.coeFn_toLp,
      Lp.coeFn_sub (vp.1.toLp _) (vn.1.toLp _),ae_restrict_mem ho.measurableSet] with x hx hpx hnx hsub hxΩ
    rw [hsub,Pi.sub_apply,hx,hpx,hnx]
    change u x = (Ω ∩ {x | 0 < u x}).indicator u x -
      (Ω ∩ {x | 0 < (-u) x}).indicator (-u) x
    by_cases h : 0 < u x
    · have hn' : ¬0 < -u x := by linarith
      simp only [indicator,mem_inter_iff,hxΩ,mem_ofPred_eq,true_and,Pi.neg_apply,h,hn',ite_true,ite_false,sub_zero]
    · by_cases h' : u x < 0
      · have hn' : 0 < -u x := neg_pos.mpr h'
        simp only [indicator,mem_inter_iff,hxΩ,mem_ofPred_eq,true_and,Pi.neg_apply,h,hn',ite_true,ite_false,zero_sub,neg_neg]
      · have hx0 : u x = 0 := le_antisymm (le_of_not_gt h) (le_of_not_gt h')
        simp [indicator,hx0]
  rw [he]
  exact (h10Submodule ho).sub_mem hp hq
end StrictHotSpots
end ContinuousZeroTraceCombinedLayer


end

end DouglasLipschitzBase

end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_Poisson
attribute [-instance] _root_.OAI.StrictHotSpots.N1.innerProductSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section DouglasLipschitzBase
noncomputable section

section SubcriticalExtensionCombinedLayer
open Set MeasureTheory
open scoped InnerProductSpace ENNReal
namespace StrictHotSpots.SubcriticalExtension
variable {Ω : Set Plane} (ho : IsOpen Ω) (hb : Bornology.IsBounded Ω)
variable {ν : Measure Plane} {C : ℝ≥0∞} (hC : C ≠ ∞) (hν : ν ≤ C • volume.restrict Ω)

def observe : H1 Ω →L[ℝ] Lp ℝ 2 ν :=
  (Lp.LpToLpOfMeasureLeSMul hC hν).comp H1.value

def solve : Lp ℝ 2 ν →L[ℝ] H10 ho :=
  DirichletOperator.solution (H10.energy ho) (H10.energy_coercive ho hb)
    (H10.weightedValue ho hC hν)


def extension (A : H1 Ω) : H1 Ω := A + (solve ho hb hC hν
  (BanachResolvent.resolvent (H10.greenOperator ho hb hC hν) (observe hC hν A))).val

end StrictHotSpots.SubcriticalExtension
end SubcriticalExtensionCombinedLayer

end
end DouglasLipschitzBase


end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_DouglasEnergy
attribute [-instance] _root_.OAI.StrictHotSpots.N1.innerProductSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section LipschitzPoissonVariational

noncomputable section
open Set MeasureTheory Filter Metric AddCircle
open scoped Topology ContDiff InnerProductSpace Laplacian
namespace StrictHotSpots.Douglas
open PlaneGreen DiskH10 SubcriticalExtension
local notation "τ" => (2*Real.pi)




theorem lipschitzPoisson_boundary_class (f : C(AddCircle τ,ℂ)) {K : ℝ}
    (hK : 0 ≤ K) (h : ChordLipschitz K f)
    {φ : Plane → ℝ} (hφ : ContDiffOn ℝ ∞ φ disk)
    (hc : ContinuousOn φ (closure disk)) (hv : HasH1Gradient disk φ (gradient φ))
    (hb : ∀ s : AddCircle τ, φ (complexIso s.toCircle) = (f s).re) :
    (lipschitz_planePoisson_hasH1Gradient f hK h).toH1-hv.toH1 ∈
      h10Submodule (show IsOpen disk from isOpen_ball) := by
  let hu := closedPlanePoisson_hasH1Gradient f hK h
  have hs := closedPlanePoisson_contDiffOn f
  have hsub : HasH1Gradient disk (closedPlanePoisson f-φ) (gradient (closedPlanePoisson f-φ)) := by
    apply (hu.sub hv).congr (ae_of_all _ (fun _ => rfl))
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    simp only [gradient,Pi.sub_apply]
    rw [fderiv_sub ((hs.contDiffAt (isOpen_ball.mem_nhds hx)).differentiableAt (by simp))
      ((hφ.contDiffAt (isOpen_ball.mem_nhds hx)).differentiableAt (by simp)),map_sub]
  have hz : ∀ x ∈ frontier disk, (closedPlanePoisson f-φ) x = 0 := by
    intro x hx
    have hn : complexIso.symm x ∈ sphere (0:ℂ) 1 := by
      simpa only [disk,frontier_ball (0:Plane) (by norm_num : (1:ℝ) ≠ 0),
        mem_sphere_zero_iff_norm,LinearIsometryEquiv.norm_map] using hx
    obtain ⟨s,hs⟩ := exists_toCircle hn
    have hxc : complexIso s.toCircle = x := by rw [hs]; exact complexIso.apply_symm_apply x
    rw [← hxc]
    exact sub_eq_zero.mpr ((closedPlanePoisson_boundary f s).trans (hb s).symm)
  have hm := interior_smooth_zero_trace_memH10 (Ω:=disk) isOpen_ball (hs.sub hφ)
    ((closedPlanePoisson_continuousOn f hK h).sub hc) hsub isBounded_ball hz
  have he : hu.toH1-hv.toH1 = hsub.toH1 := by
    apply H1.value_injective (Ω:=disk) isOpen_ball
    rw [map_sub,H1.value_toH1,H1.value_toH1,H1.value_toH1]
    apply Lp.ext
    filter_upwards [hu.1.coeFn_toLp,hv.1.coeFn_toLp,hsub.1.coeFn_toLp,
      Lp.coeFn_sub (hu.1.toLp _) (hv.1.toLp _)] with x hux hvx hsx hdiff
    rw [hdiff,Pi.sub_apply,hux,hvx,hsx]
    rfl
  rw [← he] at hm
  change (closedPlanePoisson_hasH1Gradient f hK h).toH1-hv.toH1 ∈ _ at hm
  rw [closedPlanePoisson_toH1 f hK h] at hm
  exact hm

end StrictHotSpots.Douglas
end
end LipschitzPoissonVariational

end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_BoundaryEnergy
attribute [-instance] _root_.OAI.StrictHotSpots.N1.innerProductSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section LipschitzBoundaryScalarSupport

noncomputable section

section SubcriticalUniquenessScalarSupportLayer

open Set MeasureTheory
open scoped InnerProductSpace ENNReal
namespace StrictHotSpots.SubcriticalExtension
variable {Ω : Set Plane} (ho : IsOpen Ω) (hb : Bornology.IsBounded Ω)
variable {ν : Measure Plane} {C : ℝ≥0∞} (hC : C ≠ ∞) (hν : ν ≤ C • volume.restrict Ω)

lemma extension_difference (A : H1 Ω) :
    ∃ v : H10 ho, extension ho hb hC hν A-A = v.val := by
  refine ⟨solve ho hb hC hν
    (BanachResolvent.resolvent (H10.greenOperator ho hb hC hν) (observe hC hν A)), ?_⟩
  change A+_-A = _
  abel

end StrictHotSpots.SubcriticalExtension
end SubcriticalUniquenessScalarSupportLayer

end
end LipschitzBoundaryScalarSupport


end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_Conformal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section ConformalMeasure




noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal Topology
namespace StrictHotSpots.Conformal

variable (e : OpenPartialHomeomorph CoordinatePlane CoordinatePlane) (d : CoordinatePlane → ℂ)

lemma chartMeasure_ac : chartMeasure e d ≪ volume.restrict e.source :=
  withDensity_absolutelyContinuous _ _

lemma chart_aemeasurable : AEMeasurable e (chartMeasure e d) :=
  (e.continuousOn.aemeasurable e.open_source.measurableSet).mono_ac (chartMeasure_ac e d)

end StrictHotSpots.Conformal
end
end ConformalMeasure


end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_ClosedChart
attribute [-instance] _root_.OAI.StrictHotSpots.N1.innerProductSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section ClosedConformalData

noncomputable section
open Set Filter Metric
open scoped ContDiff NNReal
namespace StrictHotSpots.Conformal.ClosedDiskChart
variable {Ω : Set Plane} (c : ClosedDiskChart Ω)



lemma diskMap_inverse_smooth : ContDiffOn ℝ ∞ c.diskMap.symm Ω := by
  change ContDiffOn ℝ ∞ c.e.symm Ω
  exact c.inverse_smooth.mono c.target_eq.symm.subset
lemma inverse_maps_closed : MapsTo c.G (closure Ω) (closure DiskH10.disk) :=
  c.source_eq ▸ c.inverse_maps_closure
lemma diskMap_inverse_agrees : EqOn c.diskMap.symm c.G Ω := fun _ hy => c.inverse_agrees (c.target_eq.symm ▸ hy)

lemma maps_boundary : MapsTo c.F (frontier DiskH10.disk) (frontier Ω) := by
  intro x hx
  refine ⟨c.maps_closed hx.1,?_⟩
  rw [(show IsOpen Ω from c.target_eq ▸ c.e.open_target).interior_eq]
  intro hy
  have hg : c.G (c.F x) ∈ DiskH10.disk := by
    rw [← c.diskMap_inverse_agrees hy]
    exact c.diskMap.map_target hy
  have hi := c.left_inverse x (c.source_eq.symm ▸ hx.1)
  rw [hi] at hg
  exact hx.2 ((show IsOpen DiskH10.disk from PlaneGreen.diskOpen).interior_eq.symm ▸ hg)

lemma inverse_maps_boundary : MapsTo c.G (frontier Ω) (frontier DiskH10.disk) := by
  intro x hx
  refine ⟨c.inverse_maps_closed hx.1,?_⟩
  rw [(show IsOpen DiskH10.disk from PlaneGreen.diskOpen).interior_eq]
  intro hy
  have hg : c.F (c.G x) ∈ Ω := by
    rw [← c.diskMap_agrees hy]
    exact c.diskMap.map_source hy
  rw [c.right_inverse x hx.1] at hg
  exact hx.2 ((show IsOpen Ω from c.target_eq ▸ c.e.open_target).interior_eq.symm ▸ hg)


end StrictHotSpots.Conformal.ClosedDiskChart
end
end ClosedConformalData

section ClosedSmoothData



noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology
namespace StrictHotSpots


lemma smooth_closure_H1 {Ω : Set Plane} {u : Plane → ℝ}
    (ho : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hs : SmoothBoundary Ω)
    (hu : ContDiffOn ℝ ∞ u (closure Ω)) : HasH1Gradient Ω u (gradient u) := by
  apply HasH1Gradient.of_contDiffOn ho (hu.mono subset_closure)
    (continuous_closure_memLp ho hb hu.continuousOn)
  apply MemLp.ae_eq _ (continuous_closure_memLp ho hb (closedGradient_continuous ho hs hu))
  filter_upwards [ae_restrict_mem ho.measurableSet] with x hx
  exact closedGradient_eq ho hx

lemma closure_directional_smooth {Ω : Set Plane} {u : Plane → ℝ}
    (ho : IsOpen Ω) (hs : SmoothBoundary Ω)
    (hu : ContDiffOn ℝ ∞ u (closure Ω)) (e : Plane) :
    ContDiffOn ℝ ∞ (fun x => fderivWithin ℝ u (closure Ω) x e) (closure Ω) :=
  (hu.fderivWithin (hs.uniqueDiffOn_closure ho) (by simp)).clm_apply contDiffOn_const

end StrictHotSpots

namespace StrictHotSpots.Conformal.ClosedDiskChart
open Set Filter Metric MeasureTheory
open scoped ContDiff InnerProductSpace NNReal
open DiskH10 PlaneGreen
variable {Ω : Set Plane} (c : ClosedDiskChart Ω)

lemma pullDatum_lipschitz (hb : Bornology.IsBounded Ω) (hs : SmoothBoundary Ω)
    {w : Plane → ℝ} (hw : ContDiffOn ℝ ∞ w (closure Ω)) :
    ∃ B : ℝ≥0, LipschitzOnWith B (c.pullDatum w) (closure disk) := by
  obtain ⟨B,hB⟩ := c.pullDatum_bounded_gradient hb hs hw
  have hsm := c.pullDatum_smooth (hw.mono subset_closure)
  have hd (x : Plane) (hx : x ∈ disk) : DifferentiableAt ℝ (c.pullDatum w) x :=
    ((hsm.differentiableOn (by simp)) x hx).differentiableAt (diskOpen.mem_nhds hx)
  have hf (x : Plane) (hx : x ∈ disk) : ‖fderiv ℝ (c.pullDatum w) x‖₊ ≤ B := by
    change ‖fderiv ℝ (c.pullDatum w) x‖ ≤ (B : ℝ)
    simpa only [gradient,LinearIsometryEquiv.norm_map] using hB x hx
  exact ⟨B,LipschitzOnWith.closure (c.pullDatum_continuous hw.continuousOn)
    ((convex_ball (0 : Plane) 1).lipschitzOnWith_of_nnnorm_fderiv_le hd hf)⟩

end StrictHotSpots.Conformal.ClosedDiskChart
end
end ClosedSmoothData

end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_Potentials
attribute [-instance] _root_.OAI.StrictHotSpots.N1.innerProductSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section ActualVectorSupport

noncomputable section




section PlaneDifferentialInteriorSupportLayer

open Set MeasureTheory InnerProductSpace
open scoped ContDiff Laplacian
namespace StrictHotSpots.Hodge
abbrev e (i : Fin 2) : Plane := planeBasis i
end StrictHotSpots.Hodge


end PlaneDifferentialInteriorSupportLayer



end

end ActualVectorSupport

end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_GreenSolution
attribute [-instance] _root_.OAI.StrictHotSpots.N1.innerProductSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section BoundaryScalarEnergy

noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology ContDiff InnerProductSpace ENNReal NNReal
namespace StrictHotSpots.PlaneGreen
open DiskH10
variable {ν : Measure Plane} [IsFiniteMeasure ν] {C : ℝ≥0∞}
  (hC : C ≠ (∞ : ℝ≥0∞)) (hν : ν ≤ C • volume.restrict disk)



def boundarySolution (f : C(Boundary,ℝ)) {A : ℝ≥0} (hf : LipschitzWith A f) : H1 disk :=
  SubcriticalExtension.extension diskOpen diskBounded hC hν (boundaryPoissonH1 f hf)

omit [IsFiniteMeasure ν] in
lemma boundarySolution_class (f : C(Boundary,ℝ)) {A : ℝ≥0} (hf : LipschitzWith A f) :
    ∃ v : H10 diskOpen, boundarySolution hC hν f hf-boundaryPoissonH1 f hf=v.val :=
  SubcriticalExtension.extension_difference diskOpen diskBounded hC hν _




end StrictHotSpots.PlaneGreen
end
end BoundaryScalarEnergy

section BoundarySolutionIdentification

noncomputable section
open Set MeasureTheory Filter Metric AddCircle
open scoped Topology ContDiff InnerProductSpace ENNReal NNReal
namespace StrictHotSpots.PlaneGreen
open DiskH10
local notation "τ" => (2*Real.pi)

lemma boundaryPoissonH1_real_class (f : C(Boundary,ℝ)) {A : ℝ≥0}
    (hf : LipschitzWith A f) {φ : Plane → ℝ}
    (hφ : ContDiffOn ℝ ∞ φ disk) (hc : ContinuousOn φ (closure disk))
    (hv : HasH1Gradient disk φ (gradient φ)) (hb : ∀ s : Boundary, φ s=f s) :
    ∃ v : H10 diskOpen, hv.toH1-boundaryPoissonH1 f hf=v.val := by
  have ht : ∀ s : AddCircle τ, φ (complexIso s.toCircle) = (boundaryAngleData f s).re := by
    intro s
    simpa only [boundaryAngleData_apply,Complex.ofReal_re,angleBoundary_coe] using hb (angleBoundary s)
  have hm := Douglas.lipschitzPoisson_boundary_class (boundaryAngleData f) A.coe_nonneg
    (boundaryAngleData_lipschitz f hf) hφ hc hv ht
  refine ⟨⟨_,(h10Submodule diskOpen).neg_mem hm⟩,?_⟩
  change hv.toH1-boundaryPoissonH1 f hf = -(boundaryPoissonH1 f hf-hv.toH1)
  abel

end StrictHotSpots.PlaneGreen
end
end BoundarySolutionIdentification

section ActualBoundaryDatum

noncomputable section
open Set MeasureTheory Filter Metric
open scoped ContDiff InnerProductSpace NNReal
namespace StrictHotSpots.Conformal.ClosedDiskChart
open DiskH10 PlaneGreen
variable {Ω : Set Plane} (c : ClosedDiskChart Ω)

lemma datumTrace_lipschitz (hb : Bornology.IsBounded Ω) (hs : SmoothBoundary Ω)
    {w : Plane → ℝ} (hw : ContDiffOn ℝ ∞ w (closure Ω)) :
    ∃ B : ℝ≥0, LipschitzWith B (c.datumTrace w hw.continuousOn) := by
  obtain ⟨B,hB⟩ := c.pullDatum_lipschitz hb hs hw
  refine ⟨B,fun x y => ?_⟩
  exact hB (boundary_mem_closed x) (boundary_mem_closed y)

lemma pullDatum_Poisson_class (hb : Bornology.IsBounded Ω) (hs : SmoothBoundary Ω)
    {w : Plane → ℝ} (hw : ContDiffOn ℝ ∞ w (closure Ω)) {B : ℝ≥0}
    (hl : LipschitzWith B (c.datumTrace w hw.continuousOn)) :
    ∃ v : H10 diskOpen, (c.pullDatum_H1 hb hs hw).toH1 -
      boundaryPoissonH1 (c.datumTrace w hw.continuousOn) hl = v.val :=
  boundaryPoissonH1_real_class (c.datumTrace w hw.continuousOn) hl
    (c.pullDatum_smooth (hw.mono subset_closure)) (c.pullDatum_continuous hw.continuousOn)
    (c.pullDatum_H1 hb hs hw) (fun _ => rfl)

end StrictHotSpots.Conformal.ClosedDiskChart
end
end ActualBoundaryDatum


end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_VectorEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section ActualVectorSupport
noncomputable section
section H1SmoothMultiplierActualCompatibleLayer
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace ENNReal
namespace StrictHotSpots



lemma HasH1Gradient.mul_smooth {Ω : Set Plane} {u : Plane → ℝ} {g : Plane → Plane}
    (hu : HasH1Gradient Ω u g) {b : Plane → ℝ} (hb : ContDiff ℝ ∞ b)
    (hb0 : MemLp b ∞ (volume.restrict Ω))
    (hb1 : MemLp (gradient b) ∞ (volume.restrict Ω)) :
    HasH1Gradient Ω (fun x => b x*u x) (fun x => b x • g x+u x • gradient b x) := by
  have hval : MemLp (fun x => b x*u x) 2 (volume.restrict Ω) := hu.1.mul' hb0
  have hbg : MemLp (fun x => b x • g x) 2 (volume.restrict Ω) := hu.2.1.smul hb0
  have hug : MemLp (fun x => u x • gradient b x) 2 (volume.restrict Ω) := hb1.smul hu.1
  refine ⟨hval,hbg.add hug,?_⟩
  intro φ hφ hk hs e
  have hp : HasCompactSupport (fun x => b x*φ x) := hk.mul_left
  have hps : tsupport (fun x => b x*φ x) ⊆ Ω := tsupport_mul_subset_right.trans hs
  have h := hu.2.2 (fun x => b x*φ x) (hb.mul hφ) hp hps e
  have hdb (x : Plane) : fderiv ℝ (fun x => b x*φ x) x e =
      (fderiv ℝ b x e)*φ x+b x*(fderiv ℝ φ x e) := by
    rw [fderiv_fun_mul (hb.differentiable (by simp) x) (hφ.differentiable (by simp) x)]
    simp only [add_apply,smul_apply,smul_eq_mul]
    ring
  have hφ2 := test_memLp (Ω := Ω) hφ hk
  have hdφ2 := test_derivative_memLp (Ω := Ω) hφ hk e
  have hd : MemLp (fun x => fderiv ℝ b x e) ∞ (volume.restrict Ω) := by
    simpa only [inner_gradient_left] using hb1.inner_const (𝕜 := ℝ) e
  have hud : MemLp (fun x => (fderiv ℝ b x e)*u x) 2 (volume.restrict Ω) := hu.1.mul' hd
  have hui : Integrable (fun x => u x*(fderiv ℝ b x e)*φ x) (volume.restrict Ω) :=
    (hud.integrable_mul hφ2).congr (Eventually.of_forall fun x => by simp only [Pi.mul_apply]; ring)
  have hvi : Integrable (fun x => b x*u x*(fderiv ℝ φ x e)) (volume.restrict Ω) :=
    hval.integrable_mul hdφ2
  have hgi : Integrable (fun x => inner ℝ (b x • g x) e*φ x) (volume.restrict Ω) :=
    (hbg.inner_const (𝕜 := ℝ) e).integrable_mul hφ2
  simp_rw [hdb,mul_add] at h
  have hl : (∫ x in Ω, u x*((fderiv ℝ b x e)*φ x)+u x*(b x*(fderiv ℝ φ x e))) =
      (∫ x in Ω, u x*(fderiv ℝ b x e)*φ x)+
      (∫ x in Ω, b x*u x*(fderiv ℝ φ x e)) := by
    convert integral_add hui hvi using 1
    congr 1
    funext x
    ring
  rw [hl] at h
  have hr : (∫ x in Ω, inner ℝ (g x) e*(b x*φ x)) =
      ∫ x in Ω, inner ℝ (b x • g x) e*φ x := by
    apply integral_congr_ae
    filter_upwards [] with x
    rw [real_inner_smul_left]
    ring
  rw [hr] at h
  have hg : (∫ x in Ω, inner ℝ (b x • g x+u x • gradient b x) e*φ x) =
      (∫ x in Ω,inner ℝ (b x • g x) e*φ x)+
      (∫ x in Ω,u x*(fderiv ℝ b x e)*φ x) := by
    simp_rw [inner_add_left,real_inner_smul_left,inner_gradient_left,add_mul]
    simpa only [real_inner_smul_left] using integral_add hgi hui
  rw [hg]
  linarith

end StrictHotSpots
end H1SmoothMultiplierActualCompatibleLayer

open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology
namespace StrictHotSpots
namespace Hodge
variable {Ω : Set Plane} {u : Plane → ℝ}




def eigenGradientField (hΩ : AdmissibleDomain Ω) (hu : InFirstNeumannEigenspace Ω u) :
    Fin 2 → H1 Ω := fun i =>
  (smooth_closure_H1 hΩ.2.1 hΩ.2.2.1 hΩ.2.2.2.2
    (closure_directional_smooth hΩ.2.1 hΩ.2.2.2.2 hu.1 (e i))).toH1

end Hodge
end StrictHotSpots
end
end ActualVectorSupport

section ActualScalarEnergy

noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace ENNReal NNReal
namespace StrictHotSpots.Conformal.ClosedDiskChart
open DiskH10 PlaneGreen
variable {Ω : Set Plane} (c : ClosedDiskChart Ω)
variable (hb : Bornology.IsBounded Ω) (hs : SmoothBoundary Ω)
variable (hμ : 0 ≤ firstPositiveNeumannValue Ω)

lemma boundarySolution_datum_class {w : Plane → ℝ}
    (hw : ContDiffOn ℝ ∞ w (closure Ω)) {B : ℝ≥0}
    (hl : LipschitzWith B (c.datumTrace w hw.continuousOn)) :
    ∃ v : H10 diskOpen,
      boundarySolution c.densityBound_ne_top (c.density_bound hμ)
        (c.datumTrace w hw.continuousOn) hl = (c.pullDatum_H1 hb hs hw).toH1+v.val := by
  obtain ⟨a,ha⟩ := boundarySolution_class c.densityBound_ne_top (c.density_bound hμ)
    (c.datumTrace w hw.continuousOn) hl
  obtain ⟨b,hb'⟩ := c.pullDatum_Poisson_class hb hs hw hl
  refine ⟨a-b,?_⟩
  change _ = _+(a.val-b.val)
  rw [← ha,← hb']
  abel



def datumCorrection {w : Plane → ℝ} (hw : ContDiffOn ℝ ∞ w (closure Ω)) {B : ℝ≥0}
    (hl : LipschitzWith B (c.datumTrace w hw.continuousOn)) : H10 diskOpen :=
  (c.boundarySolution_datum_class hb hs hμ hw hl).choose

end StrictHotSpots.Conformal.ClosedDiskChart
end
end ActualScalarEnergy


end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_Multiplier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section LipschitzMollifier

noncomputable section
open Set MeasureTheory Filter Metric ContinuousLinearMap
open scoped ContDiff InnerProductSpace ENNReal NNReal Convolution
namespace StrictHotSpots


def ambientSmooth (φ : ContDiffBump (0 : Plane)) (b : Plane → ℝ) : Plane → ℝ :=
  φ.normed volume ⋆[lsmul ℝ ℝ,volume] b

lemma ambientSmooth_smooth (φ : ContDiffBump (0 : Plane)) {b : Plane → ℝ}
    {L : ℝ≥0} (hb : LipschitzWith L b) : ContDiff ℝ ∞ (ambientSmooth φ b) :=
  φ.hasCompactSupport_normed.contDiff_convolution_left _ φ.contDiff_normed hb.continuous.locallyIntegrable

lemma ambientSmooth_integrable (φ : ContDiffBump (0 : Plane)) {b : Plane → ℝ}
    {L : ℝ≥0} (hb : LipschitzWith L b) (x : Plane) :
    Integrable (fun t : Plane => φ.normed volume t * b (x-t)) :=
  φ.hasCompactSupport_normed.convolutionExists_left_of_continuous_right
    (lsmul ℝ ℝ) φ.integrable_normed.locallyIntegrable hb.continuous x

lemma ambientSmooth_lipschitz (φ : ContDiffBump (0 : Plane)) {b : Plane → ℝ}
    {L : ℝ≥0} (hb : LipschitzWith L b) : LipschitzWith L (ambientSmooth φ b) := by
  rw [lipschitzWith_iff_norm_sub_le]
  intro x y
  have hi := (ambientSmooth_integrable φ hb x).sub (ambientSmooth_integrable φ hb y)
  have hp (t : Plane) : ‖φ.normed volume t*b (x-t)-φ.normed volume t*b (y-t)‖ ≤
      φ.normed volume t*((L:ℝ)*‖x-y‖) := by
    rw [← mul_sub,norm_mul,Real.norm_eq_abs,abs_of_nonneg (φ.nonneg_normed t)]
    apply mul_le_mul_of_nonneg_left _ (φ.nonneg_normed t)
    simpa only [sub_sub_sub_cancel_right] using hb.norm_sub_le (x-t) (y-t)
  change ‖(∫ t : Plane, φ.normed volume t*b (x-t))-(∫ t : Plane, φ.normed volume t*b (y-t))‖ ≤ _
  rw [← integral_sub (ambientSmooth_integrable φ hb x) (ambientSmooth_integrable φ hb y)]
  calc
    _ ≤ ∫ t : Plane, ‖φ.normed volume t*b (x-t)-φ.normed volume t*b (y-t)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t : Plane, φ.normed volume t*((L:ℝ)*‖x-y‖) :=
      integral_mono hi.norm (φ.integrable_normed.mul_const _) hp
    _ = _ := by rw [integral_mul_const,φ.integral_normed,one_mul]

lemma ambientSmooth_tendsto {φ : ℕ → ContDiffBump (0 : Plane)}
    (hφ : Tendsto (fun n => (φ n).rOut) atTop (nhds 0)) {b : Plane → ℝ}
    {L : ℝ≥0} (hb : LipschitzWith L b) (x : Plane) :
    Tendsto (fun n => ambientSmooth (φ n) b x) atTop (nhds (b x)) :=
  ContDiffBump.convolution_tendsto_right_of_continuous hφ hb.continuous x

lemma ambientSmooth_fderiv (φ : ContDiffBump (0 : Plane)) {b : Plane → ℝ}
    {L : ℝ≥0} (hb : LipschitzWith L b) (x : Plane) :
    fderiv ℝ (ambientSmooth φ b) x = ∫ t : Plane, φ.normed volume t • fderiv ℝ b (x-t) := by
  have hm : AEStronglyMeasurable (fun t : Plane => φ.normed volume t • fderiv ℝ b (x-t)) volume :=
    (φ.continuous_normed.measurable.smul ((measurable_fderiv ℝ b).comp
      (measurable_const.sub measurable_id))).aestronglyMeasurable
  have hl : ∀ᵐ t : Plane ∂volume, LipschitzOnWith
      (Real.nnabs (φ.normed volume t*(L:ℝ))) (fun y => φ.normed volume t*b (y-t)) univ := by
    filter_upwards [] with t
    apply LipschitzWith.lipschitzOnWith
    apply LipschitzWith.of_dist_le_mul
    intro y z
    simp only [dist_eq_norm,← mul_sub,norm_mul,Real.norm_eq_abs,Real.coe_nnabs,
      abs_of_nonneg (mul_nonneg (φ.nonneg_normed t) L.coe_nonneg),
      abs_of_nonneg (φ.nonneg_normed t)]
    calc
      _ ≤ φ.normed volume t*((L:ℝ)*‖(y-t)-(z-t)‖) :=
        mul_le_mul_of_nonneg_left (hb.norm_sub_le _ _) (φ.nonneg_normed t)
      _ = _ := by rw [sub_sub_sub_cancel_right]; ring
  have hd : ∀ᵐ t : Plane ∂volume, HasFDerivAt (fun y => φ.normed volume t*b (y-t))
      (φ.normed volume t • fderiv ℝ b (x-t)) x := by
    filter_upwards [(volume.measurePreserving_sub_left x).quasiMeasurePreserving.ae
      (hb.ae_differentiableAt (μ := volume))] with t ht
    have h := ht.hasFDerivAt.comp x ((hasFDerivAt_id x).sub (hasFDerivAt_const t x))
    simpa [Function.comp_def,Pi.smul_def,smul_eq_mul] using h.const_smul (φ.normed volume t)
  have hh := hasFDerivAt_integral_of_dominated_loc_of_lip (s := univ)
    (bound := fun t => φ.normed volume t*(L:ℝ)) (by simp : univ ∈ nhds x)
    (Filter.Eventually.of_forall (fun y => (ambientSmooth_integrable φ hb y).aestronglyMeasurable))
    (ambientSmooth_integrable φ hb x) hm hl (φ.integrable_normed.mul_const _) hd
  exact hh.2.fderiv

lemma ambientSmooth_gradient (φ : ContDiffBump (0 : Plane)) {b : Plane → ℝ}
    {L : ℝ≥0} (hb : LipschitzWith L b) (x : Plane) :
    gradient (ambientSmooth φ b) x =
      (φ.normed volume ⋆[lsmul ℝ ℝ,volume] gradient b) x := by
  unfold gradient
  rw [ambientSmooth_fderiv φ hb x]
  apply ((InnerProductSpace.toDual ℝ Plane).symm.toContinuousLinearEquiv.integral_comp_comm
    (fun t : Plane => φ.normed volume t • fderiv ℝ b (x-t))).symm.trans
  apply integral_congr_ae
  filter_upwards [] with t
  exact map_smul _ _ _

lemma lipschitz_gradient_locallyIntegrable {b : Plane → ℝ} {L : ℝ≥0} (hb : LipschitzWith L b) :
    LocallyIntegrable (gradient b) volume := by
  have hm : Measurable (gradient b) :=
    (InnerProductSpace.toDual ℝ Plane).symm.continuous.measurable.comp (measurable_fderiv ℝ b)
  apply (memLp_top_of_bound hm.aestronglyMeasurable (L:ℝ) ?_).locallyIntegrable (by simp)
  filter_upwards [] with x
  change ‖(InnerProductSpace.toDual ℝ Plane).symm (fderiv ℝ b x)‖ ≤ L
  rw [LinearIsometryEquiv.norm_map]
  exact norm_fderiv_le_of_lipschitz ℝ hb

lemma ambientSmooth_gradient_tendsto {φ : ℕ → ContDiffBump (0 : Plane)}
    (hφ : Tendsto (fun n => (φ n).rOut) atTop (nhds 0)) {K : ℝ}
    (hK : ∀ᶠ n in atTop, (φ n).rOut ≤ K*(φ n).rIn) {b : Plane → ℝ}
    {L : ℝ≥0} (hb : LipschitzWith L b) :
    ∀ᵐ x : Plane ∂volume, Tendsto (fun n => gradient (ambientSmooth (φ n) b) x) atTop (nhds (gradient b x)) := by
  simp_rw [ambientSmooth_gradient _ hb]
  exact ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable hφ hK
    (lipschitz_gradient_locallyIntegrable hb)

end StrictHotSpots
end
end LipschitzMollifier

section LipschitzH1

noncomputable section
open Set MeasureTheory Filter Metric
open scoped ContDiff InnerProductSpace ENNReal NNReal Topology
namespace StrictHotSpots


lemma HasH1Gradient.of_tendsto_L2 {Ω : Set Plane} {f : ℕ → Plane → ℝ} {g : ℕ → Plane → Plane}
    (hf : ∀ n, HasH1Gradient Ω (f n) (g n)) {u : Plane → ℝ} {v : Plane → Plane}
    (hu : MemLp u 2 (volume.restrict Ω)) (hv : MemLp v 2 (volume.restrict Ω))
    (hfu : Tendsto (fun n => (hf n).1.toLp (f n)) atTop (𝓝 (hu.toLp u)))
    (hgv : Tendsto (fun n => (hf n).2.1.toLp (g n)) atTop (𝓝 (hv.toLp v))) :
    HasH1Gradient Ω u v := by
  have ht : Tendsto (fun n => (hf n).toH1.val) atTop
      (𝓝 (WithLp.toLp 2 (hu.toLp u,hv.toLp v))) :=
    (WithLp.prod_continuous_toLp 2 _ _).continuousAt.tendsto.comp (hfu.prodMk_nhds hgv)
  have hg := (h1Graph_mem_iff Ω (WithLp.toLp 2 (hu.toLp u,hv.toLp v))).mp
    ((h1Graph_closed Ω).mem_of_tendsto ht (Eventually.of_forall fun n => (hf n).toH1.property))
  exact hg.congr hu.coeFn_toLp hv.coeFn_toLp

def planeApproxBump (n : ℕ) : ContDiffBump (0 : Plane) where
  rIn := (2*((n:ℝ)+1))⁻¹
  rOut := ((n:ℝ)+1)⁻¹
  rIn_pos := by positivity
  rIn_lt_rOut := by
    apply inv_strictAnti₀ (by positivity)
    nlinarith [Nat.cast_nonneg (α:=ℝ) n]

lemma planeApproxBump_rOut_le_one (n : ℕ) : (planeApproxBump n).rOut ≤ 1 := by
  change ((n:ℝ)+1)⁻¹ ≤ 1
  apply inv_le_one_of_one_le₀
  linarith [Nat.cast_nonneg (α:=ℝ) n]

lemma ambientSmooth_error (φ : ContDiffBump (0 : Plane)) {b : Plane → ℝ}
    {L : ℝ≥0} (hb : LipschitzWith L b) (x : Plane) :
    ‖ambientSmooth φ b x-b x‖ ≤ (L:ℝ)*φ.rOut := by
  rw [← dist_eq_norm]
  apply φ.dist_normed_convolution_le hb.continuous.aestronglyMeasurable
  intro y hy
  exact (hb.dist_le_mul y x).trans (mul_le_mul_of_nonneg_left hy.le L.coe_nonneg)

lemma lipschitz_gradient_bound {b : Plane → ℝ} {L : ℝ≥0} (hb : LipschitzWith L b) (x : Plane) :
    ‖gradient b x‖ ≤ L := by
  change ‖(InnerProductSpace.toDual ℝ Plane).symm (fderiv ℝ b x)‖ ≤ L
  rw [LinearIsometryEquiv.norm_map]
  exact norm_fderiv_le_of_lipschitz ℝ hb

lemma lipschitz_gradient_memLp_top {Ω : Set Plane} {b : Plane → ℝ} {L : ℝ≥0}
    (hb : LipschitzWith L b) : MemLp (gradient b) ∞ (volume.restrict Ω) := by
  apply memLp_top_of_bound
    ((InnerProductSpace.toDual ℝ Plane).symm.continuous.measurable.comp
      (measurable_fderiv ℝ b)).aestronglyMeasurable _
  exact Eventually.of_forall (lipschitz_gradient_bound hb)

lemma continuous_closure_memLp_top {Ω : Set Plane} {F : Type*} [NormedAddCommGroup F]
    {f : Plane → F} (ho : IsOpen Ω) (hΩ : Bornology.IsBounded Ω)
    (hf : ContinuousOn f (closure Ω)) : MemLp f ∞ (volume.restrict Ω) := by
  obtain ⟨C,hC⟩ := hΩ.isCompact_closure.exists_bound_of_continuousOn hf
  apply memLp_top_of_bound ((hf.mono subset_closure).aestronglyMeasurable ho.measurableSet) C
  filter_upwards [ae_restrict_mem ho.measurableSet] with x hx
  exact hC x (subset_closure hx)

lemma ambientSmooth_uniform_bound {Ω : Set Plane} (hΩ : Bornology.IsBounded Ω)
    {b : Plane → ℝ} {L : ℝ≥0} (hb : LipschitzWith L b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n, ∀ x ∈ Ω, ‖ambientSmooth (planeApproxBump n) b x‖ ≤ C := by
  obtain ⟨M,hM⟩ := hΩ.isCompact_closure.exists_bound_of_continuousOn hb.continuous.continuousOn
  refine ⟨max M 0+L,by positivity,fun n x hx => ?_⟩
  have he := ambientSmooth_error (planeApproxBump n) hb x
  have hφ := mul_le_mul_of_nonneg_left (planeApproxBump_rOut_le_one n) L.coe_nonneg
  have hx' := hM x (subset_closure hx)
  calc
    _ ≤ ‖ambientSmooth (planeApproxBump n) b x-b x‖+‖b x‖ := norm_le_norm_sub_add _ _
    _ ≤ (L:ℝ)+max M 0 := by linarith [le_max_left M 0]
    _ = _ := by ring



end StrictHotSpots
end
end LipschitzH1

section PhysicalHelmholtz

noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace ENNReal NNReal
namespace StrictHotSpots.PhysicalHelmholtz
variable {Ω : Set Plane} (ho : IsOpen Ω)

local instance instNormedAddCommGroupSubtypeH1AmbientMemSubmoduleRealH1H10_r4d3a39_1 : NormedAddCommGroup (H10 ho) := H10.normedAddCommGroup ho
def incl : H10 ho →L[ℝ] H1 Ω := (h10Submodule ho).subtypeL

end StrictHotSpots.PhysicalHelmholtz
end
end PhysicalHelmholtz


end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_ClosedSolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section ClosedChartTopology

noncomputable section
open Set Metric
open scoped Topology
namespace StrictHotSpots.Conformal.ClosedDiskChart
open DiskH10 PlaneGreen
variable {Ω : Set Plane} (c : ClosedDiskChart Ω)

lemma complex_maps_boundary (s : Circle) : c.F (complexIso (s:ℂ)) ∈ frontier Ω := by
  apply c.maps_boundary
  simp only [disk,frontier_ball (0:Plane) (by norm_num : (1:ℝ) ≠ 0),mem_sphere_zero_iff_norm,
    LinearIsometryEquiv.norm_map,Circle.norm_coe]

lemma complex_inverse_boundary {x : Plane} (hx : x ∈ frontier Ω) : ‖complexIso.symm (c.G x)‖ = 1 := by
  have hh := c.inverse_maps_boundary hx
  simpa only [disk,frontier_ball (0:Plane) (by norm_num : (1:ℝ) ≠ 0),mem_sphere_zero_iff_norm,
    LinearIsometryEquiv.norm_map] using hh


def circleBoundaryHomeomorph : Circle ≃ₜ frontier Ω := by
  classical
  let f : Circle → frontier Ω := fun s => ⟨c.F (complexIso (s:ℂ)),c.complex_maps_boundary s⟩
  let g : frontier Ω → Circle := fun x => ⟨complexIso.symm (c.G x),
    mem_sphere_zero_iff_norm.mpr (c.complex_inverse_boundary x.property)⟩
  have hleft : Function.LeftInverse g f := by
    intro s
    apply Subtype.ext
    have hd : complexIso (s:ℂ) ∈ closure disk := by
      simp only [disk,closure_ball (0:Plane) (by norm_num : (1:ℝ) ≠ 0),mem_closedBall_zero_iff,
        LinearIsometryEquiv.norm_map,Circle.norm_coe,le_refl]
    change complexIso.symm (c.G (c.F (complexIso (s:ℂ)))) = (s:ℂ)
    rw [c.left_inverse _ (c.source_eq.symm ▸ hd),LinearIsometryEquiv.symm_apply_apply]
  have hright : Function.RightInverse g f := by
    intro x
    apply Subtype.ext
    change c.F (complexIso (complexIso.symm (c.G x))) = x
    rw [LinearIsometryEquiv.apply_symm_apply,c.right_inverse x x.property.1]
  exact {
    toFun := f
    invFun := g
    left_inv := hleft
    right_inv := hright
    continuous_toFun := (c.lipschitz.continuous.comp (complexIso.continuous.comp continuous_subtype_val)).subtype_mk _
    continuous_invFun := (complexIso.symm.continuous.comp (c.inverse_lipschitz.continuous.comp continuous_subtype_val)).subtype_mk _ }

end StrictHotSpots.Conformal.ClosedDiskChart
end
end ClosedChartTopology


end OAI
end


