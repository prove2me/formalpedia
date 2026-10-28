-- Prove2me | Definitions.Def_OAIQ070A011
-- name    : OAIQ070A011
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T11:40:26.669258+00:00
-- url     : https://prove2.me/theorems/94550689-0afe-4350-b62c-d22040928ada
-- title:
--   Definitions bundle OAIQ070A011 of the split of OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 14 declarations of OpenAI's Lean: 7 definitions and 7 theorems. The definitions and types are `OAI.YauCounterexamples.chartFormPush`, `OAI.YauCounterexamples.chartTensorMetric`, `OAI.YauCounterexamples.pinningEnergyBilin`, `OAI.YauCounterexamples.pinningEnergyPencil`, `OAI.YauCounterexamples.restrictedPinningPencil`, `OAI.YauCounterexamples.sphericalTensorMetric`, `OAI.YauCounterexamples.threeTensorMetric`.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: [`SmoothYau_DifferentialEq_SphericalOpenFormNorm`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/DifferentialEq/SphericalOpenFormNorm.lean), [`SmoothYau_Geometry_SymmLChartTrivialization`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Geometry/SymmLChartTrivialization.lean), [`SmoothYau_Limits_RestrictedPinningPencil`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Limits/RestrictedPinningPencil.lean), [`SmoothYau_Smoothness_ChartTensorCoordLocal1`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Smoothness/ChartTensorCoordLocal1.lean), [`SmoothYau_SphereMetric_ThreeFixedFormNorm`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/SphereMetric/ThreeFixedFormNorm.lean).
--
--   **Imports.** It imports the published bundle `Def_SmoothYau`; the bundles `OAIQ070A009` and `OAIQ070A010` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ070A014`; the statements `OAI_YauCounterexamples_CompactMetricAtlas_continuousFamily_varyingLaplacian_tendsto`, `OAI_YauCounterexamples_CompactMetricAtlas_realSpectralResolvent_eigenfunction`, `OAI.YauCounterexamples.exists_spherical_open_model`, `OAI.YauCounterexamples.exists_three_open_model` and `OAI.YauCounterexamples.three_nondegenerate_pinning_tensor`; the proofs of `OAI_YauCounterexamples_CompactMetricAtlas_continuousFamily_varyingLaplacian_tendsto`, `OAI_YauCounterexamples_CompactMetricAtlas_eventually_positive_factor_of_jets`, `OAI_YauCounterexamples_CompactMetricAtlas_eventually_product_positive_factor_of_eventual_jets`, `OAI_YauCounterexamples_CompactMetricAtlas_realSpectralResolvent_eigenfunction`, `OAI_YauCounterexamples_CompactMetricAtlas_represented_weighted_quintic_smooth`, `OAI_YauCounterexamples_CompactMetricAtlas_shiftedInverse_eigenfunction`, `OAI_YauCounterexamples_MetricIntegralAtlas_green`, `OAI_YauCounterexamples_conductivity_metric_in_smooth_neighborhood`, `OAI.YauCounterexamples.exists_annular_simple_pinned_family`, `OAI.YauCounterexamples.exists_spherical_fixed_witnesses`, `OAI.YauCounterexamples.exists_spherical_open_model`, `OAI_YauCounterexamples_exists_threeCoupled_interior_gradient_rank`, `OAI.YauCounterexamples.exists_three_fixed_witnesses`, `OAI.YauCounterexamples.exists_three_open_model`, `OAI.YauCounterexamples.exists_three_simple_pinned_family`, `OAI_YauCounterexamples_spherical_wave_lift_jets`, `OAI_YauCounterexamples_threeCoupled_profile_rank_dense`, `OAI_YauCounterexamples_threePower_eigen` and `OAI.YauCounterexamples.three_nondegenerate_pinning_tensor`.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit 1581d4c

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A009
import Definitions.Def_OAIQ070A010

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_SymmLChartTrivialization
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function Manifold Bundle
open scoped Topology ContDiff Distributions
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M] [T2Space M]

attribute [local instance] OAI.YauCounterexamples.tensorDualNorm
attribute [local instance] OAI.YauCounterexamples.tensorDualSpace
attribute [local instance] OAI.YauCounterexamples.tensorFormNorm
attribute [local instance] OAI.YauCounterexamples.tensorFormSpace
attribute [local instance] OAI.YauCounterexamples.tensorTangentDualAdd
attribute [local instance] OAI.YauCounterexamples.tensorTangentDualSmul
local instance tensorTangentFormAdd_r8bc728_1 (x : M) : IsTopologicalAddGroup (TangentForm (E:=E) x) :=
  inferInstance
local instance tensorTangentFormSmul_r8bc728_1 (x : M) : ContinuousSMul ℝ (TangentForm (E:=E) x) := inferInstance
def chartFormPush (p : M) (f : E → MetricForm E) (x : M) : TangentForm (E:=E) x :=
  (chartFormTrivialization (E:=E) p).symmL ℝ x (manifoldChartPush p f x)

omit [FiniteDimensional ℝ E] [T2Space M] in
lemma chartFormPush_zero (p : M) {f : E → MetricForm E} {x : M}
    (hx : manifoldChartPush p f x = 0) : chartFormPush p f x = 0 := by
  unfold chartFormPush
  rw [hx]
  exact ((chartFormTrivialization (E:=E) p).symmL ℝ x).map_zero

omit [FiniteDimensional ℝ E] in
lemma contMDiff_chartFormPush (p : M) {f : E → MetricForm E}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hs : tsupport f ⊆ (chartAt E p).target) :
    ContMDiff 𝓘(ℝ,E) (𝓘(ℝ,E).prod 𝓘(ℝ,MetricForm E)) ∞
      (fun x => TotalSpace.mk' (MetricForm E) x (chartFormPush p f x)) := by
  let : ∀ x : M, ContinuousAdd (TangentSpace 𝓘(ℝ,E) x →L[ℝ] ℝ) :=
    fun x => (tensorTangentDualAdd (E:=E) x).toContinuousAdd
  intro x
  by_cases hx : x ∈ (chartAt E p).source
  · have hx' : x ∈ (chartFormTrivialization (E:=E) p).baseSet := by
      rwa [chartFormTrivialization_baseSet]
    rw [(chartFormTrivialization (E:=E) p).contMDiffAt_section_iff hx']
    apply (contMDiff_manifoldChartPush p hf hc hs x).congr_of_eventuallyEq
    filter_upwards [(chartFormTrivialization (E:=E) p).open_baseSet.mem_nhds hx'] with y hy
    simp only [chartFormPush,Trivialization.symmL_apply _ hy,Trivialization.apply_mk_symm _ hy]
  · have ht : x ∉ tsupport (manifoldChartPush p f) := by
      intro hn
      obtain ⟨y,hy,hxy⟩ := manifoldChartPush_tsupport p hc hs hn
      exact hx (hxy ▸ (chartAt E p).map_target (hs hy))
    apply (contMDiffAt_zeroSection ℝ (E:=TangentForm (E:=E) (M:=M))).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp ht] with y hy
    exact congrArg (TotalSpace.mk' (MetricForm E) y) (chartFormPush_zero p hy)

omit [FiniteDimensional ℝ E] [T2Space M] in
lemma chartFormPush_trivialization (p : M) {f : E → MetricForm E} {x : M}
    (hx : x ∈ (chartAt E p).source) :
    (chartFormTrivialization (E:=E) p ⟨x,chartFormPush p f x⟩).2 = f ((chartAt E p) x) := by
  have hx' : x ∈ (chartFormTrivialization (E:=E) p).baseSet := by
    rwa [chartFormTrivialization_baseSet]
  simp only [chartFormPush,Trivialization.symmL_apply _ hx',Trivialization.apply_mk_symm _ hx',
    manifoldChartPush,Set.indicator_of_mem hx,Function.comp_apply]

omit [FiniteDimensional ℝ E] [T2Space M] in
lemma chartFormPush_eq_zero_of_not_source (p : M) {f : E → MetricForm E} {x : M}
    (hx : x ∉ (chartAt E p).source) : chartFormPush p f x = 0 := by
  exact chartFormPush_zero p (by simp [manifoldChartPush,hx])

omit [FiniteDimensional ℝ E] [T2Space M] in
lemma chartFormPush_pairing (p : M) {f : E → MetricForm E} {x : M}
    (hx : x ∈ (chartAt E p).source) (v w : TangentSpace 𝓘(ℝ,E) x) :
    chartFormPush p f x v w = f ((chartAt E p) x)
      ((trivializationAt E (TangentSpace 𝓘(ℝ,E)) p ⟨x,v⟩).2)
      ((trivializationAt E (TangentSpace 𝓘(ℝ,E)) p ⟨x,w⟩).2) := by
  have ht : x ∈ (trivializationAt E (TangentSpace 𝓘(ℝ,E)) p).baseSet := by
    simpa only [TangentBundle.trivializationAt_baseSet] using hx
  have hh := congrArg (fun B : MetricForm E => B
      ((trivializationAt E (TangentSpace 𝓘(ℝ,E)) p ⟨x,v⟩).2)
      ((trivializationAt E (TangentSpace 𝓘(ℝ,E)) p ⟨x,w⟩).2))
    (chartFormPush_trivialization (f:=f) p hx)
  simpa only [chartFormTrivialization_pairing p hx,Trivialization.symm_apply_apply_mk _ ht] using hh

omit [FiniteDimensional ℝ E] [T2Space M] in
lemma chartFormPush_symm (p : M) {f : E → MetricForm E}
    (hf : ∀ x v w, f x v w = f x w v) (x : M) (v w : TangentSpace 𝓘(ℝ,E) x) :
    chartFormPush p f x v w = chartFormPush p f x w v := by
  by_cases hx : x ∈ (chartAt E p).source
  · rw [chartFormPush_pairing p hx,chartFormPush_pairing p hx,hf]
  · rw [chartFormPush_eq_zero_of_not_source p hx]
    rfl

end


open Set Filter Function Manifold Bundle
open scoped Topology ContDiff

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ChartTensorCoordLocal1
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples


section
open Set Filter Function Manifold Bundle TopologicalSpace
open scoped Topology ContDiff Distributions
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M] [T2Space M]

variable (g : SmoothMetric E M) (p : M) (K : Compacts E)

attribute [local instance] OAI.YauCounterexamples.instNormedAddCommGroupContinuousLinearMapRealId_solutions
attribute [local instance] OAI.YauCounterexamples.instNormedSpaceRealContinuousLinearMapId_solutions
attribute [local instance] OAI.YauCounterexamples.instNormedAddCommGroupMetricForm
attribute [local instance] OAI.YauCounterexamples.instNormedSpaceRealMetricForm
attribute [local instance] OAI.YauCounterexamples.instIsTopologicalAddGroupContinuousLinearMapRealIdTangentSpaceModelWithCornersSelf_solutions
local instance instContinuousSMulRealContinuousLinearMapIdTangentSpaceModelWithCornersSelf_solutions_r8bc728_1 (x : M) : ContinuousSMul ℝ (TangentSpace 𝓘(ℝ,E) x →L[ℝ] ℝ) := inferInstance
local instance instIsTopologicalAddGroupTangentForm_r8bc728_1 (x : M) : IsTopologicalAddGroup (TangentForm (E:=E) x) := inferInstance
local instance instContinuousSMulRealTangentForm_r8bc728_1 (x : M) : ContinuousSMul ℝ (TangentForm (E:=E) x) := inferInstance
omit [T2Space M] in
lemma chartTensorForm_pos (hK : (K : Set E) ⊆ (chartAt E p).target)
    (H : 𝓓_{K}(E,MetricForm E)) (hH : chartTensorPositive g p K H)
    (x : M) (v : TangentSpace 𝓘(ℝ,E) x) (hv : v ≠ 0) :
    0 < (g.inner x + chartFormPush p (fun y => symmetrizeMetricForm (H y)) x) v v := by
  by_cases hx : x ∈ (chartAt E p).source
  · by_cases hy : (chartAt E p) x ∈ (K : Set E)
    · have hx' : x ∈ (trivializationAt E (TangentSpace 𝓘(ℝ,E)) p).baseSet := by
        simpa only [TangentBundle.trivializationAt_baseSet] using hx
      let e := (trivializationAt E (TangentSpace 𝓘(ℝ,E)) p).continuousLinearEquivAt ℝ x hx'
      have hne : e v ≠ 0 := by simpa only [ne_eq,EmbeddingLike.map_eq_zero_iff] using hv
      have hh := hH _ hy (e v) (Submodule.mem_top) hne
      have hr : chartTrivMetricForm g p ((chartAt E p) x) (e v) (e v) = g.inner x v v := by
        rw [chartTrivMetricForm_pairing g p (hK hy),(chartAt E p).left_inv hx]
        change g.inner x (e.symm (e v)) (e.symm (e v)) = _
        rw [e.symm_apply_apply]
      change 0 < g.inner x v v + chartFormPush p (fun y => symmetrizeMetricForm (H y)) x v v
      rw [chartFormPush_pairing p hx]
      change 0 < chartTrivMetricForm g p ((chartAt E p) x) (e v) (e v) +
        symmetrizeMetricForm (H ((chartAt E p) x)) (e v) (e v) at hh
      rw [hr] at hh
      simpa only [e,Trivialization.continuousLinearEquivAt_apply] using hh
    · have hz : chartFormPush p (fun y => symmetrizeMetricForm (H y)) x = 0 := by
        apply chartFormPush_zero
        simp [manifoldChartPush,hx,H.zero_on_compl hy]
      rw [hz]
      change 0 < g.inner x v v + (0 : ℝ)
      simpa only [add_zero] using g.pos x v hv
  · rw [chartFormPush_eq_zero_of_not_source p hx]
    change 0 < g.inner x v v + (0 : ℝ)
    simpa only [add_zero] using g.pos x v hv

def chartTensorMetric (hK : (K : Set E) ⊆ (chartAt E p).target)
    (H : 𝓓_{K}(E,MetricForm E)) (hH : chartTensorPositive g p K H) : SmoothMetric E M where
  inner x := g.inner x + chartFormPush p (fun y => symmetrizeMetricForm (H y)) x
  symm x v w := by
    change g.inner x v w + _ = g.inner x w v + _
    rw [g.symm x v w]
    congr 1
    exact chartFormPush_symm p (fun y => symmetrizeMetricForm_symm (H y)) x v w
  pos := chartTensorForm_pos g p K hK H hH
  isVonNBounded x := positive_bilinear_bounded (show E →L[ℝ] E →L[ℝ] ℝ from
    g.inner x + chartFormPush p (fun y => symmetrizeMetricForm (H y)) x)
    (chartTensorForm_pos g p K hK H hH x)
  contMDiff := by
    let : ∀ x : M, ContinuousAdd (TangentSpace 𝓘(ℝ,E) x →L[ℝ] ℝ) :=
      fun x => (tensorTangentDualAdd (E:=E) x).toContinuousAdd
    apply g.contMDiff.add_section
    apply contMDiff_chartFormPush
    · exact symmetrizeMetricForm.contDiff.comp H.contDiff
    · exact H.hasCompactSupport.comp_left (by simp)
    · exact (tsupport_comp_subset (g := symmetrizeMetricForm) symmetrizeMetricForm.map_zero H).trans (H.tsupport_subset.trans hK)
end


open Set Filter Function Manifold Bundle TopologicalSpace
open scoped Topology ContDiff Distributions

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Limits_RestrictedPinningPencil
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function Manifold Bundle
open scoped Topology ContDiff BoundedContinuousFunction
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [CompactSpace M] [T2Space M]
variable (I : MetricIntegralAtlas (E := E) (M := M)) (g : SmoothMetric E M)
variable {u : M → ℝ} {U : Set M}

def pinningEnergyBilin (K : pinningTensorSpace g u U) :
    LinearMap.BilinForm ℝ (RealSmoothFunctions E M) :=
  LinearMap.mk₂ ℝ (fun a b => I.mean g (fun x =>
      g.inner x (smoothMetricGradientLM g x a) (K.val x (smoothMetricGradientLM g x b))))
    (by
      intro a b c
      simp only [map_add]
      refine Eq.trans ?_ (I.mean_add g _ _
        (contMDiff_tensorEnergy g K.val K.property.1 a.contMDiff c.contMDiff).continuous
        (contMDiff_tensorEnergy g K.val K.property.1 b.contMDiff c.contMDiff).continuous)
      apply congrArg (I.mean g)
      funext x
      exact congrArg (fun L : E →L[ℝ] ℝ => L (K.val x (smoothMetricGradientLM g x c)))
        ((show E →L[ℝ] E →L[ℝ] ℝ from g.inner x).map_add
          (smoothMetricGradientLM g x a) (smoothMetricGradientLM g x b)))
    (by
      intro r a b
      simp only [map_smul]
      refine Eq.trans ?_ (I.mean_const_mul g r _
        (contMDiff_tensorEnergy g K.val K.property.1 a.contMDiff b.contMDiff).continuous)
      apply congrArg (I.mean g)
      funext x
      exact congrArg (fun L : E →L[ℝ] ℝ => L (K.val x (smoothMetricGradientLM g x b)))
        ((show E →L[ℝ] E →L[ℝ] ℝ from g.inner x).map_smul r (smoothMetricGradientLM g x a)))
    (by
      intro a b c
      simp only [map_add]
      refine Eq.trans ?_ (I.mean_add g _ _
        (contMDiff_tensorEnergy g K.val K.property.1 a.contMDiff b.contMDiff).continuous
        (contMDiff_tensorEnergy g K.val K.property.1 a.contMDiff c.contMDiff).continuous)
      apply congrArg (I.mean g)
      funext x
      let L : E →L[ℝ] ℝ := (show E →L[ℝ] ℝ from g.inner x (smoothMetricGradientLM g x a)).comp
        (show E →L[ℝ] E from K.val x)
      exact L.map_add (smoothMetricGradientLM g x b) (smoothMetricGradientLM g x c))
    (by
      intro r a b
      simp only [map_smul]
      refine Eq.trans ?_ (I.mean_const_mul g r _
        (contMDiff_tensorEnergy g K.val K.property.1 a.contMDiff b.contMDiff).continuous)
      apply congrArg (I.mean g)
      funext x
      let L : E →L[ℝ] ℝ := (show E →L[ℝ] ℝ from g.inner x (smoothMetricGradientLM g x a)).comp
        (show E →L[ℝ] E from K.val x)
      exact L.map_smul r (smoothMetricGradientLM g x b))

def pinningEnergyPencil : pinningTensorSpace g u U →ₗ[ℝ]
    LinearMap.BilinForm ℝ (RealSmoothFunctions E M) where
  toFun := pinningEnergyBilin I g
  map_add' K L := by
    ext a b
    change I.mean g (fun x => g.inner x (metricGradient g a x)
      ((K.val+L.val) x (metricGradient g b x))) = _
    simp only [Pi.add_apply,add_apply,map_add]
    exact I.mean_add g _ _
      (contMDiff_tensorEnergy g K.val K.property.1 a.contMDiff b.contMDiff).continuous
      (contMDiff_tensorEnergy g L.val L.property.1 a.contMDiff b.contMDiff).continuous
  map_smul' r K := by
    ext a b
    change I.mean g (fun x => g.inner x (metricGradient g a x)
      ((r • K.val) x (metricGradient g b x))) = _
    simp only [Pi.smul_apply,smul_apply,map_smul,smul_eq_mul]
    exact I.mean_const_mul g r _
      (contMDiff_tensorEnergy g K.val K.property.1 a.contMDiff b.contMDiff).continuous

end


open Set Filter Function Manifold Bundle MeasureTheory
open scoped Topology ContDiff BoundedContinuousFunction
variable {W : Type*} [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]

def restrictedPinningPencil
    {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
    [CompactSpace M] [T2Space M]
    (I : MetricIntegralAtlas (E := E) (M := M)) (g : SmoothMetric E M)
    {u : M → ℝ} {U : Set M} (σ : W →ₗ[ℝ] RealSmoothFunctions E M) :
    pinningTensorSpace g u U →ₗ[ℝ] LinearMap.BilinForm ℝ W where
  toFun K := (pinningEnergyPencil I g K).comp σ σ
  map_add' K L := by
    ext a b
    change pinningEnergyPencil I g (K+L) (σ a) (σ b) = _
    rw [map_add]
    rfl
  map_smul' r K := by
    ext a b
    change pinningEnergyPencil I g (r • K) (σ a) (σ b) = _
    rw [map_smul]
    rfl

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_DifferentialEq_SphericalOpenFormNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function Manifold Bundle TopologicalSpace BoxIntegral
open scoped Topology ContDiff Distributions
namespace YauCounterexamples
def sphericalTensorMetric (g₀ : SmoothMetric (Euclidean 3) (Sphere 3))
    (H : SphericalPositiveTensor g₀) : SmoothMetric (Euclidean 3) (Sphere 3) :=
  chartTensorMetric g₀ sourcePole sphericalTensorSupport
    ((sphere_chart_target sourcePole).symm ▸ subset_univ _) H.val H.property
end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_SphereMetric_ThreeFixedFormNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples


section
open Set Filter Function Manifold Bundle TopologicalSpace BoxIntegral Metric
open scoped Topology ContDiff Distributions
def threeTensorMetric (R : ℝ) (H : ThreePositiveTensor R) : SmoothMetric ThreeModel ThreeManifold :=
  chartTensorMetric threeBackgroundMetric threeProfileCenter (threeTensorSupport R)
    ((three_chart_target threeProfileCenter).symm ▸ subset_univ _) H.val H.property
end


open Set Filter Function Manifold Bundle TopologicalSpace BoxIntegral
open scoped Topology ContDiff Distributions ENNReal NNReal

end YauCounterexamples
end

end OAI
end


