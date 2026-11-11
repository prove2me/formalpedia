-- Prove2me | Definitions.Def_OAIQ239Tc015
-- name    : OAIQ239Tc015
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T22:25:28.03423+00:00
-- url     : https://prove2.me/theorems/4106c245-ef77-4e76-853d-662b5e4ee7b1
-- title:
--   Definitions bundle OAIQ239Tc015 of the split of OpenAI, Taming implies compatibility on four-manifolds
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.TamingCompatibility.taming_implies_compatibility`, carved from OpenAI's openai/math development (OpenAI, *Taming implies compatibility on four-manifolds*, OpenAI Math Release, October 6, 2026, result family 342, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 60 declarations of OpenAI's Lean: 18 definitions, 1 inductive type or structure, 1 instance and 40 theorems. The definitions and types are `OAI.TamingCompatibility.GeometricChart.normalMetric`, `OAI.TamingCompatibility.GeometricChart.pairLinear`, `OAI.TamingCompatibility.GeometricChart.rawScalar`, `OAI.TamingCompatibility.GeometricChart.scalarLinear`, `OAI.TamingCompatibility.GeometricChart.scalarSchwartz`, `OAI.TamingCompatibility.HilbertSobolev.sobolevEval`, `OAI.TamingCompatibility.HodgeChart.Data`, `OAI.TamingCompatibility.HodgeGeometricCoefficients.operator`, `OAI.TamingCompatibility.HodgeGeometricCoefficients.starredField`, `OAI.TamingCompatibility.ManifoldLocalization.chartComponent`, `OAI.TamingCompatibility.ManifoldLocalization.chartRecover`, `OAI.TamingCompatibility.ManifoldLocalization.globalH1`, `OAI.TamingCompatibility.ManifoldLocalization.globalL2`, `OAI.TamingCompatibility.ManifoldLocalization.h1ToL2`, `OAI.TamingCompatibility.ManifoldLocalization.localizeH1`, `OAI.TamingCompatibility.ManifoldLocalization.localizeL2`, `OAI.TamingCompatibility.ManifoldLocalization.localizedLinear`, `OAI.TamingCompatibility.hermitianMetric`, `OAI.TamingCompatibility.unitEvaluation`.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: `TamingCompatibility_Charts_ChartComponent`, `TamingCompatibility_Charts_ChartTestPairing`, `TamingCompatibility_Charts_ChartUnitaryData`, `TamingCompatibility_Charts_Coordinates`, `TamingCompatibility_Charts_GeometricCutoff`, `TamingCompatibility_DifferentialForms_ComplexEquiv`, `TamingCompatibility_DifferentialForms_FramePairing`, `TamingCompatibility_DifferentialForms_GeometricFrameTest`, `TamingCompatibility_DifferentialForms_MetricCoords`, `TamingCompatibility_DifferentialForms_PositiveFunctions`, `TamingCompatibility_Elliptic_DerivativeIndex`, `TamingCompatibility_Elliptic_MatrixGarding`, `TamingCompatibility_Elliptic_RealSobolevLift`, `TamingCompatibility_Elliptic_SobolevBounded`, `TamingCompatibility_Functional_ChartNormalTest`, `TamingCompatibility_Hodge_HodgeFrameDifferential`, `TamingCompatibility_Hodge_HodgeFrameTest`, `TamingCompatibility_Hodge_HodgeGeometricCoefficients`, `TamingCompatibility_Hodge_HodgeGeometricGarding`, `TamingCompatibility_Hodge_HodgeWedgeEnergy`, `TamingCompatibility_Hodge_LocalCodifferential`.
--
--   **Imports.** It imports the published bundle `Def_TamingCompatibility`; the bundles `OAIQ239Tc010`, `OAIQ239Tc011` and `OAIQ239Tc012` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ239Tc017`, `OAIQ239Tc018`, `OAIQ239Tc019` and `OAIQ239Tc020`; the proof of `OAI.TamingCompatibility.HilbertSobolev.parameter_energy_two_jet`.
-- source:
--   OpenAI, Taming implies compatibility on four-manifolds, OpenAI Math Release, October 6, 2026, https://github.com/openai/math (result family 342; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Taming-implies-compatibility-on-four-manifolds-October-6-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit 7ef5c0c

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc010
import Definitions.Def_OAIQ239Tc011
import Definitions.Def_OAIQ239Tc012

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_Coordinates
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open _root_.MeasureTheory
open scoped SchwartzMap Laplacian ENNReal
open scoped BigOperators
namespace TamingCompatibility.ManifoldLocalization
open _root_.MeasureTheory Set Function
open scoped Topology Manifold ContDiff SchwartzMap
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X]
  [IsManifold Model ∞ X] [T2Space X] [CompactSpace X]
variable (A : FiniteCharts X) (k : ℕ)

omit [T2Space X] in
def localizedLinear (p : A.centers) :
    ManifoldForms.smoothForms X k →ₗ[ℝ] 𝓢(Space,CoordinateFiber k) where
  toFun α := SchwartzMap.postcompCLM (formCoordinates k) (localizedSchwartz A p α.val α.property)
  map_add' α β := by
    apply SchwartzMap.ext
    intro y
    change formCoordinates k (localizedFunction A p (α.val + β.val) y) = _
    rw [localizedFunction_add]
    exact (formCoordinates k).map_add _ _
  map_smul' c α := by
    apply SchwartzMap.ext
    intro y
    change formCoordinates k (localizedFunction A p (c • α.val) y) = _
    rw [localizedFunction_smul]
    exact (formCoordinates k).map_smul _ _

omit [T2Space X] in
def localizeL2 : ManifoldForms.smoothForms X k →ₗ[ℝ] ChartL2 A k :=
  (PiLp.continuousLinearEquiv 2 ℝ
    (fun _ : A.centers => Lp (CoordinateFiber k) 2 (volume : Measure Space))).symm.toLinearMap ∘ₗ
  LinearMap.pi (fun p => (SchwartzMap.toLpCLM ℝ (CoordinateFiber k) 2 (volume : Measure Space)).toLinearMap ∘ₗ
    localizedLinear A k p)

omit [T2Space X] in
lemma localizeL2_apply (α : ManifoldForms.smoothForms X k) (p : A.centers) :
    localizeL2 A k α p = (localizedLinear A k p α).toLp 2 := rfl

def globalL2 : Submodule ℝ (ChartL2 A k) :=
  (LinearMap.range (localizeL2 A k)).topologicalClosure

end TamingCompatibility.ManifoldLocalization

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Elliptic_DerivativeIndex
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open _root_.MeasureTheory
open scoped SchwartzMap Laplacian ENNReal
open scoped BigOperators
namespace TamingCompatibility.ManifoldLocalization
open _root_.MeasureTheory Set Function LineDeriv
open scoped Topology Manifold ContDiff SchwartzMap
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X]
  [IsManifold Model ∞ X] [T2Space X] [CompactSpace X]
variable (A : FiniteCharts X) (k : ℕ)

omit [T2Space X] in
def localizeH1 : ManifoldForms.smoothForms X k →ₗ[ℝ] ChartH1 A k :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : DerivativeIndex => ChartL2 A k)).symm.toLinearMap ∘ₗ
  LinearMap.pi (fun j =>
    (PiLp.continuousLinearEquiv 2 ℝ
      (fun _ : A.centers => Lp (CoordinateFiber k) 2 (volume : Measure Space))).symm.toLinearMap ∘ₗ
    LinearMap.pi (fun p =>
      (SchwartzMap.toLpCLM ℝ (CoordinateFiber k) 2 (volume : Measure Space)).toLinearMap ∘ₗ
      (jetComponent k j).toLinearMap ∘ₗ localizedLinear A k p))

omit [T2Space X] in
lemma localizeH1_apply (α : ManifoldForms.smoothForms X k) (j : DerivativeIndex) (p : A.centers) :
    localizeH1 A k α j p = (jetComponent k j (localizedLinear A k p α)).toLp 2 := rfl

def globalH1 : Submodule ℝ (ChartH1 A k) :=
  (LinearMap.range (localizeH1 A k)).topologicalClosure

instance globalH1_complete : CompleteSpace (globalH1 A k) :=
  (LinearMap.range (localizeH1 A k)).isClosed_topologicalClosure.completeSpace_coe

omit [T2Space X] in
lemma zeroth_mem_globalL2 (u : globalH1 A k) : zeroth A k u.val ∈ globalL2 A k := by
  apply ((LinearMap.range (localizeH1 A k)).topologicalClosure_minimal
    (t := (globalL2 A k).comap (zeroth A k).toLinearMap) ?_ ?_) u.property
  · rintro _ ⟨α,rfl⟩
    exact Submodule.le_topologicalClosure _ ⟨α,rfl⟩
  · exact (LinearMap.range (localizeL2 A k)).isClosed_topologicalClosure.preimage
      (zeroth A k).continuous

def h1ToL2 : globalH1 A k →L[ℝ] globalL2 A k :=
  ((zeroth A k).comp (globalH1 A k).subtypeL).codRestrict _ (zeroth_mem_globalL2 A k)

omit [T2Space X] in
lemma jetDistribution_localize (α : ManifoldForms.smoothForms X k)
    (j : DerivativeIndex) (p : A.centers) :
    jetDistribution A k j p (localizeH1 A k α) =
      SchwartzMap.toTemperedDistributionCLM Space (CoordinateFiber k) volume
        (jetComponent k j (localizedLinear A k p α)) := by
  exact Lp.toTemperedDistribution_toLp_eq _

omit [T2Space X] in
lemma derivative_relation (u : globalH1 A k) (i : Fin (Module.finrank ℝ Space)) (p : A.centers) :
    lineDerivOpCLM ℝ 𝓢'(Space,CoordinateFiber k) (stdOrthonormalBasis ℝ Space i)
      (jetDistribution A k none p u.val) = jetDistribution A k (some i) p u.val := by
  let D := (lineDerivOpCLM ℝ 𝓢'(Space,CoordinateFiber k) (stdOrthonormalBasis ℝ Space i)) ∘L
    jetDistribution A k none p - jetDistribution A k (some i) p
  have hz : LinearMap.range (localizeH1 A k) ≤ LinearMap.ker D.toLinearMap := by
    rintro _ ⟨α,rfl⟩
    change lineDerivOpCLM ℝ 𝓢'(Space,CoordinateFiber k) (stdOrthonormalBasis ℝ Space i)
      (jetDistribution A k none p (localizeH1 A k α)) -
      jetDistribution A k (some i) p (localizeH1 A k α) = 0
    rw [sub_eq_zero, jetDistribution_localize, jetDistribution_localize]
    exact TemperedDistribution.lineDerivOp_toTemperedDistributionCLM_eq _ _
  have h := (LinearMap.range (localizeH1 A k)).topologicalClosure_minimal hz D.isClosed_ker u.property
  exact sub_eq_zero.mp h

end TamingCompatibility.ManifoldLocalization

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_ChartComponent
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional _root_.OAI.TamingCompatibility.HilbertSobolev.localSolutionSpace_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open _root_.MeasureTheory
open scoped SchwartzMap Laplacian ENNReal
open scoped BigOperators
namespace TamingCompatibility.ManifoldLocalization
open _root_.MeasureTheory TemperedDistribution Set Function HilbertSobolev
open scoped Topology Manifold ContDiff SchwartzMap LineDeriv Laplacian RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X]
  [IsManifold Model ∞ X] [T2Space X] [CompactSpace X]
variable (A : FiniteCharts X) (k : ℕ)

def chartComponent (j : DerivativeIndex) (p : A.centers) :
    globalH1 A k →L[ℝ] H Space (CoordinateFiber k) 0 :=
  PiLp.proj 2 _ p ∘L PiLp.proj 2 _ j ∘L (globalH1 A k).subtypeL

def chartRecover (p : A.centers) : globalH1 A k →L[ℝ] H Space (CoordinateFiber k) 1 :=
  (reindex (E := Space) (F := CoordinateFiber k) (0-1) (0+1)).toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ ∘L
    ((inclusion (E := Space) (F := CoordinateFiber k) (show (0:ℝ)-1 ≤ 0 by norm_num)).restrictScalars ℝ ∘L
        chartComponent A k none p -
      ((2*Real.pi)^2)⁻¹ • ∑ i : Fin (Module.finrank ℝ Space),
        (derivative (F := CoordinateFiber k) 0 (stdOrthonormalBasis ℝ Space i)).restrictScalars ℝ ∘L
          chartComponent A k (some i) p)

omit [T2Space X] in
lemma chartRecover_apply (p : A.centers) (u : globalH1 A k) :
    chartRecover A k p u = recover 0 (u.val none p) (fun i => u.val (some i) p) := by
  simp only [chartRecover, chartComponent, ContinuousLinearMap.comp_apply,
    _root_.sub_apply, _root_.smul_apply,
    _root_.sum_apply]
  unfold recover
  rfl

omit [T2Space X] in
lemma chartRecover_distribution (p : A.centers) (u : globalH1 A k) :
    toDistribution Space (CoordinateFiber k) 1 (chartRecover A k p u) =
      Lp.toTemperedDistributionCLM (CoordinateFiber k) volume 2 (u.val none p) := by
  rw [chartRecover_apply]
  have hr := recover_distribution (E := Space) (F := CoordinateFiber k) 0
    (u.val none p) (fun i => u.val (some i) p)
  rw [show (0 : ℝ) + 1 = 1 by ring] at hr
  rw [hr]
  have hz (w : H Space (CoordinateFiber k) 0) :
      toDistribution Space (CoordinateFiber k) 0 w =
        Lp.toTemperedDistributionCLM (CoordinateFiber k) volume 2 w := by
    simp [toDistribution]
  simp only [hz]
  have hd (i : Fin (Module.finrank ℝ Space)) := derivative_relation A k u i p
  change ∀ i : Fin (Module.finrank ℝ Space),
    ∂_{stdOrthonormalBasis ℝ Space i}
      (Lp.toTemperedDistributionCLM (CoordinateFiber k) volume 2 (u.val none p)) =
      Lp.toTemperedDistributionCLM (CoordinateFiber k) volume 2 (u.val (some i) p) at hd
  simp only [← hd]
  rw [← TemperedDistribution.laplacian_eq_sum (stdOrthonormalBasis ℝ Space)]
  exact EuclideanGreen.green_helmholtz _

omit [T2Space X] in
lemma chartRecover_inclusion (p : A.centers) (u : globalH1 A k) :
    inclusion (show (0:ℝ) ≤ 1 by norm_num) (chartRecover A k p u) = u.val none p := by
  apply toDistribution_injective (E := Space) (F := CoordinateFiber k) 0
  rw [toDistribution_inclusion, chartRecover_distribution]
  simp [toDistribution]

omit [T2Space X] in
lemma localizedLinear_zero_off (p : A.centers) (α : ManifoldForms.smoothForms X k)
    (y : Space) (hy : y ∉ coordinateSupport A p) : localizedLinear A k p α y = 0 := by
  change formCoordinates k (localizedFunction A p α.val y) = 0
  suffices h : localizedFunction A p α.val y = 0 by rw [h, map_zero]
  unfold localizedFunction
  by_cases ht : y ∈ (extChartAt Model p.val).target
  · rw [indicator_of_mem ht]
    have hn : (extChartAt Model p.val).symm y ∉ tsupport (A.partition p) := by
      intro h
      exact hy ⟨_,h,(extChartAt Model p.val).right_inv ht⟩
    rw [image_eq_zero_of_notMem_tsupport hn, zero_smul]
  · rw [indicator_of_notMem ht]

omit [T2Space X] in
lemma chart_restore (p : A.centers) (u : globalH1 A k) :
    LocalRestriction.restore volume (coordinateSupport A p) (coordinateSupport_compact A p).measurableSet
      (LocalRestriction.restrict volume (coordinateSupport A p) (coordinateSupport_compact A p).measurableSet
        (u.val none p)) = u.val none p := by
  let R := LocalRestriction.restrict (F := CoordinateFiber k) volume
    (coordinateSupport A p) (coordinateSupport_compact A p).measurableSet
  let D : ChartH1 A k →L[ℝ] Lp (CoordinateFiber k) 2 (volume : Measure Space) :=
    ((ContinuousLinearMap.adjoint R) ∘L R - ContinuousLinearMap.id ℝ _) ∘L
      PiLp.proj 2 _ p ∘L PiLp.proj 2 _ none
  have ht : LinearMap.range (localizeH1 A k) ≤ LinearMap.ker D.toLinearMap := by
    rintro _ ⟨α,rfl⟩
    change LocalRestriction.restore volume (coordinateSupport A p) _
      (R ((localizedLinear A k p α).toLp 2 volume)) - (localizedLinear A k p α).toLp 2 volume = 0
    rw [sub_eq_zero]
    apply LocalRestriction.restore_restrict
    filter_upwards [(localizedLinear A k p α).coeFn_toLp 2 volume] with y hy
    intro hn
    rw [hy]
    exact localizedLinear_zero_off A k p α y hn
  have h := (LinearMap.range (localizeH1 A k)).topologicalClosure_minimal ht D.isClosed_ker u.property
  exact sub_eq_zero.mp h

omit [T2Space X] in
lemma chartComponent_compact (p : A.centers) : IsCompactOperator (chartComponent A k none p) := by
  have hc := LocalRellich.realize_compact (F := CoordinateFiber k)
    (coordinateSupport A p) (coordinateSupport_compact A p) (show (0:ℝ) < 1 by norm_num)
  have h := (hc.comp_clm (chartRecover A k p)).clm_comp
    (LocalRestriction.restore volume (coordinateSupport A p) (coordinateSupport_compact A p).measurableSet)
  have he : (chartComponent A k none p : globalH1 A k → H Space (CoordinateFiber k) 0) =
      (LocalRestriction.restore volume (coordinateSupport A p) (coordinateSupport_compact A p).measurableSet) ∘
        (LocalRellich.realize (coordinateSupport A p) (coordinateSupport_compact A p).measurableSet
          (show (0:ℝ) ≤ 1 by norm_num)) ∘ (chartRecover A k p) := by
    funext u
    change u.val none p = _
    dsimp only [Function.comp_def, LocalRellich.realize, ContinuousLinearMap.comp_apply]
    change u.val none p = LocalRestriction.restore volume (coordinateSupport A p) _
      (LocalRestriction.restrict volume (coordinateSupport A p) _
        (inclusion (show (0:ℝ) ≤ 1 by norm_num) (chartRecover A k p u)))
    rw [chartRecover_inclusion, chart_restore]
  rw [he]
  exact h

end TamingCompatibility.ManifoldLocalization

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_MetricCoords
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
open scoped Manifold ContDiff
noncomputable section
open scoped Manifold ContDiff Topology
open Filter Set
attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid
noncomputable section
open scoped Manifold ContDiff Topology
open Bundle Filter Set
noncomputable section
open Set
namespace TamingCompatibility
open Bundle Set
open scoped Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X]
  [IsManifold Model ∞ X]

theorem IsSmooth.associatedBilinear {α : TwoForm X} (hα : IsSmooth α)
    (J : AlmostComplexStructure X) :
    ContMDiff Model (Model.prod 𝓘(ℝ, Space →L[ℝ] Space →L[ℝ] ℝ)) ∞
      (fun x => TotalSpace.mk' (Space →L[ℝ] Space →L[ℝ] ℝ) x (associatedBilinear J α x)) := by
  intro x
  rw [contMDiffAt_section, contMDiffAt_iff_source]
  simp only [Model, modelWithCornersSelf_coe, Set.range_id, contMDiffWithinAt_univ,
    contMDiffAt_iff_contDiffAt, Function.comp_def, hom_trivializationAt_apply]
  exact (hα.metricCoords J x).contDiffAt (extChartAt_target_mem_nhds x)

def hermitianMetric (J : AlmostComplexStructure X) (α : TwoForm X)
    (hα : IsSmooth α) (ht : Tames α J) :
    ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type) := by
  letI (x : X) : NormedAddCommGroup (TangentSpace Model x) :=
    inferInstanceAs (NormedAddCommGroup Space)
  letI (x : X) : NormedSpace ℝ (TangentSpace Model x) :=
    inferInstanceAs (NormedSpace ℝ Space)
  letI (x : X) : FiniteDimensional ℝ (TangentSpace Model x) :=
    inferInstanceAs (FiniteDimensional ℝ Space)
  letI (x : X) : Nontrivial (TangentSpace Model x) :=
    inferInstanceAs (Nontrivial Space)
  exact {
    inner := fun x => associatedBilinear J (invariantPart J α) x
    symm := (invariantPart_isInvariant J α).associatedBilinear_symm
    pos := (tames_invariantPart ht).associatedBilinear_pos
    isVonNBounded := fun x => bilinear_unitBall_isVonNBounded _
      ((tames_invariantPart ht).associatedBilinear_pos x)
    contMDiff := (hα.invariantPart J).associatedBilinear J }

end TamingCompatibility

end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_ComplexEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped Manifold ContDiff
open scoped Manifold ContDiff Topology
open Filter Set
attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid
open scoped Manifold ContDiff Topology
open Bundle Filter Set
open Set
open Bundle Set Filter
open scoped Topology
open Set _root_.MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology
open scoped BigOperators
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open ContinuousAlternatingMap
namespace TamingCompatibility.MetricForms
open MetricModel ContinuousAlternatingMap
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
lemma pairing_sub_right (g : Metric E) {k : ℕ} (a b c : Form E k) :
    pairing g a (b-c) = pairing g a b - pairing g a c := by
  rw [pairing_symm,pairing_sub_left,pairing_symm g b a,pairing_symm g c a]
end TamingCompatibility.MetricForms

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_LocalCodifferential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section

section

noncomputable section

namespace TamingCompatibility.SmoothHodge
open MetricModel MetricForms MetricHodge
open scoped ContDiff
variable {E D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup D] [NormedSpace ℝ D]

attribute [local instance] OAI.TamingCompatibility.SmoothHodge.instFiniteDimensionalRealContinuousMultilinearMapFin_solutions
attribute [local instance] OAI.TamingCompatibility.SmoothHodge.instFiniteDimensionalRealContinuousAlternatingMapFin_solutions
lemma starThreeCLM_contDiffOn (g : D → Metric E) (J : D → E →L[ℝ] E)
    (hdim : Module.finrank ℝ E = 4) {U : Set D} (hU : IsOpen U)
    (hg : ContDiffOn ℝ ∞ (fun x => (g x).bilinear) U) (hJ : ContDiffOn ℝ ∞ J U)
    (hJs : ∀ x ∈ U, ∀ u, J x (J x u) = -u)
    (hgJ : ∀ x ∈ U, ∀ u v, (g x).bilinear (J x u) (J x v) = (g x).bilinear u v)
    {F : D → MetricForms.Form E 2} (hF : ContDiffOn ℝ ∞ F U) :
    ContDiffOn ℝ ∞ (fun x => starThreeCLM (g x) (F x)) U := by
  apply contDiffOn_clm_apply.mpr
  intro a
  exact starThree_contDiffOn g J hdim hU hg hJ hJs hgJ hF contDiffOn_const
end TamingCompatibility.SmoothHodge

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Elliptic_MatrixGarding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open _root_.MeasureTheory
open scoped SchwartzMap
namespace TamingCompatibility.MatrixEnergy
open EuclideanEnergy

lemma comparison_pointwise (c : Fin 4 → Pair →L[ℝ] V)
    (a : Fin 4 → V → Pair →L[ℝ] V) (b : V → Pair →L[ℝ] V)
    (A B : S) (x : V) {δ C : ℝ} (ha : ∀ i, ‖a i x - c i‖ ≤ δ) (hb : ‖b x‖ ≤ C) :
    ‖constantSystem c A B x‖^2 ≤ 2 * ‖system a b A B x‖^2 +
      16*δ^2*gradientEnergy A B x + 4*C^2*((A x)^2+(B x)^2) := by
  let E : V := ∑ i, (a i x-c i) (pair (coordinateDeriv i A x) (coordinateDeriv i B x))
  let L : V := b x (pair (A x) (B x))
  have he : constantSystem c A B x = system a b A B x + -(E+L) := by
    simp only [constantSystem,system,E,L,sub_apply,Finset.sum_sub_distrib]
    abel
  have h0 := norm_add_sq_le (system a b A B x) (-(E+L))
  rw [← he,norm_neg] at h0
  have h1 := norm_add_sq_le E L
  have hE := principalError_bound (fun i y => a i y-c i) A B x ha
  have hL := lowerError_bound b A B x hb
  change ‖E‖^2 ≤ _ at hE
  change ‖L‖^2 ≤ _ at hL
  nlinarith

end TamingCompatibility.MatrixEnergy

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_ChartUnitaryData
attribute [-instance] _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section

section

noncomputable section
namespace TamingCompatibility.GeometricChart
open ManifoldForms ManifoldLocalization ManifoldHodge
open Set MetricForms AntiInvariantFrame
open scoped Manifold ContDiff SchwartzMap
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

omit [T2Space X] in
lemma scalar_tsupport_subset (p : A.centers) (a : TwoForm X) (j : Fin 4) :
    tsupport (scalar A J α ht D p a j) ⊆ coordinateSupport A p := by
  apply closure_minimal _ (coordinateSupport_compact A p).isClosed
  intro x hx
  by_contra hn
  exact hx (scalar_zero_off A J α ht D p a j hn)

include hD in
omit [T2Space X] in
lemma scalar_smooth_compact (p : A.centers) (a : TwoForm X) (ha : IsSmooth a) (j : Fin 4) :
    ContDiff ℝ ∞ (scalar A J α ht D p a j) ∧ HasCompactSupport (scalar A J α ht D p a j) := by
  apply smooth_indicator_of_compact (D p).domain_open (coordinateSupport_compact A p)
    (coordinateSupport_domain A J α ht D hD p)
  · exact FormSmooth.contDiffOn_apply_two
      (localizedFunction_smooth_compact A p a ha).1.contDiffOn
      ((D p).frame_smooth 0) ((D p).frame_smooth j)
  · intro x _ hx
    rw [localizedFunction_zero_off A p a hx]
    rfl

def scalarSchwartz (p : A.centers) (a : TwoForm X) (ha : IsSmooth a) (j : Fin 4) :
    𝓢(Space,ℝ) :=
  (scalar_smooth_compact A J α ht D hD p a ha j).2.toSchwartzMap
    (scalar_smooth_compact A J α ht D hD p a ha j).1

omit [T2Space X] in
lemma scalarSchwartz_support (p : A.centers) (a : TwoForm X) (ha : IsSmooth a) (j : Fin 4) :
    tsupport (scalarSchwartz A J α ht D hD p a ha j) ⊆
      Metric.closedBall (extChartAt Model p.val p.val) (D p).radius :=
  (scalar_tsupport_subset A J α ht D p a j).trans (coordinateSupport_small A J α ht D hD p)
end TamingCompatibility.GeometricChart

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_GeometricFrameTest
attribute [-instance] _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section

section
noncomputable section
namespace TamingCompatibility.GeometricChart
open ManifoldForms ManifoldHodge AntiInvariantFrame LocalMatrixOperator Set
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α)
  (ht : Tames α J) (p : X) (D : Data J α ht p)

omit [T2Space X] in
lemma manifoldTest_anti (q : Space → EuclideanEnergy.Pair) :
    antiInvariantPart J (manifoldTest J α ht p D q) = manifoldTest J α ht p D q :=
  antiInvariantPart_idempotent J _

end TamingCompatibility.GeometricChart

end
end

section
noncomputable section

namespace TamingCompatibility.GeometricChart
open ManifoldForms ManifoldLocalization Set
open scoped Manifold ContDiff SchwartzMap
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

omit [CompactSpace X] in
lemma scalar_add (p : A.centers) (a b : TwoForm X) (j : Fin 4) :
    scalar A J α ht D p (a+b) j = scalar A J α ht D p a j + scalar A J α ht D p b j := by
  ext x
  unfold scalar
  by_cases hx : x ∈ (D p).domain
  · simp only [indicator_of_mem hx,Pi.add_apply,localizedFunction_add,ContinuousAlternatingMap.add_apply]
  · simp only [indicator_of_notMem hx,Pi.add_apply,add_zero]

omit [CompactSpace X] in
lemma scalar_smul (p : A.centers) (c : ℝ) (a : TwoForm X) (j : Fin 4) :
    scalar A J α ht D p (c • a) j = c • scalar A J α ht D p a j := by
  ext x
  unfold scalar
  by_cases hx : x ∈ (D p).domain
  · simp only [indicator_of_mem hx,Pi.smul_apply,localizedFunction_smul,ContinuousAlternatingMap.smul_apply]
  · simp only [indicator_of_notMem hx,Pi.smul_apply,smul_zero]

def scalarLinear (p : A.centers) (j : Fin 4) : smoothForms X 2 →ₗ[ℝ] 𝓢(Space,ℝ) where
  toFun a := scalarSchwartz A J α ht D hD p a.val a.property j
  map_add' a b := by
    ext x
    exact congrFun (scalar_add A J α ht D p a.val b.val j) x
  map_smul' c a := by
    ext x
    exact congrFun (scalar_smul A J α ht D p c a.val j) x

def pairLinear (p : A.centers) : smoothForms X 2 →ₗ[ℝ] 𝓢(Space,ScalarPair.F) :=
  (SchwartzMap.postcompCLM (ScalarPair.inject 0)).toLinearMap ∘ₗ scalarLinear A J α ht D hD p 2 +
    (SchwartzMap.postcompCLM (ScalarPair.inject 1)).toLinearMap ∘ₗ scalarLinear A J α ht D hD p 3

end TamingCompatibility.GeometricChart

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_ChartTestPairing
attribute [-instance] _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section

section
noncomputable section
namespace TamingCompatibility.MetricForms
open MetricModel
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
lemma pairing_zero_right (g : Metric E) {k : ℕ} (a : Form E k) : pairing g a 0 = 0 := by
  simpa only [zero_smul,zero_mul] using pairing_smul_right g (0:ℝ) a (0 : Form E k)
end TamingCompatibility.MetricForms

namespace TamingCompatibility.GeometricChart
open ManifoldForms ManifoldHodge AntiInvariantFrame LocalMatrixOperator ManifoldLocalization ManifoldVolume
open Set _root_.MeasureTheory
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J) (p : X) (D : Data J α ht p)

def rawScalar (a : TwoForm X) (j : Fin 4) (z : Space) : ℝ :=
  pullback a (extChartAt Model p).symm z ![D.frame 0 z,D.frame j z]

end TamingCompatibility.GeometricChart

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_FramePairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section

section

noncomputable section
namespace TamingCompatibility.ManifoldForms
open Bundle ContinuousAlternatingMap
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]

lemma exteriorDerivative_fun_smul {k : ℕ} {f : X → ℝ} (hf : ContMDiff Model 𝓘(ℝ,ℝ) ∞ f)
    {a : Form X k} (ha : Smooth a) :
    exteriorDerivative (fun x => f x • a x) =
      (fun x => f x • exteriorDerivative a x) + wedgeOne (scalarDifferential f) a := by
  funext x
  let e := extChartAt Model x
  let z := e x
  have hz : z ∈ e.target := e.map_source (mem_extChartAt_source x)
  have hc : ContDiffAt ℝ ∞ (f ∘ e.symm) z :=
    (((hf.comp_contMDiffOn (contMDiffOn_extChartAt_symm x)).contDiffOn) z hz).contDiffAt
      ((isOpen_extChartAt_target x).mem_nhds hz)
  have hca := ((smooth_chart a ha x) z hz).contDiffAt ((isOpen_extChartAt_target x).mem_nhds hz)
  have he : pullback (fun y => f y • a y) e.symm = fun y => (f ∘ e.symm) y • pullback a e.symm y := by
    funext y; ext v; rfl
  change extDeriv (pullback (fun y => f y • a y) e.symm) z = _
  rw [he,ExteriorForms.extDeriv_variable_smul (hc.differentiableAt (by simp)) (hca.differentiableAt (by simp))]
  have hdf : fderiv ℝ (f ∘ e.symm) z = mfderiv Model 𝓘(ℝ,ℝ) f x := by
    rw [← mfderiv_eq_fderiv,mfderiv_comp z (hf.mdifferentiable (by simp) _)
      (((contMDiffOn_extChartAt_symm (n := ∞) x) z hz).contMDiffAt ((isOpen_extChartAt_target x).mem_nhds hz) |>.mdifferentiableAt (by simp))]
    have hinv : e.symm z = x := e.left_inv (mem_extChartAt_source x)
    rw [hinv]
    have hi : mfderiv Model Model e.symm z = ContinuousLinearMap.id ℝ Space := by
      exact mfderiv_inverseChart_self x
    rw [hi]
    rfl
  have hpa : pullback a e.symm z = a x := by
    unfold pullback
    rw [e.left_inv (mem_extChartAt_source x)]
    have hi : mfderiv Model Model e.symm z = ContinuousLinearMap.id ℝ Space :=
      mfderiv_inverseChart_self x
    rw [hi]
    rfl
  have hinv : (f ∘ e.symm) z = f x := congrArg f (e.left_inv (mem_extChartAt_source x))
  rw [hinv,hdf,hpa]
  rfl
end TamingCompatibility.ManifoldForms

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_GeometricCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section

section

noncomputable section
namespace TamingCompatibility.MetricForms
open MetricModel
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
lemma pairing_sub_self_le (g : Metric E) {k : ℕ} (a b : Form E k) :
    pairing g (a-b) (a-b) ≤ 2*pairing g a a + 2*pairing g b b := by
  have h := pairing_self_nonneg g (a+b)
  have ha (c : Form E k) : pairing g c (a+b) = pairing g c a + pairing g c b := by
    rw [pairing_symm,pairing_add_left',pairing_symm g a c,pairing_symm g b c]
  rw [pairing_add_left',ha,ha,pairing_symm g b a] at h
  rw [pairing_sub_left,pairing_sub_right,pairing_sub_right,pairing_symm g b a]
  linarith
end TamingCompatibility.MetricForms

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_PositiveFunctions
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Manifold ContDiff
open scoped Manifold ContDiff Topology
open Filter Set
attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid
open scoped Manifold ContDiff Topology
open Bundle Filter Set
open Set
open Bundle Set Filter
open scoped Topology
open Set _root_.MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology
namespace TamingCompatibility

open Bundle Set _root_.MeasureTheory
open scoped Manifold ContDiff Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X]
  [IsManifold Model ∞ X]

lemma IsSmooth.continuous_tangentEval {α : TwoForm X} (hα : IsSmooth α)
    (J : AlmostComplexStructure X) :
    Continuous (fun p : TangentBundle Model X => eval α p.proj p.2 (J.endomorphism p.proj p.2)) := by
  have hm := (hα.associatedBilinear J).comp (contMDiff_proj (IB := Model) (n := ∞) (F := Space) (TangentSpace Model : X → Type))
  have he := hm.clm_bundle_apply₂ (F₁ := Space) (F₂ := Space) (F₃ := ℝ)
    (E₁ := TangentSpace Model) (E₂ := TangentSpace Model) (E₃ := Bundle.Trivial X ℝ)
    (IB := Model) (IM := Model.tangent) contMDiff_id contMDiff_id
  have hcont := he.continuous
  have hs := ((Bundle.Trivial.homeomorphProd X ℝ).continuous.comp hcont).snd
  change Continuous (fun p : TangentBundle Model X =>
    TamingCompatibility.associatedBilinear J α p.proj p.2 p.2) at hs
  simpa only [associatedBilinear_apply] using hs

def unitEvaluation (J : AlmostComplexStructure X) (g : ContMDiffRiemannianMetric Model ∞ Space
    (TangentSpace Model : X → Type)) (α : TwoForm X) (hα : IsSmooth α) :
    C(MetricUnit g, ℝ) :=
  ⟨fun p => eval α p.val.proj p.val.2 (J.endomorphism p.val.proj p.val.2),
    (hα.continuous_tangentEval J).comp continuous_subtype_val⟩

end TamingCompatibility

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Functional_ChartNormalTest
attribute [-instance] _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section

section
noncomputable section

namespace TamingCompatibility.GeometricChart
open ManifoldForms ManifoldHodge AntiInvariantFrame LocalMatrixOperator EuclideanEnergy
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J)
  (p : X) (D : Data J α ht p)

lemma normalA_smooth (i : Fin 4) : ContDiffOn ℝ ∞ (normalA J α ht p D i) D.domain := by
  apply contDiffOn_clm_apply.mpr
  intro q
  apply (contDiffOn_piLp 2).mpr
  intro j
  have hc (k : Fin 4) : ContDiffOn ℝ ∞ (fun z => D.frame k z i) D.domain :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp_contDiffOn (D.frame_smooth k)
  fin_cases j
  · exact (contDiffOn_const.mul (hc 2).neg).add (contDiffOn_const.mul (hc 3).neg)
  · exact (contDiffOn_const.mul (hc 3)).add (contDiffOn_const.mul (hc 2).neg)
  · exact (contDiffOn_const.mul (hc 0)).add (contDiffOn_const.mul (hc 1))
  · exact (contDiffOn_const.mul (hc 1).neg).add (contDiffOn_const.mul (hc 0))

include hs in
lemma realDeriv_smooth : ContDiffOn ℝ ∞ (fun z => extDeriv
    (fun y => realPart (coordinateMetric J α ht p y) (fun i => D.frame i y)) z) D.domain := by
  have hψ := realPart_smooth ((coordinateMetric_smooth J α hs ht p).mono D.domain_subset) D.frame_smooth
  exact (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ Space ℝ).contDiff.comp_contDiffOn
    (hψ.fderiv_of_isOpen (m := ∞) D.domain_open (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))

include hs in
lemma imagDeriv_smooth : ContDiffOn ℝ ∞ (fun z => extDeriv
    (fun y => imagPart (coordinateMetric J α ht p y) (fun i => D.frame i y)) z) D.domain := by
  have hχ := imagPart_smooth ((coordinateMetric_smooth J α hs ht p).mono D.domain_subset) D.frame_smooth
  exact (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ Space ℝ).contDiff.comp_contDiffOn
    (hχ.fderiv_of_isOpen (m := ∞) D.domain_open (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))

include hs in
lemma normalStar_smooth : ContDiffOn ℝ ∞ (fun z => MetricHodge.starThreeCLM
    (coordinateMetric J α ht p z)
    (TamingCompatibility.pullback (invariantPart J α) (extChartAt Model p).symm z)) D.domain := by
  exact SmoothHodge.starThreeCLM_contDiffOn (coordinateMetric J α ht p)
    (coordinateJ J p) (by simp [Space]) D.domain_open
    ((coordinateMetric_smooth J α hs ht p).mono D.domain_subset)
    ((coordinateJ_smooth J p).mono D.domain_subset)
    (fun z hz => coordinateJ_square J p (D.domain_subset hz))
    (fun z hz => coordinateMetric_hermitian J α ht p (D.domain_subset hz))
    ((smooth_chart _ (hs.invariantPart J) p).mono D.domain_subset)

include hs in
lemma normalB_smooth : ContDiffOn ℝ ∞ (normalB J α ht p D) D.domain := by
  apply contDiffOn_clm_apply.mpr
  intro q
  apply (contDiffOn_piLp 2).mpr
  intro i
  change ContDiffOn ℝ ∞ (fun z => (MetricHodge.starThreeCLM
    (coordinateMetric J α ht p z)
    (TamingCompatibility.pullback (invariantPart J α) (extChartAt Model p).symm z)
    ((q 0) • extDeriv (fun y => realPart (coordinateMetric J α ht p y) (fun j => D.frame j y)) z +
     (q 1) • extDeriv (fun y => imagPart (coordinateMetric J α ht p y) (fun j => D.frame j y)) z))
      (fun _ : Fin 1 => D.frame i z)) D.domain
  exact FormSmooth.contDiffOn_apply
    ((normalStar_smooth J α hs ht p D).clm_apply
      (((realDeriv_smooth J α hs ht p D).const_smul (q 0)).add
       ((imagDeriv_smooth J α hs ht p D).const_smul (q 1))))
    (fun _ => D.frame_smooth i)

def normalMetric (i j : Fin 4) (z : Space) : ℝ :=
  ⟪frameCovector (fun k => D.frame k z) i,frameCovector (fun k => D.frame k z) j⟫

end TamingCompatibility.GeometricChart

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Elliptic_SobolevBounded
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section

section
noncomputable section
namespace TamingCompatibility.HilbertSobolev
open _root_.MeasureTheory TemperedDistribution EuclideanSobolev
open scoped SchwartzMap ENNReal LineDeriv Topology BoundedContinuousFunction
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

lemma sobolevToBounded_schwartz (s : ℝ) (hs : Module.finrank ℝ E < 2*s) (f : 𝓢(E,F)) :
    sobolevToBounded s hs (schwartzToH s f) = f.toBoundedContinuousFunction := by
  apply boundedDistributionCLM_injective
  rw [boundedDistributionCLM_apply,boundedDistributionCLM_apply,sobolevToBounded_spec,
    schwartzToH_spec,boundedDistribution_schwartz]

end TamingCompatibility.HilbertSobolev

end
end

section
noncomputable section
namespace TamingCompatibility.HilbertSobolev
open _root_.MeasureTheory TemperedDistribution EuclideanSobolev
open scoped SchwartzMap ENNReal LineDeriv Topology BoundedContinuousFunction
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

lemma schwartz_first_derivative_bound (s : ℝ)
    (hs : Module.finrank ℝ E < 2*(s-1)) (v : E) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (f : 𝓢(E,F)) (x : E),
      ‖(∂_{v} f) x‖ ≤ K * ‖schwartzToH s f‖ := by
  let T := (sobolevToBounded (E := E) (F := F) (s-1) hs).comp (derivative s v)
  refine ⟨‖T‖,norm_nonneg T,fun f x => ?_⟩
  have he : sobolevToBounded (s-1) hs (derivative s v (schwartzToH s f)) =
      (∂_{v} f).toBoundedContinuousFunction := by
    rw [← schwartzToH_derivative]
    exact sobolevToBounded_schwartz (s-1) hs _
  calc
    ‖(∂_{v} f) x‖ ≤ ‖(∂_{v} f).toBoundedContinuousFunction‖ :=
      (∂_{v} f).toBoundedContinuousFunction.norm_coe_le_norm x
    _ = ‖T (schwartzToH s f)‖ := congrArg norm he.symm
    _ ≤ _ := T.le_opNorm _

end TamingCompatibility.HilbertSobolev

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Elliptic_RealSobolevLift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.HilbertSobolev
open _root_.MeasureTheory TemperedDistribution EuclideanSobolev Set
open scoped SchwartzMap ENNReal LineDeriv Topology BoundedContinuousFunction
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

lemma sobolevToBounded_lipschitz_bound (s : ℝ)
    (hs : Module.finrank ℝ E < 2*(s-1)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : H E F s, ∀ x y : E,
      ‖sobolevToBounded s (by linarith) u x-sobolevToBounded s (by linarith) u y‖ ≤
        C*‖u‖*‖x-y‖ := by
  classical
  choose K hK hb using fun i => schwartz_first_derivative_bound (E := E) (F := F)
    s hs (stdOrthonormalBasis ℝ E i)
  let C := ∑ i, K i
  have hC : 0 ≤ C := Finset.sum_nonneg (fun i _ => hK i)
  refine ⟨C,hC,fun u x y => ?_⟩
  have hc : _root_.IsClosed {u : H E F s |
      ‖sobolevToBounded s (by linarith) u x-sobolevToBounded s (by linarith) u y‖ ≤
        C*‖u‖*‖x-y‖} := by
    apply isClosed_le
    · exact (((BoundedContinuousFunction.evalCLM ℂ x).comp
        (sobolevToBounded s (by linarith))).continuous.sub
        (((BoundedContinuousFunction.evalCLM ℂ y).comp
        (sobolevToBounded s (by linarith))).continuous)).norm
    · fun_prop
  refine (schwartzToH_dense s).induction_on u hc ?_
  intro f
  rw [sobolevToBounded_schwartz]
  change ‖f x-f y‖ ≤ C*‖schwartzToH s f‖*‖x-y‖
  apply (convex_univ : Convex ℝ (Set.univ : Set E)).norm_image_sub_le_of_norm_fderiv_le
    (fun z _ => f.differentiableAt) _ (mem_univ y) (mem_univ x)
  intro z _
  calc
    ‖fderiv ℝ f z‖ ≤ ∑ i, ‖fderiv ℝ f z (stdOrthonormalBasis ℝ E i)‖ :=
      CriticalSobolev.opNorm_le_sum_basis _
    _ = ∑ i, ‖(∂_{stdOrthonormalBasis ℝ E i} f) z‖ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
    _ ≤ ∑ i, K i*‖schwartzToH s f‖ := Finset.sum_le_sum (fun i _ => hb i f z)
    _ = C*‖schwartzToH s f‖ := (Finset.sum_mul _ _ _).symm

def sobolevEval (s : ℝ) (hs : Module.finrank ℝ E < 2*s) (x : E) :
    H E F s →L[ℂ] F :=
  (BoundedContinuousFunction.evalCLM ℂ x).comp (sobolevToBounded s hs)

lemma sobolevEval_continuous (s : ℝ) (hs : Module.finrank ℝ E < 2*(s-1)) :
    Continuous (sobolevEval (E := E) (F := F) s (by linarith)) := by
  obtain ⟨C,hC,hb⟩ := sobolevToBounded_lipschitz_bound (E := E) (F := F) s hs
  have hl : LipschitzWith ⟨C,hC⟩ (sobolevEval (E := E) (F := F) s (by linarith)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_eq_norm,dist_eq_norm]
    apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hC (norm_nonneg _))
    intro u
    change ‖sobolevToBounded s _ u x-sobolevToBounded s _ u y‖ ≤ _
    exact (hb u x y).trans_eq (by ring)
  exact hl.continuous
end TamingCompatibility.HilbertSobolev

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeFrameDifferential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section
noncomputable section
open scoped RealInnerProductSpace
namespace TamingCompatibility.HodgeFrame
open MetricModel MetricForms MetricHodge ExteriorForms ContinuousAlternatingMap
open HodgeNormalSymbol (W)
open FormMetric (pairLeft pairRight)
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable (g : Metric E) (hdim : Module.finrank ℝ E = 4) (b : Fin 4 → E)
  (hb : ∀ i j, g.bilinear (b i) (b j) = if i=j then 1 else 0)
  (J : E →L[ℝ] E) (horth : ∀ u v, g.bilinear (J u) (J v) = g.bilinear u v)
  (h0 : J (b 0) = b 1) (h1 : J (b 1) = -b 0)
  (h2 : J (b 2) = b 3) (h3 : J (b 3) = -b 2)
  (F : MetricForms.Form E 2) (hF : ∀ u v, F ![u,v] = g.bilinear (J u) v)
include hb h0 h1 h2 h3 hF hdim horth
lemma coordinates_star (a : MetricForms.Form E 2) :
    coordinates b (starTwo g J F a) = UnitaryFrame.star (coordinates b a) := by
  rw [coordinates_model g hdim b hb,coordinates_model g hdim b hb a,
    formEquiv_starTwo g J horth]
  apply HermitianHodge.coords_star
  · simp only [basisOfFrame_apply,LinearIsometry.coe_toContinuousLinearMap]
    change @Eq E (J (b 0)) (b 1)
    exact h0
  · simp only [basisOfFrame_apply,LinearIsometry.coe_toContinuousLinearMap]
    change @Eq E (J (b 1)) (-b 0)
    exact h1
  · simp only [basisOfFrame_apply,LinearIsometry.coe_toContinuousLinearMap]
    change @Eq E (J (b 2)) (b 3)
    exact h2
  · simp only [basisOfFrame_apply,LinearIsometry.coe_toContinuousLinearMap]
    change @Eq E (J (b 3)) (-b 2)
    exact h3
  · intro u v
    exact hF u v

lemma star_wedge_star_coordinate (ξ : E →L[ℝ] ℝ) (a : MetricForms.Form E 2) (i : Fin 4) :
    starThree g F (wedgeOne ξ (starTwo g J F a)) ![b i] =
      UnitaryFrame.interior (WithLp.toLp 2 (fun j => ξ (b j))) (coordinates b a) i := by
  rw [star_wedge_coordinate g hdim b hb J h0 h1 h2 h3 F hF,
    coordinates_star g hdim b hb J horth h0 h1 h2 h3 F hF,UnitaryFrame.star_square]
end TamingCompatibility.HodgeFrame

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeGeometricCoefficients
attribute [-simp] _root_.OAI.TamingCompatibility.HodgeNormalSymbol.symbolMap_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section
noncomputable section
open scoped ContDiff RealInnerProductSpace
namespace TamingCompatibility.HodgeGeometricCoefficients
open MetricModel MetricForms MetricHodge ExteriorForms ContinuousAlternatingMap
open EuclideanEnergy HodgeFrame HodgeNormalOperator
open HodgeNormalSymbol (W Q)

variable (g : V → Metric V) (J : V → V →L[ℝ] V) (F : V → MetricForms.Form V 2)
  (b : Fin 4 → V → V) {U : Set V} (hU : IsOpen U)
  (hg : ContDiffOn ℝ ∞ (fun x => (g x).bilinear) U) (hJ : ContDiffOn ℝ ∞ J U)
  (hJs : ∀ x ∈ U, ∀ u, J x (J x u) = -u)
  (hgJ : ∀ x ∈ U, ∀ u v, (g x).bilinear (J x u) (J x v) = (g x).bilinear u v)
  (hF : ContDiffOn ℝ ∞ F U) (hb : ∀ i, ContDiffOn ℝ ∞ (b i) U)
include hU hg hJ hJs hgJ hF hb
lemma starFrame_smooth (j : Fin 6) : ContDiffOn ℝ ∞ (starFrame g J F b j) U :=
  SmoothHodge.starTwo_contDiffOn g J (by simp [V]) hU hg hJ hJs hgJ hF (frame_smooth hg hb j)

end TamingCompatibility.HodgeGeometricCoefficients

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeGeometricGarding
attribute [-instance] _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section
noncomputable section
open _root_.MeasureTheory Filter Topology
open scoped ContDiff SchwartzMap RealInnerProductSpace
namespace TamingCompatibility.HodgeGeometricCoefficients
open MetricModel MetricForms MetricHodge ExteriorForms ContinuousAlternatingMap
open EuclideanEnergy HodgeFrame HodgeNormalOperator
open HodgeNormalSymbol (W Q)
open HodgeMatrixEnergy (Field)

def starredField (g : V → Metric V) (J : V → V →L[ℝ] V) (F : V → MetricForms.Form V 2)
    (b : Fin 4 → V → V) (f : Field) (x : V) : MetricForms.Form V 2 :=
  ∑ j, f j x • starFrame g J F b j x
def operator (g : V → Metric V) (J : V → V →L[ℝ] V) (F : V → MetricForms.Form V 2)
    (b : Fin 4 → V → V) (f : Field) (x : V) : Q :=
  left (fun i => b i x) (starThree (g x) (F x) (extDeriv (starredField g J F b f) x)) +
    right (fun i => b i x) (starThree (g x) (F x) (extDeriv (field g b f) x))

lemma starredField_eq (g : V → Metric V) (J : V → V →L[ℝ] V) (F : V → MetricForms.Form V 2)
    (b : Fin 4 → V → V) (f : Field) (x : V) :
    starredField g J F b f x = starTwo (g x) (J x) (F x) (field g b f x) :=
  combine_star_basis (g x) (J x) (F x) (fun i => b i x) (HodgeMatrixEnergy.value f x)

end TamingCompatibility.HodgeGeometricCoefficients

end
end

section
noncomputable section
open scoped Manifold ContDiff SchwartzMap
namespace TamingCompatibility.HodgeChart
open ManifoldHodge ManifoldVolume ManifoldForms ManifoldLocalization
open MetricModel MetricForms MetricHodge EuclideanEnergy
open _root_.MeasureTheory Set
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]

structure Data (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J) (p : X)
    extends GeometricChart.Data J α ht p where
  fullEnergyConstant : ℝ
  fullLowerConstant : ℝ
  fullEnergy_pos : 0 < fullEnergyConstant
  fullLower_pos : 0 < fullLowerConstant
  fullGarding : ∀ f : HodgeMatrixEnergy.Field,
    (∀ j, tsupport (f j) ⊆ Metric.closedBall (extChartAt Model p p) radius) →
    (∫ x, HodgeMatrixEnergy.gradient f x) ≤ fullEnergyConstant * (∫ x,
      ‖HodgeGeometricCoefficients.operator (coordinateMetric J α ht p) (coordinateJ J p)
        (ManifoldForms.pullback (invariantPart J α) (extChartAt Model p).symm) frame f x‖^2) +
      fullLowerConstant * (∫ x, ‖HodgeMatrixEnergy.value f x‖^2)

end TamingCompatibility.HodgeChart

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeWedgeEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section
noncomputable section
open scoped RealInnerProductSpace
namespace TamingCompatibility.MetricHodge
open MetricForms MetricModel ExteriorForms ContinuousAlternatingMap HodgeFrame
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem full_wedge_energy (g : Metric E) (J : E →L[ℝ] E)
    (hJ : ∀ u, J (J u) = -u)
    (horth : ∀ u v, g.bilinear (J u) (J v) = g.bilinear u v)
    (hdim : Module.finrank ℝ E = 4) (F : MetricForms.Form E 2)
    (hF : ∀ u v, F ![u,v] = g.bilinear (J u) v)
    (ξ : E →L[ℝ] ℝ) (a : MetricForms.Form E 2) :
    pairing g (starThree g F (wedgeOne ξ (starTwo g J F a)))
      (starThree g F (wedgeOne ξ (starTwo g J F a))) +
    pairing g (starThree g F (wedgeOne ξ a)) (starThree g F (wedgeOne ξ a)) =
      pairing g (ofSubsingletonLIE (0 : Fin 1) ξ) (ofSubsingletonLIE (0 : Fin 1) ξ) *
        pairing g a a := by
  obtain ⟨b,hb,h0,h1,h2,h3⟩ := VolumeNormalization.exists_metric_unitary_basis g J hJ horth hdim
  rw [pairing_one_eq_sum g hdim b hb,pairing_one_eq_sum g hdim b hb,
    pairing_one_eq_sum g hdim b hb,← coordinates_pairing g hdim b hb,
    real_inner_self_eq_norm_sq]
  have hf (i : Fin 4) : (ofSubsingletonLIE (0 : Fin 1) ξ) ![b i] = ξ (b i) := rfl
  simp_rw [hf]
  simp_rw [star_wedge_star_coordinate g hdim b hb J horth h0 h1 h2 h3 F hF,
    star_wedge_coordinate g hdim b hb J h0 h1 h2 h3 F hF]
  have he := UnitaryFrame.hodge_symbol_energy (WithLp.toLp 2 (fun i => ξ (b i))) (coordinates b a)
  simp only [EuclideanSpace.real_norm_sq_eq] at he ⊢
  simpa only [pow_two, Matrix.cons_val_zero,
    WithLp.ofLp_toLp] using he
end TamingCompatibility.MetricHodge

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeFrameTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.HodgeNormalOperator
open MetricModel MetricForms MetricHodge HodgeFrame EuclideanEnergy
open HodgeNormalSymbol (W Q)
lemma star_reconstruct_function (g : V → Metric V) (J : V → V →L[ℝ] V)
    (F : V → MetricForms.Form V 2) (b : Fin 4 → V → V) (q : V → W) :
    (fun y => ∑ j, q y j • HodgeGeometricCoefficients.starFrame g J F b j y) =
    (fun y => starTwo (g y) (J y) (F y) (reconstruct (g y) (fun i => b i y) (q y))) := by
  funext y
  exact combine_star_basis _ _ _ _ _
end TamingCompatibility.HodgeNormalOperator

end
end

end
end

end OAI
end


