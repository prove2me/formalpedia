-- Prove2me | Definitions.Def_OAIQ239Tc034
-- name    : OAIQ239Tc034
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T23:28:11.972197+00:00
-- url     : https://prove2.me/theorems/96f14dc4-e16e-4606-802e-f30e7c998b58
-- title:
--   Definitions bundle OAIQ239Tc034 of the split of OpenAI, Taming implies compatibility on four-manifolds
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.TamingCompatibility.taming_implies_compatibility`, carved from OpenAI's openai/math development (OpenAI, *Taming implies compatibility on four-manifolds*, OpenAI Math Release, October 6, 2026, result family 342, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 7 declarations of OpenAI's Lean: 1 definition, 1 instance and 5 theorems. The definitions and types are `OAI.TamingCompatibility.GeometricHilbert.harmonicAnti`.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: [`TamingCompatibility_DifferentialForms_GeometricFredholm`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/DifferentialForms/GeometricFredholm.lean), [`TamingCompatibility_Hodge_HodgeProjectionRaw`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Hodge/HodgeProjectionRaw.lean), [`TamingCompatibility_Hodge_HodgeScaleSmoothing`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Hodge/HodgeScaleSmoothing.lean).
--
--   **Imports.** It imports the published bundle `Def_TamingCompatibility`; the bundle `OAIQ239Tc028` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ239Tc030`; the statements `OAI.TamingCompatibility.GeometricHilbert.Hermitian.combinedForm_global_lower`, `OAI.TamingCompatibility.GeometricHilbert.Hermitian.exists_combined_unit_bounds`, `OAI.TamingCompatibility.GeometricHilbert.Hermitian.exists_defect_combination`, `OAI.TamingCompatibility.GeometricHilbert.Hermitian.exists_positive_combination`, `OAI.TamingCompatibility.GeometricHilbert.Hermitian.logForm_far_uniform`, `OAI.TamingCompatibility.GeometricHilbert.Hermitian.nonharmonic_logSource_compact`, `OAI.TamingCompatibility.GeometricHilbert.Hermitian.nonharmonic_sqrtSource_compact`, `OAI.TamingCompatibility.GeometricHilbert.Hermitian.scalarCorrection_logError_estimate`, `OAI.TamingCompatibility.GeometricHilbert.Hermitian.scalarCorrection_sqrtError_estimate`, `OAI.TamingCompatibility.GeometricHilbert.Hermitian.separating_probability_smooth_defect`, `OAI.TamingCompatibility.GeometricHilbert.Hermitian.sqrtForm_far_uniform`, `OAI.TamingCompatibility.GeometricHilbert.closedLift_scalar_off_source`, `OAI.TamingCompatibility.GeometricHilbert.correctedDdc_off_source_compact`, `OAI.TamingCompatibility.GeometricHilbert.geometric_smooth_inverse`, `OAI.TamingCompatibility.GeometricHilbert.harmonic_schwartz_seminorm_bound`, `OAI.TamingCompatibility.GeometricHilbert.hodge_lift_local_estimate`, `OAI.TamingCompatibility.GeometricHilbert.scalarCorrection_all_scales` and `OAI.TamingCompatibility.GeometricHilbert.scalarCorrection_local_estimates`; the proofs of `OAI.TamingCompatibility.GeometricHilbert.Hermitian.combinedForm_global_lower`, `OAI.TamingCompatibility.GeometricHilbert.Hermitian.exists_combined_unit_bounds`, `OAI.TamingCompatibility.GeometricHilbert.Hermitian.exists_defect_combination`, `OAI.TamingCompatibility.GeometricHilbert.Hermitian.exists_positive_combination`, `OAI.TamingCompatibility.GeometricHilbert.Hermitian.logForm_far_uniform`, `OAI.TamingCompatibility.GeometricHilbert.Hermitian.nonharmonic_logSource_compact`, `OAI.TamingCompatibility.GeometricHilbert.Hermitian.nonharmonic_sqrtSource_compact`, `OAI.TamingCompatibility.GeometricHilbert.Hermitian.scalarCorrection_logError_estimate`, `OAI.TamingCompatibility.GeometricHilbert.Hermitian.scalarCorrection_sqrtError_estimate`, `OAI.TamingCompatibility.GeometricHilbert.Hermitian.separating_probability_smooth_defect`, `OAI.TamingCompatibility.GeometricHilbert.Hermitian.sqrtForm_far_uniform`, `OAI.TamingCompatibility.GeometricHilbert.closedLift_scalar_off_source`, `OAI.TamingCompatibility.GeometricHilbert.correctedDdc_off_source_compact`, `OAI.TamingCompatibility.GeometricHilbert.exists_closed_lift_hodge_bound`, `OAI.TamingCompatibility.GeometricHilbert.geometric_smooth_inverse`, `OAI.TamingCompatibility.GeometricHilbert.harmonic_schwartz_seminorm_bound`, `OAI.TamingCompatibility.GeometricHilbert.scalarCorrection_all_scales`, `OAI.TamingCompatibility.GeometricHilbert.scalarCorrection_local_estimates`, `OAI.TamingCompatibility.separating_probability_atlas_defect` and `OAI.TamingCompatibility.separating_probability_local_quadratic`.
-- source:
--   OpenAI, Taming implies compatibility on four-manifolds, OpenAI Math Release, October 6, 2026, https://github.com/openai/math (result family 342; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Taming-implies-compatibility-on-four-manifolds-October-6-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit 7ef5c0c

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc028

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_GeometricFredholm
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.HilbertSobolev.localSolutionSpace_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart
open _root_.MeasureTheory
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)

def harmonicAnti : Submodule ℝ (L2 A J α hs ht true) :=
  Fredholm.nullspace (Variational.resolvent (energyInclusion A J α hs ht)
    (weakDelta A J α hs ht) (graphEnergy_coercive A J α hs ht))

lemma harmonicAnti_closed : _root_.IsClosed (harmonicAnti A J α hs ht : Set (L2 A J α hs ht true)) :=
  (1 - Variational.resolvent (energyInclusion A J α hs ht)
    (weakDelta A J α hs ht) (graphEnergy_coercive A J α hs ht)).isClosed_ker

instance harmonicAnti_complete : CompleteSpace (harmonicAnti A J α hs ht) :=
  (harmonicAnti_closed A J α hs ht).completeSpace_coe

end TamingCompatibility.GeometricHilbert

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeScaleSmoothing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)

lemma hodgeScaleInput_spec (r : ℝ) (hr : 0 < r) (f : L2 A J α hs ht true) :
    (hodgeGraphResolvent A J α hs ht 1 zero_lt_one ^ 2) (hodgeScaleInput A J α hs ht r hr f) =
      hodgeRegularizedGraph A J α hs ht r hr f := by
  let a := (r^2)⁻¹
  let b := 1-a
  let u₁ := hodgeWeakSolution A J α hs ht r hr f
  let u₂ := hodgeWeakSolution A J α hs ht r hr (hodgeResolvent A J α hs ht r f)
  let u₃ := hodgeRegularizedGraph A J α hs ht r hr f
  have hi₁ : hodgeInclusion A J α hs ht u₁ = hodgeResolvent A J α hs ht r f := by
    rw [hodgeResolvent_eq A J α hs ht r hr]; rfl
  have hi₂ : hodgeInclusion A J α hs ht u₂ =
      hodgeResolvent A J α hs ht r (hodgeResolvent A J α hs ht r f) := by
    exact congrArg (fun L => L (hodgeResolvent A J α hs ht r f))
      (hodgeResolvent_eq A J α hs ht r hr).symm
  have hu₂ : hodgeGraphResolvent A J α hs ht r hr u₁ = u₂ := by
    change hodgeWeakSolution A J α hs ht r hr (hodgeInclusion A J α hs ht u₁) = _
    rw [hi₁]
  have hu₃ : hodgeGraphResolvent A J α hs ht r hr u₂ = u₃ := by
    change hodgeWeakSolution A J α hs ht r hr (hodgeInclusion A J α hs ht u₂) = _
    rw [hi₂]; rfl
  have he₁ := hodgeGraphResolvent_scale_transfer A J α hs ht r hr u₁
  have he₂ := hodgeGraphResolvent_scale_transfer A J α hs ht r hr u₂
  rw [hu₂] at he₁
  rw [hu₃] at he₂
  change hodgeGraphResolvent A J α hs ht 1 zero_lt_one
    (hodgeGraphResolvent A J α hs ht 1 zero_lt_one (a • (a • u₁+b • u₂)+b • (a • u₂+b • u₃))) = u₃
  rw [map_add,map_smul,map_smul,he₁,he₂,he₂]

end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeProjectionRaw
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.frameMap_apply _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDifferential_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap_zero _root_.OAI.TamingCompatibility.HodgeNormalSymbol.symbolMap_apply _root_.OAI.TamingCompatibility.HodgeStarGeometry.starMap_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.HodgeChart
open ManifoldForms ManifoldHodge ManifoldLocalization ComplexMatrix HodgeFrame Set
open scoped Manifold ContDiff SchwartzMap
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (D : ∀ p : A.centers, GeometricChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)
omit [T2Space X] in
lemma realVectorSchwartz_antiInvariant (p : A.centers) (f : smoothForms X 2) (z : Space) :
    realVectorSchwartz A J α ht D hD p ⟨antiInvariantPart J f.val,IsSmooth.antiInvariantPart f.property J⟩ z =
      UnitaryFrame.antiInvariantPart (realVectorSchwartz A J α ht D hD p f z) := by
  by_cases hz : z ∈ (D p).domain
  · rw [realVectorSchwartz_raw A J α ht D hD p _ hz,
      realVectorSchwartz_raw A J α ht D hD p f hz,
      rawVector_antiInvariantPart J α ht p.val (D p) f.val hz]
    ext i
    fin_cases i <;> simp [UnitaryFrame.antiInvariantPart,UnitaryFrame.jAction] <;> ring
  · have hzero (a : smoothForms X 2) : realVectorSchwartz A J α ht D hD p a z = 0 := by
      ext i
      rw [realVectorSchwartz_apply]
      exact indicator_of_notMem hz _
    simp [hzero,UnitaryFrame.antiInvariantPart,UnitaryFrame.jAction]

omit [T2Space X] in
lemma scalarVectorLinear_antiInvariant (p : A.centers) (f : smoothForms X 2) :
    scalarVectorLinear A J α ht D hD p ⟨antiInvariantPart J f.val,IsSmooth.antiInvariantPart f.property J⟩ =
      SchwartzMap.postcompCLM antiMatrix (scalarVectorLinear A J α ht D hD p f) := by
  rw [← realVectorSchwartz_embed A J α ht D hD p f,
    ← realVectorSchwartz_embed A J α ht D hD p _]
  ext z i
  simp only [SchwartzMap.postcompCLM_apply,realVectorSchwartz_antiInvariant,antiMatrix_embed]
end TamingCompatibility.HodgeChart

namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ComplexMatrix TemperedDistribution EuclideanSobolevOperators HilbertSobolev
open scoped Manifold ContDiff SchwartzMap
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).toData.source)
omit [T2Space X] in
lemma hodgeRawDistribution_smooth_antiInvariant (p : A.centers) (τ : 𝓢(Space,ℝ))
    (f : PreL2 A J α hs ht true) :
    hodgeRawDistribution A J α hs ht D hD p τ
      (hodgeSmooth A J α hs ht ⟨antiInvariantPart J f.val,IsSmooth.antiInvariantPart f.property J⟩) =
      fiberMap antiMatrix (hodgeRawDistribution A J α hs ht D hD p τ (hodgeSmooth A J α hs ht f)) := by
  change smulLeftCLM HodgeScalar.F (SchwartzMap.postcompCLM Complex.ofRealCLM τ)
    (hodgeScalarDistribution A J α hs ht D hD p (hodgeSmooth A J α hs ht _)) =
      fiberMap antiMatrix (smulLeftCLM HodgeScalar.F (SchwartzMap.postcompCLM Complex.ofRealCLM τ)
        (hodgeScalarDistribution A J α hs ht D hD p (hodgeSmooth A J α hs ht f)))
  let fπ : PreL2 A J α hs ht true := ⟨antiInvariantPart J f.val,IsSmooth.antiInvariantPart f.property J⟩
  change smulLeftCLM _ _ (hodgeScalarDistribution A J α hs ht D hD p (hodgeSmooth A J α hs ht fπ)) = _
  rw [hodgeScalarDistribution_smooth A J α hs ht D hD p fπ,
    hodgeScalarDistribution_smooth A J α hs ht D hD p f,fiberMap_product,fiberMap_schwartz]
  congr 2
  exact scalarVectorLinear_antiInvariant A J α ht (fun p => (D p).toData) hD p f
end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end


