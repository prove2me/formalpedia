-- Prove2me | Definitions.Def_OAIQ239Tc023
-- name    : OAIQ239Tc023
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T23:12:44.50962+00:00
-- url     : https://prove2.me/theorems/20cc78ad-7c1f-4cf3-a69d-91357e00e7d7
-- title:
--   Definitions bundle OAIQ239Tc023 of the split of OpenAI, Taming implies compatibility on four-manifolds
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.TamingCompatibility.taming_implies_compatibility`, carved from OpenAI's openai/math development (OpenAI, *Taming implies compatibility on four-manifolds*, OpenAI Math Release, October 6, 2026, result family 342, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 19 declarations of OpenAI's Lean: 4 definitions and 15 theorems. The definitions and types are `OAI.TamingCompatibility.GeometricHilbert.hodgeAmbientStar`, `OAI.TamingCompatibility.GeometricHilbert.hodgeClosedL2`, `OAI.TamingCompatibility.GeometricHilbert.hodgePreClosed`, `OAI.TamingCompatibility.GeometricHilbert.l2StarIsometry`.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: `TamingCompatibility_DifferentialForms_ScalarJet`, `TamingCompatibility_Hodge_HodgeDifferentialLocality`, `TamingCompatibility_Hodge_HodgeFrameTest`, `TamingCompatibility_Hodge_HodgeGlobalEvaluation`, `TamingCompatibility_Hodge_HodgeGraphSmoothing`, `TamingCompatibility_Hodge_HodgeHarmonicSmooth`, `TamingCompatibility_Hodge_HodgeLocalCoefficients`, `TamingCompatibility_Hodge_HodgeLocalSmooth`, `TamingCompatibility_Hodge_HodgeNormalDistribution`, `TamingCompatibility_Hodge_HodgeNormalEnergy`, `TamingCompatibility_Hodge_HodgeScalarJet`, `TamingCompatibility_Hodge_HodgeScalarRaw`, `TamingCompatibility_Hodge_HodgeTestPairing`.
--
--   **Imports.** It imports the published bundle `Def_TamingCompatibility`; the bundles `OAIQ239Tc017`, `OAIQ239Tc018`, `OAIQ239Tc019` and `OAIQ239Tc020` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ239Tc025`, `OAIQ239Tc026` and `OAIQ239Tc027`; the proofs of `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.ParametrixData.cutoff_form_weak_deriv`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.globalCandidate_L2_of_bounds`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.globalCorrection_continuous_bounds`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.globalLeading_continuousAt`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.globalLeading_heatBound`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.globalResidual_heatBound`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.leadingSlice_weak_deriv`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.leading_time_primitive` and `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.separating_current_euclidean_angular_profile`.
-- source:
--   OpenAI, Taming implies compatibility on four-manifolds, OpenAI Math Release, October 6, 2026, https://github.com/openai/math (result family 342; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Taming-implies-compatibility-on-four-manifolds-October-6-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit 7ef5c0c

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc017
import Definitions.Def_OAIQ239Tc018
import Definitions.Def_OAIQ239Tc019
import Definitions.Def_OAIQ239Tc020

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_ScalarJet
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.frameMap_apply _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDifferential_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap_zero _root_.OAI.TamingCompatibility.GeometricHilbert.antiMultiply_apply _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeInclusion_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeScaledDerivative_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.l2Star_smooth _root_.OAI.TamingCompatibility.HodgeNormalSymbol.symbolMap_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.ScalarPair
open _root_.MeasureTheory LineDeriv EuclideanEnergy ManifoldLocalization
open scoped SchwartzMap LineDeriv

lemma make_jet_bound (s t : S) :
    ‖jet (make s t)‖^2 ≤ 20*((∫ x, gradientEnergy s t x)+(∫ x, (s x)^2+(t x)^2)) := by
  let G := ∫ x, gradientEnergy s t x
  let Z := ∫ x, (s x)^2+(t x)^2
  have hG : 0 ≤ G := integral_nonneg (fun x => Finset.sum_nonneg fun i _ => add_nonneg (sq_nonneg _) (sq_nonneg _))
  have hZ : 0 ≤ Z := integral_nonneg (fun x => add_nonneg (sq_nonneg _) (sq_nonneg _))
  have hd : ∑ i : Fin 4, ∫ x, ‖(∂_{e i} (make s t)) x‖^2 = G := by
    simp only [make_derivative,make_norm_sq]
    change (∑ i : Fin 4, ∫ x, (coordinateDeriv i s x)^2+(coordinateDeriv i t x)^2) = _
    symm
    exact integral_finsetSum _ (fun i _ => (schwartz_sq_integrable (coordinateDeriv i s)).add
      (schwartz_sq_integrable (coordinateDeriv i t)))
  have hj (j : DerivativeIndex) : ‖jet (make s t) j‖^2 ≤ 4*(G+Z) := by
    change ‖(jetComponent j (make s t)).toLp 2 (volume : Measure Space)‖^2 ≤ _
    rw [GeometricChart.schwartz_l2_norm_sq]
    cases j with
    | none =>
      change (∫ x, ‖make s t x‖^2) ≤ _
      simp_rw [make_norm_sq]
      change Z ≤ 4*(G+Z)
      linarith
    | some i =>
      have hb := direction_integral_bound (make s t) (stdOrthonormalBasis ℝ Space i)
        ((stdOrthonormalBasis ℝ Space).orthonormal.norm_eq_one i).le
      rw [hd] at hb
      exact hb.trans (by linarith)
  rw [PiLp.norm_sq_eq_of_L2]
  calc
    _ ≤ ∑ j : DerivativeIndex, 4*(G+Z) := Finset.sum_le_sum (fun j _ => hj j)
    _ = _ := by simp [DerivativeIndex,Space,G,Z] <;> ring

end TamingCompatibility.ScalarPair

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeFrameTest
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.frameMap_apply _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDifferential_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap_zero _root_.OAI.TamingCompatibility.GeometricHilbert.antiMultiply_apply _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeInclusion_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeScaledDerivative_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth _root_.OAI.TamingCompatibility.HodgeNormalSymbol.symbolMap_apply _root_.OAI.TamingCompatibility.HodgeStarGeometry.starMap_apply _root_.OAI.TamingCompatibility.HodgeStarGeometry.swapMap_apply
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
open ManifoldForms ManifoldHodge HodgeFrame HodgeGeometricCoefficients GeometricChart
open Set Filter
open scoped Manifold ContDiff Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α)
  (ht : Tames α J) (p : X) (D : GeometricChart.Data J α ht p)

omit [T2Space X] in
lemma rawVector_smooth {a : TwoForm X} (ha : IsSmooth a) :
    ContDiffOn ℝ ∞ (rawVector J α ht p D a) D.domain := by
  apply (contDiffOn_piLp 2).mpr
  intro j
  exact FormSmooth.contDiffOn_apply_two ((smooth_chart a ha p).mono D.domain_subset)
    (D.frame_smooth (FormMetric.pairLeft j)) (D.frame_smooth (FormMetric.pairRight j))
omit [T2Space X] in
lemma rawVector_expansion (a : TwoForm X) {z : Space} (hz : z ∈ D.domain) :
    coordinateTest J α ht p D (rawVector J α ht p D a) z =
      ManifoldForms.pullback a (extChartAt Model p).symm z :=
  reconstruct_coordinates (coordinateMetric J α ht p z) (by simp [Space])
    (fun i => D.frame i z) (D.frame_gram z hz) _
end TamingCompatibility.HodgeChart

end
end

section
noncomputable section
namespace TamingCompatibility.HodgeChart
open ManifoldForms ManifoldHodge HodgeFrame HodgeGeometricCoefficients GeometricChart
open Set Filter
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α)
  (ht : Tames α J) (p : X) (D : GeometricChart.Data J α ht p)

include hs in
lemma normal_coordinateTest_at {q : Space → HodgeNormalSymbol.W}
    {z : Space} (hd : DifferentiableAt ℝ q z) (hz : z ∈ D.domain) :
    HodgeNormalOperator.left (fun i => D.frame i z)
      (MetricHodge.starThree (coordinateMetric J α ht p z)
        (ManifoldForms.pullback (invariantPart J α) (extChartAt Model p).symm z)
        (extDeriv (fun y => MetricHodge.starTwo (coordinateMetric J α ht p y)
          (coordinateJ J p y) (ManifoldForms.pullback (invariantPart J α) (extChartAt Model p).symm y)
          (coordinateTest J α ht p D q y)) z)) +
    HodgeNormalOperator.right (fun i => D.frame i z)
      (MetricHodge.starThree (coordinateMetric J α ht p z)
        (ManifoldForms.pullback (invariantPart J α) (extChartAt Model p).symm z)
        (extDeriv (coordinateTest J α ht p D q) z)) = normalOperator J α ht p D q z := by
  have hψ := HodgeGeometricCoefficients.frame_smooth
    ((coordinateMetric_smooth J α hs ht p).mono D.domain_subset) D.frame_smooth
  have hφ := starFrame_smooth J α hs ht p D
  have h := HodgeNormalOperator.reconstruct_expansion (coordinateMetric J α ht p) (coordinateJ J p)
    (ManifoldForms.pullback (invariantPart J α) (extChartAt Model p).symm) D.frame q z hd
    (fun j => ((hψ j z hz).contDiffAt (D.domain_open.mem_nhds hz)).differentiableAt (by norm_num))
    (fun j => ((hφ j z hz).contDiffAt (D.domain_open.mem_nhds hz)).differentiableAt (by norm_num))
  obtain ⟨h0,h1,h2,h3⟩ := D.frame_complex z hz
  have hA (i : Fin 4) : HodgeNormalOperator.rawPrincipal (coordinateMetric J α ht p z)
      (ManifoldForms.pullback (invariantPart J α) (extChartAt Model p).symm z) (fun k => D.frame k z)
      (basisForm (coordinateMetric J α ht p z) (fun k => D.frame k z))
      (fun j => MetricHodge.starTwo (coordinateMetric J α ht p z) (coordinateJ J p z)
        (ManifoldForms.pullback (invariantPart J α) (extChartAt Model p).symm z)
        (basisForm (coordinateMetric J α ht p z) (fun k => D.frame k z) j)) i = normalA J α ht p D i z :=
    HodgeNormalOperator.rawPrincipal_eq _ _ _ (D.frame_gram z hz) (coordinateJ J p z)
      (coordinateMetric_hermitian J α ht p (D.domain_subset hz)) h0 h1 h2 h3
      (ManifoldTop.coordinateFundamental J α ht p (D.domain_subset hz)) i
  simp only [hA] at h
  exact h

end TamingCompatibility.HodgeChart

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeNormalEnergy
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
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
open ManifoldForms ManifoldHodge HodgeFrame GeometricChart ManifoldLocalization ManifoldVolume
open Set Filter _root_.MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (p : X) (D : GeometricChart.Data J α ht p)
lemma rawVector_manifoldTest (q : Space → HodgeNormalSymbol.W) {z : Space} (hz : z ∈ D.domain) :
    rawVector J α ht p D (manifoldTest J α ht p D q) z = q z := by
  unfold rawVector
  rw [pullback_manifoldTest J α ht p D q (D.domain_subset hz)]
  exact coordinates_reconstruct _ _ (D.frame_gram z hz) _

end TamingCompatibility.HodgeChart

end
end

section
noncomputable section
namespace TamingCompatibility.HodgeChart
open ManifoldForms ManifoldHodge HodgeFrame GeometricChart ManifoldLocalization ManifoldVolume
open Set Filter _root_.MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
variable (hs : IsSmooth α)
include hs in
lemma energyPairing_continuous {a b : TwoForm X} (ha : IsSmooth a) (hb : IsSmooth b) :
    Continuous (energyPairing J α ht a b) := by
  exact (GeometricAdjoint.pairing_one_smooth J α hs ht
    (GeometricAdjoint.codifferential_smooth J α hs ht ha)
    (GeometricAdjoint.codifferential_smooth J α hs ht hb)).continuous.add
    (GeometricAdjoint.pairing_one_smooth J α hs ht
      (GeometricAdjoint.codifferential_smooth J α hs ht (starTwo_smooth J α hs ht ha))
      (GeometricAdjoint.codifferential_smooth J α hs ht (starTwo_smooth J α hs ht hb))).continuous
end TamingCompatibility.HodgeChart

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeNormalDistribution
attribute [-instance] _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
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
open ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume LocalFormalAdjoint
open Set Filter _root_.MeasureTheory LineDeriv
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace LineDeriv
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J)
  (p : X) (D : GeometricChart.Data J α ht p)

lemma firstOrder_local (a : Fin 4 → 𝓢(Space,HodgeNormalSymbol.W →L[ℝ] HodgeNormalSymbol.Q))
    (b : 𝓢(Space,HodgeNormalSymbol.W →L[ℝ] HodgeNormalSymbol.Q)) (s : 𝓢(Space,HodgeNormalSymbol.W))
    (f : Space → HodgeNormalSymbol.W) {z : Space} (he : (s : Space → _) =ᶠ[𝓝 z] f)
    (ha : ∀ i, a i z = normalA J α ht p D i z) (hb : b z = normalB J α ht p D z) :
    firstOrder EuclideanEnergy.e a b s z = normalOperator J α ht p D f z := by
  simp only [firstOrder,_root_.add_apply,_root_.sum_apply,ContinuousLinearMap.comp_apply,
    multiply_apply,lineDerivOpCLM_apply,SchwartzMap.lineDerivOp_apply_eq_fderiv,
    ha,hb,he.fderiv_eq,he.eq_of_nhds,normalOperator]

end TamingCompatibility.HodgeChart

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeScalarJet
attribute [-instance] _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.frameMap_apply _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDifferential_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap_zero _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeScaledDerivative_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth _root_.OAI.TamingCompatibility.HodgeNormalSymbol.symbolMap_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.HodgeScalar
open _root_.MeasureTheory LineDeriv EuclideanEnergy ManifoldLocalization
open scoped SchwartzMap LineDeriv ContDiff
lemma make_jet_bound (f : Fin 6 → 𝓢(Space,ℝ)) :
    ‖jet (make f)‖^2 ≤ 20*((∫ x, HodgeMatrixEnergy.gradient f x)+(∫ x, ‖HodgeMatrixEnergy.value f x‖^2)) := by
  let G := ∫ x, HodgeMatrixEnergy.gradient f x
  let Z := ∫ x, ‖HodgeMatrixEnergy.value f x‖^2
  have hG : 0 ≤ G := integral_nonneg (fun x => Finset.sum_nonneg fun i _ => sq_nonneg _)
  have hZ : 0 ≤ Z := integral_nonneg (fun x => sq_nonneg _)
  have hd : ∑ i : Fin 4, ∫ x, ‖(∂_{e i} (make f)) x‖^2 = G := by
    simp only [make_derivative,make_norm_sq]
    change (∑ i : Fin 4, ∫ x, ‖HodgeMatrixEnergy.derivative f i x‖^2) = _
    symm
    exact integral_finsetSum _ (fun i _ => HodgeMatrixEnergy.value_integrable (fun j => coordinateDeriv i (f j)))
  have hj (j : DerivativeIndex) : ‖jet (make f) j‖^2 ≤ 4*(G+Z) := by
    change ‖(jetComponent j (make f)).toLp 2 (volume : Measure Space)‖^2 ≤ _
    rw [GeometricChart.schwartz_l2_norm_sq]
    cases j with
    | none =>
      change (∫ x, ‖make f x‖^2) ≤ _
      simp_rw [make_norm_sq]
      change Z ≤ 4*(G+Z)
      linarith
    | some i =>
      have hb := direction_integral_bound (make f) (stdOrthonormalBasis ℝ Space i)
        ((stdOrthonormalBasis ℝ Space).orthonormal.norm_eq_one i).le
      rw [hd] at hb
      exact hb.trans (by linarith)
  rw [PiLp.norm_sq_eq_of_L2]
  calc
    _ ≤ ∑ j : DerivativeIndex, 4*(G+Z) := Finset.sum_le_sum (fun j _ => hj j)
    _ = _ := by simp [DerivativeIndex,Space,G,Z] <;> ring

end TamingCompatibility.HodgeScalar

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeScalarRaw
attribute [-instance] _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
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
open GeometricChart (coordinateWeight coordinateWeight_smooth)
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume
open Set Filter _root_.MeasureTheory ComplexMatrix
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).toData.source)
omit [T2Space X] in
lemma hodge_smooth_energy_pair (u v : PreL2 A J α hs ht true) :
    ⟪hodgeWeakDerivative A J α hs ht (hodgeSmooth A J α hs ht u),
      hodgeWeakDerivative A J α hs ht (hodgeSmooth A J α hs ht v)⟫ =
      ∫ x, energyPairing J α ht u.val v.val x ∂geometricVolume A J α := by
  let := geometricVolume_finite A J α hs ht
  change ⟪WithLp.toLp 2 (smoothL2 A J α hs ht false (hodgeDelta A J α hs ht u),
      smoothL2 A J α hs ht false (hodgeDelta A J α hs ht (preStar A J α hs ht u))),
    WithLp.toLp 2 (smoothL2 A J α hs ht false (hodgeDelta A J α hs ht v),
      smoothL2 A J α hs ht false (hodgeDelta A J α hs ht (preStar A J α hs ht v)))⟫ = _
  rw [WithLp.prod_inner_apply,(smoothL2 A J α hs ht false).inner_map_map,
    (smoothL2 A J α hs ht false).inner_map_map,preL2_inner,preL2_inner]
  symm
  apply integral_add
  · exact (GeometricAdjoint.pairing_one_smooth J α hs ht
      (GeometricAdjoint.codifferential_smooth J α hs ht u.property)
      (GeometricAdjoint.codifferential_smooth J α hs ht v.property)).continuous.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  · exact (GeometricAdjoint.pairing_one_smooth J α hs ht
      (GeometricAdjoint.codifferential_smooth J α hs ht (starTwo_smooth J α hs ht u.property))
      (GeometricAdjoint.codifferential_smooth J α hs ht (starTwo_smooth J α hs ht v.property))).continuous.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)

end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeTestPairing
attribute [-instance] _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.frameMap_apply _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDifferential_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap_zero _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeScaledDerivative_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth _root_.OAI.TamingCompatibility.HodgeNormalSymbol.symbolMap_apply _root_.OAI.TamingCompatibility.HodgeStarGeometry.starMap_apply
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
open ManifoldForms ManifoldHodge HodgeFrame GeometricChart ManifoldLocalization ManifoldVolume
open Set _root_.MeasureTheory
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J) (p : X) (D : GeometricChart.Data J α ht p)

lemma pairing_coordinateTest (a : TwoForm X)
    {q : Space → HodgeNormalSymbol.W} (hqD : tsupport q ⊆ D.domain) (z : Space) :
    MetricForms.pairing (coordinateMetric J α ht p z) (ManifoldForms.pullback a (extChartAt Model p).symm z)
      (coordinateTest J α ht p D q z) = ⟪rawVector J α ht p D a z,q z⟫ := by
  by_cases hzq : z ∈ tsupport q
  · rw [← coordinates_pairing _ (by simp [Space]) _ (D.frame_gram z (hqD hzq))]
    change ⟪rawVector J α ht p D a z, coordinates (fun i => D.frame i z)
      (reconstruct (coordinateMetric J α ht p z) (fun i => D.frame i z) (q z))⟫ = _
    rw [coordinates_reconstruct _ _ (D.frame_gram z (hqD hzq))]
  · have hq := image_eq_zero_of_notMem_tsupport hzq
    rw [coordinateTest_zero J α ht p D hq,MetricForms.pairing_zero_right,hq,inner_zero_right]

end TamingCompatibility.HodgeChart

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeGlobalEvaluation
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

def l2StarIsometry : L2 A J α hs ht true →ₗᵢ[ℝ] L2 A J α hs ht true :=
  ⟨(l2Star A J α hs ht).toLinearMap,l2Star_norm A J α hs ht⟩

def hodgeAmbientStar : HodgeGraphSpace A J α hs ht →ₗᵢ[ℝ] HodgeGraphSpace A J α hs ht :=
  LinearIsometry.withLpProdMap 2 (l2StarIsometry A J α hs ht)
    (LinearIsometryEquiv.withLpProdComm 2 ℝ (L2 A J α hs ht false)
      (L2 A J α hs ht false)).toLinearIsometry

end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeLocalSmooth
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

lemma hodgeLaplacian_apply (a : PreL2 A J α hs ht true) :
    hodgeLaplacian A J α hs ht a =
      hodgePreD A J α hs ht (hodgeDelta A J α hs ht a) +
        preStar A J α hs ht (hodgePreD A J α hs ht
          (hodgeDelta A J α hs ht (preStar A J α hs ht a))) := rfl

end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeGraphSmoothing
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

lemma hodgeEnergy_prod_norm_sq (u : hodgeEnergy A J α hs ht) :
    ‖u‖^2 = ‖hodgeInclusion A J α hs ht u‖^2 + ‖hodgeWeakDerivative A J α hs ht u‖^2 :=
  WithLp.prod_norm_sq_eq_of_L2 u.val

lemma hodgeEnergy_prod_norm_le (u : hodgeEnergy A J α hs ht) :
    ‖u‖ ≤ ‖hodgeInclusion A J α hs ht u‖ + ‖hodgeWeakDerivative A J α hs ht u‖ := by
  have h := hodgeEnergy_prod_norm_sq A J α hs ht u
  nlinarith [norm_nonneg u,norm_nonneg (hodgeInclusion A J α hs ht u),
    norm_nonneg (hodgeWeakDerivative A J α hs ht u),
    mul_nonneg (norm_nonneg (hodgeInclusion A J α hs ht u))
      (norm_nonneg (hodgeWeakDerivative A J α hs ht u))]

end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeDifferentialLocality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility
open scoped SchwartzMap

namespace HodgeChart
open ManifoldForms ManifoldHodge HodgeFrame GeometricChart ComplexMatrix
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X)
  (ht : Tames α J) (p : X) (D : GeometricChart.Data J α ht p)

lemma rawVector_antiInvariantPart (a : TwoForm X) {z : Space} (hz : z ∈ D.domain) :
    rawVector J α ht p D (antiInvariantPart J a) z =
      UnitaryFrame.antiInvariantPart (rawVector J α ht p D a z) := by
  unfold rawVector
  rw [pullback_antiInvariantPart J a p (D.domain_subset hz)]
  obtain ⟨h0,h1,h2,h3⟩ := D.frame_complex z hz
  exact coordinates_antiInvariant (fun i => D.frame i z) (coordinateJ J p z) h0 h1 h2 h3 _

end HodgeChart
end TamingCompatibility

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeHarmonicSmooth
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
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart Set
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

def hodgePreClosed : Submodule ℝ (PreL2 A J α hs ht true) where
  carrier := {a | IsClosed a.val}
  zero_mem' := IsClosed.zero
  add_mem' {a b} ha hb := IsClosed.add ha hb a.property b.property
  smul_mem' c _ ha := ha.smul c

def hodgeClosedL2 : Submodule ℝ (L2 A J α hs ht true) :=
  ((hodgePreClosed A J α hs ht).map (smoothL2 A J α hs ht true).toLinearMap).topologicalClosure

end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeLocalCoefficients
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
open GeometricChart (coordinateWeight coordinateWeight_smooth)
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume
open Set Filter _root_.MeasureTheory ComplexMatrix TemperedDistribution HilbertSobolev EuclideanSobolev
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).toData.source)

omit [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
include hs in

lemma exists_hodge_local_coefficients (p : A.centers) {U : Set Space}
    (hU : IsOpen U) (hUD : U ⊆ (D p).domain) (q : Space) (hq : q ∈ U) :
    ∃ W : Set Space, IsOpen W ∧ q ∈ W ∧ W ⊆ U ∧
      ∃ a : Fin 4 → 𝓢(Space,HodgeNormalSymbol.W →L[ℝ] HodgeNormalSymbol.Q),
      ∃ b : 𝓢(Space,HodgeNormalSymbol.W →L[ℝ] HodgeNormalSymbol.Q),
      ∃ ρ : 𝓢(Space,ℝ), ∃ θ : 𝓢(Space,ℂ), ∃ G : Fin 4 → Fin 4 → Space → ℝ,
      (∀ z ∈ W, ∀ i, a i z = normalA J α ht p.val (D p).toData i z) ∧
      (∀ z ∈ W, b z = normalB J α ht p.val (D p).toData z) ∧
      (∀ z ∈ W, ρ z = chartDensity J α p.val z) ∧
      (∀ z ∈ W, θ z * (ρ z : ℂ) = 1) ∧
      ∀ i j z, (ρ z • a i z).adjoint ∘L a j z + (ρ z • a j z).adjoint ∘L a i z =
        (2*G i j z) • ContinuousLinearMap.id ℝ (ComplexMatrix.R 6) := by
  obtain ⟨φ,hφ,hφU,V,hV,hqV,hVU,hφone⟩ := SchwartzCutoff.exists_one_near hU hq
  have hφD := hφU.trans hUD
  let a := patchA J α ht p.val (D p).toData (φ.smooth ⊤) hφ hφD
  let b := patchB J α hs ht p.val (D p).toData (φ.smooth ⊤) hφ hφD
  let ρ : 𝓢(Space,ℝ) := SchwartzCutoff.schwartz (D p).domain_open
    ((chartDensity_smooth J α hs ht p.val).mono (D p).domain_subset) (φ.smooth ⊤) hφ hφD
  have hρ : ∀ z ∈ V, ρ z = chartDensity J α p.val z := by
    intro z hz
    simp only [ρ,SchwartzCutoff.schwartz_apply,hφone z hz,one_smul]
  have hρq : ρ q ≠ 0 := by
    rw [hρ q hqV]
    exact ne_of_gt (chartDensity_pos J α ht p.val ((D p).domain_subset (hUD hq)))
  obtain ⟨κ,-,-,W,hW,hqW,hWV,hκ⟩ := SchwartzCutoff.exists_reciprocal hV
    ((ρ.smooth ⊤).contDiffOn) hqV hρq
  let θ := SchwartzMap.postcompCLM Complex.ofRealCLM κ
  let G := fun i j z => ρ z*φ z*φ z*GeometricChart.normalMetric J α ht p.val (D p).toData i j z
  refine ⟨W,hW,hqW,hWV.trans hVU,a,b,ρ,θ,G,?_,?_,?_,?_,?_⟩
  · intro z hz i
    simp only [a,patchA,SchwartzCutoff.schwartz_apply,hφone z (hWV hz),one_smul]
  · intro z hz
    simp only [b,patchB,SchwartzCutoff.schwartz_apply,hφone z (hWV hz),one_smul]
  · exact fun z hz => hρ z (hWV hz)
  · intro z hz
    change (κ z : ℂ) * (ρ z : ℂ) = 1
    exact_mod_cast hκ z hz
  · exact patchA_polarized J α ht p.val (D p).toData (φ.smooth ⊤) hφ hφD ρ
end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end


