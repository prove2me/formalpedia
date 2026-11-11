-- Prove2me | Definitions.Def_OAIQ239Tc026
-- name    : OAIQ239Tc026
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T23:18:32.111405+00:00
-- url     : https://prove2.me/theorems/090f5850-8872-4f3a-b9b9-df8cbec2d503
-- title:
--   Definitions bundle OAIQ239Tc026 of the split of OpenAI, Taming implies compatibility on four-manifolds
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.TamingCompatibility.taming_implies_compatibility`, carved from OpenAI's openai/math development (OpenAI, *Taming implies compatibility on four-manifolds*, OpenAI Math Release, October 6, 2026, result family 342, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 23 declarations of OpenAI's Lean: 2 definitions and 21 theorems. The definitions and types are `OAI.TamingCompatibility.GeometricHilbert.hodgeGraphResolvent`, `OAI.TamingCompatibility.HodgeChart.realVectorSchwartz`.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: [`TamingCompatibility_HeatFlow_HodgeResolvent`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/HeatFlow/HodgeResolvent.lean), [`TamingCompatibility_Hodge_HodgeFrameTest`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Hodge/HodgeFrameTest.lean), [`TamingCompatibility_Hodge_HodgeGraphSmoothing`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Hodge/HodgeGraphSmoothing.lean), [`TamingCompatibility_Hodge_HodgeNormalDistribution`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Hodge/HodgeNormalDistribution.lean), [`TamingCompatibility_Hodge_HodgeNormalEnergy`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Hodge/HodgeNormalEnergy.lean), [`TamingCompatibility_Hodge_HodgeScalarJet`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Hodge/HodgeScalarJet.lean), [`TamingCompatibility_Hodge_HodgeScalarRaw`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Hodge/HodgeScalarRaw.lean), [`TamingCompatibility_Hodge_HodgeScaleH3`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Hodge/HodgeScaleH3.lean), [`TamingCompatibility_Hodge_HodgeSmoothLaplacian`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Hodge/HodgeSmoothLaplacian.lean), [`TamingCompatibility_Hodge_HodgeTestPairing`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Hodge/HodgeTestPairing.lean).
--
--   **Imports.** It imports the published bundle `Def_TamingCompatibility`; the bundles `OAIQ239Tc022` and `OAIQ239Tc023` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ239Tc028` and `OAIQ239Tc029`; the proofs of `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.kernel_leading_pairing_initial` and `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.leadingSliceForm_weak_deriv`.
-- source:
--   OpenAI, Taming implies compatibility on four-manifolds, OpenAI Math Release, October 6, 2026, https://github.com/openai/math (result family 342; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Taming-implies-compatibility-on-four-manifolds-October-6-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit 7ef5c0c

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc022
import Definitions.Def_OAIQ239Tc023

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
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α)
  (ht : Tames α J) (p : X) (D : GeometricChart.Data J α ht p)

include hs in
lemma normal_delta {a : TwoForm X} (ha : IsSmooth a) {z : Space} (hz : z ∈ D.domain) :
    HodgeNormalOperator.left (fun i => D.frame i z)
      (ManifoldForms.pullback (codifferential J α ht a) (extChartAt Model p).symm z) +
    HodgeNormalOperator.right (fun i => D.frame i z)
      (ManifoldForms.pullback (codifferential J α ht (ManifoldHodge.starTwo J α ht a))
        (extChartAt Model p).symm z) = -normalOperator J α ht p D (rawVector J α ht p D a) z := by
  rw [pullback_codifferential J α hs ht ha p (D.domain_subset hz),
    pullback_codifferential_star J α hs ht ha p (D.domain_subset hz),map_neg,map_neg,← neg_add]
  congr 1
  have he : ManifoldForms.pullback a (extChartAt Model p).symm =ᶠ[𝓝 z]
      coordinateTest J α ht p D (rawVector J α ht p D a) := by
    filter_upwards [D.domain_open.mem_nhds hz] with y hy
    exact (rawVector_expansion J α ht p D a hy).symm
  have heStar : ManifoldForms.pullback (ManifoldHodge.starTwo J α ht a) (extChartAt Model p).symm =ᶠ[𝓝 z]
      (fun y => MetricHodge.starTwo (coordinateMetric J α ht p y) (coordinateJ J p y)
        (ManifoldForms.pullback (invariantPart J α) (extChartAt Model p).symm y)
        (coordinateTest J α ht p D (rawVector J α ht p D a) y)) := by
    filter_upwards [D.domain_open.mem_nhds hz,he] with y hy hye
    rw [pullback_starTwo J α ht a p (D.domain_subset hy),hye]
  rw [he.extDeriv_eq,heStar.extDeriv_eq]
  exact normal_coordinateTest_at J α hs ht p D
    (((rawVector_smooth J α ht p D ha z hz).contDiffAt
      (D.domain_open.mem_nhds hz)).differentiableAt (by norm_num)) hz

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

variable [T2Space X]
lemma manifoldTest_delta_zero_off {q : Space → HodgeNormalSymbol.W}
    (hc : HasCompactSupport q) (hqD : tsupport q ⊆ D.domain)
    {x : X} (hx : x ∉ (extChartAt Model p).symm '' tsupport q) :
    codifferential J α ht (manifoldTest J α ht p D q) x = 0 := by
  have hK : IsCompact ((extChartAt Model p).symm '' tsupport q) :=
    hc.image_of_continuousOn ((continuousOn_extChartAt_symm p).mono (hqD.trans D.domain_subset))
  have he : exteriorDerivative (starTwo J α ht (manifoldTest J α ht p D q)) x = 0 := by
    apply exteriorDerivative_eq_zero_of_eventually
    filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hx] with y hy
    have hh := manifoldTest_zero_off J α ht p D q hy
    change MetricHodge.starTwo (GeometricAdjoint.pointMetric J α ht y) (J.endomorphism y)
      (invariantPart J α y) (manifoldTest J α ht p D q y) = 0
    rw [hh]
    exact MetricHodge.full_starTwo_zero _ _ _
  change -MetricHodge.starThree (GeometricAdjoint.pointMetric J α ht x)
    (invariantPart J α x) (exteriorDerivative (starTwo J α ht (manifoldTest J α ht p D q)) x) = 0
  rw [he]
  change -MetricHodge.starThree (GeometricAdjoint.pointMetric J α ht x)
    (invariantPart J α x) (0 : MetricForms.Form Space 3) = 0
  exact (congrArg Neg.neg (MetricHodge.starThree_zero (E := Space) _ _)).trans (neg_zero)
lemma manifoldTest_delta_star_zero_off {q : Space → HodgeNormalSymbol.W}
    (hc : HasCompactSupport q) (hqD : tsupport q ⊆ D.domain)
    {x : X} (hx : x ∉ (extChartAt Model p).symm '' tsupport q) :
    codifferential J α ht (starTwo J α ht (manifoldTest J α ht p D q)) x = 0 := by
  have hK : IsCompact ((extChartAt Model p).symm '' tsupport q) :=
    hc.image_of_continuousOn ((continuousOn_extChartAt_symm p).mono (hqD.trans D.domain_subset))
  have he : exteriorDerivative (manifoldTest J α ht p D q) x = 0 := by
    apply exteriorDerivative_eq_zero_of_eventually
    filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hx] with y hy
    exact manifoldTest_zero_off J α ht p D q hy
  unfold codifferential
  rw [starTwo_square]
  change -MetricHodge.starThree (GeometricAdjoint.pointMetric J α ht x)
    (invariantPart J α x) (exteriorDerivative (manifoldTest J α ht p D q) x) = 0
  rw [he]
  change -MetricHodge.starThree (GeometricAdjoint.pointMetric J α ht x)
    (invariantPart J α x) (0 : MetricForms.Form Space 3) = 0
  exact (congrArg Neg.neg (MetricHodge.starThree_zero (E := Space) _ _)).trans (neg_zero)

variable (hs : IsSmooth α)
include hs in
lemma normal_manifoldTest_delta {q : Space → HodgeNormalSymbol.W}
    (hq : ContDiff ℝ ∞ q) (hc : HasCompactSupport q) (hqD : tsupport q ⊆ D.domain)
    {z : Space} (hz : z ∈ D.domain) :
    HodgeNormalOperator.left (fun i => D.frame i z)
      (ManifoldForms.pullback (codifferential J α ht (manifoldTest J α ht p D q)) (extChartAt Model p).symm z) +
    HodgeNormalOperator.right (fun i => D.frame i z)
      (ManifoldForms.pullback (codifferential J α ht (starTwo J α ht (manifoldTest J α ht p D q)))
        (extChartAt Model p).symm z) = -normalOperator J α ht p D q z := by
  rw [normal_delta J α hs ht p D (manifoldTest_smooth J α hs ht p D hq hc hqD) hz]
  have he : rawVector J α ht p D (manifoldTest J α ht p D q) =ᶠ[𝓝 z] q := by
    filter_upwards [D.domain_open.mem_nhds hz] with y hy
    exact rawVector_manifoldTest J α ht p D q hy
  simp only [normalOperator,he.fderiv_eq,he.eq_of_nhds]

include hs in
lemma normal_energy_point {a : TwoForm X} (ha : IsSmooth a)
    {q : Space → HodgeNormalSymbol.W} (hq : ContDiff ℝ ∞ q) (hc : HasCompactSupport q)
    (hqD : tsupport q ⊆ D.domain) {z : Space} (hz : z ∈ D.domain) :
    MetricForms.pairing (coordinateMetric J α ht p z)
      (ManifoldForms.pullback (codifferential J α ht a) (extChartAt Model p).symm z)
      (ManifoldForms.pullback (codifferential J α ht (manifoldTest J α ht p D q)) (extChartAt Model p).symm z) +
    MetricForms.pairing (coordinateMetric J α ht p z)
      (ManifoldForms.pullback (codifferential J α ht (starTwo J α ht a)) (extChartAt Model p).symm z)
      (ManifoldForms.pullback (codifferential J α ht (starTwo J α ht (manifoldTest J α ht p D q)))
        (extChartAt Model p).symm z) =
      ⟪normalOperator J α ht p D (rawVector J α ht p D a) z,normalOperator J α ht p D q z⟫ := by
  rw [← HodgeNormalOperator.output_inner _ _ (D.frame_gram z hz),normal_delta J α hs ht p D ha hz,
    normal_manifoldTest_delta J α ht p D hs hq hc hqD hz,inner_neg_neg]
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
variable (p : X) (D : GeometricChart.Data J α ht p) [T2Space X]
lemma energyPairing_zero_off (a : TwoForm X) {q : Space → HodgeNormalSymbol.W}
    (hc : HasCompactSupport q) (hqD : tsupport q ⊆ D.domain)
    {x : X} (hx : x ∉ (extChartAt Model p).symm '' tsupport q) :
    energyPairing J α ht a (manifoldTest J α ht p D q) x = 0 := by
  unfold energyPairing GeometricAdjoint.pairing
  rw [manifoldTest_delta_zero_off J α ht p D hc hqD hx,
    manifoldTest_delta_star_zero_off J α ht p D hc hqD hx]
  have h₁ := MetricForms.pairing_zero_right (E := Space)
    (GeometricAdjoint.pointMetric J α ht x) (codifferential J α ht a x)
  have h₂ := MetricForms.pairing_zero_right (E := Space)
    (GeometricAdjoint.pointMetric J α ht x) (codifferential J α ht (starTwo J α ht a) x)
  exact (congrArg₂ (fun s t : ℝ => s+t) h₁ h₂).trans (zero_add 0)
variable [CompactSpace X] [MeasurableSpace X] [BorelSpace X] (A : FiniteCharts X)
include hs in
lemma normal_energy_integral {a : TwoForm X} (ha : IsSmooth a)
    {q : Space → HodgeNormalSymbol.W} (hq : ContDiff ℝ ∞ q) (hc : HasCompactSupport q)
    (hqD : tsupport q ⊆ D.domain) :
    (∫ x, energyPairing J α ht a (manifoldTest J α ht p D q) x ∂geometricVolume A J α) =
    ∫ z, chartDensity J α p z *
      ⟪normalOperator J α ht p D (rawVector J α ht p D a) z,normalOperator J α ht p D q z⟫ := by
  let f := energyPairing J α ht a (manifoldTest J α ht p D q)
  have hfc : Continuous f := energyPairing_continuous J α ht hs ha (manifoldTest_smooth J α hs ht p D hq hc hqD)
  have hK : IsCompact ((extChartAt Model p).symm '' tsupport q) :=
    hc.image_of_continuousOn ((continuousOn_extChartAt_symm p).mono (hqD.trans D.domain_subset))
  have hfK : tsupport f ⊆ (extChartAt Model p).symm '' tsupport q := by
    apply closure_minimal _ hK.isClosed
    intro x hx
    by_contra hn
    exact hx (energyPairing_zero_off J α ht p D a hc hqD hn)
  have hfsource : tsupport f ⊆ (extChartAt Model p).source := by
    rintro x hx
    obtain ⟨z,hz,rfl⟩ := hfK hx
    exact (extChartAt Model p).map_target (D.domain_subset (hqD hz))
  change (∫ x, f x ∂geometricVolume A J α) = _
  rw [integral_geometricVolume_coordinate A J α hs ht p f hfc hfsource,
    ← integral_indicator (isOpen_extChartAt_target p).measurableSet]
  apply integral_congr_ae
  filter_upwards [] with z
  by_cases hzq : z ∈ tsupport q
  · have hz := D.domain_subset (hqD hzq)
    rw [indicator_of_mem hz]
    change chartDensity J α p z * energyPairing J α ht a (manifoldTest J α ht p D q)
      ((extChartAt Model p).symm z) = _
    unfold energyPairing
    rw [← pairing_chart J α ht p (Or.inl rfl) _ _ hz,
      ← pairing_chart J α ht p (Or.inl rfl) _ _ hz,
      normal_energy_point J α ht p D hs ha hq hc hqD (hqD hzq)]
  · rw [normalOperator_zero_off J α ht p D q hzq,inner_zero_right,mul_zero]
    by_cases hz : z ∈ (extChartAt Model p).target
    · rw [indicator_of_mem hz]
      have hn : (extChartAt Model p).symm z ∉ (extChartAt Model p).symm '' tsupport q := by
        rintro ⟨y,hy,he⟩
        apply hzq
        have hzy : y=z := (extChartAt Model p).symm.injOn (D.domain_subset (hqD hy)) hz he
        rwa [← hzy]
      change chartDensity J α p z * energyPairing J α ht a (manifoldTest J α ht p D q)
        ((extChartAt Model p).symm z) = 0
      rw [energyPairing_zero_off J α ht p D a hc hqD hn,mul_zero]
    · rw [indicator_of_notMem hz]
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
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.frameMap_apply _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDifferential_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap_zero _root_.OAI.TamingCompatibility.GeometricHilbert.antiMultiply_apply _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeScaledDerivative_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth _root_.OAI.TamingCompatibility.HodgeNormalSymbol.symbolMap_apply _root_.OAI.TamingCompatibility.HodgeStarGeometry.starMap_apply _root_.OAI.TamingCompatibility.HodgeStarGeometry.swapMap_apply
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

variable [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X)
include hs in
lemma chart_energy_local {u : TwoForm X} (hu : IsSmooth u)
    {U : Set Space} (hU : IsOpen U) (hUD : U ⊆ D.domain)
    (a : Fin 4 → 𝓢(Space,HodgeNormalSymbol.W →L[ℝ] HodgeNormalSymbol.Q))
    (b : 𝓢(Space,HodgeNormalSymbol.W →L[ℝ] HodgeNormalSymbol.Q)) (ρ : 𝓢(Space,ℝ))
    (ha : ∀ z ∈ U, ∀ i, a i z = normalA J α ht p D i z)
    (hb : ∀ z ∈ U, b z = normalB J α ht p D z)
    (hρ : ∀ z ∈ U, ρ z = chartDensity J α p z)
    (s q : 𝓢(Space,HodgeNormalSymbol.W))
    (hsU : ∀ z ∈ U, s z = rawVector J α ht p D u z)
    (hqc : HasCompactSupport (q : Space → _)) (hqU : tsupport q ⊆ U) :
    (∫ z, ρ z * ⟪firstOrder EuclideanEnergy.e a b s z,firstOrder EuclideanEnergy.e a b q z⟫) =
      ∫ x, energyPairing J α ht u (manifoldTest J α ht p D q) x ∂geometricVolume A J α := by
  rw [normal_energy_integral J α ht hs p D A hu (q.smooth ⊤) hqc (hqU.trans hUD)]
  apply integral_congr_ae
  filter_upwards [] with z
  by_cases hz : z ∈ tsupport q
  · have hzU := hqU hz
    have he : (s : Space → _) =ᶠ[𝓝 z] rawVector J α ht p D u := by
      filter_upwards [hU.mem_nhds hzU] with y hy
      exact hsU y hy
    rw [firstOrder_local J α ht p D a b s _ he (ha z hzU) (hb z hzU),
      firstOrder_local J α ht p D a b q q Filter.EventuallyEq.rfl (ha z hzU) (hb z hzU),hρ z hzU]
  · rw [firstOrder_zero_off a b q hz,normalOperator_zero_off J α ht p D q hz]
    simp
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
open ManifoldForms ManifoldLocalization Set
open scoped Manifold ContDiff SchwartzMap
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (D : ∀ p : A.centers, GeometricChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)
lemma scalarVectorLinear_eq_make (p : A.centers) (a : smoothForms X 2) :
    scalarVectorLinear A J α ht D hD p a =
      HodgeScalar.make (scalarSchwartz A J α ht D hD p a.val a.property) := by
  simp only [scalarVectorLinear,LinearMap.sum_apply,LinearMap.comp_apply,ContinuousLinearMap.coe_coe,
    HodgeScalar.make,scalarLinear,LinearMap.coe_mk,AddHom.coe_mk]
end TamingCompatibility.HodgeChart

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
namespace TamingCompatibility.HodgeChart
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ComplexMatrix Set
open scoped Manifold ContDiff SchwartzMap
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (D : ∀ p : A.centers, GeometricChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

def realVectorSchwartz (p : A.centers) (a : smoothForms X 2) : 𝓢(Space,HodgeNormalSymbol.W) :=
  SchwartzMap.postcompCLM (retract 6) (scalarVectorLinear A J α ht D hD p a)
lemma realVectorSchwartz_apply (p : A.centers) (a : smoothForms X 2) (z : Space) (i : Fin 6) :
    realVectorSchwartz A J α ht D hD p a z i = scalar A J α ht D p a.val i z := by
  simp only [realVectorSchwartz,SchwartzMap.postcompCLM_apply,scalarVectorLinear_eq_make,
    retract_apply,HodgeScalar.make_apply,Complex.ofReal_re]
  rfl
lemma realVectorSchwartz_embed (p : A.centers) (a : smoothForms X 2) :
    SchwartzMap.postcompCLM (embed 6) (realVectorSchwartz A J α ht D hD p a) =
      scalarVectorLinear A J α ht D hD p a := by
  ext z i
  simp only [SchwartzMap.postcompCLM_apply,embed_apply,realVectorSchwartz_apply,
    scalarVectorLinear_eq_make,HodgeScalar.make_apply]
  rfl
end TamingCompatibility.HodgeChart

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

variable [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (hs : IsSmooth α)
include hs in
lemma pairing_manifoldTest_integral {a : TwoForm X} (ha : IsSmooth a)
    {q : Space → HodgeNormalSymbol.W}
    (hq : ContDiff ℝ ∞ q) (hc : HasCompactSupport q) (hqD : tsupport q ⊆ D.domain) :
    (∫ x, GeometricAdjoint.pairing J α ht a (manifoldTest J α ht p D q) x ∂geometricVolume A J α) =
    ∫ z, chartDensity J α p z *
      ⟪rawVector J α ht p D a z,q z⟫ := by
  let f := GeometricAdjoint.pairing J α ht a (manifoldTest J α ht p D q)
  have hfc : Continuous f := (GeometricAdjoint.pairing_two_smooth J α hs ht ha
    (manifoldTest_smooth J α hs ht p D hq hc hqD)).continuous
  have hK : IsCompact ((extChartAt Model p).symm '' tsupport q) :=
    hc.image_of_continuousOn ((continuousOn_extChartAt_symm p).mono (hqD.trans D.domain_subset))
  have hfK : tsupport f ⊆ (extChartAt Model p).symm '' tsupport q := by
    apply closure_minimal _ hK.isClosed
    intro x hx
    by_contra hn
    apply hx
    change MetricForms.pairing (E := Space) (GeometricAdjoint.pointMetric J α ht x) (a x)
      (manifoldTest J α ht p D q x) = 0
    rw [manifoldTest_zero_off J α ht p D q hn]
    exact MetricForms.pairing_zero_right (E := Space) _ _
  have hfsource : tsupport f ⊆ (extChartAt Model p).source := by
    rintro x hx
    obtain ⟨z,hz,rfl⟩ := hfK hx
    exact (extChartAt Model p).map_target (D.domain_subset (hqD hz))
  change (∫ x, f x ∂geometricVolume A J α) = _
  rw [integral_geometricVolume_coordinate A J α hs ht p f hfc hfsource,
    ← integral_indicator (isOpen_extChartAt_target p).measurableSet]
  apply integral_congr_ae
  filter_upwards [] with z
  by_cases hz : z ∈ (extChartAt Model p).target
  · rw [indicator_of_mem hz]
    change chartDensity J α p z * GeometricAdjoint.pairing J α ht a (manifoldTest J α ht p D q)
      ((extChartAt Model p).symm z) = _
    rw [← pairing_chart J α ht p (Or.inr rfl) a (manifoldTest J α ht p D q) hz]
    rw [pullback_manifoldTest J α ht p D q hz,pairing_coordinateTest J α ht p D a hqD z]
  · rw [indicator_of_notMem hz]
    have hqz : q z = 0 := image_eq_zero_of_notMem_tsupport (fun h => hz (D.domain_subset (hqD h)))
    simp only [hqz,inner_zero_right,mul_zero]

end TamingCompatibility.HodgeChart

end
end

section
noncomputable section

namespace TamingCompatibility.GeometricHilbert
open GeometricChart (coordinateWeight coordinateWeight_smooth)
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume
open Set Filter _root_.MeasureTheory ComplexMatrix TemperedDistribution
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).toData.source)

lemma hodge_rhs_component_test (p : A.centers) (f : PreL2 A J α hs ht true)
    {U : Set Space} (hUD : U ⊆ (D p).domain)
    (g : 𝓢(Space,HodgeNormalSymbol.W))
    (hg : ∀ z ∈ U, g z = chartDensity J α p.val z • rawVector J α ht p.val (D p).toData f.val z)
    (φ : 𝓢(Space,ℝ)) (hc : HasCompactSupport (φ : Space → ℝ)) (hφU : tsupport φ ⊆ U)
    (j : Fin 6) :
    (⟪hodgeInclusion A J α hs ht (hodgeSmooth A J α hs ht f),hodgeInclusion A J α hs ht
      (hodgeSmooth A J α hs ht (hodgeTest A J α hs ht D p (componentTest j φ)
        (full_componentTest_compact j φ hc) ((full_componentTest_support j φ).trans (hφU.trans hUD))))⟫ : ℂ) =
    ((SchwartzMap.postcompCLM (embed 6) g : 𝓢'(Space,C 6))
      (SchwartzMap.postcompCLM Complex.ofRealCLM φ)) j := by
  rw [hodge_smooth_pair,embedded_component_apply]
  congr 1
  change (∫ x, GeometricAdjoint.pairing J α ht f.val
    (manifoldTest J α ht p.val (D p).toData (componentTest j φ)) x ∂geometricVolume A J α) = _
  rw [pairing_manifoldTest_integral J α ht p.val (D p).toData A hs f.property
    ((componentTest j φ).smooth ⊤) (full_componentTest_compact j φ hc)
    ((full_componentTest_support j φ).trans (hφU.trans hUD))]
  apply integral_congr_ae
  filter_upwards [] with z
  by_cases hz : z ∈ tsupport φ
  · rw [hg z (hφU hz),real_inner_smul_left]
  · have hφz := image_eq_zero_of_notMem_tsupport hz
    simp [componentTest_apply,hφz]

end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_HeatFlow_HodgeResolvent
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
open ManifoldForms ManifoldHodge ManifoldLocalization Filter Set
open scoped Manifold ContDiff RealInnerProductSpace Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)

lemma hodgeWeakSolution_identity_raw (r : ℝ) (hr : 0 < r)
    (f : L2 A J α hs ht true) (v : hodgeEnergy A J α hs ht) :
    Variational.energy (V := hodgeEnergy A J α hs ht) (H := L2 A J α hs ht true)
      (Z := HodgeDerivativePair A J α hs ht) (hodgeInclusion A J α hs ht)
      (hodgeScaledDerivative A J α hs ht r) (hodgeWeakSolution A J α hs ht r hr f) v =
        ⟪f,hodgeInclusion A J α hs ht v⟫ := by
  exact Variational.weakSolution_identity _ _ _ f v

lemma hodgeWeakSolution_identity (r : ℝ) (hr : 0 < r)
    (f : L2 A J α hs ht true) (v : hodgeEnergy A J α hs ht) :
    ⟪hodgeResolvent A J α hs ht r f,hodgeInclusion A J α hs ht v⟫ +
      r^2*⟪hodgeWeakDerivative A J α hs ht (hodgeWeakSolution A J α hs ht r hr f),
        hodgeWeakDerivative A J α hs ht v⟫ = ⟪f,hodgeInclusion A J α hs ht v⟫ := by
  have h := hodgeWeakSolution_identity_raw A J α hs ht r hr f v
  rw [hodgeResolvent_eq A J α hs ht r hr,ContinuousLinearMap.comp_apply]
  simpa only [Variational.energy_apply,hodgeScaledDerivative_apply,
    real_inner_smul_left,real_inner_smul_right,pow_two,mul_assoc] using h

lemma hodgeResolvent_norm_le (r : ℝ) (f : L2 A J α hs ht true) :
    ‖hodgeResolvent A J α hs ht r f‖ ≤ ‖f‖ := by
  unfold hodgeResolvent
  split_ifs with hr
  · exact Variational.resolvent_norm_le _ _ _ f
  · exact le_rfl

end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeSmoothLaplacian
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

lemma hodgeSmoothShift_apply (r : ℝ) (a : PreL2 A J α hs ht true) :
    hodgeSmoothShift A J α hs ht r a = a + r^2 • hodgeLaplacian A J α hs ht a := rfl

end TamingCompatibility.GeometricHilbert

end
end

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)

def hodgeGraphResolvent (r : ℝ) (hr : 0 < r) :
    hodgeEnergy A J α hs ht →L[ℝ] hodgeEnergy A J α hs ht :=
  (hodgeWeakSolution A J α hs ht r hr).comp (hodgeInclusion A J α hs ht)

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

lemma hodgeWeakSolution_derivative_bound (r : ℝ) (hr : 0 < r)
    (f : L2 A J α hs ht true) :
    ‖hodgeWeakDerivative A J α hs ht (hodgeWeakSolution A J α hs ht r hr f)‖ ≤ r⁻¹*‖f‖ := by
  let u := hodgeWeakSolution A J α hs ht r hr f
  have hi : hodgeInclusion A J α hs ht u = hodgeResolvent A J α hs ht r f := by
    rw [hodgeResolvent_eq A J α hs ht r hr]; rfl
  have he := hodgeWeakSolution_identity A J α hs ht r hr f u
  rw [hi,real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq] at he
  have hb := hodgeResolvent_norm_le A J α hs ht r f
  have hc := real_inner_le_norm f (hodgeResolvent A J α hs ht r f)
  have hsq : (r*‖hodgeWeakDerivative A J α hs ht u‖)^2 ≤ ‖f‖^2 := by
    nlinarith [sq_nonneg ‖hodgeResolvent A J α hs ht r f‖,
      mul_le_mul_of_nonneg_left hb (norm_nonneg f)]
  have hm : r*‖hodgeWeakDerivative A J α hs ht u‖ ≤ ‖f‖ := by
    nlinarith [norm_nonneg f,mul_nonneg hr.le (norm_nonneg (hodgeWeakDerivative A J α hs ht u))]
  calc
    ‖hodgeWeakDerivative A J α hs ht u‖ = r⁻¹*(r*‖hodgeWeakDerivative A J α hs ht u‖) := by
      rw [← mul_assoc,inv_mul_cancel₀ hr.ne',one_mul]
    _ ≤ r⁻¹*‖f‖ := mul_le_mul_of_nonneg_left hm (inv_nonneg.mpr hr.le)

lemma hodgeWeakSolution_graph_bound (r : ℝ) (hr : 0 < r)
    (f : L2 A J α hs ht true) :
    ‖hodgeWeakSolution A J α hs ht r hr f‖ ≤ (1+r⁻¹)*‖f‖ := by
  have hi : hodgeInclusion A J α hs ht (hodgeWeakSolution A J α hs ht r hr f) =
      hodgeResolvent A J α hs ht r f := by
    rw [hodgeResolvent_eq A J α hs ht r hr]; rfl
  calc
    _ ≤ ‖hodgeInclusion A J α hs ht (hodgeWeakSolution A J α hs ht r hr f)‖ +
        ‖hodgeWeakDerivative A J α hs ht (hodgeWeakSolution A J α hs ht r hr f)‖ :=
      hodgeEnergy_prod_norm_le A J α hs ht _
    _ ≤ ‖f‖+r⁻¹*‖f‖ := by
      rw [hi]
      exact add_le_add (hodgeResolvent_norm_le A J α hs ht r f)
        (hodgeWeakSolution_derivative_bound A J α hs ht r hr f)
    _ = _ := by ring

lemma hodgeWeakSolution_graph_small_bound (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (f : L2 A J α hs ht true) :
    ‖hodgeWeakSolution A J α hs ht r hr f‖ ≤ 2*r⁻¹*‖f‖ := by
  have hi : 1 ≤ r⁻¹ := (one_le_inv₀ hr).mpr hr1
  exact (hodgeWeakSolution_graph_bound A J α hs ht r hr f).trans
    (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg f))
end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeScaleH3
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.frameMap_apply _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDifferential_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap_zero
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

lemma hodgeRegularizedGraph_small_bound (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (f : L2 A J α hs ht true) :
    ‖hodgeRegularizedGraph A J α hs ht r hr f‖ ≤ 2*r⁻¹*‖f‖ := by
  exact (hodgeWeakSolution_graph_small_bound A J α hs ht r hr hr1 _).trans
    (mul_le_mul_of_nonneg_left
      ((hodgeResolvent_norm_le A J α hs ht r _).trans (hodgeResolvent_norm_le A J α hs ht r f))
      (mul_nonneg (by norm_num) (inv_nonneg.mpr hr.le)))

end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end


