-- Prove2me | Definitions.Def_OAIQ239Tc027
-- name    : OAIQ239Tc027
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T23:16:55.556562+00:00
-- url     : https://prove2.me/theorems/07990683-198f-4740-82cf-a641ed3af66a
-- title:
--   Definitions bundle OAIQ239Tc027 of the split of OpenAI, Taming implies compatibility on four-manifolds
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.TamingCompatibility.taming_implies_compatibility`, carved from OpenAI's openai/math development (OpenAI, *Taming implies compatibility on four-manifolds*, OpenAI Math Release, October 6, 2026, result family 342, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 19 declarations of OpenAI's Lean: 10 definitions and 9 theorems. The definitions and types are `OAI.TamingCompatibility.GeometricHilbert.hodgeCubeCommutator`, `OAI.TamingCompatibility.GeometricHilbert.hodgeCubeRepresents`, `OAI.TamingCompatibility.GeometricHilbert.hodgeDomainStar`, `OAI.TamingCompatibility.GeometricHilbert.hodgeRegularization`, `OAI.TamingCompatibility.GeometricHilbert.hodgeScaleH3Input`, `OAI.TamingCompatibility.GeometricHilbert.hodgeScaleInput`, `OAI.TamingCompatibility.GeometricHilbert.l2CurrentSource`, `OAI.TamingCompatibility.GeometricHilbert.nonharmonicCorrectionLM`, `OAI.TamingCompatibility.GeometricHilbert.positiveL2Source`, `OAI.TamingCompatibility.GeometricHilbert.scalarCorrectionLM`.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: `TamingCompatibility_DifferentialForms_RadialGeometricAssembly`, `TamingCompatibility_DifferentialForms_RadialScalarOff`, `TamingCompatibility_HeatFlow_HodgeResolvent`, `TamingCompatibility_Hodge_HodgeGlobalEvaluation`, `TamingCompatibility_Hodge_HodgeL2`, `TamingCompatibility_Hodge_HodgeLocalSmooth`, `TamingCompatibility_Hodge_HodgePairAllTests`, `TamingCompatibility_Hodge_HodgePairing`, `TamingCompatibility_Hodge_HodgeRawRegular`, `TamingCompatibility_Hodge_HodgeScaleH3`, `TamingCompatibility_Hodge_HodgeScaleSmoothing`, `TamingCompatibility_Hodge_HodgeSmoothCommutator`, `TamingCompatibility_Hodge_HodgeSmoothPatch`.
--
--   **Imports.** It imports the published bundle `Def_TamingCompatibility`; the bundles `OAIQ239Tc021`, `OAIQ239Tc022`, `OAIQ239Tc023` and `OAIQ239Tc024` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ239Tc028` and `OAIQ239Tc029`; the proof of `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.leadingKernelForm_weak_laplacian`.
-- source:
--   OpenAI, Taming implies compatibility on four-manifolds, OpenAI Math Release, October 6, 2026, https://github.com/openai/math (result family 342; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Taming-implies-compatibility-on-four-manifolds-October-6-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit 7ef5c0c

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc021
import Definitions.Def_OAIQ239Tc022
import Definitions.Def_OAIQ239Tc023
import Definitions.Def_OAIQ239Tc024

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_RadialScalarOff
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete
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
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter ComplexMatrix _root_.MeasureTheory
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)

def scalarCorrectionLM (Gs : antiPre A J α hs ht →ₗ[ℝ] antiPre A J α hs ht)
    (p : A.centers) (K : Set Space) (hK : IsCompact K)
    (hKD : K ⊆ (D p).domain) (j : Fin 2) (z : Space) :
    supportedSchwartz K →ₗ[ℝ] MetricForms.Form Space 2 :=
  (smoothPullbackLM p.val z).comp ((d.comp (antiDelta A J α hs ht)).comp
    (Gs.comp (scalarTestLM A J α hs ht D p K hK hKD j)))

end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_RadialGeometricAssembly
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete
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
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter ComplexMatrix _root_.MeasureTheory EuclideanSobolevOperators RadialPotential
open scoped Manifold ContDiff Topology SchwartzMap LineDeriv RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

def nonharmonicCorrectionLM (Gs : antiPre A J α hs ht →ₗ[ℝ] antiPre A J α hs ht)
    (p : X) (y : Space) : antiPre A J α hs ht →ₗ[ℝ] MetricForms.Form Space 2 :=
  (smoothPullbackLM p y).comp ((d.comp (antiDelta A J α hs ht)).comp Gs)

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

def hodgeRegularization (r : ℝ) : L2 A J α hs ht true →L[ℝ] L2 A J α hs ht true :=
  hodgeResolvent A J α hs ht r ^ 3

end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeRawRegular
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
open Set Filter _root_.MeasureTheory ComplexMatrix TemperedDistribution HilbertSobolev
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).toData.source)

omit [T2Space X] in
lemma hodgeRegularizedGraph_inclusion (r : ℝ) (hr : 0 < r)
    (f : L2 A J α hs ht true) :
    hodgeInclusion A J α hs ht (hodgeRegularizedGraph A J α hs ht r hr f) =
      hodgeRegularization A J α hs ht r f := by
  change hodgeInclusion A J α hs ht (hodgeWeakSolution A J α hs ht r hr
    (hodgeResolvent A J α hs ht r (hodgeResolvent A J α hs ht r f))) = _
  rw [← ContinuousLinearMap.comp_apply,← hodgeResolvent_eq A J α hs ht r hr]
  rfl

end TamingCompatibility.GeometricHilbert

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

lemma hodgeAmbientStar_graph (a : PreL2 A J α hs ht true) :
    hodgeAmbientStar A J α hs ht (hodgeGraph A J α hs ht a) =
      hodgeGraph A J α hs ht (preStar A J α hs ht a) := by
  apply (WithLp.linearEquiv 2 ℝ _).injective
  apply Prod.ext
  · exact l2Star_smooth A J α hs ht a
  · apply (WithLp.linearEquiv 2 ℝ _).injective
    change (smoothL2 A J α hs ht false (hodgeDelta A J α hs ht (preStar A J α hs ht a)),
      smoothL2 A J α hs ht false (hodgeDelta A J α hs ht a)) =
      (smoothL2 A J α hs ht false (hodgeDelta A J α hs ht (preStar A J α hs ht a)),
      smoothL2 A J α hs ht false (hodgeDelta A J α hs ht (preStar A J α hs ht (preStar A J α hs ht a))))
    rw [preStar_square]

lemma hodgeAmbientStar_mem (u : hodgeEnergy A J α hs ht) :
    hodgeAmbientStar A J α hs ht u.val ∈ hodgeEnergy A J α hs ht := by
  have hc : _root_.IsClosed {v : HodgeGraphSpace A J α hs ht |
      hodgeAmbientStar A J α hs ht v ∈ hodgeEnergy A J α hs ht} :=
    (LinearMap.range (hodgeGraph A J α hs ht)).isClosed_topologicalClosure.preimage
      (hodgeAmbientStar A J α hs ht).continuous
  apply (closure_minimal ?_ hc) u.property
  rintro _ ⟨a,rfl⟩
  change hodgeAmbientStar A J α hs ht (hodgeGraph A J α hs ht a) ∈ hodgeEnergy A J α hs ht
  rw [hodgeAmbientStar_graph]
  exact subset_closure ⟨_,rfl⟩

def hodgeDomainStar : hodgeEnergy A J α hs ht →ₗᵢ[ℝ] hodgeEnergy A J α hs ht where
  toFun u := ⟨hodgeAmbientStar A J α hs ht u.val,hodgeAmbientStar_mem A J α hs ht u⟩
  map_add' u v := Subtype.ext ((hodgeAmbientStar A J α hs ht).map_add u.val v.val)
  map_smul' c u := Subtype.ext ((hodgeAmbientStar A J α hs ht).map_smul c u.val)
  norm_map' u := (hodgeAmbientStar A J α hs ht).norm_map u.val

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

lemma hodgeLaplacian_green_weak (a : PreL2 A J α hs ht true)
    (v : hodgeEnergy A J α hs ht) :
    ⟪smoothL2 A J α hs ht true (hodgeLaplacian A J α hs ht a),
      hodgeInclusion A J α hs ht v⟫ =
      ⟪hodgeWeakDerivative A J α hs ht (hodgeSmooth A J α hs ht a),
        hodgeWeakDerivative A J α hs ht v⟫ := by
  rw [hodgeLaplacian_apply,map_add,inner_add_left,← l2Star_smooth,
    smoothL2_preD,smoothL2_preD]
  change ⟪testDerivative A J α hs ht (hodgeDelta A J α hs ht a),v.val.fst⟫ +
    ⟪l2Star A J α hs ht (testDerivative A J α hs ht
      (hodgeDelta A J α hs ht (preStar A J α hs ht a))),v.val.fst⟫ = _
  rw [hodgeEnergy_weak,hodgeEnergy_weak_star]
  rfl

end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeSmoothPatch
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
open ManifoldForms ManifoldHodge Set
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J) (p : X)
  (D : GeometricChart.Data J α ht p)

lemma manifoldTest_eq (b : TwoForm X) (q : Space → HodgeNormalSymbol.W)
    (hqD : tsupport q ⊆ D.domain)
    (hraw : ∀ z ∈ D.domain, q z = rawVector J α ht p D b z)
    (hbzero : ∀ x ∉ (extChartAt Model p).symm '' D.domain, b x = 0) :
    manifoldTest J α ht p D q = b := by
  funext x
  by_cases hx : x ∈ (extChartAt Model p).symm '' D.domain
  · obtain ⟨z,hz,rfl⟩ := hx
    apply form_eq_of_chart_pullback p _ _ ((extChartAt Model p).map_target (D.domain_subset hz))
    rw [(extChartAt Model p).right_inv (D.domain_subset hz)]
    change ManifoldForms.pullback (manifoldTest J α ht p D q) (extChartAt Model p).symm z =
      ManifoldForms.pullback b (extChartAt Model p).symm z
    rw [pullback_manifoldTest J α ht p D q (D.domain_subset hz)]
    exact (congrArg (HodgeFrame.reconstruct (coordinateMetric J α ht p z)
      (fun i => D.frame i z)) (hraw z hz)).trans (rawVector_expansion J α ht p D b hz)
  · rw [hbzero x hx,manifoldTest_zero_off J α ht p D q]
    exact fun h => hx ((image_mono hqD) h)
end TamingCompatibility.HodgeChart
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart Set ComplexMatrix
open scoped Manifold ContDiff SchwartzMap BoundedContinuousFunction
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)

omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma hodge_exists_patch (p : A.centers) {U : Set Space} (hU : IsOpen U)
    (hUD : U ⊆ (D p).domain) {z : Space} (hz : z ∈ U)
    (g : Space →ᵇ C 6) (hg : ContDiff ℝ ∞ (g : Space → C 6)) :
    ∃ W : Set Space, IsOpen W ∧ z ∈ W ∧ W ⊆ U ∧ ∃ w : PreL2 A J α hs ht true,
      ∀ y ∈ W, rawVector J α ht p.val (D p).toData w.val y = retract 6 (g y) := by
  obtain ⟨η,hc,hηU,W,hW,hzW,hWU,hη⟩ := SchwartzCutoff.exists_one_near hU hz
  let q : Space → HodgeNormalSymbol.W := fun y => η y • retract 6 (g y)
  have hq : ContDiff ℝ ∞ q := (η.smooth ⊤).smul ((retract 6).contDiff.comp hg)
  have hqs : tsupport q ⊆ tsupport η := tsupport_smul_subset_left _ _
  have hqc : HasCompactSupport q := hc.of_isClosed_subset (isClosed_tsupport q) hqs
  let ψ := hqc.toSchwartzMap hq
  let w := hodgeTest A J α hs ht D p ψ hqc (hqs.trans (hηU.trans hUD))
  refine ⟨W,hW,hzW,hWU,w,fun y hy => ?_⟩
  change rawVector J α ht p.val (D p).toData (manifoldTest J α ht p.val (D p).toData q) y = _
  rw [rawVector_manifoldTest J α ht p.val (D p).toData q (hUD (hWU hy))]
  change η y • retract 6 (g y) = _
  rw [hη y hy,one_smul]

omit [MeasurableSpace X] [BorelSpace X] in
lemma hodge_supported_test (p : A.centers) {U : Set Space} (hU : IsOpen U)
    (hUD : U ⊆ (D p).domain) (ρ : X → ℝ) (hρ : ContMDiff Model 𝓘(ℝ,ℝ) ∞ ρ)
    (hρU : ∀ x ∈ tsupport ρ, x ∈ (extChartAt Model p.val).source ∧ extChartAt Model p.val x ∈ U)
    (a : PreL2 A J α hs ht true) :
    ∃ q : 𝓢(Space,HodgeNormalSymbol.W), ∃ hc : HasCompactSupport (q : Space → HodgeNormalSymbol.W),
      ∃ hqU : tsupport q ⊆ U,
        hodgeTest A J α hs ht D p q hc (hqU.trans hUD) = hodgeMultiply A J α hs ht ρ hρ a := by
  let K := (extChartAt Model p.val) '' tsupport ρ
  have hK : IsCompact K := (isClosed_tsupport ρ).isCompact.image_of_continuousOn
    ((continuousOn_extChartAt p.val).mono (fun x hx => (hρU x hx).1))
  have hKU : K ⊆ U := by rintro _ ⟨x,hx,rfl⟩; exact (hρU x hx).2
  obtain ⟨η,hηc,hηU,hηone⟩ := SchwartzCutoff.exists_one_on_compact hK hU hKU
  let b := hodgeMultiply A J α hs ht ρ hρ a
  let q := SchwartzCutoff.schwartz (D p).domain_open (rawVector_smooth J α ht p.val (D p).toData b.property)
    (η.smooth ⊤) hηc (hηU.trans hUD)
  have hqc : HasCompactSupport (q : Space → HodgeNormalSymbol.W) := SchwartzCutoff.compact hηc
  have hqU : tsupport q ⊆ U := (tsupport_smul_subset_left _ _).trans hηU
  refine ⟨q,hqc,hqU,?_⟩
  apply Subtype.ext
  change manifoldTest J α ht p.val (D p).toData q = b.val
  apply manifoldTest_eq J α ht p.val (D p).toData b.val q (hqU.trans hUD)
  · intro z hz
    change η z • rawVector J α ht p.val (D p).toData (fun x => ρ x • a.val x) z =
      rawVector J α ht p.val (D p).toData (fun x => ρ x • a.val x) z
    rw [rawVector_fun_smul]
    by_cases hr : ρ ((extChartAt Model p.val).symm z) = 0
    · simp only [hr,zero_smul,smul_zero]
    · rw [hηone z ⟨(extChartAt Model p.val).symm z,subset_closure hr,
        (extChartAt Model p.val).right_inv ((D p).domain_subset hz)⟩,one_smul]
  · intro x hx
    change ρ x • a.val x = 0
    have hz : ρ x = 0 := by
      by_contra hn
      have hh := hρU x (subset_closure hn)
      exact hx ⟨extChartAt Model p.val x,hUD hh.2,(extChartAt Model p.val).left_inv hh.1⟩
    rw [hz,zero_smul]
end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgePairAllTests
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.GeometricHilbert

section LocalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart Set ComplexMatrix
open scoped Manifold ContDiff SchwartzMap RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J) (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
lemma hodge_pair_all_tests_eq (p : A.centers) {U : Set Space} (hUD : U ⊆ (D p).domain)
    (u v : L2 A J α hs ht true)
    (h : ∀ (φ : 𝓢(Space,ℝ)) (hc : HasCompactSupport (φ : Space → ℝ))
      (hφU : tsupport φ ⊆ U) (j : Fin 6),
      ⟪u,smoothL2 A J α hs ht true
        (hodgeTest A J α hs ht D p (componentTest j φ) (full_componentTest_compact j φ hc)
          ((full_componentTest_support j φ).trans (hφU.trans hUD)))⟫ =
      ⟪v,smoothL2 A J α hs ht true
        (hodgeTest A J α hs ht D p (componentTest j φ) (full_componentTest_compact j φ hc)
          ((full_componentTest_support j φ).trans (hφU.trans hUD)))⟫)
    (q : 𝓢(Space,HodgeNormalSymbol.W)) (hc : HasCompactSupport (q : Space → HodgeNormalSymbol.W))
    (hqU : tsupport q ⊆ U) :
    ⟪u,smoothL2 A J α hs ht true (hodgeTest A J α hs ht D p q hc (hqU.trans hUD))⟫ =
    ⟪v,smoothL2 A J α hs ht true (hodgeTest A J α hs ht D p q hc (hqU.trans hUD))⟫ := by
  classical
  let φ (j : Fin 6) := realComponent q j
  have hφc (j : Fin 6) : HasCompactSupport (φ j : Space → ℝ) :=
    hc.of_isClosed_subset (isClosed_tsupport _) (realComponent_support q j)
  have hφU (j : Fin 6) : tsupport (φ j) ⊆ U := (realComponent_support q j).trans hqU
  let w (j : Fin 6) := hodgeTest A J α hs ht D p (componentTest j (φ j))
    (full_componentTest_compact j (φ j) (hφc j)) ((full_componentTest_support j (φ j)).trans ((hφU j).trans hUD))
  have he : hodgeTest A J α hs ht D p q hc (hqU.trans hUD) = ∑ j, w j := by
    apply Subtype.ext
    change manifoldTest J α ht p.val (D p).toData q = (∑ j, w j).val
    rw [show (∑ j, w j).val = ∑ j, (w j).val from
      map_sum (smoothForms X 2).subtype w Finset.univ]
    change manifoldTest J α ht p.val (D p).toData q =
      ∑ j, manifoldTest J α ht p.val (D p).toData (componentTest j (φ j))
    rw [← manifoldTest_sum]
    exact congrArg (manifoldTest J α ht p.val (D p).toData) (real_full_decompose q)
  rw [he,map_sum,inner_sum,inner_sum]
  exact Finset.sum_congr rfl (fun j _ => h (φ j) (hφc j) (hφU j) j)
open GeometricChart (coordinateWeight coordinateWeight_smooth)
open HilbertSobolev
end LocalCharts

open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart Set _root_.MeasureTheory
open scoped Manifold ContDiff RealInnerProductSpace
end TamingCompatibility.GeometricHilbert

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgePairing
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
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart
open Set _root_.MeasureTheory
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

def hodgeCubeRepresents (r : ℝ) (F : PreL2 A J α hs ht true →ₗ[ℝ] ℝ)
    (U : L2 A J α hs ht true) : Prop :=
  ∀ a : PreL2 A J α hs ht true,
    ⟪U,smoothL2 A J α hs ht true ((hodgeSmoothShift A J α hs ht r ^ 3) a)⟫ = F a

attribute [local instance] unitMeasurable unitBorel
end TamingCompatibility.GeometricHilbert

end
end

end
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

def hodgeScaleInput (r : ℝ) (hr : 0 < r) : L2 A J α hs ht true →L[ℝ] hodgeEnergy A J α hs ht :=
  let a := (r^2)⁻¹
  let b := 1-a
  let U₁ := hodgeWeakSolution A J α hs ht r hr
  let U₂ := U₁.comp (hodgeResolvent A J α hs ht r)
  let U₃ := hodgeRegularizedGraph A J α hs ht r hr
  a • (a • U₁+b • U₂)+b • (a • U₂+b • U₃)

end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeSmoothCommutator
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

lemma hodgePowerCommutator_apply (k : ℕ) (a : PreL2 A J α hs ht true) :
    hodgePowerCommutator A J α hs ht k a =
      ((hodgeLaplacian A J α hs ht)^k) (preAntiProjection A J α hs ht a) -
        preAntiProjection A J α hs ht (((hodgeLaplacian A J α hs ht)^k) a) := rfl

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

def hodgeCubeCommutator (r : ℝ) : PreL2 A J α hs ht true →ₗ[ℝ] PreL2 A J α hs ht true :=
  ((hodgeSmoothShift A J α hs ht r)^3).comp (preAntiProjection A J α hs ht).toLinearMap -
    (preAntiProjection A J α hs ht).toLinearMap.comp ((hodgeSmoothShift A J α hs ht r)^3)

end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeL2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart Set _root_.MeasureTheory Filter
open scoped Manifold ContDiff RealInnerProductSpace Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)

def l2CurrentSource (Q : L2 A J α hs ht true) : PreL2 A J α hs ht true →ₗ[ℝ] ℝ where
  toFun a := ⟪Q,smoothL2 A J α hs ht true a⟫
  map_add' a b := by rw [map_add,inner_add_right]
  map_smul' t a := by rw [map_smul,inner_smul_right]; rfl

end TamingCompatibility.GeometricHilbert

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart Set _root_.MeasureTheory
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
attribute [local instance] unitMeasurable unitBorel 

def positiveL2Source (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsFiniteMeasure μ] :
    PreL2 A J α hs ht true →ₗ[ℝ] ℝ := unitMeasureCurrent J (hermitianMetric J α hs ht) μ

end TamingCompatibility.GeometricHilbert

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeScaleH3
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

def hodgeScaleH3Input (r : ℝ) (hr : 0 < r) : L2 A J α hs ht true →L[ℝ] hodgeEnergy A J α hs ht :=
  (r^2)⁻¹ • ((hodgeWeakSolution A J α hs ht r hr).comp (hodgeResolvent A J α hs ht r))+
    (1-(r^2)⁻¹) • hodgeRegularizedGraph A J α hs ht r hr

end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end


