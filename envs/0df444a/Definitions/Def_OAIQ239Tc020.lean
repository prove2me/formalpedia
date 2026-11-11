-- Prove2me | Definitions.Def_OAIQ239Tc020
-- name    : OAIQ239Tc020
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T22:33:41.364265+00:00
-- url     : https://prove2.me/theorems/3c82a91f-8dd8-4676-bdc2-4b044f9918da
-- title:
--   Definitions bundle OAIQ239Tc020 of the split of OpenAI, Taming implies compatibility on four-manifolds
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.TamingCompatibility.taming_implies_compatibility`, carved from OpenAI's openai/math development (OpenAI, *Taming implies compatibility on four-manifolds*, OpenAI Math Release, October 6, 2026, result family 342, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 25 declarations of OpenAI's Lean: 7 definitions, 1 instance and 17 theorems. The definitions and types are `OAI.TamingCompatibility.GeometricHilbert.hodgeMultiply`, `OAI.TamingCompatibility.GeometricHilbert.normalizedRawRHSMap`, `OAI.TamingCompatibility.GeometricHilbert.smoothPullbackLM`, `OAI.TamingCompatibility.GeometricHilbert.testDerivative`, `OAI.TamingCompatibility.closedUnitEvaluation`, `OAI.TamingCompatibility.smoothUnitEvaluation`, `OAI.TamingCompatibility.unitMeasureCurrent`.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: `TamingCompatibility_Charts_ChartReconstruction`, `TamingCompatibility_Charts_Coordinates`, `TamingCompatibility_DifferentialForms_AntiEnergyWeak`, `TamingCompatibility_DifferentialForms_ClosedUnitEvaluation`, `TamingCompatibility_DifferentialForms_RadialScalarOff`, `TamingCompatibility_DifferentialForms_SmoothUnitEvaluation`, `TamingCompatibility_Hodge_HodgeFrameDifferential`, `TamingCompatibility_Hodge_HodgeFrameTest`, `TamingCompatibility_Hodge_HodgeGeometricGarding`, `TamingCompatibility_Hodge_HodgeNormalDistribution`, `TamingCompatibility_Hodge_HodgeSmoothPatch`, `TamingCompatibility_Hodge_HodgeTestPairing`, `TamingCompatibility_Hodge_HodgeWedgeEnergy`, `TamingCompatibility_Hodge_NormalizedHarmonicRHS`.
--
--   **Imports.** It imports the published bundle `Def_TamingCompatibility`; the bundles `OAIQ239Tc014`, `OAIQ239Tc015` and `OAIQ239Tc016` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ239Tc022`, `OAIQ239Tc023` and `OAIQ239Tc024`; the statements `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.concentration_double_physical_tail`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.concentration_forces_correction_zero`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.concentration_plane_estimate`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.globalConcentration_Q_control`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.globalConcentration_current_control`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.physicalGradientMass_L2_limit`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.separating_current_angular_moment`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.separating_current_euclidean_angular_profile`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.separating_current_second_variation_limit`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.separating_current_variation_limit`, `OAI.TamingCompatibility.GeometricHilbert.separating_current_L2_correction` and `OAI.TamingCompatibility.separating_probability_local_quadratic`; the proofs of `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.concentration_double_physical_tail`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.concentration_plane_estimate`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.globalConcentration_Q_control`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.globalConcentration_current_control` and `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.physicalGradientMass_L2_limit`.
-- source:
--   OpenAI, Taming implies compatibility on four-manifolds, OpenAI Math Release, October 6, 2026, https://github.com/openai/math (result family 342; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Taming-implies-compatibility-on-four-manifolds-October-6-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit 7ef5c0c

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc014
import Definitions.Def_OAIQ239Tc015
import Definitions.Def_OAIQ239Tc016

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_ChartReconstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.ManifoldForms
open Set
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X] {k : ℕ}
lemma form_eq_of_chart_pullback (p : X) (a b : Form X k) {x : X}
    (hx : x ∈ (extChartAt Model p).source)
    (h : pullback a (extChartAt Model p).symm (extChartAt Model p x) =
      pullback b (extChartAt Model p).symm (extChartAt Model p x)) : a x = b x := by
  have hi := mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt' (I := Model) hx
  simp only [Model,modelWithCornersSelf_coe,Set.range_id,mfderivWithin_univ] at hi
  have hh := congrArg (fun c : Space [⋀^Fin k]→L[ℝ] ℝ =>
    c.compContinuousLinearMap (mfderiv Model Model (extChartAt Model p) x)) h
  simp only [pullback] at hh
  erw [(extChartAt Model p).left_inv hx] at hh
  change (a x).compContinuousLinearMap
      (mfderiv Model Model (extChartAt Model p).symm (extChartAt Model p x) ∘L
        mfderiv Model Model (extChartAt Model p) x) =
    (b x).compContinuousLinearMap
      (mfderiv Model Model (extChartAt Model p).symm (extChartAt Model p x) ∘L
        mfderiv Model Model (extChartAt Model p) x) at hh
  erw [hi] at hh
  exact hh
end TamingCompatibility.ManifoldForms

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_Coordinates
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Add _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Inner _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Module _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Normed _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
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

instance globalL2_complete : CompleteSpace (globalL2 A k) :=
  (LinearMap.range (localizeL2 A k)).isClosed_topologicalClosure.completeSpace_coe

end TamingCompatibility.ManifoldLocalization

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_AntiEnergyWeak
attribute [-instance] _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)

def testDerivative (b : PreL2 A J α hs ht false) : L2 A J α hs ht true :=
  smoothL2 A J α hs ht true ⟨exteriorDerivative b.val,b.property.exteriorDerivative⟩

end TamingCompatibility.GeometricHilbert

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_ClosedUnitEvaluation
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Add _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Inner _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Module _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Normed _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete
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

def closedUnitEvaluation (J : AlmostComplexStructure X)
    (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type)) :
    smoothClosedInvariantForms J →ₗ[ℝ] C(MetricUnit g, ℝ) where
  toFun α := unitEvaluation J g α.val α.property.1
  map_add' _ _ := by ext p; rfl
  map_smul' _ _ := by ext p; rfl

end TamingCompatibility

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_SmoothUnitEvaluation
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Add _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Inner _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Module _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Normed _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete
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
attribute [local instance] unitMeasurable unitBorel

def smoothUnitEvaluation (J : AlmostComplexStructure X)
    (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type)) :
    ManifoldForms.smoothForms X 2 →ₗ[ℝ] C(MetricUnit g, ℝ) where
  toFun α := unitEvaluation J g α.val α.property
  map_add' _ _ := by ext p; rfl
  map_smul' _ _ := by ext p; rfl

def unitMeasureCurrent [CompactSpace X] [T2Space X]
    (J : AlmostComplexStructure X)
    (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))
    (μ : Measure (MetricUnit g)) [IsFiniteMeasure μ] :
    ManifoldForms.smoothForms X 2 →ₗ[ℝ] ℝ where
  toFun α := ∫ p, smoothUnitEvaluation J g α p ∂μ
  map_add' α β := by
    simp only [map_add, ContinuousMap.add_apply]
    exact integral_add
      ((smoothUnitEvaluation J g α).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      ((smoothUnitEvaluation J g β).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
  map_smul' c α := by
    simp only [map_smul, ContinuousMap.smul_apply, RingHom.id_apply]
    exact integral_smul _ _

end TamingCompatibility

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_NormalizedHarmonicRHS
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
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set ComplexMatrix
open scoped Manifold ContDiff SchwartzMap LineDeriv RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

def normalizedRawRHSMap (p : A.centers) (τ ρ : 𝓢(Space,ℝ)) (L : Space ≃L[ℝ] Space) :
    antiPre A J α hs ht →ₗ[ℝ] 𝓢(Space,C 2) :=
  (((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L.symm).restrictScalars ℝ).toLinearMap.comp
    (SchwartzMap.postcompCLM (embed 2)).toLinearMap).comp
      ((2:ℝ) • (SchwartzMap.smulLeftCLM EuclideanEnergy.Pair ρ).toLinearMap.comp
        ((SchwartzMap.smulLeftCLM EuclideanEnergy.Pair τ).toLinearMap.comp
          ((SchwartzMap.postcompCLM (retract 2)).toLinearMap.comp
            ((pairLinear A J α ht D hD p).comp (antiPre A J α hs ht).subtype))))

end TamingCompatibility.GeometricHilbert

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_RadialScalarOff
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

def smoothPullbackLM (p : X) (z : Space) :
    smoothForms X 2 →ₗ[ℝ] MetricForms.Form Space 2 where
  toFun a := ManifoldForms.pullback a.val (extChartAt Model p).symm z
  map_add' a b := congrFun (ManifoldForms.pullback_add a.val b.val (extChartAt Model p).symm) z
  map_smul' c a := congrFun (ManifoldForms.pullback_smul c a.val (extChartAt Model p).symm) z

end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeFrameDifferential
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.HodgeNormalSymbol.symbolMap_apply _root_.OAI.TamingCompatibility.HodgeStarGeometry.starMap_apply _root_.OAI.TamingCompatibility.HodgeStarGeometry.swapMap_apply
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
namespace TamingCompatibility.HodgeNormalOperator
open MetricModel MetricForms MetricHodge ExteriorForms ContinuousAlternatingMap
open EuclideanEnergy HodgeFrame
open HodgeNormalSymbol (W Q)

lemma rawPrincipal_eq (g : Metric V) (F : MetricForms.Form V 2) (b : Fin 4 → V)
    (hb : ∀ i j, g.bilinear (b i) (b j) = if i=j then 1 else 0)
    (J : V →L[ℝ] V) (horth : ∀ u v, g.bilinear (J u) (J v) = g.bilinear u v)
    (h0 : J (b 0) = b 1) (h1 : J (b 1) = -b 0)
    (h2 : J (b 2) = b 3) (h3 : J (b 3) = -b 2)
    (hF : ∀ u v, F ![u,v] = g.bilinear (J u) v) (i : Fin 4) :
    rawPrincipal g F b (basisForm g b) (fun j => starTwo g J F (basisForm g b j)) i =
      HodgeFrozenEnergy.coefficient b i := by
  ext u k
  simp only [rawPrincipal,_root_.add_apply,ContinuousLinearMap.comp_apply,
    combine_basis,combine_star_basis,wedgeBy_apply,starThreeCLM_apply,
    left_apply,right_apply,PiLp.add_apply]
  have hA (t : Fin 4) := star_wedge_star_coordinate g (by simp [V]) b hb J horth h0 h1 h2 h3 F hF
    (EuclideanSpace.proj i) (reconstruct g b u) t
  have hB (t : Fin 4) := star_wedge_coordinate g (by simp [V]) b hb J h0 h1 h2 h3 F hF
    (EuclideanSpace.proj i) (reconstruct g b u) t
  simp only [coordinates_reconstruct g b hb] at hA hB
  fin_cases k <;>
    simp [join,LocalMatrixOperator.frameVector_apply,
      HodgeFrozenEnergy.coefficient,HodgeNormalSymbol.normalSymbol_apply,HodgeNormalSymbol.symbol]
  all_goals first | exact hA _ | exact hB _

end TamingCompatibility.HodgeNormalOperator

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeGeometricGarding
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.HodgeNormalSymbol.symbolMap_apply _root_.OAI.TamingCompatibility.HodgeStarGeometry.starMap_apply _root_.OAI.TamingCompatibility.HodgeStarGeometry.swapMap_apply
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

variable (g : V → Metric V) (J : V → V →L[ℝ] V) (F : V → MetricForms.Form V 2)
  (b : Fin 4 → V → V) {U : Set V} (hU : IsOpen U)
  (hg : ContDiffOn ℝ ∞ (fun x => (g x).bilinear) U) (hJ : ContDiffOn ℝ ∞ J U)
  (hJs : ∀ x ∈ U, ∀ u, J x (J x u) = -u)
  (hgJ : ∀ x ∈ U, ∀ u v, (g x).bilinear (J x u) (J x v) = (g x).bilinear u v)
  (hF : ContDiffOn ℝ ∞ F U) (hb : ∀ i, ContDiffOn ℝ ∞ (b i) U)
  (hgram : ∀ x ∈ U, ∀ i j, (g x).bilinear (b i x) (b j x) = if i=j then 1 else 0)
  (hcplx : ∀ x ∈ U, J x (b 0 x) = b 1 x ∧ J x (b 1 x) = -b 0 x ∧
    J x (b 2 x) = b 3 x ∧ J x (b 3 x) = -b 2 x)
  (hfund : ∀ x ∈ U, ∀ u v, F x ![u,v] = (g x).bilinear (J x u) v)
include hU hg hJ hJs hgJ hF hb hgram hcplx hfund
lemma operator_system (f : Field) (hf : ∀ j, tsupport (f j) ⊆ U) (x : V) :
    operator g J F b f x = HodgeMatrixEnergy.system (principal b) (lower g J F b) f x := by
  by_cases hx : x ∈ U
  · obtain ⟨h0,h1,h2,h3⟩ := hcplx x hx
    have he := operator_expansion (g x) (F x) (fun i => b i x)
      (frame g b) (starFrame g J F b) (fun j => f j) (fun j => (f j).differentiableAt)
      (fun j => ((frame_smooth hg hb j).differentiableOn (by simp)).differentiableAt (hU.mem_nhds hx))
      (fun j => ((starFrame_smooth g J F b hU hg hJ hJs hgJ hF hb j).differentiableOn
        (by simp)).differentiableAt (hU.mem_nhds hx))
    have hr (i : Fin 4) : rawPrincipal (g x) (F x) (fun i => b i x)
        (fun j => frame g b j x) (fun j => starFrame g J F b j x) i = principal b i x :=
      rawPrincipal_eq (g x) (F x) (fun i => b i x) (hgram x hx) (J x) (hgJ x hx)
        h0 h1 h2 h3 (hfund x hx) i
    simp only [hr] at he
    change left _ (starThree _ _ (extDeriv (fun y => ∑ j, f j y • starFrame g J F b j y) x)) +
      right _ (starThree _ _ (extDeriv (fun y => ∑ j, f j y • frame g b j y) x)) =
      (∑ i, principal b i x (WithLp.toLp 2 (fun j => fderiv ℝ (f j) x (e i)))) +
      HodgeNormalOperator.lower (g x) (F x) (fun i => b i x) (frame g b) (starFrame g J F b) x
        (WithLp.toLp 2 (fun j => f j x))
    exact he
  · have hn (j : Fin 6) : x ∉ tsupport (f j) := fun h => hx (hf j h)
    have hz (j : Fin 6) := image_eq_zero_of_notMem_tsupport (hn j)
    have hd (j : Fin 6) := fderiv_of_notMem_tsupport ℝ (hn j)
    have hv : HodgeMatrixEnergy.value f x = 0 := by ext j; exact hz j
    have hdv (i : Fin 4) : HodgeMatrixEnergy.derivative f i x = 0 := by
      ext j
      change coordinateDeriv i (f j) x = 0
      simp only [coordinateDeriv,SchwartzMap.lineDerivOp_apply_eq_fderiv,hd,zero_apply]
    change left _ (starThree _ _ (extDeriv (fun y => ∑ j, f j y • starFrame g J F b j y) x)) +
      right _ (starThree _ _ (extDeriv (fun y => ∑ j, f j y • frame g b j y) x)) = _
    rw [extDeriv_sum_zero hn, extDeriv_sum_zero hn]
    simp only [MetricHodge.starThree_zero, _root_.map_zero, add_zero,
      HodgeMatrixEnergy.system, hv, hdv, Finset.sum_const_zero]

end TamingCompatibility.HodgeGeometricCoefficients

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeWedgeEnergy
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
namespace TamingCompatibility
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricAdjoint _root_.MeasureTheory
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]

namespace GeometricHilbert
variable [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)

local instance instNormedAddCommGroupTangentSpaceRealSpaceModel_rec3fce_1 (x : X) : NormedAddCommGroup (TangentSpace Model x) :=
  inferInstanceAs (NormedAddCommGroup Space)
local instance instNormedSpaceRealTangentSpaceSpaceModel_rec3fce_1 (x : X) : NormedSpace ℝ (TangentSpace Model x) :=
  inferInstanceAs (NormedSpace ℝ Space)
local instance instFiniteDimensionalRealTangentSpaceSpaceModel_rec3fce_1 (x : X) : FiniteDimensional ℝ (TangentSpace Model x) :=
  inferInstanceAs (FiniteDimensional ℝ Space)
lemma preStar_square (a : PreL2 A J α hs ht true) :
    preStar A J α hs ht (preStar A J α hs ht a) = a :=
  Subtype.ext (starTwo_square J α ht a.val)

lemma l2Star_square (a : L2 A J α hs ht true) :
    l2Star A J α hs ht (l2Star A J α hs ht a) = a := by
  refine (smoothL2_dense A J α hs ht true).induction_on a
    (isClosed_eq ((l2Star A J α hs ht).continuous.comp (l2Star A J α hs ht).continuous) continuous_id) ?_
  intro b
  rw [l2Star_smooth,l2Star_smooth,preStar_square]

lemma l2Star_norm (a : L2 A J α hs ht true) : ‖l2Star A J α hs ht a‖ = ‖a‖ := by
  refine (smoothL2_dense A J α hs ht true).induction_on a
    (isClosed_eq (l2Star A J α hs ht).continuous.norm continuous_norm) ?_
  intro b
  rw [l2Star_smooth,(smoothL2 A J α hs ht true).norm_map,
    (preStar A J α hs ht).norm_map,(smoothL2 A J α hs ht true).norm_map]

lemma l2Star_inner (a b : L2 A J α hs ht true) :
    ⟪l2Star A J α hs ht a,l2Star A J α hs ht b⟫ = ⟪a,b⟫ := by
  let S : L2 A J α hs ht true →ₗᵢ[ℝ] L2 A J α hs ht true :=
    ⟨(l2Star A J α hs ht).toLinearMap,l2Star_norm A J α hs ht⟩
  exact S.inner_map_map a b

lemma l2Star_self_adjoint (a b : L2 A J α hs ht true) :
    ⟪l2Star A J α hs ht a,b⟫ = ⟪a,l2Star A J α hs ht b⟫ := by
  conv_lhs => rw [← l2Star_square A J α hs ht b]
  exact l2Star_inner A J α hs ht a (l2Star A J α hs ht b)
end GeometricHilbert
end TamingCompatibility

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeFrameTest
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
namespace TamingCompatibility.HodgeNormalOperator
open MetricModel MetricForms MetricHodge HodgeFrame EuclideanEnergy
open HodgeNormalSymbol (W Q)
lemma reconstruct_expansion (g : V → Metric V) (J : V → V →L[ℝ] V)
    (F : V → MetricForms.Form V 2) (b : Fin 4 → V → V) (q : V → W) (z : V)
    (hd : DifferentiableAt ℝ q z)
    (hψ : ∀ j, DifferentiableAt ℝ (HodgeGeometricCoefficients.frame g b j) z)
    (hφ : ∀ j, DifferentiableAt ℝ (HodgeGeometricCoefficients.starFrame g J F b j) z) :
    left (fun i => b i z) (starThree (g z) (F z)
      (extDeriv (fun y => starTwo (g y) (J y) (F y) (reconstruct (g y) (fun i => b i y) (q y))) z)) +
    right (fun i => b i z) (starThree (g z) (F z)
      (extDeriv (fun y => reconstruct (g y) (fun i => b i y) (q y)) z)) =
    (∑ i, rawPrincipal (g z) (F z) (fun k => b k z) (basisForm (g z) (fun k => b k z))
      (fun j => starTwo (g z) (J z) (F z) (basisForm (g z) (fun k => b k z) j)) i
        (fderiv ℝ q z (e i))) + HodgeGeometricCoefficients.lower g J F b z (q z) := by
  have h := operator_expansion (g z) (F z) (fun i => b i z)
    (HodgeGeometricCoefficients.frame g b) (HodgeGeometricCoefficients.starFrame g J F b)
    (fun j y => q y j) (fun j => (EuclideanSpace.proj (𝕜 := ℝ) j).differentiableAt.comp z hd) hψ hφ
  rw [star_reconstruct_function,reconstruct_function] at h
  simp only [vector_fderiv hd] at h
  have hv : WithLp.toLp 2 (fun j => q z j) = q z := by ext j; rfl
  rw [hv] at h
  exact h
end TamingCompatibility.HodgeNormalOperator

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
lemma starFrame_smooth (j : Fin 6) : ContDiffOn ℝ ∞
    (HodgeGeometricCoefficients.starFrame (coordinateMetric J α ht p) (coordinateJ J p)
      (ManifoldForms.pullback (invariantPart J α) (extChartAt Model p).symm) D.frame j) D.domain :=
  HodgeGeometricCoefficients.starFrame_smooth _ _ _ _ D.domain_open
    ((coordinateMetric_smooth J α hs ht p).mono D.domain_subset)
    ((coordinateJ_smooth J p).mono D.domain_subset)
    (fun _x hx => coordinateJ_square J p (D.domain_subset hx))
    (fun _x hx => coordinateMetric_hermitian J α ht p (D.domain_subset hx))
    ((smooth_chart _ (hs.invariantPart J) p).mono D.domain_subset) D.frame_smooth j

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

lemma firstOrder_zero_off (a : Fin 4 → 𝓢(Space,HodgeNormalSymbol.W →L[ℝ] HodgeNormalSymbol.Q))
    (b : 𝓢(Space,HodgeNormalSymbol.W →L[ℝ] HodgeNormalSymbol.Q)) (q : 𝓢(Space,HodgeNormalSymbol.W))
    {z : Space} (hz : z ∉ tsupport q) : firstOrder EuclideanEnergy.e a b q z = 0 := by
  have hd (i : Fin 4) : (∂_{EuclideanEnergy.e i} q : 𝓢(Space,HodgeNormalSymbol.W)) z = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hz (SchwartzMap.tsupport_lineDerivOp_subset _ _ h))
  simp only [firstOrder,_root_.add_apply,_root_.sum_apply,ContinuousLinearMap.comp_apply,
    multiply_apply,lineDerivOpCLM_apply,hd,image_eq_zero_of_notMem_tsupport hz,map_zero,
    Finset.sum_const_zero,add_zero]

end TamingCompatibility.HodgeChart

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

lemma hodgeGraph_weak (a : PreL2 A J α hs ht true) (b : PreL2 A J α hs ht false) :
    ⟪testDerivative A J α hs ht b,(hodgeGraph A J α hs ht a).fst⟫ =
      ⟪smoothL2 A J α hs ht false b,(hodgeGraph A J α hs ht a).snd.fst⟫ := by
  let db : PreL2 A J α hs ht true := ⟨exteriorDerivative b.val,b.property.exteriorDerivative⟩
  have h := GeometricAdjoint.formal_adjoint A J α hs ht b.property a.property
  have he : l2Pairing A J α ht db a = l2Pairing A J α ht b (hodgeDelta A J α hs ht a) := h
  exact ((smoothL2 A J α hs ht true).inner_map_map db a).trans
    ((preL2_inner A J α hs ht true db a).trans (he.trans
      (((smoothL2 A J α hs ht false).inner_map_map b (hodgeDelta A J α hs ht a)).trans
        (preL2_inner A J α hs ht false b (hodgeDelta A J α hs ht a))).symm))

lemma hodgeGraph_weak_star (a : PreL2 A J α hs ht true) (b : PreL2 A J α hs ht false) :
    ⟪l2Star A J α hs ht (testDerivative A J α hs ht b),(hodgeGraph A J α hs ht a).fst⟫ =
      ⟪smoothL2 A J α hs ht false b,(hodgeGraph A J α hs ht a).snd.snd⟫ := by
  rw [l2Star_self_adjoint]
  change ⟪testDerivative A J α hs ht b,l2Star A J α hs ht (smoothL2 A J α hs ht true a)⟫ = _
  rw [l2Star_smooth]
  exact hodgeGraph_weak A J α hs ht (preStar A J α hs ht a) b

lemma hodgeEnergy_weak (u : hodgeEnergy A J α hs ht) (b : PreL2 A J α hs ht false) :
    ⟪testDerivative A J α hs ht b,u.val.fst⟫ =
      ⟪smoothL2 A J α hs ht false b,u.val.snd.fst⟫ := by
  have hc : _root_.IsClosed {v : HodgeGraphSpace A J α hs ht |
      ⟪testDerivative A J α hs ht b,v.fst⟫ = ⟪smoothL2 A J α hs ht false b,v.snd.fst⟫} :=
    isClosed_eq (continuous_const.inner (WithLp.fstL 2 ℝ _ _).continuous)
      (continuous_const.inner ((WithLp.fstL 2 ℝ _ _).continuous.comp (WithLp.sndL 2 ℝ _ _).continuous))
  exact (closure_minimal (by rintro _ ⟨a,rfl⟩; exact hodgeGraph_weak A J α hs ht a b) hc) u.property

lemma hodgeEnergy_weak_star (u : hodgeEnergy A J α hs ht) (b : PreL2 A J α hs ht false) :
    ⟪l2Star A J α hs ht (testDerivative A J α hs ht b),u.val.fst⟫ =
      ⟪smoothL2 A J α hs ht false b,u.val.snd.snd⟫ := by
  have hc : _root_.IsClosed {v : HodgeGraphSpace A J α hs ht |
      ⟪l2Star A J α hs ht (testDerivative A J α hs ht b),v.fst⟫ = ⟪smoothL2 A J α hs ht false b,v.snd.snd⟫} :=
    isClosed_eq (continuous_const.inner (WithLp.fstL 2 ℝ _ _).continuous)
      (continuous_const.inner ((WithLp.sndL 2 ℝ _ _).continuous.comp (WithLp.sndL 2 ℝ _ _).continuous))
  exact (closure_minimal (by rintro _ ⟨a,rfl⟩; exact hodgeGraph_weak_star A J α hs ht a b) hc) u.property

lemma hodgeInclusion_injective : Function.Injective (hodgeInclusion A J α hs ht) := by
  suffices hz : ∀ u : hodgeEnergy A J α hs ht, hodgeInclusion A J α hs ht u = 0 → u = 0 by
    intro u v huv
    exact sub_eq_zero.mp (hz (u-v) (by rw [map_sub,sub_eq_zero.mpr huv]))
  intro u hu
  change u.val.fst = 0 at hu
  have hz (w : L2 A J α hs ht false)
      (hw : ∀ b : PreL2 A J α hs ht false, ⟪smoothL2 A J α hs ht false b,w⟫ = 0) : w = 0 := by
    have hall : ∀ v : L2 A J α hs ht false, ⟪v,w⟫ = 0 := fun v =>
      (smoothL2_dense A J α hs ht false).induction_on v
        (isClosed_eq (continuous_id.inner continuous_const) continuous_const) hw
    exact inner_self_eq_zero.mp (hall w)
  have h1 := hz u.val.snd.fst (fun b => by rw [← hodgeEnergy_weak A J α hs ht u b,hu,inner_zero_right])
  have h2 := hz u.val.snd.snd (fun b => by rw [← hodgeEnergy_weak_star A J α hs ht u b,hu,inner_zero_right])
  apply Subtype.ext
  apply (WithLp.linearEquiv 2 ℝ _).injective
  apply Prod.ext hu
  apply (WithLp.linearEquiv 2 ℝ _).injective
  exact Prod.ext h1 h2

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
open Set Filter _root_.MeasureTheory ComplexMatrix TemperedDistribution
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).toData.source)

omit [T2Space X] in
lemma hodge_smooth_pair (f v : PreL2 A J α hs ht true) :
    ⟪hodgeInclusion A J α hs ht (hodgeSmooth A J α hs ht f),
      hodgeInclusion A J α hs ht (hodgeSmooth A J α hs ht v)⟫ =
    ∫ x, GeometricAdjoint.pairing J α ht f.val v.val x ∂geometricVolume A J α := by
  change ⟪smoothL2 A J α hs ht true f,smoothL2 A J α hs ht true v⟫ = _
  rw [(smoothL2 A J α hs ht true).inner_map_map,preL2_inner]
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
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart Set ComplexMatrix
open scoped Manifold ContDiff SchwartzMap BoundedContinuousFunction
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)

def hodgeMultiply (ρ : X → ℝ) (hρ : ContMDiff Model 𝓘(ℝ,ℝ) ∞ ρ)
    (a : PreL2 A J α hs ht true) : PreL2 A J α hs ht true :=
  ⟨fun x => ρ x • a.val x,a.property.fun_smul hρ⟩

end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end


