-- Prove2me | Definitions.Def_OAIQ239Tc024
-- name    : OAIQ239Tc024
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T23:12:00.897281+00:00
-- url     : https://prove2.me/theorems/a387a7a6-3273-4d4a-9120-2e00e43ae6f7
-- title:
--   Definitions bundle OAIQ239Tc024 of the split of OpenAI, Taming implies compatibility on four-manifolds
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.TamingCompatibility.taming_implies_compatibility`, carved from OpenAI's openai/math development (OpenAI, *Taming implies compatibility on four-manifolds*, OpenAI Math Release, October 6, 2026, result family 342, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 23 declarations of OpenAI's Lean: 13 definitions and 10 theorems. The definitions and types are `OAI.TamingCompatibility.GeometricHilbert.hodgeCoexactPart`, `OAI.TamingCompatibility.GeometricHilbert.hodgeCorrectedSource`, `OAI.TamingCompatibility.GeometricHilbert.hodgeCorrectionSource`, `OAI.TamingCompatibility.GeometricHilbert.hodgeIsExact`, `OAI.TamingCompatibility.GeometricHilbert.hodgeWeakClosedL2`, `OAI.TamingCompatibility.GeometricHilbert.localizedRawSchwartz`, `OAI.TamingCompatibility.GeometricHilbert.rawRHSSeminormMap`, `OAI.TamingCompatibility.GeometricHilbert.scalarTestLM`, `OAI.TamingCompatibility.GeometricHilbert.testAnti`, `OAI.TamingCompatibility.GeometricHilbert.unitIntegral`, `OAI.TamingCompatibility.GeometricHilbert.weightedRawRHS`, `OAI.TamingCompatibility.HodgeChart.data`, `OAI.TamingCompatibility.chartDirectionFactor`.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: `TamingCompatibility_Charts_LocalDDStarEstimate`, `TamingCompatibility_DifferentialForms_InteriorEstimateApply`, `TamingCompatibility_DifferentialForms_RadialScalarOff`, `TamingCompatibility_Functional_WeakNormalEquation`, `TamingCompatibility_HeatFlow_HodgeClosedResolvent`, `TamingCompatibility_Hodge_HodgeAntiNorms`, `TamingCompatibility_Hodge_HodgeAntiRHSBound`, `TamingCompatibility_Hodge_HodgeClosedSmooth`, `TamingCompatibility_Hodge_HodgeCorrectionRegularization`, `TamingCompatibility_Hodge_HodgeGeometricGarding`, `TamingCompatibility_Hodge_HodgeHarmonicSmooth`, `TamingCompatibility_Hodge_HodgePairAllTests`, `TamingCompatibility_Hodge_HodgeScalarRaw`, `TamingCompatibility_Hodge_HodgeSmoothInverse`, `TamingCompatibility_Hodge_HodgeSmoothLimit`, `TamingCompatibility_Hodge_HodgeSmoothPatch`.
--
--   **Imports.** It imports the published bundle `Def_TamingCompatibility`; the bundles `OAIQ239Tc017`, `OAIQ239Tc018`, `OAIQ239Tc019` and `OAIQ239Tc020` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ239Tc027`; the statement `OAI.TamingCompatibility.GeometricHilbert.closedLift_scaled_basis_local_bound`; the proofs of `OAI.TamingCompatibility.GeometricHilbert.closedLift_scaled_basis_local_bound` and `OAI.TamingCompatibility.taming_implies_compatibility`.
-- source:
--   OpenAI, Taming implies compatibility on four-manifolds, OpenAI Math Release, October 6, 2026, https://github.com/openai/math (result family 342; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Taming-implies-compatibility-on-four-manifolds-October-6-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit 7ef5c0c

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc017
import Definitions.Def_OAIQ239Tc018
import Definitions.Def_OAIQ239Tc019
import Definitions.Def_OAIQ239Tc020

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Functional_WeakNormalEquation
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter _root_.MeasureTheory ComplexMatrix
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

def testAnti (p : A.centers) (q : 𝓢(Space,EuclideanEnergy.Pair))
    (hc : HasCompactSupport (q : Space → _)) (hqD : tsupport q ⊆ (D p).domain) :
    antiPre A J α hs ht :=
  ⟨⟨manifoldTest J α ht p.val (D p) q,manifoldTest_smooth J α hs ht p.val (D p) (q.smooth ⊤) hc hqD⟩,
    manifoldTest_anti J α ht p.val (D p) q⟩

end TamingCompatibility.GeometricHilbert

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_InteriorEstimateApply
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
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
open Set Filter _root_.MeasureTheory ComplexMatrix TemperedDistribution HilbertSobolev EuclideanSobolevOperators
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace LineDeriv
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

def localizedRawSchwartz (p : A.centers) (τ : 𝓢(Space,ℝ)) (χ : 𝓢(Space,ℂ))
    (a : antiPre A J α hs ht) : 𝓢(Space,C 2) :=
  SchwartzMap.smulLeftCLM (C 2) χ (SchwartzMap.postcompCLM (embed 2)
    (SchwartzMap.smulLeftCLM EuclideanEnergy.Pair τ (realPairSchwartz A J α ht D hD p a.val)))

end TamingCompatibility.GeometricHilbert

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_LocalDDStarEstimate
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume GeometricAdjoint
open Set Filter _root_.MeasureTheory ComplexMatrix TemperedDistribution HilbertSobolev EuclideanSobolevOperators
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

def weightedRawRHS (p : A.centers) (τ ρ : 𝓢(Space,ℝ))
    (f : antiPre A J α hs ht) : 𝓢(Space,EuclideanEnergy.Pair) :=
  (2:ℝ) • SchwartzMap.smulLeftCLM EuclideanEnergy.Pair ρ
    (SchwartzMap.smulLeftCLM EuclideanEnergy.Pair τ (realPairSchwartz A J α ht D hD p f.val))

end TamingCompatibility.GeometricHilbert

end

end OAI
end

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

def scalarTestLM (p : A.centers) (K : Set Space) (hK : IsCompact K)
    (hKD : K ⊆ (D p).domain) (j : Fin 2) :
    supportedSchwartz K →ₗ[ℝ] antiPre A J α hs ht where
  toFun f := testAnti A J α hs ht D p (componentTest j f.val)
    (componentTest_compact j f.val (supportedSchwartz_compact hK f))
    ((componentTest_support j f.val).trans (f.property.trans hKD))
  map_add' f g := by
    apply Subtype.ext
    apply Subtype.ext
    change manifoldTest J α ht p.val (D p) (componentTest j (f.val+g.val)) = _
    have he : (componentTest j (f.val+g.val) : Space → EuclideanEnergy.Pair) =
        componentTest j f.val + componentTest j g.val := by
      funext z
      simp only [componentTest_apply,add_apply,add_smul,Pi.add_apply]
    rw [he,manifoldTest_add]
    rfl
  map_smul' c f := by
    apply Subtype.ext
    apply Subtype.ext
    change manifoldTest J α ht p.val (D p) (componentTest j (c • f.val)) = _
    have he : (componentTest j (c • f.val) : Space → EuclideanEnergy.Pair) =
        c • (componentTest j f.val : Space → EuclideanEnergy.Pair) := by
      funext z
      simp only [componentTest_apply,smul_apply,Pi.smul_apply,smul_smul,smul_eq_mul]
    rw [he,manifoldTest_smul]
    rfl

end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeGeometricGarding
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Add _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Inner _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Module _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Normed _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.frameMap_apply _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDifferential_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap_zero _root_.OAI.TamingCompatibility.GeometricHilbert.antiMultiply_apply _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeInclusion_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeScaledDerivative_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.l2Star_smooth _root_.OAI.TamingCompatibility.HodgeNormalSymbol.symbolMap_apply _root_.OAI.TamingCompatibility.HodgeStarGeometry.starMap_apply _root_.OAI.TamingCompatibility.HodgeStarGeometry.swapMap_apply
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

theorem geometric_local_garding {x₀ : V} (hx₀ : x₀ ∈ U) :
    ∃ r K C : ℝ, 0 < r ∧ 0 < K ∧ 0 < C ∧ Metric.closedBall x₀ (2*r) ⊆ U ∧
      ∀ f : Field, (∀ j, tsupport (f j) ⊆ Metric.closedBall x₀ r) →
        (∫ x, HodgeMatrixEnergy.gradient f x) ≤ K * (∫ x, ‖operator g J F b f x‖^2) +
          C * (∫ x, ‖HodgeMatrixEnergy.value f x‖^2) := by
  let B := (basisOfFrame (g x₀) (by simp [V]) (fun i => b i x₀) (hgram x₀ hx₀)).toBasis.map
    (equiv (g x₀)).toLinearEquiv
  have hB (i : Fin 4) : B i = b i x₀ := by
    simp only [B,Module.Basis.map_apply,OrthonormalBasis.coe_toBasis,basisOfFrame_apply]
    rfl
  have hBe : (fun i => b i x₀) = B := (funext hB).symm
  let K := DirectionalEnergy.coordinateConstant B
  have hK : 0 < K := DirectionalEnergy.coordinateConstant_pos B
  have henergy (f : Field) : (∫ x, HodgeMatrixEnergy.gradient f x) ≤ K *
      (∫ x, ‖HodgeMatrixEnergy.constantSystem (principal b · x₀) f x‖^2) := by
    simpa only [principal,hBe] using HodgeFrozenEnergy.frozen_energy B f
  obtain ⟨r,C,hr,hC,hrU,he⟩ := HodgeMatrixEnergy.local_garding (principal b · x₀) hK henergy
    hU hx₀ (principal b) (lower g J F b) (fun i => (principal_smooth hb i).continuousOn)
    (lower_smooth g J F b hU hg hJ hJs hgJ hF hb).continuousOn (fun _ => rfl)
  refine ⟨r,4*K,8*K*C^2,hr,by positivity,by positivity,hrU,?_⟩
  intro f hf
  have hrU' : Metric.closedBall x₀ r ⊆ U :=
    (Metric.closedBall_subset_closedBall (by linarith)).trans hrU
  simpa only [operator_system g J F b hU hg hJ hJs hgJ hF hb hgram hcplx hfund f
    (fun j => (hf j).trans hrU')] using he f hf
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

theorem data_nonempty (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α)
    (ht : Tames α J) (p : X) : Nonempty (Data J α ht p) := by
  let D := GeometricChart.data J α hs ht p
  have hp : extChartAt Model p p ∈ D.domain := D.ball_subset
    (Metric.mem_closedBall_self (by linarith [D.radius_pos]))
  obtain ⟨r,K,C,hr,hK,hC,hrU,hgard⟩ := HodgeGeometricCoefficients.geometric_local_garding
    (coordinateMetric J α ht p) (coordinateJ J p)
    (ManifoldForms.pullback (invariantPart J α) (extChartAt Model p).symm) D.frame D.domain_open
    ((coordinateMetric_smooth J α hs ht p).mono D.domain_subset)
    ((coordinateJ_smooth J p).mono D.domain_subset)
    (fun x hx => coordinateJ_square J p (D.domain_subset hx))
    (fun x hx => coordinateMetric_hermitian J α ht p (D.domain_subset hx))
    ((smooth_chart _ (hs.invariantPart J) p).mono D.domain_subset) D.frame_smooth
    D.frame_gram D.frame_complex
    (fun x hx => ManifoldTop.coordinateFundamental J α ht p (D.domain_subset hx)) hp
  let D' : GeometricChart.Data J α ht p := { D with
    radius := min r D.radius
    radius_pos := lt_min hr D.radius_pos
    ball_subset := (Metric.closedBall_subset_closedBall
      (mul_le_mul_of_nonneg_left (min_le_left _ _) (by norm_num))).trans hrU
    garding := fun A B hA hB => D.garding A B
      (hA.trans (Metric.closedBall_subset_closedBall (min_le_right _ _)))
      (hB.trans (Metric.closedBall_subset_closedBall (min_le_right _ _))) }
  exact ⟨{ toData := D'
           fullEnergyConstant := K
           fullLowerConstant := C
           fullEnergy_pos := hK
           fullLower_pos := hC
           fullGarding := fun f hf => hgard f (fun j => (hf j).trans
             (Metric.closedBall_subset_closedBall (min_le_left _ _))) }⟩

def data (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α)
    (ht : Tames α J) (p : X) : Data J α ht p := Classical.choice (data_nonempty J α hs ht p)

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
omit [CompactSpace X] in
lemma scalar_eq_weight (p : A.centers) (a : TwoForm X) (j : Fin 6)
    {z : Space} (hz : z ∈ (D p).domain) :
    scalar A J α ht D p a j z = coordinateWeight A p z * rawVector J α ht p.val (D p) a z j := by
  unfold scalar localizedFunction
  rw [indicator_of_mem hz,indicator_of_mem ((D p).domain_subset hz)]
  rfl

end TamingCompatibility.HodgeChart

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeClosedSmooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)

def hodgeCoexactPart (a : PreL2 A J α hs ht true) : PreL2 A J α hs ht true :=
  preStar A J α hs ht (hodgePreD A J α hs ht
    (hodgeDelta A J α hs ht (preStar A J α hs ht a)))

end TamingCompatibility.GeometricHilbert

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
lemma rawVector_fun_smul (ρ : X → ℝ) (a : TwoForm X) (z : Space) :
    rawVector J α ht p D (fun x => ρ x • a x) z =
      ρ ((extChartAt Model p).symm z) • rawVector J α ht p D a z := by
  ext j
  rfl

end TamingCompatibility.HodgeChart

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
namespace TamingCompatibility.ManifoldForms
open scoped Manifold
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] {k : ℕ}
lemma chartLift_finset_sum {ι : Type*} (p : X) (s : Finset ι)
    (a : ι → Space → Space [⋀^Fin k]→L[ℝ] ℝ) :
    chartLift p (∑ i ∈ s, a i) = ∑ i ∈ s, chartLift p (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    funext x
    simp only [chartLift]
    split_ifs <;> rfl
  | @insert i s hi ih => rw [Finset.sum_insert hi,Finset.sum_insert hi,chartLift_add,ih]
end TamingCompatibility.ManifoldForms
namespace TamingCompatibility.HodgeChart
open ManifoldForms ManifoldHodge
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J) (p : X)
  (D : GeometricChart.Data J α ht p)
lemma manifoldTest_sum {ι : Type*} (s : Finset ι) (q : ι → Space → HodgeNormalSymbol.W) :
    manifoldTest J α ht p D (∑ i ∈ s, q i) = ∑ i ∈ s, manifoldTest J α ht p D (q i) := by
  classical
  have he : coordinateTest J α ht p D (∑ i ∈ s, q i) = ∑ i ∈ s, coordinateTest J α ht p D (q i) := by
    funext z
    simp only [coordinateTest,Finset.sum_apply,map_sum]
  unfold manifoldTest
  rw [he,chartLift_finset_sum]

end TamingCompatibility.HodgeChart
namespace TamingCompatibility.GeometricHilbert

open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart Set _root_.MeasureTheory
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
lemma hodge_smooth_multiply_pair (ρ : X → ℝ) (hρ : ContMDiff Model 𝓘(ℝ,ℝ) ∞ ρ)
    (a b : PreL2 A J α hs ht true) :
    ⟪smoothL2 A J α hs ht true b,smoothL2 A J α hs ht true (hodgeMultiply A J α hs ht ρ hρ a)⟫ =
    ⟪smoothL2 A J α hs ht true (hodgeMultiply A J α hs ht ρ hρ b),smoothL2 A J α hs ht true a⟫ := by
  rw [(smoothL2 A J α hs ht true).inner_map_map,(smoothL2 A J α hs ht true).inner_map_map,
    preL2_inner,preL2_inner]
  apply integral_congr_ae
  filter_upwards [] with x
  exact (MetricForms.pairing_smul_right _ _ _ _).trans (MetricForms.pairing_smul_left _ _ _ _).symm
omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma hodge_partition_sum {ι : Type*} [Fintype ι] (ρ : ι → X → ℝ)
    (hρ : ∀ i, ContMDiff Model 𝓘(ℝ,ℝ) ∞ (ρ i)) (h1 : ∀ x, ∑ i, ρ i x = 1)
    (a : PreL2 A J α hs ht true) : ∑ i, hodgeMultiply A J α hs ht (ρ i) (hρ i) a = a := by
  have he := map_sum (smoothForms X 2).subtype
    (fun i => hodgeMultiply A J α hs ht (ρ i) (hρ i) a) Finset.univ
  apply Subtype.ext
  refine he.trans ?_
  funext x
  rw [Finset.sum_apply]
  change (∑ i, ρ i x • a.val x) = a.val x
  rw [← Finset.sum_smul,h1,one_smul]
lemma hodge_energy_eq_of_pair_smooth (u v : hodgeEnergy A J α hs ht)
    (h : ∀ a : PreL2 A J α hs ht true,
      ⟪hodgeInclusion A J α hs ht u,smoothL2 A J α hs ht true a⟫ =
      ⟪hodgeInclusion A J α hs ht v,smoothL2 A J α hs ht true a⟫) : u = v := by
  have he : (fun z : hodgeEnergy A J α hs ht =>
      ⟪hodgeInclusion A J α hs ht u,hodgeInclusion A J α hs ht z⟫) =
      (fun z : hodgeEnergy A J α hs ht =>
      ⟪hodgeInclusion A J α hs ht v,hodgeInclusion A J α hs ht z⟫) :=
    (hodgeSmooth_dense A J α hs ht).equalizer
      (continuous_const.inner (hodgeInclusion A J α hs ht).continuous)
      (continuous_const.inner (hodgeInclusion A J α hs ht).continuous)
      (funext (fun a => by simpa only [Function.comp_apply,hodgeInclusion_smooth] using h a))
  apply hodgeInclusion_injective A J α hs ht
  apply sub_eq_zero.mp
  apply (inner_self_eq_zero (𝕜 := ℝ)).mp
  have hh := congrFun he (u-v)
  rw [map_sub] at hh
  rw [inner_sub_left,hh,sub_self]
lemma hodge_glue_weak_patches {ι : Type*} [Fintype ι] (ρ : ι → X → ℝ)
    (hρ : ∀ i, ContMDiff Model 𝓘(ℝ,ℝ) ∞ (ρ i)) (h1 : ∀ x, ∑ i, ρ i x = 1)
    (u : hodgeEnergy A J α hs ht) (w : ι → PreL2 A J α hs ht true)
    (hw : ∀ i a, ⟪hodgeInclusion A J α hs ht u,
        smoothL2 A J α hs ht true (hodgeMultiply A J α hs ht (ρ i) (hρ i) a)⟫ =
      ⟪smoothL2 A J α hs ht true (w i),
        smoothL2 A J α hs ht true (hodgeMultiply A J α hs ht (ρ i) (hρ i) a)⟫) :
    ∃ b : PreL2 A J α hs ht true, hodgeSmooth A J α hs ht b = u := by
  classical
  let b := ∑ i, hodgeMultiply A J α hs ht (ρ i) (hρ i) (w i)
  refine ⟨b,(hodge_energy_eq_of_pair_smooth A J α hs ht u (hodgeSmooth A J α hs ht b) ?_).symm⟩
  intro a
  have ha := congrArg (smoothL2 A J α hs ht true) (hodge_partition_sum A J α hs ht ρ hρ h1 a)
  rw [map_sum] at ha
  rw [hodgeInclusion_smooth]
  rw [← ha,inner_sum]
  conv_rhs => rw [show b = ∑ i, hodgeMultiply A J α hs ht (ρ i) (hρ i) (w i) from rfl,map_sum,sum_inner]
  apply Finset.sum_congr rfl
  intro i _
  rw [hw,hodge_smooth_multiply_pair,ha]
end TamingCompatibility.GeometricHilbert

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_HeatFlow_HodgeClosedResolvent
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

def hodgeIsExact (a : PreL2 A J α hs ht true) : Prop :=
  ∃ ξ : PreL2 A J α hs ht false, a = hodgePreD A J α hs ht ξ

end TamingCompatibility.GeometricHilbert

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

def hodgeWeakClosedL2 : Submodule ℝ (L2 A J α hs ht true) where
  carrier := {v | ∀ ξ : PreL2 A J α hs ht false, ⟪v,l2Star A J α hs ht (testDerivative A J α hs ht ξ)⟫ = 0}
  zero_mem' := by intro ξ; exact inner_zero_left _
  add_mem' hv hw := by intro ξ; rw [inner_add_left,hv ξ,hw ξ,add_zero]
  smul_mem' c _ hv := by intro ξ; rw [real_inner_smul_left,hv ξ,mul_zero]

end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeAntiRHSBound
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
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume GeometricAdjoint
open Set ComplexMatrix HilbertSobolev
open scoped Manifold ContDiff SchwartzMap
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

def rawRHSSeminormMap (p : A.centers) (τ ρ : 𝓢(Space,ℝ)) :
    antiPre A J α hs ht →ₗ[ℝ] H Space ScalarPair.F (3:ℝ) :=
  ((schwartzToH (3:ℝ)).restrictScalars ℝ).toLinearMap.comp
    ((SchwartzMap.postcompCLM (embed 2)).toLinearMap.comp
      ((2:ℝ) • (SchwartzMap.smulLeftCLM EuclideanEnergy.Pair ρ).toLinearMap.comp
        ((SchwartzMap.smulLeftCLM EuclideanEnergy.Pair τ).toLinearMap.comp
          ((SchwartzMap.postcompCLM (retract 2)).toLinearMap.comp
            ((pairLinear A J α ht D hD p).comp (antiPre A J α hs ht).subtype)))))

end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeAntiNorms
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
open ManifoldForms ManifoldVolume Bundle Set Filter
open scoped Manifold ContDiff Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]

def chartDirectionFactor (J : AlmostComplexStructure X) (p : X) (v : TangentBundle Model X) : ℝ :=
  ‖((trivializationAt Space (TangentSpace Model) p) v).2‖ *
    ‖((trivializationAt Space (TangentSpace Model) p)
      (⟨v.proj,J.endomorphism v.proj v.2⟩ : TangentBundle Model X)).2‖

end TamingCompatibility

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeSmoothInverse
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
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart GeometricHilbert
open Set _root_.MeasureTheory
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] unitMeasurable unitBorel

namespace GeometricHilbert
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)

def hodgeCorrectionSource
    (B : antiPre A J α hs ht →ₗ[ℝ] smoothForms X 2)
    (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))
    (μ : Measure (MetricUnit g)) [IsFiniteMeasure μ] : PreL2 A J α hs ht true →ₗ[ℝ] ℝ :=
  -((unitMeasureCurrent J g μ).comp (B.comp (smoothAntiProjection A J α hs ht)))

end GeometricHilbert
end TamingCompatibility

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeCorrectionRegularization
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
attribute [local instance] unitMeasurable unitBorel 

def hodgeCorrectedSource
    (B : antiPre A J α hs ht →ₗ[ℝ] smoothForms X 2)
    (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))
    (μ : Measure (MetricUnit g)) [IsFiniteMeasure μ] : PreL2 A J α hs ht true →ₗ[ℝ] ℝ :=
by
  let P : PreL2 A J α hs ht true →ₗ[ℝ] ℝ := unitMeasureCurrent J g μ
  exact P+hodgeCorrectionSource A J α hs ht B g μ

end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeSmoothLimit
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
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart Set _root_.MeasureTheory Filter
open scoped Manifold ContDiff RealInnerProductSpace Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)
attribute [local instance] unitMeasurable unitBorel 

def unitIntegral
    (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))
    (μ : Measure (MetricUnit g)) [IsFiniteMeasure μ] : C(MetricUnit g,ℝ) →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ u, f u ∂μ
      map_add' := fun f k => integral_add
        (f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
        (k.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      map_smul' := fun c f => integral_smul c f }
    (μ.real univ) (fun f => by
      change ‖∫ u, f u ∂μ‖ ≤ μ.real univ*‖f‖
      simpa only [mul_comm] using
        (norm_integral_le_of_norm_le_const (μ := μ) (Eventually.of_forall f.norm_coe_le_norm)))

end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end


