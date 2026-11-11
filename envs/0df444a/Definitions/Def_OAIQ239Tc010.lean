-- Prove2me | Definitions.Def_OAIQ239Tc010
-- name    : OAIQ239Tc010
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T22:18:42.284708+00:00
-- url     : https://prove2.me/theorems/dd7b5e3a-fe8a-4972-bb27-9b1d2b208e91
-- title:
--   Definitions bundle OAIQ239Tc010 of the split of OpenAI, Taming implies compatibility on four-manifolds
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.TamingCompatibility.taming_implies_compatibility`, carved from OpenAI's openai/math development (OpenAI, *Taming implies compatibility on four-manifolds*, OpenAI Math Release, October 6, 2026, result family 342, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 58 declarations of OpenAI's Lean: 5 definitions and 53 theorems. The definitions and types are `OAI.TamingCompatibility.ComplexMatrix.normalizedFullSquare_power_commutator_lift`, `OAI.TamingCompatibility.EuclideanSobolev.sobolevToBounded`, `OAI.TamingCompatibility.GeometricAdjoint.pointMetric`, `OAI.TamingCompatibility.HilbertSobolev.realSobolevLift`, `OAI.TamingCompatibility.MatrixEnergy.constantSystem`.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: `TamingCompatibility_DifferentialForms_ConstantGeometricEnergy`, `TamingCompatibility_DifferentialForms_FiberMap`, `TamingCompatibility_DifferentialForms_GreenNeg`, `TamingCompatibility_DifferentialForms_LinearUniform`, `TamingCompatibility_DifferentialForms_MetricCoords`, `TamingCompatibility_DifferentialForms_PerturbationNeg`, `TamingCompatibility_DifferentialForms_StarTwoComp`, `TamingCompatibility_DifferentialForms_UnitaryVectors`, `TamingCompatibility_DifferentialForms_Wedge`, `TamingCompatibility_Elliptic_CriticalH1Linear`, `TamingCompatibility_Elliptic_FrozenSystem`, `TamingCompatibility_Elliptic_InteriorRegularity`, `TamingCompatibility_Elliptic_MatrixH1Smooth`, `TamingCompatibility_Elliptic_PrincipalDerivativeError`, `TamingCompatibility_Elliptic_PrincipalTransport`, `TamingCompatibility_Elliptic_RealSobolevLift`, `TamingCompatibility_Elliptic_SecondDerivative`, `TamingCompatibility_Elliptic_SobolevBounded`, `TamingCompatibility_Hodge_HodgeCommutatorPowers`, `TamingCompatibility_Hodge_HodgeDifferentialLocality`, `TamingCompatibility_Hodge_HodgeLocalCoefficients`, `TamingCompatibility_Hodge_HodgeShiftedRegularity`.
--
--   **Imports.** It imports the published bundle `Def_TamingCompatibility`; the bundles `OAIQ239Tc005`, `OAIQ239Tc006` and `OAIQ239Tc007` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ239Tc014` and `OAIQ239Tc015`.
-- source:
--   OpenAI, Taming implies compatibility on four-manifolds, OpenAI Math Release, October 6, 2026, https://github.com/openai/math (result family 342; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Taming-implies-compatibility-on-four-manifolds-October-6-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit 7ef5c0c

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc005
import Definitions.Def_OAIQ239Tc006
import Definitions.Def_OAIQ239Tc007

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_MetricCoords
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
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

lemma IsSmooth.metricCoords {α : TwoForm X} (hα : IsSmooth α)
    (J : AlmostComplexStructure X) (x : X) :
    ContDiffOn ℝ ∞ (fun z => metricCoords J α x ((extChartAt Model x).symm z))
      (extChartAt Model x).target := by
  rw [contDiffOn_clm_apply]
  intro u
  rw [contDiffOn_clm_apply]
  intro v
  have ha := ManifoldForms.smooth_chart α hα x
  have hJ := SmoothAlmostComplex.contDiffOn_coord_chart
    (⟨J.endomorphism, J.square, J.smooth⟩ : SmoothAlmostComplex.AlmostComplexStructure X) x
  have hC : ContDiff ℝ ∞ (ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ)
      (E := Space) (F := ℝ) (n := 1)).toContinuousLinearMap := by
    exact ContinuousLinearMap.contDiff _
  have hc := hC.comp_contDiffOn ha
  have hcu := hc.clm_apply (contDiffOn_const (c := u))
  have hf := (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := Space)
    (F := ℝ) (0 : Fin 1)).symm.toContinuousLinearEquiv.contDiff.comp_contDiffOn hcu
  apply (hf.clm_apply (hJ.clm_apply (contDiffOn_const (c := v)))).congr
  intro z hz
  rw [metricCoords_chart_apply J α x hz]
  change (ManifoldForms.pullback α (extChartAt Model x).symm z) ![u, _] =
    (ManifoldForms.pullback α (extChartAt Model x).symm z) (Matrix.vecCons u (fun _ : Fin 1 => _))
  congr 1
  ext i
  fin_cases i <;> rfl

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
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_UnitaryVectors
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

namespace TamingCompatibility.SmoothHodge
open ContinuousAlternatingMap MetricForms MetricModel MetricHodge FormSmooth
open scoped ContDiff
variable {E D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup D] [NormedSpace ℝ D]

variable (g : D → Metric E) (J : D → E →L[ℝ] E)
  (hdim : Module.finrank ℝ E = 4) {U : Set D} (hU : IsOpen U)
  (hg : ContDiffOn ℝ ∞ (fun x => (g x).bilinear) U) (hJ : ContDiffOn ℝ ∞ J U)
  (hJs : ∀ x ∈ U, ∀ u, J x (J x u) = -u)
  (hgJ : ∀ x ∈ U, ∀ u v, (g x).bilinear (J x u) (J x v) = (g x).bilinear u v)
  {F : D → MetricForms.Form E 2} (hF : ContDiffOn ℝ ∞ F U)

include hdim hU hg hJ hJs hgJ hF
lemma starTwo_contDiffOn {α : D → MetricForms.Form E 2} (hα : ContDiffOn ℝ ∞ α U) :
    ContDiffOn ℝ ∞ (fun x => starTwo (g x) (J x) (F x) (α x)) U := by
  exact ((SmoothMetric.contDiffOn_pairing_two g J hdim hU hg hJ hJs hgJ hα hF).smul hF).sub
    (comp_contDiffOn hα hJ)

lemma starThree_contDiffOn {α : D → MetricForms.Form E 3} (hα : ContDiffOn ℝ ∞ α U) :
    ContDiffOn ℝ ∞ (fun x => starThree (g x) (F x) (α x)) U := by
  apply contDiffOn_of_basis (Module.finBasis ℝ E)
  intro a
  have he : (fun i => Module.finBasis ℝ E (a i)) = ![Module.finBasis ℝ E (a 0)] := by
    ext i; fin_cases i; rfl
  simp only [he,starThree_apply]
  exact (SmoothMetric.contDiffOn_pairing_three g J hdim hU hg hJ hJs hgJ hα
    (curryLeft_contDiffOn (volumeSquare_contDiffOn hF) contDiffOn_const)).neg

end TamingCompatibility.SmoothHodge

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_StarTwoComp
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
namespace TamingCompatibility.MetricHodge
open ContinuousAlternatingMap MetricForms MetricModel
variable {E D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup D] [NormedSpace ℝ D]
  [FiniteDimensional ℝ D]

lemma starTwo_comp (g : Metric E) (h : Metric D) (L : E ≃L[ℝ] D)
    (hL : ∀ u v, h.bilinear (L u) (L v) = g.bilinear u v)
    (hdim : Module.finrank ℝ E = 4) (J : E →L[ℝ] E) (K : D →L[ℝ] D)
    (hJ : ∀ u, L (J u) = K (L u)) (F α : MetricForms.Form D 2) :
    starTwo g J (F.compContinuousLinearMap L.toContinuousLinearMap) (α.compContinuousLinearMap L.toContinuousLinearMap) =
      (starTwo h K F α).compContinuousLinearMap L.toContinuousLinearMap := by
  unfold starTwo
  rw [pairing_two_comp g h L hL hdim]
  ext v
  change _ - α (fun i => L (J (v i))) = _ - α (fun i => K (L (v i)))
  simp only [hJ]
  rfl

end TamingCompatibility.MetricHodge

namespace TamingCompatibility.ManifoldHodge
open Bundle ContinuousAlternatingMap ManifoldVolume
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X]
  [IsManifold Model ∞ X]

attribute [local instance] OAI.TamingCompatibility.ManifoldHodge.instNormedAddCommGroupTangentSpaceRealSpaceModel
attribute [local instance] OAI.TamingCompatibility.ManifoldHodge.instNormedSpaceRealTangentSpaceSpaceModel
attribute [local instance] OAI.TamingCompatibility.ManifoldHodge.instFiniteDimensionalRealTangentSpaceSpaceModel
lemma pullback_starTwo (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
    (β : TwoForm X) (p : X) {z : Space} (hz : z ∈ (extChartAt Model p).target) :
    ManifoldForms.pullback (starTwo J α ht β) (extChartAt Model p).symm z =
      MetricHodge.starTwo (coordinateMetric J α ht p z) (coordinateJ J p z)
        (ManifoldForms.pullback (invariantPart J α) (extChartAt Model p).symm z)
        (ManifoldForms.pullback β (extChartAt Model p).symm z) := by
  have he := MetricHodge.starTwo_comp (coordinateMetric J α ht p z)
    (tangentMetric J α ht ((extChartAt Model p).symm z)) (inverseChartEquiv p z hz)
    (coordinateMetric_pullback J α ht p hz) (by simp [Space])
    (coordinateJ J p z) (J.endomorphism ((extChartAt Model p).symm z))
    (coordinateJ_intertwine J p hz) (invariantPart J α ((extChartAt Model p).symm z))
    (β ((extChartAt Model p).symm z))
  rw [inverseChartEquiv_coe] at he
  exact he.symm

lemma coordinateMetric_smooth (J : AlmostComplexStructure X) (α : TwoForm X)
    (hs : IsSmooth α) (ht : Tames α J) (p : X) :
    ContDiffOn ℝ ∞ (fun z => (coordinateMetric J α ht p z).bilinear) (extChartAt Model p).target := by
  apply ((hs.invariantPart J).metricCoords J p).congr
  intro z hz
  exact coordinateMetric_bilinear J α ht p hz

lemma starTwo_smooth (J : AlmostComplexStructure X) (α : TwoForm X)
    (hs : IsSmooth α) (ht : Tames α J) {β : TwoForm X} (hβ : IsSmooth β) :
    IsSmooth (starTwo J α ht β) := by
  apply ManifoldForms.smooth_of_charts
  intro p
  apply (SmoothHodge.starTwo_contDiffOn (coordinateMetric J α ht p) (coordinateJ J p)
    (by simp [Space]) (isOpen_extChartAt_target p) (coordinateMetric_smooth J α hs ht p)
    (coordinateJ_smooth J p) (fun z hz => coordinateJ_square J p hz)
    (fun z hz => coordinateMetric_hermitian J α ht p hz)
    (ManifoldForms.smooth_chart _ (hs.invariantPart J) p)
    (ManifoldForms.smooth_chart β hβ p)).congr
  intro z hz
  exact pullback_starTwo J α ht β p hz

lemma starThree_smooth (J : AlmostComplexStructure X) (α : TwoForm X)
    (hs : IsSmooth α) (ht : Tames α J) {β : ManifoldForms.Form X 3}
    (hβ : ManifoldForms.Smooth β) : ManifoldForms.Smooth (starThree J α ht β) := by
  apply ManifoldForms.smooth_of_charts
  intro p
  apply (SmoothHodge.starThree_contDiffOn (coordinateMetric J α ht p) (coordinateJ J p)
    (by simp [Space]) (isOpen_extChartAt_target p) (coordinateMetric_smooth J α hs ht p)
    (coordinateJ_smooth J p) (fun z hz => coordinateJ_square J p hz)
    (fun z hz => coordinateMetric_hermitian J α ht p hz)
    (ManifoldForms.smooth_chart _ (hs.invariantPart J) p)
    (ManifoldForms.smooth_chart β hβ p)).congr
  intro z hz
  exact pullback_starThree J α ht β p hz

end TamingCompatibility.ManifoldHodge

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_Wedge
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

namespace TamingCompatibility.GeometricAdjoint
open Bundle ContinuousAlternatingMap _root_.MeasureTheory ManifoldForms ManifoldHodge ManifoldTop ManifoldVolume
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]

def pointMetric (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J) (x : X) :
    MetricModel.Metric Space := tangentMetric J α ht x

end TamingCompatibility.GeometricAdjoint

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_ConstantGeometricEnergy
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
open _root_.MeasureTheory
open scoped SchwartzMap RealInnerProductSpace
namespace TamingCompatibility.MatrixEnergy
open EuclideanEnergy

def constantSystem (c : Fin 4 → Pair →L[ℝ] V) (A B : S) (x : V) : V :=
  ∑ i, c i (pair (coordinateDeriv i A x) (coordinateDeriv i B x))

end TamingCompatibility.MatrixEnergy

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_GreenNeg
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace TamingCompatibility.HilbertSobolev
open _root_.MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal LineDeriv Laplacian
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

lemma greenNegOne_distribution (u : H E F (-1)) :
    toDistribution E F 1 (greenNegOne u) = besselPotential E F (-2)
      (toDistribution E F (-1) u) := by
  have he : (-1:ℝ)-1 = -2 := by norm_num
  simpa only [greenNegOne, he] using toDistribution_reindex (-1) 1 u

lemma helmholtz_greenNegOne (u : H E F (-1)) :
    EuclideanGreen.helmholtz (toDistribution E F 1 (greenNegOne u)) =
      toDistribution E F (-1) u := by
  rw [greenNegOne_distribution]
  exact EuclideanGreen.helmholtz_green _

lemma weakValue_distribution (u : H E F (-1)) :
    toDistribution E F 0 (weakValue u) = toDistribution E F 1 (greenNegOne u) := by
  exact toDistribution_inclusion (show (0:ℝ) ≤ 1 by norm_num) (greenNegOne u)

lemma weakGradient_distribution (v : E) (u : H E F (-1)) :
    toDistribution E F 0 (weakGradient v u) =
      ∂_{v} (toDistribution E F 1 (greenNegOne u)) := by
  change toDistribution E F 0 (derivative 1 v (greenNegOne u)) = _
  simpa only [toDistribution, sub_self] using
    toDistribution_derivative 1 v (greenNegOne u)

lemma product_zero_distribution (g : 𝓢(E,ℂ)) (u : H E F 0) :
    toDistribution E F 0 (product 0 g u) = smulLeftCLM F g (toDistribution E F 0 u) := by
  simpa only [toDistribution, Nat.cast_zero] using toDistribution_product 0 g u

lemma derivative_zero_distribution (v : E) (u : H E F 0) :
    toDistribution E F (-1) (derivative 0 v u) = ∂_{v} (toDistribution E F 0 u) := by
  simpa only [toDistribution, zero_sub] using toDistribution_derivative 0 v u

lemma negativeProductMain_distribution (g : 𝓢(E,ℂ)) (u : H E F (-1)) :
    toDistribution E F (-1) (negativeProductMain g u) =
      smulLeftCLM F g (toDistribution E F 1 (greenNegOne u)) := by
  simp only [negativeProductMain, ContinuousLinearMap.comp_apply,
    toDistribution_inclusion, product_zero_distribution, weakValue_distribution]

lemma negativeProductTerm_distribution (g : 𝓢(E,ℂ)) (v : E) (u : H E F (-1)) :
    toDistribution E F (-1) (negativeProductTerm g v u) =
      smulLeftCLM F g (∂_{v} (∂_{v} (toDistribution E F 1 (greenNegOne u)))) := by
  simp only [negativeProductTerm, sub_apply, ContinuousLinearMap.comp_apply,
    map_sub, toDistribution_inclusion, derivative_zero_distribution,
    product_zero_distribution, weakGradient_distribution,
    EuclideanSobolevOperators.distribution_derivative_product,
    add_sub_cancel_left]

lemma toDistribution_productNegOne (g : 𝓢(E,ℂ)) (u : H E F (-1)) :
    toDistribution E F (-1) (productNegOne g u) =
      smulLeftCLM F g (toDistribution E F (-1) u) := by
  simp only [productNegOne, sub_apply, smul_apply, sum_apply, map_sub,
    ContinuousLinearMap.map_smul_of_tower, map_sum,
    negativeProductMain_distribution, negativeProductTerm_distribution]
  rw [← map_sum, ← ContinuousLinearMap.map_smul_of_tower, ← map_sub,
    ← TemperedDistribution.laplacian_eq_sum (stdOrthonormalBasis ℝ E)]
  exact congrArg (smulLeftCLM F g) (helmholtz_greenNegOne u)

end TamingCompatibility.HilbertSobolev

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Elliptic_SecondDerivative
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace TamingCompatibility.HilbertSobolev
open _root_.MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal LineDeriv
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

lemma toDistribution_secondDerivative (s : ℝ) (v w : E) (u : H E F (s+2)) :
    toDistribution E F s (secondDerivative s v w u) =
      ∂_{v} (∂_{w} (toDistribution E F (s+2) u)) := by
  have h1 := toDistribution_derivative (s+1) v (derivative (s+2) w u)
  have e1 : s+1-1=s := by ring
  rw [e1] at h1
  have h2 := toDistribution_derivative (s+2) w u
  have e2 : s+2-1=s+1 := by ring
  rw [e2] at h2
  exact h1.trans (congrArg (fun t : 𝓢'(E,F) => ∂_{v} t) h2)

lemma toDistribution_perturbation (n : ℕ)
    (a : basisIndex E → basisIndex E → 𝓢(E,ℂ)) (u : H E F ((n:ℝ)+2)) :
    toDistribution E F n (perturbation n a u) =
      differentialPerturbation a (toDistribution E F ((n:ℝ)+2) u) := by
  simp only [perturbation, differentialPerturbation, sum_apply,
    ContinuousLinearMap.comp_apply, map_sum, toDistribution_product,
    toDistribution_secondDerivative]

lemma helmholtz_toDistribution (s : ℝ) (u : H E F (s+2)) :
    EuclideanGreen.helmholtz (toDistribution E F (s+2) u) = toDistribution E F s u := by
  have h := toDistribution_reindex (s+2) s u
  have he : s+2-s=2 := by ring
  rw [he, EuclideanGreen.bessel_two_eq_helmholtz] at h
  exact h.symm

lemma perturbedHelmholtz_toDistribution (n : ℕ)
    (a : basisIndex E → basisIndex E → 𝓢(E,ℂ)) (u : H E F ((n:ℝ)+2)) :
    perturbedHelmholtz a (toDistribution E F ((n:ℝ)+2) u) =
      toDistribution E F n (u + perturbation n a u) := by
  rw [perturbedHelmholtz, helmholtz_toDistribution, map_add, toDistribution_perturbation]

theorem perturbedHelmholtz_solve (n : ℕ)
    (a : basisIndex E → basisIndex E → 𝓢(E,ℂ))
    (ha : ‖perturbation (F := F) n a‖ < 1) {f : 𝓢'(E,F)}
    (hf : MemSobolev n 2 f) :
    ∃! u : 𝓢'(E,F), MemSobolev ((n:ℝ)+2) 2 u ∧ perturbedHelmholtz a u = f := by
  have hf' : f ∈ Set.range (toDistribution E F n) := by
    rw [range_toDistribution]
    exact hf
  obtain ⟨v, hv⟩ := hf'
  obtain ⟨w, hw, hu⟩ := Neumann.existsUnique (perturbation (F := F) n a) ha v
  refine ⟨toDistribution E F ((n:ℝ)+2) w,
    ⟨toDistribution_memSobolev _ _, ?_⟩, ?_⟩
  · rw [perturbedHelmholtz_toDistribution, hw, hv]
  · intro z hz
    have hz' : z ∈ Set.range (toDistribution E F ((n:ℝ)+2)) := by
      rw [range_toDistribution]
      exact hz.1
    obtain ⟨q, hq⟩ := hz'
    have he : q + perturbation n a q = v := by
      apply toDistribution_injective (n:ℝ)
      rw [← perturbedHelmholtz_toDistribution, hq, hz.2, hv]
    rw [← hq, hu q he]

end TamingCompatibility.HilbertSobolev

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_PerturbationNeg
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace TamingCompatibility.HilbertSobolev
open _root_.MeasureTheory TemperedDistribution EuclideanSobolevOperators
open scoped SchwartzMap ENNReal LineDeriv Laplacian
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

lemma toDistribution_perturbationNegOne
    (a : basisIndex E → basisIndex E → 𝓢(E,ℂ)) (u : H E F 1) :
    toDistribution E F (-1) (perturbationNegOne a u) =
      differentialPerturbation a (toDistribution E F 1 u) := by
  have hs (i j : basisIndex E) :
      toDistribution E F (-1) (secondDerivative (-1)
        (stdOrthonormalBasis ℝ E i) (stdOrthonormalBasis ℝ E j) u) =
      ∂_{stdOrthonormalBasis ℝ E i} (∂_{stdOrthonormalBasis ℝ E j}
        (toDistribution E F 1 u)) := by
    have h := toDistribution_secondDerivative (-1)
      (stdOrthonormalBasis ℝ E i) (stdOrthonormalBasis ℝ E j) u
    have he : (-1:ℝ)+2 = 1 := by norm_num
    simpa only [toDistribution, he] using h
  simp only [perturbationNegOne, differentialPerturbation, sum_apply,
    ContinuousLinearMap.comp_apply, map_sum, toDistribution_productNegOne, hs]

lemma perturbedHelmholtz_negOne_toDistribution
    (a : basisIndex E → basisIndex E → 𝓢(E,ℂ)) (u : H E F 1) :
    perturbedHelmholtz a (toDistribution E F 1 u) =
      toDistribution E F (-1) (u + perturbationNegOne a u) := by
  have hh : EuclideanGreen.helmholtz (toDistribution E F 1 u) =
      toDistribution E F (-1) u := by
    have h := helmholtz_toDistribution (-1) u
    have he : (-1:ℝ)+2=1 := by norm_num
    simpa only [toDistribution, he] using h
  rw [perturbedHelmholtz, hh, map_add, toDistribution_perturbationNegOne]

theorem perturbedHelmholtz_solve_negOne
    (a : basisIndex E → basisIndex E → 𝓢(E,ℂ))
    (ha : ‖perturbationNegOne (F := F) a‖ < 1) {f : 𝓢'(E,F)}
    (hf : MemSobolev (-1) 2 f) :
    ∃! u : 𝓢'(E,F), MemSobolev 1 2 u ∧ perturbedHelmholtz a u = f := by
  have hf' : f ∈ Set.range (toDistribution E F (-1)) := by
    rw [range_toDistribution]
    exact hf
  obtain ⟨v, hv⟩ := hf'
  obtain ⟨w, hw, hu⟩ := Neumann.existsUnique (perturbationNegOne (F := F) a) ha v
  refine ⟨toDistribution E F 1 w, ⟨toDistribution_memSobolev _ _, ?_⟩, ?_⟩
  · rw [perturbedHelmholtz_negOne_toDistribution, hw, hv]
  · intro z hz
    have hz' : z ∈ Set.range (toDistribution E F 1) := by
      rw [range_toDistribution]
      exact hz.1
    obtain ⟨q, hq⟩ := hz'
    have he : q + perturbationNegOne a q = v := by
      apply toDistribution_injective (-1)
      rw [← perturbedHelmholtz_negOne_toDistribution, hq, hz.2, hv]
    rw [← hq, hu q he]

theorem weak_H1_regular
    (a : basisIndex E → basisIndex E → 𝓢(E,ℂ))
    (hweak : ‖perturbationNegOne (F := F) a‖ < 1)
    (hstrong : ‖perturbation (F := F) 0 a‖ < 1) {u : 𝓢'(E,F)}
    (hu : MemSobolev 1 2 u) (hf : MemSobolev 0 2 (perturbedHelmholtz a u)) :
    MemSobolev 2 2 u := by
  have hf' : MemSobolev (0:ℕ) 2 (perturbedHelmholtz a u) := by
    simpa only [Nat.cast_zero] using hf
  obtain ⟨v, hv, _⟩ := perturbedHelmholtz_solve 0 a hstrong hf'
  have hv2 : MemSobolev 2 2 v := by simpa only [Nat.cast_zero, zero_add] using hv.1
  obtain ⟨w, _, hw⟩ := perturbedHelmholtz_solve_negOne a hweak
    (hf.mono (show (-1:ℝ) ≤ 0 by norm_num))
  have hu_eq : u = w := hw u ⟨hu, rfl⟩
  have hv_eq : v = w := hw v ⟨hv2.mono (by norm_num), hv.2⟩
  rwa [hu_eq, ← hv_eq]

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in
lemma perturbedHelmholtz_cutoff
    (a : basisIndex E → basisIndex E → 𝓢(E,ℂ)) (g : 𝓢(E,ℂ)) (u : 𝓢'(E,F)) :
    perturbedHelmholtz a (smulLeftCLM F g u) =
      smulLeftCLM F g (perturbedHelmholtz a u) + localizationError a g u := by
  simp only [perturbedHelmholtz, helmholtz_cutoff, differentialPerturbation,
    distribution_second_product, map_add, map_sum, Finset.sum_add_distrib,
    coefficient_products_commute (g := g), localizationError, neg_smul]
  abel

lemma localizationError_memSobolev (n : ℕ)
    (a : basisIndex E → basisIndex E → 𝓢(E,ℂ)) (g : 𝓢(E,ℂ))
    {u : 𝓢'(E,F)} (hu : MemSobolev ((n:ℝ)+1) 2 u) :
    MemSobolev n 2 (localizationError a g u) := by
  apply MemSobolev.add
  · exact (memSobolev_sum _ _ (fun _i _ => secondCommutator_memSobolev n g _ _ hu)).smul _
  · exact memSobolev_sum _ _ (fun i _ => memSobolev_sum _ _
      (fun j _ => memSobolev_nat_product n (a i j) (secondCommutator_memSobolev n g _ _ hu)))

theorem cutoff_H1_regular
    (a : basisIndex E → basisIndex E → 𝓢(E,ℂ))
    (hweak : ‖perturbationNegOne (F := F) a‖ < 1)
    (hstrong : ‖perturbation (F := F) 0 a‖ < 1) (g : 𝓢(E,ℂ))
    {u : 𝓢'(E,F)} (hu : MemSobolev 1 2 u)
    (hf : MemSobolev 0 2 (smulLeftCLM F g (perturbedHelmholtz a u))) :
    MemSobolev 2 2 (smulLeftCLM F g u) := by
  apply weak_H1_regular a hweak hstrong
  · have hu1 : MemSobolev (1:ℕ) 2 u := by simpa only [Nat.cast_one] using hu
    simpa only [Nat.cast_one] using memSobolev_nat_product (E := E) (F := F) 1 g hu1
  · rw [perturbedHelmholtz_cutoff]
    apply hf.add
    have hu' : MemSobolev ((0:ℕ)+1:ℝ) 2 u := by simpa using hu
    simpa only [Nat.cast_zero] using localizationError_memSobolev 0 a g hu'

end TamingCompatibility.HilbertSobolev

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_FiberMap
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace TamingCompatibility.HilbertSobolev
open _root_.MeasureTheory TemperedDistribution EuclideanSobolevOperators
open scoped SchwartzMap ENNReal LineDeriv

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem matrix_cutoff_H1_regular {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a : basisIndex E → basisIndex E → 𝓢(E,ℂ))
    (hweak : ‖perturbationNegOne (F := F) a‖ < 1)
    (hstrong : ‖perturbation (F := F) 0 a‖ < 1)
    (b : ι → 𝓢(E,ℂ)) (L : ι → F →L[ℂ] F) (v : ι → E)
    (c : κ → 𝓢(E,ℂ)) (K : κ → F →L[ℂ] F) (g : 𝓢(E,ℂ))
    {u : 𝓢'(E,F)} (hu : MemSobolev 1 2 u)
    (hf : MemSobolev 0 2 (smulLeftCLM F g
      (perturbedHelmholtz a u + matrixLowerOrder b L v c K u))) :
    MemSobolev 2 2 (smulLeftCLM F g u) := by
  apply cutoff_H1_regular a hweak hstrong g hu
  have hu' : MemSobolev ((0:ℕ)+1:ℝ) 2 u := by simpa using hu
  have hl : MemSobolev (0:ℕ) 2 (matrixLowerOrder b L v c K u) :=
    matrixLowerOrder_memSobolev 0 b L v c K hu'
  have hg : MemSobolev 0 2 (smulLeftCLM F g (matrixLowerOrder b L v c K u)) := by
    simpa only [Nat.cast_zero] using memSobolev_nat_product (E := E) (F := F) 0 g hl
  rw [map_add] at hf
  simpa only [add_sub_cancel_right] using hf.sub hg

end TamingCompatibility.HilbertSobolev

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Elliptic_PrincipalDerivativeError
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
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
namespace TamingCompatibility.HilbertSobolev
open _root_.MeasureTheory TemperedDistribution EuclideanSobolevOperators
open scoped SchwartzMap ENNReal LineDeriv Laplacian FourierTransform
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [CompleteSpace F] in
lemma perturbedHelmholtz_derivative
    (a : basisIndex E → basisIndex E → 𝓢(E,ℂ)) (v : E) (u : 𝓢'(E,F)) :
    ∂_{v} (perturbedHelmholtz a u) =
      perturbedHelmholtz a (∂_{v} u) + principalDerivativeError a v u := by
  simp only [perturbedHelmholtz, differentialPerturbation,
    LineDeriv.lineDerivOp_add, LineDeriv.lineDerivOp_sum,
    distribution_derivative_product, Finset.sum_add_distrib,
    principalDerivativeError, ← helmholtz_derivative]
  have hc (i j : basisIndex E) :
      ∂_{v} (∂_{stdOrthonormalBasis ℝ E i} (∂_{stdOrthonormalBasis ℝ E j} u)) =
      ∂_{stdOrthonormalBasis ℝ E i} (∂_{stdOrthonormalBasis ℝ E j} (∂_{v} u)) := by
    rw [distribution_derivatives_commute v, distribution_derivatives_commute v]
  simp only [hc]
  abel

theorem principal_H1_bootstrap (n : ℕ)
    (a : basisIndex E → basisIndex E → 𝓢(E,ℂ))
    (hweak : ‖perturbationNegOne (F := F) a‖ < 1)
    (hstrong : ‖perturbation (F := F) 0 a‖ < 1) {u : 𝓢'(E,F)}
    (hu : MemSobolev 1 2 u)
    (hf : MemSobolev n 2 (perturbedHelmholtz a u)) :
    MemSobolev ((n:ℝ)+2) 2 u := by
  induction n generalizing u with
  | zero =>
    simp only [Nat.cast_zero, zero_add] at hf ⊢
    exact weak_H1_regular a hweak hstrong hu hf
  | succ n ih =>
    have hf' : MemSobolev n 2 (perturbedHelmholtz a u) :=
      hf.mono (by exact_mod_cast Nat.le_succ n)
    have hu2 := ih hu hf'
    have hd (i : basisIndex E) :
        MemSobolev ((n:ℝ)+2) 2 (∂_{stdOrthonormalBasis ℝ E i} u) := by
      have hd1 : MemSobolev 1 2 (∂_{stdOrthonormalBasis ℝ E i} u) :=
        hu2.lineDerivOp.mono (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
      have hdf : MemSobolev n 2 (∂_{stdOrthonormalBasis ℝ E i}
          (perturbedHelmholtz a u)) := by
        convert hf.lineDerivOp using 1
        all_goals try with_reducible_and_instances rfl
        simp
      have he := principalDerivativeError_memSobolev n a
        (stdOrthonormalBasis ℝ E i) hu2
      have hr := hdf.sub he
      rw [perturbedHelmholtz_derivative, add_sub_cancel_right] at hr
      exact ih hd1 hr
    have h := memSobolev_succ_of_derivatives (stdOrthonormalBasis ℝ E) hu2 hd
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    push_cast
    ring

end TamingCompatibility.HilbertSobolev

end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Elliptic_MatrixH1Smooth
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace TamingCompatibility.HilbertSobolev
open _root_.MeasureTheory TemperedDistribution EuclideanSobolevOperators Filter
open scoped SchwartzMap LineDeriv Topology
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in
lemma localizationError_cutoff_zero
    (a : basisIndex E → basisIndex E → 𝓢(E,ℂ)) (g h : 𝓢(E,ℂ))
    (hh : ∀ x ∈ tsupport g, h =ᶠ[𝓝 x] fun _ => 1) (u : 𝓢'(E,F)) :
    smulLeftCLM F g (localizationError a h u) = 0 := by
  simp only [localizationError, map_add, ContinuousLinearMap.map_smul_of_tower,
    map_sum, coefficient_products_commute g, cutoff_secondCommutator_zero g h hh,
    map_zero, Finset.sum_const_zero, smul_zero, add_zero]

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in
lemma perturbedHelmholtz_locality
    (a : basisIndex E → basisIndex E → 𝓢(E,ℂ)) (g h : 𝓢(E,ℂ))
    (hh : ∀ x ∈ tsupport g, h =ᶠ[𝓝 x] fun _ => 1) (u : 𝓢'(E,F)) :
    smulLeftCLM F g (perturbedHelmholtz a (smulLeftCLM F h u)) =
      smulLeftCLM F g (perturbedHelmholtz a u) := by
  rw [perturbedHelmholtz_cutoff, map_add, cutoff_mul_cutoff g h hh,
    localizationError_cutoff_zero a g h hh, add_zero]

theorem matrix_cutoff_succ_regular {ι κ : Type*} [Fintype ι] [Fintype κ]
    (n : ℕ) (a : basisIndex E → basisIndex E → 𝓢(E,ℂ))
    (hweak : ‖perturbationNegOne (F := F) a‖ < 1)
    (hstrong : ‖perturbation (F := F) 0 a‖ < 1)
    (b : ι → 𝓢(E,ℂ)) (L : ι → F →L[ℂ] F) (v : ι → E)
    (c : κ → 𝓢(E,ℂ)) (K : κ → F →L[ℂ] F) (g : 𝓢(E,ℂ))
    {u : 𝓢'(E,F)} (hu : MemSobolev ((n:ℝ)+1) 2 u)
    (hf : MemSobolev n 2 (smulLeftCLM F g
      (perturbedHelmholtz a u + matrixLowerOrder b L v c K u))) :
    MemSobolev ((n:ℝ)+2) 2 (smulLeftCLM F g u) := by
  apply principal_H1_bootstrap n a hweak hstrong
  · have h1 : MemSobolev (1:ℕ) 2 u := hu.mono (by have := Nat.cast_nonneg (α := ℝ) n; simpa only [Nat.cast_one] using le_add_of_nonneg_left this)
    simpa only [Nat.cast_one] using memSobolev_nat_product 1 g h1
  · rw [perturbedHelmholtz_cutoff]
    have hl := memSobolev_nat_product n g (matrixLowerOrder_memSobolev n b L v c K hu)
    rw [map_add] at hf
    have hp := hf.sub hl
    rw [add_sub_cancel_right] at hp
    exact hp.add (localizationError_memSobolev n a g hu)

end TamingCompatibility.HilbertSobolev

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Elliptic_InteriorRegularity
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
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
open _root_.MeasureTheory TemperedDistribution EuclideanSobolevOperators Filter Set
open scoped SchwartzMap LineDeriv Topology Manifold ContDiff BoundedContinuousFunction
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem matrix_H1_interior_bootstrap {ι κ : Type*} [Fintype ι] [Fintype κ]
    (n : ℕ) {U : Set E} (hU : IsOpen U)
    (a : basisIndex E → basisIndex E → 𝓢(E,ℂ))
    (hweak : ‖perturbationNegOne (F := F) a‖ < 1)
    (hstrong : ‖perturbation (F := F) 0 a‖ < 1)
    (b : ι → 𝓢(E,ℂ)) (L : ι → F →L[ℂ] F) (v : ι → E)
    (c : κ → 𝓢(E,ℂ)) (K : κ → F →L[ℂ] F) {u : 𝓢'(E,F)}
    (hu : MemSobolevLoc U 1 u)
    (hf : MemSobolevLoc U n (perturbedHelmholtz a u + matrixLowerOrder b L v c K u)) :
    MemSobolevLoc U ((n:ℝ)+2) u := by
  induction n with
  | zero =>
    intro g hg hgU
    obtain ⟨h,hh,hhU,hhg⟩ := exists_outer_cutoff hU g hg hgU
    have hloc := hf g hg hgU
    have he : smulLeftCLM F g (perturbedHelmholtz a (smulLeftCLM F h u) +
        matrixLowerOrder b L v c K (smulLeftCLM F h u)) =
        smulLeftCLM F g (perturbedHelmholtz a u + matrixLowerOrder b L v c K u) := by
      rw [map_add, perturbedHelmholtz_locality a g h hhg,
        matrixLowerOrder_locality b L v c K g h hhg, ← map_add]
    have hr := matrix_cutoff_H1_regular a hweak hstrong b L v c K g
      (hu h hh hhU) (by simpa only [he, Nat.cast_zero] using hloc)
    simpa only [cutoff_mul_cutoff g h hhg, Nat.cast_zero, zero_add] using hr
  | succ n ih =>
    have hun := ih (hf.mono (by exact_mod_cast Nat.le_succ n))
    intro g hg hgU
    obtain ⟨h,hh,hhU,hhg⟩ := exists_outer_cutoff hU g hg hgU
    have hhu : MemSobolev ((n+1:ℕ)+1:ℝ) 2 (smulLeftCLM F h u) := by
      convert hun h hh hhU using 1
      all_goals try with_reducible_and_instances rfl
      push_cast
      ring
    have he : smulLeftCLM F g (perturbedHelmholtz a (smulLeftCLM F h u) +
        matrixLowerOrder b L v c K (smulLeftCLM F h u)) =
        smulLeftCLM F g (perturbedHelmholtz a u + matrixLowerOrder b L v c K u) := by
      rw [map_add, perturbedHelmholtz_locality a g h hhg,
        matrixLowerOrder_locality b L v c K g h hhg, ← map_add]
    have hr := matrix_cutoff_succ_regular (n+1) a hweak hstrong b L v c K g
      hhu (he ▸ hf g hg hgU)
    simpa only [cutoff_mul_cutoff g h hhg] using hr

end TamingCompatibility.HilbertSobolev

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Elliptic_PrincipalTransport
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
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
open EuclideanSobolevOperators TemperedDistribution _root_.MeasureTheory LineDeriv
open scoped SchwartzMap LineDeriv RealInnerProductSpace Laplacian
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in

lemma local_frozen_helmholtz (χ : 𝓢(E,ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (g : basisIndex E → basisIndex E → 𝓢(E,ℂ)) (p : E)
    (hgp : ∀ i j, g i j p = if i=j then ((((2*Real.pi)^2)⁻¹ : ℝ) : ℂ) else 0)
    (r : ℝ) (hr : r ≠ 0) (ψ : 𝓢(E,ℂ)) (hψ : ∀ x ∈ tsupport ψ, χ x = 1)
    (u : 𝓢'(E,F)) :
    smulLeftCLM F ψ (perturbedHelmholtz
      (frozenPrincipal χ hχ (fun i j x => -g i j x) (fun i j => (g i j).smooth ⊤ |>.neg) p r) u) =
      smulLeftCLM F ψ u - smulLeftCLM F ψ
        (directionalPrincipal (stdOrthonormalBasis ℝ E) (fun i j => affineSchwartz p r hr (g i j)) u) := by
  simp only [perturbedHelmholtz,differentialPerturbation,EuclideanGreen.helmholtz,
    map_add,map_sub,map_sum,frozenPrincipal]
  simp only [local_frozen_product χ hχ (g _ _) p r hr _ (hgp _ _) ψ hψ,
    Finset.sum_add_distrib,Finset.sum_neg_distrib]
  have hd : (∑ i, ∑ j, (if i=j then ((((2*Real.pi)^2)⁻¹ : ℝ) : ℂ) else 0) •
      smulLeftCLM F ψ (∂_{stdOrthonormalBasis ℝ E i} (∂_{stdOrthonormalBasis ℝ E j} u))) =
      smulLeftCLM F ψ (((2*Real.pi)^2)⁻¹ • Δ u) := by
    simp only [ite_smul,zero_smul,Finset.sum_ite_eq,Finset.mem_univ,ite_true, if_true,
      laplacian_eq_sum (stdOrthonormalBasis ℝ E),ContinuousLinearMap.map_smul_of_tower,map_sum,
      Finset.smul_sum,RCLike.real_smul_eq_coe_smul (K := ℂ),RCLike.ofReal_eq_complex_ofReal,Complex.ofReal_inv]
  rw [hd]
  simp only [directionalPrincipal,map_sum]
  abel

end TamingCompatibility.HilbertSobolev

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Elliptic_FrozenSystem
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
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
open EuclideanSobolevOperators TemperedDistribution _root_.MeasureTheory LineDeriv Set Filter
open scoped SchwartzMap LineDeriv Topology ContDiff
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in
lemma local_frozen_system {ι κ : Type*} [Fintype ι] [Fintype κ]
    (χ : 𝓢(E,ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (g : basisIndex E → basisIndex E → 𝓢(E,ℂ)) (p : E)
    (hgp : ∀ i j, g i j p = if i=j then ((((2*Real.pi)^2)⁻¹ : ℝ) : ℂ) else 0)
    (r : ℝ) (hr : r ≠ 0) (ψ : 𝓢(E,ℂ)) (hψ : ∀ x ∈ tsupport ψ, χ x = 1)
    (B : ι → 𝓢(E,ℂ)) (L : ι → F →L[ℂ] F) (v : ι → E)
    (C : κ → 𝓢(E,ℂ)) (K : κ → F →L[ℂ] F) (u : 𝓢'(E,F)) :
    smulLeftCLM F ψ (perturbedHelmholtz
      (frozenPrincipal χ hχ (fun i j x => -g i j x) (fun i j => (g i j).smooth ⊤ |>.neg) p r) u +
      matrixLowerOrder B L v (Sum.elim C (fun _ : Unit => -χ))
        (Sum.elim K (fun _ : Unit => ContinuousLinearMap.id ℂ F)) u) =
    smulLeftCLM F ψ (-directionalPrincipal (stdOrthonormalBasis ℝ E)
      (fun i j => affineSchwartz p r hr (g i j)) u + matrixLowerOrder B L v C K u) := by
  rw [map_add,local_frozen_helmholtz χ hχ g p hgp r hr ψ hψ u,
    matrixLowerOrder_sub_cutoff B L v C K χ u,map_sub,local_cutoff_one χ ψ hψ u]
  simp only [map_add,map_neg]
  abel

lemma memSobolevLoc_zoom_one (p : E) (r : ℝ) (hr : r ≠ 0)
    {U : Set E} {u : 𝓢'(E,F)} (hu : MemSobolevLoc U 1 u) :
    MemSobolevLoc ((fun y => r • y+p) ⁻¹' U) 1 (zoomDistribution p r hr u) := by
  have hu' : MemSobolevLoc U (1 : ℕ) u := by simpa only [Nat.cast_one] using hu
  simpa only [Nat.cast_one] using memSobolevLoc_zoom 1 p r hr hu'

end TamingCompatibility.HilbertSobolev

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
namespace TamingCompatibility.EuclideanSobolev
open _root_.MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal Topology BoundedContinuousFunction
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

def sobolevToBounded (s : ℝ) (hs : Module.finrank ℝ E < 2*s) :
    HilbertSobolev.H E F s →L[ℂ] (E →ᵇ F) :=
  InjectiveLinearLift.continuousLift boundedDistributionCLM boundedDistributionCLM_injective
    (HilbertSobolev.toDistribution E F s) (fun u => by
      obtain ⟨g,hg⟩ := exists_boundedContinuous_representative hs
        (HilbertSobolev.toDistribution_memSobolev s u)
      exact ⟨g,hg.symm⟩)

lemma sobolevToBounded_spec (s : ℝ) (hs : Module.finrank ℝ E < 2*s)
    (u : HilbertSobolev.H E F s) :
    boundedDistribution (sobolevToBounded s hs u) = HilbertSobolev.toDistribution E F s u := by
  change boundedDistributionCLM (sobolevToBounded s hs u) = _
  exact InjectiveLinearLift.continuousLift_spec _ _ _ _ _
end TamingCompatibility.EuclideanSobolev

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Elliptic_CriticalH1Linear
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
open EuclideanSobolevOperators TemperedDistribution _root_.MeasureTheory LineDeriv Set Filter
open scoped SchwartzMap LineDeriv Topology ContDiff
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem normalized_scalar_uniform_regular {ι κ : Type*} [Fintype ι] [Fintype κ]
    {U : Set E} (hU : IsOpen U) (p : E) (hp : p ∈ U)
    (g : basisIndex E → basisIndex E → 𝓢(E,ℂ))
    (hgp : ∀ i j, g i j p = if i=j then ((((2*Real.pi)^2)⁻¹ : ℝ) : ℂ) else 0)
    (b : ι → 𝓢(E,ℂ)) (L : ι → F →L[ℂ] F) (v : ι → E)
    (c : κ → 𝓢(E,ℂ)) (K : κ → F →L[ℂ] F) :
    ∃ V : Set E, IsOpen V ∧ p ∈ V ∧ V ⊆ U ∧ ∀ (n : ℕ) (u : 𝓢'(E,F)),
      MemSobolevLoc U 1 u → MemSobolevLoc U n
        (-directionalPrincipal (stdOrthonormalBasis ℝ E) g u + matrixLowerOrder b L v c K u) →
      MemSobolevLoc V ((n:ℝ)+2) u := by
  obtain ⟨χ,hχ,hχone⟩ := exists_unit_cutoff (E := E)
  obtain ⟨r,hr,hweak,hstrong⟩ := exists_small_frozen_scale (F := F) χ hχ g p
  have hr0 : r ≠ 0 := ne_of_gt hr
  let W : Set E := (fun y => r • y+p) ⁻¹' U ∩ Metric.ball 0 1
  have hW : IsOpen W := (hU.preimage (by fun_prop)).inter Metric.isOpen_ball
  have h0W : (0 : E) ∈ W := by simpa only [W,mem_inter_iff,mem_preimage,smul_zero,zero_add,
    Metric.mem_ball,dist_self] using And.intro hp (show (0 : ℝ) < 1 by norm_num)
  let a := frozenPrincipal χ hχ (fun i j x => -g i j x) (fun i j => (g i j).smooth ⊤ |>.neg) p r
  let B := fun i => r • affineSchwartz p r hr0 (b i)
  let C := fun i => (r*r) • affineSchwartz p r hr0 (c i)
  let V : Set E := (fun y => r⁻¹ • y + -(r⁻¹ • p)) ⁻¹' W
  have hV : IsOpen V := hW.preimage (by fun_prop)
  have hpV : p ∈ V := by
    change r⁻¹ • p + -(r⁻¹ • p) ∈ W
    simpa only [add_neg_cancel] using h0W
  have hVU : V ⊆ U := by
    intro x hx
    have h := hx.1
    change r • (r⁻¹ • x + -(r⁻¹ • p))+p ∈ U at h
    simpa only [smul_add,smul_neg,smul_smul,mul_inv_cancel₀ hr0,one_smul,neg_add_cancel_right] using h
  refine ⟨V,hV,hpV,hVU,?_⟩
  intro n u hu hf
  let z := zoomDistribution p r hr0 u
  have hz : MemSobolevLoc W 1 z := by
    exact (memSobolevLoc_zoom_one p r hr0 hu).restrict inter_subset_left
  have hsource : MemSobolevLoc W n
      (perturbedHelmholtz a z + matrixLowerOrder B L v
        (Sum.elim C (fun _ : Unit => -χ))
        (Sum.elim K (fun _ : Unit => ContinuousLinearMap.id ℂ F)) z) := by
    intro ψ hψ hψW
    have hpψ : ∀ x ∈ tsupport ψ, χ x = 1 := fun x hx => hχone x (hψW hx).2
    have h := (memSobolevLoc_zoom n p r hr0 hf).real_smul (r*r) ψ hψ
      (fun x hx => (hψW hx).1)
    rw [rescaled_system] at h
    rw [local_frozen_system χ hχ g p hgp r hr0 ψ hpψ B L v C K z]
    exact h
  have hzreg : MemSobolevLoc W ((n:ℝ)+2) z :=
    matrix_H1_interior_bootstrap n hW a hweak hstrong B L v
      (Sum.elim C (fun _ : Unit => -χ))
      (Sum.elim K (fun _ : Unit => ContinuousLinearMap.id ℂ F)) hz hsource
  have hzreg' : MemSobolevLoc W ((n+2 : ℕ) : ℝ) z := by
    simpa only [Nat.cast_add,Nat.cast_ofNat] using hzreg
  have h := memSobolevLoc_affine (n+2) p r hr0 hzreg'
  rw [zoomDistribution_inverse] at h
  simpa only [Nat.cast_add,Nat.cast_ofNat] using h

end TamingCompatibility.HilbertSobolev

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_LinearUniform
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
open EuclideanSobolevOperators TemperedDistribution _root_.MeasureTheory LineDeriv Set Filter
open scoped SchwartzMap LineDeriv Topology ContDiff
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem linearly_normalized_uniform_regular {ι κ τ : Type*}
    [Fintype ι] [Fintype κ] [Fintype τ]
    {U : Set E} (hU : IsOpen U) (p : E) (hp : p ∈ U)
    (d : ι → E) (g : ι → ι → 𝓢(E,ℂ)) (A : E ≃L[ℝ] E)
    (hgp : ∀ i j, principalInBasis (stdOrthonormalBasis ℝ E) (fun i => A (d i))
      (fun i j => SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.symm (g i j)) i j (A p) =
        if i=j then ((((2*Real.pi)^2)⁻¹ : ℝ) : ℂ) else 0)
    (b : κ → 𝓢(E,ℂ)) (L : κ → F →L[ℂ] F) (v : κ → E)
    (c : τ → 𝓢(E,ℂ)) (K : τ → F →L[ℂ] F) :
    ∃ V : Set E, IsOpen V ∧ p ∈ V ∧ V ⊆ U ∧ ∀ (n : ℕ) (u : 𝓢'(E,F)),
      MemSobolevLoc U 1 u → MemSobolevLoc U n
        (-directionalPrincipal d g u + matrixLowerOrder b L v c K u) →
      MemSobolevLoc V ((n:ℝ)+2) u := by
  let G := principalInBasis (stdOrthonormalBasis ℝ E) (fun i => A (d i))
    (fun i j => SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.symm (g i j))
  let B := fun i => SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.symm (b i)
  let C := fun i => SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.symm (c i)
  obtain ⟨V,hV,hpV,hVU,hall⟩ := normalized_scalar_uniform_regular
    (hU.preimage A.symm.continuous) (A p) (by simpa only [mem_preimage,ContinuousLinearEquiv.symm_apply_apply] using hp)
    G hgp B L (fun i => A (v i)) C K
  refine ⟨A ⁻¹' V,hV.preimage A.continuous,hpV,?_,?_⟩
  · intro x hx
    have h := hVU hx
    simpa only [mem_preimage,ContinuousLinearEquiv.symm_apply_apply] using h
  · intro n u hu hf
    have hf' : MemSobolevLoc (A.symm ⁻¹' U) n
        (-directionalPrincipal (stdOrthonormalBasis ℝ E) G (linearDistribution A u) +
          matrixLowerOrder B L (fun i => A (v i)) C K (linearDistribution A u)) := by
      have h := memSobolevLoc_linear n A hf
      rw [map_add,map_neg,directionalPrincipal_linear,matrixLowerOrder_linear,
        directionalPrincipal_basis (stdOrthonormalBasis ℝ E)] at h
      exact h
    have hr := hall n (linearDistribution A u) (memSobolevLoc_linear_one A hu) hf'
    have hr' : MemSobolevLoc V ((n+2 : ℕ) : ℝ) (linearDistribution A u) := by
      simpa only [Nat.cast_add,Nat.cast_ofNat] using hr
    have h := memSobolevLoc_linear (n+2) A.symm hr'
    rw [linearDistribution_inverse] at h
    simpa only [Nat.cast_add,Nat.cast_ofNat,ContinuousLinearEquiv.symm_symm] using h

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
open _root_.MeasureTheory TemperedDistribution
open scoped SchwartzMap BoundedContinuousFunction
variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

def realSobolevLift (s : ℝ) (L : G →L[ℝ] 𝓢'(E,F))
    (hL : ∀ g, MemSobolev s 2 (L g)) : G →L[ℝ] H E F s :=
  InjectiveLinearLift.continuousLift ((toDistribution E F s).restrictScalars ℝ)
    (toDistribution_injective s) L (fun g => by
      have hg : L g ∈ Set.range (toDistribution E F s) := by
        rw [range_toDistribution]; exact hL g
      exact hg)

lemma realSobolevLift_spec (s : ℝ) (L : G →L[ℝ] 𝓢'(E,F))
    (hL : ∀ g, MemSobolev s 2 (L g)) (g : G) :
    toDistribution E F s (realSobolevLift s L hL g) = L g := by
  unfold realSobolevLift
  exact InjectiveLinearLift.continuousLift_spec ((toDistribution E F s).restrictScalars ℝ)
    (toDistribution_injective s) L _ g

end TamingCompatibility.HilbertSobolev

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeShiftedRegularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.ComplexMatrix
open HilbertSobolev EuclideanSobolevOperators TemperedDistribution _root_.MeasureTheory LineDeriv
open LocalMatrixOperator EuclideanEnergy Set
open scoped SchwartzMap LineDeriv
variable {m : ℕ}

lemma full_shifted_square_uniform_regular
    {U : Set V} (hU : IsOpen U) (p : V) (hp : p ∈ U)
    (metric : MetricModel.Metric V) (frame : Fin 4 → V)
    (hframe : ∀ i j, metric.bilinear (frame i) (frame j) = if i=j then 1 else 0)
    (a : Fin 4 → 𝓢(V,R 6 →L[ℝ] R m)) (b : 𝓢(V,R 6 →L[ℝ] R m))
    (ρ : 𝓢(V,ℝ)) (ζ : 𝓢(V,ℂ)) (g : Fin 4 → Fin 4 → V → ℝ)
    (ha : ∀ i j x, (ρ x • a i x).adjoint ∘L a j x + (ρ x • a j x).adjoint ∘L a i x =
      (2*g i j x) • ContinuousLinearMap.id ℝ (R 6))
    (c : ℝ) (hc : 0 < c)
    (hgp : ∀ i j, g i j p = c * ∑ t, frame t i * frame t j) :
    ∃ W : Set V, IsOpen W ∧ p ∈ W ∧ W ⊆ U ∧ ∀ (n : ℕ) (u : 𝓢'(V,C 6)),
      MemSobolevLoc U 1 u → MemSobolevLoc U n (fullShiftedSquare a b ρ ζ u) →
      MemSobolevLoc W ((n:ℝ)+2) u := by
  let G := fullPrincipalScalar a ρ
  have hg : ∀ i j, G i j p = (c * ∑ t, frame t i * frame t j : ℝ) := by
    intro i j
    rw [fullPrincipalScalar_apply a ρ g ha,hgp]
  have hk : 0 < ((2*Real.pi)^2)⁻¹ := by positivity
  obtain ⟨A,hA⟩ := exists_principal_normalization metric frame hframe c _ hc hk G p hg
  let B := squareFirst e (fun i => coefficient (a i)) (coefficient b)
    (fun i => fullWeightedAdj ρ (a i)) (fullWeightedAdj ρ b)
  let Cc := squareZero e (coefficient b) (fun i => fullWeightedAdj ρ (a i))
    (fullWeightedAdj ρ b)+scalarMatrix 6 ζ
  obtain ⟨W,hW,hpW,hWU,hall⟩ := linearly_normalized_uniform_regular hU p hp e G A hA
    (fun q : Fin 4 × Fin 6 × Fin 6 => B q.1 q.2.1 q.2.2)
    (fun q => unit 6 6 q.2.1 q.2.2) (fun q => e q.1)
    (fun q : Fin 6 × Fin 6 => Cc q.1 q.2) (fun q => unit 6 6 q.1 q.2)
  refine ⟨W,hW,hpW,hWU,?_⟩
  intro n u hu hf
  apply hall n u hu
  have h := hf
  rw [full_shifted_square_expansion a b ρ ζ g ha] at h
  exact h
end TamingCompatibility.ComplexMatrix

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeCommutatorPowers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.ComplexMatrix
open HilbertSobolev EuclideanSobolevOperators TemperedDistribution _root_.MeasureTheory LineDeriv
open LocalMatrixOperator EuclideanEnergy Set
open scoped SchwartzMap LineDeriv
variable {m : ℕ}

lemma normalizedFullSquare_order (n : ℕ)
    (a : Fin 4 → 𝓢(V,R 6 →L[ℝ] R m)) (b : 𝓢(V,R 6 →L[ℝ] R m))
    (ρ : 𝓢(V,ℝ)) (θ : 𝓢(V,ℂ)) (g : Fin 4 → Fin 4 → V → ℝ)
    (ha : ∀ i j x, (ρ x • a i x).adjoint ∘L a j x + (ρ x • a j x).adjoint ∘L a i x =
      (2*g i j x) • ContinuousLinearMap.id ℝ (R 6))
    {u : 𝓢'(V,C 6)} (hu : MemSobolev ((n:ℝ)+2) 2 u) :
    MemSobolev n 2 (normalizedFullSquare a b ρ θ u) :=
  memSobolev_nat_product n θ (fullShiftedSquare_memSobolev n a b ρ 0 g ha hu)

lemma normalizedFullSquare_commutator_order (n : ℕ)
    (a : Fin 4 → 𝓢(V,R 6 →L[ℝ] R m)) (b : 𝓢(V,R 6 →L[ℝ] R m))
    (ρ : 𝓢(V,ℝ)) (θ : 𝓢(V,ℂ)) (g : Fin 4 → Fin 4 → V → ℝ)
    (ha : ∀ i j x, (ρ x • a i x).adjoint ∘L a j x + (ρ x • a j x).adjoint ∘L a i x =
      (2*g i j x) • ContinuousLinearMap.id ℝ (R 6)) (M : C 6 →L[ℂ] C 6)
    {u : 𝓢'(V,C 6)} (hu : MemSobolev ((n:ℝ)+1) 2 u) :
    MemSobolev n 2 (normalizedFullSquare a b ρ θ (fiberMap M u) -
      fiberMap M (normalizedFullSquare a b ρ θ u)) := by
  change MemSobolev _ _ (smulLeftCLM (C 6) θ _ - fiberMap M (smulLeftCLM (C 6) θ _))
  rw [fiberMap_product,← map_sub]
  exact memSobolev_nat_product n θ (fullShiftedSquare_commutator_memSobolev n a b ρ 0 g ha M hu)

lemma normalizedFullSquare_power_commutator_order (k n : ℕ)
    (a : Fin 4 → 𝓢(V,R 6 →L[ℝ] R m)) (b : 𝓢(V,R 6 →L[ℝ] R m))
    (ρ : 𝓢(V,ℝ)) (θ : 𝓢(V,ℂ)) (g : Fin 4 → Fin 4 → V → ℝ)
    (ha : ∀ i j x, (ρ x • a i x).adjoint ∘L a j x + (ρ x • a j x).adjoint ∘L a i x =
      (2*g i j x) • ContinuousLinearMap.id ℝ (R 6)) (M : C 6 →L[ℂ] C 6)
    {u : 𝓢'(V,C 6)} (hu : MemSobolev ((n:ℝ)+2*k+1) 2 u) :
    MemSobolev n 2 (((normalizedFullSquare a b ρ θ)^(k+1)) (fiberMap M u)-
      fiberMap M (((normalizedFullSquare a b ρ θ)^(k+1)) u)) := by
  exact operator_power_commutator_order _ M
    (fun n _ hu => normalizedFullSquare_order n a b ρ θ g ha hu)
    (fun n _ hu => normalizedFullSquare_commutator_order n a b ρ θ g ha M hu) k n hu
end TamingCompatibility.ComplexMatrix

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeDifferentialLocality
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
namespace TamingCompatibility.ComplexMatrix
open HilbertSobolev EuclideanSobolevOperators TemperedDistribution Filter Set
open LocalMatrixOperator EuclideanEnergy
open scoped SchwartzMap LineDeriv Topology
variable {m : ℕ}

lemma normalizedFullSquare_cutoff_locality
    (a : Fin 4 → 𝓢(V,R 6 →L[ℝ] R m)) (b : 𝓢(V,R 6 →L[ℝ] R m))
    (ρ : 𝓢(V,ℝ)) (θ : 𝓢(V,ℂ)) (G : Fin 4 → Fin 4 → V → ℝ)
    (hG : ∀ i j x, (ρ x • a i x).adjoint ∘L a j x + (ρ x • a j x).adjoint ∘L a i x =
      (2*G i j x) • ContinuousLinearMap.id ℝ (R 6))
    (g h : 𝓢(V,ℂ)) (hh : ∀ x ∈ tsupport g, h =ᶠ[𝓝 x] fun _ => 1) (u : 𝓢'(V,C 6)) :
    smulLeftCLM (C 6) g (normalizedFullSquare a b ρ θ (smulLeftCLM (C 6) h u)) =
      smulLeftCLM (C 6) g (normalizedFullSquare a b ρ θ u) := by
  change smulLeftCLM (C 6) g (smulLeftCLM (C 6) θ _) = smulLeftCLM (C 6) g (smulLeftCLM (C 6) θ _)
  rw [coefficient_products_commute g θ,coefficient_products_commute g θ]
  apply congrArg (smulLeftCLM (C 6) θ)
  exact fullShiftedSquare_cutoff_locality a b ρ 0 G hG g h hh u

lemma normalizedFullSquare_local_congr
    (a : Fin 4 → 𝓢(V,R 6 →L[ℝ] R m)) (b : 𝓢(V,R 6 →L[ℝ] R m))
    (ρ : 𝓢(V,ℝ)) (θ : 𝓢(V,ℂ)) (G : Fin 4 → Fin 4 → V → ℝ)
    (hG : ∀ i j x, (ρ x • a i x).adjoint ∘L a j x + (ρ x • a j x).adjoint ∘L a i x =
      (2*G i j x) • ContinuousLinearMap.id ℝ (R 6))
    {U : Set V} (hU : IsOpen U) {u v : 𝓢'(V,C 6)} (huv : LocallyEqual U u v) :
    LocallyEqual U (normalizedFullSquare a b ρ θ u) (normalizedFullSquare a b ρ θ v) := by
  intro χ hc hχU
  obtain ⟨η,hη,hηU,hηχ⟩ := exists_outer_cutoff hU χ hc hχU
  rw [← normalizedFullSquare_cutoff_locality a b ρ θ G hG χ η hηχ u,
    huv η hη hηU,normalizedFullSquare_cutoff_locality a b ρ θ G hG χ η hηχ v]

lemma normalizedFullSquare_power_local_congr
    (a : Fin 4 → 𝓢(V,R 6 →L[ℝ] R m)) (b : 𝓢(V,R 6 →L[ℝ] R m))
    (ρ : 𝓢(V,ℝ)) (θ : 𝓢(V,ℂ)) (G : Fin 4 → Fin 4 → V → ℝ)
    (hG : ∀ i j x, (ρ x • a i x).adjoint ∘L a j x + (ρ x • a j x).adjoint ∘L a i x =
      (2*G i j x) • ContinuousLinearMap.id ℝ (R 6))
    {U : Set V} (hU : IsOpen U) (k : ℕ) {u v : 𝓢'(V,C 6)} (huv : LocallyEqual U u v) :
    LocallyEqual U (((normalizedFullSquare a b ρ θ)^k) u) (((normalizedFullSquare a b ρ θ)^k) v) := by
  induction k with
  | zero => simpa using huv
  | succ k ih =>
    rw [pow_succ',mul_apply_eq_comp,mul_apply_eq_comp]
    exact normalizedFullSquare_local_congr a b ρ θ G hG hU ih

end TamingCompatibility.ComplexMatrix

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
namespace TamingCompatibility.ComplexMatrix
open HilbertSobolev EuclideanSobolevOperators TemperedDistribution _root_.MeasureTheory LineDeriv
open LocalMatrixOperator EuclideanEnergy Set
open scoped SchwartzMap LineDeriv
variable {m : ℕ}

def normalizedFullSquare_power_commutator_lift (k n : ℕ)
    (a : Fin 4 → 𝓢(V,R 6 →L[ℝ] R m)) (b : 𝓢(V,R 6 →L[ℝ] R m))
    (ρ : 𝓢(V,ℝ)) (θ : 𝓢(V,ℂ)) (g : Fin 4 → Fin 4 → V → ℝ)
    (ha : ∀ i j x, (ρ x • a i x).adjoint ∘L a j x + (ρ x • a j x).adjoint ∘L a i x =
      (2*g i j x) • ContinuousLinearMap.id ℝ (R 6)) (M : C 6 →L[ℂ] C 6) :
    H V (C 6) ((n:ℝ)+2*k+1) →L[ℝ] H V (C 6) n :=
  let P := normalizedFullSquare a b ρ θ
  let F := (((P^(k+1)).comp (fiberMap M) - (fiberMap M).comp (P^(k+1))).comp
    (toDistribution V (C 6) ((n:ℝ)+2*k+1))).restrictScalars ℝ
  realSobolevLift n F (fun u => normalizedFullSquare_power_commutator_order
    k n a b ρ θ g ha M (toDistribution_memSobolev _ u))

lemma normalizedFullSquare_power_commutator_lift_spec (k n : ℕ)
    (a : Fin 4 → 𝓢(V,R 6 →L[ℝ] R m)) (b : 𝓢(V,R 6 →L[ℝ] R m))
    (ρ : 𝓢(V,ℝ)) (θ : 𝓢(V,ℂ)) (g : Fin 4 → Fin 4 → V → ℝ)
    (ha : ∀ i j x, (ρ x • a i x).adjoint ∘L a j x + (ρ x • a j x).adjoint ∘L a i x =
      (2*g i j x) • ContinuousLinearMap.id ℝ (R 6)) (M : C 6 →L[ℂ] C 6)
    (u : H V (C 6) ((n:ℝ)+2*k+1)) :
    toDistribution V (C 6) n (normalizedFullSquare_power_commutator_lift k n a b ρ θ g ha M u) =
      ((normalizedFullSquare a b ρ θ)^(k+1)) (fiberMap M (toDistribution V (C 6) ((n:ℝ)+2*k+1) u)) -
      fiberMap M (((normalizedFullSquare a b ρ θ)^(k+1)) (toDistribution V (C 6) ((n:ℝ)+2*k+1) u)) := by
  unfold normalizedFullSquare_power_commutator_lift
  exact realSobolevLift_spec _ _ _ _
lemma normalizedFullSquare_power_commutator_lift_zero_spec (k : ℕ)
    (a : Fin 4 → 𝓢(V,R 6 →L[ℝ] R m)) (b : 𝓢(V,R 6 →L[ℝ] R m))
    (ρ : 𝓢(V,ℝ)) (θ : 𝓢(V,ℂ)) (g : Fin 4 → Fin 4 → V → ℝ)
    (ha : ∀ i j x, (ρ x • a i x).adjoint ∘L a j x + (ρ x • a j x).adjoint ∘L a i x =
      (2*g i j x) • ContinuousLinearMap.id ℝ (R 6)) (M : C 6 →L[ℂ] C 6)
    (u : H V (C 6) (2*k+1:ℕ)) :
    toDistribution V (C 6) 0 (normalizedFullSquare_power_commutator_lift k 0 a b ρ θ g ha M u) =
      ((normalizedFullSquare a b ρ θ)^(k+1)) (fiberMap M (toDistribution V (C 6) (2*k+1:ℕ) u)) -
      fiberMap M (((normalizedFullSquare a b ρ θ)^(k+1)) (toDistribution V (C 6) (2*k+1:ℕ) u)) := by
  have h := normalizedFullSquare_power_commutator_lift_spec k 0 a b ρ θ g ha M u
  simpa only [toDistribution,Nat.cast_zero,Nat.cast_add,Nat.cast_mul,Nat.cast_one,Nat.cast_ofNat,zero_add] using h
end TamingCompatibility.ComplexMatrix

end
end

section
noncomputable section
namespace TamingCompatibility.ComplexMatrix
open HilbertSobolev TemperedDistribution EuclideanEnergy Set
open scoped SchwartzMap
variable {m : ℕ}
lemma normalized_commutator_localized_spec (k : ℕ)
    (a : Fin 4 → 𝓢(V,R 6 →L[ℝ] R m)) (b : 𝓢(V,R 6 →L[ℝ] R m))
    (ρ : 𝓢(V,ℝ)) (θ : 𝓢(V,ℂ)) (g : Fin 4 → Fin 4 → V → ℝ)
    (ha : ∀ i j x, (ρ x • a i x).adjoint ∘L a j x + (ρ x • a j x).adjoint ∘L a i x =
      (2*g i j x) • ContinuousLinearMap.id ℝ (R 6))
    (M : C 6 →L[ℂ] C 6) (χ : 𝓢(V,ℂ)) (u : H V (C 6) (2*k+1:ℕ))
    (v w : 𝓢'(V,C 6))
    (hu : toDistribution V (C 6) (2*k+1:ℕ) u = v)
    (hw : smulLeftCLM (C 6) χ
      (((normalizedFullSquare a b ρ θ)^(k+1)) (fiberMap M v) -
        fiberMap M (((normalizedFullSquare a b ρ θ)^(k+1)) v)) = smulLeftCLM (C 6) χ w) :
    toDistribution V (C 6) 0 (product 0 χ
      (normalizedFullSquare_power_commutator_lift k 0 a b ρ θ g ha M u)) = smulLeftCLM (C 6) χ w := by
  have hp : toDistribution V (C 6) 0 (product 0 χ
      (normalizedFullSquare_power_commutator_lift k 0 a b ρ θ g ha M u)) =
    smulLeftCLM (C 6) χ (toDistribution V (C 6) 0
      (normalizedFullSquare_power_commutator_lift k 0 a b ρ θ g ha M u)) := by
    simpa only [toDistribution,Nat.cast_zero] using toDistribution_product (F := C 6) 0 χ
      (normalizedFullSquare_power_commutator_lift k 0 a b ρ θ g ha M u)
  rw [hp,normalizedFullSquare_power_commutator_lift_zero_spec,hu]
  exact hw
end TamingCompatibility.ComplexMatrix

end
end

end
end

end OAI
end


