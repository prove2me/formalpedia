-- Prove2me | Definitions.Def_OAIQ239Tc029
-- name    : OAIQ239Tc029
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T23:23:58.19108+00:00
-- url     : https://prove2.me/theorems/352cf9fb-e998-4500-9fd8-f27642442b5e
-- title:
--   Definitions bundle OAIQ239Tc029 of the split of OpenAI, Taming implies compatibility on four-manifolds
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.TamingCompatibility.taming_implies_compatibility`, carved from OpenAI's openai/math development (OpenAI, *Taming implies compatibility on four-manifolds*, OpenAI Math Release, October 6, 2026, result family 342, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 20 declarations of OpenAI's Lean: 7 definitions and 13 theorems. The definitions and types are `OAI.TamingCompatibility.GeometricHilbert.hodgeHeatGamma`, `OAI.TamingCompatibility.GeometricHilbert.hodgeHeatGammaLinear`, `OAI.TamingCompatibility.GeometricHilbert.hodgeRawSchwartz`, `OAI.TamingCompatibility.GeometricHilbert.rawDistribution`, `OAI.TamingCompatibility.GeometricHilbert.rawH1`, `OAI.TamingCompatibility.GeometricHilbert.scalarDistribution`, `OAI.TamingCompatibility.GeometricHilbert.scalarEnergyDualLM`.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: [`TamingCompatibility_DifferentialForms_RawTest`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/DifferentialForms/RawTest.lean), [`TamingCompatibility_Elliptic_RawH1Bound`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Elliptic/RawH1Bound.lean), [`TamingCompatibility_Elliptic_ScalarRegularityBase`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Elliptic/ScalarRegularityBase.lean), [`TamingCompatibility_Functional_RadialEnergyDual`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Functional/RadialEnergyDual.lean), [`TamingCompatibility_HeatFlow_HodgeClosedResolvent`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/HeatFlow/HodgeClosedResolvent.lean), [`TamingCompatibility_HeatFlow_ResolventGammaScalar`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/HeatFlow/ResolventGammaScalar.lean), [`TamingCompatibility_Hodge_HodgeGlobalSmooth`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Hodge/HodgeGlobalSmooth.lean), [`TamingCompatibility_Hodge_HodgeScaleSmoothing`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Hodge/HodgeScaleSmoothing.lean), [`TamingCompatibility_Hodge_HodgeSmoothCommutator`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Hodge/HodgeSmoothCommutator.lean), [`TamingCompatibility_Hodge_HodgeSmoothLaplacian`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Hodge/HodgeSmoothLaplacian.lean), [`TamingCompatibility_Hodge_HodgeUniformCommutator`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Hodge/HodgeUniformCommutator.lean).
--
--   **Imports.** It imports the published bundle `Def_TamingCompatibility`; the bundles `OAIQ239Tc025`, `OAIQ239Tc026` and `OAIQ239Tc027` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ239Tc032`; the statements `OAI.TamingCompatibility.GeometricHilbert.Hermitian.scalarEnergyDual_cutoffLog_bound`, `OAI.TamingCompatibility.GeometricHilbert.Hermitian.scalarEnergyDual_cutoffSqrt_bound`, `OAI.TamingCompatibility.GeometricHilbert.raw_smooth_near` and `OAI.TamingCompatibility.GeometricHilbert.raw_square_source`; the proofs of `OAI.TamingCompatibility.GeometricHilbert.Hermitian.combinedForm_global_lower`, `OAI.TamingCompatibility.GeometricHilbert.Hermitian.scalarCorrection_logError_estimate`, `OAI.TamingCompatibility.GeometricHilbert.Hermitian.scalarCorrection_sqrtError_estimate`, `OAI.TamingCompatibility.GeometricHilbert.Hermitian.scalarEnergyDual_cutoffLog_bound`, `OAI.TamingCompatibility.GeometricHilbert.Hermitian.scalarEnergyDual_cutoffSqrt_bound`, `OAI.TamingCompatibility.GeometricHilbert.Hermitian.separating_probability_smooth_defect`, `OAI.TamingCompatibility.GeometricHilbert.actual_localized_square_source`, `OAI.TamingCompatibility.GeometricHilbert.actual_localized_square_source_on`, `OAI.TamingCompatibility.GeometricHilbert.closedLift_scalar_off_source`, `OAI.TamingCompatibility.GeometricHilbert.exists_closed_lift_hodge_bound`, `OAI.TamingCompatibility.GeometricHilbert.geometric_center_energy_two_jet`, `OAI.TamingCompatibility.GeometricHilbert.geometric_center_local_energy_two_jet`, `OAI.TamingCompatibility.GeometricHilbert.geometric_smooth_inverse`, `OAI.TamingCompatibility.GeometricHilbert.harmonic_schwartz_seminorm_bound`, `OAI.TamingCompatibility.GeometricHilbert.raw_smooth_near`, `OAI.TamingCompatibility.GeometricHilbert.raw_square_source`, `OAI.TamingCompatibility.GeometricHilbert.raw_two_jet_estimate`, `OAI.TamingCompatibility.GeometricHilbert.scalarCorrection_all_scales`, `OAI.TamingCompatibility.GeometricHilbert.scalarCorrection_local_estimates`, `OAI.TamingCompatibility.separating_probability_atlas_defect` and `OAI.TamingCompatibility.separating_probability_local_quadratic`.
-- source:
--   OpenAI, Taming implies compatibility on four-manifolds, OpenAI Math Release, October 6, 2026, https://github.com/openai/math (result family 342; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Taming-implies-compatibility-on-four-manifolds-October-6-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit 7ef5c0c

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc025
import Definitions.Def_OAIQ239Tc026
import Definitions.Def_OAIQ239Tc027

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Elliptic_ScalarRegularityBase
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.frameMap_apply _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDifferential_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap_zero _root_.OAI.TamingCompatibility.GeometricHilbert.antiMultiply_apply _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeInclusion_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeScaledDerivative_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.l2Star_smooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart _root_.MeasureTheory
open EuclideanSobolevOperators TemperedDistribution
open scoped Manifold ContDiff SchwartzMap RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

def scalarDistribution (p : A.centers) : antiEnergy A J α hs ht →L[ℝ] 𝓢'(Space,ScalarPair.F) :=
  ScalarPair.jetDistribution none ∘L energyToScalarJet A J α hs ht D hD p

lemma scalarDistribution_H1 (p : A.centers) (u : antiEnergy A J α hs ht) :
    MemSobolev 1 2 (scalarDistribution A J α hs ht D hD p u) := by
  have h0 (j : DerivativeIndex) : MemSobolev 0 2
      (ScalarPair.jetDistribution j (energyToScalarJet A J α hs ht D hD p u)) := by
    refine ⟨energyToScalarJet A J α hs ht D hD p u j,?_⟩
    simp only [besselPotential_zero,ContinuousLinearMap.id_apply]
    rfl
  have hd (i : Fin (Module.finrank ℝ Space)) : MemSobolev 0 2
      (LineDeriv.lineDerivOpCLM ℝ 𝓢'(Space,ScalarPair.F) (stdOrthonormalBasis ℝ Space i)
        (scalarDistribution A J α hs ht D hD p u)) := by
    change MemSobolev 0 2 (LineDeriv.lineDerivOpCLM ℝ _ _
      (ScalarPair.jetDistribution none (energyToScalarJet A J α hs ht D hD p u)))
    rw [energy_scalar_derivative]
    exact h0 (some i)
  convert memSobolev_succ_of_derivatives (stdOrthonormalBasis ℝ Space) (h0 none) hd using 1
  · rfl
  · norm_num
  · rfl

end TamingCompatibility.GeometricHilbert

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_RawTest
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
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart _root_.MeasureTheory ComplexMatrix
open EuclideanSobolevOperators TemperedDistribution
open scoped Manifold ContDiff SchwartzMap RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

def rawDistribution (p : A.centers) (τ : 𝓢(Space,ℝ)) :
    antiEnergy A J α hs ht →L[ℝ] 𝓢'(Space,ScalarPair.F) :=
  (smulLeftCLM ScalarPair.F (SchwartzMap.postcompCLM Complex.ofRealCLM τ)).restrictScalars ℝ ∘L
    scalarDistribution A J α hs ht D hD p

lemma rawDistribution_H1 (p : A.centers) (τ : 𝓢(Space,ℝ)) (u : antiEnergy A J α hs ht) :
    MemSobolev 1 2 (rawDistribution A J α hs ht D hD p τ u) := by
  change MemSobolev 1 2 (smulLeftCLM ScalarPair.F
    (SchwartzMap.postcompCLM Complex.ofRealCLM τ) (scalarDistribution A J α hs ht D hD p u))
  have hu := scalarDistribution_H1 A J α hs ht D hD p u
  simpa only [Nat.cast_one] using
    (EuclideanSobolevOperators.memSobolev_nat_product (E := Space) (F := ScalarPair.F) 1
      (SchwartzMap.postcompCLM Complex.ofRealCLM τ)
      (u := scalarDistribution A J α hs ht D hD p u) (by simpa only [Nat.cast_one] using hu))

end TamingCompatibility.GeometricHilbert

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Elliptic_RawH1Bound
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart _root_.MeasureTheory ComplexMatrix
open HilbertSobolev EuclideanSobolevOperators TemperedDistribution
open scoped Manifold ContDiff SchwartzMap RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

def rawH1 (p : A.centers) (τ : 𝓢(Space,ℝ)) :
    antiEnergy A J α hs ht →L[ℝ] H Space ScalarPair.F 1 :=
  InjectiveLinearLift.continuousLift ((toDistribution Space ScalarPair.F 1).restrictScalars ℝ)
    (toDistribution_injective 1) (rawDistribution A J α hs ht D hD p τ) (fun u => by
      have h := rawDistribution_H1 A J α hs ht D hD p τ u
      have hr : rawDistribution A J α hs ht D hD p τ u ∈
          Set.range (toDistribution Space ScalarPair.F 1) := by
        rw [range_toDistribution]
        exact h
      exact hr)

end TamingCompatibility.GeometricHilbert

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Functional_RadialEnergyDual
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

def scalarEnergyDualLM (p : A.centers) (K : Set Space) (hK : IsCompact K)
    (hKD : K ⊆ (D p).domain) (j : Fin 2) :
    supportedSchwartz K →ₗ[ℝ] StrongDual ℝ (antiEnergy A J α hs ht) :=
  (antiEnergyDualLM A J α hs ht).comp (scalarTestLM A J α hs ht D p K hK hKD j)

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

lemma hodgeWeakSolution_smoothShift (r : ℝ) (hr : 0 < r) (a : PreL2 A J α hs ht true) :
    hodgeWeakSolution A J α hs ht r hr
      (smoothL2 A J α hs ht true (hodgeSmoothShift A J α hs ht r a)) = hodgeSmooth A J α hs ht a := by
  apply (hodgeEnergy_coercive A J α hs ht r hr).continuousLinearEquivOfBilin.injective
  apply ext_inner_right ℝ
  intro v
  rw [IsCoercive.continuousLinearEquivOfBilin_apply,
    IsCoercive.continuousLinearEquivOfBilin_apply,hodgeWeakSolution_identity_raw,
    hodgeSmoothShift_apply,map_add,map_smul,inner_add_left,real_inner_smul_left,
    hodgeLaplacian_green_weak,Variational.energy_apply,hodgeInclusion_smooth,
    hodgeScaledDerivative_apply,hodgeScaledDerivative_apply,real_inner_smul_left,real_inner_smul_right]
  ring

lemma hodgeResolvent_smoothShift (r : ℝ) (hr : 0 < r) (a : PreL2 A J α hs ht true) :
    hodgeResolvent A J α hs ht r (smoothL2 A J α hs ht true (hodgeSmoothShift A J α hs ht r a)) =
      smoothL2 A J α hs ht true a := by
  rw [hodgeResolvent_eq A J α hs ht r hr,ContinuousLinearMap.comp_apply,
    hodgeWeakSolution_smoothShift,hodgeInclusion_smooth]

lemma hodgeRegularization_smoothShift_cube (r : ℝ) (hr : 0 < r) (a : PreL2 A J α hs ht true) :
    hodgeRegularization A J α hs ht r
      (smoothL2 A J α hs ht true ((hodgeSmoothShift A J α hs ht r ^ 3) a)) =
      smoothL2 A J α hs ht true a := by
  change hodgeResolvent A J α hs ht r (hodgeResolvent A J α hs ht r
    (hodgeResolvent A J α hs ht r (smoothL2 A J α hs ht true
      (hodgeSmoothShift A J α hs ht r (hodgeSmoothShift A J α hs ht r
        (hodgeSmoothShift A J α hs ht r a)))))) = _
  rw [hodgeResolvent_smoothShift A J α hs ht r hr,
    hodgeResolvent_smoothShift A J α hs ht r hr,hodgeResolvent_smoothShift A J α hs ht r hr]
end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeGlobalSmooth
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
omit [T2Space X] in
lemma hodgeResolvent_injective (r : ℝ) (hr : 0 < r) :
    Function.Injective (hodgeResolvent A J α hs ht r) := by
  intro f g h
  apply ext_inner_right ℝ
  have hsym (u v : L2 A J α hs ht true) :
      ⟪hodgeResolvent A J α hs ht r u,v⟫ = ⟪u,hodgeResolvent A J α hs ht r v⟫ :=
    hodgeResolvent_symmetric A J α hs ht r u v
  have he : (fun y : L2 A J α hs ht true => ⟪f,y⟫) = (fun y => ⟪g,y⟫) :=
    (smoothL2_dense A J α hs ht true).equalizer
      (continuous_const.inner continuous_id) (continuous_const.inner continuous_id) (by
      funext a
      change ⟪f,smoothL2 A J α hs ht true a⟫ = ⟪g,smoothL2 A J α hs ht true a⟫
      rw [← hodgeResolvent_smoothShift A J α hs ht r hr a,
        ← hsym,← hsym,h])
  exact congrFun he
omit [T2Space X] in
lemma hodgeRegularization_injective (r : ℝ) (hr : 0 < r) :
    Function.Injective (hodgeRegularization A J α hs ht r) := by
  intro f g h
  change hodgeResolvent A J α hs ht r (hodgeResolvent A J α hs ht r (hodgeResolvent A J α hs ht r f)) =
    hodgeResolvent A J α hs ht r (hodgeResolvent A J α hs ht r (hodgeResolvent A J α hs ht r g)) at h
  exact hodgeResolvent_injective A J α hs ht r hr
    (hodgeResolvent_injective A J α hs ht r hr (hodgeResolvent_injective A J α hs ht r hr h))
omit [T2Space X] in
lemma hodgeGraphResolvent_inclusion_power (r : ℝ) (hr : 0 < r) (j : ℕ)
    (u : hodgeEnergy A J α hs ht) :
    hodgeInclusion A J α hs ht ((hodgeGraphResolvent A J α hs ht r hr ^ j) u) =
      (hodgeResolvent A J α hs ht r ^ j) (hodgeInclusion A J α hs ht u) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [pow_succ',pow_succ']
    change hodgeInclusion A J α hs ht (hodgeWeakSolution A J α hs ht r hr
      (hodgeInclusion A J α hs ht ((hodgeGraphResolvent A J α hs ht r hr ^ j) u))) = _
    rw [ih,hodgeResolvent_eq A J α hs ht r hr]
    rfl
end TamingCompatibility.GeometricHilbert

end
end

end
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

omit [T2Space X] in
lemma hodgeRegularization_smooth_inverse (r : ℝ) (hr : 0 < r) (f b : PreL2 A J α hs ht true)
    (hb : smoothL2 A J α hs ht true b = hodgeRegularization A J α hs ht r (smoothL2 A J α hs ht true f)) :
    (hodgeSmoothShift A J α hs ht r ^ 3) b = f := by
  apply (smoothL2 A J α hs ht true).injective
  apply hodgeRegularization_injective A J α hs ht r hr
  rw [hodgeRegularization_smoothShift_cube A J α hs ht r hr,hb]

end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeScaleSmoothing
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.frameMap_apply _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDifferential_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap_zero _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth
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

lemma hodgeScaleInput_bound (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) (f : L2 A J α hs ht true) :
    ‖hodgeScaleInput A J α hs ht r hr f‖ ≤ 8*(r⁻¹)^5*‖f‖ := by
  let a := (r^2)⁻¹
  let b := 1-a
  let u₁ := hodgeWeakSolution A J α hs ht r hr f
  let u₂ := hodgeWeakSolution A J α hs ht r hr (hodgeResolvent A J α hs ht r f)
  let u₃ := hodgeRegularizedGraph A J α hs ht r hr f
  let K := 2*r⁻¹*‖f‖
  have ha : 0 ≤ a := inv_nonneg.mpr (sq_nonneg _)
  have ha1 : 1 ≤ a := by
    apply (one_le_inv₀ (sq_pos_of_pos hr)).mpr
    have : r*r ≤ 1*1 := mul_le_mul hr1 hr1 hr.le zero_le_one
    simpa only [pow_two,one_mul] using this
  have hb : |b| ≤ a := by rw [abs_of_nonpos (by dsimp [b] <;> linarith)]; dsimp [b]; linarith
  have hK : 0 ≤ K := mul_nonneg (mul_nonneg (by norm_num) (inv_nonneg.mpr hr.le)) (norm_nonneg f)
  have hu₁ : ‖u₁‖ ≤ K := hodgeWeakSolution_graph_small_bound A J α hs ht r hr hr1 f
  have hrf := hodgeResolvent_norm_le A J α hs ht r f
  have hrrf := hodgeResolvent_norm_le A J α hs ht r (hodgeResolvent A J α hs ht r f)
  have hu₂ : ‖u₂‖ ≤ K := (hodgeWeakSolution_graph_small_bound A J α hs ht r hr hr1 _).trans
    (mul_le_mul_of_nonneg_left hrf (mul_nonneg (by norm_num) (inv_nonneg.mpr hr.le)))
  have hu₃ : ‖u₃‖ ≤ K := (hodgeWeakSolution_graph_small_bound A J α hs ht r hr hr1 _).trans
    (mul_le_mul_of_nonneg_left (hrrf.trans hrf) (mul_nonneg (by norm_num) (inv_nonneg.mpr hr.le)))
  have hbound (u v : hodgeEnergy A J α hs ht) (hu : ‖u‖ ≤ K) (hv : ‖v‖ ≤ K) :
      ‖a • u+b • v‖ ≤ 2*a*K := by
    calc
      _ ≤ ‖a • u‖+‖b • v‖ := norm_add_le _ _
      _ = a*‖u‖+|b| *‖v‖ := by rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg ha]
      _ ≤ a*K+a*K := add_le_add (mul_le_mul_of_nonneg_left hu ha)
        (mul_le_mul hb hv (norm_nonneg _) ha)
      _ = _ := by ring
  change ‖a • (a • u₁+b • u₂)+b • (a • u₂+b • u₃)‖ ≤ _
  calc
    _ ≤ ‖a • (a • u₁+b • u₂)‖+‖b • (a • u₂+b • u₃)‖ := norm_add_le _ _
    _ = a*‖a • u₁+b • u₂‖+|b| *‖a • u₂+b • u₃‖ := by
      rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg ha]
    _ ≤ a*(2*a*K)+a*(2*a*K) := add_le_add (mul_le_mul_of_nonneg_left (hbound _ _ hu₁ hu₂) ha)
      (mul_le_mul hb (hbound _ _ hu₂ hu₃) (norm_nonneg _) ha)
    _ = 8*(r⁻¹)^5*‖f‖ := by dsimp [K,a]; rw [inv_pow]; ring
end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_HeatFlow_ResolventGammaScalar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization _root_.MeasureTheory Set
open scoped Manifold ContDiff RealInnerProductSpace

variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

lemma hodgeHeatGamma_integrable (r : ℝ) (f : L2 A J α hs ht true) :
    IntegrableOn (fun s : ℝ => hodgeGammaWeight s • hodgeSpectralHeat A J α hs ht D hD (r^2*s) f)
      (Ioi 0) := by
  have hc : Continuous (fun s : ℝ => hodgeGammaWeight s •
      hodgeSpectralHeat A J α hs ht D hD (r^2*s) f) := hodgeGammaWeight_continuous.smul
    ((hodgeSpectralHeat_continuous A J α hs ht D hD f).comp
      (continuous_const.mul continuous_id))
  apply (hodgeGammaWeight_integrable.mul_const ‖f‖).mono' hc.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hsp
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hodgeGammaWeight_nonneg hsp.le)]
  exact mul_le_mul_of_nonneg_left (hodgeSpectralHeat_norm_le A J α hs ht D hD _ f)
    (hodgeGammaWeight_nonneg hsp.le)

def hodgeHeatGammaLinear (r : ℝ) : L2 A J α hs ht true →ₗ[ℝ] L2 A J α hs ht true where
  toFun f := ∫ s : ℝ in Ioi 0, hodgeGammaWeight s • hodgeSpectralHeat A J α hs ht D hD (r^2*s) f
  map_add' f g := by
    simp only [map_add, smul_add]
    exact integral_add (hodgeHeatGamma_integrable A J α hs ht D hD r f)
      (hodgeHeatGamma_integrable A J α hs ht D hD r g)
  map_smul' c f := by
    simp only [map_smul, RingHom.id_apply, smul_comm (hodgeGammaWeight _) c]
    exact integral_smul c _

lemma hodgeHeatGammaLinear_norm_le (r : ℝ) (f : L2 A J α hs ht true) :
    ‖hodgeHeatGammaLinear A J α hs ht D hD r f‖ ≤ 120 * ‖f‖ := by
  calc
    _ ≤ ∫ s : ℝ in Ioi 0, ‖hodgeGammaWeight s • hodgeSpectralHeat A J α hs ht D hD (r^2*s) f‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ s : ℝ in Ioi 0, hodgeGammaWeight s * ‖f‖ := by
      apply integral_mono_ae (hodgeHeatGamma_integrable A J α hs ht D hD r f).norm
        (hodgeGammaWeight_integrable.mul_const ‖f‖)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hsp
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hodgeGammaWeight_nonneg hsp.le)]
      exact mul_le_mul_of_nonneg_left (hodgeSpectralHeat_norm_le A J α hs ht D hD _ f)
        (hodgeGammaWeight_nonneg hsp.le)
    _ = 120 * ‖f‖ := by rw [integral_mul_const, hodgeGammaWeight_integral]

def hodgeHeatGamma (r : ℝ) : L2 A J α hs ht true →L[ℝ] L2 A J α hs ht true :=
  (hodgeHeatGammaLinear A J α hs ht D hD r).mkContinuous 120
    (hodgeHeatGammaLinear_norm_le A J α hs ht D hD r)

end TamingCompatibility.GeometricHilbert

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

lemma hodgeRegularizedGraph_smoothShift_cube (r : ℝ) (hr : 0 < r)
    (a : PreL2 A J α hs ht true) :
    hodgeRegularizedGraph A J α hs ht r hr
      (smoothL2 A J α hs ht true ((hodgeSmoothShift A J α hs ht r ^ 3) a)) =
        hodgeSmooth A J α hs ht a := by
  apply hodgeInclusion_injective A J α hs ht
  rw [hodgeRegularizedGraph_inclusion,hodgeInclusion_smooth,
    hodgeRegularization_smoothShift_cube A J α hs ht r hr]
end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeUniformCommutator
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
open GeometricChart (coordinateWeight)
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume
open Set _root_.MeasureTheory ComplexMatrix TemperedDistribution HilbertSobolev
open scoped Manifold ContDiff SchwartzMap RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).toData.source)

def hodgeRawSchwartz (p : A.centers) (τ : 𝓢(Space,ℝ)) (χ : 𝓢(Space,ℂ))
    (f : PreL2 A J α hs ht true) : 𝓢(Space,C 6) :=
  SchwartzMap.smulLeftCLM (C 6) χ
    (SchwartzMap.postcompCLM (embed 6) (SchwartzMap.smulLeftCLM HodgeNormalSymbol.W τ
      (realVectorSchwartz A J α ht (fun p => (D p).toData) hD p f)))

end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end


