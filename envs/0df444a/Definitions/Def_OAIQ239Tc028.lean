-- Prove2me | Definitions.Def_OAIQ239Tc028
-- name    : OAIQ239Tc028
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T23:23:01.006744+00:00
-- url     : https://prove2.me/theorems/d1b70dc6-3c4f-4084-bfe0-8d0ba9236bcb
-- title:
--   Definitions bundle OAIQ239Tc028 of the split of OpenAI, Taming implies compatibility on four-manifolds
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.TamingCompatibility.taming_implies_compatibility`, carved from OpenAI's openai/math development (OpenAI, *Taming implies compatibility on four-manifolds*, OpenAI Math Release, October 6, 2026, result family 342, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 16 declarations of OpenAI's Lean: 2 definitions and 14 theorems. The definitions and types are `OAI.TamingCompatibility.GeometricHilbert.hodgeGammaTailAction`, `OAI.TamingCompatibility.GeometricHilbert.weakDelta`.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: [`TamingCompatibility_DifferentialForms_GeometricFredholm`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/DifferentialForms/GeometricFredholm.lean), [`TamingCompatibility_Functional_GeometricCompact`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Functional/GeometricCompact.lean), [`TamingCompatibility_HeatFlow_HodgeResolventStar`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/HeatFlow/HodgeResolventStar.lean), [`TamingCompatibility_Hodge_HodgeGammaSplit`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Hodge/HodgeGammaSplit.lean), [`TamingCompatibility_Hodge_HodgeScalarJet`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Hodge/HodgeScalarJet.lean), [`TamingCompatibility_Hodge_HodgeScalarRaw`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Hodge/HodgeScalarRaw.lean), [`TamingCompatibility_Hodge_HodgeScaleH3`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Hodge/HodgeScaleH3.lean), [`TamingCompatibility_Hodge_HodgeSmoothLaplacian`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Hodge/HodgeSmoothLaplacian.lean), [`TamingCompatibility_Hodge_HodgeTestPairing`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Hodge/HodgeTestPairing.lean).
--
--   **Imports.** It imports the published bundle `Def_TamingCompatibility`; the bundles `OAIQ239Tc025`, `OAIQ239Tc026` and `OAIQ239Tc027` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ239Tc034` and `OAIQ239Tc036`; the statements `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.same_resolvent_continuous_data`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.same_resolvent_smooth_spatial`, `OAI.TamingCompatibility.GeometricHilbert.HodgeSmoothingCover.pairingGammaTail_integral`, `OAI.TamingCompatibility.GeometricHilbert.actual_localized_square_source`, `OAI.TamingCompatibility.GeometricHilbert.actual_localized_square_source_on`, `OAI.TamingCompatibility.GeometricHilbert.exists_local_ddstar_estimate_on`, `OAI.TamingCompatibility.GeometricHilbert.geometric_center_energy_two_jet`, `OAI.TamingCompatibility.GeometricHilbert.geometric_center_local_energy_two_jet`, `OAI.TamingCompatibility.GeometricHilbert.raw_smooth_near`, `OAI.TamingCompatibility.GeometricHilbert.raw_square_source` and `OAI.TamingCompatibility.GeometricHilbert.raw_two_jet_estimate`; the proofs of `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.same_resolvent_smooth_spatial`, `OAI.TamingCompatibility.GeometricHilbert.actual_localized_square_source`, `OAI.TamingCompatibility.GeometricHilbert.actual_localized_square_source_on`, `OAI.TamingCompatibility.GeometricHilbert.exists_local_ddstar_estimate_on`, `OAI.TamingCompatibility.GeometricHilbert.geometric_center_energy_two_jet`, `OAI.TamingCompatibility.GeometricHilbert.geometric_center_local_energy_two_jet`, `OAI.TamingCompatibility.GeometricHilbert.raw_smooth_near`, `OAI.TamingCompatibility.GeometricHilbert.raw_square_source` and `OAI.TamingCompatibility.GeometricHilbert.raw_two_jet_estimate`.
-- source:
--   OpenAI, Taming implies compatibility on four-manifolds, OpenAI Math Release, October 6, 2026, https://github.com/openai/math (result family 342; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Taming-implies-compatibility-on-four-manifolds-October-6-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit 7ef5c0c

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc025
import Definitions.Def_OAIQ239Tc026
import Definitions.Def_OAIQ239Tc027

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Functional_GeometricCompact
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart
open _root_.MeasureTheory
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

def weakDelta : antiEnergy A J α hs ht →L[ℝ] L2 A J α hs ht false :=
  (WithLp.sndL 2 ℝ _ _) ∘L (antiEnergy A J α hs ht).subtypeL

end TamingCompatibility.GeometricHilbert

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_GeometricFredholm
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
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

lemma graphEnergy_coercive : IsCoercive
    (Variational.energy (energyInclusion A J α hs ht) (weakDelta A J α hs ht)) := by
  refine ⟨1,zero_lt_one,fun u => ?_⟩
  rw [Variational.energy_apply,real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq]
  have h := WithLp.prod_norm_sq_eq_of_L2 u.val
  change 1 * ‖u.val‖ * ‖u.val‖ ≤ ‖u.val.fst‖^2 + ‖u.val.snd‖^2
  nlinarith

end TamingCompatibility.GeometricHilbert

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeScalarJet
attribute [-instance] _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.frameMap_apply _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDifferential_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap_zero _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeScaledDerivative_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth
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
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart _root_.MeasureTheory
open EuclideanSobolevOperators TemperedDistribution
open scoped Manifold ContDiff SchwartzMap
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).toData.source)

lemma hodgeScalarDistribution_H1 (p : A.centers) (u : hodgeEnergy A J α hs ht) :
    MemSobolev 1 2 (hodgeScalarDistribution A J α hs ht D hD p u) := by
  have h0 (j : DerivativeIndex) : MemSobolev 0 2
      (HodgeScalar.jetDistribution j (hodgeEnergyToScalarJet A J α hs ht D hD p u)) := by
    refine ⟨hodgeEnergyToScalarJet A J α hs ht D hD p u j,?_⟩
    simp only [besselPotential_zero,ContinuousLinearMap.id_apply]
    rfl
  have hd (i : Fin (Module.finrank ℝ Space)) : MemSobolev 0 2
      (LineDeriv.lineDerivOpCLM ℝ 𝓢'(Space,HodgeScalar.F) (stdOrthonormalBasis ℝ Space i)
        (hodgeScalarDistribution A J α hs ht D hD p u)) := by
    change MemSobolev 0 2 (LineDeriv.lineDerivOpCLM ℝ _ _
      (HodgeScalar.jetDistribution none (hodgeEnergyToScalarJet A J α hs ht D hD p u)))
    rw [hodge_energy_scalar_derivative]
    exact h0 (some i)
  convert memSobolev_succ_of_derivatives (stdOrthonormalBasis ℝ Space) (h0 none) hd using 1
  · rfl
  · norm_num
  · rfl
lemma hodgeScalarDistribution_smooth (p : A.centers) (a : PreL2 A J α hs ht true) :
    hodgeScalarDistribution A J α hs ht D hD p (hodgeSmooth A J α hs ht a) =
      (scalarVectorLinear A J α ht (fun q => (D q).toData) hD p a : 𝓢'(Space,HodgeScalar.F)) := by
  change HodgeScalar.jetDistribution none
    (hodgeEnergyToScalarJet A J α hs ht D hD p (hodgeSmooth A J α hs ht a)) = _
  rw [hodgeEnergyToScalarJet_smooth]
  exact HodgeScalar.jetDistribution_jet _ none

lemma hodgeRawDistribution_H1 (p : A.centers) (τ : 𝓢(Space,ℝ)) (u : hodgeEnergy A J α hs ht) :
    MemSobolev 1 2 (hodgeRawDistribution A J α hs ht D hD p τ u) := by
  change MemSobolev 1 2 (smulLeftCLM HodgeScalar.F
    (SchwartzMap.postcompCLM Complex.ofRealCLM τ) (hodgeScalarDistribution A J α hs ht D hD p u))
  have hu := hodgeScalarDistribution_H1 A J α hs ht D hD p u
  simpa only [Nat.cast_one] using
    (EuclideanSobolevOperators.memSobolev_nat_product (E := Space) (F := HodgeScalar.F) 1
      (SchwartzMap.postcompCLM Complex.ofRealCLM τ)
      (u := hodgeScalarDistribution A J α hs ht D hD p u) (by simpa only [Nat.cast_one] using hu))
end TamingCompatibility.GeometricHilbert

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
lemma realVectorSchwartz_raw (p : A.centers) (a : smoothForms X 2)
    {z : Space} (hz : z ∈ (D p).domain) :
    realVectorSchwartz A J α ht D hD p a z = coordinateWeight A p z • rawVector J α ht p.val (D p) a.val z := by
  ext i
  rw [realVectorSchwartz_apply,scalar_eq_weight A J α ht D p a.val i hz]
  rfl
lemma cutoff_realVector_raw (p : A.centers) (a : smoothForms X 2) (τ : 𝓢(Space,ℝ))
    {z : Space} (hz : z ∈ (D p).domain) (hτ : τ z * coordinateWeight A p z = 1) :
    SchwartzMap.smulLeftCLM HodgeNormalSymbol.W τ (realVectorSchwartz A J α ht D hD p a) z =
      rawVector J α ht p.val (D p) a.val z := by
  rw [SchwartzMap.smulLeftCLM_apply_apply τ.hasTemperateGrowth,
    realVectorSchwartz_raw A J α ht D hD p a hz,smul_smul,hτ,one_smul]
end TamingCompatibility.HodgeChart

namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart _root_.MeasureTheory ComplexMatrix
open EuclideanSobolevOperators TemperedDistribution
open scoped Manifold ContDiff SchwartzMap
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).toData.source)
lemma hodgeRawDistribution_smooth (p : A.centers) (τ : 𝓢(Space,ℝ)) (a : PreL2 A J α hs ht true) :
    hodgeRawDistribution A J α hs ht D hD p τ (hodgeSmooth A J α hs ht a) =
      (SchwartzMap.postcompCLM (embed 6)
        (SchwartzMap.smulLeftCLM HodgeNormalSymbol.W τ
          (realVectorSchwartz A J α ht (fun q => (D q).toData) hD p a)) : 𝓢'(Space,HodgeScalar.F)) := by
  change smulLeftCLM HodgeScalar.F (SchwartzMap.postcompCLM Complex.ofRealCLM τ)
    (hodgeScalarDistribution A J α hs ht D hD p (hodgeSmooth A J α hs ht a)) = _
  rw [hodgeScalarDistribution_smooth,product_schwartz]
  congr 1
  rw [← realVectorSchwartz_embed A J α ht (fun q => (D q).toData) hD p a]
  ext z i
  simp only [SchwartzMap.smulLeftCLM_apply (SchwartzMap.postcompCLM Complex.ofRealCLM τ).hasTemperateGrowth,
    SchwartzMap.smulLeftCLM_apply τ.hasTemperateGrowth,SchwartzMap.postcompCLM_apply,embed_apply,
    PiLp.smul_apply,Complex.ofRealCLM_apply,smul_eq_mul,Complex.ofReal_mul]
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

lemma hodge_raw_weighted_pair (p : A.centers) (τ ρ : 𝓢(Space,ℝ))
    {U : Set Space} (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    (hρ : ∀ z ∈ U, ρ z = chartDensity J α p.val z)
    (φ : 𝓢(Space,ℝ)) (hc : HasCompactSupport (φ : Space → ℝ)) (hφU : tsupport φ ⊆ U)
    (j : Fin 6) (u : hodgeEnergy A J α hs ht) :
    ((smulLeftCLM (C 6) (SchwartzMap.postcompCLM Complex.ofRealCLM ρ)
      (hodgeRawDistribution A J α hs ht D hD p τ u))
      (SchwartzMap.postcompCLM Complex.ofRealCLM φ)) j =
    (⟪hodgeInclusion A J α hs ht u,hodgeInclusion A J α hs ht
      (hodgeSmooth A J α hs ht (hodgeTest A J α hs ht D p (componentTest j φ)
        (full_componentTest_compact j φ hc) ((full_componentTest_support j φ).trans (hφU.trans hUD))))⟫ : ℂ) := by
  let v := hodgeTest A J α hs ht D p (componentTest j φ)
    (full_componentTest_compact j φ hc) ((full_componentTest_support j φ).trans (hφU.trans hUD))
  let P := smulLeftCLM (C 6) (SchwartzMap.postcompCLM Complex.ofRealCLM ρ)
  have hLc : Continuous (fun w => (P (hodgeRawDistribution A J α hs ht D hD p τ w)
      (SchwartzMap.postcompCLM Complex.ofRealCLM φ)) j) :=
    continuous_system_eval (hodgeRawDistribution A J α hs ht D hD p τ) P _ j
  have hRc : Continuous (fun w => (⟪hodgeInclusion A J α hs ht w,
      hodgeInclusion A J α hs ht (hodgeSmooth A J α hs ht v)⟫ : ℂ)) :=
    Complex.continuous_ofReal.comp ((hodgeInclusion A J α hs ht).continuous.inner continuous_const)
  refine (hodgeSmooth_dense A J α hs ht).induction_on u (isClosed_eq hLc hRc) ?_
  intro f
  change (P (hodgeRawDistribution A J α hs ht D hD p τ (hodgeSmooth A J α hs ht f))
    (SchwartzMap.postcompCLM Complex.ofRealCLM φ)) j = _
  rw [hodgeRawDistribution_smooth]
  dsimp only [P]
  rw [product_schwartz,product_embed_schwartz]
  symm
  apply hodge_rhs_component_test A J α hs ht D p f hUD _ ?_ φ hc hφU j
  intro z hz
  rw [SchwartzMap.smulLeftCLM_apply ρ.hasTemperateGrowth]
  change ρ z • (SchwartzMap.smulLeftCLM HodgeNormalSymbol.W τ
    (realVectorSchwartz A J α ht (fun q => (D q).toData) hD p (⟨f.val,f.property⟩ : smoothForms X 2))) z = _
  rw [hρ z hz]
  congr 1
  exact cutoff_realVector_raw A J α ht (fun q => (D q).toData) hD p f τ (hUD hz) (hτ z hz)
end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_HeatFlow_HodgeResolventStar
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

lemma hodgeWeakSolution_unique (r : ℝ) (hr : 0 < r) (f : L2 A J α hs ht true)
    (u : hodgeEnergy A J α hs ht)
    (hu : ∀ v : hodgeEnergy A J α hs ht,
      ⟪hodgeInclusion A J α hs ht u,hodgeInclusion A J α hs ht v⟫ +
        r^2*⟪hodgeWeakDerivative A J α hs ht u,hodgeWeakDerivative A J α hs ht v⟫ =
          ⟪f,hodgeInclusion A J α hs ht v⟫) :
    hodgeWeakSolution A J α hs ht r hr f = u := by
  let w := hodgeWeakSolution A J α hs ht r hr f
  let i := hodgeInclusion A J α hs ht
  let D := hodgeWeakDerivative A J α hs ht
  have he := hodgeWeakSolution_identity A J α hs ht r hr f (w-u)
  rw [hodgeResolvent_eq A J α hs ht r hr,ContinuousLinearMap.comp_apply] at he
  have hu' := hu (w-u)
  have hz : ⟪i (w-u),i (w-u)⟫ +r^2*⟪D (w-u),D (w-u)⟫ = 0 := by
    rw [map_sub,map_sub,inner_sub_left,inner_sub_left]
    change ⟪i w,i w-i u⟫ +r^2*⟪D w,D w-D u⟫ = ⟪f,i w-i u⟫ at he
    change ⟪i u,i w-i u⟫ +r^2*⟪D u,D w-D u⟫ = ⟪f,i w-i u⟫ at hu'
    linarith
  have hnon : 0 ≤ r^2*⟪D (w-u),D (w-u)⟫ := mul_nonneg (sq_nonneg _) real_inner_self_nonneg
  have hh : ⟪i (w-u),i (w-u)⟫ = 0 := le_antisymm (by linarith) real_inner_self_nonneg
  have hzero : i (w-u) = 0 := inner_self_eq_zero.mp hh
  apply hodgeInclusion_injective A J α hs ht
  exact sub_eq_zero.mp (by rw [← map_sub]; exact hzero)

end TamingCompatibility.GeometricHilbert

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

lemma hodgeWeakSolution_scale_transfer (r : ℝ) (hr : 0 < r)
    (f : L2 A J α hs ht true) :
    hodgeWeakSolution A J α hs ht 1 zero_lt_one
      ((r^2)⁻¹ • f + (1-(r^2)⁻¹) • hodgeResolvent A J α hs ht r f) =
      hodgeWeakSolution A J α hs ht r hr f := by
  apply hodgeWeakSolution_unique
  intro v
  have he := hodgeWeakSolution_identity A J α hs ht r hr f v
  have hi : hodgeInclusion A J α hs ht (hodgeWeakSolution A J α hs ht r hr f) =
      hodgeResolvent A J α hs ht r f := by
    rw [hodgeResolvent_eq A J α hs ht r hr]; rfl
  rw [hi,inner_add_left,real_inner_smul_left,real_inner_smul_left]
  have hn : r^2 ≠ 0 := pow_ne_zero 2 hr.ne'
  have hmul := congrArg ((r^2)⁻¹ * ·) he
  rw [mul_add,← mul_assoc,inv_mul_cancel₀ hn,one_mul] at hmul
  norm_num only [one_pow,one_mul]
  linarith

lemma hodgeGraphResolvent_scale_transfer (r : ℝ) (hr : 0 < r)
    (u : hodgeEnergy A J α hs ht) :
    hodgeGraphResolvent A J α hs ht 1 zero_lt_one
      ((r^2)⁻¹ • u + (1-(r^2)⁻¹) • hodgeGraphResolvent A J α hs ht r hr u) =
      hodgeGraphResolvent A J α hs ht r hr u := by
  change hodgeWeakSolution A J α hs ht 1 zero_lt_one
    (hodgeInclusion A J α hs ht (_+_)) = _
  rw [map_add,map_smul,map_smul]
  have hi : hodgeInclusion A J α hs ht (hodgeGraphResolvent A J α hs ht r hr u) =
      hodgeResolvent A J α hs ht r (hodgeInclusion A J α hs ht u) := by
    rw [hodgeResolvent_eq A J α hs ht r hr]; rfl
  rw [hi]
  exact hodgeWeakSolution_scale_transfer A J α hs ht r hr _
end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeGammaSplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization Set _root_.MeasureTheory
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source)

def hodgeGammaTailAction (T r : ℝ) (f : L2 A J α hs ht true) : L2 A J α hs ht true :=
  (1/120 : ℝ) • ∫ s : ℝ in Ioi (T/r^2),
    hodgeGammaWeight s • hodgeSpectralHeat A J α hs ht D hD (r^2*s) f

end TamingCompatibility.GeometricHilbert

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

lemma hodgeScaleH3Input_spec (r : ℝ) (hr : 0 < r) (f : L2 A J α hs ht true) :
    hodgeGraphResolvent A J α hs ht 1 zero_lt_one (hodgeScaleH3Input A J α hs ht r hr f) =
      hodgeRegularizedGraph A J α hs ht r hr f := by
  have hi : hodgeInclusion A J α hs ht
      (hodgeWeakSolution A J α hs ht r hr (hodgeResolvent A J α hs ht r f)) =
      hodgeResolvent A J α hs ht r (hodgeResolvent A J α hs ht r f) := by
    rw [hodgeResolvent_eq A J α hs ht r hr]; rfl
  have hu : hodgeGraphResolvent A J α hs ht r hr
      (hodgeWeakSolution A J α hs ht r hr (hodgeResolvent A J α hs ht r f)) =
      hodgeRegularizedGraph A J α hs ht r hr f := by
    exact congrArg (hodgeWeakSolution A J α hs ht r hr) hi
  have h := hodgeGraphResolvent_scale_transfer A J α hs ht r hr
    (hodgeWeakSolution A J α hs ht r hr (hodgeResolvent A J α hs ht r f))
  rw [hu] at h
  exact h

lemma hodgeScaleH3Input_bound (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) (f : L2 A J α hs ht true) :
    ‖hodgeScaleH3Input A J α hs ht r hr f‖ ≤ 4*(r⁻¹)^3*‖f‖ := by
  let a := (r^2)⁻¹
  have ha : 0 ≤ a := inv_nonneg.mpr (sq_nonneg _)
  have ha1 : 1 ≤ a := by
    apply (one_le_inv₀ (sq_pos_of_pos hr)).mpr
    have : r*r ≤ 1*1 := mul_le_mul hr1 hr1 hr.le zero_le_one
    simpa only [pow_two,one_mul] using this
  have hb : |1-a| ≤ a := by rw [abs_of_nonpos (by linarith)]; linarith
  have hu₂ : ‖hodgeWeakSolution A J α hs ht r hr (hodgeResolvent A J α hs ht r f)‖ ≤ 2*r⁻¹*‖f‖ :=
    (hodgeWeakSolution_graph_small_bound A J α hs ht r hr hr1 _).trans
      (mul_le_mul_of_nonneg_left (hodgeResolvent_norm_le A J α hs ht r f)
        (mul_nonneg (by norm_num) (inv_nonneg.mpr hr.le)))
  change ‖a • hodgeWeakSolution A J α hs ht r hr (hodgeResolvent A J α hs ht r f)+
    (1-a) • hodgeRegularizedGraph A J α hs ht r hr f‖ ≤ _
  calc
    _ ≤ ‖a • hodgeWeakSolution A J α hs ht r hr (hodgeResolvent A J α hs ht r f)‖+
        ‖(1-a) • hodgeRegularizedGraph A J α hs ht r hr f‖ := norm_add_le _ _
    _ = a*‖hodgeWeakSolution A J α hs ht r hr (hodgeResolvent A J α hs ht r f)‖+
        |1-a| *‖hodgeRegularizedGraph A J α hs ht r hr f‖ := by
      rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg ha]
    _ ≤ a*(2*r⁻¹*‖f‖)+a*(2*r⁻¹*‖f‖) := add_le_add (mul_le_mul_of_nonneg_left hu₂ ha)
      (mul_le_mul hb (hodgeRegularizedGraph_small_bound A J α hs ht r hr hr1 f) (norm_nonneg _) ha)
    _ = _ := by dsimp [a]; rw [inv_pow]; ring
end TamingCompatibility.GeometricHilbert

end
end

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open GeometricChart (coordinateWeight coordinateWeight_smooth)
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume
open Set Filter _root_.MeasureTheory ComplexMatrix TemperedDistribution HilbertSobolev EuclideanSobolev
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace BoundedContinuousFunction
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).toData.source)

omit [T2Space X] in

lemma hodgeRegularization_uniform_local_H1 (p : A.centers) (q : Space)
    (hq : q ∈ (D p).domain) (hwq : coordinateWeight A p q ≠ 0) :
    ∃ τ : 𝓢(Space,ℝ), ∃ U : Set Space,
      IsOpen U ∧ q ∈ U ∧ U ⊆ (D p).domain ∧
      (∀ z ∈ U, τ z * coordinateWeight A p z = 1) ∧
      ∃ B : ℝ, 0 ≤ B ∧ ∀ (r : ℝ) (hr : 0 < r), r ≤ 1 →
        ∃ L : L2 A J α hs ht true →L[ℝ] H Space (C 6) 1,
          (∀ f, toDistribution Space (C 6) 1 (L f) =
            hodgeRawDistribution A J α hs ht D hD p τ
              (hodgeRegularizedGraph A J α hs ht r hr f)) ∧
          ∀ f, ‖L f‖ ≤ B*r⁻¹*‖f‖ := by
  obtain ⟨τ,-,-,U,hU,hqU,hUD,hτ⟩ := SchwartzCutoff.exists_reciprocal
    (D p).domain_open ((coordinateWeight_smooth A p).mono (D p).domain_subset) hq hwq
  let F := hodgeRawDistribution A J α hs ht D hD p τ
  have hF : ∀ u, MemSobolev 1 2 (F u) := hodgeRawDistribution_H1 A J α hs ht D hD p τ
  let L := realSobolevLift 1 F hF
  have hL := realSobolevLift_spec 1 F hF
  refine ⟨τ,U,hU,hqU,hUD,hτ,2*‖L‖,by positivity,fun r hr hr1 => ?_⟩
  refine ⟨L.comp (hodgeRegularizedGraph A J α hs ht r hr),?_,?_⟩
  · exact fun f => hL _
  · intro f
    calc
      _ ≤ ‖L‖*‖hodgeRegularizedGraph A J α hs ht r hr f‖ := L.le_opNorm _
      _ ≤ ‖L‖*(2*r⁻¹*‖f‖) := mul_le_mul_of_nonneg_left
        (hodgeRegularizedGraph_small_bound A J α hs ht r hr hr1 f) (norm_nonneg L)
      _ = _ := by ring
end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end


