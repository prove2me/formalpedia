-- Prove2me | Definitions.Def_OAIQ239Tc030
-- name    : OAIQ239Tc030
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T23:35:39.170628+00:00
-- url     : https://prove2.me/theorems/4baf9150-28a9-40a9-ad48-9f6402e2653c
-- title:
--   Definitions bundle OAIQ239Tc030 of the split of OpenAI, Taming implies compatibility on four-manifolds
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.TamingCompatibility.taming_implies_compatibility`, carved from OpenAI's openai/math development (OpenAI, *Taming implies compatibility on four-manifolds*, OpenAI Math Release, October 6, 2026, result family 342, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 5 declarations of OpenAI's Lean: 5 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: [`TamingCompatibility_Hodge_HodgeCommutatorPowers`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Hodge/HodgeCommutatorPowers.lean), [`TamingCompatibility_Hodge_HodgeProjectionRaw`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Hodge/HodgeProjectionRaw.lean), [`TamingCompatibility_Hodge_HodgeSmoothPatch`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Hodge/HodgeSmoothPatch.lean).
--
--   **Imports.** It imports the published bundle `Def_TamingCompatibility`; the bundles `OAIQ239Tc034` and `OAIQ239Tc036` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ239Tc032`.
-- source:
--   OpenAI, Taming implies compatibility on four-manifolds, OpenAI Math Release, October 6, 2026, https://github.com/openai/math (result family 342; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Taming-implies-compatibility-on-four-manifolds-October-6-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit 7ef5c0c

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc034
import Definitions.Def_OAIQ239Tc036

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
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume
open ComplexMatrix Set Filter _root_.MeasureTheory TemperedDistribution
open scoped Manifold ContDiff SchwartzMap RealInnerProductSpace BoundedContinuousFunction
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).toData.source)

lemma hodge_local_pairing_eq (p : A.centers) (τ : 𝓢(Space,ℝ))
    {U : Set Space} (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * GeometricChart.coordinateWeight A p z = 1)
    (u : hodgeEnergy A J α hs ht) (g : Space →ᵇ C 6)
    (hg : ∀ χ : 𝓢(Space,ℂ), HasCompactSupport (χ : Space → ℂ) → tsupport χ ⊆ U →
      hodgeRawDistribution A J α hs ht D hD p τ u χ = EuclideanSobolev.boundedDistribution g χ)
    (w : PreL2 A J α hs ht true)
    (hw : ∀ z ∈ U, rawVector J α ht p.val (D p).toData w.val z = retract 6 (g z))
    (φ : 𝓢(Space,ℝ)) (hc : HasCompactSupport (φ : Space → ℝ)) (hφU : tsupport φ ⊆ U)
    (j : Fin 6) :
    ⟪hodgeInclusion A J α hs ht u,smoothL2 A J α hs ht true
      (hodgeTest A J α hs ht D p (componentTest j φ)
        (full_componentTest_compact j φ hc) ((full_componentTest_support j φ).trans (hφU.trans hUD)))⟫ =
    ⟪smoothL2 A J α hs ht true w,smoothL2 A J α hs ht true
      (hodgeTest A J α hs ht D p (componentTest j φ)
        (full_componentTest_compact j φ hc) ((full_componentTest_support j φ).trans (hφU.trans hUD)))⟫ := by
  obtain ⟨η,hηc,hηU,hηone⟩ := SchwartzCutoff.exists_one_on_compact hc hU hφU
  let ρ : 𝓢(Space,ℝ) := SchwartzCutoff.schwartz (D p).domain_open
    ((chartDensity_smooth J α hs ht p.val).mono (D p).domain_subset)
    (η.smooth ⊤) hηc (hηU.trans hUD)
  have hρ : ∀ z ∈ tsupport φ, ρ z = chartDensity J α p.val z := by
    intro z hz
    change η z * chartDensity J α p.val z = _
    rw [hηone z hz,one_mul]
  let θ := SchwartzMap.smulLeftCLM ℝ ρ φ
  let ψ := SchwartzMap.postcompCLM Complex.ofRealCLM θ
  have hθ : tsupport θ ⊆ tsupport φ := (SchwartzMap.tsupport_smulLeftCLM_subset ρ φ).trans inter_subset_left
  have hψ : tsupport ψ ⊆ tsupport θ := tsupport_comp_subset (map_zero Complex.ofRealCLM) θ
  have he := hg ψ (hc.of_isClosed_subset (isClosed_tsupport ψ) (hψ.trans hθ))
    (hψ.trans (hθ.trans hφU))
  have hp := hodge_raw_weighted_pair A J α hs ht D hD p τ ρ (hφU.trans hUD)
    (fun z hz => hτ z (hφU hz)) hρ φ hc Subset.rfl j u
  have hψeq : SchwartzMap.smulLeftCLM ℂ (SchwartzMap.postcompCLM Complex.ofRealCLM ρ)
      (SchwartzMap.postcompCLM Complex.ofRealCLM φ) = ψ := by
    ext z
    simp only [SchwartzMap.smulLeftCLM_apply (SchwartzMap.postcompCLM Complex.ofRealCLM ρ).hasTemperateGrowth,
      SchwartzMap.postcompCLM_apply,Complex.ofRealCLM_apply,smul_eq_mul,ψ,θ,
      SchwartzMap.smulLeftCLM_apply ρ.hasTemperateGrowth,Complex.ofReal_mul]
  rw [smulLeftCLM_apply_apply,hψeq,he] at hp
  have hr := congrArg Complex.re hp
  rw [bounded_real_component,Complex.ofReal_re] at hr
  rw [hodgeInclusion_smooth] at hr
  rw [← hr,(smoothL2 A J α hs ht true).inner_map_map,preL2_inner]
  change _ = ∫ x, GeometricAdjoint.pairing J α ht w.val
    (manifoldTest J α ht p.val (D p).toData (componentTest j φ)) x ∂geometricVolume A J α
  rw [pairing_manifoldTest_integral J α ht p.val (D p).toData A hs w.property
    ((componentTest j φ).smooth ⊤) (full_componentTest_compact j φ hc)
    ((full_componentTest_support j φ).trans (hφU.trans hUD))]
  apply integral_congr_ae
  filter_upwards [] with z
  simp only [θ,SchwartzMap.smulLeftCLM_apply ρ.hasTemperateGrowth,smul_eq_mul]
  rw [componentTest_inner]
  by_cases hz : z ∈ tsupport φ
  · rw [hρ z hz,hw z (hφU hz),retract_apply]
    ring
  · rw [image_eq_zero_of_notMem_tsupport hz]
    ring
end TamingCompatibility.GeometricHilbert

end
end

end
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

lemma hodge_laplacian_weighted_distribution (p : A.centers) (τ : 𝓢(Space,ℝ))
    {U : Set Space} (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    (a : Fin 4 → 𝓢(Space,HodgeNormalSymbol.W →L[ℝ] HodgeNormalSymbol.Q))
    (b : 𝓢(Space,HodgeNormalSymbol.W →L[ℝ] HodgeNormalSymbol.Q)) (ρ : 𝓢(Space,ℝ))
    (ha : ∀ z ∈ U, ∀ i, a i z = normalA J α ht p.val (D p).toData i z)
    (hb : ∀ z ∈ U, b z = normalB J α ht p.val (D p).toData z)
    (hρ : ∀ z ∈ U, ρ z = chartDensity J α p.val z)
    (f : PreL2 A J α hs ht true)
    (χ : 𝓢(Space,ℂ)) (hc : HasCompactSupport (χ : Space → ℂ)) (hχU : tsupport χ ⊆ U) :
    smulLeftCLM (C 6) χ (fullShiftedSquare a b ρ 0
      (hodgeRawDistribution A J α hs ht D hD p τ (hodgeSmooth A J α hs ht f))) =
    smulLeftCLM (C 6) χ (smulLeftCLM (C 6) (SchwartzMap.postcompCLM Complex.ofRealCLM ρ)
      (hodgeRawDistribution A J α hs ht D hD p τ
        (hodgeSmooth A J α hs ht (hodgeLaplacian A J α hs ht f)))) := by
  apply localize_eq_of_real_tests _ χ hc hχU
  intro φ hφ hφU
  have hzero (u : 𝓢'(Space,C 6)) : smulLeftCLM (C 6) (0 : 𝓢(Space,ℂ)) u = 0 := by
    change smulLeftCLM (C 6) (fun _ => 0) u = 0
    rw [smulLeftCLM_const]
    exact zero_smul ℂ u
  change (square EuclideanEnergy.e a b ρ _ + smulLeftCLM (C 6) (0 : 𝓢(Space,ℂ)) _) (SchwartzMap.postcompCLM Complex.ofRealCLM φ) = _
  rw [hzero,add_zero]
  ext j
  rw [hodge_raw_square_energy_smooth A J α hs ht D hD p τ hU hUD hτ a b ρ ha hb hρ φ hφ hφU j,
    hodge_raw_weighted_pair A J α hs ht D hD p τ ρ hUD hτ hρ φ hφ hφU j,
    hodgeInclusion_smooth,hodgeLaplacian_green_weak]
end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeProjectionRaw
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
variable (p : A.centers) (τ : 𝓢(Space,ℝ))
    {U : Set Space} (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    (a : Fin 4 → 𝓢(Space,HodgeNormalSymbol.W →L[ℝ] HodgeNormalSymbol.Q))
    (b : 𝓢(Space,HodgeNormalSymbol.W →L[ℝ] HodgeNormalSymbol.Q)) (ρ : 𝓢(Space,ℝ))
    (ha : ∀ z ∈ U, ∀ i, a i z = normalA J α ht p.val (D p).toData i z)
    (hb : ∀ z ∈ U, b z = normalB J α ht p.val (D p).toData z)
    (hρ : ∀ z ∈ U, ρ z = chartDensity J α p.val z)
    (θ : 𝓢(Space,ℂ)) (hθ : ∀ z ∈ U, θ z * (ρ z : ℂ) = 1)

include hU hUD hτ ha hb hρ hθ

lemma hodge_laplacian_local_distribution (f : PreL2 A J α hs ht true) :
    LocallyEqual U
      (normalizedFullSquare a b ρ θ (hodgeRawDistribution A J α hs ht D hD p τ
        (hodgeSmooth A J α hs ht f)))
      (hodgeRawDistribution A J α hs ht D hD p τ
        (hodgeSmooth A J α hs ht (hodgeLaplacian A J α hs ht f))) := by
  intro χ hc hχU
  change smulLeftCLM (C 6) χ (smulLeftCLM (C 6) θ _) = _
  rw [coefficient_products_commute χ θ]
  refine (congrArg (smulLeftCLM (C 6) θ)
    (hodge_laplacian_weighted_distribution A J α hs ht D hD p τ hU hUD hτ a b ρ ha hb hρ f χ hc hχU)).trans ?_
  rw [coefficient_products_commute θ χ]
  exact triple_product_cancel χ θ (SchwartzMap.postcompCLM Complex.ofRealCLM ρ)
    (fun z hz => hθ z (hχU hz)) _

lemma hodge_laplacian_power_local_distribution
    (G : Fin 4 → Fin 4 → Space → ℝ)
    (hG : ∀ i j z, (ρ z • a i z).adjoint ∘L a j z + (ρ z • a j z).adjoint ∘L a i z =
        (2*G i j z) • ContinuousLinearMap.id ℝ (ComplexMatrix.R 6))
    (k : ℕ) (f : PreL2 A J α hs ht true) :
    LocallyEqual U
      (((normalizedFullSquare a b ρ θ)^k) (hodgeRawDistribution A J α hs ht D hD p τ
        (hodgeSmooth A J α hs ht f)))
      (hodgeRawDistribution A J α hs ht D hD p τ
        (hodgeSmooth A J α hs ht (((hodgeLaplacian A J α hs ht)^k) f))) := by
  induction k with
  | zero => exact LocallyEqual.refl _ _
  | succ k ih =>
    rw [pow_succ',mul_apply_eq_comp,pow_succ' (hodgeLaplacian A J α hs ht) k]
    change LocallyEqual U _ (hodgeRawDistribution A J α hs ht D hD p τ
      (hodgeSmooth A J α hs ht (hodgeLaplacian A J α hs ht (((hodgeLaplacian A J α hs ht)^k) f))))
    exact (normalizedFullSquare_local_congr a b ρ θ G hG hU ih).trans
      (hodge_laplacian_local_distribution A J α hs ht D hD p τ hU hUD hτ a b ρ ha hb hρ θ hθ _)
end TamingCompatibility.GeometricHilbert

end
end

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
variable (p : A.centers) (τ : 𝓢(Space,ℝ))
    {U : Set Space} (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    (a : Fin 4 → 𝓢(Space,HodgeNormalSymbol.W →L[ℝ] HodgeNormalSymbol.Q))
    (b : 𝓢(Space,HodgeNormalSymbol.W →L[ℝ] HodgeNormalSymbol.Q)) (ρ : 𝓢(Space,ℝ))
    (ha : ∀ z ∈ U, ∀ i, a i z = normalA J α ht p.val (D p).toData i z)
    (hb : ∀ z ∈ U, b z = normalB J α ht p.val (D p).toData z)
    (hρ : ∀ z ∈ U, ρ z = chartDensity J α p.val z)
    (θ : 𝓢(Space,ℂ)) (hθ : ∀ z ∈ U, θ z * (ρ z : ℂ) = 1)
    (G : Fin 4 → Fin 4 → Space → ℝ)
    (hG : ∀ i j z, (ρ z • a i z).adjoint ∘L a j z + (ρ z • a j z).adjoint ∘L a i z =
        (2*G i j z) • ContinuousLinearMap.id ℝ (ComplexMatrix.R 6))
include hU hUD hτ ha hb hρ hθ hG

lemma hodge_commutator_local_distribution (k : ℕ) (f : PreL2 A J α hs ht true) :
    LocallyEqual U
      ((((normalizedFullSquare a b ρ θ)^k)
        (fiberMap antiMatrix (hodgeRawDistribution A J α hs ht D hD p τ
          (hodgeSmooth A J α hs ht f)))) -
        fiberMap antiMatrix (((normalizedFullSquare a b ρ θ)^k)
          (hodgeRawDistribution A J α hs ht D hD p τ (hodgeSmooth A J α hs ht f))))
      (hodgeRawDistribution A J α hs ht D hD p τ
        (hodgeSmooth A J α hs ht (hodgePowerCommutator A J α hs ht k f))) := by
  have hpi (g : PreL2 A J α hs ht true) :
      hodgeRawDistribution A J α hs ht D hD p τ (hodgeSmooth A J α hs ht (preAntiProjection A J α hs ht g)) =
        fiberMap antiMatrix (hodgeRawDistribution A J α hs ht D hD p τ (hodgeSmooth A J α hs ht g)) :=
    hodgeRawDistribution_smooth_antiInvariant A J α hs ht D hD p τ g
  have h1 := hodge_laplacian_power_local_distribution A J α hs ht D hD p τ hU hUD hτ
    a b ρ ha hb hρ θ hθ G hG k (preAntiProjection A J α hs ht f)
  have h2 := (hodge_laplacian_power_local_distribution A J α hs ht D hD p τ hU hUD hτ
    a b ρ ha hb hρ θ hθ G hG k f).fiberMap antiMatrix
  rw [hpi f] at h1
  simpa only [hodgePowerCommutator_apply,map_sub,hpi] using h1.sub h2
end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end


