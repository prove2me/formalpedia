-- Prove2me | Definitions.Def_OAIQ239Tc037
-- name    : OAIQ239Tc037
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T23:57:59.676222+00:00
-- url     : https://prove2.me/theorems/4d4cd4a3-8f43-4651-949e-00645a6fbeab
-- title:
--   Definitions bundle OAIQ239Tc037 of the split of OpenAI, Taming implies compatibility on four-manifolds
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.TamingCompatibility.taming_implies_compatibility`, carved from OpenAI's openai/math development (OpenAI, *Taming implies compatibility on four-manifolds*, OpenAI Math Release, October 6, 2026, result family 342, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 theorem.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: [`TamingCompatibility_HeatFlow_HodgeResolvent`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/HeatFlow/HodgeResolvent.lean).
--
--   **Imports.** It imports the published bundle `Def_TamingCompatibility`; the bundle `OAIQ239Tc031` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ239Tc035`.
-- source:
--   OpenAI, Taming implies compatibility on four-manifolds, OpenAI Math Release, October 6, 2026, https://github.com/openai/math (result family 342; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Taming-implies-compatibility-on-four-manifolds-October-6-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit 7ef5c0c

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc031

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_HeatFlow_HodgeResolvent
attribute [-instance] _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.frameMap_apply _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDifferential_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap_zero _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth _root_.OAI.TamingCompatibility.HodgeNormalSymbol.symbolMap_apply _root_.OAI.TamingCompatibility.HodgeStarGeometry.starMap_apply _root_.OAI.TamingCompatibility.HodgeStarGeometry.swapMap_apply
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

lemma hodge_resolvent_distribution (p : A.centers) (τ : 𝓢(Space,ℝ))
    {U : Set Space} (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    (a : Fin 4 → 𝓢(Space,HodgeNormalSymbol.W →L[ℝ] HodgeNormalSymbol.Q))
    (b : 𝓢(Space,HodgeNormalSymbol.W →L[ℝ] HodgeNormalSymbol.Q)) (ρ : 𝓢(Space,ℝ))
    (ha : ∀ z ∈ U, ∀ i, a i z = normalA J α ht p.val (D p).toData i z)
    (hb : ∀ z ∈ U, b z = normalB J α ht p.val (D p).toData z)
    (hρ : ∀ z ∈ U, ρ z = chartDensity J α p.val z)
    (r : ℝ) (hr : 0 < r) (f : hodgeEnergy A J α hs ht)
    (χ : 𝓢(Space,ℂ)) (hc : HasCompactSupport (χ : Space → ℂ)) (hχU : tsupport χ ⊆ U) :
    smulLeftCLM (C 6) χ (fullShiftedSquare a b ρ
      (((r^2)⁻¹:ℂ) • SchwartzMap.postcompCLM Complex.ofRealCLM ρ)
      (hodgeRawDistribution A J α hs ht D hD p τ
        (hodgeWeakSolution A J α hs ht r hr (hodgeInclusion A J α hs ht f)))) =
    smulLeftCLM (C 6) χ (((r^2)⁻¹:ℂ) •
      smulLeftCLM (C 6) (SchwartzMap.postcompCLM Complex.ofRealCLM ρ)
        (hodgeRawDistribution A J α hs ht D hD p τ f)) := by
  apply localize_eq_of_real_tests _ χ hc hχU
  intro φ hφ hφU
  ext j
  let v := hodgeTest A J α hs ht D p (componentTest j φ)
    (full_componentTest_compact j φ hφ) ((full_componentTest_support j φ).trans (hφU.trans hUD))
  let u := hodgeWeakSolution A J α hs ht r hr (hodgeInclusion A J α hs ht f)
  have h := hodgeWeakSolution_identity A J α hs ht r hr (hodgeInclusion A J α hs ht f)
    (hodgeSmooth A J α hs ht v)
  rw [hodgeResolvent_eq A J α hs ht r hr,ContinuousLinearMap.comp_apply] at h
  have he : ⟪hodgeWeakDerivative A J α hs ht u,
      hodgeWeakDerivative A J α hs ht (hodgeSmooth A J α hs ht v)⟫ +
      (r^2)⁻¹*⟪hodgeInclusion A J α hs ht u,
        hodgeInclusion A J α hs ht (hodgeSmooth A J α hs ht v)⟫ =
      (r^2)⁻¹*⟪hodgeInclusion A J α hs ht f,
        hodgeInclusion A J α hs ht (hodgeSmooth A J α hs ht v)⟫ := by
    have hr2 : r^2 ≠ 0 := pow_ne_zero 2 hr.ne'
    field_simp
    nlinarith only [h]
  simp only [fullShiftedSquare,_root_.add_apply,PiLp.add_apply,
    FunLike.coe_smul,smulLeftCLM_smul (SchwartzMap.postcompCLM Complex.ofRealCLM ρ).hasTemperateGrowth,
    _root_.smul_apply,PiLp.smul_apply,smul_eq_mul]
  rw [hodge_raw_square_energy A J α hs ht D hD p τ hU hUD hτ a b ρ ha hb hρ φ hφ hφU j,
    hodge_raw_weighted_pair A J α hs ht D hD p τ ρ hUD hτ hρ φ hφ hφU j,
    hodge_raw_weighted_pair A J α hs ht D hD p τ ρ hUD hτ hρ φ hφ hφU j]
  exact_mod_cast he
end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end


