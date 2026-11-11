-- Prove2me | Definitions.Def_OAIQ239Tc035
-- name    : OAIQ239Tc035
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T00:47:35.189198+00:00
-- url     : https://prove2.me/theorems/232ecdb3-d637-4015-8ccd-24a0b9e7447d
-- title:
--   Definitions bundle OAIQ239Tc035 of the split of OpenAI, Taming implies compatibility on four-manifolds
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.TamingCompatibility.taming_implies_compatibility`, carved from OpenAI's openai/math development (OpenAI, *Taming implies compatibility on four-manifolds*, OpenAI Math Release, October 6, 2026, result family 342, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 theorem.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: [`TamingCompatibility_Hodge_HodgeRawRegular`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Hodge/HodgeRawRegular.lean).
--
--   **Imports.** It imports the published bundle `Def_TamingCompatibility`; the bundle `OAIQ239Tc037` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ239Tc032`.
-- source:
--   OpenAI, Taming implies compatibility on four-manifolds, OpenAI Math Release, October 6, 2026, https://github.com/openai/math (result family 342; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Taming-implies-compatibility-on-four-manifolds-October-6-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit 7ef5c0c

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc037

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

lemma hodge_resolvent_raw_gain (p : A.centers) (τ : 𝓢(Space,ℝ))
    {U : Set Space} (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    (q : Space) (hq : q ∈ U) (r : ℝ) (hr : 0 < r) :
    ∃ V : Set Space, IsOpen V ∧ q ∈ V ∧ V ⊆ U ∧
      ∀ (n : ℕ) (f : hodgeEnergy A J α hs ht),
      MemSobolevLoc U n (hodgeRawDistribution A J α hs ht D hD p τ f) →
      MemSobolevLoc V ((n:ℝ)+2) (hodgeRawDistribution A J α hs ht D hD p τ
        (hodgeWeakSolution A J α hs ht r hr (hodgeInclusion A J α hs ht f))) := by
  obtain ⟨φ,hφ,hφU,W,hW,hqW,hWU,hφone⟩ := SchwartzCutoff.exists_one_near hU hq
  have hφD := hφU.trans hUD
  let a := patchA J α ht p.val (D p).toData (φ.smooth ⊤) hφ hφD
  let b := patchB J α hs ht p.val (D p).toData (φ.smooth ⊤) hφ hφD
  let ρ : 𝓢(Space,ℝ) := SchwartzCutoff.schwartz (D p).domain_open
    ((chartDensity_smooth J α hs ht p.val).mono (D p).domain_subset) (φ.smooth ⊤) hφ hφD
  have ha : ∀ z ∈ W, ∀ i, a i z = normalA J α ht p.val (D p).toData i z := by
    intro z hz i
    simp only [a,patchA,SchwartzCutoff.schwartz_apply,hφone z hz,one_smul]
  have hb : ∀ z ∈ W, b z = normalB J α ht p.val (D p).toData z := by
    intro z hz
    simp only [b,patchB,SchwartzCutoff.schwartz_apply,hφone z hz,one_smul]
  have hρ : ∀ z ∈ W, ρ z = chartDensity J α p.val z := by
    intro z hz
    simp only [ρ,SchwartzCutoff.schwartz_apply,hφone z hz,one_smul]
  let ζ := ((r^2)⁻¹:ℂ) • SchwartzMap.postcompCLM Complex.ofRealCLM ρ
  let G := fun i j z => ρ z*φ z*φ z*GeometricChart.normalMetric J α ht p.val (D p).toData i j z
  have hG : ∀ i j, G i j q = chartDensity J α p.val q * ∑ t, (D p).frame t q i * (D p).frame t q j := by
    intro i j
    simp only [G,hρ q hqW,hφone q hqW,one_mul,GeometricChart.normalMetric,
      LocalMatrixOperator.frameCovector,EuclideanSpace.inner_eq_star_dotProduct,dotProduct,
      star_trivial,mul_comm]
  obtain ⟨V,hV,hqV,hVW,hall⟩ := full_shifted_square_uniform_regular hW q hqW
    (coordinateMetric J α ht p.val q) (fun i => (D p).frame i q)
    ((D p).frame_gram q (hUD hq)) a b ρ ζ G
    (patchA_polarized J α ht p.val (D p).toData (φ.smooth ⊤) hφ hφD ρ)
    (chartDensity J α p.val q) (chartDensity_pos J α ht p.val ((D p).domain_subset (hUD hq))) hG
  refine ⟨V,hV,hqV,hVW.trans hWU,fun n f hf => ?_⟩
  apply hall n _
    (memSobolevLoc_one_of_global (hodgeRawDistribution_H1 A J α hs ht D hD p τ _) W)
  intro χ hc hχW
  rw [hodge_resolvent_distribution A J α hs ht D hD p τ hW (hWU.trans hUD)
    (fun z hz => hτ z (hWU hz)) a b ρ ha hb hρ r hr f χ hc hχW]
  rw [map_smul,coefficient_products_commute]
  exact MemSobolev.smul _ (EuclideanSobolevOperators.memSobolev_nat_product n _
    (hf χ hc (hχW.trans hWU)))
end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end


