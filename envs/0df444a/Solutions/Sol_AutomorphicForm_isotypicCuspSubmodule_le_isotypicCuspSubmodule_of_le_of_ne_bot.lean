-- Prove2me | solution 1 for AutomorphicForm.isotypicCuspSubmodule_le_isotypicCuspSubmodule_of_le_of_ne_bot
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/a191ba81-d905-5321-87ab-6f1987d2ba71

import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Theorems.Thm_AutomorphicForm_norm_apply_archCentralUnit_lt_one_of_memLp_of_coversModCentre
import Theorems.Thm_AutomorphicForm_memLp_iUnion_centreCutSiegelSet_of_detWindow_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_isotypicCuspSubmodule_le_isotypicCuspSubmodule_of_le_of_ne_bot

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open NumberField.SiegelVolume
open AutomorphicForm.CuspidalConstituent
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

theorem solution
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ d₁' : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hc : 0 < c) (hle : d₁ ≤ d₁') (hd₁' : 0 < d₁') (hlt : d₁' < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (ξ : (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).Z →* ℂˣ)
    (N : Ideal (𝓞 F)) (S : Finset (HeightOneSpectrum (𝓞 F))) (Ψ : HeckeEigensystem F ℂ)
    (hne : isotypicCuspSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ N S Ψ ≠ ⊥) :
    isotypicCuspSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁' d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ N S Ψ ≤
      isotypicCuspSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ N S Ψ := by
  refine Submodule.span_le.mpr ?_
  intro ψ hψ
  apply Submodule.subset_span

  obtain ⟨φ₀, hφ₀, hφ₀ne⟩ := (isotypicCuspSubmodule_ne_bot_iff F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ N S Ψ).mp hne
  have hA0 := (lsXiMemberAt_iff (𝓞 F) F (adelicGLHaar (Fin 2) (𝓞 F) F) ⊤ ξ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) φ₀).mp hφ₀.smoothCusp.1.1
  have hA := (lsXiMemberAt_iff (𝓞 F) F (adelicGLHaar (Fin 2) (𝓞 F) F) ⊤ ξ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁' d₂) ψ).mp
    (show IsAutomorphicFnAt F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁' d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ ψ from hψ.smoothCusp.1.1)

  let ω : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ :=
    ξ.comp (Subgroup.topEquiv : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) ≃* (AdeleRing (𝓞 F) F)ˣ).symm.toMonoidHom
  have hω0 : ∀ (z : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F),
      φ₀ (centralScalar (𝓞 F) F z * g) = ((ω z : ℂˣ) : ℂ) * φ₀ g :=
    fun z g => hA0.1.central_transform ⟨z, Subgroup.mem_top z⟩ g
  have hωψ : ∀ (z : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F),
      ψ (centralScalar (𝓞 F) F z * g) = ((ω z : ℂˣ) : ℂ) * ψ g :=
    fun z g => hA.1.central_transform ⟨z, Subgroup.mem_top z⟩ g
  have hd₂ : 0 < d₂ := hd₁'.trans hlt
  have hcontr : d₁ ≤ 0 → ∀ (w : InfinitePlace F) (a : (w.Completion)ˣ), ‖(a : w.Completion)‖ < 1 →
      ‖((ω (AdelicVolume.archCentralUnit F w a) : ℂˣ) : ℂ)‖ < 1 :=
    fun hd₁ w a ha =>
      AutomorphicForm.norm_apply_archCentralUnit_lt_one_of_memLp_of_coversModCentre F c u d₁ d₂ T hd₁ hd₂ hcov
        φ₀ hφ₀.continuous (Function.ne_iff.mp hφ₀ne) hA0.1.left_invariant ω hω0 hA0.2 w a ha
  have hMem : MemLp ψ 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)) :=
    AutomorphicForm.memLp_iUnion_centreCutSiegelSet_of_detWindow_le F c u d₁ d₂ d₁' T hd₁' hlt hle ψ
      hψ.continuous.aestronglyMeasurable ω hωψ hcontr hA.2
  exact ⟨⟨⟨(lsXiMemberAt_iff (𝓞 F) F (adelicGLHaar (Fin 2) (𝓞 F) F) ⊤ ξ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) ψ).mpr ⟨hA.1, hMem⟩,
      hψ.smoothCusp.1.2⟩, hψ.smoothCusp.2⟩, hψ.continuous, hψ.level_invariant, hψ.hecke_eigen, hψ.central_eigen⟩

#print axioms solution

end S_AutomorphicForm_isotypicCuspSubmodule_le_isotypicCuspSubmodule_of_le_of_ne_bot
end P2MW
export P2MW.S_AutomorphicForm_isotypicCuspSubmodule_le_isotypicCuspSubmodule_of_le_of_ne_bot (solution)
