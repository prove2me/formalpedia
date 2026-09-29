-- Prove2me | solution 1 for AutomorphicForm.CuspidalConstituent.cuspKFiniteSubmodule_le_cuspKFiniteSubmodule_of_le_of_exists_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/660a0063-9bf0-5901-9745-658020c7af9e

import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Theorems.Thm_AutomorphicForm_norm_apply_archCentralUnit_lt_one_of_memLp_of_coversModCentre
import Theorems.Thm_AutomorphicForm_memLp_iUnion_centreCutSiegelSet_of_detWindow_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_CuspidalConstituent_cuspKFiniteSubmodule_le_cuspKFiniteSubmodule_of_le_of_exists_ne_zero

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent
open NumberField.SiegelVolume
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

theorem solution
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ d₁' : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hc : 0 < c) (hle : d₁ ≤ d₁') (hd₁' : 0 < d₁') (hlt : d₁' < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (ξ : (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).Z →* ℂˣ)
    (hne : ∃ φ : AdelicGL2 (𝓞 F) F → ℂ, IsAutomorphicFnAt F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ φ ∧ Continuous φ ∧ φ ≠ 0) :
    cuspKFiniteSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁' d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ ≤ cuspKFiniteSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ := by
  refine Submodule.span_le.mpr ?_
  rintro ψ ⟨hsat, hcont, htys⟩
  apply Submodule.subset_span

  obtain ⟨φ₀, hφ₀A, hφ₀c, hφ₀ne⟩ := hne
  have hA0 := (lsXiMemberAt_iff (𝓞 F) F (adelicGLHaar (Fin 2) (𝓞 F) F) ⊤ ξ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) φ₀).mp hφ₀A
  let ω : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ :=
    ξ.comp (Subgroup.topEquiv : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) ≃* (AdeleRing (𝓞 F) F)ˣ).symm.toMonoidHom
  have hω0 : ∀ (z : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F),
      φ₀ (centralScalar (𝓞 F) F z * g) = ((ω z : ℂˣ) : ℂ) * φ₀ g :=
    fun z g => hA0.1.central_transform ⟨z, Subgroup.mem_top z⟩ g
  have hd₂ : 0 < d₂ := hd₁'.trans hlt
  have hcontr : d₁ ≤ 0 → ∀ (w : InfinitePlace F) (a : (w.Completion)ˣ), ‖(a : w.Completion)‖ < 1 →
      ‖((ω (AdelicVolume.archCentralUnit F w a) : ℂˣ) : ℂ)‖ < 1 :=
    fun hd₁ w a ha =>
      AutomorphicForm.norm_apply_archCentralUnit_lt_one_of_memLp_of_coversModCentre F c u d₁ d₂ T hd₁ hd₂ hcov
        φ₀ hφ₀c (Function.ne_iff.mp hφ₀ne) hA0.1.left_invariant ω hω0 hA0.2 w a ha
  refine ⟨fun g => ?_, hcont, htys⟩

  have hg := hsat g
  have hA := (lsXiMemberAt_iff (𝓞 F) F (adelicGLHaar (Fin 2) (𝓞 F) F) ⊤ ξ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁' d₂) (rightTranslate F g ψ)).mp
    (show IsAutomorphicFnAt F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁' d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ (rightTranslate F g ψ) from hg.1.1)
  have hωψ : ∀ (z : (AdeleRing (𝓞 F) F)ˣ) (x : AdelicGL2 (𝓞 F) F),
      rightTranslate F g ψ (centralScalar (𝓞 F) F z * x) = ((ω z : ℂˣ) : ℂ) * rightTranslate F g ψ x :=
    fun z x => hA.1.central_transform ⟨z, Subgroup.mem_top z⟩ x
  have hMem : MemLp (rightTranslate F g ψ) 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)) :=
    AutomorphicForm.memLp_iUnion_centreCutSiegelSet_of_detWindow_le F c u d₁ d₂ d₁' T hd₁' hlt hle (rightTranslate F g ψ)
      (continuous_rightTranslate F hcont g).aestronglyMeasurable ω hωψ hcontr hA.2
  exact ⟨⟨(lsXiMemberAt_iff (𝓞 F) F (adelicGLHaar (Fin 2) (𝓞 F) F) ⊤ ξ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) (rightTranslate F g ψ)).mpr ⟨hA.1, hMem⟩,
      hg.1.2⟩, hg.2⟩

#print axioms solution

end S_AutomorphicForm_CuspidalConstituent_cuspKFiniteSubmodule_le_cuspKFiniteSubmodule_of_le_of_exists_ne_zero
end P2MW
export P2MW.S_AutomorphicForm_CuspidalConstituent_cuspKFiniteSubmodule_le_cuspKFiniteSubmodule_of_le_of_exists_ne_zero (solution)
