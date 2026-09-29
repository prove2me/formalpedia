-- Prove2me | solution 1 for AutomorphicForm.ext_of_invariant_of_forall_glFin_eq_one_rat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/35a7777a-46aa-522c-8fa7-f8ca5c372484

import Definitions.Def_LanglandsTunnell_DeltaLift
import Definitions.Def_AdelicDock_LocalEmbedding
import Theorems.Thm_NumberField_AdelicLevel_exists_globalPoints_mul_mem_levelOne_rat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_ext_of_invariant_of_forall_glFin_eq_one_rat

set_option autoImplicit false

namespace ExtEngine

open NumberField NumberField.AdelicLevel AdelicDock AutomorphicForm IsDedekindDomain

private theorem isReal_rat_infinitePlace (v : InfinitePlace ℚ) : v.IsReal := IsTotallyReal.isReal v

private noncomputable def ratArchHom : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ) →* GL (Fin 2) ℝ :=
  (Matrix.GeneralLinearGroup.map
    (InfinitePlace.Completion.ringEquivRealOfIsReal (isReal_rat_infinitePlace default)).toRingHom).comp
    ((archComponent ℚ default).comp (glArch (𝓞 ℚ) ℚ))

private theorem ratArchHom_apply (g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) :
    ratArchHom g = LanglandsTunnell.ratArchGL2 g := rfl

private theorem ratArch_mul (g g' : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) :
    LanglandsTunnell.ratArchGL2 (g * g')
      = LanglandsTunnell.ratArchGL2 g * LanglandsTunnell.ratArchGL2 g' := by
  rw [← ratArchHom_apply, ← ratArchHom_apply, ← ratArchHom_apply, map_mul]

private theorem ratArch_inv (g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) :
    LanglandsTunnell.ratArchGL2 g⁻¹ = (LanglandsTunnell.ratArchGL2 g)⁻¹ := by
  rw [← ratArchHom_apply, ← ratArchHom_apply, map_inv]

private theorem ratArch_finEmbed (u : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
    LanglandsTunnell.ratArchGL2 (finEmbed (𝓞 ℚ) ℚ u) = 1 := by
  unfold LanglandsTunnell.ratArchGL2
  rw [glArch_finEmbed, map_one, map_one]

theorem exists_decomp {N : Ideal (𝓞 ℚ)} (hN : N ≠ ⊥) (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    ∃ (γ : GL (Fin 2) ℚ) (h : AdelicGL2 (𝓞 ℚ) ℚ) (u : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)),
      u ∈ finiteLevelOne (𝓞 ℚ) ℚ N ∧ glFin (𝓞 ℚ) ℚ h = 1 ∧
        LanglandsTunnell.ratArchGL2 h ∈ Matrix.GLPos (Fin 2) ℝ ∧
          globalPoints (𝓞 ℚ) ℚ γ * g = h * finEmbed (𝓞 ℚ) ℚ u := by
  obtain ⟨γ, hlev, hpos⟩ := NumberField.AdelicLevel.exists_globalPoints_mul_mem_levelOne_rat hN g
  set y : AdelicGL2 (𝓞 ℚ) ℚ := globalPoints (𝓞 ℚ) ℚ γ * g with hy
  refine ⟨γ, y * (finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ y))⁻¹, glFin (𝓞 ℚ) ℚ y, ?_, ?_, ?_, ?_⟩
  · exact (mem_levelOne_iff (R := 𝓞 ℚ) (K := ℚ) (N := N)).mp hlev
  · rw [map_mul, map_inv, glFin_finEmbed, mul_inv_cancel]
  · rw [ratArch_mul, ratArch_inv, ratArch_finEmbed, inv_one, mul_one]
    exact hpos default (isReal_rat_infinitePlace default)
  · rw [inv_mul_cancel_right]

end ExtEngine

open ExtEngine NumberField NumberField.AdelicLevel AdelicDock AutomorphicForm in
theorem solution
    {M : Type*} {N : Ideal (NumberField.RingOfIntegers ℚ)} (hN : N ≠ ⊥)
    {Ψ₁ Ψ₂ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → M}
    (h₁ : ∀ (γ : GL (Fin 2) ℚ) (x : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ),
      Ψ₁ (AutomorphicForm.globalPoints (NumberField.RingOfIntegers ℚ) ℚ γ * x) = Ψ₁ x)
    (h₂ : ∀ (γ : GL (Fin 2) ℚ) (x : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ),
      Ψ₂ (AutomorphicForm.globalPoints (NumberField.RingOfIntegers ℚ) ℚ γ * x) = Ψ₂ x)
    (h₁' : ∀ u ∈ NumberField.AdelicLevel.finiteLevelOne (NumberField.RingOfIntegers ℚ) ℚ N,
      ∀ x, Ψ₁ (x * AdelicDock.finEmbed (NumberField.RingOfIntegers ℚ) ℚ u) = Ψ₁ x)
    (h₂' : ∀ u ∈ NumberField.AdelicLevel.finiteLevelOne (NumberField.RingOfIntegers ℚ) ℚ N,
      ∀ x, Ψ₂ (x * AdelicDock.finEmbed (NumberField.RingOfIntegers ℚ) ℚ u) = Ψ₂ x)
    (heq : ∀ h : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ,
      NumberField.AdelicLevel.glFin (NumberField.RingOfIntegers ℚ) ℚ h = 1 →
        LanglandsTunnell.ratArchGL2 h ∈ Matrix.GLPos (Fin 2) ℝ → Ψ₁ h = Ψ₂ h) :
    Ψ₁ = Ψ₂ := by
  funext g
  obtain ⟨γ, h, u, hu, hfin, hpos, hdec⟩ := exists_decomp hN g
  rw [← h₁ γ g, ← h₂ γ g, hdec, h₁' u hu h, h₂' u hu h]
  exact heq h hfin hpos

end S_AutomorphicForm_ext_of_invariant_of_forall_glFin_eq_one_rat
end P2MW
export P2MW.S_AutomorphicForm_ext_of_invariant_of_forall_glFin_eq_one_rat (solution)
