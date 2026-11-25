-- Prove2me | Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_IsUnramifiedOutsideIffLeMaxUnramifiedOutside
-- name    : GroundTheory_ProfiniteCohomology_RestrictedRamification_IsUnramifiedOutsideIffLeMaxUnramifiedOutside
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T02:12:06.017109+00:00
-- url     : https://prove2.me/theorems/d16ac4ee-a140-45c4-af5e-11eb82f7ea59
-- title:
--   Is Unramified Outside Iff Le Max Unramified Outside
-- statement:
--   Definitions and structural lemmas for Is Unramified Outside Iff Le Max Unramified Outside, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/RestrictedRamification/IsUnramifiedOutsideIffLeMaxUnramifiedOutside.lean

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_GaloisModules_Discrete
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_Unramified
import Theorems.Thm_GroundTheory_ProfCoh_IsUnramifiedOutside_map
import Theorems.Thm_GroundTheory_ProfCoh_IsUnramifiedOutside_sup
import Theorems.Thm_GroundTheory_ProfCoh_isUnramifiedOutside_bot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.ProfCoh
open NumberField IsDedekindDomain
variable {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω]
section Basic
variable (S : Set (HeightOneSpectrum (𝓞 F)))
theorem le_maxUnramifiedOutside {E : IntermediateField F Ω} [FiniteDimensional F E]
    (hE : IsUnramifiedOutside S E) : E ≤ maxUnramifiedOutside F Ω S :=
  le_iSup_of_le E (le_iSup_of_le ‹_› (le_iSup_of_le hE le_rfl))
theorem maxUnramifiedOutside_eq_iSup :
    maxUnramifiedOutside F Ω S =
      ⨆ E : {E : IntermediateField F Ω // FiniteDimensional F E ∧ IsUnramifiedOutside S E}, E.1 := by
  apply le_antisymm
  · exact iSup_le fun E => iSup_le fun hf => iSup_le fun hu => le_iSup_of_le ⟨E, hf, hu⟩ le_rfl
  · exact iSup_le fun E => have := E.2.1; le_maxUnramifiedOutside S E.2.2
variable [NumberField F] [IsGalois F Ω]
theorem mem_maxUnramifiedOutside_iff {x : Ω} :
    x ∈ maxUnramifiedOutside F Ω S ↔
      ∃ E : IntermediateField F Ω, FiniteDimensional F E ∧ IsUnramifiedOutside S E ∧ x ∈ E := by
  constructor
  · intro hx
    have hne : Nonempty {E : IntermediateField F Ω // FiniteDimensional F E ∧
        IsUnramifiedOutside S E} := ⟨⟨⊥, inferInstance, isUnramifiedOutside_bot S⟩⟩
    have hdir : Directed (· ≤ ·) (fun E : {E : IntermediateField F Ω // FiniteDimensional F E ∧
        IsUnramifiedOutside S E} => E.1) := by
      intro E₁ E₂
      have := E₁.2.1
      have := E₂.2.1
      exact ⟨⟨E₁.1 ⊔ E₂.1, inferInstance, E₁.2.2.sup E₂.2.2⟩, le_sup_left, le_sup_right⟩
    rw [maxUnramifiedOutside_eq_iSup, ← SetLike.mem_coe,
      IntermediateField.coe_iSup_of_directed hdir, Set.mem_iUnion] at hx
    obtain ⟨E, hE⟩ := hx
    exact ⟨E.1, E.2.1, E.2.2, hE⟩
  · rintro ⟨E, hf, hu, hx⟩
    exact le_maxUnramifiedOutside S hu hx
instance isGalois_maxUnramifiedOutside : IsGalois F (maxUnramifiedOutside F Ω S) := by
  have hN : Normal F (maxUnramifiedOutside F Ω S) := by
    rw [IntermediateField.normal_iff_forall_map_le']
    intro τ x hx
    obtain ⟨y, hy, rfl⟩ := (IntermediateField.mem_map _).1 hx
    obtain ⟨E, hf, hu, hyE⟩ := (mem_maxUnramifiedOutside_iff S).1 hy
    have : FiniteDimensional F (E.map (τ : Ω →ₐ[F] Ω)) :=
      LinearEquiv.finiteDimensional (IntermediateField.equivMap E (τ : Ω →ₐ[F] Ω)).toLinearEquiv
    exact le_maxUnramifiedOutside S (hu.map τ) ((IntermediateField.mem_map _).2 ⟨y, hyE, rfl⟩)
  exact ⟨⟩
end Basic
section Relative
variable [NumberField F] (S : Set (HeightOneSpectrum (𝓞 F)))
variable [IsGalois F Ω]
end Relative
end GroundTheory.ProfCoh


