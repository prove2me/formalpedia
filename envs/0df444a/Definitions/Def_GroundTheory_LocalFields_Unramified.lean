-- Prove2me | Definitions.Def_GroundTheory_LocalFields_Unramified
-- name    : GroundTheory_LocalFields_Unramified
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T05:09:36.703215+00:00
-- url     : https://prove2.me/theorems/4218b90e-8337-4c90-a4d1-1984ba104ba9
-- title:
--   Unramified
-- statement:
--   Definitions and structural lemmas for Unramified, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/Unramified.lean

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
import Definitions.Def_GroundTheory_LocalFields_IntermediateField
import Definitions.Def_GroundTheory_LocalFields_UnramifiedDefs
import Definitions.Def_GroundTheory_LocalFields_UnramifiedHensel
import Theorems.Thm_GroundTheory_LocalField_IsUnramified_residueDegree_eq_finrank
import Theorems.Thm_GroundTheory_LocalField_exists_unramified_adjoin
import Theorems.Thm_GroundTheory_LocalField_mem_of_residueDegree_eq_one
import Theorems.Thm_GroundTheory_LocalField_residueDegree_eq_finrank
import Theorems.Thm_GroundTheory_LocalField_residue_aeval

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel IsLocalRing Polynomial
open scoped _root_.IntermediateField
namespace GroundTheory.LocalField
section Generator
variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
theorem isUnit_aeval_derivative_of_separable (P : 𝒪[K][X])
    (hP : (P.map (residue 𝒪[K])).Separable) (x : 𝒪[L]) (hx : aeval x P = 0) :
    IsUnit (aeval x (derivative P)) := by
  rw [← residue_ne_zero_iff_isUnit, residue_aeval K L (fun _ ↦ rfl), ← derivative_map]
  refine hP.aeval_derivative_ne_zero ?_
  rw [← residue_aeval K L (fun _ ↦ rfl), hx, map_zero]
theorem IsUnramified.exists_generator [IsUnramified K L] :
    ∃ (β : 𝒪[L]) (P : 𝒪[K][X]), P.Monic ∧ aeval β P = 0 ∧ (P.map (residue 𝒪[K])).Separable ∧
      IsUnit (aeval β (derivative P)) ∧ K⟮(β : L)⟯ = ⊤ := by
  obtain ⟨β, P, hPm, hβ, hsep, -, hdeg, -⟩ := exists_unramified_adjoin K L
  refine ⟨β, P, hPm, hβ, hsep, isUnit_aeval_derivative_of_separable K L P hsep β hβ, ?_⟩
  refine IntermediateField.eq_of_le_of_finrank_eq le_top ?_
  rw [hdeg, IntermediateField.finrank_top', IsUnramified.residueDegree_eq_finrank K L]
end Generator
section Etale
variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
end Etale
section Maximal
variable (K L : Type*) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
  [Algebra K L] [ValuativeExtension K L]
def maximalUnramified : IntermediateField K L :=
  sSup {E : IntermediateField K L | IsUnramified K E}
variable [TopologicalSpace K] [IsNonarchimedeanLocalField K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [FiniteDimensional K L]
theorem exists_generator_of_isUnramified (E : IntermediateField K L) [IsUnramified K E] :
    ∃ (γ : 𝒪[L]) (P : 𝒪[K][X]), P.Monic ∧ aeval γ P = 0 ∧ IsUnit (aeval γ (derivative P)) ∧
      E = K⟮(γ : L)⟯ := by
  obtain ⟨β, P, hPm, hβ, -, hd, htop⟩ := IsUnramified.exists_generator K E
  refine ⟨algebraMap 𝒪[E] 𝒪[L] β, P, hPm, ?_, ?_, ?_⟩
  · rw [aeval_algebraMap_apply, hβ, map_zero]
  · rw [aeval_algebraMap_apply]
    exact hd.map _
  · have := congrArg (IntermediateField.map E.val) htop
    rw [IntermediateField.adjoin_map, Set.image_singleton, ← AlgHom.fieldRange_eq_map,
      IntermediateField.fieldRange_val] at this
    exact this.symm
theorem exists_maximalUnramified_eq :
    ∃ (β : 𝒪[L]) (P : 𝒪[K][X]), P.Monic ∧ aeval β P = 0 ∧ IsUnit (aeval β (derivative P)) ∧
      maximalUnramified K L = K⟮(β : L)⟯ ∧ IsUnramified K K⟮(β : L)⟯ ∧
      Module.finrank K K⟮(β : L)⟯ = residueDegree K L ∧ residueDegree K⟮(β : L)⟯ L = 1 := by
  obtain ⟨β, P, hPm, hβ, hsep, hunr, hdeg, h1⟩ := exists_unramified_adjoin K L
  refine ⟨β, P, hPm, hβ, isUnit_aeval_derivative_of_separable K L P hsep β hβ, ?_, hunr, hdeg, h1⟩
  refine le_antisymm (sSup_le fun E hE ↦ ?_) (le_sSup hunr)
  have : IsUnramified K E := hE
  obtain ⟨γ, Q, hQ, hγ, hd, hE'⟩ := exists_generator_of_isUnramified K L E
  rw [hE']
  exact IntermediateField.adjoin_simple_le_iff.2 (mem_of_residueDegree_eq_one K L _ h1 Q hQ γ hγ hd)
instance isUnramified_maximalUnramified : IsUnramified K (maximalUnramified K L) := by
  obtain ⟨β, P, -, -, -, heq, hunr, -, -⟩ := exists_maximalUnramified_eq K L
  rw [heq]
  exact hunr
end Maximal
section BaseChange
variable (K K' L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field K'] [ValuativeRel K'] [TopologicalSpace K']
  [IsNonarchimedeanLocalField K'] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K K'] [Algebra K' L] [Algebra K L] [IsScalarTower K K' L]
  [ValuativeExtension K K'] [ValuativeExtension K' L] [ValuativeExtension K L]
  [FiniteDimensional K L]
end BaseChange
section Galois
variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
def inertiaSubgroup : Subgroup (L ≃ₐ[K] L) := (residueAlgEquiv K L).ker
variable [IsGalois K L]
end Galois
end GroundTheory.LocalField


