-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterOverSubfieldOfRepresentation
-- name    : Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterOverSubfieldOfRepresentation
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:49:23.836788+00:00
-- url     : https://prove2.me/theorems/1932675b-db29-4c35-a6de-5644b9c0ba49
-- title:
--   Is Character Over Subfield Of Representation
-- statement:
--   Definitions and structural lemmas for Is Character Over Subfield Of Representation, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/IsCharacterOverSubfieldOfRepresentation.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.BI
noncomputable section
namespace GlobalTheory.BI
section
variable {K G V W : Type} [Field K] [Group G] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
def transportRep (ρ : Representation K G V) (e : V ≃ₗ[K] W) : Representation K G W where
  toFun g := e.conj (ρ g)
  map_one' := by ext w; simp
  map_mul' a b := by ext w; simp
theorem transportRep_apply (ρ : Representation K G V) (e : V ≃ₗ[K] W) (g : G) (w : W) :
    transportRep ρ e g w = e (ρ g (e.symm w)) := rfl
def transportSubOrderIso (ρ : Representation K G V) (e : V ≃ₗ[K] W) :
    Subrepresentation (transportRep ρ e) ≃o Subrepresentation ρ where
  toFun S := ⟨S.toSubmodule.comap e.toLinearMap, fun g v hv => by
    have := S.apply_mem_toSubmodule g (v := e v) hv
    simpa [transportRep_apply] using this⟩
  invFun S := ⟨S.toSubmodule.comap e.symm.toLinearMap, fun g w hw => by
    have := S.apply_mem_toSubmodule g (v := e.symm w) hw
    simpa [transportRep_apply] using this⟩
  left_inv S := by ext w; simp
  right_inv S := by ext v; simp
  map_rel_iff' {S T} := by
    constructor
    · intro h w hw
      have h1 : e.symm w ∈ S.toSubmodule.comap e.toLinearMap := by
        show e (e.symm w) ∈ S.toSubmodule
        rw [e.apply_symm_apply]; exact hw
      have h2 : e (e.symm w) ∈ T.toSubmodule := h h1
      rw [e.apply_symm_apply] at h2
      exact h2
    · intro h v hv
      exact h (show e v ∈ S from hv)
end
end GlobalTheory.BI


