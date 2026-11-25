-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SignedLengthOfCommonLower
-- name    : Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SignedLengthOfCommonLower
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T23:53:55.038422+00:00
-- url     : https://prove2.me/theorems/fa19d06e-8c80-4a22-a259-578122a625ee
-- title:
--   Signed Length Of Common Lower
-- statement:
--   Definitions and structural lemmas for Signed Length Of Common Lower, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SignedLengthOfCommonLower.lean

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_LengthCommensurableMapIffOfInjective
import Theorems.Thm_GlobalTheory_relLength_map_mkQ
import Theorems.Thm_GlobalTheory_relLength_submoduleOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2
namespace GlobalTheory.RelativeLengthAdditivity
open GlobalTheory
section
variable {S : Type u_1} {V : Type u_2} [Ring S] [AddCommGroup V] [Module S V]
theorem relLength_bot_add {A D : Submodule S V} (h : D ≤ A) :
    relLength A ⊥ = relLength A D + relLength D ⊥ := by
  let N : Submodule S A := D.submoduleOf A
  have hex := Module.length_eq_add_of_exact N.subtype N.mkQ N.injective_subtype N.mkQ_surjective
    (LinearMap.exact_subtype_mkQ N)
  have hN : Module.length S N = relLength D ⊥ := by
    have := relLength_submoduleOf h (⊥ : Submodule S V)
    have hb : (⊥ : Submodule S V).submoduleOf A = ⊥ := by
      ext x; simp [Submodule.submoduleOf]
    rw [hb, relLength_bot_right] at this
    exact this
  rw [relLength_bot_right, hex, hN, add_comm]
  rfl
theorem relLength_add {A C D : Submodule S V} (hCD : C ≤ D) (hDA : D ≤ A) :
    relLength A C = relLength A D + relLength D C := by
  have hb : C.map C.mkQ = ⊥ := Submodule.mkQ_map_self C
  rw [← relLength_map_mkQ le_rfl A, ← relLength_map_mkQ hCD A, ← relLength_map_mkQ le_rfl D, hb]
  exact relLength_bot_add (Submodule.map_mono hDA)
theorem signedLength_of_common_lower : ∀ {S : Type u_1} {V : Type u_2} [inst : Ring S] [inst_1 : AddCommGroup V]
    [inst_2 : Module S V] {A B C : Submodule S V}, C ≤ A → C ≤ B → ∀ {m n : ℕ},
    GlobalTheory.relLength A C = (↑m : ℕ∞) → GlobalTheory.relLength B C = (↑n : ℕ∞) →
    GlobalTheory.LengthCommensurable A B ∧ GlobalTheory.signedLength A B = (↑m : ℤ) - (↑n : ℤ) := by
  intro S V _ _ _ A B C hCA hCB m n hm hn
  have hCD : C ≤ A ⊓ B := le_inf hCA hCB
  have h1 := relLength_add hCD (inf_le_left : A ⊓ B ≤ A)
  have h2 := relLength_add hCD (inf_le_right : A ⊓ B ≤ B)
  rw [relLength_inf_right] at h1
  rw [relLength_inf_right'] at h2
  rw [hm] at h1
  rw [hn] at h2
  have ha : relLength A B ≠ ⊤ := fun h => by simp [h] at h1
  have hb : relLength B A ≠ ⊤ := fun h => by simp [h] at h2
  have hk : relLength (A ⊓ B) C ≠ ⊤ := fun h => by simp [h] at h1
  refine ⟨⟨ha, hb⟩, ?_⟩
  obtain ⟨a, ha'⟩ := ENat.ne_top_iff_exists.mp ha
  obtain ⟨b, hb'⟩ := ENat.ne_top_iff_exists.mp hb
  obtain ⟨k, hk'⟩ := ENat.ne_top_iff_exists.mp hk
  rw [← ha', ← hk'] at h1
  rw [← hb', ← hk'] at h2
  have e1 : m = a + k := by exact_mod_cast h1
  have e2 : n = b + k := by exact_mod_cast h2
  rw [signedLength_eq_of_relLength_eq ha'.symm hb'.symm, e1, e2]
  push_cast
  ring
end
end GlobalTheory.RelativeLengthAdditivity
example : ∀ {S : Type u_1} {V : Type u_2} [inst : Ring S] [inst_1 : AddCommGroup V] [inst_2 : Module S V] {A B C : Submodule S V}, C ≤ A → C ≤ B → ∀ {m n : ℕ}, GlobalTheory.relLength A C = (↑m : ℕ∞) → GlobalTheory.relLength B C = (↑n : ℕ∞) → GlobalTheory.LengthCommensurable A B ∧ GlobalTheory.signedLength A B = (↑m : ℤ) - (↑n : ℤ) := @GlobalTheory.RelativeLengthAdditivity.signedLength_of_common_lower


