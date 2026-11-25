-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthCommensurableIffOfLeOfLe
-- name    : Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthCommensurableIffOfLeOfLe
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T23:53:53.850822+00:00
-- url     : https://prove2.me/theorems/ce749cfa-eaaa-4ce4-98c6-a4d922071352
-- title:
--   Length Commensurable Iff Of Le Of Le
-- statement:
--   Definitions and structural lemmas for Length Commensurable Iff Of Le Of Le, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/LengthCommensurableIffOfLeOfLe.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_LengthCommensurableMapIffOfInjective
import Theorems.Thm_GlobalTheory_relLength_submoduleOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory
variable {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]
section Chain
theorem relLength_eq_add_of_le {A B C : Submodule R V} (hCB : C ≤ B) (hBA : B ≤ A) :
    relLength A C = relLength A B + relLength B C := by
  have hle : C.submoduleOf A ≤ B.submoduleOf A := Submodule.comap_mono hCB
  have hex := Module.length_eq_add_of_exact (LinearMap.ker (Submodule.factor hle)).subtype
    (Submodule.factor hle) (Submodule.injective_subtype _) (Submodule.factor_surjective hle)
    (LinearMap.exact_subtype_ker_map _)
  have hker : LinearMap.ker (Submodule.factor hle) =
      (B.submoduleOf A).map (C.submoduleOf A).mkQ := by
    rw [Submodule.factor, Submodule.ker_mapQ, Submodule.comap_id]
  rw [hker, ← relLength_eq_length_map_mkQ, relLength_submoduleOf hBA] at hex
  rw [add_comm]
  exact hex
theorem relLength_inf_eq_add (A B C : Submodule R V) :
    relLength A (B ⊓ C) = relLength A B + relLength (A ⊓ B) C := by
  have h := relLength_eq_add_of_le (A := A) (B := A ⊓ B) (C := A ⊓ B ⊓ C) inf_le_left inf_le_left
  rwa [relLength_inf_right, relLength_inf_right, inf_assoc, relLength_inf_right] at h
theorem relLength_le_add (A B C : Submodule R V) :
    relLength A C ≤ relLength A B + relLength B C :=
  calc relLength A C ≤ relLength A (B ⊓ C) := relLength_anti_right A inf_le_right
    _ = relLength A B + relLength (A ⊓ B) C := relLength_inf_eq_add A B C
    _ ≤ relLength A B + relLength B C := by
      gcongr
      exact inf_le_right
theorem relLength_ne_top_trans {A B C : Submodule R V} (hAB : relLength A B ≠ ⊤)
    (hBC : relLength B C ≠ ⊤) : relLength A C ≠ ⊤ :=
  ne_top_of_le_ne_top (WithTop.add_ne_top.mpr ⟨hAB, hBC⟩) (relLength_le_add A B C)
end Chain
section Commensurable
variable {A A' B B' C : Submodule R V}
@[trans] theorem LengthCommensurable.trans (hAB : LengthCommensurable A B)
    (hBC : LengthCommensurable B C) : LengthCommensurable A C :=
  ⟨relLength_ne_top_trans hAB.1 hBC.1, relLength_ne_top_trans hBC.2 hAB.2⟩
instance : Trans (LengthCommensurable : Submodule R V → Submodule R V → Prop)
    LengthCommensurable LengthCommensurable :=
  ⟨LengthCommensurable.trans⟩
namespace LengthCommensurable
end LengthCommensurable
end Commensurable
end GlobalTheory


