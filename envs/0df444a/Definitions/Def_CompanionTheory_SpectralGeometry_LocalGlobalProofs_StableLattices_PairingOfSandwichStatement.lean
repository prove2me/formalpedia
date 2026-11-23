-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_PairingOfSandwichStatement
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_PairingOfSandwichStatement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T09:52:20.676266+00:00
-- url     : https://prove2.me/theorems/1b9196a2-0e99-4965-b1da-76a6a0b759c5
-- title:
--   Pairing Of Sandwich Statement
-- statement:
--   Definitions and structural lemmas for Pairing Of Sandwich Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/PairingOfSandwichStatement.lean

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Rg.FlB
noncomputable section
namespace GlobalTheory.CompanionTheory.HermLat
section Lat
variable {L : Type} [NontriviallyNormedField L] {V : Type} [AddCommGroup V] [Module L V]
variable (L) in

def adjoin [IsUltrametricDist L] (Λ : AddSubgroup V) (v : V) : AddSubgroup V where
  carrier := {z | ∃ l ∈ Λ, ∃ a : L, ‖a‖ ≤ 1 ∧ z = l + a • v}
  add_mem' := by
    rintro _ _ ⟨l, hl, a, ha, rfl⟩ ⟨l', hl', a', ha', rfl⟩
    refine ⟨l + l', Λ.add_mem hl hl', a + a',
      (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha ha'), ?_⟩
    rw [add_smul]
    abel
  zero_mem' := ⟨0, Λ.zero_mem, 0, by simp, by simp⟩
  neg_mem' := by
    rintro _ ⟨l, hl, a, ha, rfl⟩
    refine ⟨-l, Λ.neg_mem hl, -a, by simpa using ha, ?_⟩
    rw [neg_smul]
    abel
end Lat
section Herm
variable {L : Type} [NontriviallyNormedField L] {V : Type} [AddCommGroup V] [Module L V]
  {s : L →+* L} {h : V → V → L}
end Herm
section Main
variable {L : Type} [NontriviallyNormedField L] [IsUltrametricDist L] {V : Type} [AddCommGroup V]
  [Module L V] {s : L →+* L} {δ : L} {h : V → V → L}
end Main
end GlobalTheory.CompanionTheory.HermLat
end


