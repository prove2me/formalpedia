-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_IsPrincipalIdealRingLoc
-- name    : Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_IsPrincipalIdealRingLoc
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T21:38:31.823186+00:00
-- url     : https://prove2.me/theorems/c91ad401-2427-43df-80ee-d820e3d3ec4c
-- title:
--   Is Principal Ideal Ring Loc
-- statement:
--   Definitions and structural lemmas for Is Principal Ideal Ring Loc, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/IsPrincipalIdealRingLoc.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.CoprimeBasisExistence
open NumberField nonZeroDivisors
def coprimeSet (A : Type*) [CommRing A] (m : ℕ) : Submonoid A where
  carrier := {x | ∃ k : ℕ, 0 < k ∧ k.Coprime m ∧ (k : A) = x}
  one_mem' := ⟨1, one_pos, by simp, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨a, ha, ha', rfl⟩ ⟨b, hb, hb', rfl⟩
    exact ⟨a * b, mul_pos ha hb, Nat.Coprime.mul_left ha' hb', by simp⟩
end GlobalTheory.CoprimeBasisExistence


