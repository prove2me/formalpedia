-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MemSaturationOfPowSmulMem
-- name    : Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MemSaturationOfPowSmulMem
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T09:58:53.613862+00:00
-- url     : https://prove2.me/theorems/8dcc9aa2-cfbd-448c-8eb3-312d0af0736b
-- title:
--   Mem Saturation Of Pow Smul Mem
-- statement:
--   Definitions and structural lemmas for Mem Saturation Of Pow Smul Mem, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MemSaturationOfPowSmulMem.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.SubmoduleSaturation
variable {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M]
def saturation (g : A) (K : Submodule A M) : Submodule A M where
  carrier := {m | ∃ k : ℕ, g ^ k • m ∈ K}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro a b ⟨k, hk⟩ ⟨l, hl⟩
    refine ⟨k + l, ?_⟩
    rw [smul_add]
    refine K.add_mem ?_ ?_
    · rw [add_comm, pow_add, mul_smul]
      exact K.smul_mem _ hk
    · rw [pow_add, mul_smul]
      exact K.smul_mem _ hl
  smul_mem' := by
    rintro c a ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [smul_comm]
    exact K.smul_mem _ hk
end GlobalTheory.SubmoduleSaturation


