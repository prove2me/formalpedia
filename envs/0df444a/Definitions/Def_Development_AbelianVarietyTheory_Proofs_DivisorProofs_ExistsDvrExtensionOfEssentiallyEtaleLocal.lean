-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDvrExtensionOfEssentiallyEtaleLocal
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDvrExtensionOfEssentiallyEtaleLocal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T22:48:09.824396+00:00
-- url     : https://prove2.me/theorems/cc656c8c-98bb-48b5-a2e1-c0c65a3da403
-- title:
--   Exists Dvr Extension Of Essentially Etale Local
-- statement:
--   Definitions and structural lemmas for Exists Dvr Extension Of Essentially Etale Local, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsDvrExtensionOfEssentiallyEtaleLocal.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct IsLocalRing
namespace GlobalTheory
def rangeValuationSubring {B L : Type} [CommRing B] [IsDomain B] [ValuationRing B] [Field L]
    (j : B →+* L) (hj : ∀ x : L, ∃ a b : B, j b ≠ 0 ∧ x = j a / j b) : ValuationSubring L where
  toSubring := j.range
  mem_or_inv_mem' x := by
    obtain ⟨a, b, hb, rfl⟩ := hj x
    obtain ⟨c, hc | hc⟩ := ValuationRing.cond a b
    · right
      have ha : j a ≠ 0 := fun h => hb (by rw [← hc, map_mul, h, zero_mul])
      exact ⟨c, by rw [inv_div, ← hc, map_mul, mul_div_cancel_left₀ _ ha]⟩
    · left
      exact ⟨c, by rw [← hc, map_mul, mul_div_cancel_left₀ _ hb]⟩
end GlobalTheory


