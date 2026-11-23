-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_RootCharOfAddNatCast
-- name    : Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_RootCharOfAddNatCast
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T13:59:33.323333+00:00
-- url     : https://prove2.me/theorems/dae3c59f-1ce4-40e4-9e27-fe4858765aaf
-- title:
--   Root Char Of Add Nat Cast
-- statement:
--   Definitions and structural lemmas for Root Char Of Add Nat Cast, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/RootCharOfAddNatCast.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.RootCharacter
open scoped BigOperators
variable {B : Type*} [CommMonoid B] {I : Type*} [Fintype I] {n : ℕ} [NeZero n]
theorem pow_val_add {x : B} (hx : x ^ n = 1) (a b : ZMod n) :
    x ^ (a + b).val = x ^ a.val * x ^ b.val := by
  rw [ZMod.val_add, ← pow_add, ← pow_eq_pow_mod _ hx]
def rootChar (u : I → B) (hu : ∀ q, u q ^ n = 1) : Multiplicative (I → ZMod n) →* B where
  toFun a := ∏ q, u q ^ (Multiplicative.toAdd a q).val
  map_one' := by simp
  map_mul' a b := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun q _ => pow_val_add (hu q) _ _
end GlobalTheory.RootCharacter


