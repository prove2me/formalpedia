-- Prove2me | Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_MemZmultiplesOfAddOrderOf
-- name    : ReciprocityTheory_ClassFieldTheory_LocalClassField_MemZmultiplesOfAddOrderOf
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:08:09.484529+00:00
-- url     : https://prove2.me/theorems/1cfbc43f-43c9-4020-989b-30ac24dede17
-- title:
--   Mem Zmultiples Of Add Order Of
-- statement:
--   Definitions and structural lemmas for Mem Zmultiples Of Add Order Of, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/MemZmultiplesOfAddOrderOf.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_Duality
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1 Function
namespace RationalModIntegerChains
open scoped Nat
variable {A : Type} [AddCommGroup A]
section Chain
variable {C : Type} [AddCommGroup C]
theorem chain_shift (c : ℕ → C) (hc : ∀ n, (n + 1) • c (n + 1) = c n) (n d : ℕ) :
    ∃ e : ℕ, c n = e • c (n + d) := by
  induction d with
  | zero => exact ⟨1, by simp⟩
  | succ d ih =>
    obtain ⟨e, he⟩ := ih
    refine ⟨e * (n + d + 1), ?_⟩
    rw [mul_nsmul', ← add_assoc, hc, ← he]
def chainSub (c : ℕ → C) (hc : ∀ n, (n + 1) • c (n + 1) = c n) : AddSubgroup C where
  carrier := {x | ∃ (n : ℕ) (k : ℤ), x = k • c n}
  zero_mem' := ⟨0, 0, by simp⟩
  add_mem' := by
    rintro _ _ ⟨n, k, rfl⟩ ⟨m, l, rfl⟩
    obtain ⟨e, he⟩ := chain_shift c hc n m
    obtain ⟨f, hf⟩ := chain_shift c hc m n
    refine ⟨n + m, k * e + l * f, ?_⟩
    rw [add_comm m n] at hf
    rw [add_zsmul, mul_zsmul, mul_zsmul, natCast_zsmul, natCast_zsmul, ← he, ← hf]
  neg_mem' := by
    rintro _ ⟨n, k, rfl⟩
    exact ⟨n, -k, by simp⟩
end Chain
noncomputable def qzc (n : ℕ) : QZ := QuotientAddGroup.mk (1 / (n ! : ℚ))
end RationalModIntegerChains
end ReciprocityTheory.DiscreteGroups.LocalClassField


