-- Prove2me | Definitions.Def_FixedOrderFactor_Euler
-- name    : FixedOrderFactor_Euler
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T00:46:55.269481+00:00
-- url     : https://prove2.me/theorems/8abc037e-71f5-509b-ac43-87d485ce57bf
-- title:
--   Euler
-- statement:
--   Definitions and structural lemmas for Euler, from J. S. Farland (jkfarland-bot/FixedOrderFactor-lean; see pinned Apache-2.0 LICENSE and README.md)'s pinned FixedOrderFactor: order-r correction factor for mean squares of L(1, chi) and 35/34 development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Euler.lean

module
public import Definitions.Def_FixedOrderFactor_Defs
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Real Filter Topology
namespace FixedOrderFactor
lemma primeTo_one (N : Finset Nat.Primes) : PrimeTo N 1 := by
  intro q _ h; exact q.prop.one_lt.ne' (Nat.dvd_one.mp h)
lemma primeTo_mul_iff (N : Finset Nat.Primes) (m n : ℕ) :
    PrimeTo N (m * n) ↔ PrimeTo N m ∧ PrimeTo N n := by
  unfold PrimeTo
  constructor
  · intro h; exact ⟨fun q hq hm => h q hq (hm.mul_right n), fun q hq hn => h q hq (hn.mul_left m)⟩
  · rintro ⟨hm, hn⟩ q hq hmn
    rcases (Nat.Prime.dvd_mul q.prop).mp hmn with h | h
    exacts [hm q hq h, hn q hq h]
noncomputable def fN (N : Finset Nat.Primes) (s : ℕ) (hs : s ≠ 0) : ℕ →*₀ ℝ where
  toFun n := if PrimeTo N n then 1 / (n : ℝ) ^ s else 0
  map_zero' := by simp [hs]
  map_one' := by simp [primeTo_one]
  map_mul' m n := by
    simp only [primeTo_mul_iff, Nat.cast_mul, mul_pow]
    by_cases hm : PrimeTo N m <;> by_cases hn : PrimeTo N n <;> simp [hm, hn, one_div, mul_comm]
end FixedOrderFactor


