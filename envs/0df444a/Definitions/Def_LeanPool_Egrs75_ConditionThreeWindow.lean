-- Prove2me | Definitions.Def_LeanPool_Egrs75_ConditionThreeWindow
-- name    : LeanPool_Egrs75_ConditionThreeWindow
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T17:26:58.283538+00:00
-- url     : https://prove2.me/theorems/e5a3a61b-78c0-4c4a-bfc8-cf1c49e2b107
-- title:
--   Condition Three Window
-- statement:
--   Definitions and structural lemmas for Condition Three Window, from Egor Lyfar; LeanPool contributors's pinned The EGRS two-prime theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/ConditionThreeWindow.lean

module
public import Definitions.Def_LeanPool_Egrs75_DigitVector
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Ring.GeomSum
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace Egrs75.P4
open Nat
open Finset
open Egrs75
open Egrs75.LeafInduction
open Egrs75.RepairDV
def geomQ (q i : ℕ) : ℕ := ∑ k ∈ Finset.range i, q ^ k
def StrictGoodAt (q i n : ℕ) : Prop := n / q ^ i % q < (q - 1) / 2
instance (q i n : ℕ) : Decidable (StrictGoodAt q i n) := by
  unfold StrictGoodAt; infer_instance
theorem exists_strictGood_above {q n : ℕ} (hq : 3 ≤ q) (_hbad : 0 < badCountQ q n) :
    ∃ i, topBadIndex q n < i ∧ StrictGoodAt q i n := by
  set j := topBadIndex q n with hj
  set L := (Nat.digits q n).length with hL
  refine ⟨max (j + 1) L, by omega, ?_⟩
  unfold StrictGoodAt
  set i := max (j + 1) L with hi
  have hge : L ≤ i := by omega
  -- n / q^i = 0 since q^i ≥ q^L > n
  have hqL : n < q ^ L := Nat.lt_base_pow_length_digits (by omega)
  have hqi : n < q ^ i := lt_of_lt_of_le hqL (Nat.pow_le_pow_right (by omega) hge)
  have hd0 : n / q ^ i = 0 := Nat.div_eq_of_lt hqi
  rw [hd0]; simp only [Nat.zero_mod]
  omega
noncomputable def leastGoodAbove {q n : ℕ} (hq : 3 ≤ q) (hbad : 0 < badCountQ q n) : ℕ :=
  Nat.find (exists_strictGood_above hq hbad)
def tailLB (q n j t : ℕ) : ℕ :=
  (n / q ^ j % q) * q ^ j + ((q - 1) / 2) * ∑ s ∈ Finset.Ico (j + 1) t, q ^ s
end Egrs75.P4


