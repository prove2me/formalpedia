-- Prove2me | Definitions.Def_CSL_Sorting_Local_Columnsort_ColumnsortExchange
-- name    : CSL_Sorting_Local_Columnsort_ColumnsortExchange
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T13:08:31.574146+00:00
-- url     : https://prove2.me/theorems/60390201-f2c6-40a0-a6f9-e8045b4dca62
-- title:
--   Coded sorting library: Sorting / Local / Columnsort / ColumnsortExchange
-- statement:
--   Module `CodedSorting.Sorting.Local.Columnsort.ColumnsortExchange` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   The six address exchanges in Proposition 6.1.  This file connects the
--   actual cyclic transpose to three adjacent field exchanges and its inverse.
--   It establishes value movement, not the I/O cost of the interchange primitive.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Sorting.Local.Columnsort.ColumnsortExchange

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Sorting_Local_Columnsort_FiniteColumnsort
import Definitions.Def_CSL_Shared_Memory_Address

/-! The six address exchanges in Proposition 6.1.  This file connects the
actual cyclic transpose to three adjacent field exchanges and its inverse.
It establishes value movement, not the I/O cost of the interchange primitive. -/
namespace CSL.ColumnsortExchange

open CSL.Columnsort CSL.RecursiveColumnsort

abbrev Fields (s : ℕ) := Fin s × (Fin s × (Fin s × Fin s))

/-- Four consecutive base-s fields, most significant first. -/
def encode (s : ℕ) : Fields s ≃ Fin (s^4) :=
  ((Equiv.prodCongr (Equiv.refl (Fin s))
    ((Equiv.prodCongr (Equiv.refl (Fin s)) finProdFinEquiv).trans finProdFinEquiv)).trans
    finProdFinEquiv).trans (finCongr (by ring))

theorem encode_val (s : ℕ) (x : Fields s) :
    (encode s x).val = ((x.1.val*s+x.2.1.val)*s+x.2.2.1.val)*s+x.2.2.2.val := by
  change x.2.2.2.val+s*x.2.2.1.val+(s*s)*x.2.1.val+(s*(s*s))*x.1.val = _
  ring

def swap34 (s : ℕ) : Fields s ≃ Fields s where
  toFun x := (x.1,x.2.1,x.2.2.2,x.2.2.1)
  invFun x := (x.1,x.2.1,x.2.2.2,x.2.2.1)
  left_inv _ := rfl
  right_inv _ := rfl

def swap23 (s : ℕ) : Fields s ≃ Fields s where
  toFun x := (x.1,x.2.2.1,x.2.1,x.2.2.2)
  invFun x := (x.1,x.2.2.1,x.2.1,x.2.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

def swap12 (s : ℕ) : Fields s ≃ Fields s where
  toFun x := (x.2.1,x.1,x.2.2.1,x.2.2.2)
  invFun x := (x.2.1,x.1,x.2.2.1,x.2.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The three swaps in the exact order used for Step 2. -/
def forward (s : ℕ) : Fields s ≃ Fields s :=
  ((swap34 s).trans (swap23 s)).trans (swap12 s)

/-- Step 4 reverses the order of these same three swaps. -/
def backward (s : ℕ) : Fields s ≃ Fields s :=
  ((swap12 s).trans (swap23 s)).trans (swap34 s)

theorem forward_apply (s : ℕ) (x : Fields s) :
    forward s x = (x.2.2.2,x.1,x.2.1,x.2.2.1) := rfl

theorem backward_apply (s : ℕ) (x : Fields s) :
    backward s x = (x.2.1,x.2.2.1,x.2.2.2,x.1) := rfl

theorem backward_eq_symm (s : ℕ) : backward s = (forward s).symm := by
  apply Equiv.ext
  intro x
  rfl

/-- This is exactly the destination index π from the manuscript. -/
theorem forward_flat_index (s : ℕ) (hs : 0 < s) (x : Fields s) :
    (encode s (forward s x)).val = (encode s x).val % s * s^3 + (encode s x).val / s := by
  rw [encode_val, encode_val]
  have hlast := x.2.2.2.isLt
  have hmod : (((x.1.val*s+x.2.1.val)*s+x.2.2.1.val)*s+x.2.2.2.val) % s =
      x.2.2.2.val := by
    rw [Nat.mul_comm _ s, Nat.mul_add_mod, Nat.mod_eq_of_lt hlast]
  have hdiv : (((x.1.val*s+x.2.1.val)*s+x.2.2.1.val)*s+x.2.2.2.val) / s =
      (x.1.val*s+x.2.1.val)*s+x.2.2.1.val := by
    rw [Nat.mul_comm _ s, Nat.mul_add_div hs, Nat.div_eq_of_lt hlast, Nat.add_zero]
  rw [hmod,hdiv]
  change ((x.2.2.2.val*s+x.1.val)*s+x.2.1.val)*s+x.2.2.1.val = _
  ring

/-- Finite-index implementation, so the forward map covers every position. -/
def transpose (s : ℕ) : Fin (s^4) ≃ Fin (s^4) :=
  ((encode s).symm.trans (forward s)).trans (encode s)

theorem transpose_val (s : ℕ) (hs : 0 < s) (j : Fin (s^4)) :
    (transpose s j).val = j.val%s*s^3+j.val/s := by
  have h := forward_flat_index s hs ((encode s).symm j)
  simpa only [transpose, Equiv.trans_apply, Equiv.apply_symm_apply] using h

/-- Full streams keep the within-record coordinate, regardless of its size. -/
def forwardRecord (s : ℕ) (Suffix : Type*) : Fields s × Suffix ≃ Fields s × Suffix :=
  Equiv.prodCongr (forward s) (Equiv.refl Suffix)

theorem forwardRecord_apply (s : ℕ) {Suffix : Type*} (x : Fields s) (z : Suffix) :
    forwardRecord s Suffix (x,z) = ((x.2.2.2,x.1,x.2.1,x.2.2.1),z) := rfl

/-- The three individual moves are precisely the Section 5 full-address
exchange, with the unused field gap empty and every spectator retained. -/
theorem swap34_is_exchange (s : ℕ) {Suffix : Type*} (x : Fields s) (z : Suffix) :
    CSL.Address.exchange
      (CSL.Address.FullAddress.mk (x.1,x.2.1) x.2.2.1 () x.2.2.2 z) =
    CSL.Address.FullAddress.mk ((swap34 s x).1,(swap34 s x).2.1)
      (swap34 s x).2.2.1 () (swap34 s x).2.2.2 z := rfl

theorem swap23_is_exchange (s : ℕ) {Suffix : Type*} (x : Fields s) (z : Suffix) :
    CSL.Address.exchange
      (CSL.Address.FullAddress.mk x.1 x.2.1 () x.2.2.1 (x.2.2.2,z)) =
    CSL.Address.FullAddress.mk (swap23 s x).1 (swap23 s x).2.1 ()
      (swap23 s x).2.2.1 ((swap23 s x).2.2.2,z) := rfl

theorem swap12_is_exchange (s : ℕ) {Suffix : Type*} (x : Fields s) (z : Suffix) :
    CSL.Address.exchange
      (CSL.Address.FullAddress.mk () x.1 () x.2.1 (x.2.2.1,x.2.2.2,z)) =
    CSL.Address.FullAddress.mk () (swap12 s x).1 () (swap12 s x).2.1
      ((swap12 s x).2.2.1,(swap12 s x).2.2.2,z) := rfl

/-- Relate the explicit field rotation to the actual finite second-batch
source layout: row k in new column c comes from old column a, row k*s+c. -/
theorem secondInput_source {α : Type*} (q s : ℕ) (one : Fin s → Fin (q*s*1) → α)
    (a : Fin s) (k : Fin (q*1)) (c : Fin s) :
    secondInput q s one c (finProdFinEquiv (a,k)) =
      one a ⟨k.val*s+c.val, by
        have hk := k.isLt
        have hc := c.isLt
        simp only [Nat.mul_one] at hk ⊢
        nlinarith⟩ := by
  unfold secondInput
  simp only [Equiv.symm_apply_apply]
  apply congrArg (one a)
  apply Fin.ext
  simp only [stripeIndex, Nat.div_one, Nat.mod_one, Nat.mul_one, Nat.add_zero]

/-- At the exact source position read by secondInput, the three-field-swap
implementation writes to that same batch's column-major destination. -/
theorem transpose_secondInput_destination (s : ℕ) (hs : 0 < s)
    (a k c : ℕ) (hc : c < s) (j : Fin (s^4))
    (hj : j.val = a*(s^2*s)+k*s+c) :
    (transpose s j).val = c*s^3+a*s^2+k := by
  rw [transpose_val s hs, hj]
  have h := groupTranspose_flat_index (s^2) s a k c hs hc
  have hpow : s^3 = s^2*s := by ring
  simpa only [hpow] using h

/-- Actual stream transport moves a complete record to the cyclically
rotated address and keeps its suffix and value unchanged. -/
theorem forward_stream_payload (s : ℕ) {Suffix Value : Type*}
    (F : Fields s × Suffix → Value) (x : Fields s) (z : Suffix) :
    CSL.Address.transport (forwardRecord s Suffix) F
      ((x.2.2.2,x.1,x.2.1,x.2.2.1),z) = F (x,z) :=
  CSL.Address.transport_at_destination (forwardRecord s Suffix) F (x,z)

end CSL.ColumnsortExchange


