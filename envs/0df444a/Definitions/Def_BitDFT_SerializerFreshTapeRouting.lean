-- Prove2me | Definitions.Def_BitDFT_SerializerFreshTapeRouting
-- name    : BitDFT_SerializerFreshTapeRouting
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-25T06:31:51.950714+00:00
-- url     : https://prove2.me/theorems/46400ec5-86e0-445c-94e0-2ae1ad994570
-- title:
--   Route serializer work onto appended tapes while preserving caller tapes
-- statement:
--   For any nonnegative integer r, rotate the serializer's enlarged tape bank while fixing its input tape and product-source tape. Logical serializer tapes 2, 3, and 4 are sent to physical tapes r+2, r+3, and r+4, respectively; all remaining logical tapes are permuted among the old work tapes. This reserves three appended physical tapes for output, countdown, and template while preserving the prior caller and bank contents.
-- source:
--   A cyclic permutation on the tail of the finite tape index set, represented through the additive group of a finite cyclic ring. The fixed first two positions are the read-only input and product source.

import Definitions.Def_BitDFT_TapePermutation
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

set_option autoImplicit false
namespace BitDFT.SerializerFreshTapeRouting
open IntMul

/-- Split the serializer's enlarged tape bank into the fixed input/source pair
    and the rotating tail that holds caller tapes plus fresh work tapes. -/
def splitIndex (r : ℕ) (i : Fin (5+r)) : Fin 2 ⊕ Fin (3+r) :=
  if h : i.val < 2 then .inl ⟨i.val,h⟩ else .inr ⟨i.val-2,by have := i.isLt; omega⟩

def joinIndex (r : ℕ) : Fin 2 ⊕ Fin (3+r) → Fin (5+r)
  | .inl i => ⟨i.val,by have := i.isLt; omega⟩
  | .inr i => ⟨i.val+2,by have := i.isLt; omega⟩

theorem join_split (r : ℕ) (i : Fin (5+r)) :
    joinIndex r (splitIndex r i) = i := by
  apply Fin.ext
  by_cases h : i.val < 2
  · simp [splitIndex,joinIndex,h]
  · simp [splitIndex,joinIndex,h]
    omega

theorem split_join (r : ℕ) (i : Fin 2 ⊕ Fin (3+r)) :
    splitIndex r (joinIndex r i) = i := by
  cases i with
  | inl i =>
      change splitIndex r (⟨i.val, by omega⟩ : Fin (5+r)) = .inl i
      have hi : i.val < 2 := i.isLt
      simp [splitIndex,hi]
  | inr i =>
      change splitIndex r ⟨i.val+2, by omega⟩ = .inr i
      simp [splitIndex]

noncomputable def splitEquiv (r : ℕ) : Fin (5+r) ≃ (Fin 2 ⊕ Fin (3+r)) :=
  Equiv.ofBijective (splitIndex r) ⟨
    (fun a b h => by
      have := congrArg (joinIndex r) h
      simpa only [split_join, join_split] using this),
    (fun i => ⟨joinIndex r i, split_join r i⟩)⟩

/-- Rotate only the non-input tail. Rotation by `r` sends logical serializer
    tapes 2, 3, and 4 to the three appended physical tapes. -/
def rotateTail (r : ℕ) : Fin (3+r) ≃ Fin (3+r) := by
  let e : Fin (3+r) ≃+* ZMod (3+r) := ZMod.finEquiv (3+r)
  exact Equiv.trans e.toEquiv
    (Equiv.trans (Equiv.addRight (e ⟨r,by omega⟩)) e.toEquiv.symm)

noncomputable def routing (r : ℕ) : Fin (5+r) ≃ Fin (5+r) :=
  (splitEquiv r).trans
    ((Equiv.sumCongr (Equiv.refl (Fin 2)) (rotateTail r)).trans (splitEquiv r).symm)

theorem routing_input (r : ℕ) : routing r ⟨0,by omega⟩ = ⟨0,by omega⟩ := by
  apply (splitEquiv r).injective
  simp only [routing, Equiv.trans_apply, Equiv.apply_symm_apply]
  change Sum.map id (rotateTail r) (splitIndex r ⟨0,by omega⟩) =
    splitIndex r ⟨0,by omega⟩
  simp [splitIndex]

theorem routing_product (r : ℕ) :
    routing r ⟨1,by omega⟩ = ⟨1,by omega⟩ := by
  apply (splitEquiv r).injective
  simp only [routing, Equiv.trans_apply, Equiv.apply_symm_apply]
  change Sum.map id (rotateTail r) (splitIndex r ⟨1,by omega⟩) =
    splitIndex r ⟨1,by omega⟩
  simp [splitIndex]

theorem routing_output (r : ℕ) :
    routing r ⟨2,by omega⟩ = ⟨r+2,by omega⟩ := by
  apply (splitEquiv r).injective
  simp only [routing, Equiv.trans_apply, Equiv.apply_symm_apply]
  change Sum.map id (rotateTail r) (splitIndex r ⟨2,by omega⟩) =
    splitIndex r ⟨r+2,by omega⟩
  simp [splitIndex,rotateTail]

theorem routing_countdown (r : ℕ) :
    routing r ⟨3,by omega⟩ = ⟨r+3,by omega⟩ := by
  apply (splitEquiv r).injective
  simp only [routing, Equiv.trans_apply, Equiv.apply_symm_apply]
  change Sum.map id (rotateTail r) (splitIndex r ⟨3,by omega⟩) =
    splitIndex r ⟨r+3,by omega⟩
  simp [splitIndex,rotateTail]
  apply Fin.ext
  simp [rotateTail]
  rw [Fin.val_add]
  rw [Nat.mod_eq_of_lt (show 1+r < 3+r by omega)]
  omega

theorem routing_template (r : ℕ) :
    routing r ⟨4,by omega⟩ = ⟨r+4,by omega⟩ := by
  apply (splitEquiv r).injective
  simp only [routing, Equiv.trans_apply, Equiv.apply_symm_apply]
  change Sum.map id (rotateTail r) (splitIndex r ⟨4,by omega⟩) =
    splitIndex r ⟨r+4,by omega⟩
  simp [splitIndex,rotateTail]
  apply Fin.ext
  simp [rotateTail]
  rw [Fin.val_add]
  rw [Nat.mod_eq_of_lt (show 2+r < 3+r by omega)]
  omega

end BitDFT.SerializerFreshTapeRouting


