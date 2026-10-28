-- Prove2me | Definitions.Def_BitDFT_DedicatedTapeBanks
-- name    : BitDFT_DedicatedTapeBanks
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-25T15:01:03.93818+00:00
-- url     : https://prove2.me/theorems/7b24a01e-6f98-45e9-a746-aedc8f483d58
-- title:
--   Disjoint tape-bank routing for a Fourier child, multiplier, and header reader
-- statement:
--   For three multitape machines sharing an input tape, reserve disjoint work-tape banks and fixed extra tapes for the Fourier child, multiplier, and header reader. The routing functions preserve the shared input address and map each component work tape to its designated host tape. The host width is the sum of component tape counts plus one.
-- source:
--   Exact tape-index arithmetic for the output-scaling host. It is built from the verified tape permutation and records the physical addresses used by subsequent staging proofs.

import Definitions.Def_BitDFT_TapePermutation
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

set_option autoImplicit false

noncomputable section
namespace BitDFT.DedicatedTapeBanks

/-- Host width for three machines with a shared read-only input tape, disjoint
    non-input tape banks, and three persistent scratch tapes. -/
abbrev tail (A M H : IntMul.MultitapeTM) := A.k + M.k + H.k - 4
abbrev width (A M H : IntMul.MultitapeTM) := 5 + tail A M H

def fourierOffset (_A M H : IntMul.MultitapeTM) : ℕ := 0
def multiplierOffset (A _M H : IntMul.MultitapeTM) : ℕ := A.k - 1
def headerOffset (A M _H : IntMul.MultitapeTM) : ℕ := A.k + M.k - 2

theorem width_eq_sum (A M H : IntMul.MultitapeTM) :
    width A M H = A.k + M.k + H.k + 1 := by
  dsimp [width, tail]
  have hA := A.two_le_k
  have hM := M.two_le_k
  have hH := H.two_le_k
  omega

def dimensionStore (A M H : IntMul.MultitapeTM) : Fin (width A M H) :=
  ⟨A.k + M.k + H.k - 2, by
    rw [width_eq_sum]
    have hA := A.two_le_k; have hM := M.two_le_k; have hH := H.two_le_k
    omega⟩
def coordinateStore (A M H : IntMul.MultitapeTM) : Fin (width A M H) :=
  ⟨A.k + M.k + H.k - 1, by
    rw [width_eq_sum]
    have hA := A.two_le_k; have hM := M.two_le_k; have hH := H.two_le_k
    omega⟩
def clockStore (A M H : IntMul.MultitapeTM) : Fin (width A M H) :=
  ⟨A.k + M.k + H.k, by
    rw [width_eq_sum]
    have hA := A.two_le_k; have hM := M.two_le_k; have hH := H.two_le_k
    omega⟩

theorem tail_ge_two (A M H : IntMul.MultitapeTM) : 2 ≤ tail A M H := by
  dsimp [tail]
  have hA := A.two_le_k
  have hM := M.two_le_k
  have hH := H.two_le_k
  omega

/-- Split off the common input tape so only work tapes are rotated. -/
def splitIndex (r : ℕ) (i : Fin (5 + r)) : Fin 1 ⊕ Fin (4 + r) :=
  if h : i.val < 1 then .inl ⟨i.val, h⟩ else .inr ⟨i.val - 1, by have := i.isLt; omega⟩

def joinIndex (r : ℕ) : Fin 1 ⊕ Fin (4 + r) → Fin (5 + r)
  | .inl i => ⟨i.val, by have := i.isLt; omega⟩
  | .inr i => ⟨i.val + 1, by have := i.isLt; omega⟩

theorem join_split (r : ℕ) (i : Fin (5 + r)) : joinIndex r (splitIndex r i) = i := by
  apply Fin.ext
  by_cases h : i.val < 1
  · simp [splitIndex, joinIndex, h]
  · simp [splitIndex, joinIndex, h]
    omega

theorem split_join (r : ℕ) (i : Fin 1 ⊕ Fin (4 + r)) :
    splitIndex r (joinIndex r i) = i := by
  cases i with
  | inl i =>
      cases i using Fin.cases <;> simp [splitIndex, joinIndex] <;> omega
  | inr i =>
      have hi : i.val + 1 ≥ 1 := by omega
      simp [splitIndex, joinIndex, hi]

noncomputable def splitEquiv (r : ℕ) : Fin (5+r) ≃ (Fin 1 ⊕ Fin (4+r)) :=
  Equiv.ofBijective (splitIndex r) ⟨
    (fun a b h => by
      have := congrArg (joinIndex r) h
      simpa only [split_join, join_split] using this),
    (fun i => ⟨joinIndex r i, split_join r i⟩)⟩

def rotateTail (r offset : ℕ) (hoff : offset < 4+r) : Fin (4+r) ≃ Fin (4+r) := by
  letI : NeZero (4+r) := ⟨by omega⟩
  let e : Fin (4+r) ≃+* ZMod (4+r) := ZMod.finEquiv (4+r)
  exact Equiv.trans e.toEquiv
    (Equiv.trans (Equiv.addRight (e ⟨offset, hoff⟩)) e.toEquiv.symm)

/-- A cyclic shift of non-input tapes, extended by the identity on tape zero. -/
def routing (r offset : ℕ) (hoff : offset < 4+r) : Fin (5+r) ≃ Fin (5+r) :=
  (splitEquiv r).trans
    ((Equiv.sumCongr (Equiv.refl (Fin 1)) (rotateTail r offset hoff)).trans
      (splitEquiv r).symm)

theorem routing_input (r offset : ℕ) (hoff : offset < 4+r) :
    routing r offset hoff ⟨0, by omega⟩ = ⟨0, by omega⟩ := by
  apply (splitEquiv r).injective
  simp only [routing, Equiv.trans_apply, Equiv.apply_symm_apply]
  change Sum.map id (rotateTail r offset hoff) (splitIndex r ⟨0, by omega⟩) =
    splitIndex r ⟨0, by omega⟩
  simp [splitIndex]

theorem routing_work (r offset : ℕ) (hoff : offset < 4+r)
    (j : Fin (5+r)) (hj : 1 ≤ j.val) (hend : offset + j.val < 5+r) :
    routing r offset hoff j = ⟨offset + j.val, hend⟩ := by
  apply (splitEquiv r).injective
  simp only [routing, Equiv.trans_apply, Equiv.apply_symm_apply]
  change Sum.map id (rotateTail r offset hoff) (splitIndex r j) =
    splitIndex r ⟨offset + j.val, hend⟩
  have hleft : ¬ j.val < 1 := by omega
  have hright : ¬ offset + j.val < 1 := by omega
  simp only [splitIndex, hleft, hright, dif_neg]
  apply congrArg Sum.inr
  apply Fin.ext
  have hmod : offset + (j.val - 1) < 4+r := by omega
  simp [rotateTail, Fin.val_add]
  change ((j.val - 1 + offset) % (4+r)) = offset + j.val - 1
  rw [Nat.add_comm (j.val - 1) offset, Nat.mod_eq_of_lt hmod]
  omega

theorem fourier_work_address (A M H : IntMul.MultitapeTM) (j : Fin A.k)
    (hj : 1 ≤ j.val) :
    routing (tail A M H) (fourierOffset A M H)
      (by have hA := A.two_le_k; have hM := M.two_le_k; have hH := H.two_le_k; dsimp [tail, fourierOffset]; omega)
      ⟨j.val, by have hA := A.two_le_k; have hM := M.two_le_k; have hH := H.two_le_k; dsimp [tail]; omega⟩ =
      ⟨j.val, by have hA := A.two_le_k; have hM := M.two_le_k; have hH := H.two_le_k; dsimp [tail]; omega⟩ := by
  have hoff : fourierOffset A M H < 4 + tail A M H := by
    dsimp [fourierOffset, tail]
    have hsum : 4 ≤ A.k + M.k + H.k := by have := A.two_le_k; have := M.two_le_k; have := H.two_le_k; omega
    omega
  have hend : fourierOffset A M H + j.val < 5 + tail A M H := by
    dsimp [fourierOffset, tail]
    have hA := A.two_le_k; have hM := M.two_le_k; have hH := H.two_le_k
    have hjk := j.isLt
    omega
  calc
    routing (tail A M H) (fourierOffset A M H) hoff
        ⟨j.val, by have hA := A.two_le_k; have hM := M.two_le_k; have hH := H.two_le_k; dsimp [tail]; omega⟩ =
      ⟨fourierOffset A M H + j.val, hend⟩ :=
        routing_work (tail A M H) (fourierOffset A M H) hoff
          ⟨j.val, by have hA := A.two_le_k; have hM := M.two_le_k; have hH := H.two_le_k; dsimp [tail]; omega⟩ hj hend
    _ = ⟨j.val, by have hA := A.two_le_k; have hM := M.two_le_k; have hH := H.two_le_k; dsimp [tail]; omega⟩ := by
      apply Fin.ext
      simp [fourierOffset]

theorem multiplier_work_address (A M H : IntMul.MultitapeTM) (j : Fin M.k)
    (hj : 1 ≤ j.val) :
    routing (tail A M H) (multiplierOffset A M H)
      (by have hA := A.two_le_k; have hM := M.two_le_k; have hH := H.two_le_k; dsimp [tail, multiplierOffset]; omega)
      ⟨j.val, by have hA := A.two_le_k; have hM := M.two_le_k; have hH := H.two_le_k; dsimp [tail]; omega⟩ =
      ⟨A.k + j.val - 1, by have hA := A.two_le_k; have hM := M.two_le_k; have hH := H.two_le_k; dsimp [tail]; omega⟩ := by
  have hoff : multiplierOffset A M H < 4 + tail A M H := by
    dsimp [multiplierOffset, tail]
    have hA := A.two_le_k; have hM := M.two_le_k; have hH := H.two_le_k
    omega
  have hend : multiplierOffset A M H + j.val < 5 + tail A M H := by
    dsimp [multiplierOffset, tail]
    have hA := A.two_le_k; have hM := M.two_le_k; have hH := H.two_le_k
    have hjk := j.isLt
    omega
  calc
    routing (tail A M H) (multiplierOffset A M H) hoff
        ⟨j.val, by have hA := A.two_le_k; have hM := M.two_le_k; have hH := H.two_le_k; dsimp [tail]; omega⟩ =
      ⟨multiplierOffset A M H + j.val, hend⟩ :=
        routing_work (tail A M H) (multiplierOffset A M H) hoff
          ⟨j.val, by have hA := A.two_le_k; have hM := M.two_le_k; have hH := H.two_le_k; dsimp [tail]; omega⟩ hj hend
    _ = ⟨A.k + j.val - 1, by have hA := A.two_le_k; have hM := M.two_le_k; have hH := H.two_le_k; dsimp [tail]; omega⟩ := by
      apply Fin.ext
      dsimp [multiplierOffset]
      have hA := A.two_le_k
      have hM := M.two_le_k
      have hH := H.two_le_k
      omega

theorem header_work_address (A M H : IntMul.MultitapeTM) (j : Fin H.k)
    (hj : 1 ≤ j.val) :
    routing (tail A M H) (headerOffset A M H)
      (by have hA := A.two_le_k; have hM := M.two_le_k; have hH := H.two_le_k; dsimp [tail, headerOffset]; omega)
      ⟨j.val, by have hA := A.two_le_k; have hM := M.two_le_k; have hH := H.two_le_k; dsimp [tail]; omega⟩ =
      ⟨A.k + M.k + j.val - 2, by have hA := A.two_le_k; have hM := M.two_le_k; have hH := H.two_le_k; dsimp [tail]; omega⟩ := by
  have hoff : headerOffset A M H < 4 + tail A M H := by
    dsimp [headerOffset, tail]
    have hA := A.two_le_k; have hM := M.two_le_k; have hH := H.two_le_k
    omega
  have hend : headerOffset A M H + j.val < 5 + tail A M H := by
    dsimp [headerOffset, tail]
    have hA := A.two_le_k; have hM := M.two_le_k; have hH := H.two_le_k
    have hjk := j.isLt
    omega
  calc
    routing (tail A M H) (headerOffset A M H) hoff
        ⟨j.val, by have hA := A.two_le_k; have hM := M.two_le_k; have hH := H.two_le_k; dsimp [tail]; omega⟩ =
      ⟨headerOffset A M H + j.val, hend⟩ :=
        routing_work (tail A M H) (headerOffset A M H) hoff
          ⟨j.val, by have hA := A.two_le_k; have hM := M.two_le_k; have hH := H.two_le_k; dsimp [tail]; omega⟩ hj hend
    _ = ⟨A.k + M.k + j.val - 2, by have hA := A.two_le_k; have hM := M.two_le_k; have hH := H.two_le_k; dsimp [tail]; omega⟩ := by
      apply Fin.ext
      dsimp [headerOffset]
      have hA := A.two_le_k
      have hM := M.two_le_k
      have hH := H.two_le_k
      omega

theorem header_value_tape_address (A M H : IntMul.MultitapeTM) :
    routing (tail A M H) (headerOffset A M H)
      (by have hA := A.two_le_k; have hM := M.two_le_k; have hH := H.two_le_k; dsimp [tail, headerOffset]; omega)
      ⟨3, by have hA := A.two_le_k; have hM := M.two_le_k; have hH := H.two_le_k; dsimp [tail]; omega⟩ =
    ⟨A.k + M.k + 1, by dsimp [tail]; have hA := A.two_le_k; have hM := M.two_le_k; have hH := H.two_le_k; omega⟩ := by
  have hj : 1 ≤ (3 : ℕ) := by omega
  have hend : headerOffset A M H + 3 < 5 + tail A M H := by
    dsimp [headerOffset, tail]
    have hA := A.two_le_k; have hM := M.two_le_k; have hH := H.two_le_k
    omega
  have hr := routing_work (tail A M H) (headerOffset A M H)
    (by dsimp [headerOffset, tail]; have hA := A.two_le_k; have hM := M.two_le_k; have hH := H.two_le_k; omega)
    ⟨3, by dsimp [tail]; have hA := A.two_le_k; have hM := M.two_le_k; have hH := H.two_le_k; omega⟩ hj hend
  rw [hr]
  apply Fin.ext
  dsimp [headerOffset]
  have hA := A.two_le_k
  have hM := M.two_le_k
  have hH := H.two_le_k
  omega

end BitDFT.DedicatedTapeBanks
end


