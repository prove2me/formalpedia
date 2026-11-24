-- Prove2me | Definitions.Def_KirkmanLib_Instances
-- name    : KirkmanLib_Instances
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T05:42:11.359955+00:00
-- url     : https://prove2.me/theorems/ec6082a5-e823-44f6-b902-56dee2c526e2
-- title:
--   Instances
-- statement:
--   Definitions and structural lemmas for Instances, from Juan Pablo Traverso Gianini (jtraverso/kirkman-steiner-triple-systems; see pinned Apache-2.0 LICENSE and source headers)'s pinned Kirkman theorem on existence of Steiner triple systems development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/kirkman-steiner-triple-systems/blob/18551414d822f7fa4fb7535dc43733c4b316c3a8/KirkmanLib/Instances.lean

module
public import Mathlib
public import Definitions.Def_KirkmanLib_Constructions
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace Kirkman
section BoseQ
variable {n : ℕ} (hn : n % 2 = 1)
def half (n : ℕ) : ZMod n := (((n + 1) / 2 : ℕ) : ZMod n)
include hn in
lemma two_mul_half : 2 * half n = 1 := by
  unfold half
  have : 2 * ((n + 1) / 2) = n + 1 := by omega
  have h2 : ((2 * ((n + 1) / 2) : ℕ) : ZMod n) = 2 * (((n + 1) / 2 : ℕ) : ZMod n) := by
    push_cast; ring
  rw [← h2, this]
  push_cast
  rw [ZMod.natCast_self, zero_add]
def boseQ : CQ (ZMod n) where
  L x y := (x + y) * half n
  D x y := 2 * y - x
  comm x y := by ring
  LD x y := by linear_combination y * two_mul_half hn
  DL x y := by linear_combination (x + y) * two_mul_half hn
end BoseQ
section SkolemQ
lemma addv {t : ℕ} (a b : Fin (2 * t + 2)) :
    (a + b).val = if a.val + b.val < 2 * t + 2 then a.val + b.val
      else a.val + b.val - (2 * t + 2) := by
  rw [Fin.val_add]
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by have := a.isLt; have := b.isLt; omega)]
def sElt (t : ℕ) : Fin (2 * t + 2) := ⟨t + 1, by omega⟩
def gfun {t : ℕ} (r : Fin (2 * t + 2)) : Fin (2 * t + 2) :=
  if r.val % 2 = 0 then ⟨r.val / 2, by have := r.isLt; omega⟩
  else ⟨r.val / 2 + (t + 1), by have := r.isLt; omega⟩
def ginv {t : ℕ} (c : Fin (2 * t + 2)) : Fin (2 * t + 2) :=
  if h : c.val < t + 1 then ⟨2 * c.val, by omega⟩
  else ⟨2 * (c.val - (t + 1)) + 1, by have := c.isLt; omega⟩
lemma g_ginv {t : ℕ} (c : Fin (2 * t + 2)) : gfun (ginv c) = c := by
  unfold gfun ginv
  by_cases h : c.val < t + 1
  · rw [dif_pos h]
    apply Fin.ext
    rw [if_pos (by simp only; omega)]
    simp only; omega
  · rw [dif_neg h]
    apply Fin.ext
    rw [if_neg (by simp only; omega)]
    simp only; omega
lemma ginv_g {t : ℕ} (r : Fin (2 * t + 2)) : ginv (gfun r) = r := by
  unfold gfun ginv
  have := r.isLt
  by_cases h : r.val % 2 = 0
  · rw [if_pos h, dif_pos (by simp only; omega)]
    apply Fin.ext; simp only; omega
  · rw [if_neg h, dif_neg (by simp only; omega)]
    apply Fin.ext; simp only; omega
def skolemCQ (t : ℕ) : CQ (Fin (2 * t + 2)) where
  L x y := gfun (x + y)
  D x y := ginv y - x
  comm x y := by rw [add_comm x y]
  LD x y := by rw [add_sub_cancel, g_ginv]
  DL x y := by rw [ginv_g]; abel
lemma s_add_s {t : ℕ} : sElt t + sElt t = 0 := by
  apply Fin.ext
  rw [addv, Fin.val_zero]
  have h : (sElt t).val = t + 1 := rfl
  split <;> omega
def skolemQ (t : ℕ) : HalfIdem (Fin (2 * t + 2)) where
  toCQ := skolemCQ t
  τ x := x + sElt t
  H x := x.val < t + 1
  ττ x := by rw [add_assoc, s_add_s, add_zero]
  Hτ x := by
    rw [addv]
    have := x.isLt
    split_ifs <;> simp only [sElt] at * <;> omega
  Lτ x := by
    change gfun (x + sElt t + (x + sElt t)) = gfun (x + x)
    congr 1
    have : x + sElt t + (x + sElt t) = x + x + (sElt t + sElt t) := by abel
    rw [this, s_add_s, add_zero]
  LH x hx := by
    change gfun (x + x) = x
    have hx' : x.val < t + 1 := hx
    have hxx : (x + x).val = 2 * x.val := by
      rw [addv]; split_ifs <;> omega
    unfold gfun
    apply Fin.ext
    rw [if_pos (by rw [hxx]; omega)]
    simp only [hxx]; omega
end SkolemQ
end Kirkman


