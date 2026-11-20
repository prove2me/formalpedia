-- Prove2me | Definitions.Def_BooleanFun_Arrow
-- name    : BooleanFun_Arrow
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T19:05:20.970243+00:00
-- url     : https://prove2.me/theorems/131056e1-8a65-480f-8edc-3714d5b13263
-- title:
--   Arrow
-- statement:
--   Definitions and structural lemmas for Arrow, from Joris Roos and contributors's pinned Boolean functions and Arrow’s theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/Arrow.lean

import Definitions.Def_BooleanFun_BooleanValued
set_option autoImplicit false
noncomputable section
namespace BooleanFun.BV
open Classical Mathlib Finset Pi RealInnerProductSpace
variable {α : Type*} {ι : Type*}
variable {n : ℕ}
variable {f : BooleanFunc n}
abbrev Votes n := Fin n → Fin 2
def majority : BooleanFunc n := fun x ↦ if ∑ j, (x j).val > n / 2 then 1 else -1
abbrev dictator {n : ℕ} (i : Fin n) : BooleanFunc n := χ {i}
abbrev NAE3 (x y z : α) : Prop := ¬ (x = y ∧ y = z)
def VoteConsistent (x y z : Votes n) : Prop :=
    ∀ i, NAE3 (x i) (y i) (z i)
def IsCondorcet (f : BooleanFunc n) : Prop :=
    ∀ x y z, VoteConsistent x y z → NAE3 (f x) (f y) (f z)
def HasDictator (f : BooleanFunc n) : Prop :=
    ∃ i, f = dictator i
def IsUnanimous (f : BooleanFunc n) : Prop := f 0 = 1 ∧ f 1 = -1
def probabilityCondorcetWinner (f : BooleanFunc n) : ℝ :=
    (1/6)^n * ∑ x, ∑ y, ∑ z, oneOn (NAE3 (f x) (f y) (f z))
      * oneOn (VoteConsistent x y z)
abbrev _Tnae3 : BooleanFunc n →ₗ[ℝ] BooleanFunc n := {
  toFun := fun f ↦
    fun x ↦ (1/3)^n * ∑ y, f y * ∑ z : Fin n → Fin 2, oneOn (VoteConsistent x y z)
  map_add' := by
    intro f g
    funext x
    simp only [one_div, inv_pow, Pi.add_apply, sum_boole]
    conv => enter [1, 2, 2, y]; rw [add_mul]
    rw [sum_add_distrib, mul_add]
  map_smul' := by
    intro c f
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    conv => enter [1, 2, 2, y]; rw [mul_assoc]
    rw [← mul_sum, ← mul_assoc, mul_comm _ c, mul_assoc]
}
local notation "T" => _Tnae3
end BooleanFun.BV


