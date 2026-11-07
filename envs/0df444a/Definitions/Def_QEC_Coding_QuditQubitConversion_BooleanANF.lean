-- Prove2me | Definitions.Def_QEC_Coding_QuditQubitConversion_BooleanANF
-- name    : QEC_Coding_QuditQubitConversion_BooleanANF
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T11:08:57.7201+00:00
-- url     : https://prove2.me/theorems/929d8681-2685-4580-a237-2c49401a5a6b
-- title:
--   Boolean ANF
-- statement:
--   Definitions and structural lemmas for Boolean ANF, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/BooleanANF.lean

import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.FieldTheory.Finite.Basic
set_option autoImplicit false
noncomputable section
namespace QEC.Coding.Why24BooleanANF
open scoped BigOperators
structure Monomial (n : Nat) where
  support : Finset (Fin n)
  deriving DecidableEq
@[ext]
theorem Monomial.ext {n : Nat} {left right : Monomial n}
    (h : left.support = right.support) : left = right := by
  cases left
  cases right
  cases h
  rfl
instance (n : Nat) : One (Monomial n) :=
  ⟨⟨∅⟩⟩
instance (n : Nat) : Mul (Monomial n) :=
  ⟨fun left right => ⟨left.support ∪ right.support⟩⟩
@[simp]
theorem one_support (n : Nat) : (1 : Monomial n).support = ∅ :=
  rfl
@[simp]
theorem mul_support {n : Nat} (left right : Monomial n) :
    (left * right).support = left.support ∪ right.support :=
  rfl
instance (n : Nat) : CommMonoid (Monomial n) where
  mul_assoc left middle right := by
    apply Monomial.ext
    simp only [mul_support]
    exact Finset.union_assoc _ _ _
  one_mul monomial := by
    apply Monomial.ext
    simp only [mul_support, one_support]
    exact Finset.empty_union _
  mul_one monomial := by
    apply Monomial.ext
    simp only [mul_support, one_support]
    exact Finset.union_empty _
  mul_comm left right := by
    apply Monomial.ext
    simp only [mul_support]
    exact Finset.union_comm _ _
abbrev Polynomial (n : Nat) :=
  MonoidAlgebra (ZMod 2) (Monomial n)
def generator {n : Nat} (coordinate : Fin n) : Polynomial n :=
  MonoidAlgebra.single ⟨{coordinate}⟩ 1
theorem bit_mul_self (bit : ZMod 2) : bit * bit = bit := by
  simpa only [pow_two] using ZMod.pow_card bit
theorem supportValue_union {n : Nat}
    (word : Fin n → ZMod 2) (left right : Finset (Fin n)) :
    (∏ coordinate ∈ left, word coordinate) *
        ∏ coordinate ∈ right, word coordinate =
      ∏ coordinate ∈ left ∪ right, word coordinate := by
  classical
  have hinter : left ∩ right ⊆ left ∪ right := by
    intro coordinate hcoordinate
    exact Finset.mem_union_left _ (Finset.mem_of_mem_inter_left hcoordinate)
  calc
    (∏ coordinate ∈ left, word coordinate) *
        ∏ coordinate ∈ right, word coordinate =
        (∏ coordinate ∈ left ∪ right, word coordinate) *
          ∏ coordinate ∈ left ∩ right, word coordinate :=
      (Finset.prod_union_inter (f := word)).symm
    _ = ((∏ coordinate ∈ (left ∪ right) \ (left ∩ right), word coordinate) *
          ∏ coordinate ∈ left ∩ right, word coordinate) *
            ∏ coordinate ∈ left ∩ right, word coordinate := by
      rw [Finset.prod_sdiff hinter]
    _ = (∏ coordinate ∈ (left ∪ right) \ (left ∩ right), word coordinate) *
          ∏ coordinate ∈ left ∩ right, word coordinate := by
      rw [mul_assoc, show
        (∏ coordinate ∈ left ∩ right, word coordinate) *
            ∏ coordinate ∈ left ∩ right, word coordinate =
          ∏ coordinate ∈ left ∩ right, word coordinate by
        rw [← Finset.prod_mul_distrib]
        exact Finset.prod_congr rfl (fun coordinate _ => bit_mul_self (word coordinate))]
    _ = ∏ coordinate ∈ left ∪ right, word coordinate :=
      Finset.prod_sdiff hinter
def evaluateMonomial {n : Nat} (word : Fin n → ZMod 2) : Monomial n →* ZMod 2 where
  toFun monomial := ∏ coordinate ∈ monomial.support, word coordinate
  map_one' := by simp
  map_mul' left right := by
    simpa only [mul_support] using
      (supportValue_union word left.support right.support).symm
def evaluate {n : Nat} (word : Fin n → ZMod 2) :
    Polynomial n →ₐ[ZMod 2] ZMod 2 :=
  MonoidAlgebra.lift (ZMod 2) (ZMod 2) (Monomial n) (evaluateMonomial word)
end QEC.Coding.Why24BooleanANF


