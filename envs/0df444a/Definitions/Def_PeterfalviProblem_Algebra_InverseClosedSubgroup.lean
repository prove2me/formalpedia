-- Prove2me | Definitions.Def_PeterfalviProblem_Algebra_InverseClosedSubgroup
-- name    : PeterfalviProblem_Algebra_InverseClosedSubgroup
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-27T04:56:01.206823+00:00
-- url     : https://prove2.me/theorems/1f95caa8-4b6f-555d-bd18-08aeaf41019d
-- title:
--   Inverse Closed Subgroup
-- statement:
--   Definitions and structural lemmas for Inverse Closed Subgroup, from Yawara Ishida (yawara/peterfalvi-problem; see pinned Apache-2.0 LICENSE and source headers)'s pinned Resolution of Péterfalvi problem for p = 3 and SL(2, 2^q) witness for p = 2 development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/yawara/peterfalvi-problem/blob/698b7ae0af649f7fad48c482aa8ff0d2d14336bb/PeterfalviProblem/Algebra/InverseClosedSubgroup.lean

import Mathlib.Algebra.Field.Subfield.Basic
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
set_option autoImplicit false
namespace PeterfalviProblem.InverseClosed
variable {F : Type*} [Field F]
theorem hua_identity {x y : F} (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x ≠ y) :
    x - (x⁻¹ + (y - x)⁻¹)⁻¹ = x ^ 2 / y := by
  have hyx : y - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hxy)
  have hval : x⁻¹ + (y - x)⁻¹ = y / (x * (y - x)) := by
    field_simp
    ring
  rw [hval, inv_div]
  field_simp
  ring
variable (W : AddSubgroup F)
theorem sq_div_mem (hinv : ∀ w ∈ W, w⁻¹ ∈ W) {x y : F} (hx : x ∈ W) (hy : y ∈ W) (hy0 : y ≠ 0) :
    x ^ 2 / y ∈ W := by
  rcases eq_or_ne x 0 with rfl | hx0
  · simp
  rcases eq_or_ne x y with rfl | hxy
  · rw [sq, mul_div_assoc, div_self hx0, mul_one]
    exact hx
  rw [← hua_identity hx0 hy0 hxy]
  exact W.sub_mem hx (hinv _ (W.add_mem (hinv _ hx) (hinv _ (W.sub_mem hy hx))))
theorem mul_sq_mem (hinv : ∀ w ∈ W, w⁻¹ ∈ W) {s v : F} (hs : s ∈ W) (hs0 : s ≠ 0)
    (hv : s * v ∈ W) : s * v ^ 2 ∈ W := by
  have key : (s * v) ^ 2 / s = s * v ^ 2 := by
    field_simp
  rw [← key]
  exact sq_div_mem W hinv hv hs hs0
theorem mul_mul_mem (hinv : ∀ w ∈ W, w⁻¹ ∈ W) (h3 : (3 : F) = 0) {s u v : F} (hs : s ∈ W)
    (hs0 : s ≠ 0) (hu : s * u ∈ W) (hv : s * v ∈ W) : s * (u * v) ∈ W := by
  have hsum : s * (u + v) ∈ W := by
    have : s * (u + v) = s * u + s * v := by ring
    rw [this]
    exact W.add_mem hu hv
  have key : s * (u * v) = s * u ^ 2 + s * v ^ 2 - s * (u + v) ^ 2 := by
    linear_combination (s * u * v) * h3
  rw [key]
  exact W.sub_mem (W.add_mem (mul_sq_mem W hinv hs hs0 hu) (mul_sq_mem W hinv hs hs0 hv))
    (mul_sq_mem W hinv hs hs0 hsum)
def scaledSubring (hinv : ∀ w ∈ W, w⁻¹ ∈ W) (h3 : (3 : F) = 0) {s : F} (hs : s ∈ W)
    (hs0 : s ≠ 0) : Subring F where
  carrier := {v | s * v ∈ W}
  zero_mem' := by
    change s * (0 : F) ∈ W
    simp
  one_mem' := by
    change s * (1 : F) ∈ W
    simpa using hs
  add_mem' := by
    intro u v hu hv
    change s * (u + v) ∈ W
    have h : s * (u + v) = s * u + s * v := by ring
    rw [h]
    exact W.add_mem hu hv
  neg_mem' := by
    intro u hu
    change s * (-u) ∈ W
    have h : s * (-u) = -(s * u) := by ring
    rw [h]
    exact W.neg_mem hu
  mul_mem' := fun hu hv => mul_mul_mem W hinv h3 hs hs0 hu hv
def scaledSubfield (hinv : ∀ w ∈ W, w⁻¹ ∈ W) (h3 : (3 : F) = 0) {s : F}
    (hs : s ∈ W) (hs0 : s ≠ 0) : Subfield F :=
  { scaledSubring W hinv h3 hs hs0 with
    inv_mem' := by
      intro v hv
      rcases eq_or_ne v 0 with rfl | hv0
      · change s * (0 : F)⁻¹ ∈ W
        simp
      change s * v⁻¹ ∈ W
      have hsv : s * v ∈ W := hv
      have key : s ^ 2 / (s * v) = s * v⁻¹ := by
        rw [sq, mul_div_mul_left _ _ hs0, div_eq_mul_inv]
      rw [← key]
      exact sq_div_mem W hinv hs hsv (mul_ne_zero hs0 hv0) }
section PrimeDegree
variable [Fintype F] {p q : ℕ} [Fact p.Prime] [CharP F p]
end PrimeDegree
end PeterfalviProblem.InverseClosed


