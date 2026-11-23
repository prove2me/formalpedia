-- Prove2me | Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnitsHerbrandA
-- name    : ReciprocityTheory_ClassFieldTheory_LocalClassField_UnitsHerbrandA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:54:03.686913+00:00
-- url     : https://prove2.me/theorems/029dd4cd-ff38-4ab4-85a7-8dda8ae6cd99
-- title:
--   Units Herbrand A
-- statement:
--   Definitions and structural lemmas for Units Herbrand A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/UnitsHerbrandA.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.DiscreteGroups.LocalClassField.UnitsFilt
open Finset
section approx
variable {U : Type*} [CommGroup U]
end approx
variable {R : Type*} [Field R] (G : Type*) [Group G] [Fintype G] [MulSemiringAction G R]
structure Filt (I : ℕ → AddSubgroup R) (e : R →+ R) : Prop where
  anti : ∀ n, I (n + 1) ≤ I n
  mul : ∀ n x y, x ∈ I n → y ∈ I 0 → x * y ∈ I (n + 1)
  smul : ∀ n (g : G) x, x ∈ I n → g • x ∈ I n
  comp : ∀ x : ℕ → R, (∀ k, x k ∈ I k) → ∃ s, ∀ n, s - ∑ k ∈ range n, x k ∈ I n
  sep : ∀ x, (∀ n, x ∈ I n) → x = 0
  inv : ∀ n x, x ∈ I n → (1 + x)⁻¹ - 1 ∈ I n
  e_mem : ∀ n x, x ∈ I n → e x ∈ I n
  e_sum : ∀ x, ∑ g : G, g • e (g⁻¹ • x) = x
namespace Filt
variable {G} {I : ℕ → AddSubgroup R} {e : R →+ R} (h : Filt G I e)
include h
theorem le_zero (n : ℕ) : I n ≤ I 0 := by
  induction n with
  | zero => exact le_rfl
  | succ n ih => exact (h.anti n).trans ih
theorem mul_unit {n : ℕ} {x u : R} (hx : x ∈ I n) (hu : u - 1 ∈ I 0) : x * u ∈ I n := by
  have : x * u = x * (u - 1) + x := by ring
  rw [this]
  exact (I n).add_mem (h.anti n (h.mul n _ _ hx hu)) hx
theorem one_add_ne_zero {x : R} (hx : x ∈ I 0) : 1 + x ≠ 0 := by
  intro h0
  have h1 : (1 : R) ∈ I 0 := by
    have : (1 : R) = - x := by linear_combination h0
    rw [this]; exact (I 0).neg_mem hx
  have hn : ∀ n, (1 : R) ∈ I n := by
    intro n
    induction n with
    | zero => exact h1
    | succ n ih => simpa using h.mul n 1 1 ih h1
  exact one_ne_zero (h.sep 1 hn)
def V (n : ℕ) : Subgroup Rˣ where
  carrier := {u | (u : R) - 1 ∈ I n}
  one_mem' := by simp
  mul_mem' := fun {u v} hu hv => by
    have hu' : (u : R) - 1 ∈ I n := hu
    have hv' : (v : R) - 1 ∈ I n := hv
    show ((u * v : Rˣ) : R) - 1 ∈ I n
    have : ((u * v : Rˣ) : R) - 1 = ((u : R) - 1) * v + ((v : R) - 1) := by
      rw [Units.val_mul]; ring
    rw [this]
    exact (I n).add_mem (h.mul_unit hu' (h.le_zero n hv')) hv'
  inv_mem' := fun {u} hu => by
    have hu' : (u : R) - 1 ∈ I n := hu
    show ((u⁻¹ : Rˣ) : R) - 1 ∈ I n
    have := h.inv n _ hu'
    rwa [add_sub_cancel, ← Units.val_inv_eq_inv_val] at this
noncomputable def mkU (x : R) (hx : x ∈ I 0) : Rˣ := Units.mk0 (1 + x) (h.one_add_ne_zero hx)
end Filt
end ReciprocityTheory.DiscreteGroups.LocalClassField.UnitsFilt


