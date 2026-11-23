-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MatrixRegular
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MatrixRegular
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:03:43.770209+00:00
-- url     : https://prove2.me/theorems/955a00de-4c38-497c-9b81-13e1194aaa10
-- title:
--   Matrix Regular
-- statement:
--   Definitions and structural lemmas for Matrix Regular, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MatrixRegular.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.OppRad
open scoped Classical
section Ring
variable {R : Type} [Ring R]
def U (p q : R) : Subgroup Rˣ where
  carrier := {u | p * (u.val - 1) = u.val - 1 ∧ (u.val - 1) * q = u.val - 1}
  one_mem' := by simp
  mul_mem' := by
    rintro u v ⟨a1, a2⟩ ⟨b1, b2⟩
    constructor
    · have e : (u * v).val - 1 = (u.val - 1) * v.val + (v.val - 1) := by rw [Units.val_mul]; noncomm_ring
      rw [e, mul_add, ← mul_assoc, a1, b1]
    · have e : (u * v).val - 1 = u.val * (v.val - 1) + (u.val - 1) := by rw [Units.val_mul]; noncomm_ring
      rw [e, add_mul, mul_assoc, a2, b2]
  inv_mem' := by
    rintro u ⟨a1, a2⟩
    constructor
    · have e : (u⁻¹).val - 1 = -((u.val - 1) * (u⁻¹).val) := by rw [sub_mul, Units.mul_inv]; noncomm_ring
      rw [e, mul_neg, ← mul_assoc, a1]
    · have e : (u⁻¹).val - 1 = -((u⁻¹).val * (u.val - 1)) := by rw [mul_sub, Units.inv_mul]; noncomm_ring
      rw [e, neg_mul, mul_assoc, a2]
def un (x : R) (h : x * x = 0) : Rˣ :=
  ⟨1 + x, 1 - x, by rw [add_mul, mul_sub, mul_sub, h]; simp, by rw [sub_mul, mul_add, mul_add, h]; simp⟩
end Ring
section Sum
variable {G V : Type} [Group G] [Finite G] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V)
def S (H : Subgroup G) : V →ₗ[ℂ] V := haveI := Fintype.ofFinite H; ∑ h : H, π h
variable {π}
end Sum
variable {R V : Type} [Ring R] [Finite R] [AddCommGroup V] [Module ℂ V] {π : Representation ℂ Rˣ V}
variable (π) in

def OppInj (p q : R) : Prop := ∀ v : V, (∀ u ∈ U p q, π u v = v) → S π (U q p) v = 0 → v = 0
end GlobalTheory.OppRad


