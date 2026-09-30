-- Prove2me | Definitions.Def_TauCeti_RingTheory_Valuation_AbsoluteValue
-- name    : TauCeti_RingTheory_Valuation_AbsoluteValue
-- status  : Definition
-- author  : @riccardo.brasca
-- created : 2026-09-29T19:55:22.47528+00:00
-- url     : https://prove2.me/theorems/93703cba-bb97-42c8-9a48-6d0ba10214d3
-- title:
--   Absolute values from valuations
-- statement:
--   Let $v$ be a valuation on a division ring $K$. Let $\phi$ be a monotone homomorphism of its value monoid to a partially ordered semiring $S$ whose addition preserves order, and assume that $\phi$ preserves and reflects zero. Composition gives an absolute value
--
--   $$
--   |x|=\phi(v(x)).
--   $$
--
--   This allows approximation results for absolute values to be applied to suitable valuations.
--
--   **Formalization Note.** These foundational declarations are transplanted from the Tau Ceti contributors' [original source](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/RingTheory/Valuation/AbsoluteValue.lean) (Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`), with compatibility adaptations for Lean 4.33.1. Mathematical proofs requiring separate theorem nodes are published separately.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/RingTheory/Valuation/AbsoluteValue.lean

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Algebra.Order.Ring.IsNonarchimedean
import Mathlib.RingTheory.Valuation.Basic

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Absolute values from valuations

This file constructs an absolute value by composing a valuation with a monotone, zero-reflecting
monoid-with-zero homomorphism.
-/

 section

open MonoidWithZeroHom

namespace Valuation

section AbsoluteValue

variable {K S Γ₀ : Type*} [DivisionRing K] [LinearOrderedCommMonoidWithZero Γ₀] [Nontrivial Γ₀]
  [Semiring S] [PartialOrder S] [addLeftMono : AddLeftMono S] [addRightMono : AddRightMono S]

omit [Nontrivial Γ₀] in
 theorem comp_apply_add_le_add_of_monotone (v : _root_.Valuation K Γ₀)
    (f : Γ₀ →*₀ S) (hf : ∀ ⦃a b⦄, a ≤ b → f a ≤ f b) (x y : K) :
    f (v (x + y)) ≤ f (v x) + f (v y) := by
  refine (hf (v.map_add x y)).trans ?_
  rcases le_total (v x) (v y) with h | h
  · rw [max_eq_right h]
    exact le_add_of_nonneg_left <| by rw [← map_zero f]; exact hf zero_le
  · rw [max_eq_left h]
    exact le_add_of_nonneg_right <| by rw [← map_zero f]; exact hf zero_le

/-- Compose a valuation with a monotone, zero-reflecting monoid-with-zero homomorphism to obtain
an absolute value. -/
noncomputable def toAbsoluteValue (v : _root_.Valuation K Γ₀) (f : Γ₀ →*₀ S)
    (hf : ∀ ⦃a b⦄, a ≤ b → f a ≤ f b) (hf_zero : ∀ a, f a = 0 ↔ a = 0) :
    AbsoluteValue K S :=
  AbsoluteValue.mk (f.comp v.toMonoidWithZeroHom)
    (fun x ↦ by rw [← map_zero f]; exact hf zero_le)
    (fun x ↦ by
      -- `AbsoluteValue.mk` has no evaluation lemma available while constructing the value.
      change f (v x) = 0 ↔ x = 0
      rw [hf_zero]
      exact v.zero_iff)
    (comp_apply_add_le_add_of_monotone v f hf)

include addLeftMono addRightMono in
/-- Evaluation of the absolute value obtained by composing a valuation with a monotone,
zero-reflecting monoid-with-zero homomorphism. -/
@[simp]
theorem toAbsoluteValue_apply (v : _root_.Valuation K Γ₀) (f : Γ₀ →*₀ S)
    (hf : ∀ ⦃a b⦄, a ≤ b → f a ≤ f b) (hf_zero : ∀ a, f a = 0 ↔ a = 0) (x : K) :
    v.toAbsoluteValue f hf hf_zero x = f (v x) := by
  -- Unfold the constructor once to establish the public evaluation lemma used below.
  change (f.comp v.toMonoidWithZeroHom) x = f (v x)
  rfl



end AbsoluteValue

section IsNonarchimedean

variable {K S Γ₀ : Type*} [DivisionRing K] [LinearOrderedCommMonoidWithZero Γ₀] [Nontrivial Γ₀]
  [Semiring S] [LinearOrder S] [addLeftMono : AddLeftMono S] [addRightMono : AddRightMono S]



end IsNonarchimedean

end Valuation

end
end


