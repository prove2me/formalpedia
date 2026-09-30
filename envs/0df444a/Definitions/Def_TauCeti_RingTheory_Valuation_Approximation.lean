-- Prove2me | Definitions.Def_TauCeti_RingTheory_Valuation_Approximation
-- name    : TauCeti_RingTheory_Valuation_Approximation
-- status  : Definition
-- author  : @riccardo.brasca
-- created : 2026-09-29T20:03:20.201511+00:00
-- url     : https://prove2.me/theorems/40120831-f5d4-4942-a94e-f50d0f6cc21d
-- title:
--   Weak approximation for discrete valuations
-- statement:
--   A discrete valuation on a division ring, valued in the multiplicative integers with zero, determines a real absolute value through the base-two embedding of the value group. Comparisons, equivalence, and nontriviality are preserved. This provides the real-valued interface for weak approximation.
--
--   **Formalization Note.** These foundational declarations are transplanted from the Tau Ceti contributors' [original source](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/RingTheory/Valuation/Approximation.lean) (Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`), with compatibility adaptations for Lean 4.33.1. Mathematical proofs requiring separate theorem nodes are published separately.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/RingTheory/Valuation/Approximation.lean

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_RingTheory_Valuation_AbsoluteValue
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Algebra.Order.Ring.IsNonarchimedean
import Mathlib.Analysis.AbsoluteValue.Equivalence
import Mathlib.Data.Int.WithZero
import Mathlib.RingTheory.Valuation.Basic

section
set_option autoImplicit true
/-
Copyright (c) 2026 Tau Ceti Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
/-!
# Weak approximation for discrete valuations

This file proves weak approximation for a finite family of pairwise inequivalent `ℤᵐ⁰`-valued
valuations. It first sends such a valuation through the strictly monotone embedding
`ℤᵐ⁰ → ℝ≥0 → ℝ`, obtaining a real absolute value with exactly the same comparisons. Mathlib's
abstract weak approximation theorem for real absolute values then supplies simultaneous open-ball
approximation. For normalized valuations, shifting each target by an element of prescribed value
gives the equality form with arbitrary integer orders.

The results below are the finite-family approximation engine for abstract `ℤᵐ⁰`-valued
valuations: they mention neither function fields nor places. Weak approximation for places of an
algebraic function field — Stichtenoth, *Algebraic Function Fields and Codes*, second edition,
Theorem 1.3.1 — follows from `Valuation.exists_forall_sub_eq_exp` once the place API supplies the
normalized valuation of a place and the inequivalence of distinct normalized places. The proof
consumes Mathlib's `AbsoluteValue.denseRange_algebraMap_pi` rather than rebuilding the
Artin--Whaples approximation argument.

## Main results

* `Valuation.toRealAbsoluteValue` realizes a `ℤᵐ⁰`-valued valuation as a real absolute value.
* `Valuation.exists_forall_sub_lt` gives simultaneous open-ball approximation.
* `Valuation.exists_forall_sub_eq_exp` gives prescribed integer orders for normalized valuations.
-/

 section

open scoped NNReal WithZero

namespace Valuation

 noncomputable def withZeroMulIntToReal : ℤᵐ⁰ →*₀ ℝ :=
  NNReal.toRealHom.toMonoidWithZeroHom.comp
    (WithZeroMulInt.toNNReal (by norm_num : (2 : ℝ≥0) ≠ 0))

 theorem withZeroMulIntToReal_strictMono :
    StrictMono withZeroMulIntToReal := by
  intro m n hmn
  exact_mod_cast
    WithZeroMulInt.toNNReal_strictMono (by norm_num : (1 : ℝ≥0) < 2) hmn

-- `AbsoluteValue K ℝ` uses `Real.partialOrder`, while the bundled strict-monotonicity theorem
-- infers `Real.instPreorder`; spell out the propositionally identical comparison needed by the
-- generic constructor to avoid an order-instance diamond.
 theorem withZeroMulIntToReal_monotone {m n : ℤᵐ⁰}
    (hmn : @LE.le ℤᵐ⁰ (@Preorder.toLE ℤᵐ⁰
      (@WithZero.instPreorder (Multiplicative ℤ)
        (@Multiplicative.preorder ℤ Int.instLinearOrder.toPreorder))) m n) :
    @LE.le ℝ Real.partialOrder.toLE (withZeroMulIntToReal m) (withZeroMulIntToReal n) := by
  exact_mod_cast
    WithZeroMulInt.toNNReal_strictMono (by norm_num : (1 : ℝ≥0) < 2) |>.monotone hmn

section DivisionRing

variable {K : Type*} [DivisionRing K]

/-- A `ℤᵐ⁰`-valued valuation, viewed as a real absolute value through the base-two embedding of
its value group. This changes neither comparisons nor equivalence of valuations.

A division ring is needed already here: an `AbsoluteValue` vanishes only at `0`, whereas a
valuation on a general ring may have nontrivial support. -/
noncomputable def toRealAbsoluteValue (v : Valuation K ℤᵐ⁰) : AbsoluteValue K ℝ :=
  @toAbsoluteValue K ℝ ℤᵐ⁰ _ _ _ _ Real.partialOrder (by infer_instance) (by infer_instance) v
    withZeroMulIntToReal
    (fun {_ _} h ↦ withZeroMulIntToReal_monotone h)
    (fun _ ↦ map_eq_zero _)

@[simp]
theorem toRealAbsoluteValue_apply (v : Valuation K ℤᵐ⁰) (x : K) :
    v.toRealAbsoluteValue x =
      (WithZeroMulInt.toNNReal (by norm_num : (2 : ℝ≥0) ≠ 0) (v x) : ℝ) :=
  by simp [toRealAbsoluteValue, withZeroMulIntToReal]

/-- Passing a discrete valuation to its real absolute value preserves and reflects inequalities. -/
theorem toRealAbsoluteValue_le_iff (v : Valuation K ℤᵐ⁰) {x y : K} :
    v.toRealAbsoluteValue x ≤ v.toRealAbsoluteValue y ↔ v x ≤ v y := by
  simp only [toRealAbsoluteValue_apply]
  exact withZeroMulIntToReal_strictMono.le_iff_le

/-- Passing discrete valuations to real absolute values preserves and reflects equivalence. -/
@[simp]
theorem toRealAbsoluteValue_isEquiv_iff (v w : Valuation K ℤᵐ⁰) :
    v.toRealAbsoluteValue.IsEquiv w.toRealAbsoluteValue ↔ v.IsEquiv w := by
  simp only [AbsoluteValue.IsEquiv, IsEquiv, toRealAbsoluteValue_le_iff]

/-- A discrete valuation is nontrivial exactly when its associated real absolute value is. -/
@[simp]
theorem toRealAbsoluteValue_isNontrivial_iff (v : Valuation K ℤᵐ⁰) :
    v.toRealAbsoluteValue.IsNontrivial ↔ v.IsNontrivial := by
  constructor
  · rintro ⟨x, hx0, hx1⟩
    refine ⟨x, v.ne_zero_iff.mpr hx0, fun hx ↦ hx1 ?_⟩
    rw [toRealAbsoluteValue_apply, hx, map_one, NNReal.coe_one]
  · rintro ⟨x, hx0, hx1⟩
    refine ⟨x, v.ne_zero_iff.mp hx0, fun hx ↦ hx1 ?_⟩
    rw [toRealAbsoluteValue_apply] at hx
    refine withZeroMulIntToReal_strictMono.injective ?_
    simpa [withZeroMulIntToReal] using hx

end DivisionRing

section Field

variable {K : Type*} [Field K]







end Field

end Valuation

end
end


