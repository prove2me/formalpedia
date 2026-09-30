-- Prove2me | Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_NormCoeff
-- name    : TauCeti_NumberTheory_ArithmeticDirichletSeries_NormCoeff
-- status  : Definition
-- author  : @riccardo.brasca
-- created : 2026-09-29T19:43:31.628259+00:00
-- url     : https://prove2.me/theorems/d7fda5a3-c9a6-4f46-a7db-e3aeca07aabc
-- title:
--   Regrouping ideal arithmetic functions by absolute norm
-- statement:
--   For a number field $K$, write $\mathrm N I$ for the absolute norm of a nonzero integral ideal. For an ideal arithmetic function $f$, define
--
--   $$
--   a_f(n)=\sum_{\mathrm N I=n}f(I).
--   $$
--
--   Each fiber is finite, and this assignment is complex-linear. It rewrites ideal Dirichlet series as series indexed by natural numbers.
--
--   **Formalization Note.** These foundational declarations are transplanted from the Tau Ceti contributors' [original source](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/ArithmeticDirichletSeries/NormCoeff.lean) (Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`), with compatibility adaptations for Lean 4.33.1. Mathematical proofs requiring separate theorem nodes are published separately.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/ArithmeticDirichletSeries/NormCoeff.lean

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Basic
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Regrouping ideal arithmetic functions by absolute norm

This file defines `TauCeti.normCoeff`, the ordinary arithmetic function obtained by summing an
`IdealArithmeticFunction` over each fibre of the absolute norm.  These fibres are finite by
`Ideal.finite_setOfPred_absNorm_eq`, so the coefficients are honest finite sums.  The resulting
function has value zero at `0`, as required by Mathlib's `ArithmeticFunction` carrier; that value
is available from `ArithmeticFunction.map_zero`.

The construction is bundled as a complex-linear map.  The basic API exposes the finite norm fibre
`TauCeti.normFiber` and its finiteness, records the value at one, proves compatibility with
complex conjugation, and records in `TauCeti.norm_normCoeff_eq_sum_norm_of_nonneg` that no
cancellation occurs inside a fibre when the values of `f` are nonnegative.  Regrouping is
compatible with transporting along an isomorphism of number fields: `TauCeti.normCoeff_map` says
that an isomorphism `e : K ≃+* L` leaves every norm coefficient unchanged.

Regrouping loses information as soon as a norm fibre has more than one element:
`TauCeti.exists_forall_normCoeff_nonneg_not_forall_nonneg` produces a nonzero ideal arithmetic
function, with a negative value, whose norm coefficients all vanish.  This is the rejection test
that forbids weakening the nonnegativity hypothesis of the converse regrouping theorem to
nonnegativity of the coefficients themselves.

## Roadmap role

This is the finite-norm-fibre part of Layer **1.1** of
`TauCetiRoadmap/ArithmeticDirichletSeries/README.md`.  The next layer step uses these coefficients
to regroup an absolutely convergent series over nonzero ideals into a Mathlib `LSeries`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII.
* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapters II--III.
-/

 section

namespace TauCeti

open scoped nonZeroDivisors NumberField ComplexOrder

variable (K : Type*) [Field K] [NumberField K]

/-- The fibre of nonzero integral ideals with a fixed absolute norm is finite. -/
theorem finite_normFiber (n : ℕ) :
    {I : (Ideal (𝓞 K))⁰ | Ideal.absNorm (I : Ideal (𝓞 K)) = n}.Finite := by
  exact (Ideal.finite_setOfPred_absNorm_eq n).preimage Subtype.val_injective.injOn

/-- The finite set of nonzero integral ideals with a fixed absolute norm. -/
noncomputable def normFiber (n : ℕ) : Finset ((Ideal (𝓞 K))⁰) :=
  (finite_normFiber K n).toFinset

/-- Membership in an absolute-norm fibre. -/
@[simp]
theorem mem_normFiber {I : (Ideal (𝓞 K))⁰} {n : ℕ} :
    I ∈ normFiber K n ↔ Ideal.absNorm (I : Ideal (𝓞 K)) = n := by
  simp [normFiber]



/-- No nonzero integral ideal has absolute norm zero. -/
@[simp]
theorem normFiber_zero : normFiber K 0 = ∅ := by
  ext I
  rw [mem_normFiber]
  constructor
  · intro hI
    exact mem_nonZeroDivisors_iff_ne_zero.mp I.property (Ideal.absNorm_eq_zero_iff.mp hI) |>.elim
  · simp



/-- Regroup ideal arithmetic functions by absolute norm as a complex-linear map.

The coefficient at `n` is the finite sum of `f I` over the nonzero integral ideals `I` whose
absolute norm is `n`.  Use `normCoeff_apply` for this formula. -/
noncomputable def normCoeff : IdealArithmeticFunction K →ₗ[ℂ] ArithmeticFunction ℂ where
  toFun f :=
    { toFun n := ∑ᶠ I ∈ {I : (Ideal (𝓞 K))⁰ | Ideal.absNorm (I : Ideal (𝓞 K)) = n}, f I
      map_zero' := by
        apply finsum_mem_eq_zero_of_forall_eq_zero
        intro I hI
        exact
          (mem_nonZeroDivisors_iff_ne_zero.mp I.property (Ideal.absNorm_eq_zero_iff.mp hI)).elim }
  map_add' f g := by
    ext n
    simp only [Pi.add_apply]
    exact finsum_mem_add_distrib (finite_normFiber K n)
  map_smul' c f := by
    ext n
    simp only [Pi.smul_apply]
    exact (DistribSMul.toAddMonoidHom ℂ c).map_finsum_mem f (finite_normFiber K n) |>.symm



















/-! ### The cancellation rejection test -/



end TauCeti

end
end


