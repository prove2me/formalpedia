-- Prove2me | Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_EulerProduct_Data
-- name    : TauCeti_NumberTheory_ArithmeticDirichletSeries_EulerProduct_Data
-- status  : Definition
-- author  : @riccardo.brasca
-- created : 2026-09-29T19:48:08.279718+00:00
-- url     : https://prove2.me/theorems/7000d873-ed63-45c7-be72-101ac006907d
-- title:
--   Euler-product coefficient data over a number field
-- statement:
--   Ideal Euler-product data consists of multiplicative coefficients on nonzero integral ideals, together with the local sequences $e\mapsto f(P^e)$. Pointwise multiplication, conjugation, and restriction away from a set of primes act on these data. They provide a common interface for Euler-product identities.
--
--   **Formalization Note.** These foundational declarations are transplanted from the Tau Ceti contributors' [original source](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/ArithmeticDirichletSeries/EulerProduct/Data.lean) (Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`), with compatibility adaptations for Lean 4.33.1. Mathematical proofs requiring separate theorem nodes are published separately.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/ArithmeticDirichletSeries/EulerProduct/Data.lean

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Basic
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_EulerProduct_Basic
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Weight
import Definitions.Def_TauCeti_RingTheory_DedekindDomain_Ideal
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Ring.Subgroup
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.LinearAlgebra.Pi
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.ArithmeticFunction.LFunction
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients
import Mathlib.RingTheory.UniqueFactorizationDomain.Finite
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.Tactic.Ring

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Euler-product coefficient data over a number field

This file bundles the algebraic input for an Euler product over the height-one primes of the ring
of integers of a number field. An `EulerProductData K` consists of an ideal arithmetic function
that is multiplicative on relatively prime nonzero ideals. The prime-power series and local
arithmetic factors are canonically derived from the function as defined in
`EulerProduct/Basic.lean`, so nothing about the local behaviour is stored: the bundle carries
exactly the one algebraic hypothesis that an Euler product consumes.

The formal Euler-product identity follows from
`IdealArithmeticFunction.normCoeff_eq_eulerProduct`: coprime multiplicativity and unique
factorization prove that `normCoeff` is Mathlib's `ArithmeticFunction.eulerProduct` of the
canonical local factors.

Two hypotheses of the classical theory are deliberately absent, because the identity proved here
does not need either. There is no distinguished finite set of exceptional primes: multiplicativity
is required on every coprime pair of nonzero ideals, and the local factor at a prime is read off
from the coefficients at its powers, good or bad. There is also no analytic input: the identity is
an equality of arithmetic functions, and the convergence of the evaluated factors to an infinite
product is a separate question.

## Main definitions

* `TauCeti.EulerProductData` bundles a multiplicative ideal coefficient system.
* `TauCeti.EulerProductData.ofMultiplicativeIdealWeight` regards a degree-one ideal weight as
  Euler-product data.
* Pointwise multiplication, complex conjugation, and restriction away from sets of primes
  preserve the bundle.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII.
* Mathlib's `ArithmeticFunction.ofPowerSeries` and `ArithmeticFunction.eulerProduct` APIs.
-/

 section

namespace TauCeti

open scoped nonZeroDivisors NumberField
open IsDedekindDomain (HeightOneSpectrum)

/-- The algebraic coefficient data of an ideal Euler product. The local prime-power series is
canonically derived from `toIdealArithmeticFunction`. -/
structure EulerProductData (K : Type*) [Field K] [NumberField K] where
  /-- The coefficients indexed by nonzero integral ideals. -/
  toIdealArithmeticFunction : IdealArithmeticFunction K
  /-- Coprime multiplicativity, the exact algebraic hypothesis used by an Euler product. -/
  isMultiplicative : toIdealArithmeticFunction.IsMultiplicative

namespace EulerProductData

variable {K : Type*} [Field K] [NumberField K]

instance : CoeFun (EulerProductData K) fun _ ↦ ((Ideal (𝓞 K))⁰) → ℂ where
  coe D := D.toIdealArithmeticFunction

@[ext]
theorem ext {D E : EulerProductData K} (h : ∀ I, D I = E I) : D = E := by
  cases D with
  | mk D _ =>
    cases E with
    | mk E _ =>
      congr
      funext I
      exact h I









/-- The canonical local arithmetic factor of bundled Euler-product data at a height-one prime. -/
noncomputable def localArithmeticFactor (D : EulerProductData K)
    (P : HeightOneSpectrum (𝓞 K)) : ArithmeticFunction ℂ :=
  D.toIdealArithmeticFunction.localArithmeticFactor P











/-- A completely multiplicative ideal weight supplies Euler-product data. -/
noncomputable def ofMultiplicativeIdealWeight (χ : MultiplicativeIdealWeight K) :
    EulerProductData K where
  toIdealArithmeticFunction := χ.toIdealArithmeticFunction
  isMultiplicative := χ.isMultiplicative_toIdealArithmeticFunction



@[simp]
theorem ofMultiplicativeIdealWeight_apply (χ : MultiplicativeIdealWeight K)
    (I : (Ideal (𝓞 K))⁰) : ofMultiplicativeIdealWeight χ I = χ I := by
  exact MultiplicativeIdealWeight.toIdealArithmeticFunction_apply χ I

/-- The pointwise product of two Euler-product coefficient systems. -/
noncomputable instance : Mul (EulerProductData K) where
  mul D E :=
    { toIdealArithmeticFunction := D.toIdealArithmeticFunction * E.toIdealArithmeticFunction
      isMultiplicative := D.isMultiplicative.mul E.isMultiplicative }

@[simp]
theorem mul_apply (D E : EulerProductData K) (I : (Ideal (𝓞 K))⁰) :
    (D * E) I = D I * E I := (rfl)

/-- The trivial ideal coefficient system as Euler-product data. -/
noncomputable instance : One (EulerProductData K) where
  one := ofMultiplicativeIdealWeight 1

@[simp]
theorem one_apply (I : (Ideal (𝓞 K))⁰) : (1 : EulerProductData K) I = 1 := by
  have hone : (1 : EulerProductData K) = ofMultiplicativeIdealWeight 1 := rfl
  rw [hone, ofMultiplicativeIdealWeight_apply]
  have hI : (I : Ideal (𝓞 K)) ≠ ⊥ := nonZeroDivisors.coe_ne_zero I
  simp [MultiplicativeIdealWeight.one_apply, hI]

/-- Pointwise multiplication makes Euler-product data a commutative monoid. This product remains
distinct from ideal Dirichlet convolution. -/
noncomputable instance : CommMonoid (EulerProductData K) where
  mul_assoc D E F := by ext I; simp [mul_assoc]
  one_mul D := by ext I; simp
  mul_one D := by ext I; simp
  mul_comm D E := by ext I; simp [mul_comm]

/-- Complex conjugation makes Euler-product data a star monoid. -/
noncomputable instance : StarMul (EulerProductData K) where
  star D :=
    { toIdealArithmeticFunction := star D.toIdealArithmeticFunction
      isMultiplicative := D.isMultiplicative.star }
  star_involutive D := by
    ext I
    simp
  star_mul D E := by
    ext I
    -- `star_apply` cannot be used while this `StarMul` instance is still being constructed, so
    -- expose the pointwise scalar identity by definitional reduction of the bundle operations.
    change star (D I * E I) = star (E I) * star (D I)
    exact star_mul (D I) (E I)



/-- Restrict Euler-product data away from a set of height-one primes, leaving its
coefficients unchanged on ideals prime to that set and setting the others to zero. -/
noncomputable def restrictAway (D : EulerProductData K)
    (S : Set (HeightOneSpectrum (𝓞 K))) : EulerProductData K where
  toIdealArithmeticFunction :=
    IdealArithmeticFunction.supportedPart D.toIdealArithmeticFunction Sᶜ
  isMultiplicative := D.isMultiplicative.supportedPart Sᶜ



end EulerProductData

end TauCeti

end
end


