-- Prove2me | Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_VonMangoldt
-- name    : TauCeti_NumberTheory_ArithmeticDirichletSeries_VonMangoldt
-- status  : Definition
-- author  : @riccardo.brasca
-- created : 2026-09-29T19:43:43.125644+00:00
-- url     : https://prove2.me/theorems/eb2c4ead-718d-4841-b703-d3b701cbaa19
-- title:
--   The ideal von Mangoldt function
-- statement:
--   The ideal von Mangoldt function of a number field is
--
--   $$
--   \Lambda(I)=\begin{cases}\log\mathrm N P&I=P^m,\ m\geq1,\\0&\text{otherwise}.\end{cases}
--   $$
--
--   The von Mangoldt transform of an ideal arithmetic function $f$ is $I\mapsto f(I)\Lambda(I)$. This supplies the coefficients of logarithmic derivatives.
--
--   **Formalization Note.** These foundational declarations are transplanted from the Tau Ceti contributors' [original source](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/ArithmeticDirichletSeries/VonMangoldt.lean) (Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`), with compatibility adaptations for Lean 4.33.1. Mathematical proofs requiring separate theorem nodes are published separately.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/ArithmeticDirichletSeries/VonMangoldt.lean

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Basic
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.IsPrimePow
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
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
# The ideal von Mangoldt function

The von Mangoldt function of a nonzero ideal `A` of the ring of integers of a number field is
`log N(P)` when `A` is a positive power of a prime ideal `P`, and zero otherwise.  This file
packages that function as an `IdealArithmeticFunction` and defines its pointwise product with an
ideal arithmetic function.

## Main definitions

* `TauCeti.IdealArithmeticFunction.vonMangoldt` is the complex-valued ideal von Mangoldt
  function.
* `TauCeti.IdealArithmeticFunction.vonMangoldtTransform` sends `f` to the weighted function
  `A ↦ f(A) Λ(A)`.

## Main results

* `TauCeti.IdealArithmeticFunction.vonMangoldt_apply_prime_pow` computes the value on a positive
  power of a prime ideal.
* `TauCeti.IdealArithmeticFunction.vonMangoldt_ne_zero_iff` says that its support is exactly the
  prime-power ideals.
* `TauCeti.IdealArithmeticFunction.vonMangoldtTransform_ne_zero_iff` identifies the support of
  the transform, and its specialization in `TauCeti.MultiplicativeIdealWeight` describes this as
  the good prime powers for a completely multiplicative weight.

The definition chooses a prime base from a proof that `A` is a prime power.  Mathlib's
`eq_of_prime_pow_eq`, applied to ideals, identifies that choice with any prime base supplied by a
caller.  The public evaluation theorem therefore removes the choice from every computation.

## Implementation notes

This is the ideal analogue of Mathlib's `ArithmeticFunction.vonMangoldt`.  Here the prime base is
chosen from `IsPrimePow` rather than computed by `Nat.minFac`, its logarithmic weight is
`Ideal.absNorm P` rather than `p`, and the function is complex-valued to match
`IdealArithmeticFunction`.

## Roadmap role

This is the algebraic part of Layer **2.3** of
`TauCetiRoadmap/ArithmeticDirichletSeries/README.md`.  The logarithmic-derivative identity named in
that target additionally requires the Euler-product package of Layer 3; this file supplies its
coefficient and exact prime-power support in advance.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII.
* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapter I.2.
-/

 section

namespace TauCeti

open NumberField
open scoped nonZeroDivisors NumberField

variable {K : Type*} [Field K] [NumberField K]



namespace IdealArithmeticFunction

open Classical in
/-- The **ideal von Mangoldt function**.  It takes the value `log N(P)` on every positive power of
a prime ideal `P`, and vanishes on ideals which are not prime powers.

The codomain is `ℂ`, matching `IdealArithmeticFunction`, although every value is real. -/
noncomputable def vonMangoldt : IdealArithmeticFunction K := fun A ↦
  if h : IsPrimePow (A : Ideal (𝓞 K)) then
    (Real.log (Ideal.absNorm h.choose) : ℂ)
  else 0























/-- The **von Mangoldt transform** of an ideal arithmetic function `f`: the pointwise product
`A ↦ f(A) Λ(A)`. -/
noncomputable def vonMangoldtTransform (f : IdealArithmeticFunction K) :
    IdealArithmeticFunction K :=
  f * vonMangoldt









end IdealArithmeticFunction

namespace MultiplicativeIdealWeight





end MultiplicativeIdealWeight

end TauCeti

end
end


