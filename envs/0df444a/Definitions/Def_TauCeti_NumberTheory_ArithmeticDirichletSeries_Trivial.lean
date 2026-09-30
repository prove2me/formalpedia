-- Prove2me | Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Trivial
-- name    : TauCeti_NumberTheory_ArithmeticDirichletSeries_Trivial
-- status  : Definition
-- author  : @riccardo.brasca
-- created : 2026-09-29T19:38:06.226288+00:00
-- url     : https://prove2.me/theorems/e4c11e80-807f-4b1f-8f1c-691f93d25777
-- title:
--   The trivial ideal weight and Dedekind zeta coefficients
-- statement:
--   For a number field $K$, the Dedekind-zeta coefficient at $n\in\mathbb N$ is
--
--   $$
--   a_K(n)=\#\{I\subseteq\mathcal O_K:\mathrm N I=n\}.
--   $$
--
--   This convention includes the zero ideal, giving $a_K(0)=1$. It connects ideal-counting coefficients with the Dedekind zeta function.
--
--   **Formalization Note.** These foundational declarations are transplanted from the Tau Ceti contributors' [original source](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/ArithmeticDirichletSeries/Trivial.lean) (Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`), with compatibility adaptations for Lean 4.33.1. Mathematical proofs requiring separate theorem nodes are published separately.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/ArithmeticDirichletSeries/Trivial.lean

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.DedekindZeta
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
# The trivial ideal weight and Dedekind zeta coefficients

This file identifies the norm coefficients of the trivial ideal weight with the coefficients of
the Dedekind zeta function.  There is one necessary exception: Mathlib's coefficient counts all
integral ideals and therefore has value `1` at index zero, contributed by the zero ideal, whereas
an `ArithmeticFunction` has value zero there.  Since `LSeries` ignores its zero coefficient, the
two coefficient systems define the same series.

For the rational field the ring of integers is isomorphic to `ℤ`.  Mapping an ideal through this
isomorphism and using `Int.ideal_span_absNorm_eq_self` shows that there is exactly one ideal of
each positive norm.  Thus the trivial ideal weight over `ℚ` regroups to the constant coefficient
`1` at every positive index, as for the Riemann zeta function.

## Roadmap role

This is Layer **1.3**, the trivial specialization, of
`TauCetiRoadmap/ArithmeticDirichletSeries/README.md`.  It completes Layer 1 without asserting the
exact abscissa of convergence; that is Layer 5, proved in
`TauCeti.abscissaOfAbsConv_normCoeff_one`.
-/

 section

namespace TauCeti

open scoped nonZeroDivisors NumberField

variable (K : Type*) [Field K] [NumberField K]

/-- The coefficient used in Mathlib's definition of the Dedekind zeta function: the number of
integral ideals of absolute norm `n`.

Unlike an `ArithmeticFunction`, this function has value `1` at zero, contributed by the zero
ideal. -/
noncomputable def dedekindZetaCoeff (n : ℕ) : ℕ :=
  Nat.card {I : _root_.Ideal (𝓞 K) // _root_.Ideal.absNorm I = n}



























end TauCeti

end
end


