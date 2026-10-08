-- Prove2me | Definitions.Def_MazurTransfer_Order18CoefficientIntegerData
-- name    : MazurTransfer_Order18CoefficientIntegerData
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-07T17:34:53.822979+00:00
-- url     : https://prove2.me/theorems/75067f45-8c29-4bc2-90d7-1873e6c9fcdf
-- title:
--   Order18: the integral coefficient generator and its defining polynomials
-- statement:
--   For the published real cubic coefficient field \(K=\mathbb Q[T]/(T^3-3T-1)\), this package defines the integer polynomial \(T^3-3T-1\), its reductions modulo rational primes, and the coefficient generator as an element of the full ring of integers \(\mathcal O_K\). The separately Proved integrality certificate supplies the subtype witness. No assertion about dyadic primes, completions, local solubility or torsion is hidden in these definitions.
-- source:
--   Exact three original pure definitions from user WIP54d43d8dda8a6fcf069cc02a815f850d762c5c0c, selected by typed kernel and whole original Lean AST ownership. The coefficientInteger declaration is replaced as a whole by its identical generator with the separately Proved public integrality witness; proof irrelevance preserves the exact original value. Original Apache-2.0 header and attribution retained. Named downstream consumer: the unchanged actual coefficient dyadic prime certificate, then the order18 local descent exclusion.

import Mathlib
import Definitions.Def_MazurTransfer_Order18AmbientSelmer
import Theorems.Thm_MazurTransfer_order18_coefficient_generator_integral


/- Source module: MazurTorsion.NumberTheory.XOneEighteenTwoDivisionSmallPrimes. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Small rational primes in the `X₁(18)` two-division compositum

This file gives the tame part of a class-number certificate for the
degree-nine two-division compositum.  For each rational prime between `5`
and `31`, one of the two cubic subfields is inert.  Contraction to that
subfield and multiplicativity of inertia degrees therefore show that every
prime of the compositum above it has inertia degree at least three.

The use of Kummer--Dedekind is unconditional: the two exact rational
power-basis discriminants are first put in the relevant conductors, which
proves that the Kummer--Dedekind exponents are prime to every prime under
consideration.  No maximal-order or class-number computation is assumed.
-/

open Polynomial Module
open scoped Matrix

namespace MazurTorsion.XOneEighteenTwoDivisionSmallPrimes

noncomputable section

open MazurTorsion.XOneEighteenTwoDivisionArithmetic
open MazurTorsion.XOneEighteenTwoDivisionClassNumber
open NumberField Ideal RingOfIntegers UniqueFactorizationMonoid

/-! ## The two rational cubic power bases -/























/-! ## Integral generators and their conductors -/

/-- The integral polynomial `X³ - 3X - 1`. -/
def coefficientPolynomialInt : Polynomial ℤ := X ^ 3 - 3 * X - 1







def coefficientInteger : NumberField.RingOfIntegers MazurTorsion.XOneEighteenRealCubicQuotient.K :=
  ⟨MazurTorsion.XOneEighteenRealCubicQuotient.tau,
    MazurTransfer.order18_coefficient_generator_integral⟩
























/-! ## Exact finite-field irreducibility certificates -/

def coefficientPolynomialMod (p : ℕ) : Polynomial (ZMod p) :=
  X ^ 3 - 3 * X - 1















































/-! ## Kummer--Dedekind and inertia in the compositum -/



















end

end MazurTorsion.XOneEighteenTwoDivisionSmallPrimes

end


