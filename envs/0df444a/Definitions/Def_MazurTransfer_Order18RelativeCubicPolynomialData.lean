-- Prove2me | Definitions.Def_MazurTransfer_Order18RelativeCubicPolynomialData
-- name    : MazurTransfer_Order18RelativeCubicPolynomialData
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-07T14:44:53.084979+00:00
-- url     : https://prove2.me/theorems/048b630b-d3d2-4fdd-82fe-57fa47158acc
-- title:
--   Order18: the exact relative cubic polynomial over the real cubic coefficient field
-- statement:
--   Let \(K=\mathbb{Q}[T]/(T^3-3T-1)\). This data package defines \(S^3-3S-10\) in \(K[S]\), retaining the original coefficient-field alias. Irreducibility and all class-number and descent results are separate theorem obligations.
-- source:
--   User MazurTheorem WIP54d43d8dda8a6fcf069cc02a815f850d762c5c0c, Apache-2.0 original headers and attribution retained. Exact original data declarations selected by typed kernel dependencies and whole original Lean AST ranges. All nontrivial supporting proofs are separately registered theorem obligations. Named downstream consumers: the complete cubic-quotient point-finiteness theorem and original full rational genus-two order18 exclusion. No rank, finiteness, image-triviality, point-classification or torsion conclusion is assumed in this package.

import Mathlib
import Definitions.Def_MazurTransfer_Order18RealCubicQuotientData


/- Source module: MazurTorsion.NumberTheory.XOneEighteenTwoDivisionArithmetic. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Exact arithmetic for the `X₁(18)` two-division algebra

This file records the exact algebraic-number certificates used by the
two-descent on the real-cubic elliptic quotient.  The rational cubic

`S³ - 3S - 10`

is proved irreducible by reduction modulo `11`.  We then form its relative
base change to the real cubic field `K = ℚ(τ)`.  All displayed relative
norm identities are checked in the kernel by the resultant formula for a
monogenic cubic algebra.

The relative object is deliberately called an algebra here: its field
structure is supplied only after a separate primitive-element certificate
proves that the two cubic fields are linearly disjoint.
-/

open Polynomial Module
open scoped Matrix

namespace MazurTorsion.XOneEighteenTwoDivisionArithmetic

noncomputable section

namespace Q

abbrev K := MazurTorsion.XOneEighteenRealCubicQuotient.K





end Q



/-! ## The rational two-division cubic -/







































/-! ## The relative cubic algebra over the quotient field -/

/-- The base-changed two-division polynomial over the real cubic field. -/
def relativePolynomial : Polynomial Q.K :=
  X ^ 3 - 3 * X - 10























/-! ## Exact relative norm certificates -/

























end

end MazurTorsion.XOneEighteenTwoDivisionArithmetic

end


