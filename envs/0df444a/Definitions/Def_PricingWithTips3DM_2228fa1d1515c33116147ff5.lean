-- Prove2me | Definitions.Def_PricingWithTips3DM_2228fa1d1515c33116147ff5
-- name    : PricingWithTips3DM_2228fa1d1515c33116147ff5
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T09:00:27.557235+00:00
-- url     : https://prove2.me/theorems/c927d8db-fa61-4231-99e2-0c3dced280c1
-- title:
--   PricingWithTips 3DM dependency: Scratch_PricingWithTips_FixedShapeLiteralOrdinalArithmetic
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://arxiv.org/abs/2507.10872

import Definitions.Def_PricingWithTips3DM_db4e278a2acaaf8b3ea05b7b
import Definitions.Def_PricingWithTips3DM_12d2e8cf841ea25263d0c142
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Affine blocks for fixed-shape literal-test ordinals

For fixed input length `L`, literal tests are ordered by polarity, variable,
then clause.  Within each `(polarity, variable)` block the row-major cell
ordinal is affine in the clause index.  All bases, strides, and counts below
are fixed natural polynomials in `L`, so they can be emitted by the verified
exact-polynomial affine-progression machine.
-/

namespace PricingWithTips.FixedShapeLiteralOrdinalArithmetic

noncomputable section

open CLRS.Chapter34.Turing.PolyBuilder
open PricingWithTips.FixedShape3DM
open PricingWithTips.FixedShapeSparseCells
open Hardness.Cert.SatToMatching3DCode

def lengthPolynomial : Polynomial Nat := Polynomial.X

def dimensionValue (L : Nat) : Nat := (L + 1) * (L * 2)

def dimensionPolynomial : Polynomial Nat :=
  (Polynomial.X + 1) * (2 * Polynomial.X)

@[simp] theorem dimensionPolynomial_eval (L : Nat) :
    dimensionPolynomial.eval L = dimensionValue L := by
  simp [dimensionPolynomial, dimensionValue]
  ring

/-- The clause-test coordinate `(L+1)L`. -/
def testBasePolynomial : Polynomial Nat :=
  (Polynomial.X + 1) * Polynomial.X

/-- Increment in a test-cell ordinal when the clause index increases by one. -/
def clauseStridePolynomial : Polynomial Nat :=
  2 * dimensionPolynomial ^ 2 + dimensionPolynomial + 1

/-- Increment in the literal-block base when the variable increases by one. -/
def variableStridePolynomial : Polynomial Nat :=
  2 * Polynomial.X * dimensionPolynomial ^ 2

/-- Base ordinal of the negative literal for variable zero and clause zero. -/
def negativeBasePolynomial : Polynomial Nat :=
  testBasePolynomial * (dimensionPolynomial + 1)

/-- Base ordinal of the positive literal for variable zero and clause zero. -/
def positiveBasePolynomial : Polynomial Nat :=
  negativeBasePolynomial + dimensionPolynomial ^ 2

@[simp] theorem testBasePolynomial_eval (L : Nat) :
    testBasePolynomial.eval L = (L + 1) * L := by
  simp [testBasePolynomial]

@[simp] theorem clauseStridePolynomial_eval (L : Nat) :
    clauseStridePolynomial.eval L =
      2 * (((L + 1) * (L * 2)) ^ 2) + (L + 1) * (L * 2) + 1 := by
  simp [clauseStridePolynomial, dimensionValue]

@[simp] theorem variableStridePolynomial_eval (L : Nat) :
    variableStridePolynomial.eval L =
      2 * L * (((L + 1) * (L * 2)) ^ 2) := by
  simp [variableStridePolynomial, dimensionValue]

@[simp] theorem negativeBasePolynomial_eval (L : Nat) :
    negativeBasePolynomial.eval L =
      ((L + 1) * L) * ((L + 1) * (L * 2) + 1) := by
  simp [negativeBasePolynomial, dimensionValue]

@[simp] theorem positiveBasePolynomial_eval (L : Nat) :
    positiveBasePolynomial.eval L =
      ((L + 1) * L) * ((L + 1) * (L * 2) + 1) +
        ((L + 1) * (L * 2)) ^ 2 := by
  simp [positiveBasePolynomial, dimensionValue]

/-- Pure ordinal contribution attached to a clause position. -/
def clauseContribution (L q : Nat) : Nat :=
  q * (2 * dimensionValue L ^ 2 + dimensionValue L + 1)

/-- Pure block base attached to a literal `(variable, polarity)`. -/
def literalBase (L v : Nat) (positive : Bool) : Nat :=
  ((2 * L * v + positive.toNat) * dimensionValue L ^ 2) +
    ((L + 1) * L) * (dimensionValue L + 1)

theorem test_ordinal_eq_contributions (L v q : Nat) (positive : Bool) :
    ordinal (dimensionValue L)
        (extIdxN L v q positive.toNat,
          testIdxN L L q, testIdxN L L q) =
      literalBase L v positive + clauseContribution L q := by
  cases positive <;>
    simp [ordinal, extIdxN, testIdxN, literalBase, clauseContribution,
      dimensionValue, Bool.toNat] <;>
    ring

theorem negativeBase_affine (L v : Nat) :
    literalBase L v false =
      negativeBasePolynomial.eval L +
        v * variableStridePolynomial.eval L := by
  simp [literalBase, negativeBasePolynomial, variableStridePolynomial,
    dimensionValue, dimensionPolynomial]
  ring

theorem positiveBase_affine (L v : Nat) :
    literalBase L v true =
      positiveBasePolynomial.eval L +
        v * variableStridePolynomial.eval L := by
  simp [literalBase, positiveBasePolynomial, negativeBasePolynomial,
    variableStridePolynomial, dimensionValue, dimensionPolynomial]
  ring

end

end PricingWithTips.FixedShapeLiteralOrdinalArithmetic


