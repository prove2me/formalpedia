-- Prove2me | Definitions.Def_MazurTransfer_Order18RelativeCubicFieldData
-- name    : MazurTransfer_Order18RelativeCubicFieldData
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-07T14:51:07.491977+00:00
-- url     : https://prove2.me/theorems/c9b309dc-ea5a-42f7-9b0d-5101cc7e8d56
-- title:
--   Order18: the exact degree-nine relative two-division field
-- statement:
--   The relative algebra \(M=K[S]/(S^3-3S-10)\), with its field structure supplied by the separately Proved irreducibility theorem. Standard finite-power-basis tower constructions supply the essential number-field instance. No principal-ideal, class-number, global descent or point-finiteness assertion is included.
-- source:
--   User MazurTheorem WIP54d43d8dda8a6fcf069cc02a815f850d762c5c0c, Apache-2.0 original headers and attribution retained. Exact original data declarations selected by typed kernel dependencies and whole original Lean AST ranges. All nontrivial supporting proofs are separately registered theorem obligations. Named downstream consumers: the complete cubic-quotient point-finiteness theorem and original full rational genus-two order18 exclusion. No rank, finiteness, image-triviality, point-classification or torsion conclusion is assumed in this package.

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI
The relative algebra declaration is retained verbatim from XOneEighteenTwoDivisionArithmetic.
Field and number-field instances consume separately Proved irreducibility theorems.
-/
import Mathlib
import Definitions.Def_MazurTransfer_Order18RelativeCubicPolynomialData
import Theorems.Thm_MazurTransfer_order18_real_cubic_polynomial_irreducible
import Theorems.Thm_MazurTransfer_order18_relative_cubic_polynomial_irreducible
open Polynomial
namespace MazurTorsion.XOneEighteenTwoDivisionArithmetic
noncomputable section
/-- The relative cubic two-division algebra `K[S]/(S³-3S-10)`.

It is not declared to be a field in this module: that conclusion requires
the independent primitive-element/linear-disjointness certificate. -/
abbrev M := AdjoinRoot relativePolynomial
end
end MazurTorsion.XOneEighteenTwoDivisionArithmetic
namespace MazurTorsion.XOneEighteenTwoDivisionClassNumber
open MazurTorsion.XOneEighteenTwoDivisionArithmetic
instance relativePolynomial_irreducibleFact : Fact (Irreducible relativePolynomial) :=
  ⟨MazurTransfer.order18_relative_cubic_polynomial_irreducible⟩
instance compositumNumberField : NumberField M := by
  letI : Module.Finite ℚ Q.K :=
    (AdjoinRoot.powerBasis MazurTransfer.order18_real_cubic_polynomial_irreducible.ne_zero).finite
  letI : NumberField Q.K := NumberField.of_module_finite ℚ Q.K
  letI : Module.Finite Q.K M :=
    (AdjoinRoot.powerBasis MazurTransfer.order18_relative_cubic_polynomial_irreducible.ne_zero).finite
  exact NumberField.of_module_finite Q.K M
end MazurTorsion.XOneEighteenTwoDivisionClassNumber


