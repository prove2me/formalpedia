-- Prove2me | Definitions.Def_MazurTransfer_Order18RationalCubics
-- name    : MazurTransfer_Order18RationalCubics
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-06T17:41:40.317696+00:00
-- url     : https://prove2.me/theorems/4b6891b9-d515-40fe-9255-1de45d956388
-- title:
--   Order-18 number-field data: rational-cubics
-- statement:
--   These data define the two original rational cubics
--   \[p(T)=T^3-3T-1,\qquad q(S)=S^3-3S-10.\]
--   They contain no irreducibility assertion. Their named downstream consumers prove irreducibility and construct the real coefficient field and rational two-division field used in the complete order-18 descent.
-- source:
--   Exact whole pure-data commands from user MazurTheorem WIP, commit 54d43d8dda8a6fcf069cc02a815f850d762c5c0c. Original types, values and docstrings retained. Apache-2.0 attribution retained. Constructor validity, where needed, comes only from separately proved public irreducibility statements; no class-number, unit-rank, Selmer or torsion assertion is included.

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI
-/
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Field.Rat

noncomputable section
open Polynomial

namespace MazurTorsion.XOneEighteenRealCubicQuotient

/-- The defining polynomial of the real cubic coefficient field. -/
def cubicPolynomial : Polynomial ℚ :=
  X ^ 3 - 3 * X - 1

end MazurTorsion.XOneEighteenRealCubicQuotient

namespace MazurTorsion.XOneEighteenTwoDivisionArithmetic

/-- The irreducible rational cubic governing the nontrivial two-torsion of
the rational model `[1,-1,1,25,1]`. -/
def twoDivisionPolynomial : Polynomial ℚ :=
  X ^ 3 - 3 * X - 10

end MazurTorsion.XOneEighteenTwoDivisionArithmetic

end


