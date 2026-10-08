-- Prove2me | Definitions.Def_MazurTransfer_Order49ResultantFactorData
-- name    : MazurTransfer_Order49ResultantFactorData
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-06T21:46:07.776272+00:00
-- url     : https://prove2.me/theorems/85c6b04c-6249-4c06-be4f-55885e0d62e2
-- title:
--   Order-49 exact factored resultant polynomial
-- statement:
--   Let $f_6,f_{12}\in\mathbb Z[T]$ be the fixed degree-six and degree-twelve polynomials recorded here. Define $$F(T)=T^{63}(T-1)^{51}(T^3-8T^2+5T+1)^{260}f_6(T)^2 f_{12}(T).$$ This is the fixed target polynomial for the bounded resultant calculation of the order-seven backtracking cofactors. The definitions assume no resultant equality or nonvanishing statement.
-- source:
--   User MazurTheorem WIP 54d43d8dda8a6fcf069cc02a815f850d762c5c0c, Apache-2.0 header retained. Three pure original definitions retained at complete Lean AST command ranges, with unchanged type/value bytes; all values compared to original definitions by controlled definitional equality proofs, with standard axioms and no limit changes. Boundary: the factored resultant polynomial, with no assumed resultant identity or nonvanishing. Named downstream consumer: generic_resultant_eq_resultantFactorData and the full order49 exclusion.

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Field.Rat

/-!
# Rational nonvanishing factors for the order-seven resultant

The primitive resultant certificate for the order-seven backtracking
calculation has two factors not accounted for by the discriminant of the
Kubert family.  This file records them over `ℤ` and proves that neither has a
rational root.  Since both polynomials are monic with constant coefficient
one, the rational-root theorem reduces the proof to evaluation at `±1`.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

noncomputable section

/-- The degree-six primitive factor in the order-seven resultant. -/
def resultantFactorSix : ℤ[X] :=
  X ^ 6 + C 229 * X ^ 5 + C 270 * X ^ 4 - C 1695 * X ^ 3 +
    C 1430 * X ^ 2 - C 235 * X + 1

/-- The degree-twelve primitive factor in the order-seven resultant. -/
def resultantFactorTwelve : ℤ[X] :=
  X ^ 12 - C 522 * X ^ 11 - C 8955 * X ^ 10 + C 37950 * X ^ 9 -
    C 70998 * X ^ 8 + C 131562 * X ^ 7 - C 253239 * X ^ 6 +
    C 316290 * X ^ 5 - C 218058 * X ^ 4 + C 80090 * X ^ 3 -
    C 14631 * X ^ 2 + C 510 * X + 1











/-- The generic first backtracking resultant, factored over the parameter
ring.  The Bézout certificate has this polynomial as its scalar target. -/
def resultantFactorData : ℚ[X] :=
  X ^ 63 * (X - 1) ^ 51 *
    (X ^ 3 - C 8 * X ^ 2 + C 5 * X + 1) ^ 260 *
    (resultantFactorSix.map (Int.castRingHom ℚ)) ^ 2 *
    resultantFactorTwelve.map (Int.castRingHom ℚ)



end

end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate


