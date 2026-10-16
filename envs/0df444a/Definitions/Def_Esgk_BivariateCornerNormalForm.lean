-- Prove2me | Definitions.Def_Esgk_BivariateCornerNormalForm
-- name    : Esgk_BivariateCornerNormalForm
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T04:44:51.215988+00:00
-- url     : https://prove2.me/theorems/3efafa1e-f373-4c4f-ada6-3ee8eb3bb068
-- title:
--   The corner monomial and its remainder
-- statement:
--   This selects the exponent with both coordinates equal to a prescribed integer and subtracts that monomial with its coefficient from a complex bivariate polynomial.

-- Extracted dependency interfaces and their necessary proofs.
import Definitions.Def_Esgk_BidegreeProductRelation
import Mathlib

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

open MvPolynomial

 
def bivariateCornerExponent (p : ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 p + Finsupp.single 1 p


def bivariateCornerRemainder (p : ℕ) (Q : BidegreePolynomial ℂ) :
    BidegreePolynomial ℂ :=
  Q - monomial (bivariateCornerExponent p) (coeff (bivariateCornerExponent p) Q)


end Esgk


