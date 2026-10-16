-- Prove2me | Definitions.Def_Esgk_PlanePolynomialRationalPullback
-- name    : Esgk_PlanePolynomialRationalPullback
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T04:45:40.894749+00:00
-- url     : https://prove2.me/theorems/d1052e9c-7e97-4890-9d20-38aa8533ee85
-- title:
--   Polynomial pullback with cleared denominators
-- statement:
--   This defines the polynomial sum obtained from each monomial $cX^aY^b$ by replacing it with $cA^aB^bD^{\max(d-a-b,0)}$, where the exponent uses truncated natural subtraction. For $d$ at least the input degree it is the denominator-cleared substitution of $A/D,B/D$ wherever $D$ is nonzero; the polynomial sum itself requires no nonvanishing hypothesis.

-- Extracted dependency interfaces and their necessary proofs.
import Definitions.Def_LeanFormalizations_PachDeZeeuw_AlgebraicPrelim
import Mathlib

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/


noncomputable section

namespace Esgk

open PachDeZeeuw.Algebraic (PlanePoly)

def planePolynomialRationalPullback
    (d : ℕ) (p A B D : PlanePoly) : PlanePoly :=
  ∑ m ∈ p.support,
    MvPolynomial.C (p.coeff m) * A ^ m 0 * B ^ m 1 *
      D ^ (d - (m 0 + m 1))


end Esgk


