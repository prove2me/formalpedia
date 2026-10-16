-- Prove2me | Definitions.Def_Esgk_BidegreeProductRelation
-- name    : Esgk_BidegreeProductRelation
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T04:43:49.400577+00:00
-- url     : https://prove2.me/theorems/87682110-2418-43f3-9ce5-3fc1d6f28833
-- title:
--   Coordinatewise bidegree bounds for bivariate polynomials
-- statement:
--   A bidegree-bounded polynomial is represented as a polynomial in two variables whose every supported monomial has exponent at most the given bound in each coordinate.

-- Extracted dependency interfaces and their necessary proofs.
import Mathlib

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

open MvPolynomial

abbrev BidegreePolynomial (R : Type*) [CommSemiring R] := MvPolynomial (Fin 2) R

 
def BidegreeBound {R : Type*} [CommSemiring R] (m : ℕ) (p : BidegreePolynomial R) : Prop :=
  ∀ e ∈ p.support, e 0 ≤ m ∧ e 1 ≤ m


end Esgk


