-- Prove2me | Definitions.Def_Esgk_IrreduciblePlaneAffineNormalizationNonsingularLift
-- name    : Esgk_IrreduciblePlaneAffineNormalizationNonsingularLift
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T04:47:15.217379+00:00
-- url     : https://prove2.me/theorems/c61a2762-9b1d-44d5-b877-5179e7f7240c
-- title:
--   Specializing a polynomial at a parameter
-- statement:
--   This evaluates the coefficients of a generic polynomial at a specified parameter into a target ring, producing the specialized polynomial.

-- Extracted dependency interfaces and their necessary proofs.
import Definitions.Def_LeanFormalizations_PachDeZeeuw_Bezout
import Mathlib

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

open PachDeZeeuw.Algebraic

namespace IrreduciblePlanePolynomial

open MvPolynomial

 
def specializeAt {R : Type*} [CommRing R] {σ : Type*} [DecidableEq σ]
    (i : σ) (c : R) : MvPolynomial σ R →+* MvPolynomial σ R :=
  MvPolynomial.eval₂Hom (C : R →+* MvPolynomial σ R)
    (fun k => if k = i then C c else X k)


end IrreduciblePlanePolynomial

end Esgk


