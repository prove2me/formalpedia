-- Prove2me | Definitions.Def_Esgk_MultivariateEliminationResultant
-- name    : Esgk_MultivariateEliminationResultant
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T04:44:11.644322+00:00
-- url     : https://prove2.me/theorems/ad315510-74b6-4aee-b836-03210c2b9661
-- title:
--   Specialization and resultant in one distinguished variable
-- statement:
--   This views a multivariate polynomial as a univariate polynomial over the remaining variables, specializes those variables to real values, and forms the resultant of two such polynomials.

-- Extracted dependency interfaces and their necessary proofs.
import Mathlib
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

 
def headCurry {n : ℕ} (p : MvPolynomial (Fin (n + 1)) ℝ) :
    Polynomial (MvPolynomial (Fin n) ℝ) :=
  MvPolynomial.finSuccEquiv ℝ n p

 
def specializeRemainingVariables {n : ℕ} (x : Fin n → ℝ)
    (p : MvPolynomial (Fin (n + 1)) ℝ) :
    Polynomial ℝ :=
  (headCurry p).map (MvPolynomial.eval x)

 
def headResultant {n : ℕ} (p q : MvPolynomial (Fin (n + 1)) ℝ) :
    MvPolynomial (Fin n) ℝ :=
  Polynomial.resultant (headCurry p) (headCurry q)


end Esgk


