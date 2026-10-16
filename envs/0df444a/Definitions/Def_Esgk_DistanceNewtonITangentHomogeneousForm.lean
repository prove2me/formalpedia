-- Prove2me | Definitions.Def_Esgk_DistanceNewtonITangentHomogeneousForm
-- name    : Esgk_DistanceNewtonITangentHomogeneousForm
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T04:56:41.079008+00:00
-- url     : https://prove2.me/theorems/3fd91bbf-6eb2-4458-900a-9dfb3f407340
-- title:
--   Dehomogenizing a circular chart polynomial
-- statement:
--   This defines the ring homomorphism that evaluates the homogenizing variable at one and the affine chart variable at the polynomial variable.

-- Extracted dependency interfaces and their necessary proofs.
import Definitions.Def_Esgk_PlaneCircularLocalChart
import Mathlib
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

open scoped BigOperators

variable {n : ℕ}


def circularChartDehomogenization : CircularChartPoly →+* Polynomial ℂ :=
  MvPolynomial.eval₂Hom (Polynomial.C : ℂ →+* Polynomial ℂ) ![Polynomial.X, 1]


end Esgk


