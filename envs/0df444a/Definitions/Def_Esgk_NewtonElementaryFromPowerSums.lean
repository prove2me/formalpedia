-- Prove2me | Definitions.Def_Esgk_NewtonElementaryFromPowerSums
-- name    : Esgk_NewtonElementaryFromPowerSums
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T04:44:11.90727+00:00
-- url     : https://prove2.me/theorems/ed1d7e5e-d363-44fe-9b8f-6060cd80284f
-- title:
--   Newton recursion from power sums
-- statement:
--   This recursively defines elementary-symmetric quantities from a sequence of power sums using the Newton identity recurrence over a commutative ring containing the rationals.

-- Extracted dependency interfaces and their necessary proofs.
import Mathlib
import Mathlib.Data.Multiset.Fintype
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

open scoped BigOperators


def newtonElementaryFromPowerSums {A : Type*} [CommRing A] [Algebra ℚ A]
    (P : ℕ → A) : ℕ → A
  | 0 => 1
  | m + 1 =>
      ((m + 1 : ℚ)⁻¹) •
        ((-1 : A) ^ (m + 2) *
          ∑ a ∈ Finset.HasAntidiagonal.antidiagonal m,
            (-1 : A) ^ (m - a.2) *
              newtonElementaryFromPowerSums P (m - a.2) * P (a.2 + 1))
termination_by m => m
decreasing_by omega


end Esgk


