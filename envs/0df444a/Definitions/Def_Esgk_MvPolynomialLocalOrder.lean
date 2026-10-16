-- Prove2me | Definitions.Def_Esgk_MvPolynomialLocalOrder
-- name    : Esgk_MvPolynomialLocalOrder
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T04:44:11.035991+00:00
-- url     : https://prove2.me/theorems/4bb4b56b-ba40-445a-bbc6-fc78ae3407e5
-- title:
--   Local order of a multivariate polynomial
-- statement:
--   This defines the local order of a multivariate polynomial by viewing it in the corresponding multivariate power-series ring and taking its power-series order.

-- Extracted dependency interfaces and their necessary proofs.
import Mathlib
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


namespace MvPolynomial

noncomputable section

variable {R σ : Type*} [CommSemiring R]

 
def localOrder (p : MvPolynomial σ R) : ℕ∞ :=
  MvPowerSeries.order (p : MvPowerSeries σ R)


end

end MvPolynomial


