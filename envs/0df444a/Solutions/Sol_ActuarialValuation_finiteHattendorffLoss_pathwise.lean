-- Prove2me | solution 1 for ActuarialValuation.finiteHattendorffLoss_pathwise
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T09:00:50.032369+00:00
-- url     : https://prove2.me/submissions/66c5a365-75e2-4333-aef3-eeb45353d581

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_finiteHattendorffLoss
import Definitions.Def_actuarial_finiteHattendorffNetAtRisk
import Definitions.Def_actuarial_finiteMortalityDeathRate
import Definitions.Def_actuarial_finiteMortalitySurvivalRate
import Theorems.Thm_ActuarialValuation_finiteReserveLoss_HattendorffBridge_fundamental
import Theorems.Thm_ActuarialValuation_finiteHattendorffYearDeathRateSum
import Theorems.Thm_ActuarialValuation_finiteHattendorffShockPortfolioBridge

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {Ω : Type*} [Fintype Ω] (w : Ω → ℝ)
    (K : Ω → ℕ) (n : ℕ) (v : ℝ)
    (premium benefit reserve : ℕ → ℝ)
    (hw : ∀ ω, 0 ≤ w ω) (hsum : (∑ ω : Ω, w ω) = 1)
    (hS : ∀ t ∈ Finset.range n, 0 < finiteMortalitySurvivalMass w K t)
    (hR : ∀ t ∈ Finset.range n,
      finiteReserveAnnualBalance v reserve premium benefit
        (finiteMortalitySurvivalRate w K) (finiteMortalityDeathRate w K) t)
    (ω : Ω) :
    finiteHattendorffLoss K n v premium benefit reserve ω =
      reserve 0 + finiteMortalityDiscountedShock w K
        (finiteHattendorffNetAtRisk v benefit reserve) n ω := by
  have hPQ : ∀ t ∈ Finset.range n,
      finiteMortalitySurvivalRate w K t +
        finiteMortalityDeathRate w K t = 1 := by
    intro t ht
    simpa [add_comm] using
      (finiteHattendorffYearDeathRateSum w K t (hS t ht))
  change finiteReserveLossAtIssue (K ω) n v premium benefit reserve =
    reserve 0 + finiteMortalityDiscountedShock w K
      (finiteHattendorffNetAtRisk v benefit reserve) n ω
  rw [finiteReserveLoss_HattendorffBridge_fundamental
    (K ω) n v reserve premium benefit
    (finiteMortalitySurvivalRate w K) (finiteMortalityDeathRate w K) hPQ hR]
  rw [finiteHattendorffShockPortfolioBridge w K n v benefit reserve ω]
