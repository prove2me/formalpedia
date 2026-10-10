-- Prove2me | solution 1 for ActuarialValuation.finiteHattendorffLossVariance_eq_shock
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T09:32:16.008326+00:00
-- url     : https://prove2.me/submissions/9a4ad1cd-8bfb-4ad1-816d-7297ac14e856

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_finiteHattendorffLossVariance
import Definitions.Def_actuarial_finiteHattendorffNetAtRisk
import Theorems.Thm_ActuarialValuation_finiteHattendorffLoss_pathwise
import Theorems.Thm_ActuarialValuation_finiteHattendorffVariance_shift

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
        (finiteMortalitySurvivalRate w K) (finiteMortalityDeathRate w K) t) :
    finiteHattendorffLossVariance w K n v premium benefit reserve =
      finiteMortalityVariance w (finiteMortalityDiscountedShock w K
        (finiteHattendorffNetAtRisk v benefit reserve) n) := by
  have hfun : finiteHattendorffLoss K n v premium benefit reserve =
      (fun ω => reserve 0 + finiteMortalityDiscountedShock w K
        (finiteHattendorffNetAtRisk v benefit reserve) n ω) := by
    funext ω
    exact finiteHattendorffLoss_pathwise w K n v premium benefit reserve
      hw hsum hS hR ω
  change finiteMortalityVariance w (finiteHattendorffLoss K n v premium benefit reserve) =
    finiteMortalityVariance w
      (finiteMortalityDiscountedShock w K (finiteHattendorffNetAtRisk v benefit reserve) n)
  rw [hfun]
  exact finiteHattendorffVariance_shift w
    (finiteMortalityDiscountedShock w K (finiteHattendorffNetAtRisk v benefit reserve) n)
    (reserve 0) hsum
