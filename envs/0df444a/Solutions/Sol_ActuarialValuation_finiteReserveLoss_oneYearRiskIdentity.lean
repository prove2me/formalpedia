-- Prove2me | solution 1 for ActuarialValuation.finiteReserveLoss_oneYearRiskIdentity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T15:32:37.488969+00:00
-- url     : https://prove2.me/submissions/0e08779e-cd7b-486e-a2ad-c93f56ccbbe7

import Mathlib
import Definitions.Def_actuarial_finiteLifeDeathIndicator
import Definitions.Def_actuarial_finiteLifeInForceIndicator
import Definitions.Def_actuarial_finiteReserveAnnualBalance
import Definitions.Def_actuarial_finiteReserveYearInnovation
import Theorems.Thm_ActuarialValuation_finiteLifeInForce_partition
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (K t : ℕ) (v : ℝ) (reserve premium benefit p q : ℕ → ℝ)
    (hPQ : p t + q t = 1)
    (hR : finiteReserveAnnualBalance v reserve premium benefit p q t) :
    v ^ (t + 1) * benefit (t + 1) * finiteLifeDeathIndicator K t -
    v ^ t * premium t * finiteLifeInForceIndicator K t +
    v ^ (t + 1) * reserve (t + 1) * finiteLifeInForceIndicator K (t + 1) -
    v ^ t * reserve t * finiteLifeInForceIndicator K t =
    v ^ (t + 1) * (benefit (t + 1) - reserve (t + 1)) *
      finiteReserveYearInnovation K t q := by
  have hp : p t = 1 - q t := by linarith
  have hPremium : premium t =
      v * (p t * reserve (t + 1) + q t * benefit (t + 1)) - reserve t := by
    dsimp [finiteReserveAnnualBalance] at hR
    linarith
  have hpart : finiteLifeInForceIndicator K t =
      finiteLifeDeathIndicator K t + finiteLifeInForceIndicator K (t + 1) :=
    finiteLifeInForce_partition K t
  rw [hPremium, hp]
  simp only [finiteReserveYearInnovation, hpart, pow_succ]
  ring
