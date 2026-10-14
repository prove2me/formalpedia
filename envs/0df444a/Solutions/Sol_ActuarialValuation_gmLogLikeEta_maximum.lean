-- Prove2me | solution 1 for ActuarialValuation.gmLogLikeEta_maximum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T20:44:23.11527+00:00
-- url     : https://prove2.me/submissions/7bf88198-f6af-4540-82e0-8b7cda2be61f

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Definitions.Def_actuarial_gmMean
import Definitions.Def_actuarial_gmPoissonLogLike
import Definitions.Def_actuarial_gmLogLikeEta

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (claims exposure fitted candidate : ℝ) (hc : 0 < claims)
    (he : 0 < exposure) (hfit : gmMean exposure fitted = claims) :
    gmLogLikeEta claims exposure candidate ≤ gmLogLikeEta claims exposure fitted := by
  let mu : ℝ := gmMean exposure candidate
  have hmu : 0 < mu := by
    dsimp [mu, gmMean]
    exact mul_pos he (Real.exp_pos candidate)
  have hratio : 0 < mu / claims := div_pos hmu hc
  have hlog : Real.log (mu / claims) ≤ mu / claims - 1 :=
    Real.log_le_sub_one_of_pos hratio
  rw [Real.log_div (ne_of_gt hmu) (ne_of_gt hc)] at hlog
  have hmul := mul_le_mul_of_nonneg_left hlog hc.le
  have hid : claims * (mu / claims) = mu := by
    field_simp
  have hdiff : 0 ≤
      claims * Real.log claims - claims -
        (claims * Real.log mu - mu) := by
    nlinarith [hmul]
  change gmPoissonLogLike claims mu ≤ gmPoissonLogLike claims (gmMean exposure fitted)
  rw [hfit]
  unfold gmPoissonLogLike
  nlinarith [hdiff]
