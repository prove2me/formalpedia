-- Prove2me | solution 1 for ActuarialValuation.gmInsuranceGLM_fundamental
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T20:58:49.939282+00:00
-- url     : https://prove2.me/submissions/2ecfb5f9-47c1-4a65-b6a6-039d2a6d26e0

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Definitions.Def_actuarial_gmMean
import Definitions.Def_actuarial_gmRate
import Definitions.Def_actuarial_gmLogMean
import Definitions.Def_actuarial_gmPurePremium
import Definitions.Def_actuarial_gmPoissonLogLike
import Definitions.Def_actuarial_gmSaturatedLike
import Definitions.Def_actuarial_gmLogLikeEta
import Definitions.Def_actuarial_gmScore
import Definitions.Def_actuarial_gmInformation
import Definitions.Def_actuarial_gmPoissonDeviance
import Definitions.Def_actuarial_gmRatingPremium

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (claims exposure eta severity : ℝ)
    (hc : 0 < claims) (he : 0 < exposure) (hs : 0 ≤ severity) :
    (Real.log (gmMean exposure eta) = gmLogMean exposure eta) ∧
    HasDerivAt (fun x => gmLogLikeEta claims exposure x)
      (gmScore claims exposure eta) eta ∧
    HasDerivAt (fun x => gmScore claims exposure x)
      (-gmInformation exposure eta) eta ∧
    (0 ≤ gmPoissonDeviance claims (gmMean exposure eta)) ∧
    (gmRatingPremium exposure eta severity =
      exposure * gmPurePremium (gmRate eta) severity) := by
  have hlogmean : Real.log (gmMean exposure eta) = gmLogMean exposure eta := by
    simp only [gmMean, gmLogMean]
    rw [Real.log_mul (ne_of_gt he) (Real.exp_ne_zero eta), Real.log_exp]
  have hsderiv : HasDerivAt (fun x => gmScore claims exposure x)
      (-gmInformation exposure eta) eta := by
    have h : HasDerivAt (fun x : ℝ => exposure * Real.exp x)
        (exposure * Real.exp eta) eta :=
      (Real.hasDerivAt_exp eta).const_mul exposure
    simpa only [gmScore, gmMean, gmInformation] using h.const_sub claims
  have hlogderiv : HasDerivAt (fun x => gmLogLikeEta claims exposure x)
      (gmScore claims exposure eta) eta := by
    have hlog (x : ℝ) : Real.log (gmMean exposure x) = Real.log exposure + x := by
      simp only [gmMean]
      rw [Real.log_mul (ne_of_gt he) (Real.exp_ne_zero x), Real.log_exp]
    have heq : (fun x : ℝ => gmLogLikeEta claims exposure x) =
        (fun x : ℝ => claims * (Real.log exposure + x) - exposure * Real.exp x) := by
      funext x
      unfold gmLogLikeEta gmPoissonLogLike
      rw [hlog x]
      rfl
    have hlin : HasDerivAt (fun x : ℝ => claims * (Real.log exposure + x))
        claims eta := by
      simpa using (((hasDerivAt_id eta).const_add (Real.log exposure)).const_mul claims)
    have hexp : HasDerivAt (fun x : ℝ => exposure * Real.exp x)
        (exposure * Real.exp eta) eta :=
      (Real.hasDerivAt_exp eta).const_mul exposure
    rw [heq]
    change HasDerivAt
      ((fun x : ℝ => claims * (Real.log exposure + x)) -
        (fun x : ℝ => exposure * Real.exp x))
      (claims - exposure * Real.exp eta) eta
    exact hlin.sub hexp
  have heMean : 0 < gmMean exposure eta := by
    dsimp [gmMean]
    exact mul_pos he (Real.exp_pos eta)
  have hdeviance : 0 ≤ gmPoissonDeviance claims (gmMean exposure eta) := by
    have hratio : 0 < gmMean exposure eta / claims := div_pos heMean hc
    have hlog : Real.log (gmMean exposure eta / claims) ≤
        gmMean exposure eta / claims - 1 :=
      Real.log_le_sub_one_of_pos hratio
    rw [Real.log_div (ne_of_gt heMean) (ne_of_gt hc)] at hlog
    have hmul := mul_le_mul_of_nonneg_left hlog hc.le
    have hid : claims * (gmMean exposure eta / claims) = gmMean exposure eta := by
      field_simp
    have hdiff : 0 ≤
        claims * Real.log claims - claims -
          (claims * Real.log (gmMean exposure eta) - gmMean exposure eta) := by
      nlinarith [hmul]
    unfold gmPoissonDeviance gmSaturatedLike gmPoissonLogLike
    nlinarith
  have hrating : gmRatingPremium exposure eta severity =
      exposure * gmPurePremium (gmRate eta) severity := by
    simp only [gmRatingPremium, gmPurePremium, gmRate, gmMean, mul_assoc]
  exact ⟨hlogmean, hlogderiv, hsderiv, hdeviance, hrating⟩
