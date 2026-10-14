-- Prove2me | solution 1 for ActuarialValuation.gmLogLikeEta_derivative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T20:55:59.418119+00:00
-- url     : https://prove2.me/submissions/692f2db3-2f6b-42de-9453-70e69f5991ac

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_gmMean
import Definitions.Def_actuarial_gmPoissonLogLike
import Definitions.Def_actuarial_gmLogLikeEta
import Definitions.Def_actuarial_gmScore

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (claims exposure eta : ℝ) (hE : 0 < exposure) :
    HasDerivAt (fun x => gmLogLikeEta claims exposure x)
      (gmScore claims exposure eta) eta := by
  have hlog (x : ℝ) : Real.log (gmMean exposure x) = Real.log exposure + x := by
    simp only [gmMean]
    rw [Real.log_mul (ne_of_gt hE) (Real.exp_ne_zero x), Real.log_exp]
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
