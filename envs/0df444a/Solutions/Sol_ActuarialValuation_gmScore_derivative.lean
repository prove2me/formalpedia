-- Prove2me | solution 1 for ActuarialValuation.gmScore_derivative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T20:24:26.614981+00:00
-- url     : https://prove2.me/submissions/da93f75f-2607-4abc-a718-ddaa6b0404c8

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_gmMean
import Definitions.Def_actuarial_gmScore
import Definitions.Def_actuarial_gmInformation

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (claims exposure eta : ℝ) :
    HasDerivAt (fun x => gmScore claims exposure x)
      (-gmInformation exposure eta) eta := by
  have h : HasDerivAt (fun x : ℝ => exposure * Real.exp x)
      (exposure * Real.exp eta) eta :=
    (Real.hasDerivAt_exp eta).const_mul exposure
  simpa only [gmScore, gmMean, gmInformation] using h.const_sub claims
