-- Prove2me | solution 1 for ActuarialValuation.scrPairSquared_swap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:36:39.828772+00:00
-- url     : https://prove2.me/submissions/8904de1a-6e3a-4fc5-9de5-dd93c25dbb27

import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_scrPairSquared

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (rho a b : ℝ) : scrPairSquared rho a b = scrPairSquared rho b a := by
  unfold scrPairSquared scrCovarianceTerm
  ring
