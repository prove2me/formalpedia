-- Prove2me | solution 1 for ActuarialValuation.scrDiversificationSquared_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:38:38.104018+00:00
-- url     : https://prove2.me/submissions/a4ec7a83-04ce-424c-820e-d29acf20e055

import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_scrDiversificationSquared
import Definitions.Def_actuarial_scrCorrelationGap

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (rho a b : ℝ) : scrDiversificationSquared rho a b = 2 * scrCorrelationGap rho * a * b := by
  unfold scrDiversificationSquared scrSumSquared
    scrPairSquared scrCovarianceTerm scrCorrelationGap
  ring
