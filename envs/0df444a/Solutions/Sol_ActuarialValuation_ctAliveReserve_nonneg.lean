-- Prove2me | solution 1 for ActuarialValuation.ctAliveReserve_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T17:25:05.195569+00:00
-- url     : https://prove2.me/submissions/17122a76-8542-4f1a-8316-8a09d95269c2

import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_ctRiskRate
import Definitions.Def_actuarial_ctInsuranceFlow
import Definitions.Def_actuarial_ctAliveReserve

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (delta mu b death maturity t : ℝ) (hr : 0 < ctRiskRate delta mu) (hb : 0 ≤ ctInsuranceFlow b mu death) (ht : t ≤ maturity) : 0 ≤ ctAliveReserve delta mu b death maturity t := by
  unfold ctAliveReserve
  apply mul_nonneg
  · exact div_nonneg hb (le_of_lt hr)
  · have hm : 0 ≤ ctRiskRate delta mu * (maturity - t) :=
        mul_nonneg (le_of_lt hr) (sub_nonneg.mpr ht)
    have he : Real.exp (-(ctRiskRate delta mu) * (maturity-t)) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      nlinarith
    linarith
