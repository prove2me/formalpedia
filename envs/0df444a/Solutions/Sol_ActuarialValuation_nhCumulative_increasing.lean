-- Prove2me | solution 1 for ActuarialValuation.nhCumulative_increasing
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T17:32:34.722028+00:00
-- url     : https://prove2.me/submissions/f337f069-0f3b-46ce-a33e-f259ee005d53

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_actuarial_nhCumulative

import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (a b s t : ℝ) (ha : 0≤a) (hb : 0≤b) (hs : 0≤s) (hst : s≤t) : nhCumulative a b s≤nhCumulative a b t := by
  unfold nhCumulative
  have hts : 0 ≤ t-s := sub_nonneg.mpr hst
  have hsum : 0 ≤ t+s := by linarith
  have hprod : 0 ≤ (t-s)*(t+s) := mul_nonneg hts hsum
  have h1 : 0 ≤ a*(t-s) := mul_nonneg ha hts
  have h2 : 0 ≤ b*((t-s)*(t+s)) := mul_nonneg hb hprod
  nlinarith
