-- Prove2me | solution 1 for ActuarialValuation.svCdf_monotone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:53:20.460337+00:00
-- url     : https://prove2.me/submissions/a5707131-285b-458a-ad10-faaacd91f122

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_actuarial_svCdf

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (Ω : Type*) [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω) (T : Ω → ℝ) (s t : ℝ) (hst : s ≤ t) : svCdf μ T s ≤ svCdf μ T t := by
  unfold svCdf
  apply MeasureTheory.measure_mono
  intro ω hω
  exact le_trans hω hst
