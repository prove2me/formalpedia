-- Prove2me | solution 1 for ActuarialValuation.nhTransition_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T17:40:22.828521+00:00
-- url     : https://prove2.me/submissions/2fa516b2-2c78-4a38-9f71-f84267970d19

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_actuarial_nhTransition

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (a b p s t : ℝ) (ha : 0≤a) (hb : 0≤b) (hp0 : 0≤p) (hp1 : p≤1) (hs : 0≤s) (hst : s≤t) (i j : Fin 3) : 0≤nhTransition a b p s t i j := by
  have hcum : 0 ≤ nhCumulative a b t - nhCumulative a b s := by
    unfold nhCumulative
    have hts : 0 ≤ t-s := sub_nonneg.mpr hst
    have hsum : 0 ≤ t+s := by linarith
    have hprod : 0 ≤ (t-s)*(t+s) := mul_nonneg hts hsum
    have h1 : 0 ≤ a*(t-s) := mul_nonneg ha hts
    have h2 : 0 ≤ b*((t-s)*(t+s)) := mul_nonneg hb hprod
    nlinarith
  have hsurv : 0 ≤ nhSurvival a b s t := by
    unfold nhSurvival
    exact le_of_lt (Real.exp_pos _)
  have hle : nhSurvival a b s t ≤ 1 := by
    unfold nhSurvival
    exact Real.exp_le_one_iff.mpr (by linarith)
  have he1 : 0 ≤ nhExitOne a b p s t := by
    unfold nhExitOne
    exact mul_nonneg hp0 (sub_nonneg.mpr hle)
  have he2 : 0 ≤ nhExitTwo a b p s t := by
    unfold nhExitTwo
    exact mul_nonneg (sub_nonneg.mpr hp1) (sub_nonneg.mpr hle)
  by_cases hi : i = 0
  · by_cases hj0 : j = 0
    · simpa [nhTransition, hi, hj0] using hsurv
    · by_cases hj1 : j = 1
      · simpa [nhTransition, hi, hj0, hj1] using he1
      · simpa [nhTransition, hi, hj0, hj1] using he2
  · simp only [nhTransition, if_neg hi]
    split_ifs <;> norm_num
