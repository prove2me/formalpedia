-- Prove2me | solution 1 for ActuarialValuation.multiStateTermCashflowPV_zero_term
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T07:36:18.963978+00:00
-- url     : https://prove2.me/submissions/96640ebb-fc44-4a7c-94e1-d307c4987133

import Mathlib
import Definitions.Def_actuarial_multiStateTermCashflowPV
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

open ActuarialValuation

theorem solution {S : Type*} [Fintype S] (μ : ℕ → S → ℝ) (P : ℕ → S → S → ℝ)
  (b : ℕ → S → S → ℝ) (c : ℕ → S → ℝ) (v : ℝ) 
  :
  multiStateTermCashflowPV μ P b c v 0 = 0 := by
  classical
  simp [multiStateTermCashflowPV]
