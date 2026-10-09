-- Prove2me | solution 1 for ActuarialValuation.multiStateTermCashflowPV_decompose
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T07:36:24.954193+00:00
-- url     : https://prove2.me/submissions/1a19a48c-24a6-49db-b60e-ccd7533ee861

import Mathlib
import Definitions.Def_actuarial_multiStateTermCashflowPV
import Definitions.Def_actuarial_occupationStageReward
import Definitions.Def_actuarial_transitionStageReward
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

open ActuarialValuation

theorem solution {S : Type*} [Fintype S] (μ : ℕ → S → ℝ) (P : ℕ → S → S → ℝ)
  (b : ℕ → S → S → ℝ) (c : ℕ → S → ℝ) (v : ℝ) (n : ℕ)
  :
  multiStateTermCashflowPV μ P b c v n =
    (∑ k ∈ Finset.range n, v ^ k * occupationStageReward (μ k) (c k)) +
    (∑ k ∈ Finset.range n, v ^ (k + 1) * transitionStageReward (μ k) (P k) (b k)) := by
  classical
  simp only [multiStateTermCashflowPV, Finset.sum_add_distrib]
