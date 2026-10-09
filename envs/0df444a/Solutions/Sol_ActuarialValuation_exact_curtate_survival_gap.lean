-- Prove2me | solution 1 for ActuarialValuation.exact_curtate_survival_gap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T06:13:38.8201+00:00
-- url     : https://prove2.me/submissions/1967ce31-6ad8-4e43-bbce-2cc580e1652e

import Mathlib
import Definitions.Def_actuarial_strictSurvivalEvent
import Definitions.Def_actuarial_curtateSurvivalEvent
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation
open MeasureTheory

theorem solution {Ω : Type*} (T : Ω → ℝ) (K : Ω → ℕ) (n : ℕ)
    (hKT : ∀ ω, (K ω : ℝ) ≤ T ω ∧ T ω < (K ω : ℝ) + 1)
    : (strictSurvivalEvent T n) ∪ {ω | T ω = (n : ℝ)} = (curtateSurvivalEvent K n) := by
  ext ω
  change (n : ℝ) < T ω ∨ T ω = (n : ℝ) ↔ n ≤ K ω
  constructor
  · rintro (hs | hb)
    · by_contra hk
      have hn : K ω < n := Nat.lt_of_not_ge hk
      have hkn : K ω + 1 ≤ n := Nat.succ_le_iff.mpr hn
      have hr : (K ω : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hkn
      have hu := (hKT ω).2
      linarith
    · by_contra hk
      have hn : K ω < n := Nat.lt_of_not_ge hk
      have hkn : K ω + 1 ≤ n := Nat.succ_le_iff.mpr hn
      have hr : (K ω : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hkn
      have hu := (hKT ω).2
      linarith
  · intro hk
    have hreal : (n : ℝ) ≤ (K ω : ℝ) := by exact_mod_cast hk
    have hnT : (n : ℝ) ≤ T ω := le_trans hreal (hKT ω).1
    rcases eq_or_lt_of_le hnT with heq | hlt
    · exact Or.inr heq.symm
    · exact Or.inl hlt
