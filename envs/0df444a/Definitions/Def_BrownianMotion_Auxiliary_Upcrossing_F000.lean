-- Prove2me | Definitions.Def_BrownianMotion_Auxiliary_Upcrossing_F000
-- name    : BrownianMotion_Auxiliary_Upcrossing_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T17:06:55.53092+00:00
-- url     : https://prove2.me/theorems/357b5d5e-5ae0-4b5e-b2e5-1e96c7cc61f6
-- title:
--   Source declarations: BrownianMotion.Auxiliary.Upcrossing
-- statement:
--   Source-preserving Lean declaration bundle from BrownianMotion.Auxiliary.Upcrossing, retaining definitions, helper results, proofs and elaboration context where present.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Mathlib.Probability.Martingale.Upcrossing

/-
Copyright (c) 2026 Rohit Manokaran. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohit Manokaran
-/

@[expose] public section

namespace MeasureTheory

variable {ι Ω β : Type*} {mΩ : MeasurableSpace Ω}
  {f g : ℕ → Ω → ℝ} {a b : ℝ} {N : ℕ} {ω : Ω}

@[simp]
lemma hittingBtwn_self [ConditionallyCompletePartialOrderInf ι]
    (f : ι → Ω → β) (s : Set β) (n : ι) (ω : Ω) :
    hittingBtwn f s n n ω = n := by
  rw [hittingBtwn]
  simp only [Set.Icc_self, Set.mem_singleton_iff, exists_eq_left, ite_eq_right_iff]
  intro h
  simp [h]
/-- `hittingBtwn` only depends on the hitting predicate. -/
lemma hittingBtwn_congr {s : Set ℝ}
    (h : ∀ i ω, f i ω ∈ s ↔ g i ω ∈ s) (n m : ℕ) :
    hittingBtwn f s n m = hittingBtwn g s n m := by
  ext
  unfold hittingBtwn
  congr <;> ext <;> simp [h]
/-- Upper crossing times only depend on the position of the process relative to `a` and `b`. -/
lemma upperCrossingTime_congr
    (hIic : ∀ i ω, f i ω ≤ a ↔ g i ω ≤ a) (hIci : ∀ i ω, b ≤ f i ω ↔ b ≤ g i ω) (n : ℕ) :
    upperCrossingTime a b f N n = upperCrossingTime a b g N n := by
  have hIic' : ∀ i ω, f i ω ∈ Set.Iic a ↔ g i ω ∈ Set.Iic a := hIic
  have hIci' : ∀ i ω, f i ω ∈ Set.Ici b ↔ g i ω ∈ Set.Ici b := hIci
  induction n with
  | zero => rfl
  | succ n ih =>
    ext ω
    rw [upperCrossingTime_succ_eq, upperCrossingTime_succ_eq, lowerCrossingTime,
      lowerCrossingTime, ih, hittingBtwn_congr hIic', hittingBtwn_congr hIci']
/-- Lower crossing times only depend on the position of the process relative to `a` and `b`. -/
lemma lowerCrossingTime_congr
    (hIic : ∀ i ω, f i ω ≤ a ↔ g i ω ≤ a) (hIci : ∀ i ω, b ≤ f i ω ↔ b ≤ g i ω) (n : ℕ) :
    lowerCrossingTime a b f N n = lowerCrossingTime a b g N n := by
  ext ω
  rw [lowerCrossingTime, lowerCrossingTime, upperCrossingTime_congr hIic hIci,
    hittingBtwn_congr hIic]
lemma upcrossingStrat_congr
    (hIic : ∀ i ω, f i ω ≤ a ↔ g i ω ≤ a) (hIci : ∀ i ω, b ≤ f i ω ↔ b ≤ g i ω) (n : ℕ) :
    upcrossingStrat a b f N n = upcrossingStrat a b g N n := by
  ext ω
  simp_rw [upcrossingStrat, upperCrossingTime_congr hIic hIci, lowerCrossingTime_congr hIic hIci]
lemma upcrossingsBefore_congr
    (hIic : ∀ i ω, f i ω ≤ a ↔ g i ω ≤ a) (hIci : ∀ i ω, b ≤ f i ω ↔ b ≤ g i ω) :
    upcrossingsBefore a b f N ω = upcrossingsBefore a b g N ω := by
  simp_rw [upcrossingsBefore, upperCrossingTime_congr hIic hIci]
end MeasureTheory


