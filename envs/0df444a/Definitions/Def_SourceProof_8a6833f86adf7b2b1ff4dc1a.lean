-- Prove2me | Definitions.Def_SourceProof_8a6833f86adf7b2b1ff4dc1a
-- name    : SourceProof_8a6833f86adf7b2b1ff4dc1a
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:46:04.79379+00:00
-- url     : https://prove2.me/theorems/7bb2d86c-c778-43c8-9e61-da9e452032e0
-- title:
--   StochLean source theorem: ProbabilityTheory.eventually_uniform_deviation_bound_of_tendstoUCP_diagonals

import Definitions.Def_StochLean_Probability_Process_UCP_F001
import Definitions.Def_SourceProof_c85f5070e7769bac711d7f66

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # UCP limits through uniformly controlled approximations

Sequential control for every choice of a column gives a uniform probability
bound over all columns. This permits a double-limit argument without assuming
uniform rates of convergence for the individual rows. No measurability or
finiteness hypothesis on the measure is needed for these outer-measure bounds.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

theorem _root_.Prove2MeSourceProof.h_8a6833f86adf7b2b1ff4dc1a
    {E : ℕ → ℕ → ℝ≥0 → Ω → ℝ}
    (hE : ∀ n : ℕ → ℕ, TendstoUCP P (fun k ↦ E k (n k)) atTop 0)
    (T : ℝ≥0) {ε : ℝ} (hε : 0 < ε) {η : ℝ≥0∞} (hη : 0 < η) :
    ∀ᶠ k in atTop, ∀ n, P {ω | ∃ t ≤ T, ε < ‖E k n t ω‖} ≤ η := by
  classical
  have hchoice (k : ℕ) : ∃ n : ℕ,
      (∃ j, η < P {ω | ∃ t ≤ T, ε < ‖E k j t ω‖}) →
        η < P {ω | ∃ t ≤ T, ε < ‖E k n t ω‖} := by
    by_cases h : ∃ j, η < P {ω | ∃ t ≤ T, ε < ‖E k j t ω‖}
    · exact ⟨h.choose, fun _ ↦ h.choose_spec⟩
    · exact ⟨0, fun h' ↦ False.elim (h h')⟩
  choose n hn using hchoice
  have hu := _root_.Prove2MeSourceProof.h_c85f5070e7769bac711d7f66.mp (hE n) T ε hε
  simp only [Pi.zero_apply, sub_zero] at hu
  obtain ⟨K, hK⟩ := ENNReal.tendsto_atTop_zero.mp hu η hη
  filter_upwards [eventually_ge_atTop K] with k hk j
  by_contra h
  exact (not_lt_of_ge (hK k hk)) (hn k ⟨j, lt_of_not_ge h⟩)
end ProbabilityTheory


