-- Prove2me | Definitions.Def_SourceProof_67abbf0ff32d832502948a1b
-- name    : SourceProof_67abbf0ff32d832502948a1b
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:27:58.868816+00:00
-- url     : https://prove2.me/theorems/2ed72261-f2a5-4162-b0b6-d13e6fd62f10
-- title:
--   StochLean source theorem: ProbabilityTheory.exists_diagonal_tendstoUCP_sub_zero

import Definitions.Def_StochLean_Probability_Process_UCP_F001
import Definitions.Def_SourceProof_38b5e68a47cd68542b624462
import Definitions.Def_SourceProof_c85f5070e7769bac711d7f66

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Simultaneous UCP diagonals on growing horizons

One index is chosen for each pair of convergent rows. Both selected errors vanish
in UCP; the construction does not require a uniform convergence rate across rows.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

theorem _root_.Prove2MeSourceProof.h_67abbf0ff32d832502948a1b
    {A B : ℕ → ℕ → ℝ≥0 → Ω → ℝ} {X Y : ℕ → ℝ≥0 → Ω → ℝ}
    (hA : ∀ n, TendstoUCP P (A n) atTop (X n))
    (hB : ∀ n, TendstoUCP P (B n) atTop (Y n)) :
    ∃ k : ℕ → ℕ, TendstoUCP P (fun n ↦ A n (k n) - X n) atTop 0 ∧
      TendstoUCP P (fun n ↦ B n (k n) - Y n) atTop 0 := by
  let a : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 1)
  have ha : ∀ n, 0 < a n := fun n ↦ by dsimp [a]; positivity
  have halim : Tendsto a atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hblim : Tendsto (fun n ↦ ENNReal.ofReal (a n)) atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero, Function.comp_def] using
      (ENNReal.continuous_ofReal.tendsto 0).comp halim
  have hAt : ∀ n : ℕ, ∃ K, ∀ k ≥ K,
      P {ω | ∃ t ≤ (n : ℝ≥0), a n < ‖A n k t ω - X n t ω‖} ≤ ENNReal.ofReal (a n) := by
    intro n
    exact ENNReal.tendsto_atTop_zero.mp
      (_root_.Prove2MeSourceProof.h_c85f5070e7769bac711d7f66.mp (hA n) n (a n) (ha n))
      (ENNReal.ofReal (a n)) (ENNReal.ofReal_pos.mpr (ha n))
  have hBt : ∀ n : ℕ, ∃ K, ∀ k ≥ K,
      P {ω | ∃ t ≤ (n : ℝ≥0), a n < ‖B n k t ω - Y n t ω‖} ≤ ENNReal.ofReal (a n) := by
    intro n
    exact ENNReal.tendsto_atTop_zero.mp
      (_root_.Prove2MeSourceProof.h_c85f5070e7769bac711d7f66.mp (hB n) n (a n) (ha n))
      (ENNReal.ofReal (a n)) (ENNReal.ofReal_pos.mpr (ha n))
  choose KA hKA using hAt
  choose KB hKB using hBt
  refine ⟨fun n ↦ max (KA n) (KB n), ?_, ?_⟩
  · exact _root_.Prove2MeSourceProof.h_38b5e68a47cd68542b624462 halim hblim
      (fun n ↦ hKA n _ (le_max_left _ _))
  · exact _root_.Prove2MeSourceProof.h_38b5e68a47cd68542b624462 halim hblim
      (fun n ↦ hKB n _ (le_max_right _ _))
end ProbabilityTheory


