-- Prove2me | Definitions.Def_SourceProof_ff61f6e818da41b2b20b8dc5
-- name    : SourceProof_ff61f6e818da41b2b20b8dc5
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:42:04.656888+00:00
-- url     : https://prove2.me/theorems/7c2903a2-e3a4-503e-8f15-4a9138b48253
-- title:
--   StochLean source theorem: ProbabilityTheory.IsContinuousLocalMartingale.exists_bounded_fundamentalSequence

import Definitions.Def_SourceProof_0feb9d2237bb25262c913342
import Definitions.Def_SourceProof_268eb95cb654b94024942d81
import Definitions.Def_SourceProof_619a18497398a378d9ad0e1b
import Definitions.Def_SourceProof_ae5a010f00e486e1966df2cd
import Definitions.Def_SourceProof_d5b15f96b9cae3c9fe969458
import Definitions.Def_SourceProof_f84942774fa9217e287c6136
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Continuous local martingales are locally square integrable

The canonical Protter mask handles arbitrary finite, possibly nonintegrable initial values.
Intersect the centered level localizer with the initial-value localizer. Each masked stopped
process is bounded, UI, and square integrable at every finite time. No unmasked L2 assertion
is made without the necessary initial-value hypothesis.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ} [IsFiniteMeasure P] [SigmaFiniteFiltration P F]

namespace IsContinuousLocalMartingale
theorem _root_.Prove2MeSourceProof.h_ff61f6e818da41b2b20b8dc5
    (hX : IsContinuousLocalMartingale X F P) (hF : F.IsUsual P) :
    ∃ σ : ℕ → Ω → WithTop ℝ≥0, IsFundamentalSequence X F P σ ∧
      ∀ n, (∀ᵐ ω ∂P, ∀ t, ‖MeasureTheory.stoppedProcess
        (fun s ↦ {ω | 0 < σ n ω}.indicator (X s)) (σ n) t ω‖ ≤ (n : ℝ) + n) ∧
        IsSquareIntegrableMartingale (MeasureTheory.stoppedProcess
          (fun s ↦ {ω | 0 < σ n ω}.indicator (X s)) (σ n)) F P := by
  obtain ⟨τ, hτ, hb⟩ := (_root_.Prove2MeSourceProof.h_f84942774fa9217e287c6136 hX) hF
  let σ : ℕ → Ω → WithTop ℝ≥0 := ProbabilityTheory.initialValueLocalizer (X 0) ⊓ τ
  have hstop : ∀ n, IsStoppingTime F (σ n) := fun n ↦
    (_root_.Prove2MeSourceProof.h_268eb95cb654b94024942d81 (hX.1.1 0) n).min (hτ.1.isStoppingTime n)
  have hmono : Monotone σ := (_root_.Prove2MeSourceProof.h_619a18497398a378d9ad0e1b (X 0)).inf hτ.2.1
  have hpre : IsPreLocalizingSequence F σ P := ⟨hstop, by
    filter_upwards [hτ.1.tendsto_top] with ω hω
    exact (_root_.Prove2MeSourceProof.h_ae5a010f00e486e1966df2cd (X 0) ω).min hω⟩
  have hbound : ∀ n, ∀ᵐ ω ∂P, ∀ t, ‖MeasureTheory.stoppedProcess
      (fun s ↦ {ω | 0 < σ n ω}.indicator (X s)) (σ n) t ω‖ ≤ (n : ℝ) + n := by
    intro n
    filter_upwards [(hb n).1] with ω hω t
    rw [stoppedProcess_indicator_comm]
    by_cases hp : 0 < σ n ω
    · rw [indicator_of_mem (show ω ∈ {ω | 0 < σ n ω} from hp)]
      have hi : |X 0 ω| ≤ (n : ℝ) := by
        by_contra hn
        have hle : σ n ω ≤ ProbabilityTheory.initialValueLocalizer (X 0) n ω := min_le_left _ _
        simp only [ProbabilityTheory.initialValueLocalizer, if_neg hn] at hle
        exact (not_le.mpr hp) hle
      let u : ℝ≥0 := (min (t : WithTop ℝ≥0) (σ n ω)).untopA
      have hne : min (t : WithTop ℝ≥0) (σ n ω) ≠ ⊤ :=
        ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _)
      have hu : (u : WithTop ℝ≥0) ≤ τ n ω := by
        dsimp only [u]
        rw [WithTop.untopA_eq_untop hne, WithTop.coe_untop]
        exact (min_le_right _ _).trans (min_le_right _ _)
      have hc : ‖X u ω - X 0 ω‖ ≤ (n : ℝ) := by
        simpa only [stoppedProcess_eq_of_le hu] using hω u
      change ‖X u ω‖ ≤ (n : ℝ) + n
      calc
        ‖X u ω‖ = ‖(X u ω - X 0 ω) + X 0 ω‖ := by rw [sub_add_cancel]
        _ ≤ ‖X u ω - X 0 ω‖ + ‖X 0 ω‖ := norm_add_le _ _
        _ ≤ (n : ℝ) + n := add_le_add hc (by simpa only [Real.norm_eq_abs] using hi)
    · rw [indicator_of_notMem (show ω ∉ {ω | 0 < σ n ω} from hp), norm_zero]
      positivity
  have hui : ∀ n, ProbabilityTheory.IsUIMartingale (MeasureTheory.stoppedProcess
      (fun s ↦ {ω | 0 < σ n ω}.indicator (X s)) (σ n)) F P := fun n ↦
    (_root_.Prove2MeSourceProof.h_d5b15f96b9cae3c9fe969458 ((_root_.Prove2MeSourceProof.h_0feb9d2237bb25262c913342 hX.1) hF (hstop n))) (n + n) (hbound n)
  refine ⟨σ, ⟨hpre, hmono, hui⟩, fun n ↦ ⟨hbound n, (hui n).1, fun t ↦ ?_⟩⟩
  exact MemLp.of_bound ((hui n).1.integrable t).aestronglyMeasurable ((n : ℝ) + n)
    ((hbound n).mono fun _ hω ↦ hω t)
end IsContinuousLocalMartingale

end ProbabilityTheory


