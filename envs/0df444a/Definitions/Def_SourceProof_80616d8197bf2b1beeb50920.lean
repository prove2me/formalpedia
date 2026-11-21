-- Prove2me | Definitions.Def_SourceProof_80616d8197bf2b1beeb50920
-- name    : SourceProof_80616d8197bf2b1beeb50920
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:51:40.610716+00:00
-- url     : https://prove2.me/theorems/15d6d65e-328e-4e33-bba0-045b567c4de4
-- title:
--   LevyStochCalc source module: SourceProof_80616d8197bf2b1beeb50920
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.leftFreeze_eval` comes from the `LevyStochCalc.Brownian.LeftFreeze` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_LeftFreeze_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Freezing a bounded adapted process at the left endpoints of a dyadic grid

Freezing a bounded adapted process `Y` at the left endpoints of the dyadic partition of `[0, t]`
of level `n` (`Analysis/DyadicGrid.lean`) gives a simple predictable integrand
`leftFreeze Y t n`, whose value at a time `s ∈ (0, t]` is `Y` at the left endpoint `leftPt t n s`
of the cell containing `s`. When the
frozen values converge, at every positive time and almost every sample point, to a bounded
process `Y₋`, the Itô integrals of `leftFreeze Y t n · H` converge in `L²` to the Itô integral of
`Y₋ · H`, by the difference isometry and dominated convergence.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Brownian.Ito

open LevyStochCalc.Analysis

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

section Freeze

variable (Y : ℝ → Ω → ℝ) {C : ℝ} (hYb : ∀ s ω, |Y s ω| ≤ C) (hYm : ∀ s, Measurable (Y s))
  {t : ℝ} (ht : 0 < t) (n : ℕ)


theorem _root_.Prove2MeSourceProof.h_80616d8197bf2b1beeb50920 {s : ℝ} (hs : 0 < s) (hst : s ≤ t) (ω : Ω) :
    (leftFreeze Y hYb hYm ht n).eval s ω = Y (leftPt t n s) ω := by
  change (∑ i : Fin (2 ^ n),
      if LevyStochCalc.Analysis.dyadicPartition t n i.castSucc < s ∧ s ≤ LevyStochCalc.Analysis.dyadicPartition t n i.succ
      then Y (LevyStochCalc.Analysis.dyadicPartition t n i.castSucc) ω else 0) = Y (LevyStochCalc.Analysis.leftPt t n s) ω
  set k : Fin (2 ^ n) := ⟨LevyStochCalc.Analysis.leftIdx t n s, LevyStochCalc.Analysis.leftIdx_lt ht n hs hst⟩ with hk
  have hmem : LevyStochCalc.Analysis.dyadicPartition t n k.castSucc < s ∧ s ≤ LevyStochCalc.Analysis.dyadicPartition t n k.succ := by
    refine ⟨LevyStochCalc.Analysis.leftPt_lt ht n hs, ?_⟩
    rw [LevyStochCalc.Analysis.dyadicPartition_succ]
    exact LevyStochCalc.Analysis.le_leftPt_add ht n hs
  rw [Finset.sum_eq_single k]
  · split_ifs with h
    · rfl
  · intro i _ hik
    split_ifs with h
    · rcases h with ⟨h1, h2⟩
      exfalso
      apply hik
      have hmono := LevyStochCalc.Analysis.dyadicPartition_strictMono ht n
      have hi1 : i.castSucc < k.succ := hmono.lt_iff_lt.mp (h1.trans_le hmem.2)
      have hi2 : k.castSucc < i.succ := hmono.lt_iff_lt.mp (hmem.1.trans_le h2)
      apply Fin.ext
      have e1 : (i : ℕ) < (k : ℕ) + 1 := by simpa [Fin.lt_def] using hi1
      have e2 : (k : ℕ) < (i : ℕ) + 1 := by simpa [Fin.lt_def] using hi2
      omega
    · rfl
  · intro hk'
    exact absurd (Finset.mem_univ k) hk'
end Freeze

section Limit

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
  (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
  (hp : Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
  (Y : ℝ → Ω → ℝ) {C : ℝ} (hYb : ∀ s ω, |Y s ω| ≤ C) (hYm : ∀ s, Measurable (Y s))
  (hYad : ∀ s, StronglyMeasurable[ℱ s] (Y s)) {t : ℝ} (ht : 0 < t)

end Limit

end LevyStochCalc.Brownian.Ito


