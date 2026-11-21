-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_LeftFreeze_F001
-- name    : LevyStochCalc_Brownian_LeftFreeze_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:53:32.261173+00:00
-- url     : https://prove2.me/theorems/e51aebb9-96d3-4594-bd86-1fe832f4a084
-- title:
--   Source declarations: LevyStochCalc.Brownian.LeftFreeze
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.LeftFreeze. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_LeftFreeze_F000
import Definitions.Def_SourceProof_80616d8197bf2b1beeb50920

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

/-- The frozen process is bounded by the bound of `Y` on `(0, t]`. -/
theorem abs_leftFreeze_eval_le {s : ℝ} (hs : 0 < s) (hst : s ≤ t) (ω : Ω) :
    |(leftFreeze Y hYb hYm ht n).eval s ω| ≤ C := by
  rw [_root_.Prove2MeSourceProof.h_80616d8197bf2b1beeb50920 Y hYb hYm ht n hs hst]
  exact hYb _ ω
/-- The elementary integral of the frozen process against a process is the sum of the frozen
values times the increments of the process over the cells. -/
theorem leftFreeze_integralAgainst (M : ℝ → Ω → ℝ) (ω : Ω) :
    (leftFreeze Y hYb hYm ht n).integralAgainst M t ω
      = ∑ k : Fin (2 ^ n), Y (dyadicPartition t n k.castSucc) ω
          * (M (dyadicPartition t n k.succ) ω - M (dyadicPartition t n k.castSucc) ω) := by
  unfold SimplePredictable.integralAgainst
  dsimp only [leftFreeze]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [min_eq_left (dyadicPartition_le ht n _), min_eq_left (dyadicPartition_le ht n _)]
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


