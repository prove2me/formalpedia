-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_LeftFreeze_F000
-- name    : LevyStochCalc_Brownian_LeftFreeze_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:50:35.38996+00:00
-- url     : https://prove2.me/theorems/ed4bdcec-048e-4650-9466-b834b130e83d
-- title:
--   Source declarations: LevyStochCalc.Brownian.LeftFreeze
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.LeftFreeze. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Analysis_DyadicGrid_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoAlgebraAssociativity_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoAlgebraAssociativity_F001
import Definitions.Def_LevyStochCalc_Brownian_ItoAlgebraAssociativity_F002
import Definitions.Def_LevyStochCalc_Brownian_ItoLinear_F001

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

/-- The process frozen at the left endpoints of the dyadic partition of `[0, t]` of level
`n`. -/
noncomputable def leftFreeze : SimplePredictable Ω t where
  N := 2 ^ n
  partition := dyadicPartition t n
  partition_zero := dyadicPartition_zero t n
  partition_le_T := (dyadicPartition_last t n).le
  partition_strictMono := dyadicPartition_strictMono ht n
  ξ := fun k => Y (dyadicPartition t n k.castSucc)
  ξ_bounded := fun _ => ⟨C, fun ω => hYb _ ω⟩
  ξ_measurable := fun _ => hYm _
theorem leftFreeze_adapt (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hYad : ∀ s, StronglyMeasurable[ℱ s] (Y s)) :
    ∀ i : Fin (leftFreeze Y hYb hYm ht n).N,
      StronglyMeasurable[ℱ ((leftFreeze Y hYb hYm ht n).partition i.castSucc)]
        ((leftFreeze Y hYb hYm ht n).ξ i) :=
  fun _ => hYad _
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


