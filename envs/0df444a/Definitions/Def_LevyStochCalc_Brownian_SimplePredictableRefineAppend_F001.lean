-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_SimplePredictableRefineAppend_F001
-- name    : LevyStochCalc_Brownian_SimplePredictableRefineAppend_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T16:03:10.851006+00:00
-- url     : https://prove2.me/theorems/de9f37fd-3090-4983-8f05-4197cc1e0eb9
-- title:
--   Source declarations: LevyStochCalc.Brownian.SimplePredictableRefineAppend
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.SimplePredictableRefineAppend. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_SimplePredictableRefineAppend_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Zero-extension of a simple predictable to a larger horizon

Appending one interval carrying the coefficient `0`
(`SimplePredictable.appendInterval`) turns a `SimplePredictable Ω T` into a
`SimplePredictable Ω T'` on a larger horizon with the same `eval`, the same
simple integral and the same adaptedness, so that two approximants on different
horizons can be compared on a common endpoint.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory
open scoped NNReal ENNReal

universe u
variable {Ω : Type u} [MeasurableSpace Ω]

/-- Adaptedness is preserved by the zero-extension. -/
lemma SimplePredictable.appendInterval_adapt
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    {T : ℝ} (H : SimplePredictable Ω T) {T' : ℝ}
    (hlt : H.partition (Fin.last H.N) < T')
    (h_adapt : ∀ i : Fin H.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (H.partition i.castSucc)) (H.ξ i)) :
    ∀ i : Fin (H.appendInterval hlt).N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ ((H.appendInterval hlt).partition i.castSucc)) ((H.appendInterval hlt).ξ i) := by
  intro i
  rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
  · rw [H.appendInterval_xi_castSucc hlt i',
        H.appendInterval_partition_castSucc hlt (Fin.castSucc i')]
    exact h_adapt i'
  · rw [H.appendInterval_xi_last hlt]; exact MeasureTheory.stronglyMeasurable_const
end LevyStochCalc.Brownian.Ito


