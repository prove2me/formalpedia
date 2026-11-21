-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_SimplePredictableRefineInvariance_F003
-- name    : LevyStochCalc_Brownian_SimplePredictableRefineInvariance_F003
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T08:00:53.545236+00:00
-- url     : https://prove2.me/theorems/a345786d-9067-49d3-87ac-04035847b712
-- title:
--   Source declarations: LevyStochCalc.Brownian.SimplePredictableRefineInvariance
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.SimplePredictableRefineInvariance. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_SimplePredictableRefineInvariance_F001

open private sum_Ico_telescope_real from Definitions.Def_LevyStochCalc_Brownian_SimplePredictableRefineInvariance_F001
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Refinement of a simple predictable integrand

Refining a `SimplePredictable Ω T` onto a finer partition
(`SimplePredictable.refine`), the pointwise description of the refined
integrand (`SimplePredictable.refine_eval`), and the invariance of the simple
stochastic integral under such a refinement
(`SimplePredictable.simpleIntegral_refine`), obtained by telescoping the driving
increments over each fiber of the refining index map.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory
open scoped NNReal ENNReal

universe u
variable {Ω : Type u} [MeasurableSpace Ω]

/-- **Clamped per-fiber telescope (`min (·) t`).** Identical telescoping to
`W_telescope_via_g`, with the point function `π'` clamped to `min (π' ·) t`.
Telescoping of consecutive differences is independent of the values, so the
proof is the same `sum_Ico_telescope_real`. -/
lemma SimplePredictable.W_telescope_via_g_clamped
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {M : ℕ} (π' : Fin (M + 1) → ℝ) (ω : Ω) (t : ℝ)
    (a b : ℕ) (hab : a ≤ b) (hb_le : b ≤ M) :
    (∑ n ∈ Finset.Ico a b,
      ((fun n : ℕ => if h : n < M + 1 then W.W (min (π' ⟨n, h⟩) t) ω else 0) (n + 1)
        - (fun n : ℕ => if h : n < M + 1 then W.W (min (π' ⟨n, h⟩) t) ω else 0) n))
      = W.W (min (π' ⟨b, by omega⟩) t) ω - W.W (min (π' ⟨a, by omega⟩) t) ω := by
  rw [sum_Ico_telescope_real a b hab
    (fun n : ℕ => if h : n < M + 1 then W.W (min (π' ⟨n, h⟩) t) ω else 0)]
  have h_b_lt : b < M + 1 := by omega
  have h_a_lt : a < M + 1 := by omega
  simp only [h_b_lt, h_a_lt, dif_pos]
end LevyStochCalc.Brownian.Ito


