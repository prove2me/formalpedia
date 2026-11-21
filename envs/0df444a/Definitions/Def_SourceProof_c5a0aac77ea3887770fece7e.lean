-- Prove2me | Definitions.Def_SourceProof_c5a0aac77ea3887770fece7e
-- name    : SourceProof_c5a0aac77ea3887770fece7e
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T16:22:57.304642+00:00
-- url     : https://prove2.me/theorems/7c67383c-8b18-4924-b1ee-56be818b6ff9
-- title:
--   LevyStochCalc source module: SourceProof_c5a0aac77ea3887770fece7e
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.SimplePredictable.appendInterval_simpleIntegral` comes from the `LevyStochCalc.Brownian.SimplePredictableRefineAppend` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Batteries.Tactic.OpenPrivate
import Definitions.Def_LevyStochCalc_Brownian_SimplePredictableRefineAppend_F000

open private appendInterval_succ_castSucc from Definitions.Def_LevyStochCalc_Brownian_SimplePredictableRefineAppend_F000
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


theorem _root_.Prove2MeSourceProof.h_c5a0aac77ea3887770fece7e
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {T : ℝ} (H : SimplePredictable Ω T) {T' : ℝ}
    (hlt : H.partition (Fin.last H.N) < T') (t : ℝ) (ω : Ω) :
    simpleIntegral W (H.appendInterval hlt) t ω = simpleIntegral W H t ω := by
  unfold LevyStochCalc.Brownian.Ito.simpleIntegral
  change (∑ i : Fin (H.N + 1),
      (Fin.snoc (α := fun _ => Ω → ℝ) H.ξ (fun _ : Ω => (0 : ℝ))) i ω
        * (W.W (min ((Fin.snoc (α := fun _ => ℝ) H.partition T') i.succ) t) ω
            - W.W (min ((Fin.snoc (α := fun _ => ℝ) H.partition T') i.castSucc) t) ω))
    = ∑ i : Fin H.N, H.ξ i ω
        * (W.W (min (H.partition i.succ) t) ω - W.W (min (H.partition i.castSucc) t) ω)
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_last, zero_mul, add_zero]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [appendInterval_succ_castSucc]
  simp only [Fin.snoc_castSucc]
end LevyStochCalc.Brownian.Ito


