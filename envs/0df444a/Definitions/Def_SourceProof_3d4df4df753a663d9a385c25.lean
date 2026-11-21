-- Prove2me | Definitions.Def_SourceProof_3d4df4df753a663d9a385c25
-- name    : SourceProof_3d4df4df753a663d9a385c25
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T16:16:37.226722+00:00
-- url     : https://prove2.me/theorems/ba0b3102-e6a0-4d29-9a39-4aa4aa45604d
-- title:
--   LevyStochCalc source module: SourceProof_3d4df4df753a663d9a385c25
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.SimplePredictable.appendInterval_eval` comes from the `LevyStochCalc.Brownian.SimplePredictableRefineAppend` module. The staged Lean declaration includes its source proof and dependency references.
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


theorem _root_.Prove2MeSourceProof.h_3d4df4df753a663d9a385c25
    {T : ℝ} (H : SimplePredictable Ω T) {T' : ℝ}
    (hlt : H.partition (Fin.last H.N) < T') (s : ℝ) (ω : Ω) :
    (H.appendInterval hlt).eval s ω = H.eval s ω := by
  unfold LevyStochCalc.Brownian.Ito.SimplePredictable.eval
  change (∑ i : Fin (H.N + 1),
      if (Fin.snoc (α := fun _ => ℝ) H.partition T') i.castSucc < s
          ∧ s ≤ (Fin.snoc (α := fun _ => ℝ) H.partition T') i.succ
        then (Fin.snoc (α := fun _ => Ω → ℝ) H.ξ (fun _ : Ω => (0 : ℝ))) i ω else 0)
    = ∑ i : Fin H.N,
        if H.partition i.castSucc < s ∧ s ≤ H.partition i.succ then H.ξ i ω else 0
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_last, ite_self, add_zero]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [appendInterval_succ_castSucc]
  simp only [Fin.snoc_castSucc]
end LevyStochCalc.Brownian.Ito


