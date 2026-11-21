-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionCompensator_F001
-- name    : LevyStochCalc_Brownian_ItoL2CompletionCompensator_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:04:57.014864+00:00
-- url     : https://prove2.me/theorems/0f49127f-102a-494f-8842-02e9eaf356f9
-- title:
--   LevyStochCalc source module: LevyStochCalc.Brownian.ItoL2CompletionCompensator
-- statement:
--   Exact source-faithful declarations from LevyStochCalc.Brownian.ItoL2CompletionCompensator in the pinned LevyStochCalc project.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionConvergence_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionConvergence_F002
import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionConvergence_F003

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Brownian Itô integral: the compensated square of a simple integral

Weighted off-diagonal vanishing for products of Brownian increments, the clamped
expansion of the square of a difference of simple integrals, and the martingale
property of the compensated square
`(simpleIntegral W H t)² − ∫_{[0, t]} (H.eval u)² du` with respect to the
filtration `ℱ`.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory
open scoped NNReal ENNReal

universe u
variable {Ω : Type u} [MeasurableSpace Ω]

/-- **Clamped-increment identity.** For `s ≤ t`,
`simpleIntegral W H t − simpleIntegral W H s = ∑ᵢ ξᵢ·(W_{cᵢ₊₁} − W_{cᵢ})` where
`cᵢ = max s (min pᵢ t)` clamps the partition points into `[s, t]`. The increment
of the simple integral between `s` and `t` rebuilds as a single sum of increments
over the `[s,t]`-clamped partition — the starting point for the conditional
(set-level) Itô isometry. -/
lemma simpleIntegral_sub_eq_clamp_sum
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {T : ℝ} (H : SimplePredictable Ω T) {s t : ℝ} (hst : s ≤ t) (ω : Ω) :
    simpleIntegral W H t ω - simpleIntegral W H s ω
      = ∑ i : Fin H.N, H.ξ i ω * (W.W (max s (min (H.partition i.succ) t)) ω
          - W.W (max s (min (H.partition i.castSucc) t)) ω) := by
  have key : ∀ p : ℝ,
      W.W (min p t) ω - W.W (min p s) ω = W.W (max s (min p t)) ω - W.W s ω := by
    intro p
    rcases le_or_gt s p with hsp | hps
    · rw [min_eq_right hsp, max_eq_right (le_min hsp hst)]
    · rw [min_eq_left (le_of_lt hps), min_eq_left (le_of_lt (lt_of_lt_of_le hps hst)),
        max_eq_left (le_of_lt hps), sub_self, sub_self]
  unfold simpleIntegral
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have e1 := key (H.partition i.succ)
  have e2 := key (H.partition i.castSucc)
  rw [← mul_sub]
  congr 1
  rw [show W.W (min (H.partition i.succ) t) ω - W.W (min (H.partition i.castSucc) t) ω
        - (W.W (min (H.partition i.succ) s) ω - W.W (min (H.partition i.castSucc) s) ω)
      = (W.W (min (H.partition i.succ) t) ω - W.W (min (H.partition i.succ) s) ω)
        - (W.W (min (H.partition i.castSucc) t) ω
            - W.W (min (H.partition i.castSucc) s) ω) from by ring]
  rw [e1, e2]; ring
end LevyStochCalc.Brownian.Ito


