-- Prove2me | Definitions.Def_PHigherOrder_LocalBoundednessInput
-- name    : PHigherOrder_LocalBoundednessInput
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T20:11:08.096835+00:00
-- url     : https://prove2.me/theorems/fbbcad28-4b73-47a4-a386-5800095d4b38
-- title:
--   Local Boundedness Input
-- statement:
--   Definitions and structural lemmas for Local Boundedness Input, from na0b and contributors's pinned Higher-order estimates for planar p-harmonic functions under the stated hypotheses development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/LocalBoundednessInput.lean

import Definitions.Def_PHigherOrder_IsPHarm
set_option autoImplicit false
structure LocalBoundednessInput (p : ℝ) where
  Cb : ℝ
  Cb_pos : 0 < Cb
  bound : ∀ (u : Plane → ℝ) (g : Plane → Plane), IsPHarm p (Metric.ball 0 1) u g →
      MeasureTheory.MemLp u (ENNReal.ofReal p)
        (MeasureTheory.volume.restrict (Metric.ball (0 : Plane) 1)) →
      ∀ x ∈ Metric.ball (0 : Plane) (3 / 4),
        |u x| ≤ Cb * (MeasureTheory.eLpNorm u (ENNReal.ofReal p)
          (MeasureTheory.volume.restrict (Metric.ball (0 : Plane) 1))).toReal


