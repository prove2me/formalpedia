-- Prove2me | Definitions.Def_PHigherOrder_FirstOrderEstimateInput
-- name    : PHigherOrder_FirstOrderEstimateInput
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T20:10:35.620612+00:00
-- url     : https://prove2.me/theorems/269c118e-d38b-4b35-9862-a84db1178617
-- title:
--   First Order Estimate Input
-- statement:
--   Definitions and structural lemmas for First Order Estimate Input, from na0b and contributors's pinned Higher-order estimates for planar p-harmonic functions under the stated hypotheses development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/FirstOrderEstimateInput.lean

import Definitions.Def_PHigherOrder_IsPHarm
set_option autoImplicit false
structure FirstOrderEstimateInput (p : ℝ) where
  kappa : ℝ
  C₀ : ℝ
  kappa_pos : 0 < kappa
  kappa_lt_one : kappa < 1
  C₀_pos : 0 < C₀
  est : ∀ (v : Plane → ℝ) (g : Plane → Plane), IsPHarm p (Metric.ball 0 1) v g →
      (∀ x ∈ Metric.ball (0 : Plane) 1, |v x| ≤ 1) →
      ContDiffOn ℝ 1 v (Metric.ball 0 (3 / 4)) ∧
      (∀ x ∈ Metric.ball (0 : Plane) (3 / 4), ‖gradient v x‖ ≤ C₀) ∧
      (∀ x ∈ Metric.ball (0 : Plane) (3 / 4), ∀ y ∈ Metric.ball (0 : Plane) (3 / 4),
        ‖gradient v x - gradient v y‖ ≤ C₀ * ‖x - y‖ ^ kappa)


