-- Prove2me | Definitions.Def_PHigherOrder_IMRegularityInput
-- name    : PHigherOrder_IMRegularityInput
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T20:10:20.941998+00:00
-- url     : https://prove2.me/theorems/80c27032-a1e9-405a-a8f4-03d6cf49c964
-- title:
--   IMRegularity Input
-- statement:
--   Definitions and structural lemmas for IMRegularity Input, from na0b and contributors's pinned Higher-order estimates for planar p-harmonic functions under the stated hypotheses development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/IMRegularityInput.lean

import Definitions.Def_PHigherOrder_IsPHarm
import Definitions.Def_PHigherOrder_SOpt
set_option autoImplicit false
structure IMRegularityInput (p : ℝ) : Prop where
  reg : ∀ (Ω : Set Plane) (u : Plane → ℝ) (g : Plane → Plane),
      IsPHarm p Ω u g →
      ∀ (k : ℕ) (β : ℝ), 0 < β → β < 1 → (k : ℝ) + β < SOpt p →
      ∀ x₀ ∈ Ω, ∃ r > 0, ∃ C > 0, Metric.ball x₀ r ⊆ Ω ∧
        ContDiffOn ℝ (k : ℕ∞) u (Metric.ball x₀ r) ∧
        ∀ x ∈ Metric.ball x₀ r, ∀ y ∈ Metric.ball x₀ r,
          ‖iteratedFDeriv ℝ k u x - iteratedFDeriv ℝ k u y‖ ≤ C * ‖x - y‖ ^ β


