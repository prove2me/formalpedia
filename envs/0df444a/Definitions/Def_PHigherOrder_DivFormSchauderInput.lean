-- Prove2me | Definitions.Def_PHigherOrder_DivFormSchauderInput
-- name    : PHigherOrder_DivFormSchauderInput
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T20:10:07.68641+00:00
-- url     : https://prove2.me/theorems/f1eed4aa-a0e9-488f-bffb-8e4158058732
-- title:
--   Div Form Schauder Input
-- statement:
--   Definitions and structural lemmas for Div Form Schauder Input, from na0b and contributors's pinned Higher-order estimates for planar p-harmonic functions under the stated hypotheses development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/DivFormSchauderInput.lean

import Definitions.Def_PHigherOrder_IsLinearDivSol
set_option autoImplicit false
structure DivFormSchauderInput : Prop where
  schauder : ∀ (j : ℕ) (κ lam Lam M r r' : ℝ),
      0 < κ → κ < 1 → 0 < lam → lam ≤ Lam → 0 < M → 0 < r' → r' < r →
      ∃ C > 0, ∀ (A : Plane → (Plane →L[ℝ] Plane)) (w : Plane → ℝ) (G : Plane → Plane),
        (∀ x ∈ Metric.ball (0 : Plane) r, ∀ ξ : Plane,
            lam * ‖ξ‖ ^ 2 ≤ inner ℝ (A x ξ) ξ ∧ ‖A x ξ‖ ≤ Lam * ‖ξ‖) →
        ContDiffOn ℝ (j : ℕ∞) A (Metric.ball 0 r) →
        (∀ i ≤ j, ∀ x ∈ Metric.ball (0 : Plane) r, ‖iteratedFDeriv ℝ i A x‖ ≤ M) →
        (∀ x ∈ Metric.ball (0 : Plane) r, ∀ y ∈ Metric.ball (0 : Plane) r,
            ‖iteratedFDeriv ℝ j A x - iteratedFDeriv ℝ j A y‖ ≤ M * ‖x - y‖ ^ κ) →
        IsLinearDivSol (Metric.ball 0 r) A w G →
        (∀ x ∈ Metric.ball (0 : Plane) r, |w x| ≤ 1) →
        ContDiffOn ℝ ((j + 1 : ℕ) : ℕ∞) w (Metric.ball 0 r') ∧
        (∀ i ≤ j + 1, ∀ x ∈ Metric.ball (0 : Plane) r', ‖iteratedFDeriv ℝ i w x‖ ≤ C) ∧
        (∀ x ∈ Metric.ball (0 : Plane) r', ∀ y ∈ Metric.ball (0 : Plane) r',
            ‖iteratedFDeriv ℝ (j + 1) w x - iteratedFDeriv ℝ (j + 1) w y‖ ≤ C * ‖x - y‖ ^ κ)


