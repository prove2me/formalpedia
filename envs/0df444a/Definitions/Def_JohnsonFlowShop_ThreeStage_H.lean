-- Prove2me | Definitions.Def_JohnsonFlowShop_ThreeStage_H
-- name    : JohnsonFlowShop_ThreeStage_H
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T16:44:37.04899+00:00
-- url     : https://prove2.me/theorems/e32b28a4-9a34-4e3e-93fe-29925e84708c
-- title:
--   Johnson's quantity $H_v$ of an order
-- statement:
--   For an ordering $\sigma$ of the items, with $\sigma(l)$ the item in position $l$, and a position $v$, set
--
--   $$
--   H_v = \sum_{l \le v} B_{\sigma(l)} - \sum_{l < v} C_{\sigma(l)} .
--   $$
--
--   In Johnson's 1-based notation, for the sequence $1, 2, \dots, n$, this is $H_v = \sum_{i=1}^{v} B_i - \sum_{i=1}^{v-1} C_i$.
--
--   **Formalization Note** Positions are 0-based (`Fin n`): the Lean value at position $v$ is the paper's $H_{v+1}$.
-- source:
--   Johnson, Optimal Two- and Three-Stage Production Schedules with Setup Times Included, NRLQ 1(1) 1954, p. 66, Three-stage production schedule, definition of H_v

import Mathlib

namespace JohnsonFlowShop.ThreeStage

/-- Johnson's quantity `H_v` for the order `σ`, with 0-based positions: for position `v`,
`H v = ∑_{l ≤ v} B (σ l) - ∑_{l < v} C (σ l)`. In the paper's 1-based indexing this is
`H_{v+1} = Σ_{i=1}^{v+1} B_i - Σ_{i=1}^{v} C_i` for the sequence `σ`. -/
def H {n : ℕ} (B C : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) (v : Fin n) : ℝ :=
  ∑ l ∈ Finset.Iic v, B (σ l) - ∑ l ∈ Finset.Iio v, C (σ l)

end JohnsonFlowShop.ThreeStage


