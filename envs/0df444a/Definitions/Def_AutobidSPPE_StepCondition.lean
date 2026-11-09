-- Prove2me | Definitions.Def_AutobidSPPE_StepCondition
-- name    : AutobidSPPE_StepCondition
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T18:09:29.837868+00:00
-- url     : https://prove2.me/theorems/955d5719-141a-4b3c-9dc5-a3cffb5a39b1
-- title:
--   Fixed separated averaging steps (13)
-- statement:
--   With the bidders in a fixed order $1,\dots,n$, the averaging steps $\tau_1,\dots,\tau_n$ satisfy the **step condition** (13) if
--   $$
--   0<\tau_1\le 1/b_0,\qquad 0<\tau_i\le\delta\,\tau_{i-1}\quad(2\le i\le n).
--   $$
--
--   **Formalization Note** The bidder ordering is the order of `Fin n`; the paper's bidder $i$ is index $i-1$.
-- source:
--   Chen–Morgenstern–Yang, Convergent Dynamics in Second Price Autobidding Games, STOC 2027 submission (manuscript sha256 185cb93f…77659a6), Assumption 2.5, (13), p.11

import Mathlib
import Definitions.Def_AutobidSPPE_b0
import Definitions.Def_AutobidSPPE_delta

namespace AutobidSPPE

/-- The fixed separated averaging steps of Assumption 2.5 (Chen–Morgenstern–Yang, *Convergent Dynamics in Second Price Autobidding Games*, STOC 2027 submission manuscript (sha256 185cb93f…77659a6), (13), p.11):
`0 < τ₁ ≤ 1/b₀` and `0 < τᵢ ≤ δτᵢ₋₁` for `2 ≤ i ≤ n`.

**Formalization Note** The bidder ordering of Assumption 2.5 is the order of `Fin n`, and the
paper's bidder `i` is `⟨i − 1, _⟩ : Fin n` (0-based): the first clause is for index `0`, the second
relates each index `i` to `j` with `j + 1 = i`. -/
def StepCondition {n : ℕ} (vhat ρ τ : Fin n → ℝ) : Prop :=
  ∀ i : Fin n, 0 < τ i ∧ (i.val = 0 → τ i ≤ 1 / b0 vhat ρ) ∧
    ∀ j : Fin n, j.val + 1 = i.val → τ i ≤ delta vhat ρ * τ j

end AutobidSPPE


