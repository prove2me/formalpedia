-- Prove2me | Definitions.Def_JohnsonFlowShop_TwoStage_FollowsOrder
-- name    : JohnsonFlowShop_TwoStage_FollowsOrder
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T10:35:52.35936+00:00
-- url     : https://prove2.me/theorems/79a77f8e-3c33-45b9-886d-80a81b5a108e
-- title:
--   A schedule processes the items in the same order $\sigma$ on both machines
-- statement:
--   Items are indexed by $i \in \{0,\dots,n-1\}$ (the paper's items $1,\dots,n$ shifted by one), and an order is a permutation $\sigma$ of the items with $\sigma(k)$ the item processed in position $k$ (positions $0,\dots,n-1$). A two-machine schedule with start times $s^1, s^2$ and processing times $A, B$ **follows the order** $\sigma$ when, for all positions $k < l$,
--   $$
--   s^1_{\sigma(k)} + A_{\sigma(k)} \le s^1_{\sigma(l)} \quad\text{and}\quad s^2_{\sigma(k)} + B_{\sigma(k)} \le s^2_{\sigma(l)},
--   $$
--   that is, on each machine the item in an earlier position is finished before the item in a later position starts.
--
--   This is the notion of "the same production sequence on both machines" in Lemma 1.
-- source:
--   Johnson, Optimal Two- and Three-Stage Production Schedules with Setup Times Included, NRLQ 1(1) 1954, p. 61, Lemma 1 ("the production sequence on either machine")

import Mathlib

namespace JohnsonFlowShop.TwoStage

/-- A two-machine schedule `(s₁, s₂)` processes the items in the order `σ` on both machines
(`σ k` is the item in position `k`, positions `0` to `n` minus one): whenever position `k` comes
before position `l`, item `σ k` completes on each machine before item `σ l` starts there. -/
def FollowsOrder {n : ℕ} (A B : Fin n → ℝ) (s₁ s₂ : Fin n → ℝ)
    (σ : Equiv.Perm (Fin n)) : Prop :=
  ∀ k l : Fin n, k < l →
    s₁ (σ k) + A (σ k) ≤ s₁ (σ l) ∧ s₂ (σ k) + B (σ k) ≤ s₂ (σ l)

end JohnsonFlowShop.TwoStage


