-- Prove2me | Definitions.Def_JohnsonFlowShop_TwoStage_asapStart1
-- name    : JohnsonFlowShop_TwoStage_asapStart1
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T10:36:14.201232+00:00
-- url     : https://prove2.me/theorems/d1d62cad-2eab-4f09-9be7-1ad30ab0c7fa
-- title:
--   Machine-1 start times of the as-soon-as-possible schedule of an order (p. 62)
-- statement:
--   Items are indexed by $i \in \{0,\dots,n-1\}$ (the paper's items $1,\dots,n$ shifted by one), and an order is a permutation $\sigma$ of the items with $\sigma(k)$ the item processed in position $k$ (positions $0,\dots,n-1$). In the **as-soon-as-possible schedule** of $\sigma$ there are no delays on the first machine: the item in position $k$ starts on machine 1 as soon as the items in positions $0,\dots,k-1$ are finished, so item $i$, in position $k = \sigma^{-1}(i)$, starts at
--   $$
--   s^1_i = \sum_{l < \sigma^{-1}(i)} A_{\sigma(l)} .
--   $$
--   Together with the machine-2 start times (`asapStart2`) this is the schedule Johnson's rule outputs.
-- source:
--   Johnson, Optimal Two- and Three-Stage Production Schedules with Setup Times Included, NRLQ 1(1) 1954, p. 62, Two-stage production schedule ("we may start each item as soon as possible ... Thus there are no delay times on the first stage")

import Mathlib

namespace JohnsonFlowShop.TwoStage

/-- Start times on machine 1 of the as-soon-as-possible schedule of the order `σ`
(`σ k` = item in position `k`): the item in position `k` starts on machine 1 when the items
in the positions before `k` are finished, i.e. at `∑_{l < k} A (σ l)`; there are no delays
on the first machine. -/
def asapStart1 {n : ℕ} (A : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) (i : Fin n) : ℝ :=
  ∑ l ∈ Finset.Iio (σ.symm i), A (σ l)

end JohnsonFlowShop.TwoStage


