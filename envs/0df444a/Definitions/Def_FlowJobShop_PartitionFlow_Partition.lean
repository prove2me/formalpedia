-- Prove2me | Definitions.Def_FlowJobShop_PartitionFlow_Partition
-- name    : FlowJobShop_PartitionFlow_Partition
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T11:01:10.978929+00:00
-- url     : https://prove2.me/theorems/7348da83-a5d6-44a7-b5e1-5aa85305cf88
-- title:
--   PARTITION: a multiset $\{a_1,\dots,a_n\}$ has a partition (p. 37)
-- statement:
--   Let $S=\{a_1,\dots,a_n\}$ be a multiset of nonnegative integers. $S$ **has a partition** if there is a subset $u$ of the indices $1,\dots,n$ with
--   $$\sum_{i\in u}a_i=\frac12\sum_{i=1}^n a_i .$$
--   The partition problem asks whether a given multiset has a partition; it is the NP-complete problem from which the paper's first reductions start.
--
--   **Formalization Note** The multiset is a function `a : Fin n → ℕ` (indices 0-based), and the condition is written without division as $2\sum_{i\in u}a_i=\sum_i a_i$ in $\mathbb N$, which is equivalent and avoids truncated division.
-- source:
--   Gonzalez, Sahni, Flowshop and Jobshop Schedules: Complexity and Approximation, Operations Research 26(1) (1978), p. 37, Partition

import Mathlib

namespace FlowJobShop.PartitionFlow

/-- PARTITION (Gonzalez–Sahni 1978, p. 37): the multiset `S = {a_1, …, a_n}` of nonnegative
integers, given as `a : Fin n → ℕ` (indices 0-based), **has a partition** if there is a subset
`u` of the indices with `∑_{i ∈ u} a_i = (∑_i a_i)/2`, written here without division as
`2 · ∑_{i ∈ u} a_i = ∑_i a_i`. -/
def HasPartition {n : ℕ} (a : Fin n → ℕ) : Prop :=
  ∃ u : Finset (Fin n), 2 * ∑ i ∈ u, a i = ∑ i, a i

end FlowJobShop.PartitionFlow


