-- Prove2me | Definitions.Def_AlmostMMS_OrderedInstance
-- name    : AlmostMMS_OrderedInstance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:47:38.218953+00:00
-- url     : https://prove2.me/theorems/19678186-dce5-4b4e-8079-361eb880dc57
-- title:
--   Assumption 1, p.3 — ordered instance with MMS bundles of value one
-- statement:
--   An **ordered instance** has $n$ agents, items $e_1,\dots,e_m$ and an integer $d$. Each agent $i$ has item values $v_i(e)\in[0,1]$ that are non-increasing along the common order, $v_i(e_1)\ge\dots\ge v_i(e_m)$, and a partition $B_i=(B_{i,1},\dots,B_{i,d})$ of the items into $d$ **MMS bundles** with
--   $$
--   \sum_{e\in B_{i,j}} v_i(e)=1\qquad\text{for all } i,\ j.
--   $$
--   This is the standing setting of Sections 3 to 5 of the paper. Every profile below is read off the bundles, which is why they are part of the data.
--
--   **Formalization Note** The item $e_j$ is the position $j-1$ in `Fin m`, and $e\in[\ell]$ is `e.val < ℓ`.
-- source:
--   Feige, Grinberg, Almost-MMS allocations with small agent redundancy, STOC 2027 submission, arXiv:2611.05360 (manuscript sha256 3925c4ab…), Assumption 1, p.3

import Mathlib

namespace AlmostMMS

open Finset

/-- **Ordered instance** (Assumption 1, p.3; Definition 3.4, p.22, for the role of the bundles).
Feige, Grinberg, STOC 2027 submission, arXiv:2611.05360 (manuscript sha256 3925c4ab…).

`n` agents, `m` items `e₁, …, e_m` and `d` MMS bundles per agent. Item values lie in `[0, 1]`, every
agent's values are non-increasing along the common item order, and each agent's `d`-partition `B i`
has bundles of value exactly `1`.

**Formalization Note.** The paper's item `e_j` is the position `⟨j - 1, _⟩ : Fin m`, and "`e ∈ [ℓ]`"
is `e.val < ℓ`. The partition `B` is data of the instance, because head profiles depend on it. The
bound `v i e ≤ 1` is the first bullet of Assumption 1. -/
structure OrderedInstance (n m d : ℕ) where
  /-- `v i e` is the value of item `e` for agent `i`. -/
  v : Fin n → Fin m → ℝ
  v_nonneg : ∀ i e, 0 ≤ v i e
  v_le_one : ∀ i e, v i e ≤ 1
  v_antitone : ∀ i, Antitone (v i)
  /-- `B i e` is the MMS bundle of agent `i` that contains item `e`. -/
  B : Fin n → Fin m → Fin d
  B_sum : ∀ i j, ∑ e with B i e = j, v i e = 1

end AlmostMMS


