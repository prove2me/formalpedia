-- Prove2me | Definitions.Def_CHMSPricing_OpmUniform_SetSystem
-- name    : CHMSPricing_OpmUniform_SetSystem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T11:15:19.145701+00:00
-- url     : https://prove2.me/theorems/56968ce3-6abc-4453-8cca-cf8fdaca938f
-- title:
--   Downward-closed feasibility constraints and the k-uniform matroid
-- statement:
--   The seller's **feasibility constraint** is a set system $\mathcal J \subseteq 2^{\alpha}$ on a finite set $\alpha$ of agents that is downward closed: $\emptyset \in \mathcal J$, and whenever $A \subseteq B$ and $B \in \mathcal J$ we have $A \in \mathcal J$. The seller may serve any set of agents in $\mathcal J$.
--
--   For $n$ agents $[n]$ and an integer $k \ge 0$, the **$k$-uniform matroid** is the set system in which a set $S \subseteq [n]$ is feasible if and only if
--   $$|S| \le k,$$
--   that is, every set of size at most $k$ is independent: the seller has $k$ identical units to sell.
--
--   The uniform matroid is the feasibility constraint of the mission's main theorem (Theorem 10).
--
--   **Formalization Note** Agents are `Fin n`, i.e. indexed $0, \dots, n-1$. No restriction is placed on $k$: for $k \ge n$ every set is feasible, and for $k = 0$ only $\emptyset$ is.
-- source:
--   Chawla, Hartline, Malec and Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, p. 4, §2.1 (set system, downward closed); p. 9, §5.2 (uniform matroids)

import Mathlib

namespace CHMSPricing.OpmUniform

/-- A downward-closed set system `𝒥 ⊆ 2^α` (the feasibility constraint of §2.1, p. 4):
the empty set is feasible and every subset of a feasible set is feasible. -/
structure SetSystem (α : Type*) [Fintype α] [DecidableEq α] where
  Feasible : Finset α → Prop
  feasible_empty : Feasible ∅
  feasible_mono : ∀ ⦃A B : Finset α⦄, A ⊆ B → Feasible B → Feasible A

/-- The `k`-uniform matroid on the agents `[n] = Fin n` (§5.2, p. 9): "every set of size at
most `k` is independent". -/
def uniformSystem (n k : ℕ) : SetSystem (Fin n) where
  Feasible S := S.card ≤ k
  feasible_empty := by simp
  feasible_mono := fun _ _ hAB hB => (Finset.card_le_card hAB).trans hB

end CHMSPricing.OpmUniform


