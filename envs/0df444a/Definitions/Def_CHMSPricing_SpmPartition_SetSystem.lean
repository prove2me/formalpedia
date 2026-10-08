-- Prove2me | Definitions.Def_CHMSPricing_SpmPartition_SetSystem
-- name    : CHMSPricing_SpmPartition_SetSystem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T11:04:56.992974+00:00
-- url     : https://prove2.me/theorems/9e3d27fe-92e7-45da-a769-878ddae0cbbf
-- title:
--   Downward-closed set systems, rank, k-uniform matroids and partition matroids
-- statement:
--   A **feasibility constraint** on a finite set of agents is a downward-closed set system $\mathcal J\subseteq 2^{[n]}$: the empty set is feasible, and every subset of a feasible set is feasible. The **rank** of a set $S$ of agents is the size of its largest feasible subset,
--
--   $$
--   \operatorname{rank}(S)=\max_{S'\subseteq S,\ S'\in\mathcal J}|S'|.
--   $$
--
--   Two constraints are named. The **$k$-uniform matroid** declares a set feasible iff it has at most $k$ elements (a seller with $k$ identical units). A **partition matroid** is a disjoint union of uniform matroids: each agent $i$ belongs to a part $\mathrm{part}(i)$, each part $b$ has a capacity $\mathrm{cap}(b)\in\mathbb N$, and a set $S$ is feasible iff
--
--   $$
--   |\{i\in S:\mathrm{part}(i)=b\}|\le \mathrm{cap}(b)\quad\text{for every part } b.
--   $$
--
--   The $k$-uniform matroid is the partition matroid with a single part of capacity $k$. These are the constraints under which the mission's approximation theorems are stated.
--
--   **Formalization Note** The rank is a maximum over the finite family of feasible subsets of $S$, which always contains $\emptyset$, so it is a genuine maximum. Capacities may be $0$.
-- source:
--   Chawla, Hartline, Malec and Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, p. 4, §2.1 (downward-closed set system); p. 6, §4 (rank); p. 7, §4.2 (uniform and partition matroids)

import Mathlib

namespace CHMSPricing.SpmPartition

/-- A downward-closed set system `𝒥 ⊆ 2^α` (the feasibility constraint of §2.1, p. 4):
the empty set is feasible and every subset of a feasible set is feasible. -/
structure SetSystem (α : Type*) [Fintype α] [DecidableEq α] where
  Feasible : Finset α → Prop
  feasible_empty : Feasible ∅
  feasible_mono : ∀ ⦃A B : Finset α⦄, A ⊆ B → Feasible B → Feasible A

namespace SetSystem

variable {α : Type*} [Fintype α] [DecidableEq α]

open Classical in
/-- §4, p. 6: `rank(S) = max_{S' ⊆ S, S' ∈ 𝒥} |S'|`, the size of a largest feasible subset of `S`
(a genuine maximum: `∅` is a feasible subset of every `S`). -/
noncomputable def rank (J : SetSystem α) (S : Finset α) : ℕ :=
  (S.powerset.filter J.Feasible).sup Finset.card

end SetSystem

/-- §4.2, p. 7: the `k`-uniform matroid on `α`: a set is feasible iff it has at most `k`
elements. -/
def uniformSystem (α : Type*) [Fintype α] [DecidableEq α] (k : ℕ) : SetSystem α where
  Feasible S := S.card ≤ k
  feasible_empty := by simp
  feasible_mono := fun _ _ hAB hB => (Finset.card_le_card hAB).trans hB

/-- §4.2, p. 7: the partition matroid ("disjoint union of uniform matroids") given by a map
`part : α → β` assigning each agent to a part and capacities `cap : β → ℕ`: a set is feasible
iff it contains at most `cap b` agents of each part `b`. -/
def partitionSystem {α β : Type*} [Fintype α] [DecidableEq α] [DecidableEq β]
    (part : α → β) (cap : β → ℕ) : SetSystem α where
  Feasible S := ∀ b, (S.filter (fun i => part i = b)).card ≤ cap b
  feasible_empty := by simp
  feasible_mono := fun _ _ hAB hB b =>
    (Finset.card_le_card (Finset.filter_subset_filter _ hAB)).trans (hB b)

end CHMSPricing.SpmPartition


