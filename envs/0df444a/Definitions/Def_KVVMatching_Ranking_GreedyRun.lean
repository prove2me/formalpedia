-- Prove2me | Definitions.Def_KVVMatching_Ranking_GreedyRun
-- name    : KVVMatching_Ranking_GreedyRun
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T04:28:12.838994+00:00
-- url     : https://prove2.me/theorems/708b983d-f5ea-4af2-a810-c6a1ad188827
-- title:
--   Greedy online matching and arbitrary refusal rules
-- statement:
--   A finite bipartite graph has two sides of size $n$ and an adjacency relation $E$. A partial matching is a set of edges with no vertex repeated on either side. In a greedy online run, one side arrives in a specified order. At each arrival, the algorithm selects the eligible adjacent, unmatched vertex of highest priority on the other side, unless a refusal rule declines the arrival. The rule may inspect the time, the matching accumulated by its own run, and the arriving vertex.
--
--   $$M_{t+1}=\begin{cases}M_t,&\text{if the arrival is refused or no eligible vertex exists},\\ M_t\cup\{(a_t,b_t)\},&\text{otherwise, with }b_t\text{ the highest-ranked eligible vertex.}\end{cases}$$
--
--   This run is the common finite model for RANKING, the rows-arrive dual, and the paper's refusal algorithms.
--
--   **Formalization Note** Priority zero is highest. The generic run returns ordered pairs (arriving vertex, selected vertex); its refusal decision uses the state of that same run.
-- source:
--   Karp, Vazirani, Vazirani, An Optimal Algorithm for On-line Bipartite Matching, STOC 1990, pp. 353–354, RANKING algorithm and paragraph before Lemma 2

import Mathlib

namespace KVVMatching.Ranking

/-- A partial matching is a set of pairs with no repeated vertex on either side. -/
def IsMatching {n : ℕ} (M : Finset (Fin n × Fin n)) : Prop :=
  (∀ e ∈ M, ∀ f ∈ M, e.1 = f.1 → e = f) ∧
  (∀ e ∈ M, ∀ f ∈ M, e.2 = f.2 → e = f)

/-- Whether the first vertex of a pair is covered by a matching. -/
def firstMatched {n : ℕ} (M : Finset (Fin n × Fin n)) (i : Fin n) : Prop :=
  ∃ e ∈ M, e.1 = i

/-- Whether the second vertex of a pair is covered by a matching. -/
def secondMatched {n : ℕ} (M : Finset (Fin n × Fin n)) (j : Fin n) : Prop :=
  ∃ e ∈ M, e.2 = j

/-- Greedy online matching. `arrivals t` arrives at time `t`; `rank r` is the
opposite-side vertex of priority `r`, with smaller priorities preferred.
The refusal rule sees the time, this run's current matching, and the arrival. -/
noncomputable def greedyRun {n : ℕ} (adj : Fin n → Fin n → Prop)
    (arrivals rank : Equiv.Perm (Fin n))
    (refuse : ℕ → Finset (Fin n × Fin n) → Fin n → Bool) :
    Finset (Fin n × Fin n) := by
  classical
  exact (List.range n).foldl (fun M t =>
    if ht : t < n then
      let a : Fin n := ⟨t, ht⟩
      let v := arrivals a
      if refuse t M v then M else
        let eligible : Finset (Fin n) := Finset.univ.filter
          (fun r => adj v (rank r) ∧ ¬ secondMatched M (rank r))
        if he : eligible.Nonempty then
          insert (v, rank (eligible.min' he)) M
        else M
    else M) ∅

end KVVMatching.Ranking


