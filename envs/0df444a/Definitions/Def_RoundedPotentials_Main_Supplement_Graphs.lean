-- Prove2me | Definitions.Def_RoundedPotentials_Main_Supplement_Graphs
-- name    : RoundedPotentials_Main_Supplement_Graphs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T13:02:51.517743+00:00
-- url     : https://prove2.me/theorems/088c8f50-eae7-477b-8cb0-4643192249a7
-- title:
--   Capacity matrices and arc sets as base-mission instances
-- statement:
--   This file adapts two further input encodings to the base mission's §2 instance (a list of distinct loopless ordered pairs with capacities at most $W$), without changing the graph class.
--
--   1. For a capacity matrix $c:[n]\times[n]\to\mathbb N$, the instance `matrixInstance n W c` has one edge $(u,v)$ of capacity $\min\{c_{uv},W\}$ for every ordered pair of distinct vertices with nonzero capped capacity. Diagonal entries are ignored, because §2 graphs are loopless, and absent pairs have capacity zero. Every statement that uses it assumes $c_{uv}\le W$, so the cap changes nothing.
--   2. For a loopless arc set $A$ with arbitrary natural capacities $c$, the instance `arcInstance A c` has one edge per arc, zero capacities included, with capacity bound $W=\max_{(u,v)\in A}c_{uv}$.
--   3. `MatrixMaxValue n W c s t p` says that $\mathrm{MaxFlow}(s,t)=p$ for the matrix $c$. It is the base mission's `MaxValue`: $p$ is the largest value of an $s$–$t$ flow.
--
--   `distinctPairs n` lists the ordered pairs of distinct vertices in lexicographic order. The file also contains the one-line structural lemma that this list has no duplicates.
-- source:
--   Ohad Trabelsi, STOC 2027 submission #1650 (October 2026), p. 11, §2 (graph conventions)

import Mathlib
import Definitions.Def_RoundedPotentials_Main_Certificate

namespace RoundedPotentials.Main.Supplement

open RoundedPotentials.Main

/-- All ordered pairs `(u, v)` of distinct vertices of `[n]`, in lexicographic order. -/
def distinctPairs (n : ℕ) : List (Fin n × Fin n) :=
  ((List.finRange n).product (List.finRange n)).filter (fun e => e.1 ≠ e.2)

theorem distinctPairs_nodup (n : ℕ) : (distinctPairs n).Nodup :=
  List.Nodup.filter _ ((List.nodup_finRange n).product (List.nodup_finRange n))

/-- The §2 instance (`Instance n W` of the base mission) of a capacity matrix `c` on `[n]`:
one edge `(u, v, c u v)` for every ordered pair of distinct vertices with `c u v ≠ 0`.
Diagonal entries are ignored (§2 graphs are loopless) and absent capacities are zero.
Every capacity is capped at `W`, so the instance always satisfies the promise `c ≤ W`; under the
promise `∀ u v, c u v ≤ W` of every statement that uses it, the cap changes nothing. -/
def matrixInstance (n W : ℕ) (c : Fin n → Fin n → ℕ) : Instance n W where
  edges := ((distinctPairs n).filter (fun e => min (c e.1 e.2) W ≠ 0)).map
    (fun e => (e.1, e.2, min (c e.1 e.2) W))
  noLoops := by
    intro e he
    simp only [List.mem_map, List.mem_filter, distinctPairs] at he
    obtain ⟨a, ⟨⟨_, ha⟩, _⟩, rfl⟩ := he
    simpa using ha
  uniquePairs := by
    rw [List.map_map]
    have : ((fun e : Fin n × Fin n × ℕ => (e.1, e.2.1)) ∘
        (fun e : Fin n × Fin n => (e.1, e.2, min (c e.1 e.2) W))) = id := by
      funext e; rfl
    rw [this, List.map_id]
    exact (distinctPairs_nodup n).filter _
  bounded := by
    intro e he
    simp only [List.mem_map] at he
    obtain ⟨a, _, rfl⟩ := he
    exact min_le_right _ _

/-- The §2 instance of a loopless arc set `A` with arbitrary natural capacities `c` (absent arcs
and capacities off `A` play no role): one edge `(u, v, c u v)` per arc, with capacity bound
`W = max_{(u,v) ∈ A} c u v`. Zero-capacity arcs are kept as edges. -/
noncomputable def arcInstance {n : ℕ} (A : Finset (Fin n × Fin n)) (hA : ∀ e ∈ A, e.1 ≠ e.2)
    (c : Fin n → Fin n → ℕ) : Instance n (A.sup (fun e => c e.1 e.2)) where
  edges := A.toList.map (fun e => (e.1, e.2, c e.1 e.2))
  noLoops := by
    intro e he
    simp only [List.mem_map, Finset.mem_toList] at he
    obtain ⟨a, ha, rfl⟩ := he
    exact hA a ha
  uniquePairs := by
    rw [List.map_map]
    have : ((fun e : Fin n × Fin n × ℕ => (e.1, e.2.1)) ∘
        (fun e : Fin n × Fin n => (e.1, e.2, c e.1 e.2))) = id := by
      funext e; rfl
    rw [this, List.map_id]
    exact A.nodup_toList
  bounded := by
    intro e he
    simp only [List.mem_map, Finset.mem_toList] at he
    obtain ⟨a, ha, rfl⟩ := he
    exact Finset.le_sup (f := fun e => c e.1 e.2) ha

/-- `MaxFlow(s, t) = p` for the capacity matrix `c` (capacities capped at `W`, see
`matrixInstance`): the base mission's `MaxValue`, the largest value of an `s`–`t` flow. -/
def MatrixMaxValue (n W : ℕ) (c : Fin n → Fin n → ℕ) (s t : Fin n) (p : ℤ) : Prop :=
  MaxValue (matrixInstance n W c) s t (p : ℝ)

end RoundedPotentials.Main.Supplement


