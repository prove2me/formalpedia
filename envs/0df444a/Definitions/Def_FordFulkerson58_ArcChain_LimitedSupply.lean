-- Prove2me | Definitions.Def_FordFulkerson58_ArcChain_LimitedSupply
-- name    : FordFulkerson58_ArcChain_LimitedSupply
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T07:15:33.505748+00:00
-- url     : https://prove2.me/theorems/3e54fa89-7cc2-4fe1-8060-155c3c7569ea
-- title:
--   §4, p. 1780 — the limited-supply multi-commodity flow problem and the augmented network with one new directed source arc per (commodity, source)
-- statement:
--   Let $N$ be a multi-commodity network and suppose an amount $a_{k,v}$ of commodity $k$ is available at each of its sources $v \in S_k$.
--
--   The **limited-supply problem** has one variable for each triple $(k, v, C)$ with $v \in S_k$ and $C$ a chain from $v$ to a sink of $k$. A flow $x \ge 0$ on these triples is feasible when, for every arc $r$, the total flow on the triples whose chain contains $r$ is at most $b_r$, and, for every commodity $k$ and source $v \in S_k$, the total flow on the triples $(k, v, \cdot)$ is at most $a_{k,v}$.
--
--   The **augmented network** adds, for every commodity $k$ and source $v \in S_k$, a new node $P'_{k,v}$ and a new directed arc $A'_{k,v}$ from $P'_{k,v}$ to $v$ with capacity $a_{k,v}$. The sources of commodity $k$ become the new nodes $P'_{k,v}$, $v \in S_k$; the sinks, and all old arcs with their ends, directions and capacities, are unchanged.
--
--   This is the construction by which §4 reduces limited supplies to a problem of the same type as (2)–(3).
--
--   **Formalization Note** New nodes and arcs are indexed by the pairs $(k, v)$ with $v \in S_k$ only (the type `Σ k, ↥(N.src k)`), one new arc per (commodity, source) pair, as the page's count $\sum_i n_i$ confirms. Capacity rows of the limited problem are written as inequalities (equivalent to (3) with a non-negative slack).
-- source:
--   Ford and Fulkerson, A suggested computation for maximal multi-commodity network flows, Management Sci. 50(12S) (2004), p. 1780, §4 (limited supplies; new arcs A′ from P′ with capacities a)

import Mathlib
import Definitions.Def_FordFulkerson58_ArcChain_Network

namespace FordFulkerson58.ArcChain

variable {V E ι : Type*}

/-- The (commodity, source) pairs `(k, v)` with `v ∈ S_k`. -/
abbrev SupplyPair (N : Network V E ι) : Type _ :=
  Σ k : ι, ↥(N.src k)

/-- The columns of the limited-supply problem (§4, p. 1780): triples `(k, v, C)` with `v` a source of
commodity `k` and `C` a chain from `v` to a sink of `k`. -/
abbrev LCol [DecidableEq E] (N : Network V E ι) : Type _ :=
  {q : ι × V × Finset E // q.2.1 ∈ N.src q.1 ∧ ∃ t ∈ N.snk q.1, IsChain N q.2.1 t q.2.2}

noncomputable instance instFintypeLCol [Fintype V] [Fintype ι] [Fintype E] [DecidableEq E]
    (N : Network V E ι) : Fintype (LCol N) := by
  classical
  exact Subtype.fintype _

/-- Feasibility for the limited-supply problem with supplies `a k v` (an amount `a k v` of commodity
`k` available at its source `v`): flows `x ≥ 0` on the triples; for every arc `r`, the total flow on
the chains containing `r` is at most the capacity `b_r`; and for every commodity `k` and source
`v ∈ S_k`, the total flow of commodity `k` on chains starting at `v` is at most `a k v`. -/
def LimitedFeasible [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]
    (N : Network V E ι)
    (a : ι → V → ℝ) (x : LCol N → ℝ) : Prop :=
  (∀ q, 0 ≤ x q) ∧
  (∀ r, ∑ q, (if r ∈ q.1.2.2 then (1 : ℝ) else 0) * x q ≤ N.b r) ∧
  ∀ k, ∀ v ∈ N.src k, ∑ q, (if q.1.1 = k ∧ q.1.2.1 = v then (1 : ℝ) else 0) * x q ≤ a k v

/-- The augmented network of §4, p. 1780: for every commodity `k` and source `v ∈ S_k` a new node
`P'_v = inr ⟨k, v⟩` and a new arc `A'_v = inr ⟨k, v⟩`, directed from `P'_v` to `v`, with capacity
`a k v`. The sources of commodity `k` become the new nodes `P'_v` (`v ∈ S_k`); the sinks are unchanged;
old arcs keep their ends, directions and capacities. -/
def augment [DecidableEq V] [DecidableEq ι] (N : Network V E ι) (a : ι → V → ℝ) :
    Network (V ⊕ SupplyPair N) (E ⊕ SupplyPair N) ι where
  tail := Sum.elim (fun e => Sum.inl (N.tail e)) (fun p => Sum.inr p)
  head := Sum.elim (fun e => Sum.inl (N.head e)) (fun p => Sum.inl p.2.1)
  directed := Sum.elim N.directed (fun _ => true)
  b := Sum.elim N.b (fun p => a p.1 p.2.1)
  src := fun k => (N.src k).attach.image (fun v => Sum.inr ⟨k, v⟩)
  snk := fun k => (N.snk k).image Sum.inl

end FordFulkerson58.ArcChain


