-- Prove2me | Definitions.Def_IntervalExplore_KT1_Model
-- name    : IntervalExplore_KT1_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:09:18.47572+00:00
-- url     : https://prove2.me/theorems/34f78e7c-06f0-40a1-8dc8-869c5b7b6d4a
-- title:
--   Finite dynamic graphs and the fixed-port KT1 observation interface
-- statement:
--   Let $V$ be a finite set and $G=(V,E)$ a simple undirected graph. A dynamic graph is a sequence $G_t\subseteq G$ of snapshots on the same vertex set. The numbers $n=|V|$ and $m=|E|$ count the underlying graph, including edges that never appear. A port assignment at $v$ is a bijection from its neighbors to $1,\ldots,\deg_G(v)$, fixed over time. Vertex identifiers are distinct natural numbers.
--
--   For a positive integer $T$, interval connectivity means
--   $$
--   \forall t\ge0,\qquad \bigcap_{i=0}^{T-1}G_{t+i}\text{ is connected}.
--   $$
--   A common spanning tree is a tree on all of $V$ contained in every snapshot. A world packages a graph, schedule, identifiers, ports and starting vertex, without any performance assumptions.
--
--   A KT1 observation contains the current identifier, available local ports, incoming port (absent initially), and pairs consisting of a currently adjacent identifier and the local port leading to it. A deterministic algorithm maps a finite observation history to either a port or a termination decision. It receives no world, graph size, edge count or connectivity parameter. This interface is reusable for online graph exploration.
-- source:
--   Yuichi Sudo, Naoki Kitamura, Masahiro Shibata, Junya Nakamura, Sébastien Tixeuil, Toshimitsu Masuzawa, Koichi Wada, STOC 2027 submission #1589 (October 2026), §1.2, p.3 (PDF p.4), and Note 1, p.4 (PDF p.5)

import Mathlib

set_option autoImplicit false

namespace IntervalExplore.KT1

/-! The fixed-port KT1 interface, §1.2, printed p.3 (PDF p.4).
The underlying graph is separate from its schedule; unused/null edges still count. -/

noncomputable def edgeCount {V : Type} [Fintype V] (G : SimpleGraph V) : ℕ := by
  classical
  exact (Finset.univ.filter fun e : Sym2 V => e ∈ G.edgeSet).card

noncomputable def degree {V : Type} [Fintype V] (G : SimpleGraph V) (v : V) : ℕ := by
  classical
  exact (Finset.univ.filter fun u => G.Adj v u).card

/-- A bijection from the neighbors of each vertex to the positive ports 1,...,degree.
Values at nonneighbors are unused and impose no condition. -/
structure Ports {V : Type} [Fintype V] (G : SimpleGraph V) where
  number : V → V → ℕ
  bijective : ∀ v, Set.BijOn (number v) {u | G.Adj v u}
    {p | 1 ≤ p ∧ p ≤ degree G v}

structure DynamicGraph {V : Type} (G : SimpleGraph V) where
  snapshot : ℕ → SimpleGraph V
  subgraph : ∀ t, snapshot t ≤ G

/-- Every window uses the snapshots at t,...,t+T-1; T=0 is excluded. -/
def IntervalConnected {V : Type} {G : SimpleGraph V} (D : DynamicGraph G) (T : ℕ) : Prop :=
  1 ≤ T ∧ ∀ t, (⨅ i : Fin T, D.snapshot (t + i.val)).Connected

def CommonTree {V : Type} {G : SimpleGraph V} (D : DynamicGraph G) : Prop :=
  ∃ H : SimpleGraph V, H.IsTree ∧ ∀ t, H ≤ D.snapshot t

/-- All instance data. None of these fields is an input to Alg. -/
structure World (V : Type) [Fintype V] where
  graph : SimpleGraph V
  dynamic : DynamicGraph graph
  labels : V ↪ ℕ
  ports : Ports graph
  start : V

structure Obs where
  own : ℕ
  available : Finset ℕ
  incoming : Option ℕ
  neighbors : Finset (ℕ × ℕ)
  deriving DecidableEq, Inhabited

/-- Input is only the finite sequence of observations, including the current one.
`none` means terminate; `some p` means traverse local port p. -/
abbrev Alg := List Obs → Option ℕ

noncomputable def observe {V : Type} [Fintype V] (W : World V)
    (t : ℕ) (v : V) (incoming : Option ℕ) : Obs := by
  classical
  let ns := Finset.univ.filter fun u => (W.dynamic.snapshot t).Adj v u
  exact ⟨W.labels v, ns.image (W.ports.number v), incoming,
    ns.image fun u => (W.labels u, W.ports.number v u)⟩

end IntervalExplore.KT1


