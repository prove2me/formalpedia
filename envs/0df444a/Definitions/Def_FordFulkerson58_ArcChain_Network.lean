-- Prove2me | Definitions.Def_FordFulkerson58_ArcChain_Network
-- name    : FordFulkerson58_ArcChain_Network
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T07:00:44.727488+00:00
-- url     : https://prove2.me/theorems/5ccbc7ac-b9f5-430a-beb0-85399888f132
-- title:
--   §2–§3, pp. 1778–1780 — networks with directed or undirected arcs, commodities, chains as arc sets, commodity chains, the incidence (1)
-- statement:
--   A **multi-commodity network** consists of a finite set of nodes $P_1,\dots,P_N$, a finite set of arcs $A_1,\dots,A_m$, and a finite set of commodities. Each arc $e$ joins two nodes, $\mathrm{tail}(e)$ and $\mathrm{head}(e)$, has a flow capacity $b_e \in \mathbb{R}$, and is either *directed* (it can be traversed only from its tail to its head) or *undirected* (it can be traversed both ways). Each commodity $k$ has a set of sources $S_k$ and a set of sinks $T_k$. Directed and undirected arcs may be mixed, and parallel arcs are allowed.
--
--   A **chain** from a node $u$ to a node $w$ is a set $C$ of arcs that can be arranged as a sequence
--   $$u = v_0 \xrightarrow{e_1} v_1 \xrightarrow{e_2} \cdots \xrightarrow{e_p} v_p = w$$
--   with pairwise distinct nodes $v_0,\dots,v_p$, distinct arcs, and each $e_i$ traversable from $v_{i-1}$ to $v_i$. The case $p = 0$ (the empty arc set, from $u$ to itself) is the **null chain**. A chain from a set $S$ to $w$ is a chain from some node of $S$ to $w$, and a **commodity chain** for commodity $k$ is a chain from a node of $S_k$ to a node of $T_k$; it may pass through other sources or sinks of the same commodity.
--
--   The **columns** $C_1,\dots,C_n$ of the arc-chain formulation are the pairs (commodity $k$, commodity chain $C$ of $k$): the same arc set used by two commodities gives two columns. The **incidence matrix** $A = (a_{rs})$ of (1) is
--   $$a_{rs} = \begin{cases} 1 & \text{if } C_s \text{ contains } A_r,\\ 0 & \text{otherwise.}\end{cases}$$
--
--   These are the objects of the arc-chain formulation of the maximal multi-commodity flow problem; every other item of the mission is stated over them.
--
--   **Formalization Note** Nodes, arcs and commodities are finite types `V`, `E`, `ι`; the per-arc flag `directed` covers the page's remark (p. 1779) that it is immaterial whether arcs are directed or undirected, and the supply reduction of §4 adds directed arcs to an undirected network. A chain is the arc set of a simple path, encoded by `IsChainWalk` (node list without repetition, arc list without repetition, consecutive traversals), mirroring `FordFulkerson56.MinCut.IsChainWalk` of the 1956 paper; that published definition is not reused because it has undirected arcs only, a single source and sink, and positive capacities. No sign of the capacities and no disjointness of sources and sinks is assumed. The column type `Col N` is the subtype of pairs `(k, C)` with `C` a commodity chain of `k`, finite by classical decidability.
-- source:
--   Ford and Fulkerson, A suggested computation for maximal multi-commodity network flows, Management Sci. 50(12S) (2004), pp. 1778–1780, §2 (the list of arcs and chains, display (1), the directed/undirected remark on p. 1779) and §3 (p. 1780, nodes P_1, …, P_N, sources S, sinks T)

import Mathlib

namespace FordFulkerson58.ArcChain

/-- A multi-commodity network (Ford–Fulkerson 1958, §2, pp. 1778–1779, and §3, p. 1780).
Nodes form the type `V` (the page's `P₁, …, P_N`) and arcs the type `E` (the page's `A₁, …, A_m`);
arc `e` joins `tail e` and `head e`. If `directed e = true` the arc may only be traversed from `tail e`
to `head e`; otherwise it is undirected and may be traversed both ways. `b e` is the flow capacity of
`e`. Commodities form the type `ι`; commodity `k` has the set of sources `src k` (`S_k`) and the set of
sinks `snk k` (`T_k`). -/
structure Network (V E ι : Type*) where
  tail : E → V
  head : E → V
  directed : E → Bool
  b : E → ℝ
  src : ι → Finset V
  snk : ι → Finset V

variable {V E ι : Type*}

/-- Arc `e` can be traversed from `u` to `v`: either `e` goes from `u` to `v`, or `e` is undirected and
goes from `v` to `u`. -/
def Traverses (N : Network V E ι) (e : E) (u v : V) : Prop :=
  (N.tail e = u ∧ N.head e = v) ∨ (N.directed e = false ∧ N.tail e = v ∧ N.head e = u)

/-- `IsChainWalk N u w p vs`: the arc list `p` and the node list `vs` arrange a chain from `u` to `w`:
`vs` has one more entry than `p`, starts at `u`, ends at `w`, has no repeated node, `p` has no repeated
arc, and the `i`-th arc can be traversed from the `i`-th to the `(i+1)`-th node. With `p = []` and
`vs = [u]` it is the null chain from `u` to `u`. -/
def IsChainWalk (N : Network V E ι) (u w : V) (p : List E) (vs : List V) : Prop :=
  vs.length = p.length + 1 ∧ vs.head? = some u ∧ vs.getLast? = some w ∧ vs.Nodup ∧ p.Nodup ∧
  ∀ (i : ℕ) (h : i < p.length), ∃ x y : V,
    vs[i]? = some x ∧ vs[i + 1]? = some y ∧ Traverses N p[i] x y

/-- A chain from `u` to `w`: a set `C` of arcs that can be arranged as a chain walk from `u` to `w`. -/
def IsChain [DecidableEq E] (N : Network V E ι) (u w : V) (C : Finset E) : Prop :=
  ∃ (p : List E) (vs : List V), IsChainWalk N u w p vs ∧ p.toFinset = C

/-- A chain from some node of the set `S` to the node `w`. -/
def IsChainFrom [DecidableEq E] (N : Network V E ι) (S : Finset V) (w : V) (C : Finset E) : Prop :=
  ∃ u ∈ S, IsChain N u w C

/-- A chain for commodity `k`: a chain joining a source of `k` with a sink of `k`. -/
def IsCommodityChain [DecidableEq E] (N : Network V E ι) (k : ι) (C : Finset E) : Prop :=
  ∃ t ∈ N.snk k, IsChainFrom N (N.src k) t C

/-- The commodity chains `C₁, …, C_n` of §2, as pairs (commodity, arc set). The same arc set used by two
commodities gives two columns. -/
abbrev Col [DecidableEq E] (N : Network V E ι) : Type _ :=
  {kc : ι × Finset E // IsCommodityChain N kc.1 kc.2}

noncomputable instance instFintypeCol [Fintype ι] [Fintype E] [DecidableEq E] (N : Network V E ι) :
    Fintype (Col N) := by
  classical
  exact Subtype.fintype _

/-- The incidence matrix (1): `a_rs = 1` if the chain `C_s` contains the arc `A_r`, `0` otherwise. -/
def inc [DecidableEq E] (N : Network V E ι) (r : E) (s : Col N) : ℝ :=
  if r ∈ s.1.2 then 1 else 0

end FordFulkerson58.ArcChain


