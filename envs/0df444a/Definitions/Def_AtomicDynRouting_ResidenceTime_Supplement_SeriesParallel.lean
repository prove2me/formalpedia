-- Prove2me | Definitions.Def_AtomicDynRouting_ResidenceTime_Supplement_SeriesParallel
-- name    : AtomicDynRouting_ResidenceTime_Supplement_SeriesParallel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T06:32:32.872559+00:00
-- url     : https://prove2.me/theorems/05e7849c-f9a9-4c0d-ae44-747c4e3c96da
-- title:
--   Definition 7, §6, §6.1, p. 15 — series-parallel networks and their constructions, o-d cuts and capacity, maximum in-degree
-- statement:
--   **Series-parallel networks** (Definition 7). A network with origin $o$ and destination $d$ is $o$-$d$ series-parallel if (i) it is a single edge $od$; or (ii) it is obtained from an $o$-$w$ and a $w$-$d$ series-parallel network by merging $d_1$ with $o_2$ (series connection); or (iii) it is obtained from two $o$-$d$ series-parallel networks by merging their origins and their destinations (parallel connection).
--
--   A **construction** of $G=(V,E)$ is a binary tree whose leaves are the $m=|E|$ edges and whose internal nodes are series or parallel connections; the set $\mathcal S$ of p. 15 is the set of subnetworks at its nodes, $G$ included.
--
--   An **$o$-$d$ cut** is a set of edges meeting every $o$-$d$ path, and the **capacity** $|\Xi(G)|$ of $G$ is the minimum number of edges of an $o$-$d$ cut. $D=\max_{v\in V}|E^-_v|$ is the maximum in-degree.
--
--   **Formalization Note** A construction is a term `SPTree E` (leaves are edges of the ambient network); `IsSP N T o d` checks the three rules inside $N$, with the two parts edge-disjoint and sharing exactly the merged vertices. `IsSPConstruction` requires that the tree uses every edge and that every vertex is an endpoint of some edge. Only the size $|\Xi(G)|$ of the leftmost minimum cut is needed by the theorems, so it is defined as the minimum cut size.
-- source:
--   Cao, Chen, Chen, Wang, Bounding residence times for atomic dynamic routings, accepted manuscript (Mathematics of Operations Research, accepted Nov. 12, 2021; WRAP 160244), p. 15 (PDF 16), Definition 7, the set S, o-d cut and capacity (§6), D and L (§6.1)

import Mathlib
import Definitions.Def_AtomicDynRouting_ResidenceTime_Network

namespace AtomicDynRouting.ResidenceTime.Supplement

open AtomicDynRouting.ResidenceTime

/-- A construction tree of a series-parallel network (Definition 7, p. 15): a leaf is a single edge;
an internal node connects the subnetworks of its two children in series or in parallel. -/
inductive SPTree (E : Type) where
  | edge (e : E)
  | series (A B : SPTree E)
  | par (A B : SPTree E)

namespace SPTree

variable {V E : Type}

/-- The edge set of the subnetwork built by a construction tree. -/
def edges : SPTree E → Set E
  | edge e => {e}
  | series A B => edges A ∪ edges B
  | par A B => edges A ∪ edges B

/-- The vertex set of the subnetwork built by `T` inside the network `N`: the endpoints of its
edges. -/
def verts (N : Network V E) (T : SPTree E) : Set V :=
  {v | ∃ e ∈ T.edges, N.tail e = v ∨ N.head e = v}

/-- `IsSP N T o d` (Definition 7, p. 15): the edges of `T`, inside `N`, form an `o`-`d`
series-parallel network built as `T` prescribes:
(i) a single edge `od` (from `o` to a different vertex `d`);
(ii) the series connection of an `o`-`w` and a `w`-`d` series-parallel network that share no edge
and have only the merged vertex `w` (`d₁ = o₂`) in common;
(iii) the parallel connection of two `o`-`d` series-parallel networks that share no edge and have
only the merged terminals `o` (`o₁ = o₂`) and `d` (`d₁ = d₂`) in common. -/
def IsSP (N : Network V E) : SPTree E → V → V → Prop
  | edge e, o, d => N.tail e = o ∧ N.head e = d ∧ o ≠ d
  | series A B, o, d => ∃ w, IsSP N A o w ∧ IsSP N B w d ∧ Disjoint A.edges B.edges ∧
      verts N A ∩ verts N B = {w}
  | par A B, o, d => IsSP N A o d ∧ IsSP N B o d ∧ Disjoint A.edges B.edges ∧
      verts N A ∩ verts N B = {o, d}

/-- `IsNode S T`: `S` is one of the subnetworks appearing in the construction `T` (the set `S` of
p. 15 is the set of all nodes of `T`, the whole network included). -/
def IsNode (S : SPTree E) : SPTree E → Prop
  | edge e => S = edge e
  | series A B => S = series A B ∨ IsNode S A ∨ IsNode S B
  | par A B => S = par A B ∨ IsNode S A ∨ IsNode S B

end SPTree

variable {V E : Type}

/-- `IsSPConstruction N o d T`: the whole network `N` is `o`-`d` series-parallel, built by the
construction `T` (Definition 7 and p. 15): `T` builds an `o`-`d` series-parallel network whose edge
set is all of `E`, and every vertex of `N` is an endpoint of some edge. -/
def IsSPConstruction (N : Network V E) (o d : V) (T : SPTree E) : Prop :=
  SPTree.IsSP N T o d ∧ T.edges = Set.univ ∧ ∀ v : V, ∃ e : E, N.tail e = v ∨ N.head e = v

/-- `N` is an `o`-`d` series-parallel network (Definition 7): it has some construction. -/
def IsSeriesParallel (N : Network V E) (o d : V) : Prop :=
  ∃ T : SPTree E, IsSPConstruction N o d T

/-- `C` is an `o`-`d` cut of `N` (§6, p. 15): every `o`-`d` path uses an edge of `C`, so that
removing `C` leaves no path from `o` to `d`. -/
def IsCut (N : Network V E) (o d : V) (C : Finset E) : Prop :=
  ∀ P : List E, N.IsPathFrom o d P → ∃ e ∈ P, e ∈ C

/-- The capacity `|Ξ(G)|` of the network (§6, p. 15): the minimum number of edges of an `o`-`d`
cut. When `o ≠ d`, `Finset.univ` is a cut, so the infimum is attained. This applies
to every series-parallel network used below. For `o = d` the empty path prevents
any cut; the defining set is empty and the natural-number infimum is `0`. -/
noncomputable def minCut [Fintype E] (N : Network V E) (o d : V) : ℕ :=
  sInf {k : ℕ | ∃ C : Finset E, C.card = k ∧ IsCut N o d C}

/-- `D = max_{v ∈ V} |E⁻_v|` (§6.1, p. 15): the maximum in-degree of the vertices of `N`. -/
noncomputable def maxInDeg [Fintype V] [Fintype E] [DecidableEq V] (N : Network V E) : ℕ :=
  Finset.univ.sup fun v : V => (Finset.univ.filter fun e : E => N.head e = v).card

end AtomicDynRouting.ResidenceTime.Supplement


