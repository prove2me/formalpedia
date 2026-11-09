-- Prove2me | Definitions.Def_TwoOptAllExp_TSP_LayerPath
-- name    : TwoOptAllExp_TSP_LayerPath
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:09:41.815247+00:00
-- url     : https://prove2.me/theorems/35dec823-9667-43d2-838a-6084cc2ac59e
-- title:
--   The layers $F_i$ and the layer-path invariant
-- statement:
--   The vertex set of the layer $F_i$ consists of all its interfaces and gadget vertices, so consecutive layers share their identified interfaces. The **restriction** $H_i$ of an edge set $H$ to $F_i$ consists of the edges of $H$ with both endpoints in $F_i$.
--
--   An edge set $H$ of $G_n$ satisfies the **layer-path invariant** if
--
--   1. $H_0$ is a spanning path of $F_0$ with one endpoint on the $A_0$-interface and the other on the $B_0$-interface;
--   2. $H_n$ is a spanning path of $F_n$ with one endpoint on the $X_n$-interface and the other on the $Y_n$-interface;
--   3. for every $i\in[n-1]$, $H_i$ is a disjoint union of two paths that together span $F_i$, each with one endpoint on the $X_i$- or $Y_i$-interface and one endpoint on the $A_i$- or $B_i$-interface, such that each of the four interfaces carries exactly one endpoint.
--
--   A **2-regular subgraph** of $G_n$ is a set of edges of $G_n$ such that every vertex lies on exactly two of them. Lemma 9 characterizes the tours of $G_n$ by these two notions.
--
--   **Formalization Note** An interface belongs to both layers that it joins, as on p. 14, where the paths of consecutive layers "overlap precisely on their identified interfaces". Edge sets are compared as sets of named pairs. In condition 3 the path with its endpoint on the $X_i$-interface is named first, which loses nothing.
-- source:
--   Heimann, Hoang and Hougardy, Closing All-Exp Gaps in Local Search for the Traveling Salesman Problem and Maximum Constraint Assignment, November 2, 2026 preprint, STOC 2027 submission #112, SHA-256 9ac9fdf5ac1be95dff40e95db1590649f15b4eeb94559413175c88f9a42bff60, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/112.pdf, Definition 7, p. 15, with §4.1, p. 14

import Mathlib
import Definitions.Def_TwoOptAllExp_TSP_Construction

namespace TwoOptAllExp.TSP

open Pt

/-- The vertices of the `A_i`-interface. -/
def ifaceA (i : ℕ) : Finset Pt := {A i, A'' i, A' i}

/-- The vertices of the `B_i`-interface. -/
def ifaceB (i : ℕ) : Finset Pt := {B i, B'' i, B' i}

/-- The vertices of the `X_i`-interface, which is the `A_{i-1}`-interface reversed (p. 14). -/
def ifaceX (i : ℕ) : Finset Pt := {X i, X'' i, X' i}

/-- The vertices of the `Y_i`-interface, which is the `B_{i-1}`-interface reversed (p. 14). -/
def ifaceY (i : ℕ) : Finset Pt := {Y i, Y'' i, Y' i}

/-- The vertex set of the layer `F_i`, `0 ≤ i ≤ n` (§4.1, p. 14). Every layer contains all of its
interfaces, so consecutive layers overlap on their identified interfaces. -/
def layerVerts (n i : ℕ) : Finset Pt :=
  if i = 0 then
    ifaceA 0 ∪ ifaceB 0 ∪ {C 0, C'' 0, C' 0}
  else if i < n then
    ifaceX i ∪ ifaceY i ∪ ifaceA i ∪ ifaceB i ∪ {C' i, C'' i, C i, D i, D'' i, D' i, E i}
  else
    ifaceX n ∪ ifaceY n ∪ {C n}

/-- The restriction `H_i` of an edge set `H` to the layer `F_i`: the edges of `H` with both
endpoints in `F_i`. No edge of `G_n` joins two vertices of `F_i` without being an edge of `F_i`. -/
def layerRestrict {n : ℕ} (H : Finset (Sym2 (Vtx n))) (i : ℕ) : Finset (Sym2 Pt) :=
  raw H ∩ (layerVerts n i).sym2

/-- The edge set `P` is a path from `u` to `v` with vertex set exactly `W`. -/
def IsPathOn (W : Finset Pt) (P : Finset (Sym2 Pt)) (u v : Pt) : Prop :=
  ∃ p : (SimpleGraph.fromEdgeSet (P : Set (Sym2 Pt))).Walk u v,
    p.IsPath ∧ p.support.toFinset = W ∧ p.edges.toFinset = P

/-- **Definition 7 (layer-path invariant)**, p. 15. Condition 3 names the path with its endpoint
on the `X_i`-interface first, which loses nothing, since each of the four interfaces carries
exactly one endpoint. -/
def LayerPathInvariant {n : ℕ} (H : Finset (Sym2 (Vtx n))) : Prop :=
  (∃ u ∈ ifaceA 0, ∃ v ∈ ifaceB 0, IsPathOn (layerVerts n 0) (layerRestrict H 0) u v) ∧
  (∃ u ∈ ifaceX n, ∃ v ∈ ifaceY n, IsPathOn (layerVerts n n) (layerRestrict H n) u v) ∧
  ∀ i, 1 ≤ i → i < n →
    ∃ (W₁ W₂ : Finset Pt) (P₁ P₂ : Finset (Sym2 Pt)) (x y u v : Pt),
      Disjoint W₁ W₂ ∧ W₁ ∪ W₂ = layerVerts n i ∧ P₁ ∪ P₂ = layerRestrict H i ∧
      x ∈ ifaceX i ∧ y ∈ ifaceY i ∧
      ((u ∈ ifaceA i ∧ v ∈ ifaceB i) ∨ (u ∈ ifaceB i ∧ v ∈ ifaceA i)) ∧
      IsPathOn W₁ P₁ x u ∧ IsPathOn W₂ P₂ y v

/-- `H` is a 2-regular subgraph of `G_n`: its edges are edges of `G_n` and every vertex lies on
exactly two of them. -/
def IsTwoRegularSubgraph {n : ℕ} (H : Finset (Sym2 (Vtx n))) : Prop :=
  (H : Set (Sym2 (Vtx n))) ⊆ (G n).edgeSet ∧ ∀ v : Vtx n, (H.filter (fun e => v ∈ e)).card = 2

end TwoOptAllExp.TSP


