-- Prove2me | Definitions.Def_OnlineStochMatching_TSM_Coloring
-- name    : OnlineStochMatching_TSM_Coloring
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T21:22:16.125836+00:00
-- url     : https://prove2.me/theorems/9a45520b-3a4a-47e9-8dc7-09384b7638b8
-- title:
--   The maximum flow edge set $E_f$ of the boosted flow graph, its blue/red colouring, and the ad classes $A_{BR}, A_{BB}, A_B, A_R$ (Section 4.2.1–4.2.2)
-- statement:
--   Let $G = (A, I, E)$ be a finite bipartite graph of advertisers and impression types. The **boosted flow graph** $G_f$ has a source $s$ with an arc of capacity $2$ to every advertiser, an arc of capacity $1$ from $a$ to $i$ for every edge $(a, i) \in E$, and an arc of capacity $2$ from every impression type to a sink $t$. An integral flow of $G_f$ is described by the set $F \subseteq E$ of middle arcs that carry flow; these are exactly the edge sets in which every advertiser and every impression type has at most two edges, and the flow value is $|F|$. The set $E_f$ is such an edge set of **maximum** cardinality, i.e. the edge set of an integral maximum flow.
--
--   The graph induced by $E_f$ is a disjoint union of paths and cycles. A **TSM colouring** splits $E_f$ into blue and red edges component by component, following the rules of the paper:
--   1. on a cycle, the edges alternate blue and red;
--   2. on a path of odd length, the edges alternate blue and red, with more blue than red;
--   3. on a path of even length whose ends are advertisers, the edges alternate blue and red;
--   4. on a path of even length whose ends are impression types, the first two edges are blue, and then the edges alternate red, blue, red, …, ending in blue.
--
--   The rules leave the phase on a cycle and the choice of the "first" end of a path open; every such choice is a TSM colouring.
--
--   Given a colouring, the advertisers are classified by their coloured edges: $A_{BR}$ (one blue and one red edge), $A_{BB}$ (two blue edges), $A_B$ (only a blue edge) and $A_R$ (only a red edge).
--
--   These objects define the two suggested matchings that guide the online algorithm, and the quantities in which the paper bounds both ALG and OPT.
--
--   **Formalization Note** A colouring is given by a listing of components, each a vertex sequence $v_0, \dots, v_k$ in $A \oplus I$ with a flag "path" or "cycle": consecutive vertices are joined by edges of $E_f$; a path has pairwise distinct vertices; a cycle has $k \ge 4$, $v_k = v_0$ and distinct $v_0, \dots, v_{k-1}$. Distinct components are vertex-disjoint and together cover $E_f$, so each is a whole connected component. The $j$-th edge ($j = 0, \dots, k-1$) is blue iff $j$ is even, except on an even path between impression types, where it is blue iff $j = 0$ or $j$ is odd. Rules stated only locally (degree conditions at each vertex) would admit colourings the paper excludes, so the per-component rule is kept. The classes are defined by the numbers of blue and red edges at the advertiser: $(1,1)$, $(2,0)$, $(1,0)$, $(0,1)$.
-- source:
--   Feldman, Mehta, Mirrokni, Muthukrishnan, Online Stochastic Matching: Beating 1-1/e, arXiv:0905.4100v1, pp. 6–7, Section 4.2.1 (boosted flow graph, colouring rules); p. 7, Section 4.2.2 (A_BR, A_B, A_BB, A_R)

import Mathlib

namespace OnlineStochMatching.TSM

open Finset

variable {A I : Type}

/-- The number of edges of `F ⊆ A × I` at the advertiser `a`. -/
def degA [DecidableEq A] (F : Finset (A × I)) (a : A) : ℕ :=
  (F.filter fun e => e.1 = a).card

/-- The number of edges of `F ⊆ A × I` at the impression type `i`. -/
def degI [DecidableEq I] (F : Finset (A × I)) (i : I) : ℕ :=
  (F.filter fun e => e.2 = i).card

/-- An integral flow of the boosted flow graph `G_f` (Feldman, Mehta, Mirrokni, Muthukrishnan,
*Online Stochastic Matching: Beating 1-1/e*, arXiv:0905.4100v1, §4.2.1, p. 6), given by its set of
saturated middle edges. `G_f` has a source `s` with an arc of capacity 2 to every advertiser
`a ∈ A`, an arc of capacity 1 from `a` to `i` for every `(a, i) ∈ E`, and an arc of capacity 2
from every impression type `i ∈ I` to the sink `t`. An integral flow is determined by the set
`F ⊆ E` of middle arcs carrying (unit) flow, the flow on `(s, a)` being `deg_F(a)` and on `(i, t)`
being `deg_F(i)`; so integral flows are exactly the sets `F ⊆ E` with at most two edges at every
advertiser and at most two at every impression type, and the flow value is `|F|`. -/
def IsTwoMatching [DecidableEq A] [DecidableEq I] (E F : Finset (A × I)) : Prop :=
  F ⊆ E ∧ (∀ a, degA F a ≤ 2) ∧ ∀ i, degI F i ≤ 2

/-- `E_f` (§4.2.1, p. 6): the edge set of an integral **maximum** flow of `G_f`, i.e. a set as in
`IsTwoMatching` of maximum cardinality. -/
def IsMaxFlowSet [DecidableEq A] [DecidableEq I] (E F : Finset (A × I)) : Prop :=
  IsTwoMatching E F ∧ ∀ F' : Finset (A × I), IsTwoMatching E F' → F'.card ≤ F.card

/-- A walk in the bipartite graph on `A ⊕ I`, used to list one connected component of the graph
induced by `E_f`: the vertices `v 0, v 1, …, v len` in order, `len ≥ 1` edges, and a flag `cyc`
telling whether the component is a cycle (then `v len = v 0`) or a path. -/
structure Comp (A I : Type) where
  /-- The number of edges. -/
  len : ℕ
  /-- The vertices, in order; only `v 0, …, v len` matter. -/
  v : ℕ → A ⊕ I
  /-- `true` for a cycle, `false` for a path. -/
  cyc : Bool

/-- The `j`-th edge of the component (`j < len`), joining `v j` and `v (j+1)`, is `e = (a, i)`. -/
def Comp.HasEdgeAt (C : Comp A I) (j : ℕ) (e : A × I) : Prop :=
  (C.v j = Sum.inl e.1 ∧ C.v (j + 1) = Sum.inr e.2) ∨
    (C.v j = Sum.inr e.2 ∧ C.v (j + 1) = Sum.inl e.1)

/-- The vertex set `{v 0, …, v len}` of the component. -/
def Comp.verts [DecidableEq A] [DecidableEq I] (C : Comp A I) : Finset (A ⊕ I) :=
  (Finset.range (C.len + 1)).image C.v

/-- `C` is a path or a cycle of the graph induced by `F`: it has at least one edge, each of its
consecutive vertex pairs is an edge of `F` (so consecutive vertices lie on opposite sides), and
either `C` is a path with pairwise distinct vertices `v 0, …, v len`, or `C` is a cycle with at least
four edges, `v len = v 0` and pairwise distinct vertices `v 0, …, v (len - 1)`. -/
def Comp.IsPathOrCycle (F : Finset (A × I)) (C : Comp A I) : Prop :=
  1 ≤ C.len ∧
  (∀ j < C.len, ∃ e ∈ F, C.HasEdgeAt j e) ∧
  (if C.cyc = true then
      4 ≤ C.len ∧ C.v C.len = C.v 0 ∧
        ∀ j₁ < C.len, ∀ j₂ < C.len, C.v j₁ = C.v j₂ → j₁ = j₂
    else ∀ j₁ ≤ C.len, ∀ j₂ ≤ C.len, C.v j₁ = C.v j₂ → j₁ = j₂)

/-- `C` is a path of even length whose end vertices are impressions. -/
def Comp.IsEvenImpressionPath (C : Comp A I) : Prop :=
  C.cyc = false ∧ Even C.len ∧ (C.v 0).isRight = true

/-- The colouring rule of §4.2.1 (pp. 6–7), read along the listed order of the component: the
`j`-th edge is **blue** iff
* `j` is even, for a cycle (edges alternate blue and red);
* `j` is even, for a path of odd length (alternating, both end edges blue, so more blue than red);
* `j` is even, for a path of even length between two advertisers (alternating);
* `j = 0` or `j` is odd, for a path of even length between two impressions (the first two edges
  blue, then red, blue, red, …, ending in blue).
Every other edge of the component is red. The choices the rules leave open (the phase on a cycle,
which end of a path comes first) are the choice of the listing. -/
def Comp.BlueAt (C : Comp A I) (j : ℕ) : Prop :=
  (C.IsEvenImpressionPath ∧ (j = 0 ∨ Odd j)) ∨ (¬ C.IsEvenImpressionPath ∧ Even j)

/-- The two colour classes `blue, red ⊆ E_f` arise from the TSM colouring of §4.2.1 (pp. 6–7):
"Since the capacities of edges `(s, a)` and `(i, t)` are all 2, we know that the graph induced by
`E_f` is a collection of paths and cycles", and blue/red are assigned per component by the rules of
`Comp.BlueAt`. Concretely, there is a listing `C 0, …, C (m-1)` of components such that every `C k`
is a path or a cycle of `F`, distinct components are vertex-disjoint, every edge of `F` occurs in
some component, and an edge is blue (resp. red) iff it occurs in a component at a position that the
rule colours blue (resp. red). Vertex-disjointness together with covering `F` makes each `C k` a
whole connected component of the graph induced by `F`. -/
def IsTSMColoring [DecidableEq A] [DecidableEq I] (F blue red : Finset (A × I)) : Prop :=
  ∃ (m : ℕ) (C : Fin m → Comp A I),
    (∀ k, (C k).IsPathOrCycle F) ∧
    (∀ k k', k ≠ k' → Disjoint (C k).verts (C k').verts) ∧
    (∀ e ∈ F, ∃ k, ∃ j < (C k).len, (C k).HasEdgeAt j e) ∧
    (∀ e, e ∈ blue ↔ ∃ k, ∃ j < (C k).len, (C k).HasEdgeAt j e ∧ (C k).BlueAt j) ∧
    (∀ e, e ∈ red ↔ ∃ k, ∃ j < (C k).len, (C k).HasEdgeAt j e ∧ ¬ (C k).BlueAt j)

/-- `A_BR` (§4.2.2, p. 7): the advertisers incident to one blue and one red edge. -/
def adsBR [Fintype A] [DecidableEq A] (blue red : Finset (A × I)) : Finset A :=
  Finset.univ.filter fun a => degA blue a = 1 ∧ degA red a = 1

/-- `A_BB` (§4.2.2, p. 7): the advertisers incident to two blue edges (and no red edge). -/
def adsBB [Fintype A] [DecidableEq A] (blue red : Finset (A × I)) : Finset A :=
  Finset.univ.filter fun a => degA blue a = 2 ∧ degA red a = 0

/-- `A_B` (§4.2.2, p. 7): the advertisers incident to only a blue edge (one blue edge, no red). -/
def adsB [Fintype A] [DecidableEq A] (blue red : Finset (A × I)) : Finset A :=
  Finset.univ.filter fun a => degA blue a = 1 ∧ degA red a = 0

/-- `A_R` (§4.2.2, p. 7): the advertisers incident to only a red edge (one red edge, no blue). -/
def adsR [Fintype A] [DecidableEq A] (blue red : Finset (A × I)) : Finset A :=
  Finset.univ.filter fun a => degA blue a = 0 ∧ degA red a = 1

end OnlineStochMatching.TSM


