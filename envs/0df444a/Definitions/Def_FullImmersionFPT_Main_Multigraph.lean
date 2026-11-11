-- Prove2me | Definitions.Def_FullImmersionFPT_Main_Multigraph
-- name    : FullImmersionFPT_Main_Multigraph
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T04:46:20.099003+00:00
-- url     : https://prove2.me/theorems/9bc44e05-bd3e-4d67-a84e-be912c771980
-- title:
--   Half-edge multigraphs: edges, degrees, cuts, k-edge-connectivity, Eulerian graphs, trails, shifting, splitting off, isomorphisms, treewidth and immersions (§§1, 5, 13.1, 18.1)
-- statement:
--   All graphs may have loops and parallel edges. A **multigraph** $G$ has a finite vertex set $V(G)$ and a finite set of **half-edges**; each half-edge $h$ sits at a vertex $\mathrm{inc}(h)$, and the half-edges are paired by a fixed-point-free involution $h\mapsto\mathrm{mate}(h)$: the **edge** of $h$ is the unordered pair $\{h,\mathrm{mate}(h)\}$ (a **loop** when both halves sit at the same vertex). The **degree** of $v$ is the number of half-edges at $v$; $G$ is $k$-**regular** if every vertex has degree $k$. $G$ is **connected** if it has a vertex and any two vertices are joined by a walk. For $S\subseteq V(G)$, the **cut** $\delta(S)$ is the set of edges with exactly one end in $S$ (a loop is never in a cut); $G$ is $k$-**edge-connected** if it is connected and $|\delta(S)|\ge k$ whenever $\emptyset\ne S\subsetneq V(G)$; $G$ is **Eulerian** if it is connected and every degree is even.
--
--   An **arc** is an edge with an orientation, named by its tail half-edge $h$ (from $\mathrm{inc}(h)$ to $\mathrm{inc}(\mathrm{mate}(h))$). A **trail** $T=\vec e_1\cdots\vec e_n$ is a sequence of arcs with pairwise distinct underlying edges, the head of each arc being the tail of the next; its **reversal** $T^{-1}$ reverses order and orientations. With labels $\lambda$ on edges, the weight of $T$ is $\lambda(T)=\sum_i\lambda(e_i)$; with colors $\alpha$ on half-edges, the **forward color** of $T$ is the union of the colors of its tail half-edges and the **backward color** the union of the colors of its head half-edges.
--
--   **Shifting** at $S$ by a vector $c$ adds $c$ to the label of every edge of $\delta(S)$; a **shifting** $\lambda'$ of $\lambda$ is the result of a sequence of shiftings.
--
--   **Splitting off** a vertex $v$ of degree four: pair its four half-edges into two pairs; for each pair $\{h_1,h_2\}$ delete the edges $e_1,e_2$ of $h_1,h_2$ and add a new edge joining their other ends, whose half-edges take the places of $\mathrm{mate}(h_1)$ and $\mathrm{mate}(h_2)$; delete $v$. If one of the edges is a loop at $v$ (not paired with itself), the two new edges are joined through the loop into a single edge. The new edge's label is the sum of the labels of the edges it replaces, and the half-edge replacing $\mathrm{mate}(h_1)$ gets the colors $\alpha(\mathrm{mate}(h_1))\cup\alpha(h_2)$ (and $\cup\,\alpha(h_4)$ when it passes through a loop). Footnote 2: two half-edges may not be paired if they belong to the same loop or to the same 2-edge cut.
--
--   Two labeled multigraphs are **isomorphic** if bijections of vertices and of half-edges commute with incidence and pairing and preserve labels. The **treewidth** of a multigraph is that of its underlying simple graph (published `RobertsonSeymour1986.GM5.TreewidthLE`). $G$ contains a simple graph $K$ as an **immersion** if distinct vertices $\varphi(a)$ of $G$ represent the vertices $a$ of $K$ and each edge $ab$ of $K$ is represented by a non-empty trail from $\varphi(a)$ to $\varphi(b)$, the trails being pairwise edge-disjoint (weak immersion, footnote 3).
--
--   **Formalization Note.** `Multigraph V H` holds `verts : Finset V`, `halves : Finset H`, `inc`, `mate`; `IsValid` says half-edges sit at vertices of the graph and `mate` is a fixed-point-free involution of `halves`. Edges are `s(h, mate h) : Sym2 H`; labels are functions on half-edges equal on both halves of an edge. A trail is a list of tail half-edges whose list together with its mates has no duplicate. `splitOff G v π` keeps the ambient types: it erases `v` and the half-edges at `v` and redirects `mate` along `splitVia`, which follows `π` through `v` (twice when a loop at `v` is traversed); `π` matters only on the half-edges at `v`. `IsLegalPairing` is footnote 2 verbatim: `π h ≠ mate h` and no `S ⊆ V(G)` with `δ(S) = {edge of h, edge of π h}`. Treewidth at least `k` means no tree-decomposition of width `< k`.
-- source:
--   Barabash, Geelen, McCarty, McFarland, Wollan, Finding full immersions is fixed-parameter tractable in labeled tour graphs, STOC 2027 submission (manuscript of November 2, 2026, sha256 c071967d…), pp. 2 (Section 1, footnote 2), 3 (footnote 3), 13 (§5), 18 (§8), 30 (§13.1), 56 (§18.1)

import Mathlib
import Definitions.Def_RobertsonSeymour1986_GM5_TreewidthLE
import Definitions.Def_RobertsonSeymour1986_GM5_grid

set_option autoImplicit false

/-!
# Half-edge multigraphs (§5, p. 13; §1, p. 2 and footnote 2; §13.1, p. 30; §18.1, p. 56)

Barabash, Geelen, McCarty, McFarland, Wollan, *Finding full immersions is fixed-parameter
tractable in labeled tour graphs* (STOC 2027 submission, manuscript of November 2, 2026).

"All graphs are undirected and may have loops and parallel edges. We consider each edge `e` to be
an unordered set `{h₁, h₂}` of two half-edges `h₁` and `h₂`, where `h₁` is only incident to one end
of `e` and `h₂` is incident to the other. (If `e` is a loop, then `h₁` and `h₂` are incident to the
same vertex.)" (§5, p. 13.)

Conventions.
* A multigraph lives on ambient types `V` (vertices) and `H` (half-edges): its vertex set `verts`
  and half-edge set `halves` are finite subsets, `inc h` is the vertex of `h` and `mate h` the other
  half-edge of the edge of `h`. Keeping the ambient types fixed lets splitting off delete vertices
  and half-edges without changing types.
* The edge of `h` is the unordered pair `s(h, mate h) : Sym2 H`; a set of edges is a
  `Finset (Sym2 H)`.
* An arc (oriented edge) is named by its tail half-edge `h`: it goes from `inc h` to
  `inc (mate h)`. A trail is the list of the tail half-edges of its arcs.
-/

namespace FullImmersionFPT.Main

open Classical

noncomputable section

/-- A finite multigraph with half-edges: vertex set `verts`, half-edge set `halves`, the vertex
`inc h` of each half-edge and the other half `mate h` of its edge. -/
structure Multigraph (V H : Type) where
  verts : Finset V
  halves : Finset H
  inc : H → V
  mate : H → H

namespace Multigraph

variable {V H : Type}

/-- Well-formedness: half-edges sit at vertices of the graph, and `mate` is a fixed-point-free
involution of the half-edges (each edge has exactly two half-edges). -/
def IsValid (G : Multigraph V H) : Prop :=
  (∀ h ∈ G.halves, G.inc h ∈ G.verts) ∧ (∀ h ∈ G.halves, G.mate h ∈ G.halves) ∧
    (∀ h ∈ G.halves, G.mate (G.mate h) = h) ∧ (∀ h ∈ G.halves, G.mate h ≠ h)

/-- The edge `{h, mate h}` containing the half-edge `h`. -/
def edgeOf (G : Multigraph V H) (h : H) : Sym2 H := s(h, G.mate h)

/-- The edge set `E(G)`. -/
def edges (G : Multigraph V H) : Finset (Sym2 H) := G.halves.image G.edgeOf

/-- The degree of `v`: the number of half-edges at `v` (a loop counts twice). -/
def deg (G : Multigraph V H) (v : V) : ℕ := (G.halves.filter fun h => G.inc h = v).card

/-- Every vertex has degree `k`. -/
def IsRegular (G : Multigraph V H) (k : ℕ) : Prop := ∀ v ∈ G.verts, G.deg v = k

/-- `u` and `w` are joined by an edge whose two ends lie in `A`. -/
def JoinsIn (G : Multigraph V H) (A : Set V) (u w : V) : Prop :=
  u ∈ A ∧ w ∈ A ∧ ∃ h ∈ G.halves, G.inc h = u ∧ G.inc (G.mate h) = w

/-- `u` and `w` are connected in the subgraph induced on `A` (reflexive). -/
def ConnectedIn (G : Multigraph V H) (A : Set V) (u w : V) : Prop :=
  Relation.ReflTransGen (G.JoinsIn A) u w

/-- `G` is connected: it has a vertex, and any two vertices are joined by a walk.
(Connected includes non-empty.) -/
def IsConnected (G : Multigraph V H) : Prop :=
  G.verts.Nonempty ∧ ∀ u ∈ G.verts, ∀ w ∈ G.verts, G.ConnectedIn (↑G.verts) u w

/-- The cut `δ(S)`: the edges with exactly one end in `S` (a loop is never in a cut). -/
def cut (G : Multigraph V H) (S : Finset V) : Finset (Sym2 H) :=
  (G.halves.filter fun h => G.inc h ∈ S ∧ G.inc (G.mate h) ∉ S).image G.edgeOf

/-- `G` is `k`-edge-connected: connected, and every cut `δ(S)` with `∅ ≠ S ⊊ V(G)` has at least
`k` edges. -/
def IsKEdgeConnected (G : Multigraph V H) (k : ℕ) : Prop :=
  G.IsConnected ∧ ∀ S ⊆ G.verts, S.Nonempty → S ≠ G.verts → k ≤ (G.cut S).card

/-- Eulerian (§1, p. 4): connected and every vertex has even degree. -/
def IsEulerian (G : Multigraph V H) : Prop :=
  G.IsConnected ∧ ∀ v ∈ G.verts, Even (G.deg v)

/-- A trail (§5, p. 13), written as the list of the tail half-edges of its arcs: every arc is a
half-edge of `G`, the underlying edges are pairwise distinct (no half-edge occurs twice in `T`
or together with its mate), and the head of each arc is the tail of the next. -/
def IsTrail (G : Multigraph V H) (T : List H) : Prop :=
  (∀ h ∈ T, h ∈ G.halves) ∧ (T ++ T.map G.mate).Nodup ∧
    ∀ (i : ℕ) (hi : i + 1 < T.length),
      G.inc (G.mate (T[i]'(by omega))) = G.inc (T[i + 1]'hi)

/-- A non-empty trail from `u` (its tail) to `w` (its head). -/
def IsTrailFrom (G : Multigraph V H) (T : List H) (u w : V) : Prop :=
  G.IsTrail T ∧ T ≠ [] ∧ T.head?.map G.inc = some u ∧
    T.getLast?.map (fun h => G.inc (G.mate h)) = some w

/-- The reversal `T⁻¹` of a trail: the arcs in reverse order and with reverse orientation. -/
def rev (G : Multigraph V H) (T : List H) : List H := (T.map G.mate).reverse

/-- The sum of the labels of the arcs of a trail (its weight). -/
def trailSum {L : Type} [AddCommMonoid L] (lab : H → L) (T : List H) : L := (T.map lab).sum

/-- The forward color of a trail (§13.1, p. 30): the union of the colors of its tail half-edges. -/
def fwdColor {C : Type} (col : H → Finset C) (T : List H) : Finset C :=
  T.toFinset.biUnion col

/-- The backward color of a trail: the union of the colors of its head half-edges. -/
def bwdColor {C : Type} (G : Multigraph V H) (col : H → Finset C) (T : List H) : Finset C :=
  T.toFinset.biUnion fun h => col (G.mate h)

/-! ## Shifting -/

/-- Shifting at `S` by the vector `c`: add `c` to the label of every edge of `δ(S)`
(§1, p. 2; §13.1, p. 30). Labels are stored on both half-edges of an edge. -/
def shiftAt {L : Type} [Add L] (G : Multigraph V H) (lab : H → L) (S : Finset V) (c : L) :
    H → L :=
  fun h => if (G.inc h ∈ S ∧ G.inc (G.mate h) ∉ S) ∨ (G.inc h ∉ S ∧ G.inc (G.mate h) ∈ S)
    then lab h + c else lab h

/-- `lab'` is obtained from `lab` by a sequence of shiftings ("shiftings `λ′` of `λ`"). -/
def IsShiftingOf {L : Type} [Add L] (G : Multigraph V H) (lab lab' : H → L) : Prop :=
  Relation.ReflTransGen (fun l₁ l₂ => ∃ (S : Finset V) (c : L), l₂ = G.shiftAt l₁ S c) lab lab'

/-! ## Splitting off a vertex -/

/-- A pairing of the four half-edges at `v` (§1, p. 2, footnote 2; §18.1): `π` maps each half-edge
at `v` to a different half-edge at `v`, and `π (π h) = h`. -/
def IsPairingAt (G : Multigraph V H) (v : V) (π : H → H) : Prop :=
  ∀ h ∈ G.halves, G.inc h = v →
    π h ∈ G.halves ∧ G.inc (π h) = v ∧ π h ≠ h ∧ π (π h) = h

/-- Footnote 2 (p. 2): two half-edges may not be paired if they belong to the same loop or to the
same 2-edge cut. -/
def IsLegalPairing (G : Multigraph V H) (v : V) (π : H → H) : Prop :=
  ∀ h ∈ G.halves, G.inc h = v →
    π h ≠ G.mate h ∧ ¬ ∃ S ⊆ G.verts, G.cut S = {G.edgeOf h, G.edgeOf (π h)}

/-- The half-edges at `v` that a new edge passes through when `v` is split off with the pairing
`π`, starting from the half-edge `h` (not at `v`): if `mate h = g₁` is at `v`, the new edge leaves
`v` through `g₂ = π g₁`; if `g₂` belongs to a loop at `v`, it continues through the other half
`g₃ = mate g₂` of that loop and leaves through `π g₃` ("the two new edges are joined through the
loop into a single edge", §18.1). The list holds the half-edges `π g₁` (and `π g₃`). -/
def splitVia (G : Multigraph V H) (v : V) (π : H → H) (h : H) : List H :=
  if G.inc (G.mate h) ≠ v then []
  else if G.inc (G.mate (π (G.mate h))) ≠ v then [π (G.mate h)]
  else [π (G.mate h), π (G.mate (π (G.mate h)))]

/-- The new mate of `h` after splitting off `v`: the far half-edge of the new edge. -/
def splitMate (G : Multigraph V H) (v : V) (π : H → H) (h : H) : H :=
  match (G.splitVia v π h).getLast? with
  | none => G.mate h
  | some g => G.mate g

/-- Splitting off `v` with the pairing `π` (§1, p. 2; §8, p. 18; §18.1, items 1–4): delete `v`
and its half-edges; each pair `{h₁, h₂}` joins the other ends of the edges of `h₁` and `h₂` by a
new edge whose half-edges take the places of `mate h₁` and `mate h₂`. -/
def splitOff (G : Multigraph V H) (v : V) (π : H → H) : Multigraph V H where
  verts := G.verts.erase v
  halves := G.halves.filter fun h => G.inc h ≠ v
  inc := G.inc
  mate := G.splitMate v π

/-- The labels after splitting off: the new edge gets the sum of the labels of the edges it
replaces (§1, p. 2; §18.1, item 5). -/
def splitLabel {L : Type} [AddCommMonoid L] (G : Multigraph V H) (v : V) (π : H → H)
    (lab : H → L) : H → L :=
  fun h => lab h + ((G.splitVia v π h).map lab).sum

/-- The colors after splitting off (§18.1, item 6): the half-edge `g₁` taking the place of `h₁′`
gets `α(h₁′) ∪ α(h₂)` (and `∪ α(h₄)` when the edge passes through a loop). -/
def splitColor {C : Type} (G : Multigraph V H) (v : V) (π : H → H) (col : H → Finset C) :
    H → Finset C :=
  fun h => col h ∪ (G.splitVia v π h).toFinset.biUnion col

/-! ## Isomorphism -/

/-- An isomorphism of labeled multigraphs: bijections of the vertices and of the half-edges that
commute with `inc` and `mate` and preserve the labels. -/
def IsIsoLabeled {V' H' L : Type} (G : Multigraph V H) (lab : H → L) (K : Multigraph V' H')
    (lab' : H' → L) : Prop :=
  ∃ (φ : V → V') (ψ : H → H'), Set.BijOn φ ↑G.verts ↑K.verts ∧ Set.BijOn ψ ↑G.halves ↑K.halves ∧
    ∀ h ∈ G.halves, K.inc (ψ h) = φ (G.inc h) ∧ K.mate (ψ h) = ψ (G.mate h) ∧ lab' (ψ h) = lab h

/-! ## Treewidth and immersions of simple graphs -/

/-- The underlying simple graph on `V(G)`: two distinct vertices are adjacent when an edge joins
them (loops and parallel edges are dropped; they do not affect treewidth). -/
def simple (G : Multigraph V H) : SimpleGraph ↥G.verts :=
  SimpleGraph.fromRel fun u w => ∃ h ∈ G.halves, G.inc h = u.1 ∧ G.inc (G.mate h) = w.1

/-- `G` has treewidth at least `k`: the underlying simple graph has no tree-decomposition of width
`< k` (published `RobertsonSeymour1986.GM5.TreewidthLE`). For `k = 0` this always holds. -/
def TreewidthAtLeast (G : Multigraph V H) (k : ℕ) : Prop :=
  ∀ w : ℕ, w < k → ¬ RobertsonSeymour1986.GM5.TreewidthLE G.simple w

/-- `G` has treewidth at most `k`. -/
def TreewidthAtMost (G : Multigraph V H) (k : ℕ) : Prop :=
  RobertsonSeymour1986.GM5.TreewidthLE G.simple k

/-- `G` contains the simple graph `K` as an immersion (footnote 3, p. 3: weak immersions):
distinct vertices `φ a` of `G` for the vertices `a` of `K`, and for each edge `ab` of `K` a
non-empty trail `T a b` of `G` from `φ a` to `φ b` (with `T b a` its reversal), the trails of
different edges of `K` being edge-disjoint. -/
def ImmersesSimple {W : Type} (G : Multigraph V H) (K : SimpleGraph W) : Prop :=
  ∃ (φ : W → V) (T : W → W → List H), Function.Injective φ ∧ (∀ a, φ a ∈ G.verts) ∧
    (∀ a b, K.Adj a b → G.IsTrailFrom (T a b) (φ a) (φ b) ∧ T b a = G.rev (T a b)) ∧
    ∀ g ∈ G.halves, ∀ a b a' b', K.Adj a b → K.Adj a' b' → g ∈ T a b → g ∈ T a' b' →
      a = a' ∧ b = b'

end Multigraph

end

end FullImmersionFPT.Main


