-- Prove2me | Definitions.Def_MatroidSensOracle_Supplement_GraphProblems
-- name    : MatroidSensOracle_Supplement_GraphProblems
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:04:19.477178+00:00
-- url     : https://prove2.me/theorems/046a204d-c83a-47f8-9f45-e5d341064730
-- title:
--   Graph problems of §§4–10: cuts, connectivity, spanning trees, arborescences, forests, colorful trees, $\alpha$-factors, matchings; undirected, colored and subset updates
-- statement:
--   This module fixes the graph notions used by the supplement, all on the base mission's directed cost multigraphs.
--
--   1. **Undirected inputs.** An undirected input graph on $V=\{0,\dots,n-1\}$ is an input graph whose every edge is written $(a,b)$ with $a<b$ (p.39). The updated graph $G+U$ is the base multigraph, read undirected: an edge joins its tail and its head.
--   2. **Undirected notions on a multigraph.** A set $X$ of edges is a *forest* if every nonempty vertex set $S$ spans at most $|S|-1$ edges of $X$. A *spanning tree* is a forest with $|V|-1$ edges. An *$r$-rooted spanning arborescence* is a spanning tree of the underlying undirected graph in which $r$ has in-degree $0$ and every other vertex in-degree $1$ (p.32). The *degree* of $v$ in $X$ counts the edges of $X$ with tail $v$ plus those with head $v$. An *$\alpha$-factor* is a set in which every $v$ has degree $\alpha(v)$ (p.39), and a *matching* one in which every degree is at most $1$. $c(G)$ is the number of connected components.
--   3. **Cuts.** $\mu_G(s)=\min_{v\ne s}\lambda_G(s,v)$ and $\mu_G=\min_s\mu_G(s)$ (p.30). An $s$-min-cut is a vertex set $A\ni s$, $A\ne V$, of out-capacity $\mu_G(s)$; a global min-cut is a nonempty proper $A$ of out-capacity $\mu_G$.
--   4. **Colored graphs.** A coloring $\chi:V\times V\to\{0,\dots,n-2\}$ is read on the edges (p.34). A colored update inserts edges with a cost and a color, deletes edges and changes colors, each counting one. A *colorful spanning tree* is a spanning tree with exactly one edge of each color.
--   5. **Subset model.** A susceptible set $E_Q$ of pairs, possibly not in $E$ (p.45); a query $U\subseteq E_Q$ deletes $U\cap E$ and inserts $U\setminus E$.
--   6. **Encodings.** The word encodings of instances and queries.
--
--   Minimum costs take values in $\mathbb Z\cup\{+\infty\}$, with $+\infty$ when no feasible structure exists.
--
--   **Formalization Note** $\mu_G(s)$ and $\mu_G$ are natural-number infima of nonempty sets as soon as $|V|\ge 2$, the case in which every theorem uses them.
-- source:
--   Choudhary, Kumar, Saggi, Sensitivity Oracles for Matroid Packing, Matroid Covering, and Matching Problems with Applications, arXiv:2609.01283 (held version, sha256 0de50841…), §4 p.23, §5.3 p.30, §6 pp.32–35, §8 p.39, §9.1 p.45 (PDF pp.26, 33, 35–38, 42, 48)

import Mathlib
import Definitions.Def_MatroidSensOracle_InputGraph
import Definitions.Def_MatroidSensOracle_LinearMatroid

set_option autoImplicit false

namespace MatroidSensOracle.Supplement

/-!
# Graph problems of §§4–10: cuts, connectivity, trees, arborescences, forests, colorful trees,
# `α`-factors, matchings; undirected and colored inputs, subset (toggle) updates, word encodings

Choudhary, Kumar, Saggi, arXiv:2609.01283 (held version, sha256 0de50841…).
* §4, p.23 (PDF p.26): "For an update U = (F, I) […] we denote by c(G + U) the number of connected
  components in the updated graph G + U."
* §5.3, p.30 (PDF p.33): "For a fixed source s ∈ V, the s-min-cut value in G is
  μ_G(s) := min_{v∈V∖{s}} λ_G(s, v). The global min-cut value is μ_G := min_{s∈V} μ_G(s)."
* §6.1, p.32 (PDF p.35): "A valid z-rooted spanning arborescence in H is a set of N − 1 edges
  forming a spanning tree in the underlying undirected graph, where every vertex v ∈ V_H ∖ {z} has
  exactly one incoming edge, and z has no incoming edges."
* §6.2, p.33 (PDF p.36): "A spanning tree is a maximal acyclic subgraph of G, containing exactly
  n − 1 edges." §6.4, p.35 (PDF p.38): "The forest packing problem […] asks whether the entire active
  edge set E can be partitioned into k disjoint forests."
* §6.3, p.34 (PDF p.37): "The edge set E is partitioned into exactly n − 1 disjoint color classes
  […]. A colorful spanning tree is a spanning tree of G containing exactly one edge from each color
  class."
* §8, p.39 (PDF p.42): "we define a (perfect) α-factor as a subgraph H of G such that every vertex
  v ∈ V has degree exactly α(v) in H. […] The minimum-cost α-factor is the α-factor with minimum
  total edge cost"; "an edge e in G is written as (a, b), where a < b".
* §9.1, p.45 (PDF p.48): "a set of susceptible edges E_Q (which may include edges not currently in
  E) subject to insertions or deletions. Any query (s, t, U) satisfies s, t ∈ V_Q and U ⊆ E_Q with
  |U| ⩽ f."

**Formalization Note.**
* **Directed inputs** are the base `InputGraph n` (simple: `E ⊆ V × V`), updates the base `Update n`,
  and `G + U` the base multigraph `G.plus U`.
* **Undirected inputs** are `InputGraph n` whose every edge is written `(a, b)` with `a < b` (p.39),
  so there are no loops and no parallel edges in the input. An inserted edge joins two distinct
  vertices (in either order; it may be parallel to an existing edge). `G + U` is the base multigraph
  `G.plus U`, read **undirected**: an edge joins its tail and its head.
* On a multigraph read undirected: `X` is a **forest** iff every nonempty vertex set `S` spans at
  most `|S| − 1` edges of `X` (the graphic-matroid independence; a cycle on `S` spans `|S|` edges);
  a **spanning tree** is a forest with `|V| − 1` edges; vertices are **connected** when they are in
  one component of the simple graph whose adjacency is "joined by an edge"; the **degree** of `v` in
  `X` counts the edges of `X` with tail `v` plus those with head `v`.
* An **arborescence rooted at `r`** is read directly from p.32: a spanning tree of the underlying
  undirected graph in which `r` has in-degree `0` and every other vertex in-degree `1`.
  "`k`-disjoint" families are `k` pairwise edge-disjoint members (`SplitsInto`); their cost is the
  total cost of the union.
* `μ_G(s)` and `μ_G` are the minima of the base `maxFlow` (an `sInf` in `ℕ` over a set that is
  nonempty as soon as `|V| ≥ 2`, the case in which they are used). An `s`-min-cut is a source side
  `A ∋ s`, `A ≠ V`, of capacity `μ_G(s)`; a global min-cut a nonempty proper `A` of capacity `μ_G`.
* **Subset model** (§9): a susceptible set `E_Q` of pairs (each with its cost `G.cost e`, and colour
  `χ e` for coloured graphs), which may contain pairs not in `E`; a query `U ⊆ E_Q` deletes `U ∩ E`
  and inserts `U ∖ E` (`toggle`).
* **Coloured graphs** (§6.3): a colouring `χ : V × V → Fin (n − 1)` read on the edges. A coloured
  update inserts edges with a cost and a colour, deletes edges of `E`, and changes the colour of
  edges (each counts one); `G + U` is the coloured multigraph `cplus`.
-/

open CostMultigraph

variable {n : ℕ}

/-! ## Inputs, updates, toggles -/

/-- Every edge of the input is written `(a, b)` with `a < b`: an undirected simple loopless graph. -/
def _root_.MatroidSensOracle.InputGraph.Undirected (G : InputGraph n) : Prop :=
  ∀ e ∈ G.E, e.1 < e.2

/-- Costs on `E ∪ E_Q` lie in `[−W, W]`. -/
def _root_.MatroidSensOracle.InputGraph.CostsBoundedOn (G : InputGraph n) (EQ : Finset (Fin n × Fin n))
    (W : ℕ) : Prop :=
  ∀ e ∈ G.E ∪ EQ, |G.cost e| ≤ W

/-- An update of a directed graph with at most `f` updates and no cost condition: `F ⊆ E`,
`|I| + |F| ≤ f`. -/
def _root_.MatroidSensOracle.InputGraph.ValidPlain (G : InputGraph n) (f : ℕ) (U : Update n) : Prop :=
  U.del ⊆ G.E ∧ U.size ≤ f

/-- A valid update of an undirected graph: `F ⊆ E`, `|I| + |F| ≤ f`, inserted costs in `[−W, W]`,
every inserted edge joins two distinct vertices. -/
def _root_.MatroidSensOracle.InputGraph.ValidU (G : InputGraph n) (f W : ℕ) (U : Update n) : Prop :=
  G.ValidUpdate f W U ∧ ∀ x ∈ U.ins, x.1 ≠ x.2.1

/-- A valid update of an undirected graph without costs: `F ⊆ E`, `|I| + |F| ≤ f`, every inserted
edge joins two distinct vertices. -/
def _root_.MatroidSensOracle.InputGraph.ValidUPlain (G : InputGraph n) (f : ℕ) (U : Update n) : Prop :=
  G.ValidPlain f U ∧ ∀ x ∈ U.ins, x.1 ≠ x.2.1

/-- The subset (toggle) update of `U ⊆ E_Q`: delete `U ∩ E`, insert the pairs of `U ∖ E` with their
costs. -/
def _root_.MatroidSensOracle.InputGraph.toggle (G : InputGraph n) (U : Finset (Fin n × Fin n)) :
    Update n :=
  ⟨(pairList n (U \ G.E)).map (fun e => (e.1, e.2, G.cost e)), U ∩ G.E⟩

/-! ## Undirected notions on a multigraph -/

section Multigraph

variable {V : Type} [DecidableEq V] [Fintype V]

/-- `X` is a forest of the multigraph read undirected: every nonempty vertex set `S` spans at most
`|S| − 1` edges of `X`. -/
def IsForest (G : CostMultigraph V) (X : Finset (Fin G.m)) : Prop :=
  ∀ S : Finset V, S.Nonempty →
    (X.filter fun e => G.arcs.tail e ∈ S ∧ G.arcs.head e ∈ S).card + 1 ≤ S.card

/-- `X` is a spanning tree: a forest with `|V| − 1` edges. -/
def IsSpanningTree (G : CostMultigraph V) (X : Finset (Fin G.m)) : Prop :=
  IsForest G X ∧ X.card + 1 = Fintype.card V

/-- The number of edges of `X` with head `v`. -/
def inDeg (G : CostMultigraph V) (X : Finset (Fin G.m)) (v : V) : ℕ :=
  (X.filter fun e => G.arcs.head e = v).card

/-- The degree of `v` in `X`, read undirected: edges with tail `v` plus edges with head `v`. -/
def deg (G : CostMultigraph V) (X : Finset (Fin G.m)) (v : V) : ℕ :=
  (X.filter fun e => G.arcs.tail e = v).card + (X.filter fun e => G.arcs.head e = v).card

/-- `X` is a spanning arborescence rooted at `r`: a spanning tree of the underlying undirected graph
in which `r` has no incoming edge and every other vertex exactly one. -/
def IsArborescence (G : CostMultigraph V) (r : V) (X : Finset (Fin G.m)) : Prop :=
  IsSpanningTree G X ∧ inDeg G X r = 0 ∧ ∀ v, v ≠ r → inDeg G X v = 1

/-- The cost of a set of edges. -/
def edgeCost (G : CostMultigraph V) (X : Finset (Fin G.m)) : ℤ := ∑ e ∈ X, G.cost e

/-- `G` has `k` pairwise edge-disjoint members of the family `P`. -/
def HasKDisjoint (G : CostMultigraph V) (P : Finset (Fin G.m) → Prop) (k : ℕ) : Prop :=
  ∃ S : Finset (Fin G.m), SplitsInto P k S

open Classical in
/-- The least total cost of `k` pairwise edge-disjoint members of `P` (`⊤` if there are none). -/
noncomputable def minKDisjointCost (G : CostMultigraph V) (P : Finset (Fin G.m) → Prop) (k : ℕ) :
    WithTop ℤ :=
  (Finset.univ.filter fun S => SplitsInto P k S).inf fun S => ((edgeCost G S : ℤ) : WithTop ℤ)

/-- The edge set of `G` partitions into `k` forests. -/
def PartitionsIntoForests (G : CostMultigraph V) (k : ℕ) : Prop :=
  SplitsInto (IsForest G) k Finset.univ

/-- The simple graph of `G` read undirected: `u ≠ v` adjacent iff some edge joins them. -/
def adj (G : CostMultigraph V) : SimpleGraph V :=
  SimpleGraph.fromRel fun u v => ∃ e, G.arcs.tail e = u ∧ G.arcs.head e = v

/-- `x` and `y` are connected in `G` (read undirected). -/
def Connected (G : CostMultigraph V) (x y : V) : Prop := (adj G).Reachable x y

/-- The number `c(G)` of connected components of `G` (read undirected). -/
noncomputable def compCount (G : CostMultigraph V) : ℕ := Nat.card (adj G).ConnectedComponent

/-- `X` is an `α`-factor: every vertex `v` has degree exactly `α v` in `X`. -/
def IsFactor (G : CostMultigraph V) (α : V → ℕ) (X : Finset (Fin G.m)) : Prop :=
  ∀ v, deg G X v = α v

/-- `G` has an `α`-factor. -/
def HasFactor (G : CostMultigraph V) (α : V → ℕ) : Prop := ∃ X, IsFactor G α X

open Classical in
/-- The least cost of an `α`-factor (`⊤` if there is none). -/
noncomputable def minFactorCost (G : CostMultigraph V) (α : V → ℕ) : WithTop ℤ :=
  (Finset.univ.filter fun X => IsFactor G α X).inf fun X => ((edgeCost G X : ℤ) : WithTop ℤ)

/-- `X` is a matching: every vertex has degree at most `1` in `X`. -/
def IsMatching (G : CostMultigraph V) (X : Finset (Fin G.m)) : Prop := ∀ v, deg G X v ≤ 1

open Classical in
/-- The maximum size of a matching. -/
noncomputable def maxMatching (G : CostMultigraph V) : ℕ :=
  (Finset.univ.filter fun X => IsMatching G X).sup Finset.card

/-- `X` is a colorful spanning tree for the edge colouring `col`: a spanning tree containing exactly
one edge of each colour. -/
def IsColorful {κ : Type} [Fintype κ] [DecidableEq κ] (G : CostMultigraph V) (col : Fin G.m → κ)
    (X : Finset (Fin G.m)) : Prop :=
  IsSpanningTree G X ∧ ∀ c : κ, (X.filter fun e => col e = c).card = 1

/-- `μ_G(s) = min_{v ≠ s} λ_G(s, v)`. -/
noncomputable def sMinCutValue (G : CostMultigraph V) (s : V) : ℕ :=
  sInf {k : ℕ | ∃ v, v ≠ s ∧ G.maxFlow s v = k}

/-- `μ_G = min_s μ_G(s)`. -/
noncomputable def globalMinCutValue (G : CostMultigraph V) : ℕ :=
  sInf {k : ℕ | ∃ s, sMinCutValue G s = k}

/-- `A` is (the source side of) an `s`-min-cut: `s ∈ A ≠ V` with capacity `μ_G(s)`. -/
def IsSMinCut (G : CostMultigraph V) (s : V) (A : Finset V) : Prop :=
  s ∈ A ∧ A ≠ Finset.univ ∧ G.cutCapacity A = sMinCutValue G s

/-- `A` is (the source side of) a global min-cut: `∅ ≠ A ≠ V` with capacity `μ_G`. -/
def IsGlobalMinCut (G : CostMultigraph V) (A : Finset V) : Prop :=
  A.Nonempty ∧ A ≠ Finset.univ ∧ G.cutCapacity A = globalMinCutValue G

end Multigraph

/-! ## Coloured graphs -/

/-- A coloured update: insertions `(u, v, cost, colour)`, deletions `F ⊆ E`, and colour changes
`(e, new colour)` of edges of `E ∖ F`. -/
structure CUpdate (n : ℕ) where
  ins : List (Fin n × Fin n × ℤ × Fin (n - 1))
  del : Finset (Fin n × Fin n)
  recol : List ((Fin n × Fin n) × Fin (n - 1))

/-- `|U|`: insertions, deletions and colour changes each count one. -/
def CUpdate.size (U : CUpdate n) : ℕ := U.ins.length + U.del.card + U.recol.length

/-- The colour of the surviving edge `e` after `U`: its last new colour in `U`, else `χ e`. -/
def CUpdate.colorOf (U : CUpdate n) (χ : Fin n × Fin n → Fin (n - 1)) (e : Fin n × Fin n) :
    Fin (n - 1) :=
  ((U.recol.filter fun r => r.1 = e).getLast?.map Prod.snd).getD (χ e)

/-- A valid coloured update of an undirected graph: `F ⊆ E`, recoloured edges in `E ∖ F`, at most
`f` updates, inserted costs in `[−W, W]`, inserted edges join distinct vertices. -/
def CUpdate.Valid (G : InputGraph n) (f W : ℕ) (U : CUpdate n) : Prop :=
  U.del ⊆ G.E ∧ (∀ r ∈ U.recol, r.1 ∈ G.E \ U.del) ∧ U.size ≤ f ∧
    ∀ x ∈ U.ins, |x.2.2.1| ≤ W ∧ x.1 ≠ x.2.1

/-- The edges `(u, v, cost, colour)` of the coloured multigraph `G + U`: the edges of `E ∖ F`
(lexicographically) with their current colours, then the inserted edges. -/
def cEdges (G : InputGraph n) (χ : Fin n × Fin n → Fin (n - 1)) (U : CUpdate n) :
    List (Fin n × Fin n × ℤ × Fin (n - 1)) :=
  (pairList n (G.E \ U.del)).map (fun e => (e.1, e.2, G.cost e, U.colorOf χ e)) ++ U.ins

/-- The multigraph of a list of coloured edges. -/
def cGraph (L : List (Fin n × Fin n × ℤ × Fin (n - 1))) : CostMultigraph (Fin n) :=
  CostMultigraph.ofList (L.map fun x => (x.1, x.2.1, x.2.2.1))

/-- The colour of each edge of `cGraph L`. -/
def cColor (L : List (Fin n × Fin n × ℤ × Fin (n - 1))) (e : Fin (cGraph L).m) : Fin (n - 1) :=
  (L.get (Fin.cast (by simp [cGraph, CostMultigraph.ofList]) e)).2.2.2

/-- The coloured multigraph `G + U` has a colorful spanning tree. -/
def HasColorfulTree (L : List (Fin n × Fin n × ℤ × Fin (n - 1))) : Prop :=
  ∃ X, IsColorful (cGraph L) (cColor L) X

open Classical in
/-- The least cost of a colorful spanning tree of the coloured multigraph (`⊤` if there is none). -/
noncomputable def minColorfulCost (L : List (Fin n × Fin n × ℤ × Fin (n - 1))) : WithTop ℤ :=
  (Finset.univ.filter fun X => IsColorful (cGraph L) (cColor L) X).inf
    fun X => ((edgeCost (cGraph L) X : ℤ) : WithTop ℤ)

/-- The coloured subset (toggle) update of `U ⊆ E_Q`: delete `U ∩ E`, insert `U ∖ E` with its cost
and colour `χ`. -/
def ctoggle (G : InputGraph n) (χ : Fin n × Fin n → Fin (n - 1)) (U : Finset (Fin n × Fin n)) :
    CUpdate n :=
  ⟨(pairList n (U \ G.E)).map (fun e => (e.1, e.2, G.cost e, χ e)), U ∩ G.E, []⟩

/-! ## Word encodings -/

/-- The edges of `E` as words `tail, head, cost`, lexicographically. -/
def edgeWords (G : InputGraph n) (E : Finset (Fin n × Fin n)) : List ℤ :=
  (pairList n E).flatMap fun e => [((e.1 : ℕ) : ℤ), ((e.2 : ℕ) : ℤ), G.cost e]

/-- The input words of an instance: the parameters `ps`, then `m = |E|` and the edges of `E`. -/
def encodeWith (G : InputGraph n) (ps : List ℤ) : List ℤ :=
  ps ++ [((pairList n G.E).length : ℤ)] ++ edgeWords G G.E

/-- A set of pairs as words: its size, then `tail, head` of each pair, lexicographically. -/
def pairWords (S : Finset (Fin n × Fin n)) : List ℤ :=
  [((pairList n S).length : ℤ)] ++ (pairList n S).flatMap fun e => [((e.1 : ℕ) : ℤ), ((e.2 : ℕ) : ℤ)]

/-- A set of vertices as words: its size, then its members in increasing order. -/
def vertWords (S : Finset (Fin n)) : List ℤ :=
  [(S.card : ℤ)] ++ ((List.finRange n).filter fun v => v ∈ S).map fun v => ((v : ℕ) : ℤ)

/-- The input words of a subset instance: `encodeWith G ps`, then `|E_Q|` and the pairs of `E_Q`
with their costs, then the vertex set `V_Q`. -/
def encodeSubset (G : InputGraph n) (ps : List ℤ) (EQ : Finset (Fin n × Fin n))
    (VQ : Finset (Fin n)) : List ℤ :=
  encodeWith G ps ++ [((pairList n EQ).length : ℤ)] ++ edgeWords G EQ ++ vertWords VQ

/-- The coloured edges of `E` as words `tail, head, cost, colour`. -/
def cEdgeWords (G : InputGraph n) (χ : Fin n × Fin n → Fin (n - 1)) (E : Finset (Fin n × Fin n)) :
    List ℤ :=
  (pairList n E).flatMap fun e => [((e.1 : ℕ) : ℤ), ((e.2 : ℕ) : ℤ), G.cost e, ((χ e : ℕ) : ℤ)]

/-- The input words of a coloured instance: `ps`, then `m` and the coloured edges of `E`, then
`|E_Q|` and the coloured pairs of `E_Q` (`E_Q = ∅` in the general setting). -/
def encodeColored (G : InputGraph n) (χ : Fin n × Fin n → Fin (n - 1)) (ps : List ℤ)
    (EQ : Finset (Fin n × Fin n)) : List ℤ :=
  ps ++ [((pairList n G.E).length : ℤ)] ++ cEdgeWords G χ G.E ++ [((pairList n EQ).length : ℤ)] ++
    cEdgeWords G χ EQ

/-- The query words of a coloured update: insertions `(u, v, cost, colour)`, deletions `(u, v)`,
colour changes `(u, v, colour)`, each list preceded by its length. -/
def CUpdate.encode (U : CUpdate n) : List ℤ :=
  [(U.ins.length : ℤ)] ++
    U.ins.flatMap (fun x => [((x.1 : ℕ) : ℤ), ((x.2.1 : ℕ) : ℤ), x.2.2.1, ((x.2.2.2 : ℕ) : ℤ)]) ++
    pairWords U.del ++ [(U.recol.length : ℤ)] ++
    U.recol.flatMap fun r => [((r.1.1 : ℕ) : ℤ), ((r.1.2 : ℕ) : ℤ), ((r.2 : ℕ) : ℤ)]

/-- The set of vertices read off a final memory: `v` belongs iff the low bit of word `v` is set. -/
def outSet {w : ℕ} (mQ : ℤ → BitVec w) : Finset (Fin n) :=
  Finset.univ.filter fun v : Fin n => (mQ (v : ℕ)).getLsbD 0 = true

end MatroidSensOracle.Supplement


