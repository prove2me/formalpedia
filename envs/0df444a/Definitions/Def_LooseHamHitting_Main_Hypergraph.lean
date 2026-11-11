-- Prove2me | Definitions.Def_LooseHamHitting_Main_Hypergraph
-- name    : LooseHamHitting_Main_Hypergraph
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T03:17:22.187972+00:00
-- url     : https://prove2.me/theorems/612da0c6-a971-4cbf-8080-5094fc2678d8
-- title:
--   3-graphs, degrees and codegrees, Berge paths, perfect matchings, loose Hamilton cycles, (G, M)-respecting mixed Hamilton cycles, Φ, root orientation and Ψ
-- statement:
--   Fix a finite **vertex set** $V$ (a `Finset` of an arbitrary type). A hypergraph is identified with its edge set; a **3-graph on $V$** is a family $G$ of 3-element subsets of $V$, and $|G|$ is its number of edges.
--
--   * **Degrees.** $d_G(v)$ is the number of edges containing $v$, $d_G(u,v)$ the number containing both $u$ and $v$. Over the vertex set $V$: $\delta_1(G)=\min_{v\in V}d_G(v)$ ($0$ if $V=\emptyset$), $\Delta_1(G)=\max_{v\in V}d_G(v)$, $\Delta_2(G)=\max_{u\neq v\in V}d_G(u,v)$, and the average degree $d(G)=3|G|/|V|$.
--   * **Operations.** $G-S=\{e\in G:e\cap S=\emptyset\}$ (a 3-graph on $V\setminus S$); $G[A,B]=\{e\in G:|e\cap A|=2,\ |e\cap B|=1\}$; the link $L_G(v)=\{e\setminus\{v\}: v\in e\in G\}$.
--   * **Berge path** of length $h$: distinct vertices $v_0,\dots,v_h$ and distinct edges $e_1,\dots,e_h\in G$ with $\{v_{i-1},v_i\}\subseteq e_i$.
--   * **Matchings.** A matching $M$ of pairs on $V$ is a family of pairwise disjoint 2-subsets of $V$; $V(M)$ is the set of $M$-saturated vertices. A **perfect matching** of $G$ is a set of pairwise disjoint edges of $G$ covering $V$; $F(u)$ is the edge of $F$ containing $u$.
--   * **Cyclic loose ordering** of an edge set $C$: an enumeration $e_0,\dots,e_{L-1}$ of $C$ without repetition, $L\ge 3$, indices mod $L$, such that $|e_i\cap e_{i+1}|=1$ for every $i$, the intersection vertices $e_i\cap e_{i+1}$ are distinct for distinct $i$, and $e_i\cap e_j=\emptyset$ whenever $i,j$ are distinct and not consecutive.
--   * **Loose Hamilton cycle** of a 3-graph $H$ on $V$ (p. 1): $C\subseteq H$ with $\bigcup C=V$ admitting a cyclic loose ordering.
--   * **Mixed Hamilton cycle** (Definition 3.1): $C$ is a $(G,M)$-respecting mixed Hamilton cycle on $V$ if it contains every pair of $M$, every other member is a triple of $G$, $\bigcup C=V$, and $C$ admits a cyclic loose ordering. $\Phi(G,M)$ is the number of such $C$ (counted as edge sets).
--   * **Private / intersection vertices** of a cycle: vertices of $V$ in exactly one / exactly two edges of $C$.
--   * **Traversal and root orientation** (pp. 8, 10). In an ordering, $e_i$ is traversed from $a$ to $b$ when $a\in e_{i-1}\cap e_i$ and $b\in e_i\cap e_{i+1}$. With a root pair $\{r_1,r_2\}\in M$ directed $r_1\to r_2$, $C$ traverses $f$ from $a$ to $b$ in the root orientation if some ordering of $C$ traverses the root pair from $r_1$ to $r_2$ and $f$ from $a$ to $b$ (for a triple $f=\{a,b,w\}$ this makes $w$ private). Then
--   $$\Psi_{G,M}(x;y\to z)=\#\{C\ (G-x,\,M\cup\{yz\})\text{-respecting on }V\setminus\{x\}:\ C\text{ traverses }yz\text{ from }y\text{ to }z\}.$$
--   * $\vec G-V(M)$: the oriented triples $(w;u\to v)$ with $\{u,v,w\}\in G$, $u,v,w$ distinct and outside $V(M)$. $K_M=\{e\in\binom V3:|e\cap V(M)|\le1\}$ are the $M$-compatible triples.
--
--   **Formalization Note.** A cyclic ordering is `e : Fin L → Finset α` with successor `finRotate L`; requiring $L\ge3$ and one intersection vertex per position excludes the degenerate one- and two-edge "cycles". The count $\Phi$ ranges over subsets of $G\cup M$. Brute force on these definitions gives 120 loose Hamilton cycles in $\binom{[6]}{3}$, $\Phi=120$ for $(n,s)=(7,1)$, $96$ for $(8,2)$, and $\Psi/\Phi=1/105$ at $n=9$, $s=1$, matching Lemma 3.3(i) and (3.1).
-- source:
--   León, Liu, Hitting time for loose Hamilton cycles in the random hypergraph process, arXiv:2610.29894v1, p. 1 (loose Hamilton cycle); pp. 7–8 (§3 notation, Definition 3.1); p. 10 (Ψ); p. 17 (perfect matchings)

import Mathlib

set_option autoImplicit false

/-!
# 3-graphs, loose Hamilton cycles and (G, M)-respecting mixed Hamilton cycles

León, Liu, *Hitting time for loose Hamilton cycles in the random hypergraph process*,
arXiv:2610.29894v1, p. 1 (loose Hamilton cycle), pp. 7–8 (§3 notation, Definition 3.1),
p. 10 (root orientation, `Ψ`), p. 17 (perfect matchings).

A hypergraph is identified with its edge set, a `Finset (Finset α)`; its vertex set is a separate
`Finset α`, so that `G − S` lives on `V \ S`. A 3-graph on `V` has every edge a 3-subset of `V`.
-/

namespace LooseHamHitting.Main

noncomputable section

open Classical

variable {α : Type*}

/-- `G` is a 3-graph on the vertex set `V`: every edge is a 3-element subset of `V`. -/
def IsThreeGraph (V : Finset α) (G : Finset (Finset α)) : Prop :=
  ∀ e ∈ G, e ⊆ V ∧ e.card = 3

/-- Vertex degree `d_G(v)`: the number of edges containing `v`. -/
def degree (G : Finset (Finset α)) (v : α) : ℕ :=
  (G.filter (fun e => v ∈ e)).card

/-- Codegree `d_G(u, v)`: the number of edges containing both `u` and `v`. -/
def codegree (G : Finset (Finset α)) (u v : α) : ℕ :=
  (G.filter (fun e => u ∈ e ∧ v ∈ e)).card

/-- Minimum vertex degree `δ₁(G)` over the vertex set `V` (`0` when `V = ∅`). -/
def minDegree (V : Finset α) (G : Finset (Finset α)) : ℕ :=
  if h : V.Nonempty then V.inf' h (degree G) else 0

/-- Maximum vertex degree `Δ₁(G)` over the vertex set `V`. -/
def maxDegree (V : Finset α) (G : Finset (Finset α)) : ℕ :=
  V.sup (degree G)

/-- Maximum codegree `Δ₂(G)`: the largest codegree of two distinct vertices of `V`. -/
def maxCodegree (V : Finset α) (G : Finset (Finset α)) : ℕ :=
  V.offDiag.sup (fun p => codegree G p.1 p.2)

/-- Average degree `d(G) := 3|G|/|V(G)|` of a 3-graph on `V`. -/
def avgDegree (V : Finset α) (G : Finset (Finset α)) : ℝ :=
  3 * (G.card : ℝ) / (V.card : ℝ)

/-- `G − S`: the edges of `G` disjoint from `S` (the hypergraph lives on `V \ S`). -/
def deleteVerts (G : Finset (Finset α)) (S : Finset α) : Finset (Finset α) :=
  G.filter (fun e => Disjoint e S)

/-- `G[A, B] := {e ∈ G : |e ∩ A| = 2 and |e ∩ B| = 1}`. -/
def crossEdges (G : Finset (Finset α)) (A B : Finset α) : Finset (Finset α) :=
  G.filter (fun e => (e ∩ A).card = 2 ∧ (e ∩ B).card = 1)

/-- The link `L_G(v)`: the pairs `ab` with `vab ∈ G`. -/
def link (G : Finset (Finset α)) (v : α) : Finset (Finset α) :=
  (G.filter (fun e => v ∈ e)).image (fun e => e.erase v)

/-- A Berge path of length `h` in `G`: distinct vertices `v 0, …, v h` and distinct edges
`e 1, …, e h` of `G` (indexed from `0` here) with `{v (i-1), v i} ⊆ e i`. -/
def IsBergePath (G : Finset (Finset α)) (h : ℕ) (v : Fin (h + 1) → α) (e : Fin h → Finset α) :
    Prop :=
  Function.Injective v ∧ Function.Injective e ∧
    ∀ i : Fin h, e i ∈ G ∧ v i.castSucc ∈ e i ∧ v i.succ ∈ e i

/-- `M` is a matching of pairs on `V`: its members are pairwise disjoint 2-subsets of `V`. -/
def IsMatching (V : Finset α) (M : Finset (Finset α)) : Prop :=
  (∀ p ∈ M, p ⊆ V ∧ p.card = 2) ∧ (M : Set (Finset α)).PairwiseDisjoint id

/-- `V(M)`: the vertices covered by the pairs of `M` (the `M`-saturated vertices). -/
def matchedVerts (M : Finset (Finset α)) : Finset α :=
  M.biUnion id

/-- `F` is a perfect matching of the 3-graph `G` on `V`: pairwise disjoint edges of `G`
covering `V`. -/
def IsPerfectMatching (V : Finset α) (G F : Finset (Finset α)) : Prop :=
  F ⊆ G ∧ (F : Set (Finset α)).PairwiseDisjoint id ∧ F.biUnion id = V

/-- The finite set of perfect matchings of `G` on `V`. -/
def perfectMatchings (V : Finset α) (G : Finset (Finset α)) : Finset (Finset (Finset α)) :=
  G.powerset.filter (fun F => IsPerfectMatching V G F)

/-- The edge of `F` containing `u`, encoded as the set of edges of `F` that contain `u`
(a singleton when `F` is a perfect matching). This is the random variable `F(u)`. -/
def edgeAt (F : Finset (Finset α)) (u : α) : Finset (Finset α) :=
  F.filter (fun f => u ∈ f)

/-- A cyclic ordering `e 0, …, e (L-1)` (indices mod `L`, successor `finRotate L`) of the edge
set `C` in which consecutive edges meet in exactly one vertex, these intersection vertices are
distinct (one per position), and nonconsecutive edges are disjoint. At least three edges. -/
def IsCyclicLooseOrder (C : Finset (Finset α)) (L : ℕ) (e : Fin L → Finset α) : Prop :=
  3 ≤ L ∧ Function.Injective e ∧ Finset.univ.image e = C ∧
    (∀ i, (e i ∩ e (finRotate L i)).card = 1) ∧
    (∀ i j, i ≠ j → Disjoint (e i ∩ e (finRotate L i)) (e j ∩ e (finRotate L j))) ∧
    (∀ i j, i ≠ j → j ≠ finRotate L i → i ≠ finRotate L j → Disjoint (e i) (e j))

/-- A loose Hamilton cycle of the 3-graph `H` on `V` (p. 1): a spanning subhypergraph `C ⊆ H`
whose edges cover `V` and admit a cyclic loose ordering. -/
def IsLooseHamCycle (V : Finset α) (H C : Finset (Finset α)) : Prop :=
  C ⊆ H ∧ C.biUnion id = V ∧ ∃ L, ∃ e : Fin L → Finset α, IsCyclicLooseOrder C L e

/-- `H` (on `V`) contains a loose Hamilton cycle. -/
def ContainsLooseHamCycle (V : Finset α) (H : Finset (Finset α)) : Prop :=
  ∃ C, IsLooseHamCycle V H C

/-- Definition 3.1(i): a `(G, M)`-respecting mixed Hamilton cycle on `V`: a hypergraph consisting
of all pairs of `M` and triples of `G`, covering `V`, with a cyclic loose ordering. -/
def IsMixedHamCycle (V : Finset α) (G M C : Finset (Finset α)) : Prop :=
  M ⊆ C ∧ (∀ f ∈ C, f ∈ M ∨ (f ∈ G ∧ f.card = 3)) ∧ C.biUnion id = V ∧
    ∃ L, ∃ e : Fin L → Finset α, IsCyclicLooseOrder C L e

/-- The finite set of `(G, M)`-respecting mixed Hamilton cycles on `V` (as edge sets). -/
def mixedHamCycles (V : Finset α) (G M : Finset (Finset α)) : Finset (Finset (Finset α)) :=
  (G ∪ M).powerset.filter (fun C => IsMixedHamCycle V G M C)

/-- Definition 3.1(iii): `Φ(G, M)`, the number of `(G, M)`-respecting mixed Hamilton cycles. -/
def Phi (V : Finset α) (G M : Finset (Finset α)) : ℕ :=
  (mixedHamCycles V G M).card

/-- Number of edges of `C` containing `v`. -/
def cycleDegree (C : Finset (Finset α)) (v : α) : ℕ :=
  (C.filter (fun f => v ∈ f)).card

/-- Private vertices of a cycle: the vertices of `V` in exactly one edge of `C`. -/
def privateVerts (V : Finset α) (C : Finset (Finset α)) : Finset α :=
  V.filter (fun v => cycleDegree C v = 1)

/-- Intersection vertices of a cycle: the vertices of `V` in exactly two edges of `C`. -/
def intersectionVerts (V : Finset α) (C : Finset (Finset α)) : Finset α :=
  V.filter (fun v => cycleDegree C v = 2)

/-- In the ordering `e`, the edge `e i` is traversed from `a` to `b`: `a` is its intersection
vertex with the previous edge and `b` its intersection vertex with the next edge. -/
def TraversesAt (L : ℕ) (e : Fin L → Finset α) (i : Fin L) (a b : α) : Prop :=
  a ∈ e i ∧ a ∈ e ((finRotate L).symm i) ∧ b ∈ e i ∧ b ∈ e (finRotate L i)

/-- In the root orientation of the cycle `C` (the one traversing the root pair `{r₁, r₂}` from
`r₁` to `r₂`), the edge `f` of `C` is traversed from `a` to `b`. For a triple `f = {a, b, w}`
this says `w` is its private vertex. -/
def RootTraverses (C : Finset (Finset α)) (r₁ r₂ : α) (f : Finset α) (a b : α) : Prop :=
  ∃ L, ∃ e : Fin L → Finset α, IsCyclicLooseOrder C L e ∧
    (∃ i, e i = {r₁, r₂} ∧ TraversesAt L e i r₁ r₂) ∧ (∃ j, e j = f ∧ TraversesAt L e j a b)

/-- `Ψ_{G,M}(x; y → z)` (p. 10), root pair `{r₁, r₂}` directed `r₁ → r₂`: the number of
`(G − x, M ∪ {yz})`-respecting mixed Hamilton cycles on `V \ {x}` traversing `yz` from `y` to `z`
in the root orientation. -/
def Psi (V : Finset α) (G M : Finset (Finset α)) (r₁ r₂ x y z : α) : ℕ :=
  ((mixedHamCycles (V.erase x) (deleteVerts G {x}) (insert {y, z} M)).filter
    (fun C => RootTraverses C r₁ r₂ {y, z} y z)).card

/-- The oriented triples `(w; u → v)` of `G⃗ − V(M)`, encoded as `(w, u, v)`: distinct vertices of
`V \ V(M)` with `{u, v, w} ∈ G`. -/
def orientedTriplesOff (V : Finset α) (G M : Finset (Finset α)) : Finset (α × α × α) :=
  let W := V \ matchedVerts M
  (W ×ˢ W ×ˢ W).filter (fun t =>
    t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2 ∧ ({t.2.1, t.2.2, t.1} : Finset α) ∈ G)

/-- The triples of `V` meeting `V(M)` in at most one vertex (`M`-compatible triples). -/
def compatibleTriples (V : Finset α) (M : Finset (Finset α)) : Finset (Finset α) :=
  (V.powersetCard 3).filter (fun e => (e ∩ matchedVerts M).card ≤ 1)

end

end LooseHamHitting.Main


