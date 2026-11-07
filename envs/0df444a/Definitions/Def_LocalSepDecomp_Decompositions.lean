-- Prove2me | Definitions.Def_LocalSepDecomp_Decompositions
-- name    : LocalSepDecomp_Decompositions
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:41:15.154692+00:00
-- url     : https://prove2.me/theorems/f43ad30b-1741-4a2a-a9a8-d69340cc5dc9
-- title:
--   Graph-decompositions with parts, tree-decompositions, canonicity, isomorphism, contraction, folding; tangles and trees of tangles
-- statement:
--   1. A **graph-decomposition with parts** $(H,\mathcal G)$ of $G$ consists of a multigraph $H$ and subgraphs $G_h\subseteq G$, $h\in V(H)$, such that (H1′) $G=\bigcup_hG_h$ and (H2) for every vertex $v$ the sub-multigraph of $H$ induced on $W_v=\{h:v\in V(G_h)\}$ is connected. It is a **tree-decomposition** if $H$ is a tree (no loops or parallel edges) and every part is the induced subgraph on its bag; an edge $t_1t_2$ of the tree then **induces** the separation $\{A_1,A_2\}$ with $A_i$ the union of the bags in the component of $T-t_1t_2$ containing $t_i$.
--   2. It is **$\Gamma$-canonical** if $\Gamma\le\operatorname{Aut}(G)$ acts on $H$ by automorphisms with $\varphi(G_h)=G_{\varphi(h)}$. An **isomorphism** of decompositions is a pair of bijections of nodes and edges respecting incidences and parts.
--   3. For a set $F$ of edges, $H/F$ contracts the edges in $F$ (keeping loops and parallel edges), the part of a branch set being the union of the parts of its nodes; $H$ **refines** $H/F$.
--   4. **Folding** (Construction 2.6): for a decomposition of a covering $C$ of $G$ on which the deck transformations act, the folded decomposition has the orbits of nodes and edges as nodes and edges, and the part $p(G_t)$ for the orbit of $t$.
--   5. A **tangle of order $k$** (Diestel §12.5) is a set $\tau$ of oriented separations of order $<k$ containing exactly one orientation of each separation of order $<k$, with no three elements $(A_i,B_i)$ such that $G[A_1]\cup G[A_2]\cup G[A_3]=G$. A separation **distinguishes** two tangles if they orient it differently, **efficiently** if no separation of smaller order does. A **tree of tangles of scope $k$** is a nested set of separations containing an efficient distinguisher of every two $(\le k)$-distinguishable tangles, and a **tangle tree-decomposition of scope $k$** is a tree-decomposition whose induced separations form one.
--
--   These are the decomposition notions in which the paper's main theorem is stated.
--
--   **Formalization Note** A multigraph is a node type, an edge type and an end map to unordered pairs (loops allowed). The folding takes the orbit relations of the deck action as input; ends and parts are computed from representatives. In a tangle, $(A,B)\in\tau$ means that $\tau$ orients $\{A,B\}$ towards $B$.
-- source:
--   Jacobs, Knappe, Kurkofka, Canonical Graph Decompositions via Local Separations, preprint (STOC 2027 submission, arXiv:2501.16170; sha256 9a11d48d…), §2.3 (pp.16–18), §3.1–3.2 (pp.20, 23), §8.4 (pp.54, 56); tangles from Diestel, Graph Theory, 6th ed., §12.5, cited on pp.1 and 20

import Mathlib
import Definitions.Def_LocalSepDecomp_Crossing

set_option autoImplicit false

namespace LocalSepDecomp

/-! # Graph-decompositions with parts, tree-decompositions, canonicity, isomorphism,
contraction, folding along a covering; tangles and trees of tangles

R. W. Jacobs, P. Knappe, J. Kurkofka, *Canonical Graph Decompositions via Local Separations*,
preprint (STOC 2027 submission, arXiv:2501.16170; sha256 9a11d48d…), §2.3 (pp.16–18), §3.1–3.2
(pp.20, 23), §8.4 (pp.54, 56); tangles as in R. Diestel, *Graph Theory*, 6th ed., §12.5 (cited
by the paper on pp.1 and 20 for the definition).

**Formalization Note.**
1. A multigraph (loops and parallel edges allowed) is a node type, an edge type and an end map
   `ends : Edge → Sym2 Node` (a loop has diagonal ends). A graph-decomposition with parts carries
   a part `G_h` (a subgraph of `G`) for every node; its bag is the vertex set of the part.
2. (H2) is required for the co-bags `W_v = {h : v ∈ V(G_h)}`: the sub-multigraph of `H` induced on
   `W_v` is connected (non-empty, any two nodes of `W_v` joined through edges with both ends in
   `W_v`).
3. Tree-decompositions have induced parts `G_t = G[V_t]` (the paper's convention, pp.16–17), and
   a multigraph is a tree if it has no loops, no parallel edges, and its underlying simple graph
   is a tree.
4. Folding (Construction 2.6) takes the orbit relations of the action of the deck transformation
   group on the nodes and on the edges; nodes and edges of the folded decomposition are their
   classes, ends and parts are computed from a representative (the paper's "for `t ∈ h`").
5. A tangle of order `k` is a set `τ` of oriented separations of order `< k` containing exactly one
   orientation of every separation of order `< k`, with no three (not necessarily distinct)
   elements `(A₁, B₁), (A₂, B₂), (A₃, B₃)` such that `G[A₁] ∪ G[A₂] ∪ G[A₃] = G`; `(A, B) ∈ τ`
   means that `τ` orients `{A, B}` towards `B`. -/

open SimpleGraph

universe u w w'

variable {V : Type u}

/-- A candidate graph-decomposition with parts `(H, G)` of `G` (p.16): a multigraph `H`
(nodes, edges, ends) and a part `G_h ⊆ G` for every node `h`. -/
structure GraphDecomp (G : SimpleGraph V) where
  Node : Type w
  Edge : Type w
  ends : Edge → Sym2 Node
  part : Node → G.Subgraph

variable {G : SimpleGraph V}

/-- The co-bag `W_v = {h ∈ V(H) : v ∈ V_h}` of a vertex `v` (p.16). -/
def GraphDecomp.coBag (D : GraphDecomp.{u, w} G) (v : V) : Set D.Node :=
  {h | v ∈ (D.part h).verts}

/-- The sub-multigraph of `H` induced on the node set `S` is connected: `S` is non-empty and any
two nodes of `S` are joined by a walk through edges with both ends in `S`. -/
def GraphDecomp.InducedConnected (D : GraphDecomp.{u, w} G) (S : Set D.Node) : Prop :=
  S.Nonempty ∧ ∀ a ∈ S, ∀ b ∈ S,
    Relation.ReflTransGen (fun x y => ∃ e, D.ends e = s(x, y) ∧ x ∈ S ∧ y ∈ S) a b

/-- `(H, G)` is a **graph-decomposition** of `G` with parts (p.16): (H1′) `G = ⋃_h G_h`
(vertices and edges), and (H2) for every vertex `v` the sub-multigraph `H[W_v]` is connected. -/
def IsGraphDecomp (D : GraphDecomp.{u, w} G) : Prop :=
  (⨆ h, D.part h) = ⊤ ∧ ∀ v, D.InducedConnected (D.coBag v)

/-- The underlying simple graph of the multigraph `H`: distinct nodes joined by an edge. -/
def GraphDecomp.simpleGraph (D : GraphDecomp.{u, w} G) : SimpleGraph D.Node :=
  SimpleGraph.fromRel (fun a b => ∃ e, D.ends e = s(a, b))

/-- The multigraph `H` is a **tree**: no loops, no parallel edges, and its underlying simple graph
is connected and acyclic. -/
def GraphDecomp.IsMultiTree (D : GraphDecomp.{u, w} G) : Prop :=
  (∀ e, ¬ (D.ends e).IsDiag) ∧ Function.Injective D.ends ∧ D.simpleGraph.IsTree

/-- `(T, G)` is a **tree-decomposition** (with parts) of `G` (pp.16–17): a graph-decomposition
whose decomposition graph is a tree and whose parts are the induced subgraphs `G[V_t]`. -/
def IsTreeDecomp (D : GraphDecomp.{u, w} G) : Prop :=
  IsGraphDecomp D ∧ D.IsMultiTree ∧ ∀ t, D.part t = (⊤ : G.Subgraph).induce (D.part t).verts

/-- For an edge `e` of the tree `T` and a node `t`, the union `⋃_{t' ∈ T_t} V_{t'}` of the bags of
the nodes reachable from `t` without using `e` (for an end `tᵢ` of `e`, this is `A^e_i`, p.17). -/
def GraphDecomp.sideOf (D : GraphDecomp.{u, w} G) (e : D.Edge) (t : D.Node) : Set V :=
  ⋃ (t' : D.Node) (_ : Relation.ReflTransGen (fun a b => ∃ e', e' ≠ e ∧ D.ends e' = s(a, b)) t t'),
    (D.part t').verts

/-- The separation `{A^e_1, A^e_2}` **induced** by the edge `e = t₁t₂` of a tree-decomposition
(p.17), where `A^e_i = ⋃_{t ∈ T_i} V_t` and `T_i` is the component of `T − t₁t₂` containing
`tᵢ`. -/
def GraphDecomp.inducedSep (D : GraphDecomp.{u, w} G) (e : D.Edge) : Sym2 (Set V) :=
  Sym2.map (D.sideOf e) (D.ends e)

/-- `(H, G)` is **`Γ`-canonical** (p.17): there is an action of `Γ ≤ Aut(G)` on `H` by
automorphisms of `H` (pairs of a node and an edge permutation respecting the ends) that
commutes with the parts: `φ(G_h) = G_{φ(h)}`. -/
def IsCanonicalDecomp (Γ : Subgroup (G ≃g G)) (D : GraphDecomp.{u, w} G) : Prop :=
  ∃ (ρV : Γ →* Equiv.Perm D.Node) (ρE : Γ →* Equiv.Perm D.Edge),
    (∀ φ e, D.ends (ρE φ e) = Sym2.map (ρV φ) (D.ends e)) ∧
    ∀ φ h, D.part (ρV φ h) = (D.part h).map (φ : G ≃g G).toHom

/-- An **isomorphism** of graph-decompositions with parts of `G` (p.54): bijections of nodes and
of edges respecting incidences, under which corresponding nodes have the same part. -/
structure DecompIso (D : GraphDecomp.{u, w} G) (D' : GraphDecomp.{u, w'} G) where
  node : D.Node ≃ D'.Node
  edge : D.Edge ≃ D'.Edge
  ends_eq : ∀ e, D'.ends (edge e) = Sym2.map node (D.ends e)
  part_eq : ∀ h, D'.part (node h) = D.part h

/-- The contraction `H/F` (p.56): contract the edges in `F` (keeping loops and parallel edges);
the nodes are the branch sets (classes of the equivalence relation generated by "joined by an
edge in `F`"), the edges are the edges not in `F`, and the part of a branch set is the union of
the parts of its nodes. -/
def contract (D : GraphDecomp.{u, w} G) (F : Set D.Edge) : GraphDecomp.{u, w} G where
  Node := Quot (fun a b : D.Node => ∃ e ∈ F, D.ends e = s(a, b))
  Edge := {e : D.Edge // e ∉ F}
  ends e := Sym2.map (Quot.mk _) (D.ends e.1)
  part h := ⨆ (h' : D.Node) (_ : Quot.mk _ h' = h), D.part h'

/-- Folding a graph-decomposition `D` of a cover `C` via `p : C → G` (Construction 2.6, p.17),
given the orbit relations `relV`, `relE` of the deck-transformation action on the nodes and the
edges of `D`: the nodes and edges are the orbits, the ends of the orbit of `e = st` are the orbits
of `s` and `t`, and the part of the orbit `h` is `p(G_t)` for `t ∈ h`. -/
noncomputable def foldDecomp {W : Type u} {C : SimpleGraph W} (D : GraphDecomp.{u, w} C)
    (p : C →g G) (relV : D.Node → D.Node → Prop) (relE : D.Edge → D.Edge → Prop) :
    GraphDecomp.{u, w} G where
  Node := Quot relV
  Edge := Quot relE
  ends e := Sym2.map (Quot.mk relV) (D.ends e.out)
  part h := (D.part h.out).map p

/-! ## Tangles (Diestel §12.5) and trees of tangles (p.20, p.23) -/

/-- `G[A₁] ∪ G[A₂] ∪ G[A₃] = G`: every vertex lies in some `Aᵢ` and every edge has both ends in
some `Aᵢ`. -/
def CoversByThree (G : SimpleGraph V) (A₁ A₂ A₃ : Set V) : Prop :=
  (∀ v, v ∈ A₁ ∨ v ∈ A₂ ∨ v ∈ A₃) ∧
    ∀ a b, G.Adj a b → (a ∈ A₁ ∧ b ∈ A₁) ∨ (a ∈ A₂ ∧ b ∈ A₂) ∨ (a ∈ A₃ ∧ b ∈ A₃)

/-- `τ` is a **tangle of order `k`** in `G` (Diestel §12.5): a set of oriented separations of order
`< k` containing exactly one orientation of each separation of order `< k`, with no three elements
`(A₁, B₁), (A₂, B₂), (A₃, B₃)` such that `G[A₁] ∪ G[A₂] ∪ G[A₃] = G`. -/
def IsTangle (G : SimpleGraph V) (k : ℕ) (τ : Set (Set V × Set V)) : Prop :=
  (∀ q ∈ τ, IsSep G q ∧ sepOrder q < k) ∧
    (∀ q : Set V × Set V, IsSep G q → sepOrder q < k → (q ∈ τ ↔ (q.2, q.1) ∉ τ)) ∧
    ∀ q₁ ∈ τ, ∀ q₂ ∈ τ, ∀ q₃ ∈ τ, ¬ CoversByThree G q₁.1 q₂.1 q₃.1

/-- `τ` is a tangle in `G` (of some order `k ∈ ℕ`). -/
def IsTangleIn (G : SimpleGraph V) (τ : Set (Set V × Set V)) : Prop := ∃ k : ℕ, IsTangle G k τ

/-- The separation `{A, B}` **distinguishes** `τ` and `τ'` (p.20): they orient it to different
sides. -/
def Distinguishes (u : Sym2 (Set V)) (τ τ' : Set (Set V × Set V)) : Prop :=
  ∃ q : Set V × Set V, unorientSep q = u ∧ q ∈ τ ∧ (q.2, q.1) ∈ τ'

/-- `u` distinguishes `τ` and `τ'` **efficiently** (p.20): it distinguishes them with minimal order
among all separations distinguishing them. -/
def DistinguishesEff (u : Sym2 (Set V)) (τ τ' : Set (Set V × Set V)) : Prop :=
  Distinguishes u τ τ' ∧ ∀ u', Distinguishes u' τ τ' → usepOrder u ≤ usepOrder u'

/-- `τ` and `τ'` are **`(≤ k)`-distinguishable** (p.20): some separation of order `≤ k`
distinguishes them. -/
def LeDistinguishable (G : SimpleGraph V) (k : ℕ) (τ τ' : Set (Set V × Set V)) : Prop :=
  ∃ u, IsUSep G u ∧ usepOrder u ≤ k ∧ Distinguishes u τ τ'

/-- `τ` and `τ'` are **distinguishable** (p.20): some separation distinguishes them. -/
def IsDistinguishable (G : SimpleGraph V) (τ τ' : Set (Set V × Set V)) : Prop :=
  ∃ u, IsUSep G u ∧ Distinguishes u τ τ'

/-- The set `β(τ, τ')` of all separations efficiently distinguishing `τ` and `τ'` (Example 3.4,
p.20). -/
def effDistinguishers (G : SimpleGraph V) (τ τ' : Set (Set V × Set V)) : Set (Sym2 (Set V)) :=
  {u | IsUSep G u ∧ DistinguishesEff u τ τ'}

/-- `N` is a **tree of tangles of `G` of scope `k`** (p.23): a nested set of separations of `G`
which contains, for every pair of `(≤ k)`-distinguishable tangles, a separation that efficiently
distinguishes them. -/
def IsTreeOfTangles (G : SimpleGraph V) (k : ℕ) (N : Set (Sym2 (Set V))) : Prop :=
  (∀ u ∈ N, IsUSep G u) ∧ USepSetNested N ∧
    ∀ τ τ', IsTangleIn G τ → IsTangleIn G τ' → LeDistinguishable G k τ τ' →
      ∃ u ∈ N, DistinguishesEff u τ τ'

/-- `T` is a **tangle tree-decomposition of `G` of scope `k`** (p.23): a tree-decomposition whose
set of induced separations is a tree of tangles of scope `k`. -/
def IsTangleTreeDecomp (G : SimpleGraph V) (k : ℕ) (D : GraphDecomp.{u, w} G) : Prop :=
  IsTreeDecomp D ∧ IsTreeOfTangles G k (Set.range D.inducedSep)

end LocalSepDecomp


