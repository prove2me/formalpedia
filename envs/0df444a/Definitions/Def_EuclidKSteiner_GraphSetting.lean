-- Prove2me | Definitions.Def_EuclidKSteiner_GraphSetting
-- name    : EuclidKSteiner_GraphSetting
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:15:44.904149+00:00
-- url     : https://prove2.me/theorems/c1543144-394b-49b0-b45c-5c32bb51fbdd
-- title:
--   The graph setting of §§3–4: Steiner and backbone edges, attachment forests, completions, $C_F$ and augmented trees
-- statement:
--   The **graph setting** consists of a finite graph $G=(V,E)$ without loops, edge weights $w\ge0$, a terminal set $P$ with $|P|\ge2$, candidates $Q=V\setminus P$, and a fixed minimum spanning tree $M$ of $G[P]$ (its existence means $G[P]$ is connected). Let $\ell$ and $\Phi$ be the bottleneck length and attachment value of $M$.
--
--   1. A **Steiner edge** is an edge of $G$ with an endpoint in $Q$; a **backbone edge** is an edge of $G$ with both endpoints in $P$; a **virtual edge** is a pair of distinct terminals weighted by $\ell$, which need not be an edge of $G$.
--   2. An **attachment forest** is a forest $F$ of Steiner edges in which every component contains a terminal. Its vertex set is $V(F)$, its **attachment set** is $A=V(F)\cap P$, and its components are $F_1,\dots,F_{\mathrm{cc}(F)}$ with $A_i=V(F_i)\cap P$.
--   3. A **completion** of $F$ is a tree of $G$ spanning $P\cup(V(F)\cap Q)$ that contains $F$ and whose other edges are backbone edges; $\mathrm{opt}(F)$ is the minimum weight of a completion.
--   4. The **component graph** $C_F$ is the complete graph on the components with edge weight $\min_{u\in A_i,v\in A_j}\ell(u,v)$ on $ij$.
--   5. An **augmented tree** with terminal set $\emptyset\ne A\subseteq P$ and candidate set $\emptyset\ne S\subseteq Q$ is a tree on $A\cup S$ whose edges are Steiner edges of $G$ and virtual edges between terminals of $A$, such that every terminal of $A$ has a neighbor in $S$. Its weight $w(T)$ charges $w$ to Steiner edges and $\ell$ to virtual edges, and its Steiner edges form its attachment forest.
--
--   **Formalization Note** Edge sets are finite sets of unordered pairs. A minimum-weight completion is expressed by the predicate `IsOptCompletion`, so no statement depends on a default value of an empty minimum.
-- source:
--   Bhore, Kisfaludi-Bak, Marx, Odak, Parameterized Tractability of Euclidean k-Steiner Tree, STOC 2027 submission (manuscript sha256 75361687…), §3 p.8 (PDF p.10), §3.2 pp.9–11 (PDF pp.11–13), §4.1 pp.14–15 (PDF pp.16–17); Theorem 1.2 p.3 (PDF p.5); proof of Theorem 1.1 p.19 (PDF p.21)

import Mathlib
import Definitions.Def_EuclidKSteiner_SpanningTree
import Definitions.Def_EuclidKSteiner_TermTree

namespace EuclidKSteiner

open Classical

/-!
# The graph setting of §§3–4: terminals, candidates, Steiner and backbone edges, attachment forests,
completions, the component graph `C_F` and augmented trees

Bhore, Kisfaludi-Bak, Marx, Odak, *Parameterized Tractability of Euclidean k-Steiner Tree*,
STOC 2027 submission (manuscript sha256 75361687…), §3 pp.8–11 (PDF pp.10–13), §4.1 pp.14–15
(PDF pp.16–17), Theorem 1.2 p.3 (PDF p.5), proof of Theorem 1.1 p.19 (PDF p.21).

**Formalization Note**
* A `GraphSetting V` is a graph `G` on the finite vertex type `V` (an edge set `E` of unordered
  pairs, no loops) with weights `w`, nonnegative on edges, a terminal set `P`, candidates `Q = V \ P`
  (§1, Theorem 1.2: "a candidate set Q = V(G) \ P"), and a fixed minimum spanning tree `M` of `G[P]`
  (§3, p.8: "Fix a minimum spanning tree M of G[P]"). That `M` exists encodes "G[P] connected". The
  standing assumption `|P| ≥ 2` of §3 (p.8) is a field.
* A **Steiner edge** is an edge of `G` with an endpoint outside `P`; a **backbone edge** is an edge
  of `G` with both endpoints in `P` (§2.1 and §3, p.8). A **virtual edge** is an auxiliary pair of
  distinct terminals weighted by `ℓ`, possibly not an edge of `G` (§4.1, p.14).
* Edge sets are `Finset (Sym2 V)`; `V(F)` is the set of endpoints of edges of `F`. The components of
  a forest `F` are the vertex sets of the connected components of `(V(F), F)`.
* Optimal completions are stated through `IsOptCompletion` (a completion of least weight), never
  through an unguarded minimum.
-/

/-- The edges of `E` with both endpoints in `P`: the edge set of `G[P]`. -/
noncomputable def backboneOf {V : Type*} (E : Finset (Sym2 V)) (P : Finset V) : Finset (Sym2 V) :=
  E.filter (fun e => ∀ v ∈ e, v ∈ P)

/-- **The graph setting of §§3–4.** A graph `G = (V, E)` with nonnegative edge weights `w`, terminal
set `P` with `|P| ≥ 2`, candidates `Q = V \ P`, and a fixed minimum spanning tree `M` of `G[P]`.
Source: Bhore, Kisfaludi-Bak, Marx, Odak, STOC 2027 submission (manuscript sha256 75361687…), §3,
p.8 (PDF p.10): "Fix a minimum spanning tree M of G[P]. … We handle P = ∅, |P| = 1, and k = 0
directly, and hence assume |P| ≥ 2 and k ≥ 1"; proof of Theorem 1.1, p.19 (PDF p.21): "For a graph G
with nonnegative edge weights and connected G[P]".

**Formalization Note** The budget `k ≥ 1` of the same sentence is kept in the statements that
mention `k`, not here. -/
structure GraphSetting (V : Type*) [Fintype V] [DecidableEq V] where
  /-- Terminals. -/
  P : Finset V
  /-- Edges of `G`. -/
  E : Finset (Sym2 V)
  /-- Edge weights. -/
  w : Sym2 V → ℝ
  /-- The fixed minimum spanning tree of `G[P]`. -/
  M : Finset (Sym2 V)
  /-- `G` has no loops. -/
  E_nondiag : ∀ e ∈ E, ¬ e.IsDiag
  /-- Nonnegative edge weights. -/
  w_nonneg : ∀ e ∈ E, 0 ≤ w e
  /-- At least two terminals. -/
  two_le_card : 2 ≤ P.card
  /-- `M` is a minimum spanning tree of `G[P]`. -/
  M_mst : IsMST P id (backboneOf E P) w M

namespace GraphSetting

variable {V : Type*} [Fintype V] [DecidableEq V] (S : GraphSetting V)

/-- The fixed terminal tree `M` as a weighted tree on `P`. -/
def toTermTree : TermTree V where
  P := S.P
  M := S.M
  w := S.w
  isTree := ⟨subset_refl _, S.M_mst.1.2.1, S.M_mst.1.2.2.1, S.M_mst.1.2.2.2⟩
  w_nonneg := fun e he => by
    have h := S.M_mst.1.1 he
    simp only [backboneOf, Finset.mem_filter] at h
    exact S.w_nonneg e h.1

/-- The bottleneck length `ℓ(u, v)` in the fixed tree `M`. -/
noncomputable def ell (u v : V) : ℝ := S.toTermTree.ell u v

/-- The attachment value `Φ(A) = w(MST(A, ℓ))` with respect to `M`. -/
noncomputable def Phi (A : Finset V) : ℝ := S.toTermTree.Phi A

/-- A **Steiner edge**: an edge of `G` with an endpoint outside `P` (touching a candidate). -/
def IsSteinerEdge (e : Sym2 V) : Prop := e ∈ S.E ∧ ∃ v ∈ e, v ∉ S.P

/-- A **backbone edge**: an edge of `G` with both endpoints in `P`. -/
def IsBackboneEdge (e : Sym2 V) : Prop := e ∈ S.E ∧ ∀ v ∈ e, v ∈ S.P

/-- `V(F)`: the endpoints of the edges of `F`. -/
noncomputable def verts (F : Finset (Sym2 V)) : Finset V :=
  Finset.univ.filter (fun v => ∃ e ∈ F, v ∈ e)

/-- An **attachment forest** (with a terminal in each component): a set of Steiner edges forming a
forest in which every vertex is joined by edges of `F` to a terminal.
Source: Bhore, Kisfaludi-Bak, Marx, Odak, Lemma 3.1 and §3.2, p.9 (PDF p.11): "Let F be a forest of
Steiner edges with a terminal in each component"; "For a nonempty attachment forest F, each
component contains at least one terminal from P". -/
def IsAttachmentForest (F : Finset (Sym2 V)) : Prop :=
  (∀ e ∈ F, S.IsSteinerEdge e) ∧ (SimpleGraph.fromEdgeSet (F : Set (Sym2 V))).IsAcyclic ∧
    ∀ v ∈ verts F, ∃ p ∈ S.P, (SimpleGraph.fromEdgeSet (F : Set (Sym2 V))).Reachable v p

/-- The **attachment set** `A = V(F) ∩ P`. Source: §3.2, p.9 (PDF p.11). -/
noncomputable def attachSet (F : Finset (Sym2 V)) : Finset V := verts F ∩ S.P

/-- The **Steiner components** `F_1, …, F_cc(F)` of `F`, as their vertex sets. -/
noncomputable def comps (F : Finset (Sym2 V)) : Finset (Finset V) :=
  (verts F).image fun v =>
    (verts F).filter fun u => (SimpleGraph.fromEdgeSet (F : Set (Sym2 V))).Reachable u v

/-- `cc(F)`, the number of Steiner components. -/
noncomputable def ccF (F : Finset (Sym2 V)) : ℕ := (comps F).card

/-- A **completion** of `F`: a tree in `G` spanning `P ∪ (V(F) ∩ Q)` that contains `F` and whose other
edges are backbone edges. Source: §3.2, p.9 (PDF p.11). -/
def IsCompletion (F T : Finset (Sym2 V)) : Prop :=
  IsSpanningTree (S.P ∪ verts F) id S.E T ∧ F ⊆ T ∧ ∀ e ∈ T, e ∉ F → S.IsBackboneEdge e

/-- `T` is a **minimum-weight completion** of `F`; its weight is `opt(F)`.
Source: §3.2, p.9 (PDF p.11): "Let opt(F) denote the minimum weight of a completion." -/
def IsOptCompletion (F T : Finset (Sym2 V)) : Prop :=
  S.IsCompletion F T ∧ ∀ T', S.IsCompletion F T' → edgeSum S.w T ≤ edgeSum S.w T'

/-- `min_{u ∈ C ∩ P, v ∈ C' ∩ P} ℓ(u, v)` (`0` if either side has no terminal). -/
noncomputable def compDist (C C' : Finset V) : ℝ :=
  if h : ((C ∩ S.P) ×ˢ (C' ∩ S.P)).Nonempty then
    ((C ∩ S.P) ×ˢ (C' ∩ S.P)).inf' h (fun x => S.ell x.1 x.2)
  else 0

/-- The edge weight of the **component graph** `C_F` on the pair `{F_i, F_j}`:
`min_{u ∈ A_i, v ∈ A_j} ℓ(u, v)`. Since `ℓ` is symmetric the two orders agree; the `min` makes
the symmetry hold by definition. Source: §3.2, p.11 (PDF p.13). -/
noncomputable def compWeight : Sym2 (Finset V) → ℝ :=
  Sym2.lift ⟨fun C C' => min (S.compDist C C') (S.compDist C' C),
    fun C C' => by simp [min_comm]⟩

/-- `w(MST(C_F))`: the minimum spanning tree weight of the complete graph on the Steiner components
of `F` with edge weights `compWeight`. Source: §3.2, Lemma 3.5, p.11 (PDF p.13). -/
noncomputable def mstCF (F : Finset (Sym2 V)) : ℝ :=
  mstWeightOn (comps F) id (completeEdges (comps F)) S.compWeight

/-- The edges an augmented tree on `A ∪ C` may use: Steiner edges of `G` inside `A ∪ C`, and
virtual edges, i.e. pairs of distinct terminals of `A`. -/
noncomputable def augEdges (A C : Finset V) : Finset (Sym2 V) :=
  (S.E.filter (fun e => (∃ v ∈ e, v ∉ S.P) ∧ ∀ v ∈ e, v ∈ A ∪ C)) ∪ completeEdges A

/-- An **augmented tree** with terminal set `A` and candidate set `C`: `∅ ≠ A ⊆ P`, `∅ ≠ C ⊆ Q`,
`T` a tree on `A ∪ C` whose edges are Steiner edges and virtual edges between terminals of `A`,
and every terminal of `A` has a neighbor in `C`.
Source: Bhore, Kisfaludi-Bak, Marx, Odak, §4.1, p.15 (PDF p.17). -/
def IsAugTree (A C : Finset V) (T : Finset (Sym2 V)) : Prop :=
  A ⊆ S.P ∧ A.Nonempty ∧ Disjoint C S.P ∧ C.Nonempty ∧
    IsSpanningTree (A ∪ C) id (S.augEdges A C) T ∧
    ∀ a ∈ A, ∃ c ∈ C, s(a, c) ∈ T

/-- The weight `w(T)` of an augmented tree: original weights on Steiner edges, `ℓ` on virtual
edges (pairs of terminals). Source: §4.1, p.15 (PDF p.17). -/
noncomputable def augWeight (T : Finset (Sym2 V)) : ℝ :=
  ∑ e ∈ T, if (∀ v ∈ e, v ∈ S.P) then S.toTermTree.ellSym e else S.w e

/-- The attachment forest of an augmented tree: its Steiner edges (the virtual edges deleted).
Source: §4.1, p.15 (PDF p.17): "Deleting the virtual edges leaves an attachment forest F with
attachment set A." -/
noncomputable def augForest (T : Finset (Sym2 V)) : Finset (Sym2 V) :=
  T.filter (fun e => ∃ v ∈ e, v ∉ S.P)

end GraphSetting

end EuclidKSteiner


