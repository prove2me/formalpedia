-- Prove2me | Definitions.Def_SnarlSPQR_Snarls_Multigraph
-- name    : SnarlSPQR_Snarls_Multigraph
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T03:27:03.935323+00:00
-- url     : https://prove2.me/theorems/b22dfc1d-037e-4ec8-b2d7-3baca6e64bcd
-- title:
--   Undirected multigraphs with edge identities: connectivity, cutvertices, 2-connectivity, separation pairs, multi-bridges, blocks, split pairs and split components
-- statement:
--   An **undirected multigraph** $K$ consists of a finite vertex set $V(K)$, a finite set $E(K)$ of edge identifiers and an endpoint map assigning to each edge an unordered pair $\{x,y\}$ of vertices. Parallel edges are allowed (several edges may have the same endpoints), as in §2.1 of the paper. $K$ is well formed when every endpoint of an edge is a vertex. A **subgraph** $C\subseteq K$ has the same endpoint map, $V(C)\subseteq V(K)$, $E(C)\subseteq E(K)$, and is well formed.
--
--   Two vertices are joined by an undirected walk if they are linked by a chain of edges. The **components** are the classes of this relation on $V(K)$. $K$ is **disconnected** if two of its vertices are not joined by a walk, and **connected** otherwise. For $S\subseteq V(K)$, $K-S$ deletes the vertices of $S$ and every edge meeting $S$.
--
--   - $v$ is a **cutvertex** if $K-v$ has more components than $K$. $K$ is **biconnected** if it has no cutvertex; fewer than three vertices are allowed.
--   - $K$ is **$k$-connected** if $|V(K)|>k$ and no set of fewer than $k$ vertices disconnects it.
--   - Two distinct vertices $\{u,v\}$ form a **separation pair** if $(K-u)-v$ has more components than $K$.
--   - A **multi-bridge** is a nonempty set of parallel edges whose removal increases the number of components.
--   - A **block** (2-block) is a maximal connected subgraph without cutvertices.
--   - A **split pair** is a separation pair or the endpoint pair of an edge.
--   - A **split component** of a split pair $\{u,v\}$ is either a single edge with endpoints $u,v$, or a maximal subgraph $C$ that is connected, contains $u$ and $v$, and in which $\{u,v\}$ is not a split pair.
--   - A $u$-$v$ **path** is an alternating sequence of distinct vertices and edges joining consecutive vertices. Two $u$-$v$ paths are **internally vertex-disjoint** if they are distinct and share no vertex other than $u$ and $v$.
--
--   **Formalization Note.** `MGraph V E` has fields `verts : Finset V`, `edges : Finset E` and `ends : E → Sym2 V`. Well-formedness `WF` is a predicate, so subgraphs are plain data. Maximality is with respect to the subgraph relation `IsSub`. Mathlib's `SimpleGraph` is not used because it cannot hold parallel edges, and blocks, multi-bridges, separation pairs and split components of the underlying graph $U(G)$ of a bidirected graph depend on them.
-- source:
--   Sena, Politov, Moumard, Cairo, Rizzi, Cáceres, Schmidt, Harviainen, Tomescu, Identifying bubble-like subgraphs in linear-time via a unified SPQR-tree framework, arXiv:2604.08071 (copy of 2026-11-03, sha256 40a9dca1…), pp. 4–6, §2.1 and §2.3; split pairs and split components p. 6, §2.4

import Mathlib

open Classical

namespace SnarlSPQR.Snarls

/-!
# Undirected multigraphs and their connectivity (§2.1, §2.3, pp. 4–6)

Sena, Politov, Moumard, Cairo, Rizzi, Cáceres, Schmidt, Harviainen, Tomescu, *Identifying
bubble-like subgraphs in linear-time via a unified SPQR-tree framework*, arXiv:2604.08071
(copy of 2026-11-03, sha256 40a9dca1…), §2.1 (pp. 4–5) and §2.3 (p. 6).

The paper's undirected graphs allow parallel edges ("parallel edges are allowed", p. 4), and the
underlying undirected graph `U(G)` of a bidirected graph keeps them ("edges are thus labeled with
unique identifiers", p. 5). So an undirected graph here is a **multigraph with edge identities**:
a finite vertex set `verts : Finset V`, a finite edge set `edges : Finset E` of edge identifiers,
and an endpoint map `ends : E → Sym2 V`. Only `ends` on `edges` matters. Well-formedness (every
endpoint of an edge is a vertex) is the predicate `WF`, not a field, so that subgraphs are plain
data. Mathlib's `SimpleGraph` is not used: it cannot hold two edges between the same vertices.

* `Reach K x y`: an undirected `x`-`y` walk in `K` (`x` a vertex of `K`).
* `numComp K`: the number of components (reachability classes of `verts`).
* `deleteVerts`, `deleteVert`, `deleteEdges`: `K − S`, `K − v`, `K − F`.
* `IsCutvertex`, `Biconnected` (no cutvertex, p. 5), `KConnected` (more than `k` vertices and no
  set of fewer than `k` vertices disconnects), `IsSepPair` (`(K − u) − v` has more components
  than `K`), `IsMultiBridge`, `IsBlock` (a 2-block: a maximal connected subgraph without
  cutvertices, p. 6), `IsSplitPair` and `IsSplitComponent` (p. 6), `IsPath` and internally
  vertex-disjoint paths.
-/

/-- A finite undirected multigraph with edge identities: vertices `verts`, edges `edges`, and an
endpoint map `ends` (an unordered pair of vertices per edge identifier). -/
structure MGraph (V E : Type*) where
  verts : Finset V
  edges : Finset E
  ends : E → Sym2 V

namespace MGraph

variable {V E : Type*}

/-- Well-formed: every endpoint of an edge of `K` is a vertex of `K`. -/
def WF (K : MGraph V E) : Prop := ∀ e ∈ K.edges, ∀ x ∈ K.ends e, x ∈ K.verts

/-- `C` is a subgraph of `K`: same endpoint map, fewer vertices and edges, and well-formed. -/
def IsSub (C K : MGraph V E) : Prop :=
  C.ends = K.ends ∧ C.verts ⊆ K.verts ∧ C.edges ⊆ K.edges ∧ C.WF

/-- `C` is maximal with property `P` among subgraphs: every `C'` with `P` containing `C` is
contained in `C` (so equals it). -/
def IsMaximalWith (P : MGraph V E → Prop) (C : MGraph V E) : Prop :=
  P C ∧ ∀ C', P C' → IsSub C C' → IsSub C' C

/-- The subgraph of `K` induced by an edge set `F`: edges `F`, vertices all their endpoints. -/
noncomputable def edgeSub (K : MGraph V E) (F : Finset E) : MGraph V E where
  verts := F.biUnion fun e => (K.ends e).toFinset
  edges := F
  ends := K.ends

/-- `K` has an edge with endpoints `u` and `v`. -/
def HasEdge (K : MGraph V E) (u v : V) : Prop := ∃ e ∈ K.edges, K.ends e = s(u, v)

/-- Adjacency of distinct vertices through some edge. -/
def Adj (K : MGraph V E) (x y : V) : Prop := x ≠ y ∧ K.HasEdge x y

/-- `x` is a vertex of `K` and `K` has an undirected `x`-`y` walk. -/
def Reach (K : MGraph V E) (x y : V) : Prop :=
  x ∈ K.verts ∧ Relation.ReflTransGen K.Adj x y

/-- The vertex set of the component of `K` containing `x`. -/
noncomputable def compOf (K : MGraph V E) (x : V) : Finset V := K.verts.filter fun y => K.Reach x y

/-- The number of components of `K`. -/
noncomputable def numComp (K : MGraph V E) : ℕ := (K.verts.image K.compOf).card

/-- `K` is disconnected if it has two vertices without an undirected path between them (p. 5). -/
def Disconnected (K : MGraph V E) : Prop := ∃ x ∈ K.verts, ∃ y ∈ K.verts, ¬ K.Reach x y

/-- `K` is connected: not disconnected. -/
def Connected (K : MGraph V E) : Prop := ¬ K.Disconnected

/-- `K − S`: delete the vertices of `S` and every edge with an endpoint in `S`. -/
noncomputable def deleteVerts (K : MGraph V E) (S : Finset V) : MGraph V E where
  verts := K.verts \ S
  edges := K.edges.filter fun e => ∀ x ∈ K.ends e, x ∉ S
  ends := K.ends

/-- `K − v`. -/
noncomputable def deleteVert (K : MGraph V E) (v : V) : MGraph V E := K.deleteVerts {v}

/-- `K − F`: delete the edges of `F`. -/
noncomputable def deleteEdges (K : MGraph V E) (F : Finset E) : MGraph V E where
  verts := K.verts
  edges := K.edges \ F
  ends := K.ends

/-- `v` is a cutvertex of `K`: `K − v` has more components than `K` (p. 5). -/
def IsCutvertex (K : MGraph V E) (v : V) : Prop :=
  v ∈ K.verts ∧ K.numComp < (K.deleteVert v).numComp

/-- `K` is biconnected: it has no cutvertex (p. 5; fewer than three vertices are allowed). -/
def Biconnected (K : MGraph V E) : Prop := ∀ v, ¬ K.IsCutvertex v

/-- `K` is `k`-connected: it has more than `k` vertices and no set of fewer than `k` vertices
disconnects it (p. 5). -/
def KConnected (K : MGraph V E) (k : ℕ) : Prop :=
  k < K.verts.card ∧ ∀ S : Finset V, S ⊆ K.verts → S.card < k → (K.deleteVerts S).Connected

/-- `K` is 2-connected. -/
def TwoConnected (K : MGraph V E) : Prop := K.KConnected 2

/-- `{u, v}` (two distinct vertices of `K`) is a separation pair: `(K − u) − v` has more
components than `K` (p. 5). -/
def IsSepPair (K : MGraph V E) (u v : V) : Prop :=
  u ≠ v ∧ u ∈ K.verts ∧ v ∈ K.verts ∧ K.numComp < ((K.deleteVert u).deleteVert v).numComp

/-- A multi-bridge: a nonempty set of parallel edges whose removal increases the number of
components (p. 5). -/
def IsMultiBridge (K : MGraph V E) (F : Finset E) : Prop :=
  F.Nonempty ∧ F ⊆ K.edges ∧ (∀ e ∈ F, ∀ f ∈ F, K.ends e = K.ends f) ∧
    K.numComp < (K.deleteEdges F).numComp

/-- A block (2-block) of `K`: a maximal connected subgraph without cutvertices (p. 6). -/
def IsBlock (K : MGraph V E) (B : MGraph V E) : Prop :=
  IsMaximalWith (fun C => IsSub C K ∧ C.Connected ∧ C.Biconnected) B

/-- A split pair of `K`: a separation pair or (the endpoints of) an edge of `K` (p. 6). -/
def IsSplitPair (K : MGraph V E) (u v : V) : Prop := K.IsSepPair u v ∨ K.HasEdge u v

/-- A split component of the split pair `{u, v}` (p. 6): an edge `{u, v}` (as the one-edge
subgraph), or a maximal subgraph `C` of `K` such that `{u, v}` is not a split pair of `C`, where
(as the paper's parenthesis says) `C` is connected and contains `u` and `v`. -/
def IsSplitComponent (K : MGraph V E) (u v : V) (C : MGraph V E) : Prop :=
  (∃ e ∈ K.edges, K.ends e = s(u, v) ∧ C = K.edgeSub {e}) ∨
    IsMaximalWith (fun C' => IsSub C' K ∧ u ∈ C'.verts ∧ v ∈ C'.verts ∧ C'.Connected ∧
      ¬ C'.IsSplitPair u v) C

/-- `(vs, es)` is an undirected path of `K` from `vs.head` to `vs.last`: consecutive vertices
`vs[i], vs[i+1]` are joined by the edge `es[i]` of `K`, and no vertex repeats. -/
def IsPath (K : MGraph V E) (vs : List V) (es : List E) : Prop :=
  vs.length = es.length + 1 ∧ vs.Nodup ∧ (∀ x ∈ vs, x ∈ K.verts) ∧
    ∀ i (h : i < es.length), es[i] ∈ K.edges ∧
      ∃ a b, vs[i]? = some a ∧ vs[i + 1]? = some b ∧ K.ends es[i] = s(a, b)

/-- `(vs, es)` is a `u`-`v` path of `K`. -/
def IsPathBetween (K : MGraph V E) (u v : V) (vs : List V) (es : List E) : Prop :=
  K.IsPath vs es ∧ vs.head? = some u ∧ vs.getLast? = some v

/-- `K` has two distinct, internally vertex-disjoint `u`-`v` paths. -/
def TwoDisjointPaths (K : MGraph V E) (u v : V) : Prop :=
  ∃ vs₁ es₁ vs₂ es₂, K.IsPathBetween u v vs₁ es₁ ∧ K.IsPathBetween u v vs₂ es₂ ∧
    es₁ ≠ es₂ ∧ ∀ x ∈ vs₁, x ∈ vs₂ → x = u ∨ x = v

end MGraph

end SnarlSPQR.Snarls


