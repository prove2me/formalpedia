-- Prove2me | Definitions.Def_DirKECC1549_Main_Graph
-- name    : DirKECC1549_Main_Graph
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T06:40:01.468498+00:00
-- url     : https://prove2.me/theorems/483ed665-3b6e-4e06-8b7b-2de7adb25a86
-- title:
--   §2 and Definition 1 — multidigraphs, out-sets, volumes, edge-disjoint paths, λ, k-edge-connectivity, (k,Δ)-connectivity
-- statement:
--   A directed multigraph $D$ with $n$ vertices and $m$ edges is given by an edge map $D:\{0,\dots,m-1\}\to V\times V$, $V=\{0,\dots,n-1\}$; edge $e$ goes from its tail $(D e)_1$ to its head $(D e)_2$. Distinct edge ids may join the same pair, so every count below includes multiplicities; self-loops are allowed. The reverse graph $D^R$ reverses every edge.
--
--   For $S\subseteq V$:
--
--   1. $\mathrm{out}_D(S)$ is the number of edges with tail in $S$ and head outside $S$;
--   2. $\deg^+_D(v)$ is the number of edges with tail $v$, and the out-volume is $\mathrm{vol}_D(S)=\sum_{v\in S}\deg^+_D(v)$;
--   3. a $(<k)$-out set (resp. $(\le k)$-out set) satisfies $\emptyset\ne S\subsetneq V$ and $\mathrm{out}_D(S)<k$ (resp. $\le k$);
--   4. $S$ is a $(u,v)$-cut when $u\in S$ and $v\notin S$.
--
--   A directed $u\to v$ path is a list of edge ids forming a walk from $u$ to $v$ that uses no edge id twice. $\lambda_D(u,v)$ is the maximum number of pairwise edge-disjoint directed $u\to v$ paths (disjoint as sets of edge ids), used for $u\ne v$. A $(u,v)$-mincut is a $(u,v)$-cut $S$ with $\mathrm{out}_D(S)=\lambda_D(u,v)$; the inclusion-wise minimum $(u,v)$-mincut is contained in every $(u,v)$-mincut.
--
--   Vertices $u,v$ are $k$-edge-connected,
--   $$u\leftrightarrow^D_k v\iff u=v\ \text{ or }\ \big(\lambda_D(u,v)\ge k\ \text{and}\ \lambda_D(v,u)\ge k\big),$$
--   where "$\lambda_D(u,v)\ge k$" means that $k$ pairwise edge-disjoint $u\to v$ paths exist. Reachability is the existence of a directed walk; $u,v$ are strongly connected when each reaches the other, and $D$ is strongly connected when every pair is. The strongly connected component of $u$ is the set of vertices strongly connected to $u$. The induced subgraph $D[S]$ keeps exactly the edges with both ends in $S$ (with multiplicity); its vertices are renamed $0,\dots,|S|-1$ in increasing order, and a relation on $D[S]$ is transported back to $D$ through this renaming.
--
--   Finally (Definition 1), $u$ and $v$ are $(k,\Delta)$-connected in $G$ if there is no $(<k)$-out set $S$ with $\mathrm{vol}_D(S)\le\Delta$, for any $D\in\{G,G^R\}$, that contains $u$ and not $v$, or vice versa.
--
--   These are the objects of Section 2 and Definition 1 on which every statement of the mission is built.
--
--   **Formalization Note** The number $\lambda_D(u,v)$ is the supremum of the attainable path counts; for $u\ne v$ this set contains $0$ and is bounded by $m$, so it is a maximum. At $u=v$ the supremum is a junk value $0$, which no statement uses: $k$-edge-connectivity is defined directly by the existence of $k$ disjoint paths.
-- source:
--   Loukas Georgiadis, Evangelos Kipouridis, Evangelos Kosinas, Charis Papadopoulos, Christos Pergaminelis, STOC 2027 submission #1549 (October 2026), Section 2, p.9; Section 3.1, Definition 1, p.11; Section 3.3, Algorithm 3 line 4 and Claim 1, p.17

import Mathlib

set_option autoImplicit false

noncomputable section

open Classical Finset

namespace DirKECC1549.Main

/-!
# Directed multigraphs, cuts, edge-disjoint paths and k-edge-connectivity (§2, p.9; Def. 1, p.11)

A directed multigraph with `n` vertices and `m` edges is an edge map `D : Fin m → Fin n × Fin n`;
edge `e` goes from its tail `(D e).1` to its head `(D e).2`. Edge identities carry multiplicity:
parallel edges are distinct ids. Self-loops are allowed (a loop leaves no vertex set).
-/

variable {n m : ℕ}

/-- The reverse graph `Dᴿ`: every edge reversed, same edge ids. -/
def Rev (D : Fin m → Fin n × Fin n) : Fin m → Fin n × Fin n := fun e => ((D e).2, (D e).1)

/-- The edges leaving `S`: tail in `S`, head outside `S`. -/
def outEdges (D : Fin m → Fin n × Fin n) (S : Finset (Fin n)) : Finset (Fin m) :=
  univ.filter (fun e => (D e).1 ∈ S ∧ (D e).2 ∉ S)

/-- `out_D(S)`, the number of edges leaving `S`, counted with multiplicity. -/
def outCount (D : Fin m → Fin n × Fin n) (S : Finset (Fin n)) : ℕ := (outEdges D S).card

/-- The out-degree `deg⁺_D(v)`, counted with multiplicity (a loop at `v` counts). -/
def outDeg (D : Fin m → Fin n × Fin n) (v : Fin n) : ℕ := (univ.filter (fun e => (D e).1 = v)).card

/-- The out-volume `vol_D(S) = ∑_{v ∈ S} deg⁺_D(v)`. -/
def vol (D : Fin m → Fin n × Fin n) (S : Finset (Fin n)) : ℕ := ∑ v ∈ S, outDeg D v

/-- A `(< k)`-out set: `∅ ≠ S ⊊ V(D)` and `out_D(S) < k`. -/
def IsLtOut (D : Fin m → Fin n × Fin n) (k : ℕ) (S : Finset (Fin n)) : Prop :=
  S.Nonempty ∧ S ≠ univ ∧ outCount D S < k

/-- A `(≤ k)`-out set: `∅ ≠ S ⊊ V(D)` and `out_D(S) ≤ k`. -/
def IsLeOut (D : Fin m → Fin n × Fin n) (k : ℕ) (S : Finset (Fin n)) : Prop :=
  S.Nonempty ∧ S ≠ univ ∧ outCount D S ≤ k

/-- `S` is a `(u, v)`-cut: `u ∈ S` and `v ∉ S`. -/
def IsCut (S : Finset (Fin n)) (u v : Fin n) : Prop := u ∈ S ∧ v ∉ S

/-- `IsWalk D u p v`: the list of edge ids `p` is a directed walk from `u` to `v` in `D`. -/
inductive IsWalk (D : Fin m → Fin n × Fin n) : Fin n → List (Fin m) → Fin n → Prop
  | nil (u : Fin n) : IsWalk D u [] u
  | cons {u v : Fin n} (e : Fin m) (p : List (Fin m)) :
      (D e).1 = u → IsWalk D (D e).2 p v → IsWalk D u (e :: p) v

/-- A directed `u → v` path, taken as a trail: a walk that uses no edge id twice. -/
def IsTrail (D : Fin m → Fin n × Fin n) (u : Fin n) (p : List (Fin m)) (v : Fin n) : Prop :=
  IsWalk D u p v ∧ p.Nodup

/-- There are `k` pairwise edge-disjoint directed `u → v` paths (disjoint as sets of edge ids). -/
def HasDisjointPaths (D : Fin m → Fin n × Fin n) (k : ℕ) (u v : Fin n) : Prop :=
  ∃ P : Fin k → List (Fin m), (∀ i, IsTrail D u (P i) v) ∧
    ∀ i j, i ≠ j → Disjoint (P i).toFinset (P j).toFinset

/-- `λ_D(u, v)`, the maximum number of pairwise edge-disjoint directed `u → v` paths. For
`u ≠ v` the set of attainable counts contains `0` and is bounded by `m`, so this is a maximum;
it is used only for distinct `u, v` (at `u = v` the set is unbounded and `sSup` returns `0`). -/
def lam (D : Fin m → Fin n × Fin n) (u v : Fin n) : ℕ := sSup {k | HasDisjointPaths D k u v}

/-- A `(u, v)`-mincut: a `(u, v)`-cut `S` with `out_D(S) = λ_D(u, v)`. -/
def IsMinCut (D : Fin m → Fin n × Fin n) (u v : Fin n) (S : Finset (Fin n)) : Prop :=
  IsCut S u v ∧ outCount D S = lam D u v

/-- `S` is the inclusion-wise minimum `(u, v)`-mincut. -/
def IsMinimumMinCut (D : Fin m → Fin n × Fin n) (u v : Fin n) (S : Finset (Fin n)) : Prop :=
  IsMinCut D u v S ∧ ∀ T, IsMinCut D u v T → S ⊆ T

/-- `u ↔_k v` in `D`: `u = v`, or there are `k` edge-disjoint `u → v` paths and `k` edge-disjoint
`v → u` paths (i.e. `λ_D(u,v) ≥ k` and `λ_D(v,u) ≥ k`). -/
def KEdgeConnected (k : ℕ) (D : Fin m → Fin n × Fin n) (u v : Fin n) : Prop :=
  u = v ∨ (HasDisjointPaths D k u v ∧ HasDisjointPaths D k v u)

/-- `v` is reachable from `u` by a directed walk. -/
def Reach (D : Fin m → Fin n × Fin n) (u v : Fin n) : Prop := ∃ p, IsWalk D u p v

/-- `u` and `v` are strongly connected (mutually reachable). -/
def StronglyConn (D : Fin m → Fin n × Fin n) (u v : Fin n) : Prop := Reach D u v ∧ Reach D v u

/-- The whole graph is strongly connected. -/
def IsStronglyConnected (D : Fin m → Fin n × Fin n) : Prop := ∀ u v, StronglyConn D u v

/-- The strongly connected component of `u`. -/
def sccOf (D : Fin m → Fin n × Fin n) (u : Fin n) : Finset (Fin n) :=
  univ.filter (fun v => StronglyConn D u v)

/-- The edges of the induced subgraph `D[S]`: both ends in `S`. -/
def inducedEdges (D : Fin m → Fin n × Fin n) (S : Finset (Fin n)) : Finset (Fin m) :=
  univ.filter (fun e => (D e).1 ∈ S ∧ (D e).2 ∈ S)

/-- The `i`-th vertex of `S` in increasing order: the vertex renaming `Fin |S| → S`. -/
def vertexOf (S : Finset (Fin n)) (i : Fin S.card) : Fin n := (S.orderIsoOfFin rfl i).1

/-- The position of a vertex `u ∈ S` in increasing order: the renaming `S → Fin |S|`. -/
def posIn (S : Finset (Fin n)) (u : Fin n) (hu : u ∈ S) : Fin S.card :=
  (S.orderIsoOfFin rfl).symm ⟨u, hu⟩

/-- The induced subgraph `D[S]`, with vertices `Fin |S|` (the elements of `S` in increasing order)
and edges `Fin |inducedEdges D S|` (the edges with both ends in `S`, in increasing id order),
keeping every such edge with its multiplicity. -/
def induced (D : Fin m → Fin n × Fin n) (S : Finset (Fin n)) :
    Fin (inducedEdges D S).card → Fin S.card × Fin S.card := fun i =>
  let e := (inducedEdges D S).orderIsoOfFin rfl i
  have he : (D e.1).1 ∈ S ∧ (D e.1).2 ∈ S := (Finset.mem_filter.1 e.2).2
  (posIn S (D e.1).1 he.1, posIn S (D e.1).2 he.2)

/-- Transport a relation on the vertices `Fin |S|` of `D[S]` back to vertices of `D`:
`u, v` are related iff both lie in `S` and their renamed copies are related. -/
def liftRel (S : Finset (Fin n)) (R : Fin S.card → Fin S.card → Prop) (u v : Fin n) : Prop :=
  ∃ (hu : u ∈ S) (hv : v ∈ S), R (posIn S u hu) (posIn S v hv)

/-- `(k, Δ)`-connectivity (Definition 1, p.11): there is no `(< k)`-out set `S` with
`vol_D(S) ≤ Δ`, for any `D ∈ {G, Gᴿ}`, that contains `u` and not `v`, or vice versa. -/
def KDeltaConnected (k Δ : ℕ) (G : Fin m → Fin n × Fin n) (u v : Fin n) : Prop :=
  ∀ D ∈ ({G, Rev G} : Set (Fin m → Fin n × Fin n)), ∀ S : Finset (Fin n),
    IsLtOut D k S → vol D S ≤ Δ → ¬ ((u ∈ S ∧ v ∉ S) ∨ (v ∈ S ∧ u ∉ S))

end DirKECC1549.Main


