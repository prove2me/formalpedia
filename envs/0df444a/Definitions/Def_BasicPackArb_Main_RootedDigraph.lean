-- Prove2me | Definitions.Def_BasicPackArb_Main_RootedDigraph
-- name    : BasicPackArb_Main_RootedDigraph
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T10:28:19.591087+00:00
-- url     : https://prove2.me/theorems/a5fb2a56-c7ba-4f29-8646-60ef5b401155
-- title:
--   §1: digraphs with roots, $\varrho_D$, arborescences, $\mathrm{Span}_M$, M-independence, M-connectedness and M-basic packings
-- statement:
--   This module fixes the objects of Theorem 1.6 of Durand de Gevigney, Nguyen and Szigeti.
--
--   **Digraphs.** A digraph $D=(V,A)$ has a finite vertex set $V$ and a finite set $A$ of arcs; every arc $a$ has a tail and a head, and $a$ is written $uv$ when its tail is $u$ and its head is $v$. Parallel arcs and loops are allowed. For a vertex set $X\subseteq V$, $\varrho_D(X)$ is the set of arcs of $A$ **entering** $X$ (tail outside $X$, head inside $X$), and
--   $$\rho_D(X)=|\varrho_D(X)|.$$
--   $D-uv$ is the digraph obtained by deleting one arc $uv$ (other parallel copies remain). A vertex $v$ is **reachable** from $u$ in the induced subgraph $D[X]$ if $u\in X$ and there is a directed path from $u$ to $v$ all of whose arcs belong to $A$ and have both ends in $X$; every vertex of $X$ is reachable from itself. The module also defines the set of vertices of $X$ from which a given vertex $v$ is reachable in $D[X]$, optionally through arcs of a prescribed kind only.
--
--   **Arborescences.** An arborescence of $D$ rooted at $r$ is a sub-digraph $T$ of $D$ (a vertex set $V(T)\subseteq V$ containing $r$ and an arc set contained in $A$ whose arcs have both ends in $V(T)$) that is a directed tree in which $r$ has in-degree $0$ and every other vertex has in-degree $1$. The single vertex $r$ with no arc is an arborescence rooted at $r$.
--
--   **Matroids.** $M$ is a matroid on the finite set $S$ with rank function $r_M$; independent sets and bases are the usual ones. For $Q\subseteq S$,
--   $$\mathrm{Span}_M(Q)=\{s\in S:\ r_M(Q\cup\{s\})=r_M(Q)\}.$$
--
--   **Digraphs with roots.** A digraph with roots is a triple $(D,S,\pi)$ with $\pi:S\to V$ a placement of the elements of $S$ at vertices ($\pi$ need not be injective). For $X\subseteq V$, $S_X=\pi^{-1}(X)$ and $S_v=\pi^{-1}(v)$.
--
--   1. $\pi$ is **$M$-independent** if $S_v$ is independent in $M$ for every $v\in V$.
--   2. $(D,S,\pi)$ is **$M$-connected** if
--   $$\rho_D(X)\ \ge\ r_M(S)-r_M(S_X)\qquad\text{for all non-empty }X\subseteq V.\tag{3}$$
--   3. An **$M$-basic packing of arborescences** in $(D,S,\pi)$ is a family $(T_s)_{s\in S}$ of pairwise arc-disjoint arborescences of $D$, $T_s$ rooted at $\pi(s)$, such that for every vertex $v\in V$ the set $\{s\in S:\ v\in V(T_s)\}$ is a base of $M$. The arborescences need not be spanning.
--
--   These are the objects in which Theorem 1.6 and every claim of its proof are stated.
--
--   **Formalization Note** The digraph is a structure with `tail`, `head : Arc → V` over an ambient arc type and a `Finset` of arcs, so $D-uv$ is `arcs.erase a`. An arborescence is a structure (vertex finset, arc finset, root) with arcs in $A$ and ends in the vertex set, no arc entering the root, exactly one arc entering each other vertex, and every vertex reachable from the root along its arcs; under the in-degree conditions the reachability clause is equivalent to the underlying graph being a tree (it also rules out loops and directed cycles). The packing is indexed by $S$, not a set of arborescences, so $|S_v|$ copies of the same single-vertex arborescence are distinct members. The rank is Mathlib's `Matroid.eRk` with values in $\mathbb{N}_{\infty}$ (finite here), $\mathrm{Span}_M$ is defined literally by the rank, and (3) is written additively, $r_M(S)\le\rho_D(X)+r_M(S_X)$, which avoids truncated subtraction. $S$ is the whole root type and theorems assume the matroid's ground set is all of it.
-- source:
--   Durand de Gevigney, Nguyen, Szigeti, Basic Packing of Arborescences, arXiv:1207.1985v1, pp. 1–3, §1 (digraph notation and arborescences p. 1; matroids, Span_M, digraphs with roots, S_X p. 2; M-independent p. 2; M-basic packing of arborescences and M-connected, (3), p. 3)

import Mathlib

namespace BasicPackArb.Main

/-- A finite digraph `D = (V, A)` with parallel arcs and loops allowed (p. 1). Arcs are drawn from an
ambient arc type `Arc`, each with a tail and a head; the digraph's arc set is the finite set
`arcs = A`. An arc `a` with `tail a = u` and `head a = v` is the arc `uv`. -/
structure Digraph (V Arc : Type*) where
  /-- The tail of an arc. -/
  tail : Arc → V
  /-- The head of an arc. -/
  head : Arc → V
  /-- The arc set `A` of the digraph. -/
  arcs : Finset Arc

namespace Digraph

variable {V Arc : Type*}

/-- `ϱ_D(X)`: the set of arcs of `D` entering the vertex set `X`, i.e. with tail outside `X` and
head inside `X` (p. 1). -/
def enteringArcs [DecidableEq V] (D : Digraph V Arc) (X : Finset V) : Finset Arc :=
  D.arcs.filter (fun a => D.tail a ∉ X ∧ D.head a ∈ X)

/-- `ρ_D(X) = |ϱ_D(X)|`, the in-degree of the vertex set `X` (p. 1). -/
def inDeg [DecidableEq V] (D : Digraph V Arc) (X : Finset V) : ℕ :=
  (D.enteringArcs X).card

/-- `D − uv`: the digraph obtained by deleting the single arc `a` from the arc set (other parallel
copies of `uv` are kept). -/
def deleteArc [DecidableEq Arc] (D : Digraph V Arc) (a : Arc) : Digraph V Arc :=
  { tail := D.tail, head := D.head, arcs := D.arcs.erase a }

/-- `v` is reachable from `u` in the induced subgraph `D[X]` using only arcs satisfying `P`: `u ∈ X`
and there is a directed path from `u` to `v` whose arcs belong to `A`, satisfy `P`, and have both
ends in `X`. Every vertex of `X` is reachable from itself (the path of length zero). -/
def ReachVia (D : Digraph V Arc) (P : Arc → Prop) (X : Finset V) (u v : V) : Prop :=
  u ∈ X ∧ Relation.ReflTransGen
    (fun x y => ∃ a ∈ D.arcs, P a ∧ D.tail a = x ∧ D.head a = y ∧ x ∈ X ∧ y ∈ X) u v

/-- The set of vertices `y` of `X` from which `v` is reachable in `D[X]` using only arcs
satisfying `P`. -/
noncomputable def reachSetVia (D : Digraph V Arc) (P : Arc → Prop) (X : Finset V) (v : V) :
    Finset V := by
  classical
  exact X.filter (fun y => D.ReachVia P X y v)

/-- The set of vertices `y` of `X` from which `v` is reachable in `D[X]` (p. 1: `v` is reachable
from `y` if there is a directed path from `y` to `v`), all arcs of `D[X]` allowed. -/
noncomputable def reachSet (D : Digraph V Arc) (X : Finset V) (v : V) : Finset V :=
  D.reachSetVia (fun _ => True) X v

end Digraph

/-- An arborescence of the digraph `D` rooted at `root` (p. 1): a sub-digraph of `D` with vertex
set `verts` and arc set `arcs ⊆ A` (both ends of every arc in `verts`), in which the root has
in-degree `0`, every other vertex has in-degree exactly `1`, and every vertex is reachable from the
root along arcs of `arcs`. Under the in-degree conditions, the reachability condition is
equivalent to the underlying graph being a tree. The single vertex `root` with no arc is an
arborescence. -/
structure Arborescence {V Arc : Type*} (D : Digraph V Arc) where
  /-- The vertex set `V(T)`. -/
  verts : Finset V
  /-- The arc set of `T`. -/
  arcs : Finset Arc
  /-- The root of `T`. -/
  root : V
  arcs_subset : arcs ⊆ D.arcs
  tail_mem : ∀ a ∈ arcs, D.tail a ∈ verts
  head_mem : ∀ a ∈ arcs, D.head a ∈ verts
  root_mem : root ∈ verts
  /-- The root has in-degree `0` in `T`. -/
  root_inDeg : ∀ a ∈ arcs, D.head a ≠ root
  /-- Every other vertex of `T` has in-degree exactly `1` in `T`. -/
  inDeg_one : ∀ v ∈ verts, v ≠ root → ∃! a, a ∈ arcs ∧ D.head a = v
  /-- Every vertex of `T` is reachable from the root inside `T`. -/
  reach : ∀ v ∈ verts,
    Relation.ReflTransGen (fun x y => ∃ a ∈ arcs, D.tail a = x ∧ D.head a = y) root v

/-- The arborescence consisting of the single vertex `r` and no arcs (p. 1). -/
def Arborescence.single {V Arc : Type*} (D : Digraph V Arc) (r : V) : Arborescence D where
  verts := {r}
  arcs := ∅
  root := r
  arcs_subset := Finset.empty_subset _
  tail_mem := by simp
  head_mem := by simp
  root_mem := Finset.mem_singleton_self r
  root_inDeg := by simp
  inDeg_one := by simp
  reach := by
    intro v hv
    rw [Finset.mem_singleton] at hv
    subst hv
    exact Relation.ReflTransGen.refl

/-- `Span_M(Q) = {s ∈ S : r_M(Q ∪ {s}) = r_M(Q)}` (p. 2), with `r_M = M.eRk`. -/
def Span {S : Type*} (M : Matroid S) (Q : Set S) : Set S :=
  {s | M.eRk (insert s Q) = M.eRk Q}

/-- `π` is `M`-independent (p. 2): `S_v = π⁻¹(v)` is independent in `M` for every vertex `v`. -/
def MIndependent {S V : Type*} (π : S → V) (M : Matroid S) : Prop :=
  ∀ v : V, M.Indep (π ⁻¹' {v})

/-- `(D, S, π)` is `M`-connected (p. 3, (3)): `ρ_D(X) ≥ r_M(S) − r_M(S_X)` for every non-empty
vertex set `X`, written additively as `r_M(S) ≤ ρ_D(X) + r_M(S_X)` in `ℕ∞`, where
`S_X = π⁻¹(X)` and `S` is the whole root type. -/
def MConnected {V Arc S : Type*} [DecidableEq V] (D : Digraph V Arc) (π : S → V)
    (M : Matroid S) : Prop :=
  ∀ X : Finset V, X.Nonempty →
    M.eRk Set.univ ≤ (D.inDeg X : ℕ∞) + M.eRk (π ⁻¹' (X : Set V))

/-- `T : S → Arborescence D` is an `M`-basic packing of arborescences in `(D, S, π)` (p. 3): one
arborescence `T s` for every root element `s`, rooted at `π s`, pairwise arc-disjoint, and such
that for every vertex `v` the set `{s ∈ S : v ∈ V(T s)}` is a base of `M`. -/
def IsBasicPacking {V Arc S : Type*} (D : Digraph V Arc) (π : S → V) (M : Matroid S)
    (T : S → Arborescence D) : Prop :=
  (∀ s, (T s).root = π s) ∧
  (∀ s s', s ≠ s' → Disjoint (T s).arcs (T s').arcs) ∧
  (∀ v : V, M.IsBase {s | v ∈ (T s).verts})

end BasicPackArb.Main


