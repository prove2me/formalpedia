-- Prove2me | Definitions.Def_DirKECC1549_Main_Supplement_VertexConn
-- name    : DirKECC1549_Main_Supplement_VertexConn
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T11:16:03.468126+00:00
-- url     : https://prove2.me/theorems/667d12d6-b4a1-41b6-9a3f-8cc9585bfaf5
-- title:
--   Directed k-vertex-connectivity, separators, k-blocks, k-vertex-connected components and partially vertex-split graphs
-- statement:
--   Let $G$ be a directed multigraph with vertex set $V=\{0,\dots,n-1\}$ and edge ids $0,\dots,m-1$ (the published graph model of this mission). For $X\subseteq V$, a vertex $v$ is **reachable from $u$ in $G-X$** if a directed walk from $u$ to $v$ uses only edges with both endpoints outside $X$.
--
--   1. **$k$-vertex-connectivity** (§5, p.24). Vertices $u,v$ are $k$-vertex-connected if they remain strongly connected after the deletion of any set of fewer than $k$ vertices disjoint from $\{u,v\}$:
--   $$\forall X\subseteq V\setminus\{u,v\},\ |X|<k\ \Longrightarrow\ u\to v\text{ and }v\to u\text{ in }G-X.$$
--   Every vertex is $k$-vertex-connected to itself, and a pair joined by edges in both directions is $k$-vertex-connected for every $k$.
--   2. **Separator** (§5.1, p.25). For distinct $s,t\notin X$, the set $X$ is an $(s,t)$-separator if $G-X$ has no directed path from $s$ to $t$. An **$(s,t)$-edge cut** is a set of edges whose deletion leaves no directed path from $s$ to $t$.
--   3. **$k$-block** (§6, p.28): an inclusion-maximal set $B\subseteq V$ with $|B|\ge k$ whose vertices are pairwise $k$-vertex-connected. **$k$-vertex-connected component** (p.33): a nonempty inclusion-maximal set of pairwise $k$-vertex-connected vertices, with no lower bound on its cardinality.
--   4. **Partially vertex-split graph** $G'_C$ (§5.2, p.25), for $C\subseteq V$ and a bundle size $k$: vertices of $C$ stay unsplit; every $v\notin C$ is replaced by an entry copy $v^-$ and an exit copy $v^+$ joined by the split edge $(v^-,v^+)$; with $v^-_C=v^+_C=v$ for $v\in C$, every edge $(u,v)$ of $G$ is replaced by $k$ parallel edges from $u^+_C$ to $v^-_C$.
--
--   These notions are shared by the oracle, reduction and decomposition theorems of the paper's Sections 5–6.
--
--   **Formalization Note** $G'_C$ has vertex set $\{0,\dots,2n-1\}$: vertex $v<n$ is $v$ (if $v\in C$) or $v^-$ (if $v\notin C$), vertex $n+v$ is $v^+$ (if $v\notin C$) or an unused vertex (if $v\in C$). Its $km+n$ edge ids are: $ke+j$ ($j<k$) for the bundle of edge $e$, and $km+v$ for the split edge of $v\notin C$, or a self-loop at the unused vertex $n+v$ when $v\in C$. The unused vertices and loops lie on no path between other vertices, so they change no edge-connectivity between vertices of $C$; the paper's bound "at most $2n$ vertices and $km+n$ edges" is met with equality.
-- source:
--   Loukas Georgiadis, Evangelos Kipouridis, Evangelos Kosinas, Charis Papadopoulos, Christos Pergaminelis, STOC 2027 submission #1549 (October 2026), §5 p.24 (k-vertex-connectivity), §5.1 p.25 (separators), §5.2 p.25 (partially vertex-split graphs), §6 p.28 (k-blocks), §6.4–6.5 p.33 (k-vertex-connected components)

import Mathlib
import Definitions.Def_DirKECC1549_Main_Graph

set_option autoImplicit false

noncomputable section

open Classical Finset

namespace DirKECC1549.Main.Supplement

open DirKECC1549.Main

/-!
# Vertex connectivity, separators, k-blocks, k-vertex-connected components and partially
# vertex-split graphs of a directed multigraph (§5 p.24, §5.1–5.2 pp.25–26, §6 p.28, §6.4 p.33)

Graphs are the base mission's directed multigraphs `D : Fin m → Fin n × Fin n`.
-/

variable {n m : ℕ}

/-- `v` is reachable from `u` in `D − X`: a directed walk from `u` to `v` every edge of which has
both endpoints outside `X`. (Used for `u, v ∉ X`.) -/
def ReachAvoid (D : Fin m → Fin n × Fin n) (X : Finset (Fin n)) (u v : Fin n) : Prop :=
  ∃ p, IsWalk D u p v ∧ ∀ e ∈ p, (D e).1 ∉ X ∧ (D e).2 ∉ X

/-- `k`-vertex-connectivity (§5, p.24): `u` and `v` remain strongly connected after the deletion of
any set of fewer than `k` vertices disjoint from `{u, v}`. Every vertex is `k`-vertex-connected to
itself, and a pair joined by edges in both directions is `k`-vertex-connected for every `k`. -/
def KVertexConnected (k : ℕ) (D : Fin m → Fin n × Fin n) (u v : Fin n) : Prop :=
  ∀ X : Finset (Fin n), u ∉ X → v ∉ X → X.card < k → ReachAvoid D X u v ∧ ReachAvoid D X v u

/-- An `(s, t)`-separator (§5.1, p.25): for distinct `s, t ∉ X`, `D − X` contains no directed path
from `s` to `t` (no size bound). -/
def IsSeparator (D : Fin m → Fin n × Fin n) (X : Finset (Fin n)) (s t : Fin n) : Prop :=
  s ≠ t ∧ s ∉ X ∧ t ∉ X ∧ ¬ ReachAvoid D X s t

/-- An `(s, t)`-edge cut: a set `F` of edge ids whose deletion leaves no directed walk from `s` to
`t`. -/
def IsEdgeCut (D : Fin m → Fin n × Fin n) (F : Finset (Fin m)) (s t : Fin n) : Prop :=
  ¬ ∃ p, IsWalk D s p t ∧ ∀ e ∈ p, e ∉ F

/-- The vertices of `S` are pairwise `k`-vertex-connected. -/
def PairwiseKVC (k : ℕ) (D : Fin m → Fin n × Fin n) (S : Finset (Fin n)) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, KVertexConnected k D u v

/-- A `k`-block (§6, p.28): an inclusion-maximal set `B ⊆ V` with `|B| ≥ k` whose vertices are
pairwise `k`-vertex-connected (every superset of `B` also has at least `k` elements, so maximality
is among all pairwise `k`-vertex-connected sets). -/
def IsKBlock (k : ℕ) (D : Fin m → Fin n × Fin n) (B : Finset (Fin n)) : Prop :=
  k ≤ B.card ∧ PairwiseKVC k D B ∧ ∀ B' : Finset (Fin n), B ⊆ B' → PairwiseKVC k D B' → B' = B

/-- A `k`-vertex-connected component (§6.4–6.5, p.33): a nonempty inclusion-maximal set of
pairwise `k`-vertex-connected vertices, with no lower bound on its cardinality. -/
def IsKVCC (k : ℕ) (D : Fin m → Fin n × Fin n) (K : Finset (Fin n)) : Prop :=
  K.Nonempty ∧ PairwiseKVC k D K ∧ ∀ K' : Finset (Fin n), K ⊆ K' → PairwiseKVC k D K' → K' = K

/-! ## Partially vertex-split graphs (§5.2, p.25)

The vertex set of `G′_C` is `Fin (2n)`: vertex `v < n` is `v` itself when `v ∈ C` and the entry
copy `v⁻` when `v ∉ C`; vertex `n + v` is the exit copy `v⁺` when `v ∉ C` and an unused vertex
when `v ∈ C`. The edge ids are `Fin (k·m + n)`: ids `k·e + j` (`j < k`) form the bundle of `k`
parallel copies of edge `e`, from `tail(e)⁺_C` to `head(e)⁻_C`; id `k·m + v` is the split edge
`(v⁻, v⁺)` when `v ∉ C`, and a self-loop at the unused vertex `n + v` when `v ∈ C`. -/

/-- The entry vertex `v⁻_C` (equal to `v` when `v ∈ C`). -/
def entryV (v : Fin n) : Fin (2 * n) := ⟨v, by omega⟩

/-- The exit vertex `v⁺_C`: `v` when `v ∈ C`, the copy `n + v` otherwise. -/
def exitV (C : Finset (Fin n)) (v : Fin n) : Fin (2 * n) :=
  if v ∈ C then ⟨v, by omega⟩ else ⟨n + v, by omega⟩

/-- The partially vertex-split graph `G′_C` with bundles of `k` parallel copies. -/
def splitGraph (k : ℕ) (D : Fin m → Fin n × Fin n) (C : Finset (Fin n)) :
    Fin (k * m + n) → Fin (2 * n) × Fin (2 * n) := fun i =>
  if h : (i : ℕ) < k * m then
    let e : Fin m := ⟨(i : ℕ) / k, Nat.div_lt_of_lt_mul h⟩
    (exitV C (D e).1, entryV (D e).2)
  else
    let v : Fin n := ⟨(i : ℕ) - k * m, by omega⟩
    if v ∈ C then (⟨n + v, by omega⟩, ⟨n + v, by omega⟩) else (entryV v, ⟨n + v, by omega⟩)

/-- The id of the split edge `(v⁻, v⁺)` of `v` in `G′_C`. -/
def splitEdge (k m : ℕ) (v : Fin n) : Fin (k * m + n) := ⟨k * m + v, by omega⟩

end DirKECC1549.Main.Supplement


