-- Prove2me | Definitions.Def_AcycTesting_NearLinear_Digraphs
-- name    : AcycTesting_NearLinear_Digraphs
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T00:34:15.403217+00:00
-- url     : https://prove2.me/theorems/0c515c58-37a1-4015-9803-3affca81eef4
-- title:
--   Simple digraphs on [n] with in- and outdegree at most d; acyclicity, fas, ε-farness and the complete blow-up
-- statement:
--   A directed graph without parallel edges on a finite vertex set $V$ is given by the set $N^+(u)\subseteq V$ of outneighbours of each vertex $u$ (so there is at most one edge $u\to v$ for each ordered pair; the antiparallel pair $u\to v$, $v\to u$ is allowed). It is *simple* when, in addition, it has no self-loop: $u\notin N^+(u)$ for all $u$. The outdegree of $u$ is $|N^+(u)|$ and its indegree is $|\{w : u\in N^+(w)\}|$.
--
--   The input class $\mathcal G(n,d)$ consists of the simple directed graphs on the vertex set $[n]$ (here $\{0,\dots,n-1\}$; a vertex is its own ID) in which every outdegree and every indegree is at most $d$.
--
--   A graph is *acyclic* if no vertex reaches itself by a directed path of positive length. For a set $F$ of ordered pairs, $G-F$ deletes the edges in $F$. The minimum feedback arc set size is
--   $$\mathrm{fas}(G)=\min\{|F| : G-F \text{ is acyclic}\},$$
--   the minimum number of edges whose deletion makes $G$ acyclic. For $\varepsilon\in\mathbb R$ and a degree bound $d$, $G$ on $n$ vertices is *$\varepsilon$-far from acyclic* if $\mathrm{fas}(G)\ge \varepsilon d n$.
--
--   The *complete blow-up* $G^{(t)}$ of $G$ has vertex set $V\times[t]$ (copies indexed $0,\dots,t-1$) and an edge $(u,i)\to(v,j)$ exactly when $u\to v$ in $G$; that is, $N^+_{G^{(t)}}((u,i)) = N^+_G(u)\times[t]$.
--
--   **Formalization Note.** `OutGraph V := V → Finset V`; `InClass n d G` is $G\in\mathcal G(n,d)$ on `Fin n`; `fas` is an `sInf` over a nonempty set of naturals (deleting every pair always works), so it is the true minimum.
-- source:
--   Czumaj, Peng, Wang, Near-Linear Lower Bounds for Testing Directed Acyclicity, arXiv:2611.04901v1 (sha256 5685fc7b…), pp. 1, 13–14 (PDF 4, 16–17), §1 and §3.1; p. 23 (PDF 26), Lemma 5.10 (the blow-up)

import Mathlib

namespace AcycTesting.NearLinear

/-- A directed graph without parallel edges on a vertex type `V`, given by the set of
outneighbours of each vertex (`v ∈ G u` iff `u → v`). Antiparallel pairs `u → v`, `v → u`
are allowed; loops are excluded separately by `IsLoopless`. -/
abbrev OutGraph (V : Type*) := V → Finset V

variable {V : Type*}

/-- The edge relation `u → v`. -/
def Adj (G : OutGraph V) (u v : V) : Prop := v ∈ G u

/-- No self-loops; together with the representation (at most one edge per ordered pair) this
is "simple". -/
def IsLoopless (G : OutGraph V) : Prop := ∀ u, u ∉ G u

/-- Outdegree of `u`. -/
def outdeg (G : OutGraph V) (u : V) : ℕ := (G u).card

/-- Indegree of `v`. -/
def indeg [Fintype V] [DecidableEq V] (G : OutGraph V) (v : V) : ℕ :=
  (Finset.univ.filter (fun u => v ∈ G u)).card

/-- The input class `𝒢(n, d)`: simple directed graphs on `[n]` (here `Fin n`) with every
outdegree and every indegree at most `d`. -/
def InClass (n d : ℕ) (G : OutGraph (Fin n)) : Prop :=
  IsLoopless G ∧ ∀ u, outdeg G u ≤ d ∧ indeg G u ≤ d

/-- Acyclic: no vertex reaches itself by a directed path of positive length. -/
def IsAcyclic (G : OutGraph V) : Prop := ∀ v, ¬ Relation.TransGen (Adj G) v v

/-- Delete the ordered pairs in `F` from the edge set of `G`. -/
def deleteArcs [DecidableEq V] (G : OutGraph V) (F : Finset (V × V)) : OutGraph V :=
  fun u => (G u).filter (fun v => (u, v) ∉ F)

/-- `fas G`: the minimum number of edges whose deletion makes `G` acyclic (the set is nonempty:
deleting every pair works). -/
noncomputable def fas [Fintype V] [DecidableEq V] (G : OutGraph V) : ℕ :=
  sInf {k : ℕ | ∃ F : Finset (V × V), F.card = k ∧ IsAcyclic (deleteArcs G F)}

/-- `G` is `ε`-far from acyclic with respect to the degree bound `d`: `fas G ≥ ε · d · |V|`. -/
def IsFar [Fintype V] [DecidableEq V] (ε : ℝ) (d : ℕ) (G : OutGraph V) : Prop :=
  ε * (d : ℝ) * (Fintype.card V : ℝ) ≤ (fas G : ℝ)

/-- The complete blow-up `G^(t)` on `V × [t]`: `(u, i) → (v, j)` iff `u → v` in `G`
(copies are indexed `0, …, t - 1`). -/
def blowUp (G : OutGraph V) (t : ℕ) : OutGraph (V × Fin t) :=
  fun p => G p.1 ×ˢ (Finset.univ : Finset (Fin t))

end AcycTesting.NearLinear


