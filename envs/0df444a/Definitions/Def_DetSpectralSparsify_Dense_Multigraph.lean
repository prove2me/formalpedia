-- Prove2me | Definitions.Def_DetSpectralSparsify_Dense_Multigraph
-- name    : DetSpectralSparsify_Dense_Multigraph
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T03:58:05.816412+00:00
-- url     : https://prove2.me/theorems/ecf06e15-9071-424a-89c1-1d6f2ed6af68
-- title:
--   Weighted multigraphs with self-loops: degree, Laplacian, conductance, cluster graphs, aggregation and spectral sparsifiers
-- statement:
--   All graphs of the paper are finite undirected weighted **multigraphs** (§2): parallel edges and self-loops are allowed. A multigraph $G$ on the vertex set $V=\{0,\dots,n-1\}$ has edges indexed by $\{0,\dots,m-1\}$; edge $e$ joins $\mathrm{src}(e)$ and $\mathrm{dst}(e)$ and has a real weight $w(e)$. Parallel edges are distinct indices; $\mathrm{src}(e)=\mathrm{dst}(e)$ is a **self-loop**. Sign conditions on weights are stated by each result.
--
--   1. **Weighted degree** $\deg_G(v)$: the total weight of the edges at $v$, where a self-loop of weight $x$ at $v$ contributes $x$ once (p.22: the loop of weight $\deg_G(v)-\deg_{G[U]}(v)$ makes $\deg_{G\langle U\rangle}(v)=\deg_G(v)$). The **volume** of $S\subseteq V$ is $\mathrm{vol}_G(S)=\sum_{v\in S}\deg_G(v)$.
--   2. **Laplacian** $L_G=D_G-A_G$, where $D_G=\mathrm{diag}(\deg_G)$ and $A_G$ is the weighted adjacency matrix in which a loop of weight $x$ at $v$ adds $x$ to $A_G(v,v)$; loops therefore cancel in $L_G$. The **normalized Laplacian** is $\mathcal L_G=D_G^{-1/2}L_GD_G^{-1/2}$.
--   3. **Combinatorial degree** $\deg^\#_G(v)$: the number of non-loop edges at $v$, parallel edges counted with multiplicity; $\Delta^\#_G=\max_v\deg^\#_G(v)$.
--   4. **Conductance.** For $\emptyset\ne S\subsetneq V$ let $w(E_G(S,V\setminus S))$ be the weight of the edges with exactly one endpoint in $S$. The paper's condition $\Phi(G)\ge\phi$ is written as
--   $$w(E_G(S,V\setminus S))\;\ge\;\phi\cdot\min\{\mathrm{vol}_G(S),\mathrm{vol}_G(V\setminus S)\}\qquad\text{for every }\emptyset\ne S\subsetneq V .$$
--   $G$ is **connected** when every such cut is crossed by an edge of positive weight.
--   5. **Induced subgraph** $G[U]$: the edges with both endpoints in $U$. **Cluster graph** $G\langle U\rangle$ (p.22): $G[U]$ plus, at each $v\in U$, a self-loop of weight $\deg_G(v)-\deg_{G[U]}(v)$.
--   6. **Edge-disjoint union** of a finite family of multigraphs on $V$; **contraction** of a multigraph on $V(G^\circ)$ along a fiber map $f:V(G^\circ)\to V$, deleting the resulting self-loops.
--   7. **Aggregation** $\bar G$: self-loops are deleted and the parallel non-loop edges between each pair of vertices are replaced by one edge of their total weight.
--   8. **Weight spread** $b(G)=1+\lceil\log_2(w_{\max}/w_{\min})\rceil$ (p.26), extrema over all edges; $b(G)=1$ when $G$ has no edges.
--   The **number of occupied dyadic classes**, `dyadicClassCount`, counts distinct integers $\lfloor\log_2 w(e)\rfloor$ among non-loop edges. It is zero for an empty edge list, and can be much smaller than $b(G)$ when the weight range has gaps. The aggregation paragraph of Theorem 15 uses this count.
--
--   9. **Spectral sparsifier** (Definition 2): $H$ is a $(1\pm\varepsilon)$-spectral sparsifier of $G$ if
--   $$(1-\varepsilon)L_G\preceq L_H\preceq(1+\varepsilon)L_G,$$
--   where $A\preceq B$ means $B-A$ is positive semidefinite. $H$ is a **reweighted subgraph** of $G$ if every edge of $H$ has positive weight and joins two distinct vertices joined by a non-loop edge of $G$.
--   10. A **matching partition** of the non-loop edges into $t$ classes: a label $<t$ for every non-loop edge such that two distinct non-loop edges with the same label share no endpoint.
--
--   These are the graph objects every statement of the mission is about.
--
--   **Formalization Note** Vertices are `Fin n` and edges `Fin m`, so edge identities and multiplicities are kept. Induced and cluster graphs keep the whole vertex set `Fin n`; the vertices outside $U$ become isolated (degree $0$), which leaves the all-cuts conductance condition equivalent to the one on $U$. The operator norm `opNorm` is the norm of the matrix as a continuous linear map on Euclidean space.
-- source:
--   Trevor Vaughn, Jason Li, Deterministic Spectral Sparsification in Almost-Linear Time for Dense Graphs, STOC 2027 submission #370 (October 2026), source.pdf SHA-256 b88d92728f937730b7e9664f482778048c0b667d4376e0488686c9708e5d8467, pp.4–5 (§2, Definition 2), p.22 (cluster graph G⟨U⟩), p.26 (b(G)), p.27 (aggregation)

import Mathlib

set_option autoImplicit false

namespace DetSpectralSparsify.Dense

open Matrix

/-- A finite undirected weighted multigraph on the vertex set `Fin n` (§2, p.4).
Edges are indexed by `Fin m`; edge `e` joins `src e` and `dst e` (order irrelevant) and has
weight `w e`. Parallel edges are distinct indices; `src e = dst e` is a self-loop.
Sign conditions on the weights are stated as hypotheses where the source makes them. -/
structure Multigraph (n : ℕ) where
  m : ℕ
  src : Fin m → Fin n
  dst : Fin m → Fin n
  w : Fin m → ℝ

namespace Multigraph

variable {n : ℕ}

/-- Edge `e` is a self-loop. -/
def IsLoop (G : Multigraph n) (e : Fin G.m) : Prop := G.src e = G.dst e

instance (G : Multigraph n) (e : Fin G.m) : Decidable (G.IsLoop e) :=
  inferInstanceAs (Decidable (G.src e = G.dst e))

/-- Weighted degree `deg_G(v)`, including self-loops; a loop of weight `x` at `v` adds `x`
once (p.4 and p.22). -/
noncomputable def deg (G : Multigraph n) (v : Fin n) : ℝ :=
  ∑ e : Fin G.m,
    if G.IsLoop e then (if G.src e = v then G.w e else 0)
    else (if G.src e = v then G.w e else 0) + (if G.dst e = v then G.w e else 0)

/-- Weighted adjacency matrix `A_G`; a loop of weight `x` at `v` contributes `x` to `A_G(v,v)`. -/
noncomputable def adj (G : Multigraph n) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun u v => ∑ e : Fin G.m,
    if G.IsLoop e then (if G.src e = u ∧ u = v then G.w e else 0)
    else (if G.src e = u ∧ G.dst e = v then G.w e else 0) +
      (if G.src e = v ∧ G.dst e = u then G.w e else 0)

/-- The diagonal degree matrix `D_G`. -/
noncomputable def degMatrix (G : Multigraph n) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal G.deg

/-- The Laplacian `L_G = D_G - A_G` (self-loops cancel). -/
noncomputable def laplacian (G : Multigraph n) : Matrix (Fin n) (Fin n) ℝ :=
  G.degMatrix - G.adj

/-- The vector `D_G^{1/2} 𝟏`. -/
noncomputable def sqrtDegVec (G : Multigraph n) : Fin n → ℝ := fun v => Real.sqrt (G.deg v)

/-- The normalized Laplacian `𝓛_G = D_G^{-1/2} L_G D_G^{-1/2}` (used only when every degree
is positive). -/
noncomputable def normLaplacian (G : Multigraph n) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal (fun v => (Real.sqrt (G.deg v))⁻¹) * G.laplacian *
    Matrix.diagonal (fun v => (Real.sqrt (G.deg v))⁻¹)

/-- Combinatorial degree `deg#_G(v)`: the number of non-loop edges at `v`, parallel edges
counted with multiplicity, self-loops ignored. -/
def combDeg (G : Multigraph n) (v : Fin n) : ℕ :=
  (Finset.univ.filter fun e : Fin G.m => ¬ G.IsLoop e ∧ (G.src e = v ∨ G.dst e = v)).card

/-- Maximum combinatorial degree `Δ#_G` (`0` for the empty vertex set). -/
def maxCombDeg (G : Multigraph n) : ℕ := Finset.univ.sup G.combDeg

/-- Volume `vol_G(S) = ∑_{v ∈ S} deg_G(v)`. -/
noncomputable def vol (G : Multigraph n) (S : Finset (Fin n)) : ℝ := ∑ v ∈ S, G.deg v

/-- Edge `e` has exactly one endpoint in `S`. -/
def Crosses (G : Multigraph n) (S : Finset (Fin n)) (e : Fin G.m) : Prop :=
  (G.src e ∈ S ∧ G.dst e ∉ S) ∨ (G.dst e ∈ S ∧ G.src e ∉ S)

instance (G : Multigraph n) (S : Finset (Fin n)) (e : Fin G.m) : Decidable (G.Crosses S e) := by
  unfold Crosses; infer_instance

/-- Cut weight `w(E_G(S, V ∖ S))`. -/
noncomputable def cut (G : Multigraph n) (S : Finset (Fin n)) : ℝ :=
  ∑ e : Fin G.m, if G.Crosses S e then G.w e else 0

/-- `Φ(G) ≥ ϕ` (p.5): every cut `∅ ≠ S ⊊ V` has `w(E_G(S, V∖S)) ≥ ϕ · min{vol S, vol (V∖S)}`.
This is the minimum in the source's definition written for all cuts at once; with one vertex it
is vacuous instead of a minimum over an empty family. -/
def CondAtLeast (G : Multigraph n) (ϕ : ℝ) : Prop :=
  ∀ S : Finset (Fin n), S.Nonempty → S ≠ Finset.univ →
    ϕ * min (G.vol S) (G.vol Sᶜ) ≤ G.cut S

/-- `G` is connected: every cut `∅ ≠ S ⊊ V` is crossed by an edge of positive weight. -/
def IsConnected (G : Multigraph n) : Prop :=
  ∀ S : Finset (Fin n), S.Nonempty → S ≠ Finset.univ → ∃ e, G.Crosses S e ∧ 0 < G.w e

/-- No isolated vertices: every vertex is an endpoint of some edge (the standing convention
"we discard isolated vertices", p.5). -/
def NoIsolated (G : Multigraph n) : Prop := ∀ v : Fin n, ∃ e, G.src e = v ∨ G.dst e = v

/-- Every edge has positive weight. -/
def PosWeights (G : Multigraph n) : Prop := ∀ e, 0 < G.w e

/-- Every non-loop edge has weight in `[lo, hi]`. -/
def NonloopWeightsIn (G : Multigraph n) (lo hi : ℝ) : Prop :=
  ∀ e, ¬ G.IsLoop e → lo ≤ G.w e ∧ G.w e ≤ hi

/-- Every self-loop has nonnegative weight. -/
def LoopsNonneg (G : Multigraph n) : Prop := ∀ e, G.IsLoop e → 0 ≤ G.w e

/-- Every edge has unit weight (an unweighted multigraph). -/
def Unweighted (G : Multigraph n) : Prop := ∀ e, G.w e = 1

/-- The same multigraph with every weight replaced by `1` (`G#`, p.24). -/
def unitWeights (G : Multigraph n) : Multigraph n := { G with w := fun _ => 1 }

/-- Induced subgraph `G[U]` on the same vertex type: the edges with both endpoints in `U`
(self-loops in `U` included). Vertices outside `U` become isolated. -/
noncomputable def induced (G : Multigraph n) (U : Finset (Fin n)) : Multigraph n :=
  let s := Finset.univ.filter fun e : Fin G.m => G.src e ∈ U ∧ G.dst e ∈ U
  { m := s.card
    src := fun j => G.src (s.equivFin.symm j).1
    dst := fun j => G.dst (s.equivFin.symm j).1
    w := fun j => G.w (s.equivFin.symm j).1 }

/-- The cluster graph `G⟨U⟩` (p.22): `G[U]` plus, at every `v ∈ U`, a self-loop of weight
`deg_G(v) - deg_{G[U]}(v)`. The loops are listed after the edges of `G[U]`, in vertex order. -/
noncomputable def cluster (G : Multigraph n) (U : Finset (Fin n)) : Multigraph n :=
  let H := G.induced U
  let L : Fin U.card → Fin n := fun i => (U.equivFin.symm i).1
  { m := H.m + U.card
    src := Fin.append H.src L
    dst := Fin.append H.dst L
    w := Fin.append H.w (fun i => G.deg (L i) - H.deg (L i)) }

/-- Edge-disjoint union of a finite family of multigraphs on the same vertex set. -/
def union {t : ℕ} (Gs : Fin t → Multigraph n) : Multigraph n where
  m := ∑ i, (Gs i).m
  src := fun e => (Gs (finSigmaFinEquiv.symm e).1).src (finSigmaFinEquiv.symm e).2
  dst := fun e => (Gs (finSigmaFinEquiv.symm e).1).dst (finSigmaFinEquiv.symm e).2
  w := fun e => (Gs (finSigmaFinEquiv.symm e).1).w (finSigmaFinEquiv.symm e).2

/-- Contract every fiber `f⁻¹(v)` of a multigraph on `Fin N` to the vertex `v ∈ Fin n`, and
delete the self-loops this creates or that were already present (Lemma 10 (iv), Algorithm 6). -/
noncomputable def contract {N : ℕ} (f : Fin N → Fin n) (H : Multigraph N) : Multigraph n :=
  let s := Finset.univ.filter fun e : Fin H.m => f (H.src e) ≠ f (H.dst e)
  { m := s.card
    src := fun j => f (H.src (s.equivFin.symm j).1)
    dst := fun j => f (H.dst (s.equivFin.symm j).1)
    w := fun j => H.w (s.equivFin.symm j).1 }

/-- `lab` partitions the non-loop edges of `G` into the matchings `lab⁻¹(0), …, lab⁻¹(t-1)`:
every non-loop edge gets a label `< t`, and two distinct non-loop edges with the same label share
no endpoint (Lemma 11). Labels of self-loops are ignored. -/
def IsMatchingPartition (G : Multigraph n) (t : ℕ) (lab : Fin G.m → ℕ) : Prop :=
  (∀ e, ¬ G.IsLoop e → lab e < t) ∧
  ∀ e e', e ≠ e' → ¬ G.IsLoop e → ¬ G.IsLoop e' → lab e = lab e' →
    G.src e ≠ G.src e' ∧ G.src e ≠ G.dst e' ∧ G.dst e ≠ G.src e' ∧ G.dst e ≠ G.dst e'

/-- The unordered vertex pairs `{u, v}`, `u < v`, joined by at least one non-loop edge. -/
def aggPairs (G : Multigraph n) : Finset (Fin n × Fin n) :=
  Finset.univ.filter fun p => p.1 < p.2 ∧
    ∃ e : Fin G.m, (G.src e = p.1 ∧ G.dst e = p.2) ∨ (G.src e = p.2 ∧ G.dst e = p.1)

/-- Total weight of the non-loop edges between `p.1` and `p.2`. -/
noncomputable def pairWeight (G : Multigraph n) (p : Fin n × Fin n) : ℝ :=
  ∑ e : Fin G.m,
    if (G.src e = p.1 ∧ G.dst e = p.2) ∨ (G.src e = p.2 ∧ G.dst e = p.1) then G.w e else 0

/-- The aggregated graph `Ḡ` (Theorem 15, p.27; Algorithm 9 line 1): self-loops deleted and the
parallel non-loop edges between each pair of vertices replaced by one edge carrying their total
weight. -/
noncomputable def aggregate (G : Multigraph n) : Multigraph n :=
  let s := G.aggPairs
  { m := s.card
    src := fun j => (s.equivFin.symm j).1.1
    dst := fun j => (s.equivFin.symm j).1.2
    w := fun j => G.pairWeight (s.equivFin.symm j).1 }

/-- `b(G) = 1 + ⌈log₂ (w_max / w_min)⌉` (p.26), extrema over all edges of `G`; set to `1` when
`G` has no edges. -/
noncomputable def bClasses (G : Multigraph n) : ℕ :=
  if h : 0 < G.m then
    1 + ⌈Real.logb 2 (Finset.univ.sup' ⟨⟨0, h⟩, Finset.mem_univ _⟩ G.w /
      Finset.univ.inf' ⟨⟨0, h⟩, Finset.mem_univ _⟩ G.w)⌉₊
  else 1


/-- Number of occupied dyadic classes of the non-loop edges (Theorem 15, p.27).
For positive weights, edge `e` belongs to class `⌊log₂(w e)⌋`; empty classes in the
weight span are not counted. The empty graph has zero occupied classes. -/
noncomputable def dyadicClassCount (G : Multigraph n) : ℕ :=
  ((Finset.univ.filter fun e : Fin G.m => ¬ G.IsLoop e).image
    (fun e => (⌊Real.logb 2 (G.w e)⌋ : ℤ))).card

end Multigraph

/-- Loewner order on real square matrices: `A ⪯ B` iff `B - A` is positive semidefinite. -/
def PSDLe {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℝ) : Prop := (B - A).PosSemidef

/-- Operator norm (spectral norm) of a real square matrix acting on Euclidean space. -/
noncomputable def opNorm {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ) : ℝ :=
  ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖

/-- Definition 2 (p.5): `H` is a `(1 ± ε)`-spectral sparsifier of `G`:
`(1 - ε) L_G ⪯ L_H ⪯ (1 + ε) L_G`. -/
def IsSpectralSparsifier {n : ℕ} (ε : ℝ) (G H : Multigraph n) : Prop :=
  PSDLe ((1 - ε) • G.laplacian) H.laplacian ∧ PSDLe H.laplacian ((1 + ε) • G.laplacian)

/-- `H` is a reweighted subgraph of `G`: every edge of `H` has positive weight and joins two
distinct vertices that are joined by a non-loop edge of `G`. -/
def IsReweightedSubgraph {n : ℕ} (G H : Multigraph n) : Prop :=
  ∀ e : Fin H.m, 0 < H.w e ∧ H.src e ≠ H.dst e ∧
    ∃ f : Fin G.m, (G.src f = H.src e ∧ G.dst f = H.dst e) ∨
      (G.src f = H.dst e ∧ G.dst f = H.src e)

/-- The output specification shared by every sparsification result of the paper:
`H` is a `(1 ± ε)`-spectral sparsifier of `G` and a reweighted subgraph of `G`. -/
def IsSparsifierOutput {n : ℕ} (ε : ℝ) (G H : Multigraph n) : Prop :=
  IsSpectralSparsifier ε G H ∧ IsReweightedSubgraph G H

end DetSpectralSparsify.Dense


