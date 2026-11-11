-- Prove2me | Definitions.Def_PowerMinUncut_Threshold_Instance
-- name    : PowerMinUncut_Threshold_Instance
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T03:43:11.960195+00:00
-- url     : https://prove2.me/theorems/137c412f-abab-445b-8e17-f8c8215eb26b
-- title:
--   Weighted loopless graphs, vector Min Uncut OPT_{k,q}, the elliptope relaxation REL_q, the constant C_{k,p} and the gap set
-- statement:
--   A **weighted graph** $G=(V,E,w)$ has vertices $V=\{0,\dots,N-1\}$ and a symmetric weight function $w:V\times V\to\mathbb Q_{\ge 0}$ with $w_{ii}=0$ (loopless). An edge is an unordered pair $\{i,j\}$, $i\neq j$; sums over $E$ run over the pairs $i<j$, so every edge is counted once, and pairs of weight $0$ contribute nothing. The total weight is $\sum_{ij\in E}w_{ij}$ and $|E|$ is the number of pairs of positive weight.
--
--   For integers $k\ge 1$ and $q\ge 2$, **vector Min Uncut** of rank $k$ and power $q$ is
--   $$\mathrm{OPT}_{k,q}(G)=\min_{v_i\in S^{k-1}}\sum_{ij\in E}w_{ij}\,\|v_i+v_j\|^q,$$
--   with $S^{k-1}$ the unit sphere of $\mathbb R^k$, and its **convex elliptope relaxation** is
--   $$\mathrm{REL}_q(G)=\min_{X\succeq 0,\ X_{ii}=1}\sum_{ij\in E}w_{ij}\,[2(1+X_{ij})]^{q/2},$$
--   the minimum over real positive semidefinite matrices with unit diagonal (correlation matrices). For $k>p$,
--   $$C_{k,p}=\frac{\Gamma((k-1+p)/2)\,\Gamma((k-p)/2)}{\Gamma((k-1)/2)\,\Gamma(k/2)}.$$
--   The **gap set** is the set of ratios $\mathrm{OPT}_{k,q}(G)/\mathrm{REL}_q(G)$ over all such graphs with $\mathrm{REL}_q(G)>0$. A graph's positive-weight support is **bipartite** if some 2-colouring separates the endpoints of every positive-weight edge, and **Min Uncut** is the least total weight of edges whose endpoints get the same colour.
--
--   **Formalization Note.** Graphs are `WGraph` (`Fin N`, `w : Fin N → Fin N → ℚ`); the minima are `⨅` over the nonempty index types `Fin N → sphere 0 1` and the elliptope (for $k\ge1$; both families are bounded below by $0$ and the minima are attained by compactness). The power $q/2$ is `Real.rpow` on the base $2(1+X_{ij})\ge 0$; $\|v_i+v_j\|^q$ is a natural power. `Ckp k p` takes a real power $p$ (Theorem 7 uses real $p$).
-- source:
--   Xie, Sharp Power Loss Thresholds for Vector Min Uncut, STOC 2027 submission (manuscript sha256 391063da…), p. 1, §1 (displays defining OPT_{k,q} and REL_q, Theorem 1); p. 9, Theorem 7 (E3); p. 34, §7; p. 63, §10.11

import Mathlib

/-!
# Weighted loopless graphs, vector Min Uncut `OPT_{k,q}`, the elliptope relaxation `REL_q`,
# and the constant `C_{k,q}`

Xie, *Sharp Power Loss Thresholds for Vector Min Uncut*, STOC 2027 submission (manuscript
sha256 391063da…), p. 1 (§1, the displays defining `OPT_{k,q}` and `REL_q`, Theorem 1),
p. 9 (Theorem 7, (E3)), p. 34 (§7, Eq. (11)), p. 63 (§10.11).

Conventions.
* A graph on `N` vertices is `Fin N` with a symmetric, nonnegative, rational weight function
  `w` with zero diagonal (loopless). An edge is an unordered pair `{i, j}`, `i ≠ j`; sums over
  edges run over the pairs `i < j`, so each edge is counted once. A pair of weight `0` contributes
  nothing, so the edge set `E` is the set of pairs of positive weight.
* `‖·‖` on `EuclideanSpace ℝ (Fin k)` is the Euclidean norm; `S^{k-1}` is `Metric.sphere 0 1`.
* `OPT k q G = min_{v_i ∈ S^{k-1}} Σ_{ij ∈ E} w_ij ‖v_i + v_j‖^q` (an infimum over a nonempty
  family bounded below by `0` when `k ≥ 1`; it is attained by compactness).
* `REL q G = min_{X ⪰ 0, X_ii = 1} Σ_{ij ∈ E} w_ij [2(1 + X_ij)]^{q/2}`, with `Real.rpow` for the
  power `q/2` (the base is `≥ 0` on correlation matrices); an infimum over the nonempty
  (identity matrix) compact elliptope, bounded below by `0`.
* `C k p = Γ((k-1+p)/2) Γ((k-p)/2) / (Γ((k-1)/2) Γ(k/2))` with `Real.Gamma`, for a natural `k`
  and a real power `p` (Theorem 1 uses integer `p = q`, Theorem 7 real `p`).
-/

namespace PowerMinUncut.Threshold

/-- A finite undirected loopless graph `G = (V, E, w)` with nonnegative rational edge weights:
vertices `Fin N`, weights `w i j = w j i ≥ 0`, `w i i = 0`. -/
structure WGraph where
  N : ℕ
  w : Fin N → Fin N → ℚ
  symm : ∀ i j, w i j = w j i
  loopless : ∀ i, w i i = 0
  nonneg : ∀ i j, 0 ≤ w i j

namespace WGraph

/-- Sum of `w_ij · g i j` over the unordered edges `{i, j}` (pairs `i < j`). -/
noncomputable def edgeSum (G : WGraph) (g : Fin G.N → Fin G.N → ℝ) : ℝ :=
  ∑ i, ∑ j, if i < j then (G.w i j : ℝ) * g i j else 0

/-- The total edge weight `Σ_{ij ∈ E} w_ij`. -/
def total (G : WGraph) : ℚ :=
  ∑ i, ∑ j, if i < j then G.w i j else 0

/-- The number of edges `|E|`: unordered pairs of positive weight. -/
def numEdges (G : WGraph) : ℕ :=
  (Finset.univ.filter fun p : Fin G.N × Fin G.N => p.1 < p.2 ∧ G.w p.1 p.2 ≠ 0).card

/-- The `q`-power cost `Σ_{ij ∈ E} w_ij ‖v_i + v_j‖^q` of an assignment of vectors in `ℝ^k`. -/
noncomputable def cost (G : WGraph) (k q : ℕ) (v : Fin G.N → EuclideanSpace ℝ (Fin k)) : ℝ :=
  G.edgeSum fun i j => ‖v i + v j‖ ^ q

/-- Vector Min Uncut of rank `k` and power `q`:
`OPT_{k,q}(G) = min_{v_i ∈ S^{k-1}} Σ_{ij ∈ E} w_ij ‖v_i + v_j‖^q`. -/
noncomputable def OPT (k q : ℕ) (G : WGraph) : ℝ :=
  ⨅ v : Fin G.N → Metric.sphere (0 : EuclideanSpace ℝ (Fin k)) 1,
    G.cost k q fun i => (v i : EuclideanSpace ℝ (Fin k))

/-- Correlation matrices (the elliptope): real positive semidefinite matrices with unit
diagonal. -/
def Elliptope (N : ℕ) : Set (Matrix (Fin N) (Fin N) ℝ) :=
  {X | X.PosSemidef ∧ ∀ i, X i i = 1}

/-- The convex elliptope relaxation
`REL_q(G) = min_{X ⪰ 0, X_ii = 1} Σ_{ij ∈ E} w_ij [2(1 + X_ij)]^{q/2}`. -/
noncomputable def REL (q : ℕ) (G : WGraph) : ℝ :=
  ⨅ X : Elliptope G.N, G.edgeSum fun i j => (2 * (1 + (X : Matrix (Fin G.N) (Fin G.N) ℝ) i j)) ^ ((q : ℝ) / 2)

/-- The positive-weight support is bipartite: some 2-colouring separates the endpoints of every
edge of positive weight. -/
def SupportBipartite (G : WGraph) : Prop :=
  ∃ s : Fin G.N → Bool, ∀ i j, 0 < G.w i j → s i ≠ s j

/-- Ordinary (weighted) Min Uncut: the least total weight of the edges whose endpoints lie on the
same side of a 2-colouring. -/
noncomputable def minUncut (G : WGraph) : ℝ :=
  ⨅ s : Fin G.N → Bool, G.edgeSum fun i j => if s i = s j then 1 else 0

end WGraph

/-- The constant `C_{k,p} = Γ((k-1+p)/2) Γ((k-p)/2) / (Γ((k-1)/2) Γ(k/2))` of Theorems 1 and 7
(used for `k > p`). -/
noncomputable def Ckp (k : ℕ) (p : ℝ) : ℝ :=
  Real.Gamma (((k : ℝ) - 1 + p) / 2) * Real.Gamma (((k : ℝ) - p) / 2) /
    (Real.Gamma (((k : ℝ) - 1) / 2) * Real.Gamma ((k : ℝ) / 2))

/-- The set of integrality ratios `OPT_{k,q}(G) / REL_q(G)` over finite rational weighted loopless
graphs of positive relaxation value (Theorem 1). -/
def gapSet (k q : ℕ) : Set ℝ :=
  {r | ∃ G : WGraph, 0 < WGraph.REL q G ∧ r = WGraph.OPT k q G / WGraph.REL q G}

end PowerMinUncut.Threshold


