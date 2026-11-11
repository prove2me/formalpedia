-- Prove2me | Definitions.Def_HiddenCorr_ERM_CandidateGraph
-- name    : HiddenCorr_ERM_CandidateGraph
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T02:34:35.226195+00:00
-- url     : https://prove2.me/theorems/1a1bd00f-d229-4443-b8cb-79101ac5f264
-- title:
--   Candidate graphs, perfect matchings, matching-covered graphs, the bipartite Laplacian, the incidence matrix and $n_{\mathrm{eff}}(G)$
-- statement:
--   In **learning with hidden correspondences** the learner sees inputs $X_1,\dots,X_n$ and labels $Y_1,\dots,Y_n$ without their pairing, together with a bipartite **candidate graph** $G=(U\cup V,E)$ whose sides $U$ and $V$ are two disjoint copies of $[n]$ (inputs and labels). An edge $(i,j)\in E\subseteq U\times V$ says that label $j$ may belong to input $i$; $m=|E|$.
--
--   A **perfect matching** of $G$ is identified with the bijection $M:U\to V$ it induces: every pair $(i,M(i))$ is an edge. $\mathcal M(G)$ is the set of perfect matchings, and $x_{M'}\in\{0,1\}^m$ is the edge-indicator vector of $M'\in\mathcal M(G)$. $G$ is **matching-covered** if every edge lies in some perfect matching (connectedness is not required).
--
--   The **degree** $\deg(v)$ of a vertex is its number of incident edges. With $A_G\in\mathbb R^{2n\times 2n}$ the adjacency matrix and $D$ the diagonal degree matrix, the (unnormalized) **Laplacian** is $L=D-A_G$. The **oriented incidence matrix** $B\in\mathbb R^{2n\times m}$ has, in the column of the edge $e=(i,j)$, entry $+1$ at $i\in U$, $-1$ at $j\in V$ and $0$ elsewhere. The **bipartite demand vector** $u\in\mathbb R^{2n}$ is $+1$ on $U$ and $-1$ on $V$, and the **effective sample size** of $G$ is the Laplacian energy
--   $$n_{\mathrm{eff}}(G)=u^\top L^\dagger u,$$
--   with $L^\dagger$ the Moore–Penrose pseudoinverse.
--
--   **Formalization Note.** $U$ and $V$ are `Fin n`, the vertex set $U\cup V$ is `Fin n ⊕ Fin n` (`Vtx n`), $E$ is a `Finset (Fin n × Fin n)`, and a perfect matching is a permutation `σ` of `Fin n` with `(i, σ i) ∈ E` for all `i` (`IsPerfectMatching`). Edges index the columns of $B$ and the coordinates of $x_{M'}$ through the subtype `↥E`. `neff E = IncrementalER.energy (laplacian E) (demand n)`, the published energy $d^\top L^\dagger d$.
-- source:
--   Chen, Gentile, Kaplan, Koren, Supervised Learning with Hidden Correspondences, STOC 2027 submission (manuscript sha256 d0029978…), p. 1; p. 14, §4.1 and footnote 2; pp. 14–15, §4.2, Eq. (19); p. 9, §2.2

import Mathlib
import Definitions.Def_IncrementalER_energy

open Matrix

namespace HiddenCorr.ERM

/-!
# Candidate graphs, perfect matchings, the bipartite Laplacian and the effective sample size

Chen, Gentile, Kaplan, Koren, *Supervised Learning with Hidden Correspondences*, STOC 2027
submission (manuscript sha256 d0029978…), p. 1, §4.1 (p. 14, footnote 2), §4.2 (pp. 14–15,
Eq. (19)), §2.2 (p. 9).

* The candidate graph `G = (U ∪ V, E)` has two disjoint copies `U`, `V` of `[n]`, encoded as
  `Fin n` (inputs) and `Fin n` (labels); its edge set is `E ⊆ Fin n × Fin n`, the edge `(i, j)`
  joining input `i ∈ U` to label `j ∈ V`. Its vertex set `U ∪ V` is `Fin n ⊕ Fin n`
  (`Sum.inl i` = input vertex `i`, `Sum.inr j` = label vertex `j`).
* A perfect matching is identified with the bijection `M : U → V` it induces: a permutation `σ`
  of `Fin n` with `(i, σ i) ∈ E` for every `i`.
* `G` is matching-covered if every edge lies in some perfect matching.
* `L = D − A_G` is the unnormalized Laplacian of `G` (`2n × 2n`), `u` the bipartite demand vector
  (`+1` on `U`, `−1` on `V`), and `n_eff(G) = uᵀ L† u` the Laplacian energy, computed with the
  published `IncrementalER.energy` (Moore–Penrose pseudoinverse).
* `B` is the oriented incidence matrix (`2n × |E|`, column of `e = (i, j)` equal to `+1` at `i`,
  `−1` at `j`); `x_{M'}` is the edge-indicator vector of a perfect matching `M'`.
-/

/-- The vertex set `U ∪ V` of a candidate graph: `Sum.inl i` is input vertex `i ∈ U`,
`Sum.inr j` is label vertex `j ∈ V`. -/
abbrev Vtx (n : ℕ) : Type := Fin n ⊕ Fin n

/-- `σ` is (the bijection `U → V` induced by) a perfect matching of the candidate graph with edge
set `E`: every pair `(i, σ i)` is an edge. `M(G)` is the set of such `σ`. -/
def IsPerfectMatching {n : ℕ} (E : Finset (Fin n × Fin n)) (σ : Equiv.Perm (Fin n)) : Prop :=
  ∀ i : Fin n, (i, σ i) ∈ E

/-- The candidate graph is matching-covered (footnote 2, p. 14): every edge belongs to at least one
perfect matching. Connectedness is not required. -/
def MatchingCovered {n : ℕ} (E : Finset (Fin n × Fin n)) : Prop :=
  ∀ e ∈ E, ∃ σ : Equiv.Perm (Fin n), IsPerfectMatching E σ ∧ σ e.1 = e.2

/-- Degree of input vertex `i ∈ U`: the number of edges `(i, j) ∈ E`. -/
def degU {n : ℕ} (E : Finset (Fin n × Fin n)) (i : Fin n) : ℕ :=
  (E.filter (fun e => e.1 = i)).card

/-- Degree of label vertex `j ∈ V`: the number of edges `(i, j) ∈ E`. -/
def degV {n : ℕ} (E : Finset (Fin n × Fin n)) (j : Fin n) : ℕ :=
  (E.filter (fun e => e.2 = j)).card

/-- The degree `deg(v)` of a vertex `v ∈ U ∪ V`. -/
def deg {n : ℕ} (E : Finset (Fin n × Fin n)) : Vtx n → ℕ
  | Sum.inl i => degU E i
  | Sum.inr j => degV E j

/-- The unweighted adjacency matrix `A_G ∈ ℝ^{2n×2n}` of the bipartite graph: entry `1` between
`i ∈ U` and `j ∈ V` when `(i, j) ∈ E`, and `0` otherwise (in particular `0` within a side). -/
def adjacency {n : ℕ} (E : Finset (Fin n × Fin n)) : Matrix (Vtx n) (Vtx n) ℝ :=
  Matrix.of fun a b =>
    match a, b with
    | Sum.inl i, Sum.inr j => if (i, j) ∈ E then 1 else 0
    | Sum.inr j, Sum.inl i => if (i, j) ∈ E then 1 else 0
    | Sum.inl _, Sum.inl _ => 0
    | Sum.inr _, Sum.inr _ => 0

/-- The unnormalized graph Laplacian `L = D − A_G` (§4.2, p. 14), `D` the diagonal matrix of vertex
degrees. -/
def laplacian {n : ℕ} (E : Finset (Fin n × Fin n)) : Matrix (Vtx n) (Vtx n) ℝ :=
  Matrix.diagonal (fun v => (deg E v : ℝ)) - adjacency E

/-- The bipartite demand vector `u ∈ ℝ^{2n}`: `+1` on `U`, `−1` on `V` (§4.2, p. 15). -/
def demand (n : ℕ) : Vtx n → ℝ
  | Sum.inl _ => 1
  | Sum.inr _ => -1

/-- The effective sample size `n_eff(G) = uᵀ L† u` (Eq. (19), p. 15), the Laplacian energy of the
bipartite demand vector, with `L†` the Moore–Penrose pseudoinverse. -/
noncomputable def neff {n : ℕ} (E : Finset (Fin n × Fin n)) : ℝ :=
  IncrementalER.energy (laplacian E) (demand n)

/-- The oriented incidence matrix `B ∈ ℝ^{2n×m}` (§4.2, p. 15), every edge directed from `U` to
`V`: the column of `e = (i, j)` is `+1` at `i ∈ U`, `−1` at `j ∈ V`, and `0` elsewhere. Edges are
indexed by the subtype `↥E`. -/
def incidence {n : ℕ} (E : Finset (Fin n × Fin n)) : Matrix (Vtx n) E ℝ :=
  Matrix.of fun a e =>
    match a with
    | Sum.inl i => if e.1.1 = i then 1 else 0
    | Sum.inr j => if e.1.2 = j then -1 else 0

/-- The edge-indicator vector `x_{M'} ∈ {0, 1}^m` of the perfect matching `σ`: `1` on the edges
`(i, σ i)`, `0` on the other edges. -/
def matchingIndicator {n : ℕ} (E : Finset (Fin n × Fin n)) (σ : Equiv.Perm (Fin n)) :
    E → ℝ :=
  fun e => if σ e.1.1 = e.1.2 then 1 else 0

end HiddenCorr.ERM


