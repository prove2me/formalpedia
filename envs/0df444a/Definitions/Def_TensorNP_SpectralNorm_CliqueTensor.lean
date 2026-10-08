-- Prove2me | Definitions.Def_TensorNP_SpectralNorm_CliqueTensor
-- name    : TensorNP_SpectralNorm_CliqueTensor
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T17:07:00.990973+00:00
-- url     : https://prove2.me/theorems/0295d264-7d7e-4fa1-9bf5-49b349b71aed
-- title:
--   §6 — the matrices Q_l and E_k, the values M_l, N_l, T_l, the form (26) and the rational tensor A_l of a graph
-- statement:
--   Let $G=(V,E)$ be a simple graph with vertex set $V=\{1,\dots,v\}$ and $e$ edges, enumerated as $\{i_1,j_1\},\dots,\{i_e,j_e\}$; let $A_G$ be its adjacency matrix, $J$ the $v\times v$ all-ones matrix, $I$ the identity, and $\Delta_v=\{\mathbf x\in\mathbb R^v_{\ge 0}:\sum_i x_i=1\}$ the standard simplex. For a positive integer $l$:
--
--   1. $Q_l = A_G + \frac1l J$ and
--   $$
--   M_l = \max_{\mathbf x\in\Delta_v} \mathbf x^\top Q_l\mathbf x .
--   $$
--   2. For $k=1,\dots,e$, $E_k=\frac12E_{i_kj_k}+\frac12E_{j_ki_k}$, where $E_{ij}$ has a $1$ in position $(i,j)$ and zeros elsewhere, and
--   $$
--   N_l = \max_{\|\mathbf u\|_2=1}\Big\{\sum_{i=1}^l\Big(\mathbf u^\top\tfrac1lI\mathbf u\Big)^2 + 2\sum_{k=1}^e(\mathbf u^\top E_k\mathbf u)^2\Big\}.
--   $$
--   3. For $\mathbf u,\mathbf v\in\mathbb R^v$ and $\mathbf w\in\mathbb R^{l+2e}$, the multilinear form (26) is
--   $$
--   \sum_{i=1}^l\Big(\mathbf u^\top\tfrac1lI\mathbf v\Big)w_i+\sum_{k=1}^e(\mathbf u^\top E_k\mathbf v)w_{l+k}+\sum_{k=1}^e(\mathbf u^\top E_k\mathbf v)w_{e+l+k},
--   $$
--   and $T_l$ is its maximum over $\|\mathbf u\|_2=\|\mathbf v\|_2=\|\mathbf w\|_2=1$.
--   4. $\mathcal A_l\in\mathbb Q^{v\times v\times(l+2e)}$ is the tensor whose entry $a_{ijk}$ is the coefficient of $u_iv_jw_k$ in (26): $a_{ijk}=\frac1l[i=j]$ for $k\le l$, and $a_{ijk}=(E_{k'})_{ij}$ for $k=l+k'$ and for $k=e+l+k'$, $1\le k'\le e$.
--
--   These are the objects of the reduction from the clique number to the spectral norm and singular values of a rational tensor (proof of Theorem 6.5).
--
--   **Formalization Note** Vertices are `Fin v` (the paper's vertex $i$ is `i-1`), and the edge enumeration is an arbitrary equivalence `ε : Fin e ≃ G.edgeSet` (the paper's $k$-th edge is `ε (k-1)`); every theorem of the mission holds for every enumeration. The $(i,j)$ entry of $E_k$ is written as $\frac12$ if $\{i,j\}=\{i_k,j_k\}$ and $0$ otherwise, which equals $\frac12E_{i_kj_k}+\frac12E_{j_ki_k}$ because $i_k\neq j_k$. The maxima $M_l$, $N_l$, $T_l$ are written as `sSup` of the image of a compact nonempty set (for $v\ge1$), so they are attained. The statement of Lemma 6.11 prints the index $w_{m+l+k}$ in the third sum; there is no $m$ in this section, and the proof on p. 0:24 uses $w_{e+l+k}$, which is what is formalized. The tensor $\mathcal A_l$ has rational entries; theorems read it over $\mathbb R$ by casting entrywise.
-- source:
--   Hillar & Lim, Most Tensor Problems Are NP-Hard, J. ACM 60(6) (2013), Art. 45 (final version, arXiv:0911.1393v5), p. 0:22 (Q_l, M_l, E_k); p. 0:23 (N_l, (26)); p. 0:24, proof of Lemma 6.11 and proof of Theorem 6.5 (A_l)

import Mathlib
import Definitions.Def_TensorNP_SpectralNorm_Tensor

namespace TensorNP.SpectralNorm

open Matrix

/-! # The graph data of §6: `Q_l`, `M_l`, `E_k`, `N_l`, the form (26), `T_l` and the tensor `A_l`
(Hillar–Lim, pp. 0:22–0:24)

`G` is a simple graph on the vertex set `Fin v` (the paper's vertex `i` is `i-1`). Its `e` edges
are enumerated by an equivalence `ε : Fin e ≃ G.edgeSet`; the paper's `k`-th edge `{i_k, j_k}`
is `ε (k-1)`. -/

/-- The matrix `E_k = ½ E_{i_k j_k} + ½ E_{j_k i_k}` of an edge `s = {i_k, j_k}`: its `(i, j)`
entry is `1/2` if `{i, j} = s` and `0` otherwise (for a loopless edge `i_k ≠ j_k` the two
matrices `E_{i_k j_k}`, `E_{j_k i_k}` have disjoint supports, so this is the same matrix). -/
def edgeMatrix (R : Type*) [Field R] {v : ℕ} (s : Sym2 (Fin v)) : Matrix (Fin v) (Fin v) R :=
  Matrix.of fun i j => if s(i, j) = s then (1 / 2 : R) else 0

/-- `Q_l = A_G + (1/l) J`, with `A_G` the adjacency matrix of `G` and `J` the all-ones matrix. -/
noncomputable def Qmat {v : ℕ} (G : SimpleGraph (Fin v)) [DecidableRel G.Adj] (l : ℕ) :
    Matrix (Fin v) (Fin v) ℝ :=
  G.adjMatrix ℝ + (1 / (l : ℝ)) • Matrix.of (fun _ _ => (1 : ℝ))

/-- `M_l = max_{x ∈ Δ_v} xᵀ Q_l x`, as the supremum over the standard simplex
`Δ_v = {x ∈ ℝ^v_{≥0} : Σ_i x_i = 1}` (Mathlib's `stdSimplex`). -/
noncomputable def Mval {v : ℕ} (G : SimpleGraph (Fin v)) [DecidableRel G.Adj] (l : ℕ) : ℝ :=
  sSup ((fun x : Fin v → ℝ => x ⬝ᵥ (Qmat G l *ᵥ x)) '' stdSimplex ℝ (Fin v))

/-- `N_l = max_{‖u‖₂=1} { Σ_{i=1}^l (uᵀ (1/l) I u)² + 2 Σ_{k=1}^e (uᵀ E_k u)² }`, as the supremum
over the unit sphere. -/
noncomputable def Nval {v e : ℕ} (G : SimpleGraph (Fin v)) (ε : Fin e ≃ G.edgeSet) (l : ℕ) : ℝ :=
  sSup ((fun u : Fin v → ℝ =>
      ∑ _i : Fin l, (u ⬝ᵥ (((1 / (l : ℝ)) • (1 : Matrix (Fin v) (Fin v) ℝ)) *ᵥ u)) ^ 2 +
        2 * ∑ k : Fin e, (u ⬝ᵥ (edgeMatrix ℝ (ε k : Sym2 (Fin v)) *ᵥ u)) ^ 2) ''
    {u | l2norm u = 1})

/-- The multilinear form (26), with `u, v ∈ ℝ^v` and `w ∈ ℝ^{l+2e}`:
`Σ_{i=1}^l (uᵀ(1/l)I v) w_i + Σ_{k=1}^e (uᵀE_k v) w_{l+k} + Σ_{k=1}^e (uᵀE_k v) w_{e+l+k}`.
In 0-based indices the three blocks of `w` are `0, …, l-1`, `l, …, l+e-1` and
`l+e, …, l+2e-1`. (The statement of Lemma 6.11 prints `w_{m+l+k}` for the third block; its
proof, p. 0:24, has `w_{e+l+k}`, which is used here.) -/
noncomputable def form26 {v e : ℕ} (G : SimpleGraph (Fin v)) (ε : Fin e ≃ G.edgeSet) (l : ℕ)
    (x y : Fin v → ℝ) (w : Fin (l + 2 * e) → ℝ) : ℝ :=
  (∑ i : Fin l, (x ⬝ᵥ (((1 / (l : ℝ)) • (1 : Matrix (Fin v) (Fin v) ℝ)) *ᵥ y)) *
      w ⟨i.val, by omega⟩) +
    (∑ k : Fin e, (x ⬝ᵥ (edgeMatrix ℝ (ε k : Sym2 (Fin v)) *ᵥ y)) * w ⟨l + k.val, by omega⟩) +
    (∑ k : Fin e, (x ⬝ᵥ (edgeMatrix ℝ (ε k : Sym2 (Fin v)) *ᵥ y)) * w ⟨e + l + k.val, by omega⟩)

/-- `T_l`, the maximum of (26) over `‖u‖₂ = ‖v‖₂ = ‖w‖₂ = 1`, as a supremum. -/
noncomputable def Tval {v e : ℕ} (G : SimpleGraph (Fin v)) (ε : Fin e ≃ G.edgeSet) (l : ℕ) : ℝ :=
  sSup {t : ℝ | ∃ (x y : Fin v → ℝ) (w : Fin (l + 2 * e) → ℝ),
    l2norm x = 1 ∧ l2norm y = 1 ∧ l2norm w = 1 ∧ t = form26 G ε l x y w}

/-- The rational tensor `A_l ∈ ℚ^{v × v × (l+2e)}` of the proof of Theorem 6.5 (p. 0:24): its
entry `a_{ijk}` is the coefficient of `u_i v_j w_k` in (26). For `k` in the first block it is
`1/l` if `i = j` and `0` otherwise; for `k = l + k'` or `k = e + l + k'` (0-based) it is the
`(i, j)` entry of `E_{k'}`. -/
noncomputable def cliqueTensor {v e : ℕ} (G : SimpleGraph (Fin v)) (ε : Fin e ≃ G.edgeSet)
    (l : ℕ) : Fin v → Fin v → Fin (l + 2 * e) → ℚ :=
  fun i j k =>
    if _h0 : k.val < l then (if i = j then 1 / (l : ℚ) else 0)
    else if _h1 : k.val < l + e then
      edgeMatrix ℚ (ε ⟨k.val - l, by omega⟩ : Sym2 (Fin v)) i j
    else
      edgeMatrix ℚ (ε ⟨k.val - l - e, by omega⟩ : Sym2 (Fin v)) i j

end TensorNP.SpectralNorm


