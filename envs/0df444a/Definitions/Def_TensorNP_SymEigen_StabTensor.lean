-- Prove2me | Definitions.Def_TensorNP_SymEigen_StabTensor
-- name    : TensorNP_SymEigen_StabTensor
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T17:07:45.720446+00:00
-- url     : https://prove2.me/theorems/16986976-3cfb-4837-b58e-2ae6ee1b9a3b
-- title:
--   §9, pp. 0:27–0:28 — the symmetric tensor S_G of a graph and Nesterov's cubic Σ x_i x_j y_ij
-- statement:
--   Let $G=(V,E)$ be a simple graph on the vertex set $V=\{1,\dots,v\}$ and put $n=v+v(v-1)/2$. Coordinates of $\mathbb R^n=\mathbb R^v\times\mathbb R^{v(v-1)/2}$ are written $\mathbf z=(\mathbf x,\mathbf y)$, with $\mathbf x=(x_1,\dots,x_v)$ indexed by vertices and $\mathbf y=(y_{ij})_{i<j}$ indexed by the $v(v-1)/2$ pairs $i<j$ of vertices.
--
--   The **tensor $\mathcal S=\mathcal S_G=[\![s_{abc}]\!]\in\mathbb R^{n\times n\times n}$** has entry $1$ at each of the six orderings $(a,b,c)$ of the three distinct coordinates $(x_i,\,x_j,\,y_{ij})$, for every pair $i<j$ with $\{i,j\}\notin E$, and entry $0$ everywhere else (in particular whenever two of the three indices coincide).
--
--   Attached to $G$ is also **Nesterov's cubic**
--   $$\sum_{i<j,\ \{i,j\}\notin E}x_ix_jy_{ij},$$
--   the polynomial maximized in Nesterov's Theorem 9.2.
--
--   $\mathcal S_G$ is the tensor whose largest eigenvalue Hillar and Lim relate to the stability number of $G$ (Theorem 9.3).
--
--   **Formalization Note** The paper places $y_{ij}$ at position $v+\varphi(i,j)$ with $\varphi(i,j)=(i-1)v-i(i-1)/2+j-i$; in Lean the coordinate set is the disjoint union of the vertices and the pairs $i<j$, which is the same $\mathbb R^n$ with its coordinates labelled by name instead of by $\varphi$. The paper's index range "$1\le i<j<k\le v$" is read as $k\le n$: since $k=v+\varphi(i,j)>v$, the literal range would make $\mathcal S=0$. Vertices are $0,\dots,v-1$ in Lean.
-- source:
--   Hillar & Lim, Most Tensor Problems Are NP-Hard, J. ACM 60(6) (2013), Art. 45 (final version, arXiv:0911.1393v5), pp. 0:27–0:28, §9, definition of s_ijk and S; p. 0:27, Theorem 9.2 (31)

import Mathlib
import Definitions.Def_TensorNP_SymEigen_Defs

namespace TensorNP.SymEigen

/-- The `v(v−1)/2` pairs `i < j` of vertices of a graph on `Fin v` (Hillar–Lim §9, p. 0:27).
The paper enumerates them lexicographically by `φ(i, j) = (i − 1)v − i(i − 1)/2 + j − i`; here a
pair is indexed by itself. -/
abbrev PairIdx (v : ℕ) : Type := {p : Fin v × Fin v // p.1 < p.2}

/-- The index set of `ℝ^n = ℝ^v × ℝ^{v(v−1)/2}`, `n = v + v(v−1)/2` (Theorem 9.2, p. 0:27):
`Sum.inl i` is the coordinate `x_i`, and `Sum.inr ⟨(i, j), _⟩` is the coordinate `y_{ij}`, which
the paper places at position `v + φ(i, j)`. -/
abbrev Idx (v : ℕ) : Type := Fin v ⊕ PairIdx v

/-- The symmetric tensor `S = S_G = ⟦s_{ijk}⟧ ∈ ℝ^{n×n×n}` of Hillar–Lim §9 (pp. 0:27–0:28).
For each pair `i < j` with `{i, j} ∉ E`, the entry is `1` at the six orderings of the three
distinct indices `(x_i, x_j, y_{ij})` (the paper's `(i, j, v + φ(i, j))`); every other entry,
including every entry with two equal indices, is `0`. This is the paper's definition with its
index range "`1 ≤ i < j < k ≤ v`" read as `k ≤ n` (as printed, `k = v + φ(i, j) > v` would make
`S = 0`). -/
noncomputable def stabTensor {v : ℕ} (G : SimpleGraph (Fin v)) : Tensor3 (Idx v) :=
  open Classical in
  fun a b c =>
    if ∃ p : PairIdx v, ¬ G.Adj p.1.1 p.1.2 ∧
        ({a, b, c} : Multiset (Idx v)) = {Sum.inl p.1.1, Sum.inl p.1.2, Sum.inr p}
    then 1 else 0

/-- The cubic polynomial of Nesterov's Theorem 9.2 (31) (p. 0:27):
`∑_{i<j, {i,j}∉E} x_i x_j y_{ij}` for `x ∈ ℝ^v`, `y ∈ ℝ^{v(v−1)/2}`. -/
noncomputable def nesterovForm {v : ℕ} (G : SimpleGraph (Fin v)) (x : Fin v → ℝ)
    (y : PairIdx v → ℝ) : ℝ :=
  open Classical in
  ∑ p ∈ Finset.univ.filter (fun p : PairIdx v => ¬ G.Adj p.1.1 p.1.2), x p.1.1 * x p.1.2 * y p

end TensorNP.SymEigen


