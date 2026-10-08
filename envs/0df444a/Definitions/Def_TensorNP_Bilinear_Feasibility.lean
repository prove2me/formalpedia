-- Prove2me | Definitions.Def_TensorNP_Bilinear_Feasibility
-- name    : TensorNP_Bilinear_Feasibility
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T18:05:09.65885+00:00
-- url     : https://prove2.me/theorems/21019efb-10d5-4ef1-8d6e-9dc812c8dd7c
-- title:
--   Problem 3.1 — tensor bilinear feasibility, and the doubled tensor of Lemma 3.6
-- statement:
--   Let $F$ be a field (in the paper $F = \mathbb R$ or $F = \mathbb C$) and let $\mathcal A = [\![a_{ijk}]\!]$ be a 3-tensor with entries in $F$, indexed by $i \in I$, $j \in J$, $k \in K$ for finite index sets $I, J, K$ (for $\mathcal A \in F^{l\times m\times n}$ these are $\{1,\dots,l\}$, $\{1,\dots,m\}$, $\{1,\dots,n\}$). Its slices are the matrices $A_i(j,k) = B_j(i,k) = C_k(i,j) = a_{ijk}$.
--
--   **Tensor bilinear feasibility** (Problem 3.1) asks whether the system (9)
--   $$
--   \mathbf v^\top A_i \mathbf w = \sum_{j,k} a_{ijk} v_j w_k = 0 \ (\forall i), \qquad
--   \mathbf u^\top B_j \mathbf w = \sum_{i,k} a_{ijk} u_i w_k = 0 \ (\forall j), \qquad
--   \mathbf u^\top C_k \mathbf v = \sum_{i,j} a_{ijk} u_i v_j = 0 \ (\forall k)
--   $$
--   has a solution $\mathbf u \in F^I$, $\mathbf v \in F^J$, $\mathbf w \in F^K$ in which **each** of the three vectors is nonzero. We write $\mathrm{TBF}(\mathcal A)$ when it does. The three families are determined by the one tensor $\mathcal A$; they are not three independent families of matrices (that would be Problem 3.5).
--
--   The file also defines the tensor $\mathcal B$ of the proof of Lemma 3.6. For $\mathcal A$ with slices $A_i$, $\mathcal B \in R^{2l\times 2m\times 2n}$ has the slices
--   $$
--   B_i = \begin{bmatrix} A_i & 0 \\ 0 & -A_i \end{bmatrix}, \qquad
--   B_{l+i} = \begin{bmatrix} 0 & A_i \\ A_i & 0 \end{bmatrix}, \qquad i = 1,\dots,l .
--   $$
--
--   These are the decision problem of the mission and the construction that transfers it from $\mathbb C$ to $\mathbb R$.
--
--   **Formalization Note** A tensor is a function `A : I → J → K → F` over finite types; indices are 0-based, so the paper's $a_{ijk}$ on $F^{l\times m\times n}$ is `A (i-1) (j-1) (k-1)` on `Fin l`, `Fin m`, `Fin n`. The doubled index sets are the disjoint unions `I ⊕ I`, `J ⊕ J`, `K ⊕ K`: `Sum.inl i` is the paper's index $i$ and `Sum.inr i` is its index $l+i$ (resp. $m+j$, $n+k$). The block matrices are read with rows indexed by $j$ and columns by $k$.
-- source:
--   Hillar & Lim, Most Tensor Problems Are NP-Hard, J. ACM 60(6) (2013), Art. 45 (final version, arXiv:0911.1393v5), p. 0:15, Problem 3.1, system (9); p. 0:17, proof of Lemma 3.6

import Mathlib

namespace TensorNP.Bilinear

/-! # Tensor bilinear feasibility (Hillar–Lim, Problem 3.1, p. 0:15) and the realification of
Lemma 3.6 (p. 0:17)

A 3-tensor is an array `A : I → J → K → F` over finite index types; for the paper's
`A ∈ F^{l×m×n}` take `I = Fin l`, `J = Fin m`, `K = Fin n` (indices are 0-based in Lean, so the
paper's `a_{ijk}` is `A (i-1) (j-1) (k-1)`). -/

/-- **Tensor bilinear feasibility** (Problem 3.1, system (9)). With the slices
`A_i(j,k) = B_j(i,k) = C_k(i,j) = a_{ijk}` of the single tensor `A`, the system (9) reads
`vᵀ A_i w = Σ_{j,k} a_{ijk} v_j w_k = 0` for every `i`, `uᵀ B_j w = Σ_{i,k} a_{ijk} u_i w_k = 0`
for every `j`, and `uᵀ C_k v = Σ_{i,j} a_{ijk} u_i v_j = 0` for every `k`. `TBF A` holds iff the
system has a solution with **each** of `u`, `v`, `w` nonzero. -/
def TBF {I J K F : Type*} [Fintype I] [Fintype J] [Fintype K] [CommRing F]
    (A : I → J → K → F) : Prop :=
  ∃ (u : I → F) (v : J → F) (w : K → F), u ≠ 0 ∧ v ≠ 0 ∧ w ≠ 0 ∧
    (∀ i, ∑ j, ∑ k, A i j k * v j * w k = 0) ∧
    (∀ j, ∑ i, ∑ k, A i j k * u i * w k = 0) ∧
    (∀ k, ∑ i, ∑ j, A i j k * u i * v j = 0)

/-- The tensor `B` of the proof of Lemma 3.6 (p. 0:17), built from `A` with slices
`A_i = A(i, ·, ·)`: its slices are
`B_i = [[A_i, 0], [0, -A_i]]` and `B_{l+i} = [[0, A_i], [A_i, 0]]` for `i = 1, …, l`.
The doubled index sets are `I ⊕ I`, `J ⊕ J`, `K ⊕ K`: `Sum.inl i` is the paper's index `i` and
`Sum.inr i` is the paper's index `l + i` (likewise for `j`, with `m`, and `k`, with `n`). -/
def doubling {I J K R : Type*} [Ring R] (A : I → J → K → R) : I ⊕ I → J ⊕ J → K ⊕ K → R
  | .inl i, .inl j, .inl k => A i j k
  | .inl i, .inr j, .inr k => -A i j k
  | .inr i, .inl j, .inr k => A i j k
  | .inr i, .inr j, .inl k => A i j k
  | _, _, _ => 0

end TensorNP.Bilinear


