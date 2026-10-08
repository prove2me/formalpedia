-- Prove2me | Definitions.Def_TensorNP_Bilinear_Construction
-- name    : TensorNP_Bilinear_Construction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T18:05:48.493119+00:00
-- url     : https://prove2.me/theorems/edfe582b-dee0-4f9f-b1c0-4b100cd59b24
-- title:
--   Proof of Theorem 3.7 — the tensor $\mathcal A_G$ with $v(2v+5)$ slices
-- statement:
--   Let $G = (V, E)$ be a simple graph on $V = \{1,\dots,v\}$, and write the two vectors of unknowns of the proof of Theorem 3.7 as $\mathbf v = (x_1,\dots,x_v,y_1,\dots,y_v,z)$ and $\mathbf w = (\hat x_1,\dots,\hat x_v,\hat y_1,\dots,\hat y_v,\hat z)$, both of length $2v+1$. The integer tensor $\mathcal A_G = [\![a_{sjk}]\!]$, $a_{sjk} = A_s(j,k)$, has $l = v(2v+5)$ slices $A_s \in \mathbb Z^{(2v+1)\times(2v+1)}$ in three blocks:
--
--   1. **Minors** ($v(2v+1)$ slices): for each pair of rows $a < b$ of the $(2v+1)\times 2$ matrix $[\mathbf v\ \mathbf w]$, the matrix with $\mathbf v^\top A_s \mathbf w = v_a w_b - v_b w_a$, the $2\times 2$ minor of rows $a, b$. Its entries lie in $\{-1,0,1\}$.
--   2. **Cube roots** ($3v$ slices): for each vertex $i$, the bilinear forms
--   $$ x_i\hat y_i - z\hat z, \qquad y_i\hat z - x_i\hat x_i, \qquad x_i\hat z - y_i\hat y_i . $$
--   3. **Edges** ($v$ slices): for each vertex $i$, the bilinear form
--   $$ \sum_{j:\{i,j\}\in E} \big( x_i\hat x_i + x_i\hat x_j + x_j\hat x_j \big). $$
--
--   Setting $\mathbf w = \mathbf v$ in blocks 2 and 3 gives exactly the $4v$ polynomials of the color encoding $C_G$ of Definition 2.9.
--
--   This is the instance that the reduction of Theorem 3.7 produces from a graph.
--
--   **Formalization Note** The paper does not print the matrices of blocks 2 and 3; it only requires that their vanishing, together with the minors, encodes $C_G$. The bilinearizations above are one such choice, recorded here as the mission's construction; any choice with $\mathbf v^\top A_s\mathbf v$ equal to the printed polynomial serves the proof. The slice index set is the disjoint union of the pairs $\{(a,b) : a < b\}$ in `Fin (2v+1)`, of `Fin 3 × Fin v`, and of `Fin v`, in this order, so its cardinality is $v(2v+1) + 3v + v = v(2v+5)$. Rows and columns are indexed by `Fin (2v+1)` with the coordinate order of Definition 2.9 (0-based).
-- source:
--   Hillar & Lim, Most Tensor Problems Are NP-Hard, J. ACM 60(6) (2013), Art. 45 (final version, arXiv:0911.1393v5), p. 0:17, proof of Theorem 3.7

import Mathlib
import Definitions.Def_TensorNP_Bilinear_ColorEncoding

namespace TensorNP.Bilinear

/-! # The tensor `A_G` of the proof of Theorem 3.7 (Hillar–Lim, p. 0:17)

`A_G` has `l = v(2v+5)` slices `A_i ∈ ℤ^{(2v+1)×(2v+1)}`, in three blocks:
`v(2v+1)` slices for the 2×2 minors of `[v w]`, `3v` slices bilinearizing the first `3v`
polynomials of `C_G`, and `v` slices bilinearizing its `v` edge polynomials. -/

/-- The pairs `(a, b)` of row indices of the `(2v+1) × 2` matrix `[v w]` with `a < b`; there are
`(2v+1)·2v/2 = v(2v+1)` of them. -/
abbrev MinorIdx (N : ℕ) : Type := {p : Fin N × Fin N // p.1 < p.2}

/-- The slice index set of `A_G`: the `v(2v+1)` minors, then the `3v` cube-root slices
(a kind in `Fin 3` and a vertex), then the `v` edge slices (a vertex). Its cardinality is
`v(2v+1) + 3v + v = v(2v+5)`. -/
abbrev SliceIdx (v : ℕ) : Type := MinorIdx (2 * v + 1) ⊕ (Fin 3 × Fin v) ⊕ Fin v

/-- The matrix of the 2×2 minor of rows `a < b` of `[v w]`: `vᵀ M w = v_a w_b − v_b w_a`.
Entries are in `{−1, 0, 1}`. -/
def minorSlice {N : ℕ} (ab : MinorIdx N) (p q : Fin N) : ℤ :=
  (if p = ab.1.1 ∧ q = ab.1.2 then 1 else 0) - (if p = ab.1.2 ∧ q = ab.1.1 then 1 else 0)

/-- The matrix with a single `1` in position `(a, b)`. -/
def unitMat {N : ℕ} (a b : Fin N) (p q : Fin N) : ℤ := if p = a ∧ q = b then 1 else 0

open Classical in
/-- The tensor `A_G` (proof of Theorem 3.7), `a_{sjk} = A_s(j,k)`. With
`v = (x, y, z)` and `w = (x̂, ŷ, ẑ)`, the chosen bilinearizations are
* minors: `vᵀ A_{(a,b)} w = v_a w_b − v_b w_a`;
* cube slices for vertex `i`: `x_i ŷ_i − z ẑ`, `y_i ẑ − x_i x̂_i`, `x_i ẑ − y_i ŷ_i`;
* edge slice for vertex `i`: `Σ_{j : {i,j} ∈ E} (x_i x̂_i + x_i x̂_j + x_j x̂_j)`;
so that `vᵀ A_s v` is the corresponding polynomial of `C_G` for the last two blocks. -/
noncomputable def AG {v : ℕ} (G : SimpleGraph (Fin v)) :
    SliceIdx v → Fin (2 * v + 1) → Fin (2 * v + 1) → ℤ
  | .inl ab => minorSlice ab
  | .inr (.inl (c, i)) =>
      match c with
      | 0 => fun p q => unitMat (xIdx i) (yIdx i) p q - unitMat (zIdx v) (zIdx v) p q
      | 1 => fun p q => unitMat (yIdx i) (zIdx v) p q - unitMat (xIdx i) (xIdx i) p q
      | 2 => fun p q => unitMat (xIdx i) (zIdx v) p q - unitMat (yIdx i) (yIdx i) p q
  | .inr (.inr i) => fun p q => ∑ j : Fin v, if G.Adj i j then
      unitMat (xIdx i) (xIdx i) p q + unitMat (xIdx i) (xIdx j) p q +
        unitMat (xIdx j) (xIdx j) p q else 0

end TensorNP.Bilinear


