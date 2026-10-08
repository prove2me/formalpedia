-- Prove2me | Definitions.Def_TensorNP_Bilinear_ColorEncoding
-- name    : TensorNP_Bilinear_ColorEncoding
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T18:05:03.463985+00:00
-- url     : https://prove2.me/theorems/4c87ffb5-beea-4a7c-8d27-bd335f5e8d0d
-- title:
--   Definition 2.9 — the color encoding $C_G$ of a graph
-- statement:
--   Let $G = (V, E)$ be a simple graph on the vertex set $V = \{1,\dots,v\}$. The **color encoding** of $G$ (Definition 2.9) is the set of $4v$ quadratic polynomials in the $2v+1$ unknowns $x_1,\dots,x_v,y_1,\dots,y_v,z$:
--   $$
--   C_G := \begin{cases} x_i y_i - z^2,\quad y_i z - x_i^2,\quad x_i z - y_i^2, & i = 1,\dots,v,\\[2pt] \displaystyle\sum_{j:\{i,j\}\in E} \big(x_i^2 + x_i x_j + x_j^2\big), & i = 1,\dots,v. \end{cases} \tag{8}
--   $$
--   The first $3v$ polynomials force each $x_i$ to be a cube root of unity once $z$ is normalized to $1$, and the last $v$ ones say that adjacent vertices receive different cube roots. The polynomials are evaluated at a point $p = (x_1,\dots,x_v,y_1,\dots,y_v,z)$ with coordinates in a commutative ring $F$.
--
--   This is the encoding of graph 3-colorability into polynomial systems that the reduction of Theorem 3.7 bilinearizes.
--
--   **Formalization Note** A point is `p : Fin (2v+1) → F` with the coordinates in the order of the paper: $x_i$ at position $i-1$ (`xIdx`), $y_i$ at position $v+i-1$ (`yIdx`), $z$ at position $2v$ (`zIdx`). The polynomials are indexed by a kind `c : Fin 4` (the three cube-root polynomials, then the edge polynomial) and a vertex `i : Fin v`, and are represented by their evaluation functions. The sum over $\{i,j\}\in E$ is the sum over the vertices $j$ adjacent to $i$.
-- source:
--   Hillar & Lim, Most Tensor Problems Are NP-Hard, J. ACM 60(6) (2013), Art. 45 (final version, arXiv:0911.1393v5), p. 0:14, Definition 2.9, (8)

import Mathlib

namespace TensorNP.Bilinear

/-! # The color encoding `C_G` of a graph (Hillar–Lim, Definition 2.9, p. 0:14)

The `2v + 1` unknowns `x_1, …, x_v, y_1, …, y_v, z` are the coordinates of a vector
`p : Fin (2v+1) → F`, in this order: `x_i` is coordinate `i - 1`, `y_i` is coordinate `v + i - 1`
and `z` is coordinate `2v` (0-based). -/

/-- Position of the unknown `x_i` (0-based `i`) in `Fin (2v+1)`. -/
def xIdx {v : ℕ} (i : Fin v) : Fin (2 * v + 1) := ⟨i.val, by have := i.isLt; omega⟩

/-- Position of the unknown `y_i` (0-based `i`) in `Fin (2v+1)`. -/
def yIdx {v : ℕ} (i : Fin v) : Fin (2 * v + 1) := ⟨v + i.val, by have := i.isLt; omega⟩

/-- Position of the unknown `z` in `Fin (2v+1)`. -/
def zIdx (v : ℕ) : Fin (2 * v + 1) := ⟨2 * v, by omega⟩

open Classical in
/-- The color encoding `C_G` (8) of a simple graph `G` on the vertices `Fin v`: the `4v`
quadratic polynomials, as functions of the point `p = (x, y, z) ∈ F^{2v+1}`, indexed by a kind
`c ∈ {0,1,2,3}` and a vertex `i`:
* `c = 0`: `x_i y_i − z²`;
* `c = 1`: `y_i z − x_i²`;
* `c = 2`: `x_i z − y_i²`;
* `c = 3`: `Σ_{j : {i,j} ∈ E} (x_i² + x_i x_j + x_j²)`. -/
noncomputable def colorEncoding {v : ℕ} (G : SimpleGraph (Fin v)) {F : Type*} [CommRing F]
    (c : Fin 4) (i : Fin v) (p : Fin (2 * v + 1) → F) : F :=
  match c with
  | 0 => p (xIdx i) * p (yIdx i) - p (zIdx v) ^ 2
  | 1 => p (yIdx i) * p (zIdx v) - p (xIdx i) ^ 2
  | 2 => p (xIdx i) * p (zIdx v) - p (yIdx i) ^ 2
  | 3 => ∑ j : Fin v, if G.Adj i j then
      p (xIdx i) ^ 2 + p (xIdx i) * p (xIdx j) + p (xIdx j) ^ 2 else 0

end TensorNP.Bilinear


