-- Prove2me | Definitions.Def_TensorNP_Eigen_Construction
-- name    : TensorNP_Eigen_Construction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T17:07:10.600328+00:00
-- url     : https://prove2.me/theorems/96f64527-d545-48dc-877c-b505c4bbf37a
-- title:
--   Definition 2.9, Lemmas 2.7–2.8, proof of Theorem 1.3 — the color encoding $C_G$ and the tensor $T_G$
-- statement:
--   The constructions of Hillar and Lim's reduction from graph 3-colorability to tensor $0$-eigenvalue. A homogeneous quadratic polynomial $p$ in unknowns $\mathbf w$ is stored as a matrix $M$ with $p(\mathbf w)=\mathbf w^\top M\mathbf w$; the monomial $w_aw_b$ is the matrix unit $E_{ab}$.
--
--   **Color encoding (Definition 2.9).** For a simple graph $G=(V,E)$ with vertices $1,\dots,v$, the color encoding $C_G$ is the family of $4v$ quadratic polynomials in the $2v+1$ unknowns $x_1,\dots,x_v,y_1,\dots,y_v,z$ (in this order):
--
--   $$C_G:=\Big\{\,x_iy_i-z^2,\;\; y_iz-x_i^2,\;\; x_iz-y_i^2,\;\; \sum_{j:\{i,j\}\in E}\big(x_i^2+x_ix_j+x_j^2\big)\;:\; i=1,\dots,v\Big\}.$$
--
--   A vertex without neighbours contributes the zero polynomial as its fourth polynomial. In the list form the polynomials are numbered so that number $4(i-1)+f$ (0-based) is family $f\in\{0,1,2,3\}$ of vertex $i$.
--
--   **Realification (Lemma 2.7).** From $m$ matrices $A_i\in R^{n\times n}$ it forms the $2m$ matrices of size $2n\times 2n$
--
--   $$B_i=\begin{bmatrix}A_i&0\\0&-A_i\end{bmatrix},\qquad B_{m+i}=\begin{bmatrix}0&A_i\\A_i&0\end{bmatrix},\qquad i=1,\dots,m,$$
--
--   acting on $\mathbf x=[\mathbf u^\top,\mathbf v^\top]^\top$.
--
--   **Padding (Lemma 2.8).** From $m$ matrices $A_i\in R^{n\times n}$ and sizes $r,s$ it forms the $r$ matrices of size $s\times s$
--
--   $$B_i=\begin{bmatrix}A_i&0\\0&0\end{bmatrix}\ (i\le m),\qquad B_j=0\ (m<j<r),\qquad B_r=\begin{bmatrix}0&0\\0&I_{s-n}\end{bmatrix}.$$
--
--   It is meant for $r\ge m+1$ and $s\ge n$, the hypotheses of Lemma 2.8.
--
--   **The square system and the tensor $T_G$.** Applying realification to $C_G$ gives $8v$ real equations in $4v+2$ unknowns. Padding with $r=s=N:=8v+2$ gives a square system $B_1,\dots,B_N$ of $N\times N$ integer matrices. The tensor of the reduction is
--
--   $$T_G=[\![a_{ijk}]\!]\in\mathbb Q^{N\times N\times N},\qquad a_{ijk}=(B_k)_{ij}.$$
--
--   Its entries are integers (the coefficient of $x_i^2$ in the fourth family is the degree of $i$).
--
--   **Formalization Note** Indices are 0-based. The size $N=8v+2$ satisfies both bounds of Lemma 2.8 for every $v\ge 0$ ($8v+1$ would fail at $v=0$, where $4v+2=2$); Example 1.4 uses a different count, and any size meeting Lemma 2.8's bounds is equally faithful. The realified and padded systems are reindexed onto `Fin` by `finSumFinEquiv`, which lists the first block first. The padding function is total: for $r<m+1$ it still returns a family, but every statement about it assumes $r\ge m+1$, $s\ge n$.
-- source:
--   Hillar & Lim, Most Tensor Problems Are NP-Hard, J. ACM 60(6) (2013), Art. 45 (final version, arXiv:0911.1393v5), p. 0:14, Definition 2.9 (8), Lemmas 2.7 and 2.8; p. 0:17, proof of Theorem 3.8; p. 0:20, proof of Theorem 1.3; pp. 0:7–0:8, Example 1.4

import Mathlib
import Definitions.Def_TensorNP_Eigen_Defs

namespace TensorNP.Eigen

/-! # The reduction of Theorem 1.3: color encoding, realification, padding, the tensor `T_G`

Hillar & Lim, *Most Tensor Problems Are NP-Hard*, J. ACM 60(6) (2013): Definition 2.9 (p. 0:14),
Lemmas 2.7 and 2.8 (p. 0:14), proof of Theorem 3.8 (p. 0:17), proof of Theorem 1.3 (p. 0:20).

A homogeneous quadratic polynomial is stored as a (not necessarily symmetric) matrix `M` with
`xᵀ M x` equal to the polynomial; the monomial `x_a x_b` is `Matrix.single a b 1`. Indices are
0-based. -/

open Matrix Finset

section ColorEncoding

variable {v : ℕ}

/-- The unknown `x_i` (paper's `x_{i+1}`) among the `2v + 1` unknowns
`x_1, …, x_v, y_1, …, y_v, z`, which are numbered `0, …, 2v` in this order. -/
def xVar (i : Fin v) : Fin (2 * v + 1) := ⟨i, by omega⟩

/-- The unknown `y_i` (paper's `y_{i+1}`), at position `v + i`. -/
def yVar (i : Fin v) : Fin (2 * v + 1) := ⟨v + i, by omega⟩

/-- The unknown `z`, at the last position `2v`. -/
def zVar : Fin (2 * v + 1) := ⟨2 * v, by omega⟩

open Classical in
/-- Definition 2.9, eq. (8): the color encoding `C_G` of a simple graph `G` on `v` vertices, the
`4v` quadratic polynomials in the `2v + 1` unknowns `x_1, …, x_v, y_1, …, y_v, z`, indexed by
`(family, vertex)`:
* family `0`: `x_i y_i − z²`;
* family `1`: `y_i z − x_i²`;
* family `2`: `x_i z − y_i²`;
* family `3`: `∑_{j : {i,j} ∈ E} (x_i² + x_i x_j + x_j²)` (a vertex without neighbours gives the
  zero polynomial).
Each polynomial `p` is the rational matrix `M` with `p(w) = wᵀ M w`. -/
noncomputable def colorEncoding (G : SimpleGraph (Fin v)) :
    Fin 4 × Fin v → Matrix (Fin (2 * v + 1)) (Fin (2 * v + 1)) ℚ :=
  fun p =>
    ![single (xVar p.2) (yVar p.2) 1 - single zVar zVar 1,
      single (yVar p.2) zVar 1 - single (xVar p.2) (xVar p.2) 1,
      single (xVar p.2) zVar 1 - single (yVar p.2) (yVar p.2) 1,
      ∑ j ∈ univ.filter (G.Adj p.2),
        (single (xVar p.2) (xVar p.2) 1 + single (xVar p.2) (xVar j) 1
          + single (xVar j) (xVar j) 1)] p.1

/-- `C_G` as a list of `4v` matrices `A_1, …, A_{4v}` (polynomial number `4i + f`, 0-based, is
family `f` of vertex `i`, via `finProdFinEquiv`). -/
noncomputable def colorEncodingFin (G : SimpleGraph (Fin v)) :
    Fin (4 * v) → Matrix (Fin (2 * v + 1)) (Fin (2 * v + 1)) ℚ :=
  fun k => colorEncoding G (finProdFinEquiv.symm k)

end ColorEncoding

/-- Lemma 2.7: from `m` matrices `A_i ∈ R^{n×n}`, the `2m` matrices of size `2n × 2n`
`B_i = [A_i 0; 0 −A_i]` and `B_{m+i} = [0 A_i; A_i 0]` (`i = 1, …, m`). The first `m` outputs
are the `B_i` and the last `m` the `B_{m+i}`; the unknowns `x = [uᵀ, vᵀ]ᵀ` list `u` first. -/
def realSplit {R : Type} [CommRing R] {m n : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) R) :
    Fin (m + m) → Matrix (Fin (n + n)) (Fin (n + n)) R :=
  fun j => Matrix.reindex finSumFinEquiv finSumFinEquiv
    (Sum.elim (fun i => Matrix.fromBlocks (A i) 0 0 (-A i))
      (fun i => Matrix.fromBlocks 0 (A i) (A i) 0) (finSumFinEquiv.symm j))

/-- Lemma 2.8: from `m` matrices `A_i ∈ R^{n×n}`, the `r` matrices of size `s × s`
`B_i = [A_i 0; 0 0]` (`i = 1, …, m`), `B_j = 0` (`j = m + 1, …, r − 1`) and `B_r = [0 0; 0 I]`
with `I` the `(s − n) × (s − n)` identity. Meant for `r ≥ m + 1` and `s ≥ n`, the hypotheses of
Lemma 2.8; in 0-based indices `B_r` is number `r − 1`. -/
def padSystem {R : Type} [Zero R] [One R] {m n : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) R)
    (r s : ℕ) : Fin r → Matrix (Fin s) (Fin s) R :=
  fun k a b =>
    if hk : (k : ℕ) < m then
      (if h : (a : ℕ) < n ∧ (b : ℕ) < n then A ⟨k, hk⟩ ⟨a, h.1⟩ ⟨b, h.2⟩ else 0)
    else if (k : ℕ) + 1 = r then (if n ≤ (a : ℕ) ∧ a = b then 1 else 0)
    else 0

/-- The size `N = 8v + 2` of the square system built from a graph on `v` vertices: Lemma 2.7
turns the `4v` polynomials of `C_G` in `2v + 1` unknowns into `8v` real equations in `4v + 2`
unknowns, and Lemma 2.8 needs `r ≥ 8v + 1` and `s ≥ 4v + 2`; `8v + 2` satisfies both for every
`v ≥ 0`. -/
def colorSize (v : ℕ) : ℕ := 8 * v + 2

/-- Proof of Theorem 1.3 (with the proof of Theorem 3.8 and Example 1.4): the square system of
`N = 8v + 2` real quadratic equations in `N` unknowns obtained from `C_G` by Lemma 2.7 and then
Lemma 2.8 with `r = s = N`. -/
noncomputable def squareSystem {v : ℕ} (G : SimpleGraph (Fin v)) :
    Fin (colorSize v) → Matrix (Fin (colorSize v)) (Fin (colorSize v)) ℚ :=
  padSystem (realSplit (colorEncodingFin G)) (colorSize v) (colorSize v)

/-- The tensor `T_G = ⟦a_{ijk}⟧ ∈ ℚ^{N×N×N}` of the reduction, `a_{ijk} = (B_k)_{ij}` where
`B_1, …, B_N` is `squareSystem G`; its entries are integers. -/
noncomputable def colorTensor {v : ℕ} (G : SimpleGraph (Fin v)) :
    Fin (colorSize v) → Fin (colorSize v) → Fin (colorSize v) → ℚ :=
  fun i j k => squareSystem G k i j

end TensorNP.Eigen


