-- Prove2me | Definitions.Def_CodedSorting_LinAlg
-- name    : CodedSorting_LinAlg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T23:05:01.008346+00:00
-- url     : https://prove2.me/theorems/c173741d-2c04-4795-93e0-98abf9e7ac22
-- title:
--   Orthogonal complements and projections over $\mathbb Q$, partial swaps, and the matrix $L$
-- statement:
--   Work in $\mathbb Q^m$ with the standard dot product $u\cdot v=\sum_i u_iv_i$.
--
--   1. The **orthogonal complement** of a subspace $U$ is $U^\perp=\{v:\ u\cdot v=0\text{ for all }u\in U\}$.
--   2. A rational $m\times m$ matrix $P$ is the **orthogonal projection** onto $U$ when $P^{\mathsf T}=P$, $P^2=P$ and the column space of $P$ is $U$.
--   3. The **partial swap** of $P$ is the $2m\times 2m$ block matrix acting on address vectors $(H,D)$:
--   $$D_P=\begin{pmatrix}I-P&P\\ P&I-P\end{pmatrix},\qquad D_P\begin{pmatrix}H\\D\end{pmatrix}=\begin{pmatrix}(I-P)H+PD\\ PH+(I-P)D\end{pmatrix}.$$
--   It is also written on $\mathbb Q^{2m}$ with the coordinates of $H$ first.
--   4. For $\xi\in\mathbb Q^{n}$ with first nonzero entry at index $i$ and last nonzero entry at index $j$, put $\nu=\xi^{\mathsf T}\xi$ and $\alpha=-\nu/(2\xi_j)$. The matrix $L$ has columns
--   $$L_i=\xi+\alpha e_j,\quad L_j=\alpha e_j,\quad L_k=e_k-\frac{\xi_k}{\xi_j}e_j\ (i<k<j),\quad L_k=e_k\ \text{otherwise}.$$
--
--   The partial swap turns a projection label into a storage order for a data stream (§6.2), and $L$ factors the partial swap of a rank-one projection into one coordinate exchange, display (17).
--
--   **Formalization Note** Mathlib's orthogonal complement needs a real or complex inner-product space, so the rational one is defined directly. Projections are never constructed; statements quantify over every matrix satisfying the projection conditions, which over $\mathbb Q$ exists and is unique for each subspace.
-- source:
--   B. Li, Z. Li, S. Liu, Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting, arXiv:2610.20079 (held version, sha256 6e149d97…8850b), §5.1, p.11 (PDF 12); §5.2, p.15 (PDF 16); §6.2, display (16), pp.20–21 (PDF 21–22), and the matrix $L$, p.22 (PDF 23)

import Mathlib

namespace CodedSorting

/-! # Rational subspaces, orthogonal projections and partial swaps

arXiv:2610.20079 (held version, sha256 6e149d97…8850b), §5.1 p.11, §5.2 p.15, §6.2 pp.20–22. -/

open Matrix

/-- The orthogonal complement `U^⊥` of a subspace `U ⊆ ℚ^m` for the standard inner product (§5.1,
p.11: "Equip E with the standard inner product. For U ⊆ E, write U^⊥ for its orthogonal
complement").

**Formalization Note.** Mathlib's `Submodule.orthogonal` needs an inner-product space over `ℝ` or
`ℂ`; this is the same definition with the dot product of `ℚ^m`. -/
def perp {m : ℕ} (U : Submodule ℚ (Fin m → ℚ)) : Submodule ℚ (Fin m → ℚ) where
  carrier := {v | ∀ u ∈ U, u ⬝ᵥ v = 0}
  add_mem' := by
    intro a b ha hb u hu
    simp [dotProduct_add, ha u hu, hb u hu]
  zero_mem' := by
    intro u _
    simp
  smul_mem' := by
    intro c v hv u hu
    simp [dotProduct_smul, hv u hu]

/-- `P` is the matrix of the orthogonal projection onto `U`: `P` is symmetric, idempotent, and its
column space (equal to its row space, by symmetry) is `U` (§5.2, p.15: "the orthogonal projection
M_u = P_{U_u}. This is an m × m rational matrix with row space U_u").

**Formalization Note.** Over `ℚ` such a `P` exists and is unique for every `U`, because the dot
product is anisotropic. Statements quantify over all `P` with `IsOrthProj U P` instead of
constructing it. -/
def IsOrthProj {m : ℕ} (U : Submodule ℚ (Fin m → ℚ)) (P : Matrix (Fin m) (Fin m) ℚ) : Prop :=
  Pᵀ = P ∧ P * P = P ∧ LinearMap.range (Matrix.toLin' P) = U

/-- The partial swap `D_P` of display (16), p.21: the `2m × 2m` block matrix
`[[I − P, P], [P, I − P]]` acting on address vectors `(H, D)`, `H` the first block. -/
def psw {m : ℕ} (P : Matrix (Fin m) (Fin m) ℚ) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℚ :=
  Matrix.fromBlocks (1 - P) P P (1 - P)

/-- `psw P` on `Fin (m + m)`, the coordinates of `H` first (indices `0, …, m−1`), then those of `D`
(display (16) as a `2m × 2m` matrix). -/
def pswFlat {m : ℕ} (P : Matrix (Fin m) (Fin m) ℚ) : Matrix (Fin (m + m)) (Fin (m + m)) ℚ :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (psw P)

/-- The lower-triangular matrix `L` of p.22, for `ξ ∈ ℚ^{2m}` with first nonzero entry at `i` and
last nonzero entry at `j`. With `ν = ξᵀξ` and `α = −ν / (2 ξ_j)`, its columns are
`L_i = ξ + α e_j`, `L_j = α e_j`, `L_k = e_k − (ξ_k / ξ_j) e_j` for `i < k < j`, and `L_k = e_k`
for the remaining `k`. The entry in row `a` and column `k` is the `a`-th coordinate of `L_k`. -/
def lowerL {n : ℕ} (ξ : Fin n → ℚ) (i j : Fin n) : Matrix (Fin n) (Fin n) ℚ :=
  let α : ℚ := -(ξ ⬝ᵥ ξ) / (2 * ξ j)
  fun a k =>
    if k = i then ξ a + (if a = j then α else 0)
    else if k = j then (if a = j then α else 0)
    else if i < k ∧ k < j then (if a = k then 1 else 0) - (if a = j then ξ k / ξ j else 0)
    else (if a = k then 1 else 0)

end CodedSorting


