-- Prove2me | Definitions.Def_MatrixLewis_dilation
-- name    : MatrixLewis_dilation
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:13:10.964214+00:00
-- url     : https://prove2.me/theorems/2965762c-1883-402d-ad9b-bafb3a47c84f
-- title:
--   Symmetric dilation $\hat T$, direction $\hat X$ and power trace $\chi$
-- statement:
--   With $T$, $X$ and $\Xi$ as in Lemma 3.16, on $\mathbb R^n\oplus(\mathbb R^m\otimes\mathbb R^n)$ define
--   $$
--   \hat T=\begin{pmatrix}0&T^\top\\ T&0\end{pmatrix},\qquad
--   \hat X=\begin{pmatrix}-X&0\\0&2\Xi\end{pmatrix},\qquad
--   \chi(t)=\operatorname{tr}\bigl|e^{t\hat X/2}\hat Te^{t\hat X/2}\bigr|^q .
--   $$
--
--   **Formalization Note** $\mathbb R^n\oplus(\mathbb R^m\otimes\mathbb R^n)$ is indexed by the disjoint union of $\{1..n\}$ and $\{1..m\}\times\{1..n\}$ (`Matrix.fromBlocks`).
-- source:
--   Kelner, Jiang, Sidford, Zhang, Matrix Lewis Weights: Solving Semidefinite Programs in Square Root Constraints Iterations, STOC 2027 submission (manuscript sha256 31ce765b…), Lemma 3.20, p.33

import Mathlib
import Definitions.Def_MatrixLewis_expCurve

namespace MatrixLewis

/-- The symmetric dilation `T̂ = [[0, Tᵀ], [T, 0]]` of the row operator `T` of the `Bᵢ(I)`, on
`ℝⁿ ⊕ (ℝᵐ ⊗ ℝⁿ)` (Kelner–Jiang–Sidford–Zhang, *Matrix Lewis Weights: Solving Semidefinite Programs in Square Root Constraints Iterations*, STOC 2027 submission (manuscript sha256 31ce765b…), Lemma 3.20, p.33), indexed by `Fin n ⊕ (Fin m × Fin n)`. -/
def dilT {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n ⊕ (Fin m × Fin n)) (Fin n ⊕ (Fin m × Fin n)) ℝ :=
  Matrix.fromBlocks 0 (rowOp A).transpose (rowOp A) 0

/-- The block-diagonal direction `X̂ = [[−X, 0], [0, 2Ξ]]` on `ℝⁿ ⊕ (ℝᵐ ⊗ ℝⁿ)` (Kelner–Jiang–Sidford–Zhang, *Matrix Lewis Weights: Solving Semidefinite Programs in Square Root Constraints Iterations*, STOC 2027 submission (manuscript sha256 31ce765b…),
Lemma 3.20, p.33). -/
noncomputable def dilX {n m : ℕ} (q : ℝ) (A : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (X : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n ⊕ (Fin m × Fin n)) (Fin n ⊕ (Fin m × Fin n)) ℝ :=
  Matrix.fromBlocks (-X) 0 0 ((2 : ℝ) • xiGen q A X)

/-- The power trace along the congruence curve, `χ(t) = tr |e^{tX̂/2} T̂ e^{tX̂/2}|^q` (Kelner–Jiang–Sidford–Zhang, *Matrix Lewis Weights: Solving Semidefinite Programs in Square Root Constraints Iterations*, STOC 2027 submission (manuscript sha256 31ce765b…),
Lemma 3.20, p.33), with `T̂` the dilation of the row operator of the `Bᵢ(I)`. -/
noncomputable def chiDil {n m : ℕ} (q : ℝ) (A : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (X : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) : ℝ :=
  (mabsPow q (mexp ((t / 2) • dilX q A X) * dilT (scaled A 1) *
    mexp ((t / 2) • dilX q A X))).trace

end MatrixLewis


