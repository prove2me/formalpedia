-- Prove2me | Definitions.Def_SmoothBerr_blockView
-- name    : SmoothBerr_blockView
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:27:04.306918+00:00
-- url     : https://prove2.me/theorems/27235af2-752f-4ef0-a017-abd502ee01bb
-- title:
--   $2\times2$ block view of an $n\times n$ matrix with blocks $t$ and $n-t$
-- statement:
--   For $t\le n$, split the index set $\{1,\dots,n\}$ into the first $t$ indices and the last $n-t$ indices. The **block view** of $M\in\mathbb R^{n\times n}$ is the same matrix written as
--   $$
--   M=\begin{bmatrix}M_{11}&M_{12}\\ M_{21}&M_{22}\end{bmatrix},\qquad
--   M_{11}\in\mathbb R^{t\times t},\ M_{12}\in\mathbb R^{t\times(n-t)},\ M_{21}\in\mathbb R^{(n-t)\times t},\ M_{22}\in\mathbb R^{(n-t)\times(n-t)}.
--   $$
--   The hidden Gaussian theorem (Theorem 5.1) states that $R^\top AS$ has this shape with a Gaussian lower-right block.
--
--   **Formalization Note** The splitting is `Fin n ≃ Fin t ⊕ Fin (n - t)`, and the four blocks are read with Mathlib's `toBlocks₁₁`, `toBlocks₁₂`, `toBlocks₂₁`, `toBlocks₂₂`.
-- source:
--   Dereziński, Mahoney, Meyer, Musco, From smoothed analysis to backward error: The power of adaptive perturbations (manuscript of 3 Nov 2026, STOC 2027 submission; sha256 9575cd20bc2c854eb092a4950988f7fbef8715adda344a1ba39489bc28b4e58d), Theorem 5.1, p.9 (R^⊤AS = [B_11 B_12; B_21 G])

import Mathlib

namespace SmoothBerr

/-- The splitting `{0,…,n−1} ≃ {0,…,t−1} ⊔ {0,…,n−t−1}` of the index set of an `n × n` matrix into
its first `t` and its last `n − t` indices (for `t ≤ n`). -/
def splitEquiv {n t : ℕ} (h : t ≤ n) : Fin n ≃ Fin t ⊕ Fin (n - t) :=
  (finCongr (by omega : n = t + (n - t))).trans finSumFinEquiv.symm

/-- The `2 × 2` block view of an `n × n` matrix with blocks of sizes `t` and `n − t` (Dereziński,
Mahoney, Meyer, Musco, *From smoothed analysis to backward error: The power of adaptive
perturbations*, manuscript of 3 Nov 2026, sha256 9575cd20…, Theorem 5.1, p.9:
`R^⊤AS = [B_11 B_12; B_21 G]` with `B_11 ∈ ℝ^{t×t}`, `B_12 ∈ ℝ^{t×(n−t)}`, `B_21 ∈ ℝ^{(n−t)×t}`,
`G ∈ ℝ^{(n−t)×(n−t)}`).

**Formalization Note** `(blockView h M).toBlocks₁₁` is the upper-left `t × t` block (rows and
columns `0, …, t−1`), `toBlocks₁₂`, `toBlocks₂₁` the off-diagonal blocks, and `toBlocks₂₂` the
lower-right `(n − t) × (n − t)` block. -/
def blockView {n t : ℕ} (h : t ≤ n) (M : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin t ⊕ Fin (n - t)) (Fin t ⊕ Fin (n - t)) ℝ :=
  Matrix.reindex (splitEquiv h) (splitEquiv h) M

end SmoothBerr


