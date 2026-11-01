-- Prove2me | Definitions.Def_VRAccelCLT_accelBlock
-- name    : VRAccelCLT_accelBlock
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:20:11.665919+00:00
-- url     : https://prove2.me/theorems/e5284f97-380d-4993-bd59-88409d85e1aa
-- title:
--   The block matrix $H_2$ of the proof of Theorem 2
-- statement:
--   For $\alpha,\beta\in\mathbb R$ and $H\in\mathbb R^{m\times m}$ define the $2m\times 2m$ matrix
--
--   $$
--   H_2=\begin{pmatrix}(1+\beta)(I_m-\alpha H) & -\beta(I_m-\alpha H)\\ I_m & 0_m\end{pmatrix}.
--   $$
--
--   It is the linear part of the recursion (44) satisfied by the stacked error $z_{k+1}=(y_{k+1}-x^*;\,y_k-x^*)$ of Algorithm 2.
--
--   **Formalization Note** Indices of $\mathbb R^{2m}$ are the disjoint union of two copies of $\{1,\dots,m\}$, the first copy being the first block.
-- source:
--   Lei, Shanbhag, Variance-Reduced Accelerated First-order Methods: Central Limit Theorems and Confidence Statements, arXiv:2006.07769v3, proof of Theorem 2, p.19

import Mathlib

namespace VRAccelCLT

/-- **The block matrix `H₂`** of the proof of Theorem 2. Lei, Shanbhag, arXiv:2006.07769v3, proof
of Theorem 2, p.19: "H2 ≜ ((1 + β)(Im − αH)  −β(Im − αH) ; Im  0m)".

`accelBlock α β H` is the `2m × 2m` matrix with blocks `(1+β)(I − αH)`, `−β(I − αH)` in the first
block row and `I`, `0` in the second.

**Formalization Note.** The index type is `Fin m ⊕ Fin m` (first summand = first block),
assembled with `Matrix.fromBlocks`. -/
def accelBlock {m : ℕ} (α β : ℝ) (H : Matrix (Fin m) (Fin m) ℝ) :
    Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ :=
  Matrix.fromBlocks ((1 + β) • (1 - α • H)) (-(β • (1 - α • H))) 1 0

end VRAccelCLT


