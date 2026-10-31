-- Prove2me | Definitions.Def_LinearZeroSumMG_clip
-- name    : LinearZeroSumMG_clip
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:50:20.293356+00:00
-- url     : https://prove2.me/theorems/a35b0f38-1c2d-438e-a92e-30ecdf74947c
-- title:
--   The clipping $\Pi_H$ and the norms $\|\cdot\|$, $\|\cdot\|_F$, $\|\cdot\|_A$ (§2.1)
-- statement:
--   For a real number $u$ and $H\in\mathbb N$, the **clipping operation** is
--   $$
--   \Pi_H(u)=\max\{\min\{u,H\},-H\}\in[-H,H].
--   $$
--   For $v\in\mathbb R^d$, $\|v\|=\sqrt{v^\top v}$ is the Euclidean norm; for a $d\times d$ matrix $A$, $\|A\|_F=\big(\sum_{i,j}A_{ij}^2\big)^{1/2}$ is the Frobenius norm; and for a positive semidefinite $A$, $\|v\|_A=\sqrt{v^\top A v}$ is the weighted norm.
--
--   These are the notational conventions of the paper, used by the algorithm (clipping of the estimates), by the function class of (5), and by the confidence bonus $\beta\|\phi\|_{\Lambda^{-1}}$.
--
--   **Formalization Note** Vectors of $\mathbb R^d$ are functions `Fin d → ℝ`. The Euclidean norm is the published definition `ApproxVI.euclNorm`, $\sqrt{\sum_i z_i^2}$, written out because the default norm on that type is the sup norm; this module adds $\Pi_H$, $\|\cdot\|_F$ and $\|\cdot\|_A$. The square root is `Real.sqrt`, which is $0$ on negative numbers; it is applied only to positive semidefinite forms in this mission.
-- source:
--   Xie, Chen, Wang & Yang, Learning Zero-Sum Simultaneous-Move Markov Games Using Function Approximation and Correlated Equilibrium, arXiv:2002.07066v3, §2.1 (Notation), p.5

import Mathlib
import Definitions.Def_ApproxVI_euclNorm

namespace LinearZeroSumMG

open Matrix

/-- **The clipping operation `Π_H` and the vector norms of §2.1.**
Xie, Chen, Wang & Yang, *Learning Zero-Sum Simultaneous-Move Markov Games Using Function
Approximation and Correlated Equilibrium*, arXiv:2002.07066v3, §2.1 (Notation), p.5:
"For each real number `u`, define the clipping operation `Π_H(u) = max{min{u, H}, −H}`. We use `‖·‖`
to denote the vector `ℓ₂` norm and `‖·‖_F` the matrix Frobenius norm. Given a positive semidefinite
matrix `A`, define the weighted `ℓ₂` norm `‖v‖_A := √(vᵀAv)`."

This module holds `clip` (`Π_H`) and the norms `frobNorm` (`‖·‖_F`) and `wNorm` (`‖·‖_A`). The
vector norm `‖·‖` is the published `ApproxVI.euclNorm`, `‖z‖ = √(∑ᵢ zᵢ²)` on `Fin d → ℝ`.

**Formalization Note** Vectors of `ℝ^d` are `Fin d → ℝ` and matrices are functions
`Fin d → Fin d → ℝ` (read as `Matrix (Fin d) (Fin d) ℝ` through `Matrix.of`). The `ℓ₂` norm is
written out (`ApproxVI.euclNorm`), because the norm Mathlib puts on `Fin d → ℝ` is the sup norm. In `wNorm`
the square root is `Real.sqrt`, which is `0` on negative numbers; it is applied in this mission only
to positive semidefinite matrices (inverses of Gram matrices). -/
noncomputable def clip (H : ℕ) (u : ℝ) : ℝ := max (min u (H : ℝ)) (-(H : ℝ))

/-- The Frobenius norm `‖A‖_F = √(∑ᵢⱼ Aᵢⱼ²)` of a `d × d` matrix (arXiv:2002.07066v3, §2.1, p.5). -/
noncomputable def frobNorm {d : ℕ} (A : Fin d → Fin d → ℝ) : ℝ :=
  Real.sqrt (∑ i, ∑ j, A i j ^ 2)

/-- The weighted norm `‖v‖_A = √(vᵀ A v)` (arXiv:2002.07066v3, §2.1, p.5). -/
noncomputable def wNorm {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (v : Fin d → ℝ) : ℝ :=
  Real.sqrt (v ⬝ᵥ A *ᵥ v)

end LinearZeroSumMG


