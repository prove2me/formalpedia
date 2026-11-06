-- Prove2me | Definitions.Def_RandomLPIPM_gaussProj
-- name    : RandomLPIPM_gaussProj
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:06:12.406767+00:00
-- url     : https://prove2.me/theorems/c51bc1d3-d9e1-4d98-9546-dd3bf754b7fb
-- title:
--   Gaussian projection $\Pi=T^{1/2}G^\top(GTG^\top)^{-1}GT^{1/2}$
-- statement:
--   For a positive semidefinite $T\in\mathbb R^{N\times N}$ and $G\in\mathbb R^{m\times N}$,
--   $$\Pi=T^{1/2}G^\top(GTG^\top)^{-1}GT^{1/2},$$
--   where $T^{1/2}$ is the positive semidefinite square root. When $GTG^\top$ is invertible, $\Pi$ is the orthogonal projection onto the row space of $GT^{1/2}$.
--
--   **Formalization Note** Lean's matrix inverse is total, so $\Pi=0$ on the null event that $GTG^\top$ is singular.
-- source:
--   Dadush–Jiang–Kyng–Ma, Interior Point Methods Solve Random LPs in polylog(n) iterations, STOC 2027 submission (manuscript sha256 a8a320f9…), Theorem 5.1, p.33; Theorem 2.7, p.14

import Mathlib

open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator

namespace RandomLPIPM

/-- **The Gaussian projection `Π = T^{1/2}Gᵀ(GTGᵀ)⁻¹GT^{1/2}`.** Dadush–Jiang–Kyng–Ma, *Interior Point Methods Solve Random LPs in polylog(n) iterations*, STOC 2027 submission (manuscript sha256 a8a320f9…), Theorem 5.1, p.33 (and
Theorem 2.7, p.14), for `T ⪰ 0` of size `N × N` and `G ∈ ℝ^{m×N}`.

**Formalization Note.** `T^{1/2}` is the positive semidefinite square root (`CFC.sqrt` with the
matrix order). Mathlib's matrix inverse is total, so `Π = 0` on the null event that `GTGᵀ` is
singular. -/
noncomputable def gaussProj {m N : ℕ} (T : Matrix (Fin N) (Fin N) ℝ)
    (G : Matrix (Fin m) (Fin N) ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  CFC.sqrt T * Gᵀ * (G * T * Gᵀ)⁻¹ * G * CFC.sqrt T

end RandomLPIPM


