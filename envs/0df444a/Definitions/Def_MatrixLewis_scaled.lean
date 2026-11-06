-- Prove2me | Definitions.Def_MatrixLewis_scaled
-- name    : MatrixLewis_scaled
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:06:19.475416+00:00
-- url     : https://prove2.me/theorems/86e15dad-050c-48e7-b7e9-fa18ba634ddc
-- title:
--   Scaled constraint matrices $B_i(S)=S^{-1/2}A_iS^{-1/2}$ and scaled direction $X_S(h)$
-- statement:
--   At a slack $S\succ0$, the **scaled constraint matrices** are
--   $$
--   B_i(S):=S^{-1/2}A_iS^{-1/2},\qquad i=1,\dots,m,
--   $$
--   and the **scaled direction** of $h\in\mathbb R^m$ is $X_S(h):=\sum_i h_iB_i(S)=S^{-1/2}(\mathcal Ah)S^{-1/2}$. The $B_i(S)$ span the subspace $\mathcal L_S=S^{-1/2}\mathcal L S^{-1/2}$.
-- source:
--   Kelner, Jiang, Sidford, Zhang, Matrix Lewis Weights: Solving Semidefinite Programs in Square Root Constraints Iterations, STOC 2027 submission (manuscript sha256 31ce765b…), §3.1, p.15

import Mathlib
import Definitions.Def_MatrixLewis_mpow

namespace MatrixLewis

/-- The scaled constraint matrices `Bᵢ(S) := S^{−1/2} Aᵢ S^{−1/2}` at a slack `S ≻ 0`
(Kelner–Jiang–Sidford–Zhang, *Matrix Lewis Weights: Solving Semidefinite Programs in Square Root Constraints Iterations*, STOC 2027 submission (manuscript sha256 31ce765b…), §3.1, p.15). `S^{−1/2}` is `mpow (−1/2) S`. -/
noncomputable def scaled {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (S : Matrix (Fin n) (Fin n) ℝ) (i : Fin m) : Matrix (Fin n) (Fin n) ℝ :=
  mpow (-(1 / 2 : ℝ)) S * A i * mpow (-(1 / 2 : ℝ)) S

/-- The scaled direction `X_S(h) := ∑ᵢ hᵢ Bᵢ(S) = S^{−1/2}(𝒜h)S^{−1/2}` of `h ∈ ℝᵐ`
(Kelner–Jiang–Sidford–Zhang, *Matrix Lewis Weights: Solving Semidefinite Programs in Square Root Constraints Iterations*, STOC 2027 submission (manuscript sha256 31ce765b…), §3.1, p.15). -/
noncomputable def scaledDir {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (S : Matrix (Fin n) (Fin n) ℝ) (h : EuclideanSpace ℝ (Fin m)) : Matrix (Fin n) (Fin n) ℝ :=
  ∑ i, h i • scaled A S i

end MatrixLewis


