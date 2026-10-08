-- Prove2me | Definitions.Def_WassKF_Bisect_gradF
-- name    : WassKF_Bisect_gradF
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T22:08:57.580066+00:00
-- url     : https://prove2.me/theorems/e1e7cb84-3441-48b4-bae9-ead5b500b41c
-- title:
--   Algorithm 2 and (A.11), pp. 6, 14 — the gradient D = ∇f(S) = [I_n, −G]ᵀ[I_n, −G] with G = S_xy S_yy⁻¹
-- statement:
--   Let $d = n + m$ and write a symmetric matrix $S \in \mathbb{S}^d$ in blocks
--   $$
--   S = \begin{bmatrix} S_{xx} & S_{xy} \\ S_{yx} & S_{yy} \end{bmatrix},\qquad S_{xx}\in\mathbb{R}^{n\times n},\ S_{yy}\in\mathbb{R}^{m\times m}.
--   $$
--   The objective of the robust estimation program (5) is $f(S) = \mathrm{Tr}\big[S_{xx} - S_{xy}S_{yy}^{-1}S_{yx}\big]$. Its gradient is the matrix
--   $$
--   D = \nabla f(S) = \begin{bmatrix} I_n & -G \end{bmatrix}^{\top}\begin{bmatrix} I_n & -G \end{bmatrix} = \begin{bmatrix} I_n & -G \\ -G^{\top} & G^{\top}G \end{bmatrix},\qquad G = S_{xy}S_{yy}^{-1},
--   $$
--   which is the closed form Algorithm 2 uses to feed the bisection Algorithm 1. Being of the form $B^\top B$, $D$ is always positive semidefinite, and its upper-left block is $I_n$, so $D \neq 0$ whenever $n \ge 1$.
--
--   **Formalization Note** The index set is `Fin n ⊕ Fin m` (state coordinates first), with $S_{xy}$ = `S.toBlocks₁₂` and $S_{yy}$ = `S.toBlocks₂₂`. The inverse is Mathlib's matrix inverse, which is the zero matrix when $S_{yy}$ is singular; then $G = 0$ and $D = \mathrm{diag}(I_n, 0)$, still positive semidefinite and nonzero.
-- source:
--   Shafieezadeh-Abadeh, Nguyen, Kuhn, Mohajerin Esfahani, Wasserstein Distributionally Robust Kalman Filtering, arXiv:1809.08830v3, p. 6, Algorithm 2 (gradient step); p. 14, (A.11); p. 5, ∇f(S) display

import Mathlib

open Matrix

namespace WassKF.Bisect

/-- The gradient matrix `D = ∇f(S)` of the objective `f(S) = Tr[S_xx − S_xy S_yy⁻¹ S_yx]` of
program (5), in the closed form of Algorithm 2 (p. 6) and (A.11) (p. 14):
`D = [I_n, −G]ᵀ [I_n, −G]` with `G = S_xy S_yy⁻¹`. The blocks are `S_xy = S.toBlocks₁₂` and
`S_yy = S.toBlocks₂₂`; `⁻¹` is Mathlib's matrix inverse (the zero matrix when `S_yy` is singular). -/
noncomputable def gradF {n m : ℕ} (S : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ) :
    Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ :=
  (Matrix.fromCols (1 : Matrix (Fin n) (Fin n) ℝ) (-(S.toBlocks₁₂ * S.toBlocks₂₂⁻¹)))ᵀ *
    Matrix.fromCols (1 : Matrix (Fin n) (Fin n) ℝ) (-(S.toBlocks₁₂ * S.toBlocks₂₂⁻¹))

end WassKF.Bisect


