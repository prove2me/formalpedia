-- Prove2me | Definitions.Def_XuMannorRobust_Lasso_LassoFormulation
-- name    : XuMannorRobust_Lasso_LassoFormulation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T16:23:43.582803+00:00
-- url     : https://prove2.me/theorems/46f4a75c-b269-42f0-adef-dbdf72faab9c
-- title:
--   The Lasso: $\min_w \frac1n\sum_i (s_i^{(y)} - w^\top s_i^{(x)})^2 + c\|w\|_1$
-- statement:
--   Consider supervised samples $z = (z^{(y)}, z^{(x)})$ with a real response $z^{(y)} \in \mathbb R$ and a feature vector $z^{(x)} \in \mathbb R^m$. For a coefficient vector $w \in \mathbb R^m$ write $\|w\|_1 = \sum_{j=1}^m |w_j|$ for its $\ell_1$ norm. Given a training set $\mathbf s = (s_1, \dots, s_n)$ and a regularization parameter $c$, the **Lasso** (Tibshirani 1996) is the regression formulation
--
--   $$\min_{w \in \mathbb R^m}\ \frac1n \sum_{i=1}^n \big(s_i^{(y)} - w^\top s_i^{(x)}\big)^2 + c\,\|w\|_1 .$$
--
--   A vector $w$ **solves the Lasso** for $\mathbf s$ if its objective value is at most that of every $w' \in \mathbb R^m$. The minimizer need not be unique; a Lasso algorithm is any rule selecting one solution for each training set.
--
--   **Formalization Note** The $\ell_1$ norm is written out as a sum of absolute values, because Lean's default norm on `Fin m → ℝ` is the sup norm. $w^\top x$ is `dotProduct w x`. The factor $1/n$ is the real number `1 / (n : ℝ)`, which Lean sets to $0$ when $n = 0$; then the objective is $c\|w\|_1$.
-- source:
--   Xu & Mannor, Robustness and Generalization, Mach Learn 86 (2012), DOI 10.1007/s10994-011-5268-1, p. 404, Example 6, Eq. (5)

import Mathlib

namespace XuMannorRobust.Lasso

/-- The `ℓ₁` norm `‖w‖₁ = ∑_j |w_j|` of a coefficient vector `w ∈ ℝ^m`. (Lean's default norm on
`Fin m → ℝ` is the sup norm, so the `ℓ₁` norm is written out.) -/
noncomputable def l1norm {m : ℕ} (w : Fin m → ℝ) : ℝ :=
  ∑ j, |w j|

/-- **Lasso objective** (Xu & Mannor 2012, p. 404, Eq. (5)): for a training set
`s = ((s_1^{(y)}, s_1^{(x)}), …, (s_n^{(y)}, s_n^{(x)}))` in `ℝ × ℝ^m`, regularization parameter `c`
and coefficient vector `w`,
`(1/n) ∑_{i=1}^n (s_i^{(y)} − w^⊤ s_i^{(x)})² + c ‖w‖₁`. -/
noncomputable def lassoObjective {m n : ℕ} (c : ℝ) (s : Fin n → ℝ × (Fin m → ℝ))
    (w : Fin m → ℝ) : ℝ :=
  (1 / (n : ℝ)) * ∑ i, ((s i).1 - dotProduct w (s i).2) ^ 2 + c * l1norm w

/-- `w` **solves the Lasso** (Xu & Mannor 2012, p. 404, Eq. (5)): `w` minimizes the Lasso objective
over all of `ℝ^m`. The minimizer need not be unique. -/
def IsLassoSolution {m n : ℕ} (c : ℝ) (s : Fin n → ℝ × (Fin m → ℝ)) (w : Fin m → ℝ) : Prop :=
  ∀ w' : Fin m → ℝ, lassoObjective c s w ≤ lassoObjective c s w'

end XuMannorRobust.Lasso


