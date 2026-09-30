-- Prove2me | Definitions.Def_XuMannorRobust_Lasso_LassoLoss
-- name    : XuMannorRobust_Lasso_LassoLoss
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T16:25:05.561917+00:00
-- url     : https://prove2.me/theorems/d27b8623-06d9-4b50-8d55-33aa0e20c20f
-- title:
--   Absolute loss $|z^{(y)} - w^\top z^{(x)}|$ and mean squared response $Y(\mathbf s)$
-- statement:
--   For a linear predictor with coefficient vector $w \in \mathbb R^m$ and a sample $z = (z^{(y)}, z^{(x)}) \in \mathbb R \times \mathbb R^m$, the **absolute loss** is
--
--   $$l(w, z) = \big|z^{(y)} - w^\top z^{(x)}\big| .$$
--
--   For a training set $\mathbf s = (s_1, \dots, s_n)$ the **mean squared response** is
--
--   $$Y(\mathbf s) = \frac1n \sum_{i=1}^n \big[s_i^{(y)}\big]^2 .$$
--
--   These are the loss and the data-dependent scale that enter the robustness guarantee for the Lasso in Example 6 of Xu and Mannor.
--
--   **Formalization Note** $Y(\mathbf s)$ uses the real factor `1 / (n : ℝ)`, equal to $0$ when $n = 0$.
-- source:
--   Xu & Mannor, Robustness and Generalization, Mach Learn 86 (2012), DOI 10.1007/s10994-011-5268-1, p. 404, Example 6 (loss l(A_s, z) and Y(s))

import Mathlib

namespace XuMannorRobust.Lasso

/-- **Absolute prediction loss of a linear predictor** (Xu & Mannor 2012, p. 404, Example 6):
for a coefficient vector `w ∈ ℝ^m` and a sample `z = (z^{(y)}, z^{(x)}) ∈ ℝ × ℝ^m`,
`l(w, z) = |z^{(y)} − w^⊤ z^{(x)}|`. -/
noncomputable def lassoLoss {m : ℕ} (w : Fin m → ℝ) (z : ℝ × (Fin m → ℝ)) : ℝ :=
  |z.1 - dotProduct w z.2|

/-- **Mean squared response** (Xu & Mannor 2012, p. 404, Example 6):
`Y(s) = (1/n) ∑_{i=1}^n [s_i^{(y)}]²` for a training set `s` in `ℝ × ℝ^m`. -/
noncomputable def meanSqResponse {m n : ℕ} (s : Fin n → ℝ × (Fin m → ℝ)) : ℝ :=
  (1 / (n : ℝ)) * ∑ i, (s i).1 ^ 2

end XuMannorRobust.Lasso


