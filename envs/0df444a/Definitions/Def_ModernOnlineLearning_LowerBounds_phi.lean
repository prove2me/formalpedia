-- Prove2me | Definitions.Def_ModernOnlineLearning_LowerBounds_phi
-- name    : ModernOnlineLearning_LowerBounds_phi
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T02:37:33.530799+00:00
-- url     : https://prove2.me/theorems/a3557f57-9e7e-4ef7-8618-db315d91cd33
-- title:
--   The auxiliary function φ in Theorem 5.4
-- statement:
--   For $0<\alpha<1$, define the coefficient used in the lower bound for unprojected online subgradient descent by
--
--   $$
--   \phi(\alpha)=\frac{1}{2-\alpha}+\frac{(1/2)^{1-\alpha}-1}{1-\alpha}.
--   $$
--
--   The coefficient specifies the explicit constant in the regret lower bound of Theorem 5.4.
--
--   **Formalization Note** The Lean function is total on $\mathbb R$, while the theorem uses it only on $(0,1)$, the domain stated in the book.
-- source:
--   Orabona, arXiv:1912.13213v10, Theorem 5.4, p. 52

import Mathlib

namespace ModernOnlineLearning.LowerBounds

/-- The auxiliary function `φ` in Theorem 5.4. The theorem restricts its
argument to `0 < α < 1`, where both denominators are nonzero. -/
noncomputable def phi (α : ℝ) : ℝ :=
  1 / (2 - α) + (((1 / 2 : ℝ) ^ (1 - α)) - 1) / (1 - α)

end ModernOnlineLearning.LowerBounds


