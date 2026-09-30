-- Prove2me | Definitions.Def_SteuerChoo_Lexico_Phi
-- name    : SteuerChoo_Lexico_Phi
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T16:50:45.127692+00:00
-- url     : https://prove2.me/theorems/03fe920c-d312-4c34-a902-6c6ac6308542
-- title:
--   The set $\Phi(\alpha)=\{z \mid z_i \ge z^*_i-\alpha/\lambda_i \text{ when } \lambda_i>0\}$
-- statement:
--   For weights $\lambda\in\mathbb R^k$, an ideal vector $z^*$ and a level $\alpha\in\mathbb R$, let
--   $$
--   \Phi(\alpha)=\{z\in\mathbb R^k \mid z_i\in[z^*_i-\alpha/\lambda_i,\,+\infty) \text{ when } \lambda_i>0\}.
--   $$
--   Coordinates with $\lambda_i=0$ are unconstrained. For $\alpha\ge0$ these sets are nested, and minimizing the weighted Tchebycheff program amounts to finding the smallest $\Phi(\alpha)$ that meets $Z$.
--
--   **Formalization Note** The division $\alpha/\lambda_i$ occurs only under the guard $\lambda_i>0$.
-- source:
--   Steuer and Choo, An Interactive Weighted Tchebycheff Procedure for Multiple Objective Programming, Math. Programming 26 (1983), p. 330, §3, the set Phi(alpha); p. 335, proof of Theorem 4.5

import Mathlib

namespace SteuerChoo.Lexico

/-- The set `Φ(α) = {z ∈ ℝ^k | z_i ∈ [z*_i − α/λ_i, +∞) when λ_i > 0}` of §3,
p. 330 (and of the proof of Theorem 4.5, p. 335). Coordinates with `λ_i = 0`
are unconstrained. -/
def Phi {k : ℕ} (lam zstar : Fin k → ℝ) (α : ℝ) : Set (Fin k → ℝ) :=
  {z | ∀ i, 0 < lam i → zstar i - α / lam i ≤ z i}

end SteuerChoo.Lexico


