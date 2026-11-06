-- Prove2me | Definitions.Def_NondualOpt_cappedSimplex
-- name    : NondualOpt_cappedSimplex
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T23:57:47.2232+00:00
-- url     : https://prove2.me/theorems/b761748f-034a-49db-b92c-ee3816314506
-- title:
--   The capped simplex $\Delta_T^{(\kappa)}$
-- statement:
--   For $\kappa>0$, the **capped simplex** is
--   $$
--   \Delta_T^{(\kappa)}=\Big\{\lambda\in\mathbb R^T:\ \lambda_t\ge0,\ \sum_t\lambda_t=1,\ \lambda_t\le\frac\kappa T\ \text{for every }t\Big\}.
--   $$
--   The paper uses $\kappa=2$: restricting convex weights to $\Delta_T^{(2)}$ trades greedy sample selection against averaging and yields the offset process of Lemma 5 and Lemma 18.
-- source:
--   Bullins–Guzmán–Martínez-Rubio–Molina, The First-Order Oracle Complexity of Lipschitz Convex Optimization in Nondual Settings, arXiv:2609.20687, p.26 and p.10

import Mathlib

namespace NondualOpt

/-- The capped simplex `Δ_T^{(κ)} = {λ ∈ Δ_T : λ_t ≤ κ/T for every t}`; the paper uses `κ = 2`.
Bullins–Guzmán–Martínez-Rubio–Molina, arXiv:2609.20687, p.26 (`Δ_T^{(2)}`); `Δ_T` is the simplex,
§2, p.6. -/
def cappedSimplex (T : ℕ) (κ : ℝ) : Set (Fin T → ℝ) :=
  {w | (∀ t, 0 ≤ w t ∧ w t ≤ κ / T) ∧ ∑ t, w t = 1}

end NondualOpt


