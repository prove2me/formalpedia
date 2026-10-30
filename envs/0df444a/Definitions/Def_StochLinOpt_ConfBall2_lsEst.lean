-- Prove2me | Definitions.Def_StochLinOpt_ConfBall2_lsEst
-- name    : StochLinOpt_ConfBall2_lsEst
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:47:37.356448+00:00
-- url     : https://prove2.me/theorems/df3bd91b-efad-459f-a0be-4e4e061e1810
-- title:
--   Regularized least-squares estimate $\widehat\mu_t$
-- statement:
--   Given the spanner, decisions $x_\tau$ and observed losses $\ell_\tau$, the **least-squares estimate** of the unknown mean vector at round $t\ge1$ is
--
--   $$\widehat\mu_t=A_t^{-1}\sum_{1\le\tau<t}\ell_\tau x_\tau .$$
--
--   In particular $\widehat\mu_1=0$. It is the least-squares fit of the data in which the spanner vectors are pretended to have been played with loss $0$.
--
--   **Formalization Note** Lean's matrix inverse is $0$ for a singular matrix; every statement using $\widehat\mu_t$ assumes a spanner of a full-rank decision set, which makes $A_t$ invertible.
-- source:
--   Dani, Hayes, Kakade, Stochastic Linear Optimization under Bandit Feedback, COLT 2008, §3.1, p. 4 (definition of the estimator); Algorithm 3.1, p. 4

import Mathlib
import Definitions.Def_StochLinOpt_ConfBall2_gram
open Matrix

namespace StochLinOpt.ConfBall2

/-- **The regularized least-squares estimate `µ̂_t`** (Dani, Hayes, Kakade, *Stochastic Linear Optimization under Bandit Feedback*, COLT 2008, §3.1, p. 4:
"define the estimator µ̂t at time t by µ̂t = A−1t Σ_{τ<t} ℓτxτ"; Algorithm 3.1: "µ̂1 = 0",
"µ̂t+1 = A−1t+1 Σ_{τ=1}^t ℓτxτ").

`lsEst b x ℓ t = (gram b x t)⁻¹ (∑_{1 ≤ τ < t} ℓ τ • x τ)`.

**Formalization Note** Rounds are 1-based, so `lsEst b x ℓ 1 = 0`. `(gram b x t)⁻¹` is Mathlib's
matrix inverse, which is `0` for a singular matrix; every statement that uses `lsEst` assumes a
barycentric spanner of a full-rank `D`, which makes `gram b x t` positive definite. -/
noncomputable def lsEst {n : ℕ} (b : Fin n → Fin n → ℝ) (x : ℕ → Fin n → ℝ) (ℓ : ℕ → ℝ) (t : ℕ) :
    Fin n → ℝ :=
  (gram b x t)⁻¹ *ᵥ ∑ τ ∈ Finset.Ico 1 t, ℓ τ • x τ

end StochLinOpt.ConfBall2


