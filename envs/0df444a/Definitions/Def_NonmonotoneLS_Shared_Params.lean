-- Prove2me | Definitions.Def_NonmonotoneLS_Shared_Params
-- name    : NonmonotoneLS_Shared_Params
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T20:14:16.41081+00:00
-- url     : https://prove2.me/theorems/8359e46b-f5ef-42d7-9e1a-e188367102c9
-- title:
--   Parameters of the nonmonotone line search algorithm (NLSA)
-- statement:
--   The Nonmonotone Line Search Algorithm (NLSA) of Zhang and Hager is run with six real parameters
--   $\eta_{\min}, \eta_{\max}, \delta, \sigma, \rho, \mu$ subject to
--
--   $$0 \le \eta_{\min} \le \eta_{\max} \le 1, \qquad 0 < \delta < \sigma < 1 < \rho, \qquad \mu > 0.$$
--
--   Here $\eta_{\min}$ and $\eta_{\max}$ bound the averaging weights $\eta_k$ that control the degree of nonmonotonicity, $\delta$ is the sufficient-decrease constant of condition (1.4), $\sigma$ the curvature constant of the Wolfe condition (1.5), $\rho > 1$ the expansion factor of the Armijo rule and $\mu$ the upper bound on an Armijo step.
--
--   These parameters are shared by every statement about the algorithm.
--
--   It serves chunk 01-global-convergence (p. 1044, NLSA Initialization; used by Lemma 1.1 p. 1045, Lemma 2.1 p. 1046, Theorem 2.2 and Eqs. (2.8)–(2.9) p. 1047, Eq. (2.14) and Corollary 2.3 p. 1048) and chunk 02-r-linear-convergence (p. 1044, NLSA Initialization; used by Lemma 1.1 p. 1045, the constants of Eq. (2.9) p. 1047 and Eqs. (3.7)–(3.8) p. 1050, Theorem 3.1 p. 1049 and its proof p. 1050).
--
--   **Formalization Note.** A structure with the six reals as fields and the eight inequalities above as proof fields, exactly those of the paper's "Initialization".
-- source:
--   Zhang, Hager, A Nonmonotone Line Search Technique and Its Application to Unconstrained Optimization, SIAM J. Optim. 14 (2004), p. 1044, NLSA, Initialization

import Mathlib

namespace NonmonotoneLS.Shared

/-- The parameters of the Nonmonotone Line Search Algorithm (NLSA) of Zhang and Hager
(SIAM J. Optim. 14 (2004), p. 1044, "Initialization"):
`0 ≤ η_min ≤ η_max ≤ 1`, `0 < δ < σ < 1 < ρ` and `μ > 0`. -/
structure Params where
  /-- lower bound `η_min` for the averaging weights `η_k` -/
  ηmin : ℝ
  /-- upper bound `η_max` for the averaging weights `η_k` -/
  ηmax : ℝ
  /-- sufficient-decrease constant `δ` in (1.4) -/
  δ : ℝ
  /-- curvature constant `σ` in (1.5) -/
  σ : ℝ
  /-- expansion factor `ρ > 1` of the Armijo rule -/
  ρ : ℝ
  /-- upper bound `μ` on the Armijo step -/
  μ : ℝ
  ηmin_nonneg : 0 ≤ ηmin
  ηmin_le_ηmax : ηmin ≤ ηmax
  ηmax_le_one : ηmax ≤ 1
  δ_pos : 0 < δ
  δ_lt_σ : δ < σ
  σ_lt_one : σ < 1
  one_lt_ρ : 1 < ρ
  μ_pos : 0 < μ

end NonmonotoneLS.Shared


