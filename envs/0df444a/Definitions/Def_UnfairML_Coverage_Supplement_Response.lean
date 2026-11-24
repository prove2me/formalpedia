-- Prove2me | Definitions.Def_UnfairML_Coverage_Supplement_Response
-- name    : UnfairML_Coverage_Supplement_Response
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T00:35:39.096837+00:00
-- url     : https://prove2.me/theorems/211097f9-1485-4a54-a82a-a9f1034d17fd
-- title:
--   Eqs. (39)–(41) — fixed-loss applicant response and ET global optimality
-- statement:
--   Fix the loss $\beta$, regular default proportion $d_r$, positive expected loss $c$, efficiencies $\gamma_p,\gamma_r$ and learning cost $\tau$. At protected default proportion $u$, define
--   $$\alpha(u)=\frac{\beta(u+d_r)-2c}{2-u-d_r},\qquad
--   P(u)=(\alpha(u),\beta,u,d_r,\gamma_p,\gamma_r).$$
--   Thus $\alpha_p(u)=\alpha(u)(1-u)$, $\alpha_r(u)=\alpha(u)(1-d_r)$, $\beta_p(u)=\beta u$ and $\beta_r=\beta d_r$. The active-branch ET objective (41) is
--   $$\pi_{ET,u}(s)=\frac{\alpha_r(u)\gamma_r s}{1-\gamma_r s}+
--   \frac{[\alpha_p(u)\gamma_r+\beta_p(u)\gamma_p-\beta_p(u)\gamma_r]s}{1-\gamma_p s}-\tau(s).$$
--   Its optimal effort is an attained global maximum over $[0,1/(2\gamma_r)]$. These definitions retain the change in both groups' expected revenues when $u$ changes.
--
--   **Formalization Note** Theorem 8 restricts the response family to valid standing parameters and the active low-loss branch. On that domain $d_r<u<1$, so $2-u-d_r>0$. The ET portion of (39) is encoded; the EO counterfactual with both defaults $d_r$ is contextual and is not part of this ET comparison. No equilibrium selection or stationarity assumption is used.
-- source:
--   Fu, Aseri, Singh & Srinivasan, “Un”Fair Machine Learning Algorithms, SSRN working paper 3408275 (version of 25 Mar 2021), pp. 38–39, eqs. (39)–(41)

import Mathlib
import Definitions.Def_UnfairML_Coverage_Supplement_CostModel

namespace UnfairML.Coverage.Supplement

/-- The utility response required by fixed expected loss (39), namely (40), p. 38. -/
noncomputable def responseAlpha (β dr c u : ℝ) : ℝ :=
  (β * (u + dr) - 2 * c) / (2 - u - dr)

/-- The existing primitive parameter structure, recomputed at protected default rate `u`.
Both groups' expected revenues therefore vary with `u`. -/
noncomputable def responseParams (β dr c γp γr u : ℝ) : Params :=
  { α := responseAlpha β dr c u, β := β, dp := u, dr := dr, γp := γp, γr := γr }

/-- Equation (41), with the parameter response (40) and arbitrary learning cost. -/
noncomputable def responseProfit (β dr c γp γr : ℝ) (τ : ℝ → ℝ) (u s : ℝ) : ℝ :=
  let P := responseParams β dr c γp γr u
  P.αr * P.γr * s / (1 - P.γr * s) +
    (P.αp * P.γr + P.βp * P.γp - P.βp * P.γr) * s / (1 - P.γp * s) - τ s

/-- Attainment of a global maximum of the active-branch ET objective (41). -/
def IsOptResponse (β dr c γp γr : ℝ) (τ : ℝ → ℝ) (u s : ℝ) : Prop :=
  s ∈ Set.Icc (0 : ℝ) (responseParams β dr c γp γr u).sMax ∧
  ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) (responseParams β dr c γp γr u).sMax →
    responseProfit β dr c γp γr τ u t ≤ responseProfit β dr c γp γr τ u s

end UnfairML.Coverage.Supplement


