-- Prove2me | Definitions.Def_UnfairML_Coverage_Supplement_GeneralFairness
-- name    : UnfairML_Coverage_Supplement_GeneralFairness
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T00:34:53.358502+00:00
-- url     : https://prove2.me/theorems/33059ac8-2ce0-44ed-a835-ab601ea3a515
-- title:
--   Eqs. (12)–(14) — general-fairness branch, feasible efforts and global optimality
-- statement:
--   For fairness parameter $\theta\ge1$, consider the branch $c_r=1-\gamma_r s$ and $c_p=1-\theta\gamma_r s$. Let $\tau$ be the learning cost and set
--   $$G_1(\theta)=\gamma_p\beta_p-\theta\gamma_r(\beta_p-\alpha_p),\qquad
--   \pi_\theta(s)=\frac{\gamma_r s\alpha_r}{1-\gamma_r s}+\frac{sG_1(\theta)}{1-\gamma_p s}-\tau(s).$$
--   Feasible efforts satisfy $0\le s\le1/(2\gamma_r)$ and $\gamma_p s\le1-\theta\gamma_r s\le1-\gamma_p s$. An optimal effort attains the global maximum of $\pi_\theta$ over precisely this feasible set.
--
--   The score-overlap restriction keeps the displayed profit within its active probability branch. It also retains zero effort and possible endpoint maxima. This definition supplies the optimizer referred to by Theorem 4 without assuming differentiability of an optimizer selection.
--
--   **Formalization Note** For $\theta\ge1$ and the standing parameter assumptions, both thresholds are in $[0,1]$, and the displayed condition is equivalent to the additional upper bound $s\le1/(\theta\gamma_r+\gamma_p)$. Formula (13) is never extrapolated to coverage above one. The closed effort convention follows Appendix A.
-- source:
--   Fu, Aseri, Singh & Srinivasan, “Un”Fair Machine Learning Algorithms, SSRN working paper 3408275 (version of 25 Mar 2021), pp. 25–26, eqs. (12)–(14)

import Mathlib
import Definitions.Def_UnfairML_Coverage_Supplement_CostModel

namespace UnfairML.Coverage.Supplement

/-- The coefficient of the protected-group term, (13), p. 26. -/
def G1 (P : Params) (θ : ℝ) : ℝ := P.γp * P.βp - θ * P.γr * (P.βp - P.αp)

/-- Profit (13) on the branch `cr = 1 - γr*s`, `cp = 1 - θ*γr*s`. -/
noncomputable def generalProfit (P : Params) (τ : ℝ → ℝ) (θ s : ℝ) : ℝ :=
  P.γr * s * P.αr / (1 - P.γr * s) + s * G1 P θ / (1 - P.γp * s) - τ s

/-- The effort box together with the protected threshold's overlapping-score-support
condition. For `θ ≥ 1`, these imply both thresholds lie in `[0,1]`. -/
def GeneralFeasible (P : Params) (θ s : ℝ) : Prop :=
  s ∈ Set.Icc (0 : ℝ) P.sMax ∧
  (1 - θ * P.γr * s) ∈ Set.Icc (P.γp * s) (1 - P.γp * s)

/-- Attainment of a global maximum of (13) over this branch's feasible efforts. -/
def IsOptGeneral (P : Params) (τ : ℝ → ℝ) (θ s : ℝ) : Prop :=
  GeneralFeasible P θ s ∧
  ∀ t : ℝ, GeneralFeasible P θ t → generalProfit P τ θ t ≤ generalProfit P τ θ s

end UnfairML.Coverage.Supplement


