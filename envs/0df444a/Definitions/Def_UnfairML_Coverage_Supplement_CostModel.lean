-- Prove2me | Definitions.Def_UnfairML_Coverage_Supplement_CostModel
-- name    : UnfairML_Coverage_Supplement_CostModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T00:33:42.201733+00:00
-- url     : https://prove2.me/theorems/1caba661-4df1-4ec7-bfe2-4e7d14e56a50
-- title:
--   §3.1–3.3 — arbitrary learning cost, profit and globally optimal ET/EO policies
-- statement:
--   Let $P=(\alpha,\beta,d_p,d_r,\gamma_p,\gamma_r)$ be the published two-group parameters. Expected payoffs, score supports and fairness constraint (6) are those of the published model. Write $S=[0,1/(2\gamma_r)]$. A learning cost $\tau:\mathbb R\to\mathbb R$ is convex and nondecreasing on $S$. The cost-parametric profit is
--   $$\pi_\tau(c_p,c_r,s)=\pi_0(c_p,c_r,s)-\tau(s),$$
--   where $\pi_0$ is the gross revenue in (1), computed with the published rational-cost parameter set to zero. An ET optimum is an attained global maximum over $c_p=c_r=c\in[0,1]$, $s\in S$. An EO optimum is an attained global maximum over $c_p,c_r\in[0,1]$, $s\in S$, subject to $(1-c_r)/(1-\gamma_r s)=(1-c_p)/(1-\gamma_p s)$.
--
--   The definitions preserve the full threshold problem, including all three loss regimes, while allowing every cost in §3.1. Neither a derivative nor a stationarity condition replaces optimality.
--
--   **Formalization Note** The primitives are imported unchanged. The effort interval is closed as in Appendix A, rather than half-open as in §3.1. Thresholds lie in $[0,1]$. “Increasing” is read as nondecreasing; no differentiability, zero-cost normalization or uniqueness is assumed.
-- source:
--   Fu, Aseri, Singh & Srinivasan, “Un”Fair Machine Learning Algorithms, SSRN working paper 3408275 (version of 25 Mar 2021), pp. 10–17, eqs. (1), (6); Appendix A p. 43

import Mathlib
import Definitions.Def_UnfairML_Coverage_Model

namespace UnfairML.Coverage.Supplement

/-- The arbitrary convex increasing cost of §3.1, on the admissible effort interval.
No differentiability, strict convexity, normalization or optimizer uniqueness is imposed. -/
def IsLearningCost (P : Params) (τ : ℝ → ℝ) : Prop :=
  ConvexOn ℝ (Set.Icc (0 : ℝ) P.sMax) τ ∧
  MonotoneOn τ (Set.Icc (0 : ℝ) P.sMax)

/-- Equation (1), replacing only the published rational cost slot. -/
noncomputable def profitWithCost (P : Params) (τ : ℝ → ℝ) (cp cr s : ℝ) : ℝ :=
  profit P 0 cp cr s - τ s

/-- Joint, globally attained ET optimum, including every threshold branch. -/
def IsOptETWithCost (P : Params) (τ : ℝ → ℝ) (c s : ℝ) : Prop :=
  c ∈ Set.Icc (0 : ℝ) 1 ∧ s ∈ Set.Icc (0 : ℝ) P.sMax ∧
  ∀ c' s', c' ∈ Set.Icc (0 : ℝ) 1 → s' ∈ Set.Icc (0 : ℝ) P.sMax →
    profitWithCost P τ c' c' s' ≤ profitWithCost P τ c c s

/-- Joint, globally attained EO optimum using (6), including every threshold branch. -/
def IsOptEOWithCost (P : Params) (τ : ℝ → ℝ) (cp cr s : ℝ) : Prop :=
  cp ∈ Set.Icc (0 : ℝ) 1 ∧ cr ∈ Set.Icc (0 : ℝ) 1 ∧
  s ∈ Set.Icc (0 : ℝ) P.sMax ∧ EOConstraint P cp cr s ∧
  ∀ cp' cr' s', cp' ∈ Set.Icc (0 : ℝ) 1 → cr' ∈ Set.Icc (0 : ℝ) 1 →
    s' ∈ Set.Icc (0 : ℝ) P.sMax → EOConstraint P cp' cr' s' →
    profitWithCost P τ cp' cr' s' ≤ profitWithCost P τ cp cr s

end UnfairML.Coverage.Supplement


