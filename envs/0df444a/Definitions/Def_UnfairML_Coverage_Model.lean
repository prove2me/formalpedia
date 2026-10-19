-- Prove2me | Definitions.Def_UnfairML_Coverage_Model
-- name    : UnfairML_Coverage_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T01:18:49.57754+00:00
-- url     : https://prove2.me/theorems/f97cfcab-501c-49d8-99e0-5dfe3a272ef5
-- title:
--   §3, pp. 10–17 — two-group threshold classification with learning effort: profit (1), ET and EO constraints, optimal decisions, coverage rate
-- statement:
--   This file sets up the lending model of Fu, Aseri, Singh and Srinivasan.
--
--   A bank accepts or rejects loan candidates from two groups of equal (unit) size, a **protected** group $p$ and a **regular** group $r$. A good candidate repays and earns the bank $\alpha$; a bad candidate defaults and costs the bank $\beta$. The proportions of bad candidates are $d_p$ and $d_r$, and the expected profit and loss per group are
--   $$\alpha_p=\alpha(1-d_p),\quad \beta_p=\beta d_p,\quad \alpha_r=\alpha(1-d_r),\quad \beta_r=\beta d_r .$$
--   The **standing assumptions** of §3.1 are: $\alpha>0$, $\beta>0$, $0<d_r<d_p<1$, $\beta_r\ge\alpha_r$, and $0<\gamma_p<\gamma_r$. **Case (1)** (low expected loss) is the further assumption $\beta_p\le\alpha_p+\alpha_r$.
--
--   The bank exerts a learning effort $s\in[0,1/(2\gamma_r)]$. In group $A\in\{p,r\}$ the scores of bad candidates are uniform on $[0,1-\gamma_A s]$ and those of good candidates uniform on $[\gamma_A s,1]$. The bank accepts a candidate of group $A$ when the score is above the threshold $c_A\in[0,1]$. With the learning cost
--   $$\tau(s)=\frac{ks}{1-\gamma_r s},$$
--   the bank's profit is equation (1):
--   $$\pi=\min\Big\{\tfrac{1-c_r}{1-\gamma_r s},1\Big\}\alpha_r-\max\Big\{\tfrac{1-\gamma_r s-c_r}{1-\gamma_r s},0\Big\}\beta_r+\min\Big\{\tfrac{1-c_p}{1-\gamma_p s},1\Big\}\alpha_p-\max\Big\{\tfrac{1-\gamma_p s-c_p}{1-\gamma_p s},0\Big\}\beta_p-\tau(s).$$
--
--   The **coverage rate** of group $A$ is the fraction of its good candidates that are accepted, $\min\{(1-c_A)/(1-\gamma_A s),1\}$. **Equal treatment** (ET) requires $c_p=c_r$; **equal opportunity** (EO) requires equal coverage rates, written as equation (6):
--   $$\frac{1-c_r}{1-\gamma_r s}=\frac{1-c_p}{1-\gamma_p s}.$$
--   An **optimal ET decision** is a feasible $(c,s)$ whose profit with $c_p=c_r=c$ is at least that of every feasible $(c',s')$; an **optimal EO decision** is a feasible triple $(c_p,c_r,s)$ satisfying (6) whose profit is at least that of every feasible triple satisfying (6).
--
--   The file also records the reduced profits of case (1) (p. 17),
--   $$\pi_{ET}(s)=\frac{\alpha_p\gamma_r s}{1-\gamma_p s}+\frac{\alpha_r\gamma_r s}{1-\gamma_r s}+\frac{\beta_p\gamma_p s}{1-\gamma_p s}-\frac{\beta_p\gamma_r s}{1-\gamma_p s}-\tau(s),$$
--   $$\pi_{EO}(s)=\frac{\alpha_p\gamma_r s}{1-\gamma_r s}+\frac{\alpha_r\gamma_r s}{1-\gamma_r s}+\frac{\beta_p\gamma_p s}{1-\gamma_p s}-\frac{\beta_p\gamma_r s}{1-\gamma_r s}-\tau(s),$$
--   the coefficient $A=\alpha_p\gamma_r-\beta_p\gamma_r+\beta_p\gamma_p$, $\rho=1/(2-\gamma_p/\gamma_r)$, and the cost range of p. 23: $k\in[\alpha_r\gamma_r+\rho^2A,\ \alpha_r\gamma_r+A)$, rewritten as $k=\alpha_r\gamma_r+\sigma^2A$ with $\sigma\in[\rho,1)$.
--
--   These objects are shared by every statement of the mission: the threshold reductions, the closed forms of the optimal efforts, and Theorem 2.
--
--   **Formalization Note** All quantities are real numbers. `Params` holds $\alpha,\beta,d_p,d_r,\gamma_p,\gamma_r$; $\alpha_p,\beta_p,\alpha_r,\beta_r$, $A$ (`Acoef`), $\rho$ (`rho`) and $1/(2\gamma_r)$ (`sMax`) are derived. Two hypotheses are added to the page: $\alpha>0$ and $\beta>0$ (Table 1 calls them a utility and a dis-utility but never states their sign). Effort ranges over the **closed** interval $[0,1/(2\gamma_r)]$ of Appendix A (p. 43) rather than §3.1's half-open $[0,1/(2\gamma_r))$: on the half-open interval the ET problem has no optimum when $\sigma=\rho$. Thresholds range over $[0,1]$. All optimality quantifiers are restricted to these boxes, on which the denominators $1-\gamma s$ are at least $1/2$. `CostRange` keeps both forms of p. 23 as printed; it is satisfiable only when $A>0$, which is a consequence and not a separate hypothesis.
-- source:
--   Fu, Aseri, Singh & Srinivasan, “Un”Fair Machine Learning Algorithms, SSRN working paper 3408275 (version of 25 Mar 2021), pp. 10–17, §3, eqs. (1), (6), case (1) p. 17; cost function and k-range pp. 22–23; coverage rate p. 20; effort domain p. 43

import Mathlib

namespace UnfairML.Coverage

/-- Primitive parameters of the model of §3.1 (pp. 10–11): `α` profit of accepting a good candidate,
`β` loss of accepting a bad candidate, `dp`, `dr` the proportions of bad candidates in the protected and
the regular group, `γp`, `γr` the rates at which learning effort separates the score distributions of
the protected and the regular group. -/
structure Params where
  α : ℝ
  β : ℝ
  dp : ℝ
  dr : ℝ
  γp : ℝ
  γr : ℝ

namespace Params

/-- `αp = α(1 − dp)`, expected profit from the protected group's good candidates (p. 11). -/
def αp (P : Params) : ℝ := P.α * (1 - P.dp)

/-- `βp = β dp`, expected loss from the protected group's bad candidates (p. 11). -/
def βp (P : Params) : ℝ := P.β * P.dp

/-- `αr = α(1 − dr)` (p. 11). -/
def αr (P : Params) : ℝ := P.α * (1 - P.dr)

/-- `βr = β dr` (p. 11). -/
def βr (P : Params) : ℝ := P.β * P.dr

/-- Standing assumptions of §3.1 (pp. 10–11): both groups contain good and bad candidates
(`0 < dr`, `dp < 1`), `dp > dr`, `βr ≥ αr`, `γp > 0`, `γr > γp`. The positivity of `α` and `β`
(the utility and dis-utility of Table 1, p. 13) is added. -/
def Standing (P : Params) : Prop :=
  0 < P.α ∧ 0 < P.β ∧ 0 < P.dr ∧ P.dr < P.dp ∧ P.dp < 1 ∧ P.αr ≤ P.βr ∧ 0 < P.γp ∧ P.γp < P.γr

/-- Case (1) of §3.3, p. 17 (low expected loss): `βp ≤ αp + αr`. -/
def LowLoss (P : Params) : Prop := P.βp ≤ P.αp + P.αr

/-- The coefficient `αp γr − βp γr + βp γp` of the cost range, p. 23. -/
def Acoef (P : Params) : ℝ := P.αp * P.γr - P.βp * P.γr + P.βp * P.γp

/-- `ρ = 1 / (2 − γp/γr)`, p. 23. -/
noncomputable def rho (P : Params) : ℝ := 1 / (2 - P.γp / P.γr)

/-- The largest admissible effort `1/(2γr)`; efforts range over the closed interval
`[0, 1/(2γr)]` of Appendix A, p. 43. -/
noncomputable def sMax (P : Params) : ℝ := 1 / (2 * P.γr)

end Params

/-- The learning cost `τ(s) = k s / (1 − γr s)` of §4.4, p. 22. -/
noncomputable def tau (P : Params) (k s : ℝ) : ℝ := k * s / (1 - P.γr * s)

/-- The bank's profit, equation (1), p. 13, with thresholds `cp`, `cr`, effort `s` and cost
`τ(s) = k s/(1 − γr s)`. -/
noncomputable def profit (P : Params) (k cp cr s : ℝ) : ℝ :=
  min ((1 - cr) / (1 - P.γr * s)) 1 * P.αr - max ((1 - P.γr * s - cr) / (1 - P.γr * s)) 0 * P.βr
  + min ((1 - cp) / (1 - P.γp * s)) 1 * P.αp - max ((1 - P.γp * s - cp) / (1 - P.γp * s)) 0 * P.βp
  - tau P k s

/-- Coverage rate (p. 20): the fraction of a group's good candidates, with scores `U[γ s, 1]`,
whose score is at least the threshold `c`. -/
noncomputable def coverage (γ c s : ℝ) : ℝ := min ((1 - c) / (1 - γ * s)) 1

/-- The equal-opportunity constraint in the form of equation (6), p. 16. -/
def EOConstraint (P : Params) (cp cr s : ℝ) : Prop :=
  (1 - cr) / (1 - P.γr * s) = (1 - cp) / (1 - P.γp * s)

/-- `(c, s)` is an optimal decision of the bank under equal treatment (`cp = cr = c`, §3.2):
feasible, and its profit (1) is at least that of every feasible `(c', s')`. -/
def IsOptET (P : Params) (k c s : ℝ) : Prop :=
  c ∈ Set.Icc (0 : ℝ) 1 ∧ s ∈ Set.Icc (0 : ℝ) P.sMax ∧
  ∀ c' s', c' ∈ Set.Icc (0 : ℝ) 1 → s' ∈ Set.Icc (0 : ℝ) P.sMax →
    profit P k c' c' s' ≤ profit P k c c s

/-- `(cp, cr, s)` is an optimal decision of the bank under equal opportunity (§3.2, eq. (6)):
feasible, satisfying (6), and its profit (1) is at least that of every feasible triple satisfying (6). -/
def IsOptEO (P : Params) (k cp cr s : ℝ) : Prop :=
  cp ∈ Set.Icc (0 : ℝ) 1 ∧ cr ∈ Set.Icc (0 : ℝ) 1 ∧ s ∈ Set.Icc (0 : ℝ) P.sMax ∧
  EOConstraint P cp cr s ∧
  ∀ cp' cr' s', cp' ∈ Set.Icc (0 : ℝ) 1 → cr' ∈ Set.Icc (0 : ℝ) 1 → s' ∈ Set.Icc (0 : ℝ) P.sMax →
    EOConstraint P cp' cr' s' → profit P k cp' cr' s' ≤ profit P k cp cr s

/-- `πET(s)`, the profit under equal treatment at the optimal threshold for effort `s`, in case (1),
p. 17. -/
noncomputable def piET (P : Params) (k s : ℝ) : ℝ :=
  P.αp * P.γr * s / (1 - P.γp * s) + P.αr * P.γr * s / (1 - P.γr * s)
  + P.βp * P.γp * s / (1 - P.γp * s) - P.βp * P.γr * s / (1 - P.γp * s) - tau P k s

/-- `πEO(s)`, the profit under equal opportunity at the optimal thresholds for effort `s`, in case
(1), p. 17. -/
noncomputable def piEO (P : Params) (k s : ℝ) : ℝ :=
  P.αp * P.γr * s / (1 - P.γr * s) + P.αr * P.γr * s / (1 - P.γr * s)
  + P.βp * P.γp * s / (1 - P.γp * s) - P.βp * P.γr * s / (1 - P.γr * s) - tau P k s

/-- The cost assumptions of p. 23: `k ∈ [αrγr + ρ²A, αrγr + A)` with `A = αpγr − βpγr + βpγp`, and
its rewriting `k = αrγr + σ²A` with `σ ∈ [ρ, 1)`. -/
def CostRange (P : Params) (k σ : ℝ) : Prop :=
  k ∈ Set.Ico (P.αr * P.γr + P.rho ^ 2 * P.Acoef) (P.αr * P.γr + P.Acoef) ∧
  σ ∈ Set.Ico P.rho 1 ∧ k = P.αr * P.γr + σ ^ 2 * P.Acoef

end UnfairML.Coverage


