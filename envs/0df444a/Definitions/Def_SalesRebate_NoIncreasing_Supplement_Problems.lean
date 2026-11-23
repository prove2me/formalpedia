-- Prove2me | Definitions.Def_SalesRebate_NoIncreasing_Supplement_Problems
-- name    : SalesRebate_NoIncreasing_Supplement_Problems
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T03:14:35.14782+00:00
-- url     : https://prove2.me/theorems/26ae5fc5-e6ad-43b1-aeee-65ba549067aa
-- title:
--   Problem (3) p. 10, full-refund policies pp. 13–15, spread-constrained problem p. 18, rate-constrained problem (29) p. 34, saturated linear program p. 20
-- statement:
--   This file adds, on top of the published model `SalesRebate.NoIncreasing.Setting` of Ajorlou and Jadbabaie's *Sales-Based Rebate Design* (arXiv:1902.09646v4), the optimization problems of §III and §IV.
--
--   A valid model is $(\theta,\sigma_\theta,\sigma_\epsilon)$ with $\sigma_\theta,\sigma_\epsilon>0$; $\sigma^2=\sigma_\epsilon^2+\sigma_\theta^2$, $\tau=\sigma_\theta^2/\sigma^2$, $\sigma_v^2=\sigma_\epsilon^2\sigma_\theta^2/\sigma^2$, and $\mathbb E_{v\mid v_i=x}[\hat r(v)]$ is the expectation of a reward $\hat r$ (a function of the quality $v$) under the posterior $N(\tau x+(1-\tau)\theta,\sigma_v^2)$. The expected profit of $(\hat r,c)$ is (2): $\mathbb E_v[(p-\hat r(v))\Phi((v-c)/\sigma_\epsilon)]$. The objects defined are:
--
--   1. **Problem (3)** (p. 10): a pair $(\hat r,c)$ is feasible if $\hat r\in L^\infty(\mathbb R;[0,p])$ (measurable with values in $[0,p]$) and the threshold strategy with cutoff $c$ satisfies the equilibrium constraints (1): $\mathbb E_{v\mid v_i}[\hat r(v)]+v_i-p\ge0$ for $v_i\ge c$ and $\le0$ for $v_i\le c$. It is optimal if its profit is at least that of every feasible pair; the optimal value is the supremum of the profit over feasible pairs.
--   2. **Full-refund-or-nothing policies** (pp. 13, 15): $\hat r$ is, almost everywhere,
--   $$\hat r(v)=p\times\sum_{j=1}^{l}\mathbf 1\{w_L^j\le v\le w_H^j\}$$
--   with extended-real endpoints (so $w_L^1=-\infty$ is allowed); the best profit over feasible pairs of (3) whose reward has this form with $l$ intervals, and `IsOptimalRefund`, which asserts feasibility in this class and maximal profit among all pairs in the class.
--   3. **The spread-constrained problem** (p. 18): $\hat r:\mathbb R\to[0,p]$ measurable with $r_{\max}-r_{\min}\le\sqrt{2\pi}\,\sigma_\epsilon\sigma/\sigma_\theta$, and the indifference equation $c+\mathbb E_{v\mid v_i=c}[\hat r(v)]=p$; its optimal pairs; $r_M=\min(p,\sqrt{2\pi}\,\sigma_\epsilon\sigma/\sigma_\theta)$ and $\sigma_v=\sqrt{\sigma_v^2}$.
--   4. **The rate-constrained problem** (p. 19 and (29), p. 34): $\hat r:\mathbb R\to[0,p]$ continuous and piecewise continuously differentiable (finitely many break points in every bounded interval, with finite left and right limits of the derivative at each break point) with $|\tfrac{d}{dv}\hat r(v)|\le1/\tau$ off the break points, and the indifference equation; its optimal pairs and optimal value.
--   5. **The saturated linear program** of Theorem 4: $p$ for $v<v_L$, $p-(v-v_L)/\tau$ for $v_L\le v<v_H$, $0$ for $v_H\le v$.
--   6. **The fixed-total-uncertainty family** of Theorems 1 and 5: $(\theta,\sqrt{\sigma^2-s^2},s)$, whose taste deviation is $s$ and whose total uncertainty is $\sigma$ for $0<s<\sigma$.
--
--   These are the feasible sets and optimal programs that Theorems 1, 3, 4 and 5 characterize.
--
--   **Formalization Note** Optimal values are real suprema (`sSup`). Each set is nonempty (the no-reward pair $(0,p)$ is feasible for (3) and is a full-refund policy with empty intervals; the constant reward $p-c$, $c\in[0,p]$, is feasible for both constrained problems) and bounded above by $p$, since $\Phi\le1$; so no junk value arises. $r_{\max}-r_{\min}$ is encoded as "every two rewards differ by at most the bound", which is the supremum minus the infimum. The full-refund form is an equality almost everywhere with respect to Lebesgue measure, because $\hat r$ is an element of $L^\infty$; the conditional expectations and the profit do not see null sets.
-- source:
--   Ajorlou, Jadbabaie, Sales-Based Rebate Design, arXiv:1902.09646v4, p. 10 (3); pp. 13, 15 (full-refund-or-nothing policy); p. 18 (spread-constrained problem); p. 19 and p. 34 (29) (rate-constrained problem); p. 20 (Theorem 4 program); pp. 15, 22 (fixed σ)

import Mathlib
import Definitions.Def_BlackScholesModel_Core
import Definitions.Def_SalesRebate_NoIncreasing_Setting

namespace SalesRebate.NoIncreasing.Supplement

open MeasureTheory ProbabilityTheory BlackScholesModel Filter Topology

/-- p. 10: `r̂ ∈ L∞(ℝ; [0, p])`, a measurable reward (as a function of the quality) with values
in `[0, p]`. -/
def IsAdmissibleReward (p : ℝ) (rhat : ℝ → ℝ) : Prop :=
  Measurable rhat ∧ ∀ v, rhat v ∈ Set.Icc 0 p

/-- Problem (3), p. 10: the pair `(r̂, c)` is feasible, i.e. `r̂ ∈ L∞(ℝ; [0, p])` and the
threshold strategy with cutoff `c` satisfies the equilibrium constraints (1) for `r̂`. -/
def Feasible3 (M : Model) (p : ℝ) (rhat : ℝ → ℝ) (c : ℝ) : Prop :=
  IsAdmissibleReward p rhat ∧ M.IsEquilibriumCutoff p rhat c

/-- Problem (3), p. 10: `(r̂, c)` is an optimal solution: it is feasible and its expected profit
(2) is at least that of every feasible pair. -/
def IsOptimal3 (M : Model) (p : ℝ) (rhat : ℝ → ℝ) (c : ℝ) : Prop :=
  Feasible3 M p rhat c ∧
    ∀ rhat' c', Feasible3 M p rhat' c' → M.expectedProfit p rhat' c' ≤ M.expectedProfit p rhat c

/-- The optimal value of problem (3): the supremum of the expected profit (2) over the feasible
pairs. (The feasible set contains `(0, p)` and every profit is at most `p`.) -/
noncomputable def optValue3 (M : Model) (p : ℝ) : ℝ :=
  sSup {π : ℝ | ∃ rhat c, Feasible3 M p rhat c ∧ M.expectedProfit p rhat c = π}

/-- pp. 13, 15: `r̂` is (almost everywhere) a full-refund-or-nothing policy with `l` refund
intervals, `r̂(v) = p × Σ_{j=1}^{l} 1{w_L^j ≤ v ≤ w_H^j}`; the endpoints are extended reals, so
`w_L^1 = −∞` (and `w_H^l = +∞`) are allowed. -/
def IsFullRefundPolicy (p : ℝ) (l : ℕ) (rhat : ℝ → ℝ) : Prop :=
  ∃ wL wH : Fin l → EReal,
    rhat =ᵐ[volume] fun v => p * ∑ j, Set.indicator {x : ℝ | wL j ≤ (x : EReal) ∧ (x : EReal) ≤ wH j}
      (fun _ => (1 : ℝ)) v

/-- The supremum of the expected profit (2) over the feasible pairs of (3) whose reward is a
full-refund-or-nothing policy with `l` refund intervals (Theorem 1 ii, p. 15). -/
noncomputable def optValueRefund (M : Model) (p : ℝ) (l : ℕ) : ℝ :=
  sSup {π : ℝ | ∃ rhat c, Feasible3 M p rhat c ∧ IsFullRefundPolicy p l rhat ∧
    M.expectedProfit p rhat c = π}

/-- Theorem 1(ii), p. 15: an optimal feasible full-refund policy with at most `l` intervals.
Empty intervals pad a representation without changing its reward. -/
def IsOptimalRefund (M : Model) (p : ℝ) (l : ℕ) (rhat : ℝ → ℝ) (c : ℝ) : Prop :=
  Feasible3 M p rhat c ∧ IsFullRefundPolicy p l rhat ∧
    ∀ rhat' c', Feasible3 M p rhat' c' → IsFullRefundPolicy p l rhat' →
      M.expectedProfit p rhat' c' ≤ M.expectedProfit p rhat c

/-- p. 18: the spread bound `√(2π) σε σ / σθ` of (11). -/
noncomputable def spreadBound (M : Model) : ℝ := Real.sqrt (2 * Real.pi) * M.σε * M.σ / M.σθ

/-- Theorem 3, p. 18: `r_M = min(p, √(2π) σε σ / σθ)`. -/
noncomputable def rM (M : Model) (p : ℝ) : ℝ := min p (spreadBound M)

/-- p. 18: `σv = σε σθ / √(σε² + σθ²)`, the posterior standard deviation. -/
noncomputable def sigmaV (M : Model) : ℝ := Real.sqrt M.σv2

/-- The spread-constrained problem, p. 18: `r̂ : ℝ → [0, p]` measurable, every two rewards differ
by at most `√(2π) σε σ / σθ` (`r_max − r_min ≤ √(2π) σε σ / σθ`), and the cutoff `c` solves the
indifference equation `c + E_{v|vᵢ=c}[r̂(v)] = p`. -/
def FeasibleSC (M : Model) (p : ℝ) (rhat : ℝ → ℝ) (c : ℝ) : Prop :=
  IsAdmissibleReward p rhat ∧ (∀ v w, rhat v - rhat w ≤ spreadBound M) ∧
    c + M.condReward rhat c = p

/-- An optimal solution of the spread-constrained problem (p. 18). -/
def IsOptimalSC (M : Model) (p : ℝ) (rhat : ℝ → ℝ) (c : ℝ) : Prop :=
  FeasibleSC M p rhat c ∧
    ∀ rhat' c', FeasibleSC M p rhat' c' → M.expectedProfit p rhat' c' ≤ M.expectedProfit p rhat c

/-- A continuous, piecewise continuously differentiable function: `f` is continuous, the set `D`
of break points is locally finite, `f` is `C¹` off `D`, and its derivative has finite one-sided
limits at the break points, as for the piecewise continuous control in (29), p. 34. -/
def IsPiecewiseC1 (f : ℝ → ℝ) (D : Set ℝ) : Prop :=
  Continuous f ∧ (∀ a b : ℝ, (D ∩ Set.Icc a b).Finite) ∧ ContDiffOn ℝ 1 f Dᶜ ∧
    ∀ v ∈ D, ∃ L R : ℝ,
      Tendsto (deriv f) (𝓝[<] v) (𝓝 L) ∧ Tendsto (deriv f) (𝓝[>] v) (𝓝 R)

/-- The rate-of-change constraint, p. 19 and (29), p. 34: `r̂` is continuous and piecewise `C¹`
with `|d r̂/dv| ≤ 1/τ` off its break points. -/
def IsRateConstrained (M : Model) (rhat : ℝ → ℝ) : Prop :=
  ∃ D : Set ℝ, IsPiecewiseC1 rhat D ∧ ∀ v ∉ D, |deriv rhat v| ≤ 1 / M.tau

/-- The rate-constrained problem (29), p. 34: `0 ≤ r̂ ≤ p`, the rate-of-change constraint, and
the indifference equation `c + E_{v|vᵢ=c}[r̂(v)] = p`. -/
def FeasibleRC (M : Model) (p : ℝ) (rhat : ℝ → ℝ) (c : ℝ) : Prop :=
  (∀ v, rhat v ∈ Set.Icc 0 p) ∧ IsRateConstrained M rhat ∧ c + M.condReward rhat c = p

/-- An optimal solution of the rate-constrained problem (29). -/
def IsOptimalRC (M : Model) (p : ℝ) (rhat : ℝ → ℝ) (c : ℝ) : Prop :=
  FeasibleRC M p rhat c ∧
    ∀ rhat' c', FeasibleRC M p rhat' c' → M.expectedProfit p rhat' c' ≤ M.expectedProfit p rhat c

/-- The optimal value of the rate-constrained problem. (The constant reward `p − c` with `c ∈ [0, p]`
is feasible and every profit is at most `p`.) -/
noncomputable def optValueRC (M : Model) (p : ℝ) : ℝ :=
  sSup {π : ℝ | ∃ rhat c, FeasibleRC M p rhat c ∧ M.expectedProfit p rhat c = π}

/-- Theorem 4, p. 20: the saturated linear reward `p` for `v < v_L`, `p − (v − v_L)/τ` for
`v_L ≤ v < v_H`, and `0` for `v_H ≤ v`. -/
noncomputable def rcProgram (M : Model) (p vL vH : ℝ) (v : ℝ) : ℝ :=
  if v < vL then p else if v < vH then p - (v - vL) / M.tau else 0

/-- Theorems 1 and 5 (pp. 15, 22): the model with prior mean `θ`, total uncertainty `σ` held
fixed, and taste deviation `σε = s`, so that `σθ = √(σ² − s²)` (meaningful for `0 < s < σ`). -/
noncomputable def famModel (θ σ s : ℝ) : Model := ⟨θ, Real.sqrt (σ ^ 2 - s ^ 2), s⟩

end SalesRebate.NoIncreasing.Supplement


