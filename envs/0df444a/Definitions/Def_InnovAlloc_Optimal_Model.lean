-- Prove2me | Definitions.Def_InnovAlloc_Optimal_Model
-- name    : InnovAlloc_Optimal_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T02:19:49.34898+00:00
-- url     : https://prove2.me/theorems/388c23e9-3cb0-49f6-a58b-7eaf82200673
-- title:
--   §3.1–3.3 — innovation success, the effort game, principal profit, and threshold formulas
-- statement:
--   A principal has capacity $\bar B>0$ and allocates nonnegative resources $b_1,b_2$ with $b_1+b_2\le\bar B$. Agent $i$ chooses effort $x_i\ge0$, pays cost $x_i$, and succeeds with probability $p_i=1-e^{-b_ix_i}$. Successes are independent. A lone successful product earns $1$; when both succeed, each earns $\alpha\in[0,1]$. The agent receives the fraction $\gamma\in(0,1)$ of their product's profit.
--
--   The model defines each agent's expected payoff, the pure Nash equilibria of their simultaneous effort choices, and the principal's expected profit:
--
--   $$\Pi=(1-\gamma)\bigl(2\alpha p_1p_2+p_1(1-p_2)+p_2(1-p_1)\bigr).$$
--
--   An allocation is optimal when it is feasible, has an equilibrium, and every equilibrium at that allocation gives at least the profit of every equilibrium at every feasible allocation. The file also records the paper's monopoly and equal-split closed forms, and the thresholds of Theorem 1.
--
--   **Formalization Note** Effort remains the primitive even at $b_i=0$, where the paper's failure-rate transformation would divide by zero. The region-c threshold is set to $9$ at $\alpha=1/2$, correcting the printed $0/0$ formula.
-- source:
--   Gao, Fan, Huang & Chen, “Resource Allocation Among Competing Innovators”, SSRN preprint 3658157 (February 2021), pp. 6–15, §3.1–3.3, eqs. (1), (2), (7), (8), (10), (11), Theorem 1

import Mathlib
import Definitions.Def_CompetingChains_Cournot_TwoPlayerGame

namespace InnovAlloc.Optimal

noncomputable section

/-- The standing restrictions of §3.1, pp. 6–7: `γ ∈ (0,1)` and `α ∈ [0,1]`. -/
def Standing (α γ : ℝ) : Prop := 0 < γ ∧ γ < 1 ∧ 0 ≤ α ∧ α ≤ 1

/-- Equation (1), p. 6: success probability at resource `b` and effort `x`. -/
def succ (b x : ℝ) : ℝ := 1 - Real.exp (-(b * x))

/-- The agent's expected payoff, the effort form of (4), p. 10. -/
def agentPayoff (α γ bi xi bj xj : ℝ) : ℝ :=
  γ * succ bi xi * (α * succ bj xj + (1 - succ bj xj)) - xi

/-- Pure Nash equilibrium of the two agents' simultaneous effort game on `[0,∞)`, p. 10. -/
def IsEquilibrium (α γ b1 b2 x1 x2 : ℝ) : Prop :=
  ∃ (v1 v2 : {x : ℝ // 0 ≤ x}), v1.1 = x1 ∧ v2.1 = x2 ∧
    CompetingChains.Cournot.IsPureNash
      (fun z1 z2 => agentPayoff α γ b1 z1.1 b2 z2.1)
      (fun z1 z2 => agentPayoff α γ b2 z2.1 b1 z1.1) v1 v2

/-- The principal's expected profit, equation (7), p. 11, using independent innovations. -/
def principalProfit (α γ b1 b2 x1 x2 : ℝ) : ℝ :=
  (1 - γ) * (2 * α * succ b1 x1 * succ b2 x2
    + succ b1 x1 * (1 - succ b2 x2) + succ b2 x2 * (1 - succ b1 x1))

/-- Feasible allocations under the capacity constraint of §3.1, p. 6. -/
def Feasible (Bbar b1 b2 : ℝ) : Prop :=
  0 ≤ b1 ∧ 0 ≤ b2 ∧ b1 + b2 ≤ Bbar

/-- An optimal allocation for (7), p. 11: feasible, with an equilibrium, and every one
    of its equilibria dominates every equilibrium of every feasible allocation. -/
def IsOptimal (α γ Bbar b1 b2 : ℝ) : Prop :=
  Feasible Bbar b1 b2 ∧ (∃ x1 x2, IsEquilibrium α γ b1 b2 x1 x2) ∧
    ∀ x1 x2, IsEquilibrium α γ b1 b2 x1 x2 →
      ∀ c1 c2, Feasible Bbar c1 c2 → ∀ z1 z2,
        IsEquilibrium α γ c1 c2 z1 z2 →
          principalProfit α γ c1 c2 z1 z2 ≤ principalProfit α γ b1 b2 x1 x2

/-- The threshold `6√2 − 8` of Theorem 1, p. 15. -/
def alphaLow : ℝ := 6 * Real.sqrt 2 - 8

/-- The lower band end of Theorem 1 (iii)-b, p. 15. Used only where the radicand
    is nonnegative and `α < 1/2`, or where `α > 1/2` in the region-c threshold. -/
def bandLow (α : ℝ) : ℝ :=
  (1 - α - Real.sqrt (α ^ 2 + 16 * α - 8)) / (1 - 2 * α)

/-- The upper band end of Theorem 1 (iii)-b, p. 15. -/
def bandHigh (α : ℝ) : ℝ :=
  (1 - α + Real.sqrt (α ^ 2 + 16 * α - 8)) / (1 - 2 * α)

/-- Theorem 1 (iii)-c, p. 15, corrected at `α = 1/2`: the printed fraction is
    `0/0`, while its continuous limit and the true threshold are `9`. -/
def cThreshold (α : ℝ) : ℝ := if α = 1 / 2 then 9 else bandLow α

/-- Equation (2), p. 9: the single agent's optimal effort at positive resources. -/
def effortStar (γ b : ℝ) : ℝ :=
  if γ * b < 1 then 0 else Real.log (γ * b) / b

/-- Equation (8), p. 12: the principal's profit from investing `B` in one agent. -/
def profitMono (γ B : ℝ) : ℝ :=
  if γ * B ≤ 1 then 0 else (1 - γ) * (1 - 1 / (γ * B))

/-- Equation (10), p. 13: the symmetric equilibrium failure probability for `γB > 2`. -/
def yStar (α γ B : ℝ) : ℝ :=
  4 / (α * B * γ + Real.sqrt (B * γ) * Real.sqrt (8 - 8 * α + α ^ 2 * B * γ))

/-- Equation (11), p. 13: the principal's equal-allocation profit. -/
def profitDuo (α γ B : ℝ) : ℝ :=
  if γ * B ≤ 2 then 0
  else (1 - γ) * (α - 4 / (γ * B) +
    Real.sqrt ((γ * α ^ 2 * B - 8 * α + 8) / (γ * B)))

end
end InnovAlloc.Optimal


