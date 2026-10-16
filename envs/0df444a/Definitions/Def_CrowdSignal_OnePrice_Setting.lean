-- Prove2me | Definitions.Def_CrowdSignal_OnePrice_Setting
-- name    : CrowdSignal_OnePrice_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-16T06:16:24.86498+00:00
-- url     : https://prove2.me/theorems/87b95e55-b204-4c6f-b37c-9ae527f1e45f
-- title:
--   §3 and §4.3: one-price crowdfunding signaling game
-- statement:
--   Let $0<q_L<q_H$ be the low and high product qualities, $0<\alpha<1$ the share of regular-period customers whose taste repeats from the funding period, and $T>0$ the financing target. The two market sizes are one; marginal cost and salvage value are zero; and the discount factor is one. The prior probability of high quality does not enter the one-price separating-equilibrium results.
--
--   For true quality $q_i\in\{q_L,q_H\}$, believed quality $q_j\in\{q_L,q_H\}$, funding price $T\le p_1<q_j$, and regular price $0<p_2\le q_i$, conditional regular-period profit is
--   $$
--   \pi^{ij}_2(p_2\mid p_1)=\begin{cases}
--   \alpha p_2+(1-\alpha)(1-p_2/q_i)p_2,&p_2<p_1q_i/q_j,\\
--   \dfrac{\alpha}{1-p_1/q_j}(1-p_2/q_i)p_2+(1-\alpha)(1-p_2/q_i)p_2,&p_2\ge p_1q_i/q_j.
--   \end{cases}
--   $$
--   Its optimum is the supremum over $0<p_2\le q_i$. The campaign succeeds with probability $\max\{0,1-p_1/q_j\}$. Total expected profit is this probability multiplied by the sum of the funding price and the optimal conditional regular-period profit. The funding-price optimum is the supremum of this total payoff over $p_1\ge T$. The threshold in Proposition 1 is
--   $$
--   \bar p_1=\frac{4q_H-(1-\alpha)q_L-\sqrt{(q_H-q_L)(16q_H-(1-\alpha)^2q_L)}}{8}.
--   $$
--
--   A separating equilibrium has distinct feasible funding prices $p_H,p_L$. Backers believe high quality exactly at $p_H$ and low quality at every other price. Neither type may gain by a feasible deviation. It survives the intuitive criterion when there is no third feasible price that the high type strictly prefers and the low type strictly dislikes if backers believed that deviation signaled high quality.
--
--   These definitions give the one-price lemmas and Proposition 1 a common payoff and equilibrium model.
--
--   **Formalization Note** Success probability is clipped at zero when the funding price exceeds believed quality. The conditional regular-profit formula is used by the theorems only when $p_1<q_j$; at $p_1=q_j$ the conditioning event has probability zero. The low type's full-information optimum and the high type's optimum under a low belief are suprema over feasible prices, not inserted closed forms. The price-commitment mission imports the success-probability function but has its own payoff and parameter structure.
-- source:
--   Bolandifar, Chen, Kouvelis, Zhou, Quality Signaling through Crowdfunding Pricing, SSRN 3689946 (manuscript of 2022-05-30), pp. 9–19, §§3–4.3, (1), (2), (4)–(6)

import Mathlib

namespace CrowdSignal.OnePrice

/-- The qualities, repeat-customer fraction, and financing target in §3. -/
structure Params where
  qL : ℝ
  qH : ℝ
  α : ℝ
  T : ℝ

/-- The parameter restrictions used throughout §§3–4. -/
def Params.Standing (P : Params) : Prop :=
  0 < P.qL ∧ P.qL < P.qH ∧ 0 < P.α ∧ P.α < 1 ∧ 0 < P.T

/-- Conditional regular-period profit, equation (2). -/
noncomputable def rsProfit (P : Params) (qi qj p1 p2 : ℝ) : ℝ :=
  if p2 < p1 * qi / qj then
    P.α * p2 + (1 - P.α) * (1 - p2 / qi) * p2
  else
    P.α / (1 - p1 / qj) * (1 - p2 / qi) * p2 +
      (1 - P.α) * (1 - p2 / qi) * p2

/-- Optimal conditional regular-period profit over positive prices at most true quality. -/
noncomputable def rsOpt (P : Params) (qi qj p1 : ℝ) : ℝ :=
  sSup (rsProfit P qi qj p1 '' Set.Ioc (0 : ℝ) qi)

/-- Campaign success probability at a nonnegative funding price. -/
noncomputable def succ (qj p1 : ℝ) : ℝ := max 0 (1 - p1 / qj)

/-- Total expected profit when true quality is `qi` and believed quality is `qj`. -/
noncomputable def profit (P : Params) (qi qj p1 : ℝ) : ℝ :=
  succ qj p1 * (p1 + rsOpt P qi qj p1)

/-- Optimal expected profit over the feasible funding prices. -/
noncomputable def optProfit (P : Params) (qi qj : ℝ) : ℝ :=
  sSup (profit P qi qj '' Set.Ici P.T)

/-- The lower barred price in Proposition 1. -/
noncomputable def pbar (P : Params) : ℝ :=
  (4 * P.qH - (1 - P.α) * P.qL -
    Real.sqrt ((P.qH - P.qL) * (16 * P.qH - (1 - P.α) ^ 2 * P.qL))) / 8

/-- A pure separating equilibrium with the on-path high price believed high and all
other prices believed low. -/
def IsSepEq (P : Params) (pH pL : ℝ) : Prop :=
  P.T ≤ pH ∧ P.T ≤ pL ∧ pH ≠ pL ∧
  (∀ p, P.T ≤ p → p ≠ pH →
    profit P P.qH P.qL p ≤ profit P P.qH P.qH pH) ∧
  profit P P.qL P.qH pH ≤ profit P P.qL P.qL pL ∧
  (∀ p, P.T ≤ p → p ≠ pH →
    profit P P.qL P.qL p ≤ profit P P.qL P.qL pL)

/-- No off-path price is attractive only to the high type when believed high. -/
def SurvivesIC (P : Params) (pH pL : ℝ) : Prop :=
  ¬ ∃ p, P.T ≤ p ∧ p ≠ pH ∧ p ≠ pL ∧
    profit P P.qH P.qH pH < profit P P.qH P.qH p ∧
    profit P P.qL P.qH p < profit P P.qL P.qL pL

end CrowdSignal.OnePrice


