-- Prove2me | Definitions.Def_CrowdSignal_TwoPrice_Setting
-- name    : CrowdSignal_TwoPrice_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-16T08:03:35.369665+00:00
-- url     : https://prove2.me/theorems/c0c6691b-8784-47ea-921c-9f60cf58c06b
-- title:
--   §§3, 5, pp. 9–24 — the two-price crowdfunding signaling game
-- statement:
--   Let $0<q_L<q_H$ be the low and high product qualities, $0<\alpha<1$ the share of returning customers, and $T>0$ the financing target. A committed price pair $x=(P_1,P_2)$ is feasible when $P_1\ge T$ and $P_2>0$. The funding campaign succeeds with probability $\max\{0,1-P_1/q_j\}$ when customers believe quality is $q_j$. After success, true quality $q_i$ is revealed. Returning customers buy for sure if $P_2\le P_1q_i/q_j$; otherwise their conditional purchase probability is $\max\{0,(1-P_2/q_i)/(1-P_1/q_j)\}$. Independent customers buy with probability $\max\{0,1-P_2/q_i\}$.
--
--   The expected payoff $\Pi^{ij}(x)$ is the campaign success probability times the funding price plus the expected regular-period revenue from these two customer groups. The printed expressions $V^{ij}$ and $W^{ij}$ describe its two regular-demand regions. Write $\Pi^{ij*}$ for the supremum of $\Pi^{ij}$ over feasible pairs.
--
--   In a pure separating equilibrium, the high and low types choose different feasible pairs $x_H$ and $x_L$. Customers believe high quality exactly at $x_H$ and low quality at every other pair; neither type profits from a unilateral deviation. The intuitive criterion excludes an equilibrium if an off-path feasible pair, when believed high, strictly benefits the high type and strictly reduces the low type's payoff.
--
--   These definitions provide the common game and optimization objects for Lemmas 4 and 6 and Proposition 2.
--
--   **Formalization Note** Market sizes are one, marginal cost and salvage value are zero, and the second-period discount factor is one, as in the manuscript. The prior belief does not enter these separating-equilibrium statements. Success and demand probabilities are clipped at zero outside the domains of the printed formulas. $V^{ij}$ and $W^{ij}$ are retained exactly as printed for the equation and optimization on p. 41; the game payoff uses the clipped formula on all feasible prices. The strict low-type comparison follows Appendix D.1's equilibrium-dominance test.
-- source:
--   Bolandifar, Chen, Kouvelis, Zhou, Quality Signaling through Crowdfunding Pricing, SSRN 3689946 (manuscript of 2022-05-30), pp. 9–13, 19, 22–24, (7)–(10)

import Mathlib
import Definitions.Def_CrowdSignal_OnePrice_Setting

namespace CrowdSignal.TwoPrice

/-- The two qualities, the returning-customer share, and the financing target. -/
structure Params where
  qL : ℝ
  qH : ℝ
  α : ℝ
  T : ℝ

/-- The standing parameter assumptions of §§3 and 5. -/
def Params.Standing (P : Params) : Prop :=
  0 < P.qL ∧ P.qL < P.qH ∧ 0 < P.α ∧ P.α < 1 ∧ 0 < P.T

/-- The expression V^{ij} in §5, for sure purchases by returning customers. -/
noncomputable def V (P : Params) (qi qj P1 P2 : ℝ) : ℝ :=
  (1 - P1 / qj) * (P1 + P.α * P2 + (1 - P.α) * (1 - P2 / qi) * P2)

/-- The expression W^{ij} in §5, for conditional purchases by returning customers. -/
noncomputable def W (P : Params) (qi qj P1 P2 : ℝ) : ℝ :=
  (1 - P1 / qj) *
    (P1 + P.α / (1 - P1 / qj) * (1 - P2 / qi) * P2 +
      (1 - P.α) * (1 - P2 / qi) * P2)

/-- Probability of purchase by a returning customer, conditional on success. -/
noncomputable def buyA (qi qj P1 P2 : ℝ) : ℝ :=
  if P2 ≤ P1 * qi / qj then 1
  else max 0 ((1 - P2 / qi) / (1 - P1 / qj))

/-- The expected two-period payoff Π^{ij}, including the campaign success event. -/
noncomputable def payoff (P : Params) (qi qj : ℝ) (x : ℝ × ℝ) : ℝ :=
  CrowdSignal.OnePrice.succ qj x.1 *
    (x.1 + P.α * x.2 * buyA qi qj x.1 x.2 +
      (1 - P.α) * x.2 * max 0 (1 - x.2 / qi))

/-- Feasible committed prices: funding covers the target; the regular price is positive. -/
def Feas (P : Params) (x : ℝ × ℝ) : Prop := P.T ≤ x.1 ∧ 0 < x.2

/-- The maximum expected payoff over all feasible price pairs. -/
noncomputable def optPayoff (P : Params) (qi qj : ℝ) : ℝ :=
  sSup (payoff P qi qj '' {x | Feas P x})

/-- A pure separating equilibrium with high belief exactly at the high type's pair. -/
def IsSepEq2 (P : Params) (xH xL : ℝ × ℝ) : Prop :=
  Feas P xH ∧ Feas P xL ∧ xH ≠ xL ∧
    (∀ x : ℝ × ℝ, Feas P x → x ≠ xH →
      payoff P P.qH P.qL x ≤ payoff P P.qH P.qH xH) ∧
    payoff P P.qL P.qH xH ≤ payoff P P.qL P.qL xL ∧
    (∀ x : ℝ × ℝ, Feas P x → x ≠ xH →
      payoff P P.qL P.qL x ≤ payoff P P.qL P.qL xL)

/-- The p. 19 intuitive-criterion test applied to committed price pairs. -/
def SurvivesIC2 (P : Params) (xH xL : ℝ × ℝ) : Prop :=
  ¬ ∃ x : ℝ × ℝ, Feas P x ∧ x ≠ xH ∧ x ≠ xL ∧
    payoff P P.qH P.qH xH < payoff P P.qH P.qH x ∧
    payoff P P.qL P.qH x < payoff P P.qL P.qL xL

end CrowdSignal.TwoPrice


