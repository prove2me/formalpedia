-- Prove2me | Definitions.Def_AdviceBonus_Advisor
-- name    : AdviceBonus_Advisor
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:44:56.609094+00:00
-- url     : https://prove2.me/theorems/17bab636-5e51-4036-958d-52c8985885e4
-- title:
--   The advisor's sequential recommendation problem
-- statement:
--   The advisor makes two recommendations $m_1,m_2\in\{A,B\}$, the second after the first customer has bought.
--
--   **Second recommendation.** If the first customer bought $m_1$ and the second customer's posterior is $q_2$, recommending $m_2$ pays the advisor
--   $$
--   u_2(m_1,q_2,m_2)=f_{m_2}+\mathbf 1[m_2=m_1]\,b_{m_2}+\begin{cases}q_2w,&m_2=A,\\(1-q_2)w,&m_2=B.\end{cases}
--   $$
--   For $m_1=A$ these are $f_A+b_A+q_2w$ and $f_B+(1-q_2)w$ (p.10): the bonus is earned when the same firm makes the second sale.
--
--   **First recommendation.** Recommending $m_1$ to a first customer with posterior $q_1$ pays
--   $$
--   u_1(q_1,m_1)=f_{m_1}+\begin{cases}q_1w,&m_1=A,\\(1-q_1)w,&m_1=B\end{cases}\;+\;V(m_1),\qquad V(m_1)=\int_0^1\max\{u_2(m_1,q,A),u_2(m_1,q,B)\}\,g(q)\,dq,
--   $$
--   where $V(m_1)$ is the expected payoff of optimal advice to the second customer. The second-customer cutoff after $m_1$ is $\bar q^A_2$ for $m_1=A$ and $\bar q^B_2$ for $m_1=B$.
--
--   This is the decision problem whose solution Lemma 1 characterizes by the cutoffs $(\bar q_1,\bar q^A_2,\bar q^B_2)$.
--
--   **Formalization Note** Firms and messages are the two-constructor type `Firm`. The constant $w_l$ is dropped from every payoff. The continuation value is defined as the optimal expected second-stage payoff, not by the paper's $Z^A$, $Z^B$: that these coincide is part of Lemma 1.
-- source:
--   Honda–Inderst–Ottaviani, When Liability is Not Enough, SSRN 4125013 (May 2022), §3, advisor payoffs, pp.10–11

import Mathlib
import Definitions.Def_AdviceBonus_Model

namespace AdviceBonus

/-!
Honda, Inderst, Ottaviani, *When Liability is Not Enough*, SSRN 4125013 (May 2022 version), §3,
pp.10–11: the advisor's sequential recommendation problem, the object of Lemma 1.
-/

/-- The two firms (product providers) `n = A, B`, p.7, which are also the advisor's messages
`m_i ∈ {A, B}`, p.8. -/
inductive Firm
  | A
  | B
  deriving DecidableEq

/-- Firm `n`'s commission `f_n` in the profile `(sA, sB)`. -/
def comm (sA sB : ℝ × ℝ) : Firm → ℝ
  | .A => sA.1
  | .B => sB.1

/-- Firm `n`'s bonus `b_n` in the profile `(sA, sB)`. -/
def bonus (sA sB : ℝ × ℝ) : Firm → ℝ
  | .A => sA.2
  | .B => sB.2

/-- The advisor's expected suitability payoff (net of `w_l`) from recommending product `m` to a
customer with posterior `q`, p.10: `q w` for A and `(1 − q) w` for B (`w = w_h − w_l`). -/
def suit (w q : ℝ) : Firm → ℝ
  | .A => q * w
  | .B => (1 - q) * w

/-- The advisor's payoff from the second recommendation `m₂` when the first customer bought `m₁`
and the second customer's posterior is `q₂`, p.10: the commission `f_{m₂}`, plus the bonus
`b_{m₂}` when `m₂ = m₁` (the second sale of the same firm completes `F(2) = 2f + b`), plus the
suitability payoff. For `m₁ = A` these are `f_A + b_A + q₂ w` and `f_B + (1 − q₂) w` (p.10). -/
def secondPayoff (w : ℝ) (sA sB : ℝ × ℝ) (m₁ : Firm) (q₂ : ℝ) (m₂ : Firm) : ℝ :=
  comm sA sB m₂ + (if m₂ = m₁ then bonus sA sB m₂ else 0) + suit w q₂ m₂

/-- The advisor's optimal expected continuation payoff after the first recommendation `m₁`: the
expectation over the second customer's posterior `q₂ ~ G` of the better of the two second
recommendations. -/
noncomputable def contValue (D : Dist) (w : ℝ) (sA sB : ℝ × ℝ) (m₁ : Firm) : ℝ :=
  ∫ q in (0 : ℝ)..1, max (secondPayoff w sA sB m₁ q .A) (secondPayoff w sA sB m₁ q .B) * D.g q

/-- The advisor's payoff from the first recommendation `m₁` to a customer with posterior `q₁`,
followed by optimal advice to the second customer, p.11: `f_{m₁} + (suitability) + (optimal
continuation)`. -/
noncomputable def firstPayoff (D : Dist) (w : ℝ) (sA sB : ℝ × ℝ) (q₁ : ℝ) (m₁ : Firm) : ℝ :=
  comm sA sB m₁ + suit w q₁ m₁ + contValue D w sA sB m₁

/-- The second-customer cutoff after the first customer bought `m₁`: `q̄^A_2` (2) or `q̄^B_2` (3). -/
noncomputable def cutoff2 (w : ℝ) (sA sB : ℝ × ℝ) : Firm → ℝ
  | .A => q2A w sA sB
  | .B => q2B w sA sB

end AdviceBonus


