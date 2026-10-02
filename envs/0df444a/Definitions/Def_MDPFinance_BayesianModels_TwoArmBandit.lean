-- Prove2me | Definitions.Def_MDPFinance_BayesianModels_TwoArmBandit
-- name    : MDPFinance_BayesianModels_TwoArmBandit
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:18:35.918395+00:00
-- url     : https://prove2.me/theorems/0b870e81-f871-4d38-b9e2-19fd412565a0
-- title:
--   The two-unknown-arms Bernoulli bandit's value function (Section 5.5)
-- statement:
--   This definition packages the concrete finite-state Markov Decision Model Bäuerle and
--   Rieder reduce the two-unknown-arms Bernoulli bandit to (p. 167-168), the setting for Theorem
--   5.5.1: two arms, each with an unknown Bernoulli success probability, played sequentially.
--
--   Applying Example 5.4.4(ii) to both arms, the information state is $x = (m_1,n_1,m_2,n_2) \in
--   \mathbb N_0^4$, the number of successes/failures observed at each arm, and the posterior mean
--   success probability at arm $a$ is $p_a(x) := (m_a+1)/(m_a+n_a+2)$. Choosing arm $a$ and observing
--   success/failure moves $x$ to $x + e_{2a-1}$/$x+e_{2a}$ respectively; the averaging operators are
--   $$
--   (Q_1v)(x) := p_1(x)v(x+e_1) + (1-p_1(x))v(x+e_2), \qquad
--   (Q_2v)(x) := p_2(x)v(x+e_3) + (1-p_2(x))v(x+e_4).
--   $$
--
--   The value function with $n$ stages remaining satisfies
--   $$
--   J_n(x) = \max_{a=1,2}\big[p_a(x) + \beta (Q_aJ_{n-1})(x)\big], \qquad J_0 \equiv 0,
--   $$
--   and $d_k := p_2 + \beta Q_2 J_{k-1} - p_1 - \beta Q_1 J_{k-1}$ (Theorem 5.5.1's own notation).
--   `VpiB` is the value of a general Markov policy through this same recursion, used to state
--   Theorem 5.5.1's optimality claim.
--
--   **Formalization Note.** Since $E$ is countable and $A$ is finite here, the book notes SAN holds
--   automatically and this recursion is exactly the (unique) true value function — no separate
--   appeal to the general apparatus of Theorem 2.3.8/5.4.8 is needed to state it.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 167-168, p. 167-168 (unnumbered, underlies Theorem 5.5.1)

import Mathlib

namespace MDPFinance.BayesianModels

/-- The two-unknown-arms Bernoulli bandit's information state (Bäuerle–Rieder, p. 167-168, PDF
180-181): `x = (m_1,n_1,m_2,n_2)` records the number of successes/failures observed so far at
arm 1 and arm 2 (via the sufficient statistic of Example 5.4.4(ii) applied to both arms). -/
abbrev BanditState2 := ℕ × ℕ × ℕ × ℕ

/-- The unit vectors `e_1,e_2,e_3,e_4` of `ℕ^4` recording a success/failure at arm 1/arm 2
(Bäuerle–Rieder, p. 167, PDF 180). -/
def bE1 : BanditState2 := (1, 0, 0, 0)

def bE2 : BanditState2 := (0, 1, 0, 0)

def bE3 : BanditState2 := (0, 0, 1, 0)

def bE4 : BanditState2 := (0, 0, 0, 1)

/-- Pointwise addition on `BanditState2`. -/
def badd (x y : BanditState2) : BanditState2 :=
  (x.1 + y.1, x.2.1 + y.2.1, x.2.2.1 + y.2.2.1, x.2.2.2 + y.2.2.2)

/-- `p_1(x) := (m_1+1)/(m_1+n_1+2)`, the posterior mean success probability at arm 1
(Bäuerle–Rieder, p. 167, PDF 180: `\hat Q^Z(\{1\}|x,a) = \dots =: p_a(x)`, specialized to
`a = 1`). -/
noncomputable def p1B (x : BanditState2) : ℝ := (x.1 + 1) / (x.1 + x.2.1 + 2)

/-- `p_2(x) := (m_2+1)/(m_2+n_2+2)`, the posterior mean success probability at arm 2. -/
noncomputable def p2B (x : BanditState2) : ℝ := (x.2.2.1 + 1) / (x.2.2.1 + x.2.2.2 + 2)

/-- `(Q_1 v)(x) := p_1(x) v(x+e_1) + (1-p_1(x)) v(x+e_2)` (Bäuerle–Rieder, p. 167, PDF 180). -/
noncomputable def Q1B (v : BanditState2 → ℝ) (x : BanditState2) : ℝ :=
  p1B x * v (badd x bE1) + (1 - p1B x) * v (badd x bE2)

/-- `(Q_2 v)(x) := p_2(x) v(x+e_3) + (1-p_2(x)) v(x+e_4)` (Bäuerle–Rieder, p. 167, PDF 180). -/
noncomputable def Q2B (v : BanditState2 → ℝ) (x : BanditState2) : ℝ :=
  p2B x * v (badd x bE3) + (1 - p2B x) * v (badd x bE4)

/-- `J_n(x) := max_{a=1,2} [p_a(x) + β (Q_a J_{n-1})(x)]`, `J_0 ≡ 0` (Bäuerle–Rieder, p. 167,
PDF 180), the value function of the two-unknown-arms bandit with `n` stages remaining. -/
noncomputable def JB (β : ℝ) : ℕ → BanditState2 → ℝ
  | 0, _ => 0
  | (n + 1), x => max (p1B x + β * Q1B (JB β n) x) (p2B x + β * Q2B (JB β n) x)

/-- `d_k := p_2 + β Q_2 J_{k-1} - p_1 - β Q_1 J_{k-1}`, `k ∈ ℕ` (Bäuerle–Rieder, Theorem 5.5.1,
p. 168, PDF 181). -/
noncomputable def dB (β : ℝ) : ℕ → BanditState2 → ℝ
  | 0, _ => 0
  | (n + 1), x => p2B x + β * Q2B (JB β n) x - p1B x - β * Q1B (JB β n) x

/-- The expected total reward `V_n^f(x)` of a (Markov) policy `f : ℕ → BanditState2 → Fin 2`
(`f k` the decision rule used when `k` stages remain; `0` = arm 1, `1` = arm 2) over `n` further
stages from `x`, in the two-unknown-arms bandit, `β`-discounted. -/
noncomputable def VpiB (β : ℝ) (f : ℕ → BanditState2 → Fin 2) : ℕ → BanditState2 → ℝ
  | 0, _ => 0
  | (n + 1), x =>
      if f (n + 1) x = 0 then p1B x + β * Q1B (VpiB β f n) x
      else p2B x + β * Q2B (VpiB β f n) x

end MDPFinance.BayesianModels


