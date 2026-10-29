-- Prove2me | Definitions.Def_PutermanMDP_MarkovPolicies_RewardCriteria
-- name    : PutermanMDP_MarkovPolicies_RewardCriteria
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T02:30:16.551579+00:00
-- url     : https://prove2.me/theorems/32488c1c-1053-44cc-9916-7e5513a3f805
-- title:
--   Bounded reward criteria and randomized one-step evaluation
-- statement:
--   For a stationary model, write $m_n^{\pi,\mu}$ for its state-action marginal at epoch $n+1$. Under the uniform bound $|r(s,a)|\le C$ on available actions, define the expected stage reward $e_n=\sum_{j,a}m_n^{\pi,\mu}(j,a)r(j,a)$, the return $R_N=\sum_{n=0}^{N-1}e_n$ with zero terminal reward, and
--   $$V_\beta=\sum_{n=0}^\infty\beta^ne_n,\qquad
--   G_\beta=\sum_{n=0}^\infty(1-\beta)\beta^nR_{n+1}.$$
--   For $0\le\beta<1$, $G_\beta$ is the expected return over an independent geometric number of reward periods, supported on $1,2,\ldots$. The space $V$ consists of real functions $u$ having a uniform finite bound. For a randomized Markov decision rule $d$, the one-step operator is
--   $$T_du(s)=\sum_{a\in A_s}d_s(a)\left[r(s,a)+\beta\sum_jp(j\mid s,a)u(j)\right].$$
--
--   The definitions connect discrete distributions with the bounded reward criteria and operator notation used in Chapter 5.
--
--   **Formalization Note** The book's discount factor $\lambda$ is called $\beta$ in Lean. These real series are used in theorem statements only with bounded rewards, bounded $u$ where applicable, and the stated discount domain. Outside those domains Lean's total `tsum` can return zero for a nonsummable family; no probabilistic meaning is asserted there. $R_N$ is the book's $v_{N+1}$ with zero terminal reward. These definitions do not define unbounded total or average reward.
-- source:
--   Puterman, Markov Decision Processes, Wiley, 1994, pp. 120–121, 125–126, 137–138 (PDF 136–137, 141–142, 153–154), Eqs. (5.1.3)–(5.1.4), (5.3.1), (5.6.1)–(5.6.2)

import Mathlib
import Definitions.Def_PutermanMDP_MarkovPolicies_Model

namespace PutermanMDP.MarkovPolicies

/-- Equation (5.1.4), restricted to the available actions. -/
def RewardBounded {S A : Type*} (M : Model S A) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ s a, a ∈ M.actions s → |M.reward s a| ≤ C

/-- The space V of bounded real-valued functions; the bound is uniform in s. -/
def BoundedValue {S : Type*} (u : S → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ s, |u s| ≤ C

/-- Expected reward at epoch n+1. Used below only under RewardBounded. -/
noncomputable def expectedReward {S A : Type*} (M : Model S A)
    (π : HistoryPolicy M) (μ : PMF S) (n : ℕ) : ℝ :=
  ∑' z : S × A, (stateActionLaw M π μ n z).toReal * M.reward z.1 z.2

/-- Expected return for n reward periods, with zero terminal reward (v_(n+1)). -/
noncomputable def finiteReturn {S A : Type*} (M : Model S A)
    (π : HistoryPolicy M) (μ : PMF S) (n : ℕ) : ℝ :=
  ∑ t ∈ Finset.range n, expectedReward M π μ t

/-- Equation (5.1.3), in the bounded-reward regime where the series converges. -/
noncomputable def discountedReturn {S A : Type*} (M : Model S A)
    (π : HistoryPolicy M) (μ : PMF S) (β : ℝ) : ℝ :=
  ∑' n : ℕ, β ^ n * expectedReward M π μ n

/-- Equation (5.3.1) for an independent horizon with P(ν=n+1)=(1-β)β^n.
The outer expectation averages the fixed-horizon returns, so the horizon is independent. -/
noncomputable def geometricReturn {S A : Type*} (M : Model S A)
    (π : HistoryPolicy M) (μ : PMF S) (β : ℝ) : ℝ :=
  ∑' n : ℕ, ((1 - β) * β ^ n) * finiteReturn M π μ (n + 1)

/-- The one-step reward r_d + β P_d u in (5.6.1)--(5.6.2). -/
noncomputable def oneStep {S A : Type*} (M : Model S A)
    (d : (s : S) → PMF {a : A // a ∈ M.actions s}) (β : ℝ) (u : S → ℝ)
    (s : S) : ℝ :=
  ∑' a : {a : A // a ∈ M.actions s}, (d s a).toReal *
    (M.reward s a.val + β * ∑' j : S, (M.transition s a j).toReal * u j)

end PutermanMDP.MarkovPolicies


