-- Prove2me | Definitions.Def_KallenbergLP_Bias_Stationary
-- name    : KallenbergLP_Bias_Stationary
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T11:04:14.678102+00:00
-- url     : https://prove2.me/theorems/3c05dbe0-5c89-4273-b58d-641ea880fa0d
-- title:
--   Stationary, deviation, gain, and bias matrices for a pure stationary policy
-- statement:
--   A pure stationary rule $f$ gives a stochastic transition matrix $P(f)_{ij}=p_{i,f(i),j}$ and reward vector $r(f)_i=r_{i,f(i)}$. Its **stationary matrix** is the Cesàro limit $P^*(f)$ of the powers of $P(f)$, and its **deviation matrix** is
--
--   $$
--   D(f)=\bigl(I-P(f)+P^*(f)\bigr)^{-1}-P^*(f).
--   $$
--
--   The **gain** and **bias** vectors are $\phi(f^\infty)=P^*(f)r(f)$ and $u(f^\infty)=D(f)r(f)$. The file also defines the average over horizons of the cumulative difference in expected period rewards of two pure stationary policies, the expression in Theorem 5.2.2(iv). The Cesàro limit and deviation matrix are imported from the published Blackwell matrix definitions, whose formulas are identical to Kallenberg's.
--
--   These matrices give the finite-chain quantities used in the bias comparison and connect the chapter's discounted and average reward criteria.
--
--   **Formalization Note** The Cesàro limit exists and $I-P+P^*$ is nonsingular for a finite stochastic matrix by Theorem 2.4.1. Mathlib's total limit and inverse operations are used in these definitions only on those valid matrices. Period $t$ is represented by index $t-1$ in the finite sums; the totalized $T=0$ average does not affect the limit.
-- source:
--   Kallenberg, Linear Programming and Finite Markovian Control Problems, Mathematical Centre Tracts 148, Mathematisch Centrum, Amsterdam 1983, p. 29, Theorem 2.4.1 and Definition 2.4.2; pp. 33–34, equations (2.5.3)–(2.5.6); pp. 164–165, Theorem 5.2.2(iv); https://ir.cwi.nl/pub/13008

import Definitions.Def_KallenbergLP_Bias_Criteria
import Definitions.Def_BlackwellDiscreteDP_NearOne_LimitMatrix

open Filter Matrix BlackwellDiscreteDP.NearOne

namespace KallenbergLP.Bias

variable {N : ℕ} {α : Type} [Fintype α] [DecidableEq α]

/-- The transition matrix under a pure stationary rule. -/
def stationaryMatrix (M : MDP N α) (f : PureRule M) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => M.transition i (f.choose i) j

/-- The one-period reward vector under a pure stationary rule. -/
def stationaryReward (M : MDP N α) (f : PureRule M) : Fin N → ℝ :=
  fun i => M.reward i (f.choose i)

/-- The average-reward vector φ(f∞) = P*(f) r(f), equation (2.5.4). -/
noncomputable def gain (M : MDP N α) (f : PureRule M) (i : Fin N) : ℝ :=
  ∑ j : Fin N,
    BlackwellDiscreteDP.NearOne.limitMatrix (stationaryMatrix M f) i j * stationaryReward M f j

/-- The bias vector u(f∞) = D(f) r(f), equation (2.5.5). -/
noncomputable def bias (M : MDP N α) (f : PureRule M) (i : Fin N) : ℝ :=
  ∑ j : Fin N,
    BlackwellDiscreteDP.NearOne.deviationMatrix (stationaryMatrix M f) i j *
      stationaryReward M f j

/-- The average over horizons `1,...,T` of cumulative period-reward differences. -/
noncomputable def cesaroRewardDifference (M : MDP N α)
    (f g : PureRule M) (i : Fin N) (T : ℕ) : ℝ :=
  (T : ℝ)⁻¹ *
    ∑ t ∈ Finset.range T,
      ∑ s ∈ Finset.range (t + 1),
        (periodReward M (purePolicy M f) i s - periodReward M (purePolicy M g) i s)

end KallenbergLP.Bias


