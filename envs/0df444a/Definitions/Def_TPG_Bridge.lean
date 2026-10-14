-- Prove2me | Definitions.Def_TPG_Bridge
-- name    : TPG_Bridge
-- status  : Definition
-- author  : @Wenqian Xing
-- created : 2026-10-12T03:47:36.630144+00:00
-- url     : https://prove2.me/theorems/806b3517-4e59-4151-877e-f7274f0117f7
-- title:
--   Expected reward in matrix form, $\rho^\top P^0_{q_0}\cdots P^{t-1}_{q_{t-1}}\,r_{q_t}$
-- statement:
--   For an environment of `TPG_Model` and a sequence $q=(q_t)_{t\ge0}$ of treatment probabilities, `Env.meanReward q t` is the number
--
--   $$m_t(q)=\mu_q^t\,r_{q_t}=\rho^\top P^0_{q_0}P^1_{q_1}\cdots P^{t-1}_{q_{t-1}}\,r_{q_t},$$
--
--   where $P^s_\theta=\theta P^s_1+(1-\theta)P^s_0$, $r_\theta(x)=\theta\,r(x,1)+(1-\theta)\,r(x,0)$ and $r(x,z)=\int y\,R(dy\mid x,z)$. Time is $0$-indexed.
--
--   It is the expected reward $\mathbb E_q[Y_t]$ at time $t$ when the action at time $s$ is treatment with probability $q_s$ (a separate lemma proves this), written in the matrix form used throughout the source's proofs. It is affine in each $q_s$ with $s\le t$ and does not depend on $q_s$ for $s>t$.
-- source:
--   Johari, Peng, Xing, Estimation of Treatment Effects Under Nonstationarity via the Truncated Policy Gradient Estimator, revised manuscript of October 2026 (revision of arXiv:2506.05308v3, https://arxiv.org/abs/2506.05308); numbering follows the revised manuscript. Auxiliary statement, not a numbered result of the paper: it is the matrix expression ρ^⊤ P_θ^{1→t} r_θ of Appendix G.1, p. 42 (proof of Proposition 1), for a time-varying sequence of treatment probabilities.

import Mathlib
import Definitions.Def_TPG_Model
import Definitions.Def_TPG_Markov

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace TPG

/-- Expected reward at time `t` when the action at time `s` is treatment with probability `q s`,
in matrix form: `ρᵀ P_{q_0}^0 ⋯ P_{q_{t-1}}^{t-1} r_{q_t}`. -/
noncomputable def Env.meanReward {S : Type} [Fintype S] [DecidableEq S] (E : Env S)
    (q : ℕ → ℝ) (t : ℕ) : ℝ :=
  dotProduct (E.stateVec q t) (E.rMix (q t))

end TPG


