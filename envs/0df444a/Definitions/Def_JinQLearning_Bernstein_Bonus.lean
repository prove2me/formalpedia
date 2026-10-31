-- Prove2me | Definitions.Def_JinQLearning_Bernstein_Bonus
-- name    : JinQLearning_Bernstein_Bonus
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T14:32:46.382886+00:00
-- url     : https://prove2.me/theorems/5ed088f8-cb8a-4397-a40d-43afd3fbd5af
-- title:
--   Historical empirical variance and UCB-Bernstein bonuses
-- statement:
--   Let iota=log(S A K H / p). For the list of observed next-state values Y_1,...,Y_t at a fixed state-action-stage triple, W_t is sum(Y_i^2)/t-(sum(Y_i)/t)^2. Set W_0=beta_0=0. For t>0, beta_t=min{c1[sqrt((H/t)(W_t+H)iota)+sqrt(H^7 S A)iota/t],c2 sqrt(H^3 iota/t)}. The bonus for a new observation is [beta_t-(1-alpha_t)beta_{t-1}]/(2alpha_t), with the published alpha_t=(H+1)/(H+t); this gives b_1=beta_1/2. The new observation is included before computing beta_t. Reading: use (C.1)-(C.3), explicitly invoked by Theorem 2, rather than Algorithm 2 line 10's inconsistent expression (sigma-mu^2)/t. The discrepancy is insight I1. Logs in the targets have positive argument and p lies in (0,1).
-- source:
--   Jin, Allen-Zhu, Bubeck & Jordan, Is Q-learning Provably Efficient?, arXiv:1807.03765v1, p. 15, equations (C.1)–(C.3).

import Definitions.Def_VLearning_CCE_WeightedBandit

open scoped BigOperators
noncomputable section

namespace JinQLearning.Bernstein

/-- The log is evaluated only at positive S,A,H,K and 0 < p < 1 in the targets. -/
def iota (S A H K : ℕ) (p : ℝ) : ℝ := Real.log ((S : ℝ) * A * (K * H) / p)

/-- Raw sums of the values recorded at the time of each visit; the empty variance is 0. -/
def empiricalVariance (ys : List ℝ) : ℝ :=
  if ys = [] then 0 else
    (ys.map (fun y => y ^ 2)).sum / (ys.length : ℝ) - (ys.sum / (ys.length : ℝ)) ^ 2

/-- Equations (C.1)-(C.2), with β₀=0. -/
def beta (S A H : ℕ) (c₁ c₂ ℓ : ℝ) (ys : List ℝ) : ℝ :=
  if ys = [] then 0 else
    min (c₁ * (Real.sqrt ((H : ℝ) / ys.length * (empiricalVariance ys + H) * ℓ) +
      Real.sqrt ((H : ℝ) ^ 7 * S * A) * ℓ / ys.length))
      (c₂ * Real.sqrt ((H : ℝ) ^ 3 * ℓ / ys.length))

/-- The bonus for appending y, including the first visit, equation (C.3). -/
def bonus (S A H : ℕ) (c₁ c₂ ℓ : ℝ) (ys : List ℝ) (y : ℝ) : ℝ :=
  (beta S A H c₁ c₂ ℓ (ys ++ [y]) -
    (1 - VLearning.CCE.lr H (ys.length + 1)) * beta S A H c₁ c₂ ℓ ys) /
      (2 * VLearning.CCE.lr H (ys.length + 1))

end JinQLearning.Bernstein


