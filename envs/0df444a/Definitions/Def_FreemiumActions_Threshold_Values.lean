-- Prove2me | Definitions.Def_FreemiumActions_Threshold_Values
-- name    : FreemiumActions_Threshold_Values
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T08:58:47.057614+00:00
-- url     : https://prove2.me/theorems/57839e59-a766-46eb-b06f-a6bf30aa0c65
-- title:
--   Infinite-horizon visits, policy values, and optimality
-- statement:
--   For every stationary policy $y$, let $S_y$ be its transient transition matrix and define
--   $$n_y(e,j)=\sum_{t=0}^{\infty}(S_y^t)_{e,j},\qquad W_y(e)=\sum_{j\in E}n_y(e,j)r(j,y(j)).$$
--   The starting visit is included. Matrix powers and sums are evaluated in the extended nonnegative reals, with real transition entries and rewards embedded by $\max(0,x)$. Under the standing model assumptions all embedded inputs are already nonnegative and positive quitting makes every count and value finite.
--
--   The optimal value $W(e)$ is the maximum over all stationary policies. The constrained value $W(e,y=u)$ is the maximum over all stationary policies taking action $u$ whenever they visit $e$, with their choices elsewhere unrestricted. Each policy set is finite and nonempty, so the indexed supremum is attained. A policy is optimal if it weakly dominates every stationary policy at every initial engagement level. No Bellman equation, threshold condition, visit formula or monotonicity is assumed in these definitions.
-- source:
--   Sheng, Ryan and Nagarajan, Incentivized actions in freemium games, supplied source.pdf dated October 8, 2016, §3.2, p. 11 (PDF p. 11), equations (7)–(9); §5, p. 17 (PDF p. 17); A.1, p. 29 (PDF p. 29), equations (33)–(35); catalog DOI 10.1287/msom.2020.0925.

import Definitions.Def_FreemiumActions_Threshold_Dynamics

open scoped ENNReal

namespace FreemiumActions.Threshold

noncomputable def visits {N : ℕ} (d : Data N) (y : Policy N)
    (e f : Level N) : ℝ≥0∞ :=
  ∑' t : ℕ, ((fun i j => ENNReal.ofReal (transient d y i j)) ^ t :
    Matrix (Level N) (Level N) ℝ≥0∞) e f

noncomputable def policyValue {N : ℕ} (d : Data N) (y : Policy N)
    (e : Level N) : ℝ≥0∞ :=
  ∑ f : Level N, visits d y e f * ENNReal.ofReal (reward d f (y f))

noncomputable def optimalValue {N : ℕ} (d : Data N) (e : Level N) : ℝ≥0∞ :=
  ⨆ y : Policy N, policyValue d y e

noncomputable def constrainedValue {N : ℕ} (d : Data N)
    (e : Level N) (u : Bool) : ℝ≥0∞ :=
  ⨆ y : {y : Policy N // y e = u}, policyValue d y.val e

def IsOptimal {N : ℕ} (d : Data N) (y : Policy N) : Prop :=
  ∀ z : Policy N, ∀ e : Level N, policyValue d z e ≤ policyValue d y e

end FreemiumActions.Threshold


