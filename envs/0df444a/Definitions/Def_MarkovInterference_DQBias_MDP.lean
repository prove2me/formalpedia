-- Prove2me | Definitions.Def_MarkovInterference_DQBias_MDP
-- name    : MarkovInterference_DQBias_MDP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T01:18:55.171758+00:00
-- url     : https://prove2.me/theorems/d8b4ee0c-dd37-4f8c-96db-aa1f97164245
-- title:
--   Two-action average-reward MDP and idealized differences-in-Q value
-- statement:
--   A finite Markov decision process has actions $0$ (control) and $1$ (intervention), a transition matrix $P_a$ for each action, and real rewards $r(s,a)$. Each $P_a$ is row stochastic. The experiment assigns either action with probability one half at every state, giving $P_{1/2}=(P_0+P_1)/2$ and $r_{1/2}=(r_0+r_1)/2$.
--
--   At a stationary law $\rho_{1/2}$, the average reward is $\bar r=\rho_{1/2}^{\top}r_{1/2}$. The relative value $V_{1/2}(s)$ sums expected rewards in excess of $\bar r$ under the experiment. The state-action value $Q_{1/2}(s,a)$ takes action $a$ first and then follows the experiment. The population differences-in-Q value and average treatment effect are
--
--   $$D=\sum_s\rho_{1/2}(s)[Q_{1/2}(s,1)-Q_{1/2}(s,0)],\qquad \mathrm{ATE}=\rho_1^{\top}r_1-\rho_0^{\top}r_0.$$
--
--   The largest absolute reward is $r_{\max}=\max_{s,a}|r(s,a)|$. These definitions make the paper's idealized estimator and estimand available to the goal theorem.
--
--   **Formalization Note** $V$ and $Q$ are sums of expected excess rewards, the interpretation used in §3.3. Lean's total infinite sum returns zero if a series is not summable; the goal's mixing hypothesis guarantees convergence, and a milestone states it explicitly for $V$.
-- source:
--   Farias, Li, Peng, Zheng, Markovian Interference in Experiments, arXiv:2206.02371v2, pp. 9–11, 13, §2, §3.1 and §3.3

import Mathlib
import Definitions.Def_MarkovInterference_DQBias_Chain

namespace MarkovInterference.DQBias

/-- The two-action finite MDP of §2: actions `0` and `1` have stochastic transition matrices. -/
structure MDP (S : Type) [Fintype S] where
  P : Fin 2 → Matrix S S ℝ
  r : S → Fin 2 → ℝ
  stoch : ∀ a, IsStochastic (P a)

namespace MDP

variable {S : Type} [Fintype S] [DecidableEq S] (M : MDP S)

/-- The transition matrix of the half-randomized policy. -/
noncomputable def Phalf : Matrix S S ℝ :=
  (1 / 2 : ℝ) • (M.P 0 + M.P 1)

/-- The reward vector under a fixed action. -/
def rvec (a : Fin 2) : S → ℝ := fun s => M.r s a

/-- The reward vector under the half-randomized policy. -/
noncomputable def rHalf : S → ℝ := fun s => (M.r s 0 + M.r s 1) / 2

/-- The average reward of the half-randomized policy at its stationary law. -/
noncomputable def avgReward (rho : S → ℝ) : ℝ :=
  rho ⬝ᵥ M.rHalf

/-- The relative value is the sum of expected rewards in excess of the average reward. -/
noncomputable def V (rho : S → ℝ) (s : S) : ℝ :=
  ∑' t : ℕ, (M.Phalf ^ t).mulVec M.rHalf s - M.avgReward rho

/-- After a forced first action, follow the half-randomized policy. -/
noncomputable def Q (rho : S → ℝ) (s : S) (a : Fin 2) : ℝ :=
  (M.r s a - M.avgReward rho) +
    ∑' t : ℕ, (M.P a * M.Phalf ^ t).mulVec M.rHalf s - M.avgReward rho

/-- The population value of the idealized differences-in-Q estimator. -/
noncomputable def dqMean (rho : S → ℝ) : ℝ :=
  ∑ s, rho s * (M.Q rho s 1 - M.Q rho s 0)

/-- The average treatment effect, expressed through the two stationary laws. -/
noncomputable def ate (rho0 rho1 : S → ℝ) : ℝ :=
  rho1 ⬝ᵥ M.rvec 1 - rho0 ⬝ᵥ M.rvec 0

/-- The largest absolute reward across states and actions. -/
noncomputable def rmax : ℝ :=
  ⨆ s, ⨆ a, |M.r s a|

end MDP
end MarkovInterference.DQBias


