-- Prove2me | Definitions.Def_MinimaxRegretRL_Bernstein_MDP
-- name    : MinimaxRegretRL_Bernstein_MDP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T16:07:42.480964+00:00
-- url     : https://prove2.me/theorems/e5156b59-df4c-4625-b928-1417233a5415
-- title:
--   Finite stationary MDP, policies, and values (§2; Assumption 1)
-- statement:
--   Let $\mathcal S$ and $\mathcal A$ be nonempty finite sets. An MDP has a stationary transition probability $P(y\mid x,a)$ on $\mathcal S$ for each state $x$ and action $a$, and a known deterministic reward $R(x,a)\in[0,1]$.
--
--   A deterministic policy $\pi$ selects an action for each state and each of the $H$ steps. Its value $V_h^\pi(x)$ is the expected sum of rewards from step $h$ through the final step; $V_{H+1}^\pi=0$. The optimal value is the supremum over all these policies, $V_h^*(x)=\sup_\pi V_h^\pi(x)$. The file also defines transition expectations and variances as finite sums.
--
--   These definitions supply the model and the comparison value in Theorem 2.
--
--   **Formalization Note** Steps are indexed $0,\ldots,H-1$ in Lean. The stationary transition predicate is the published `IsTransitionKernel` definition.
-- source:
--   Azar, Osband and Munos, Minimax Regret Bounds for Reinforcement Learning, arXiv:1703.05449v2 (2017), pp. 2–3, §2 and Assumption 1

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_MinimaxRegretRL_Bernstein_FiniteVariance
import Definitions.Def_MinimaxRegretRL_Hoeffding_MDP

open scoped Classical

namespace MinimaxRegretRL.Bernstein

variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]

/-- The value of a policy at a step, with value zero at and after step H. -/
noncomputable def valueAt (M : MinimaxRegretRL.Hoeffding.MDP S A) {H : ℕ} (π : MinimaxRegretRL.Hoeffding.Policy S A H) : ℕ → S → ℝ
  | h, x =>
    if hh : h < H then
      let a := π x ⟨h, hh⟩
      M.R x a + ∑ y : S, M.P x a y * valueAt M π (h + 1) y
    else 0
  termination_by h => H - h
  decreasing_by all_goals omega

/-- The paper's literal supremum over deterministic nonstationary policies. -/
noncomputable def optimalValue (M : MinimaxRegretRL.Hoeffding.MDP S A) (H : ℕ) (h : ℕ) (x : S) : ℝ :=
  ⨆ π : MinimaxRegretRL.Hoeffding.Policy S A H, valueAt M π h x

/-- Finite-distribution expectation under one transition row. -/
def transitionExp (M : MinimaxRegretRL.Hoeffding.MDP S A) (x : S) (a : A) (f : S → ℝ) : ℝ :=
  finiteExp (M.P x a) f

/-- Finite-distribution variance under one transition row. -/
def transitionVar (M : MinimaxRegretRL.Hoeffding.MDP S A) (x : S) (a : A) (f : S → ℝ) : ℝ :=
  finiteVar (M.P x a) f

end MinimaxRegretRL.Bernstein


