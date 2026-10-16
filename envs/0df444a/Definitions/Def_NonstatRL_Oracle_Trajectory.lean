-- Prove2me | Definitions.Def_NonstatRL_Oracle_Trajectory
-- name    : NonstatRL_Oracle_Trajectory
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-16T04:28:30.991995+00:00
-- url     : https://prove2.me/theorems/8b02d561-f2f4-4edc-81d8-0f3f0ac35a24
-- title:
--   §2.2 — nonstationary trajectory law and cumulative expected mean reward
-- statement:
--   Fix a sequence of MDPs $M_1,M_2,\ldots$, an initial state $s_1$, and a randomized policy whose action distribution may depend on the full earlier state–action history and current state. The trajectory law starts at $s_1$, samples each action from that policy, and samples the next state using the transition distribution of the MDP for the current round. A policy is allowed when it assigns probability zero to unavailable actions at every state and history.
--
--   The expected cumulative mean reward is
--
--   $$\mathbb E^\pi_{s_1}\!\left[\sum_{t=1}^{T}r_t(s_t,a_t)\right].$$
--
--   This law is the probability space used in the window and horizon inequalities, so the transition at round $t$ uses $p_t$ and the summand uses $r_t$.
--
--   **Formalization Note** The paper's time $t\in\{1,\ldots,T\}$ is Lean index $t-1$. The policy here observes state–action history, while the paper also permits past sampled rewards. Taking the conditional distribution of each action given the state–action history gives the same state–action trajectory law for such a reward-aware policy. The definition integrates mean rewards, as the proposition does, and its trajectory law is a probability measure.
-- source:
--   Cheung, Simchi-Levi & Zhu, Non-Stationary Reinforcement Learning: The Blessing of (More) Optimism, arXiv:1906.02922v4, p. 7, §2.2 Learning Protocol and (2); p. 8, Proposition 1

import Mathlib
import Definitions.Def_FiniteMDPLearning
import Definitions.Def_NonstatRL_Oracle_Model

open BanditAlgorithm MeasureTheory ProbabilityTheory

namespace NonstatRL.Oracle

/-- State observation at round n+1 under the time-varying transition sequence. -/
noncomputable def nsStateKernel {S A : ℕ} (M : ℕ → FiniteMDP S A)
    (s₁ : Fin S) : (n : ℕ) → Kernel (MDPTrajectory S A n) (Fin S)
  | 0 => Kernel.const _ (Measure.dirac s₁)
  | n + 1 =>
      (mdpTransitionKernel (M n)).comap
        (fun h : MDPTrajectory S A (n + 1) => h (Fin.last n))
        (measurable_pi_apply _)

instance nsStateKernel.instIsMarkovKernel {S A : ℕ} (M : ℕ → FiniteMDP S A)
    (s₁ : Fin S) (n : ℕ) : IsMarkovKernel (nsStateKernel M s₁ n) := by
  cases n with
  | zero => rw [nsStateKernel]; infer_instance
  | succ n => rw [nsStateKernel]; infer_instance

/-- One state observation followed by a history-dependent action. -/
noncomputable def nsStepKernel {S A : ℕ} (M : ℕ → FiniteMDP S A)
    (s₁ : Fin S) (π : MDPPolicy S A) (n : ℕ) :
    Kernel (MDPTrajectory S A n) (Fin S × Fin A) :=
  (nsStateKernel M s₁ n).compProd (π.select n)

instance nsStepKernel.instIsMarkovKernel {S A : ℕ} (M : ℕ → FiniteMDP S A)
    (s₁ : Fin S) (π : MDPPolicy S A) (n : ℕ) :
    IsMarkovKernel (nsStepKernel M s₁ π n) := by
  rw [nsStepKernel]
  infer_instance

/-- Law of the first n state-action pairs under nonstationary transitions. -/
noncomputable def nsMeasure {S A : ℕ} (M : ℕ → FiniteMDP S A)
    (s₁ : Fin S) (π : MDPPolicy S A) :
    (n : ℕ) → Measure (MDPTrajectory S A n)
  | 0 => Measure.dirac (fun t => t.elim0)
  | n + 1 =>
      ((nsMeasure M s₁ π n).compProd (nsStepKernel M s₁ π n)).map
        (fun p => Fin.snoc (α := fun _ => Fin S × Fin A) p.1 p.2)

instance nsMeasure.instIsProbabilityMeasure {S A : ℕ} (M : ℕ → FiniteMDP S A)
    (s₁ : Fin S) (π : MDPPolicy S A) (n : ℕ) :
    IsProbabilityMeasure (nsMeasure M s₁ π n) := by
  induction n with
  | zero => exact Measure.dirac.isProbabilityMeasure
  | succ n ih =>
      rw [nsMeasure]
      haveI := ih
      exact Measure.isProbabilityMeasure_map measurable_mdpTrajectorySnoc.aemeasurable

/-- The policy puts zero probability on actions disallowed at the current state. -/
def IsAllowedPolicy {S A : ℕ} (As : Fin S → Finset (Fin A))
    (π : MDPPolicy S A) : Prop :=
  ∀ n h s, π.select n (h, s) {a | a ∉ As s} = 0

/-- Expected sum of the mean rewards during the T rounds. -/
noncomputable def expectedReward {S A : ℕ} (M : ℕ → FiniteMDP S A)
    (s₁ : Fin S) (π : MDPPolicy S A) (T : ℕ) : ℝ :=
  ∫ h, ∑ t : Fin T, (M t).r (h t).1 (h t).2 ∂(nsMeasure M s₁ π T)

end NonstatRL.Oracle


