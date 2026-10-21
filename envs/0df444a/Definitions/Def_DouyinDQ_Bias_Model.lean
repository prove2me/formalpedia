-- Prove2me | Definitions.Def_DouyinDQ_Bias_Model
-- name    : DouyinDQ_Bias_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T05:04:54.022177+00:00
-- url     : https://prove2.me/theorems/d7e5dd34-889c-438d-a05c-31ab99e5ce7a
-- title:
--   Absorbing experiment, trajectory law, total rewards, DQ estimator, and value functionals
-- statement:
--   Specialize the finite MDP to control action $0$ and treatment action $1$. The policies $\pi_0$ and $\pi_1$ choose their named actions surely, while $\pi_{1/2}$ chooses each with probability $1/2$. An absorbing class $S_{\rm abs}$ is closed under the induced transition matrix and gives zero mean reward for either action. Assumption 1 bounds, strictly by $T_{\rm abs}$, the sum of the probabilities of remaining outside this class at each time, from every starting state and under all three policies.
--
--   The probability of a length $H+1$ state-action path is its initial-state probability times its action probabilities and action-conditioned transition probabilities. Summing a statistic against these path weights defines its finite-horizon expectation. The total reward $J_\pi$ sums the expected reward over all times, and ${\rm ATE}=J_{\pi_1}-J_{\pi_0}$. The truncated DQ estimator is equation (4) with both time sums stopped at $H$ and inverse-propensity weight $2$; its expectation is taken under $\pi_{1/2}$.
--
--   For a state reward $g$, the value functional $\widetilde E_\pi g$ is its expected total reward. The state-reward $Q_\pi(s,a;g)$, successive $DQ^{(k)}_{\pi,\pi'}$ terms, and the state-action-reward $Q_\pi(s,a)$ follow Section 5. The latter includes the immediate reward $r(s,a)$, whereas $Q_\pi(s,a;g)$ includes $g(s)$.
--
--   **Formalization Note** The infinite sums are real `tsum`s. Assumption 1 uses explicit `HasSum` witnesses to prevent a divergent absorption-time series from receiving Lean's default value. The path reward uses conditional mean rewards in place of random rewards. The closed-class reading corrects the printed absorbing-row equation, which is incompatible with stochasticity for a class of more than one state.
-- source:
--   Farias, Li, Peng, Ren, Zhang, Zheng, Correcting for Interference in Experiments: A Case Study at Douyin, arXiv:2305.02542v1, pp. 3–7, §3, §4.2 Eq. (4), §5.1, Assumptions 1 and 5

import Definitions.Def_DouyinDQ_Bias_FiniteMDP

noncomputable section

namespace DouyinDQ.Bias

variable {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]

/-- Global treatment: action 1 at every state. -/
def pi1 : S → Fin 2 → ℝ := fun _ a => if a = 1 then 1 else 0

/-- Global control: action 0 at every state. -/
def pi0 : S → Fin 2 → ℝ := fun _ a => if a = 0 then 1 else 0

/-- The experimental policy: each action has probability one half. -/
def piHalf : S → Fin 2 → ℝ := fun _ _ => 1 / 2

/-- A closed absorbing class on which all actions have zero mean reward. -/
def IsAbsorbingFor (M : MDP S A) (Sabs : Set S)
    (π : S → A → ℝ) : Prop :=
  (∀ s ∈ Sabs, ∀ s' ∉ Sabs, Ppol M π s s' = 0) ∧
  (∀ s ∈ Sabs, ∀ a, M.r s a = 0)

/-- The expected number of steps outside the absorbing class is strictly below T,
from every starting state. The explicit `HasSum` excludes a divergent series. -/
def AbsTimeLT (M : MDP S A) (Sabs : Set S)
    [DecidablePred (· ∈ Sabs)] (π : S → A → ℝ) (T : ℝ) : Prop :=
  ∀ s, ∃ x : ℝ,
    HasSum (fun t : ℕ => ∑ s' : S, if s' ∈ Sabs then 0 else
      (Ppol M π ^ t) s s') x ∧ x < T

/-- Assumption 1 for the control, treatment, and half-treatment policies. -/
def Assumption1 (M : MDP S (Fin 2)) (Sabs : Set S)
    [DecidablePred (· ∈ Sabs)] (Tabs : ℝ) : Prop :=
  (IsAbsorbingFor M Sabs pi0 ∧ AbsTimeLT M Sabs pi0 Tabs) ∧
  (IsAbsorbingFor M Sabs pi1 ∧ AbsTimeLT M Sabs pi1 Tabs) ∧
  (IsAbsorbingFor M Sabs piHalf ∧ AbsTimeLT M Sabs piHalf Tabs)

/-- Probability of a state-action path through time H under a stationary policy. -/
def pathWeight (M : MDP S A) (π : S → A → ℝ) (H : ℕ)
    (ω : Fin (H + 1) → S × A) : ℝ :=
  M.ρ (ω 0).1 * (∏ t : Fin (H + 1), π (ω t).1 (ω t).2) *
    ∏ t : Fin H, M.P (ω t.castSucc).2 (ω t.castSucc).1 (ω t.succ).1

/-- Finite expectation of a path statistic. -/
def pathExp (M : MDP S A) (π : S → A → ℝ) (H : ℕ)
    (f : (Fin (H + 1) → S × A) → ℝ) : ℝ :=
  ∑ ω, pathWeight M π H ω * f ω

/-- Total reward J_π, computed from the path law. -/
def totalReward (M : MDP S A) (π : S → A → ℝ) : ℝ :=
  ∑' t : ℕ, pathExp M π t
    (fun ω => M.r (ω (Fin.last t)).1 (ω (Fin.last t)).2)

/-- Average treatment effect J_{π₁} - J_{π₀}. -/
def ATE (M : MDP S (Fin 2)) : ℝ :=
  totalReward M pi1 - totalReward M pi0

/-- Equation (4) truncated after action and reward H. -/
def dqTrunc (M : MDP S (Fin 2)) (H : ℕ)
    (ω : Fin (H + 1) → S × Fin 2) : ℝ :=
  ∑ t : Fin (H + 1),
    2 * ((if (ω t).2 = 1 then 1 else 0) -
      (if (ω t).2 = 0 then 1 else 0)) *
      ∑ t' ∈ Finset.univ.filter (fun t' : Fin (H + 1) => t ≤ t'),
        M.r (ω t').1 (ω t').2

/-- Expectation of the truncated DQ estimator under the half-treatment policy. -/
def expDQTrunc (M : MDP S (Fin 2)) (H : ℕ) : ℝ :=
  pathExp M piHalf H (dqTrunc M H)

/-- The total-reward value functional of Assumption 5. -/
def Etilde (M : MDP S A) (π : S → A → ℝ) (g : S → ℝ) : ℝ :=
  ∑' t : ℕ, ∑ s : S, M.ρ s * Matrix.mulVec (Ppol M π ^ t) g s

/-- Assumption 5's Q-function for a state reward g. -/
def Qfun (M : MDP S A) (π : S → A → ℝ) (a : A)
    (g : S → ℝ) (s : S) : ℝ :=
  g s + ∑' t : ℕ, Matrix.mulVec (M.P a * Ppol M π ^ t) g s

/-- The successive Differences-in-Qs terms of Theorem 2. -/
def DQ (M : MDP S A) (π π' : S → A → ℝ) : ℕ → S → ℝ
  | 0 => rpol M π'
  | k + 1 => fun s =>
      (∑ a, π' s a * Qfun M π a (DQ M π π' k) s) -
      (∑ a, π s a * Qfun M π a (DQ M π π' k) s)

/-- Equation (5)'s Q-function, with an action-dependent reward at time zero. -/
def Qsa (M : MDP S A) (π : S → A → ℝ) (s : S) (a : A) : ℝ :=
  M.r s a + ∑' t : ℕ,
    Matrix.mulVec (M.P a * Ppol M π ^ t) (rpol M π) s

/-- The largest absolute conditional mean reward. -/
def rmax (M : MDP S A) : ℝ := ⨆ s, ⨆ a, |M.r s a|

end DouyinDQ.Bias


