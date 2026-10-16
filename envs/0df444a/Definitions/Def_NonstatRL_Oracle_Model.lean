-- Prove2me | Definitions.Def_NonstatRL_Oracle_Model
-- name    : NonstatRL_Oracle_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-16T04:27:57.747586+00:00
-- url     : https://prove2.me/theorems/72126be3-6e8f-42a5-95a3-349e4d317f70
-- title:
--   §2.2, (1), Definition 1, (15)–(16) — MDP drift, LP gain and diameter
-- statement:
--   Fix finite state and action sets. Each state has a nonempty set of allowed actions; a sequence of finite Markov decision processes supplies a mean reward in $[0,1]$ and a transition distribution at each time.
--
--   The reward drift $B_{r,q}$ is the largest absolute change in mean reward from round $q$ to $q+1$ over allowed state–action pairs. The transition drift $B_{p,q}$ is the corresponding largest $\ell_1$ change in a transition distribution. Their horizon budgets are
--
--   $$B_r=\sum_{q=1}^{T-1}B_{r,q},\qquad B_p=\sum_{q=1}^{T-1}B_{p,q}.$$
--
--   For a stationary MDP, $\rho^*$ is the supremum of the objective of the occupancy linear program (15): occupancies are nonnegative, vanish on disallowed actions, satisfy stationarity and have total mass one. Dual feasibility means $\rho+\gamma(s)\ge r(s,a)+\sum_{s'}p(s'\mid s,a)\gamma(s')$ at each allowed pair.
--
--   The hitting time is the expected number of positive transitions until the target is reached. The diameter takes the largest, over every ordered pair of states including equal states, of the minimum hitting time over deterministic stationary allowed policies. These definitions provide the common mathematical model for the proposition and its drift bounds.
--
--   **Formalization Note** Paper time $t\in\{1,\ldots,T\}$ is stored at Lean index $t-1$. Hitting times and diameters use extended nonnegative reals, including infinity. The stationary policy class is deterministic; for expected hitting time, a deterministic stationary policy attains the minimum. The LP occupancy is extended by zero to disallowed actions. The finite MDP has unused transition and reward rows on those actions. Empty-state or empty-action data make some maxima and LP suprema return a Lean default, so the theorems require a nonempty state set and a nonempty allowed-action set at every state.
-- source:
--   Cheung, Simchi-Levi & Zhu, Non-Stationary Reinforcement Learning: The Blessing of (More) Optimism, arXiv:1906.02922v4, pp. 6–8, §2.2, (1), Definition 1; p. 33, (15), (16)

import Mathlib
import Definitions.Def_FiniteMDPLearning

open BanditAlgorithm MeasureTheory ENNReal

namespace NonstatRL.Oracle

/-- Equation (1): largest one-step reward change over allowed state-action pairs. -/
noncomputable def rewardDrift {S A : ℕ} (M : ℕ → FiniteMDP S A)
    (As : Fin S → Finset (Fin A)) (q : ℕ) : ℝ :=
  sSup {d : ℝ | ∃ s a, a ∈ As s ∧ d = |(M (q + 1)).r s a - (M q).r s a|}

/-- Equation (1): largest one-step ℓ₁ transition change over allowed pairs. -/
noncomputable def transDrift {S A : ℕ} (M : ℕ → FiniteMDP S A)
    (As : Fin S → Finset (Fin A)) (q : ℕ) : ℝ :=
  sSup {d : ℝ | ∃ s a, a ∈ As s ∧
    d = ∑ s' : Fin S, |((M (q + 1)).P s a s' : ℝ) - ((M q).P s a s' : ℝ)|}

/-- Equation (1): reward variation across the T-round horizon. -/
noncomputable def rewardBudget {S A : ℕ} (M : ℕ → FiniteMDP S A)
    (As : Fin S → Finset (Fin A)) (T : ℕ) : ℝ :=
  ∑ q ∈ Finset.range (T - 1), rewardDrift M As q

/-- Equation (1): transition variation across the T-round horizon. -/
noncomputable def transBudget {S A : ℕ} (M : ℕ → FiniteMDP S A)
    (As : Fin S → Finset (Fin A)) (T : ℕ) : ℝ :=
  ∑ q ∈ Finset.range (T - 1), transDrift M As q

/-- Dual feasibility in (16), on the allowed state-action pairs. -/
def DualFeasible {S A : ℕ} (r : Fin S → Fin A → ℝ)
    (P : Fin S → Fin A → Fin S → ℝ) (As : Fin S → Finset (Fin A))
    (ρ : ℝ) (γ : Fin S → ℝ) : Prop :=
  ∀ s a, a ∈ As s → ρ + γ s ≥ r s a + ∑ s' : Fin S, P s a s' * γ s'

/-- The primal LP optimum of (15), with occupancy zero on disallowed actions. -/
noncomputable def lpValue {S A : ℕ} (r : Fin S → Fin A → ℝ)
    (P : Fin S → Fin A → Fin S → ℝ) (As : Fin S → Finset (Fin A)) : ℝ :=
  sSup {v : ℝ | ∃ x : Fin S → Fin A → ℝ,
    (∀ s a, 0 ≤ x s a) ∧
    (∀ s a, a ∉ As s → x s a = 0) ∧
    (∀ s, (∑ a ∈ As s, x s a) =
      ∑ s' : Fin S, ∑ a' ∈ As s', P s' a' s * x s' a') ∧
    (∑ s : Fin S, ∑ a ∈ As s, x s a) = 1 ∧
    v = ∑ s : Fin S, ∑ a ∈ As s, r s a * x s a}

/-- The optimal long-run gain, represented by the LP (15). -/
noncomputable def optGain {S A : ℕ} (M : FiniteMDP S A)
    (As : Fin S → Finset (Fin A)) : ℝ :=
  lpValue M.r (fun s a s' => (M.P s a s' : ℝ)) As

/-- Definition 1 hitting time: expectation of the first positive transition count
at which the target is reached. The k=0 survival term is one. -/
noncomputable def hitTime {S A : ℕ} (M : FiniteMDP S A)
    (f : Fin S → Fin A) (s s' : Fin S) : ℝ≥0∞ :=
  ∑' k : ℕ,
    mdpMeasure M (mdpStateDirac s) (mdpMemorylessDetPolicy f) (k + 1)
      {h | ∀ i : Fin (k + 1), i ≠ 0 → (h i).1 ≠ s'}

/-- Definition 1 diameter, including return times when s = s'. -/
noncomputable def diameter {S A : ℕ} (M : FiniteMDP S A)
    (As : Fin S → Finset (Fin A)) : ℝ≥0∞ :=
  ⨆ s : Fin S, ⨆ s' : Fin S,
    ⨅ f : Fin S → Fin A, ⨅ (_ : ∀ x, f x ∈ As x), hitTime M f s s'

end NonstatRL.Oracle


