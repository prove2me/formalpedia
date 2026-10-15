-- Prove2me | Definitions.Def_BreakingSample_Perturbed_Model
-- name    : BreakingSample_Perturbed_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T09:04:27.154809+00:00
-- url     : https://prove2.me/theorems/f869e036-1ddd-4b6e-af5b-8de1e7c3e668
-- title:
--   §2.1 and §6.1 — finite discounted MDP, values, optimal values, resolvent, variance, and auxiliary vectors
-- statement:
--   Let $S$ and $A$ be nonempty finite state and action sets. A discounted Markov decision process has transition probabilities $P(s'\mid s,a)$, rewards $r(s,a)\in[0,1]$, and discount factor $\gamma\in(0,1)$. A deterministic policy $\pi:S\to A$ has discounted value $V^\pi$ and action value $Q^\pi$. The optimal value is the maximum of $V^\pi(s)$ over deterministic policies, and the optimal action value satisfies
--
--   $$Q^\star(s,a)=r(s,a)+\gamma\sum_{s'}P(s'\mid s,a)V^\star(s').$$
--
--   The module also defines the policy transition matrix $P_\pi$, reward vector $r_\pi$, resolvent $(I-\gamma P_\pi)^{-1}$, transition variance, and the auxiliary vectors $V^{(l)}$ of display (36). These are the shared objects used by the statistical and absorbing-MDP statements.
--
--   **Formalization Note** Values for a deterministic policy use the published stochastic-policy value after embedding $\pi$ as a point mass. The value definition accepts arbitrary real rewards, as required by the absorbing construction.
-- source:
--   arXiv:2005.12900v8, §2.1, p. 5; §6.1, pp. 12–13; (36), p. 15

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_FoundationsML_ReinforcementLearning_QFunction

namespace BreakingSample.Perturbed

open FoundationsML.ReinforcementLearning

/-- The standing setting of §2.1 (arXiv:2005.12900v8, p. 5): nonempty finite state and action
sets, transition kernel `P` (`P s a s'` = P(s'|s,a)), rewards `r(s,a) ∈ [0,1]` and
discount factor `γ ∈ (0,1)`. -/
def IsDiscountedMDP {S A : Type*} [Fintype S] (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) : Prop :=
  IsTransitionKernel P ∧ (∀ s a, 0 ≤ r s a ∧ r s a ≤ 1) ∧ 0 < γ ∧ γ < 1 ∧
    Nonempty S ∧ Nonempty A

/-- A deterministic policy `π : S → A` (p. 5), seen as the stochastic policy with all its mass on `π s`. -/
def detPolicy {S A : Type*} [DecidableEq A] (π : S → A) : S → A → ℝ :=
  fun s a => if a = π s then 1 else 0

/-- The value function `V^π(s)` of (1), p. 5, of a deterministic policy `π` in the MDP `(P, r, γ)`.
The reward may take any real values (the absorbing MDPs of (39) use rewards outside `[0,1]`). -/
noncomputable def value {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (π : S → A) (s : S) : ℝ :=
  PolicyValue (detPolicy π) P r γ s

/-- The Q-function `Q^π(s,a)` of (2), p. 5, in its one-step form `r + γ P V^π` of (25), p. 12. -/
noncomputable def qValue {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (π : S → A) (s : S) (a : A) : ℝ :=
  QFunction (detPolicy π) P r γ s a

/-- The optimal value `V⋆(s) = max_π V^π(s)`, the maximum over the finitely many deterministic policies
(§2.1, p. 5). -/
noncomputable def optValue {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
    [Nonempty A] (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (s : S) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun π : S → A => value P r γ π s)

/-- The optimal Q-function `Q⋆(s,a) = r(s,a) + γ ∑_{s'} P(s'|s,a) V⋆(s')` (the Bellman equation used on
p. 18 and in App. B.2, p. 28). -/
noncomputable def optQ {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
    [Nonempty A] (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (s : S) (a : A) : ℝ :=
  r s a + γ * ∑ s', P s a s' * optValue P r γ s'

/-- `π` is an optimal policy of `(P, r, γ)`: `V^π(s) = V⋆(s)` at every state (p. 5; (9), p. 8). -/
def IsOptimal {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A] [Nonempty A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (π : S → A) : Prop :=
  ∀ s, value P r γ π s = optValue P r γ s

/-- The state transition matrix `P_π = Π^π P` of (24), p. 12: `P_π(s, s') = P(s' | s, π(s))`. -/
def policyMatrix {S A : Type*} (P : S → A → S → ℝ) (π : S → A) : Matrix S S ℝ :=
  fun s s' => P s (π s) s'

/-- The reward vector `r_π(s) = r(s, π(s))` (§6.1, p. 12). -/
def policyReward {S A : Type*} (r : S → A → ℝ) (π : S → A) : S → ℝ :=
  fun s => r s (π s)

/-- The resolvent `(I − γP_π)⁻¹` of (27), p. 12. -/
noncomputable def resolvent {S A : Type*} [Fintype S] [DecidableEq S]
    (P : S → A → S → ℝ) (γ : ℝ) (π : S → A) : Matrix S S ℝ :=
  (1 - γ • policyMatrix P π)⁻¹

/-- `Var_P(V)(s,a) = ∑_{s'} P(s'|s,a) V(s')² − (∑_{s'} P(s'|s,a) V(s'))²` (§6.1, p. 12). -/
def varP {S A : Type*} [Fintype S] (P : S → A → S → ℝ) (V : S → ℝ) (s : S) (a : A) : ℝ :=
  ∑ s', P s a s' * V s' ^ 2 - (∑ s', P s a s' * V s') ^ 2

/-- `Var_{P_π}(V)(s) = Var_P(V)(s, π(s))` of (29), p. 13. -/
def varPi {S A : Type*} [Fintype S] (P : S → A → S → ℝ) (π : S → A) (V : S → ℝ) (s : S) : ℝ :=
  varP P V s (π s)

/-- The auxiliary vectors (36), p. 15: `V⁽⁰⁾ = (I − γP_π)⁻¹ r_π` and
`V⁽ˡ⁾ = (I − γP_π)⁻¹ √(Var_{P_π}(V⁽ˡ⁻¹⁾))` for `l ≥ 1`. -/
noncomputable def auxV {S A : Type*} [Fintype S] [DecidableEq S]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (π : S → A) : ℕ → S → ℝ
  | 0 => Matrix.mulVec (resolvent P γ π) (policyReward r π)
  | l + 1 => Matrix.mulVec (resolvent P γ π) (fun s => Real.sqrt (varPi P π (auxV P r γ π l) s))

end BreakingSample.Perturbed


