-- Prove2me | Definitions.Def_WeaklyCoupledDP_Model_optimalValue
-- name    : WeaklyCoupledDP_Model_optimalValue
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:13:14.597507+00:00
-- url     : https://prove2.me/theorems/edf877b0-a085-4cee-a63a-bb6afd2b6acd
-- title:
--   The optimal value function $V^*_t$ of the weakly coupled DP (2)
-- statement:
--   The **optimal value function** of the weakly coupled DP is defined by the dynamic programming recursion (2), with terminal value $V^*_{T+1} \equiv 0$:
--   $$
--   V^*_t(s_t, e_t) = \max_{a_t \in \mathcal A_t(s_t, e_t)} \Big\{ r_t(s_t, e_t, a_t) + \mathbb E\big[V^*_{t+1}(s_{t+1}, e_{t+1}) \,\big|\, (s_t, e_t, a_t)\big] \Big\}, \qquad t = 1, \dots, T .
--   $$
--   The maximum runs over the **feasible** action set $\mathcal A_t(s_t,e_t)$ (the linking constraints are enforced), and the expectation is under the product law $\prod_i P_{t,i} \cdot Q_t$.
--
--   $V^*_1(s_1, e_1)$ is the optimal expected total reward, the quantity that both relaxations of the paper bound from above.
--
--   **Formalization Note** The weakly coupled DP is cast as a finite-horizon MDP on the joint state $(s_t, e_t)$ and $V^*$ is its backward-induction value. The paper defines $V^*_1$ as a maximum over feasible policies, (1), and states that it satisfies (2); here (2) is the definition.
-- source:
--   Brown & Zhang, On the Strength of Relaxations of Weakly Coupled Stochastic Dynamic Programs, SSRN 3849573 (Feb. 6, 2022), §2, p.4 (PDF p.5), eqs. (1)–(2)

import Mathlib
import Definitions.Def_WeaklyCoupledDP_FiniteHorizonMDP
import Definitions.Def_WeaklyCoupledDP_Model

open Finset

namespace WeaklyCoupledDP

namespace Model

variable {N : ℕ} {S : ℕ → Fin N → Type*} {E : Type*} {Act : ℕ → Fin N → Type*} {L : ℕ → ℕ}
  [∀ t i, Fintype (S t i)] [Fintype E] (M : Model N S E Act L)

/-- The weakly coupled DP as one Markov decision process on the joint state `(sₜ, eₜ)`, with the
feasible action sets `𝒜ₜ(sₜ, eₜ)`, the total reward `rₜ` and the product transition law (§2, p.4). -/
noncomputable def feasibleMDP :
    FiniteHorizonMDP M.T (fun t => (∀ i, S t i) × E) (fun t => ∀ i, Act t i) where
  avail t x := M.feasActions t x.1 x.2
  reward t x a := M.reward t x.1 x.2 a
  kernel t x a y := (∏ i, M.P t i (x.1 i) x.2 (a i) (y.1 i)) * M.Q t x.2 y.2
  avail_nonempty t h1 hT x := by
    obtain ⟨a, ha⟩ := M.feasible_nonempty t h1 hT x.1 x.2
    exact ⟨a, M.mem_feasActions.2 ha⟩
  kernel_nonneg t h1 hT x a ha y :=
    M.jointLaw_nonneg h1 hT x.1 x.2 (M.mem_feasActions.1 ha).1 y.1 y.2
  kernel_sum t h1 hT x a ha :=
    M.jointLaw_sum h1 hT x.1 x.2 (M.mem_feasActions.1 ha).1

/-- **The optimal value function** `V*ₜ(sₜ, eₜ)` of the DP (2), p.4:
`V*ₜ(sₜ, eₜ) = max_{aₜ ∈ 𝒜ₜ(sₜ, eₜ)} { rₜ(sₜ, eₜ, aₜ) + E[V*ₜ₊₁(sₜ₊₁, eₜ₊₁) | (sₜ, eₜ, aₜ)] }`
with `V*_{T+1} = 0`. -/
noncomputable def optimalValue (t : ℕ) (s : ∀ i, S t i) (e : E) : ℝ :=
  M.feasibleMDP.value t (s, e)

end Model

end WeaklyCoupledDP


