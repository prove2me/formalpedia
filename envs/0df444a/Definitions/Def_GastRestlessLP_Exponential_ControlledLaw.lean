-- Prove2me | Definitions.Def_GastRestlessLP_Exponential_ControlledLaw
-- name    : GastRestlessLP_Exponential_ControlledLaw
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T00:19:29.012029+00:00
-- url     : https://prove2.me/theorems/ae366e8e-07c5-48e0-a489-5ba291ccd879
-- title:
--   Finite controlled trajectories and expected total reward per arm
-- statement:
--   A length-$T$ path records the chosen action vector and the next state vector at each epoch. The initial labeled assignment $x_0$ supplies the current state at time zero; later current states are the preceding recorded next states. The probability of a path is the product, over epochs, of its action-kernel probability and its independent arm-transition probability. Weights outside an action distribution's finite support are explicitly zeroed.
--
--   The path reward is $\sum_{t<T,s,a}R_s^aY^{(N)}_{s,a}(t)$. Its finite-law expectation defines $V^{(N)}_\pi(m_0,T)$, with the rounding family implementing $\pi$. Under valid rounding, all action kernels are probabilities, and stochastic transition rows make this trajectory law a probability distribution. All sums are finite, so no integrability default or global measurability hypothesis occurs. Rewards can be negative; no terminal reward is added. The expected reward is computed from the stochastic process, not defined equal to the fluid or LP value.
-- source:
--   Gast, Gaujal and Yan, arXiv:2106.10067v3 (22 December 2023), https://arxiv.org/abs/2106.10067v3, pp. 4–8, (1), (2a), (6), §3.2

import Definitions.Def_GastRestlessLP_Exponential_Rounding

open scoped BigOperators
noncomputable section

namespace GastRestlessLP.Exponential

variable {S : Type} [Fintype S] [DecidableEq S]

/-- A finite path records the chosen actions and next labeled states at each epoch. -/
abbrev Path (S : Type) (N T : ℕ) := Fin T → (Fin N → Fin 2) × (Fin N → S)

/-- Current state on a path; the first epoch uses the specified initial assignment. -/
def currentState {N T : ℕ} (x₀ : Fin N → S) (ω : Path S N T) (t : Fin T) : Fin N → S :=
  if h : t.val = 0 then x₀ else (ω ⟨t.val - 1, by omega⟩).2

/-- The full trajectory distribution obtained by composing action and independent
transition kernels. Indicator truncation discards the FinLaw's unused outside-support weights. -/
noncomputable def trajectoryLaw (M : Model S) (K : Rounding S) {N T : ℕ}
    (x₀ : Fin N → S) : RawBlending.UB.FinLaw (Path S N T) := by
  classical
  exact {
    supp := Finset.univ
    weight := fun ω => ∏ t : Fin T,
      (let μ := K N t.val (currentState x₀ ω t)
       if (ω t).1 ∈ μ.supp then μ.weight (ω t).1 else 0) *
      (transitionLaw M (currentState x₀ ω t) (ω t).1).weight (ω t).2 }

/-- Realized total reward per arm, with no reward at the terminal epoch. -/
def pathReward (M : Model S) {N T : ℕ} (x₀ : Fin N → S) (ω : Path S N T) : ℝ :=
  ∑ t : Fin T, reward M (empiricalAllocation (currentState x₀ ω t) (ω t).1)

/-- The stochastic value is the expectation under the actual finite trajectory law. -/
noncomputable def populationValue (M : Model S) (T : ℕ) (K : Rounding S)
    {N : ℕ} (x₀ : Fin N → S) : ℝ :=
  (trajectoryLaw M K (T := T) x₀).expect (pathReward M x₀)

end GastRestlessLP.Exponential


