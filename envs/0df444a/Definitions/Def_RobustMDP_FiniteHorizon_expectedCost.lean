-- Prove2me | Definitions.Def_RobustMDP_FiniteHorizon_expectedCost
-- name    : RobustMDP_FiniteHorizon_expectedCost
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T17:17:46.802471+00:00
-- url     : https://prove2.me/theorems/93151819-8528-4859-8a13-562da7c75ce3
-- title:
--   Expected total cost $C_N(\pi,\tau)$ of a policy under given transition matrices
-- statement:
--   Fix an initial state $i_0$, a controller policy $\pi=(\mathbf a_0,\dots,\mathbf a_{N-1})$ and transition matrices $P=(P_t^a)_{a\in\mathcal A,\,t\in T}$, where $P_t^a(i,j)$ is the probability of moving from $i$ to $j$ under action $a$ at stage $t$. The distribution $\mu_t$ of the state $i_t$ is defined forward by
--
--   $$
--   \mu_0=e_{i_0},\qquad \mu_{t+1}(j)=\sum_{i}\mu_t(i)\,P_t^{\mathbf a_t(i)}(i,j)\quad(t<N),
--   $$
--
--   and the **expected total cost** (2) is
--
--   $$
--   C_N(\pi,P)=\mathbf E\Big(\sum_{t=0}^{N-1}c_t(i_t,\mathbf a_t(i_t))+c_N(i_N)\Big)=\sum_{t=0}^{N-1}\sum_i\mu_t(i)\,c_t(i,\mathbf a_t(i))+\sum_i\mu_N(i)\,c_N(i).
--   $$
--
--   For a policy of nature $\tau\in\mathcal T$ one writes $C_N(\pi,\tau)$.
--
--   **Formalization Note** The cost is defined through the forward state distribution, i.e. as the expectation in (2), and not through a backward recursion: the backward recursions (10) and (7) are what the theorems of this mission prove. The distribution is indexed by $t\in\mathbb N$ and set to $0$ for $t>N$, where it is never used.
-- source:
--   Nilim and El Ghaoui, Robust Control of Markov Decision Processes with Uncertain Transition Matrices, Oper. Res. 53 (2005), p. 781, Eq. (2)

import Mathlib
import Definitions.Def_RobustMDP_FiniteHorizon_Model

namespace RobustMDP.FiniteHorizon

/-- The distribution of the state `i_t` at time `t` under controller policy `π` and transition
matrices `P` (`P t a i j` = probability of moving from `i` to `j` under action `a` at stage `t`),
starting from the initial state `i₀`: `μ_0 = e_{i₀}` and
`μ_{t+1}(j) = ∑_i μ_t(i) P_t^{𝐚_t(i)}(i, j)` for `t < N`. Only `t ≤ N` is ever used; the value
for `t > N` is set to `0`. -/
noncomputable def stateDist {n N : ℕ} {A : Type} (π : ControlPolicy n N A)
    (P : Fin N → A → Fin n → Fin n → ℝ) (i₀ : Fin n) : ℕ → Fin n → ℝ
  | 0 => fun j => if j = i₀ then 1 else 0
  | t + 1 => fun j =>
      if h : t < N then ∑ i, stateDist π P i₀ t i * P ⟨t, h⟩ (π ⟨t, h⟩ i) i j else 0

/-- The expected total cost (2), p. 781:
`C_N(π, P) = 𝐄(∑_{t=0}^{N-1} c_t(i_t, 𝐚_t(i_t)) + c_N(i_N))` from the initial state `i₀`,
computed with the forward state distribution `stateDist`. -/
noncomputable def Model.expectedCost {n N : ℕ} {A : Type} (M : Model n N A)
    (i₀ : Fin n) (π : ControlPolicy n N A) (P : Fin N → A → Fin n → Fin n → ℝ) : ℝ :=
  ∑ t : Fin N, ∑ i, stateDist π P i₀ t i * M.cost t i (π t i) +
    ∑ i, stateDist π P i₀ N i * M.terminalCost i

end RobustMDP.FiniteHorizon


