-- Prove2me | Definitions.Def_WeaklyCoupledDP_Model_ALPFeasible
-- name    : WeaklyCoupledDP_Model_ALPFeasible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:12:48.367395+00:00
-- url     : https://prove2.me/theorems/a34fac2d-5dca-4b80-8906-b544bac2a9ca
-- title:
--   The approximate linear program (5) — feasibility and objective
-- statement:
--   The **approximate linear program (ALP)** restricts the exact LP of the DP to additively separable value functions $V_t(s_t,e_t) \approx \sum_i V_{t,i}(s_{t,i},e_t)$. Its variables are an array $V = (V_{t,i}(s_{t,i},e_t))$, and it reads
--   $$
--   \begin{aligned}
--   \text{minimize}\quad & \sum_{i=1}^N V_{1,i}(s_{1,i},e_1) && \text{(5a)}\\
--   \text{subject to}\quad & \sum_{i=1}^N V_{t,i}(s_{t,i},e_t) \ \ge\ r_t(s_t,e_t,a_t) + \mathbb E\Big[\sum_{i=1}^N V_{t+1,i}(s_{t+1,i},e_{t+1}) \,\Big|\, (s_t,e_t,a_t)\Big] \quad \forall t,\ (s_t,e_t,a_t) \in \overline\Gamma_t, && \text{(5b)}
--   \end{aligned}
--   $$
--   where $\overline\Gamma_t$ is the set of state–action triples with $a_t \in \mathcal A_t(s_t,e_t)$ (the linking constraints hold), and $V_{T+1,i} \equiv 0$. Its optimal value is denoted $V^{\mathrm{LP}}_1(s_1,e_1)$.
--
--   The module defines feasibility in (5) and the objective (5a).
--
--   **Formalization Note** The paper uses $V_{T+1,i}$ in (5b) at $t = T$ without giving it a value; as in the DP (2) and in LP (7) it is $0$ (without this the ALP would be unbounded below). This is the first clause of feasibility. Constraints are imposed for $1 \le t \le T$, every joint state and every exogenous state.
-- source:
--   Brown & Zhang, On the Strength of Relaxations of Weakly Coupled Stochastic Dynamic Programs, SSRN 3849573 (Feb. 6, 2022), §3.1, pp.5–6 (PDF pp.6–7), the ALP (5a)–(5b); Γ̄ₜ, p.5 (PDF p.6)

import Mathlib
import Definitions.Def_WeaklyCoupledDP_Model

open Finset

namespace WeaklyCoupledDP

namespace Model

variable {N : ℕ} {S : ℕ → Fin N → Type*} {E : Type*} {Act : ℕ → Fin N → Type*} {L : ℕ → ℕ}
  [∀ t i, Fintype (S t i)] [Fintype E] (M : Model N S E Act L)

/-- An array `V = (Vₜ,ᵢ(sₜ,ᵢ, eₜ))` of additively separable value function approximations
(§3.1, p.5, (4)). Also the type of the variables `V^λₜ,ᵢ` of LP (7). -/
abbrev ValueArray (_M : Model N S E Act L) : Type _ := ∀ t i, S t i → E → ℝ

/-- **Feasibility in the approximate linear program (5), pp.5–6.** `V` is feasible when
`∑ᵢ Vₜ,ᵢ(sₜ,ᵢ, eₜ) ≥ rₜ(sₜ, eₜ, aₜ) + E[∑ᵢ Vₜ₊₁,ᵢ(sₜ₊₁,ᵢ, eₜ₊₁) | (sₜ, eₜ, aₜ)]`
for every period `1 ≤ t ≤ T` and every `(sₜ, eₜ, aₜ) ∈ Γ̄ₜ`, that is `aₜ ∈ 𝒜ₜ(sₜ, eₜ)` (5b).

**Formalization Note.** The paper's variables run over `t ≤ T`. It uses `V_{T+1,i}` in (5b) without
giving it a value; as in the DP (2) and in LP (7) it is `0` (without that the ALP is unbounded
below), which is the first clause here. The periods after `T + 1` are never read. -/
def ALPFeasible (V : M.ValueArray) : Prop :=
  (∀ i s e, V (M.T + 1) i s e = 0) ∧
    ∀ t, 1 ≤ t → t ≤ M.T → ∀ (s : ∀ i, S t i) (e : E), ∀ a ∈ M.feasActions t s e,
      M.reward t s e a + M.jointExp t s e a (fun s' e' => ∑ i, V (t + 1) i (s' i) e') ≤
        ∑ i, V t i (s i) e

/-- The objective (5a) of the ALP, `∑ᵢ V₁,ᵢ(s₁,ᵢ, e₁)`. -/
def alpObjective (V : M.ValueArray) : ℝ :=
  ∑ i, V 1 i (M.s₁ i) M.e₁

end Model

end WeaklyCoupledDP


