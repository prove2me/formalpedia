-- Prove2me | Definitions.Def_WeaklyCoupledDP_Model_LagrangianLPFeasible
-- name    : WeaklyCoupledDP_Model_LagrangianLPFeasible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:14:02.845279+00:00
-- url     : https://prove2.me/theorems/11c6c14b-4df3-45ce-850f-003828175be7
-- title:
--   The linear program (7) for the Lagrangian dual — feasibility and objective
-- statement:
--   The **Lagrangian dual LP** (7) has variables $\lambda_t(e_t) \in \mathbb R^{L_t}$ and $V^\lambda_{t,i}(s_{t,i},e_t)$, written $W_{t,i}$ here:
--   $$
--   \begin{aligned}
--   \text{minimize}\quad & \sum_{t=1}^T \mathbb E_{e_t}\big[\lambda_t(e_t)^\top b_t(e_t)\big] + \sum_{i=1}^N W_{1,i}(s_{1,i},e_1) && \text{(7a)}\\
--   \text{subject to}\quad & W_{t,i}(s_{t,i},e_t) \ge r_{t,i}(s_{t,i},e_t,a_{t,i}) - \lambda_t(e_t)^\top \ell_{t,i}(s_{t,i},e_t,a_{t,i}) + \mathbb E\big[W_{t+1,i}(s_{t+1,i},e_{t+1}) \,\big|\, (s_{t,i},e_t,a_{t,i})\big] \\ & \qquad \forall (t,i),\ (s_{t,i},e_t,a_{t,i}) \in \Gamma_{t,i}, && \text{(7b)}\\
--   & \lambda_t(e_t) \ge 0 \quad \forall (t,e_t), && \text{(7c)}
--   \end{aligned}
--   $$
--   with $W_{T+1,i} = 0$. Here $\Gamma_{t,i}$ is the set of triples with $a_{t,i} \in A_{t,i}(s_{t,i},e_t)$ (no linking constraint), and $\mathbb E_{e_t}$ is the expectation of $e_t$ given the initial exogenous state $e_1$, through the kernels $Q_1,\dots,Q_{t-1}$ (at $t=1$ it is evaluation at $e_1$).
--
--   The module defines feasibility in (7) and the objective (7a).
--
--   **Formalization Note** Only the periods $1 \le t \le T$ of $(\lambda, W)$ are constrained or read, apart from the terminal condition $W_{T+1,i} = 0$.
-- source:
--   Brown & Zhang, On the Strength of Relaxations of Weakly Coupled Stochastic Dynamic Programs, SSRN 3849573 (Feb. 6, 2022), §3.2.1, p.9 (PDF p.10), LP (7a)–(7c)

import Mathlib
import Definitions.Def_WeaklyCoupledDP_Model_ALPFeasible
import Definitions.Def_WeaklyCoupledDP_Model_lagrangianValue

open Finset Matrix

namespace WeaklyCoupledDP

namespace Model

variable {N : ℕ} {S : ℕ → Fin N → Type*} {E : Type*} {Act : ℕ → Fin N → Type*} {L : ℕ → ℕ}
  [∀ t i, Fintype (S t i)] [Fintype E] (M : Model N S E Act L)

/-- **Feasibility in the Lagrangian LP (7), §3.2.1, p.9.** `(λ, W)` is feasible when
(7c) `λ ∈ Λ`, `W_{T+1,i} = 0`, and (7b)
`Wₜ,ᵢ(sₜ,ᵢ, eₜ) ≥ rₜ,ᵢ(sₜ,ᵢ, eₜ, aₜ,ᵢ) − λₜ(eₜ)ᵀ ℓₜ,ᵢ(sₜ,ᵢ, eₜ, aₜ,ᵢ) + E[Wₜ₊₁,ᵢ(sₜ₊₁,ᵢ, eₜ₊₁) | (sₜ,ᵢ, eₜ, aₜ,ᵢ)]`
for all `(t, i)` and `(sₜ,ᵢ, eₜ, aₜ,ᵢ) ∈ Γₜ,ᵢ`. The paper writes `V^λ` for the variables `W`. -/
def LagrangianLPFeasible (lam : M.Multiplier) (W : M.ValueArray) : Prop :=
  lam ∈ M.Lambda ∧ (∀ i s e, W (M.T + 1) i s e = 0) ∧
    ∀ t, 1 ≤ t → t ≤ M.T → ∀ (i : Fin N) (s : S t i) (e : E), ∀ a ∈ M.A t i s e,
      M.r t i s e a - lam t e ⬝ᵥ M.ℓ t i s e a + M.subExp t i s e a (W (t + 1) i) ≤ W t i s e

/-- The objective (7a) of LP (7), `∑_{t=1}^T E_{eₜ}[λₜ(eₜ)ᵀ bₜ(eₜ)] + ∑ᵢ W₁,ᵢ(s₁,ᵢ, e₁)`, where
`E_{eₜ}` is the expectation of `eₜ` given the initial `e₁`. -/
noncomputable def lagrangianLPObjective (lam : M.Multiplier) (W : M.ValueArray) : ℝ :=
  ∑ t ∈ Icc 1 M.T, ∑ e, M.exoProb t e * (lam t e ⬝ᵥ M.b t e) + ∑ i, W 1 i (M.s₁ i) M.e₁

end Model

end WeaklyCoupledDP


