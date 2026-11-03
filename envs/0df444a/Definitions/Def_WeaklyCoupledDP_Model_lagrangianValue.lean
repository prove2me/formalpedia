-- Prove2me | Definitions.Def_WeaklyCoupledDP_Model_lagrangianValue
-- name    : WeaklyCoupledDP_Model_lagrangianValue
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:12:57.212036+00:00
-- url     : https://prove2.me/theorems/2cbbc1bd-8c6c-4d43-91e8-7f21df316cc2
-- title:
--   Lagrange multipliers $\Lambda$, the Lagrangian value $V^\lambda_t$ and the subproblem values $V^\lambda_{t,i}$ (§3.2)
-- statement:
--   A **Lagrange multiplier** is an array $\lambda = (\lambda_t(e_t))$ with $\lambda_t(e_t) \in \mathbb R^{L_t}$, and the feasible set of multipliers is
--   $$
--   \Lambda = \{ \lambda : \lambda_t(e_t) \ge 0 \ \ \forall (t, e_t) \}.
--   $$
--   For a multiplier $\lambda$ the **Lagrangian value function** relaxes the linking constraints into the objective:
--   $$
--   V^\lambda_t(s_t,e_t) = \max_{a_t \in \mathbf A_t(s_t,e_t)} \Big\{ r_t(s_t,e_t,a_t) + \lambda_t(e_t)^\top\Big[b_t(e_t) - \sum_{i=1}^N \ell_{t,i}(s_{t,i},e_t,a_{t,i})\Big] + \mathbb E\big[V^\lambda_{t+1}(s_{t+1},e_{t+1}) \,\big|\, (s_t,e_t,a_t)\big] \Big\},
--   $$
--   with $V^\lambda_{T+1} = 0$. The maximum is over the **product** set $\mathbf A_t(s_t,e_t)$, not over the feasible set.
--
--   The **subproblem value function** of subproblem $i$ in isolation is
--   $$
--   V^\lambda_{t,i}(s_{t,i},e_t) = \max_{a_{t,i} \in A_{t,i}(s_{t,i},e_t)} \Big\{ r_{t,i}(s_{t,i},e_t,a_{t,i}) - \lambda_t(e_t)^\top \ell_{t,i}(s_{t,i},e_t,a_{t,i}) + \mathbb E\big[V^\lambda_{t+1,i}(s_{t+1,i},e_{t+1}) \,\big|\, (s_{t,i},e_t,a_{t,i})\big] \Big\},
--   $$
--   with $V^\lambda_{T+1,i} = 0$, the expectation being under $P_{t,i} \cdot Q_t$.
--
--   For $\lambda \in \Lambda$, $V^\lambda_1(s_1,e_1)$ is an upper bound on $V^*_1(s_1,e_1)$, and the Lagrangian dual problem is $V^{\lambda*}_1(s_1,e_1) = \min_{\lambda \in \Lambda} V^\lambda_1(s_1,e_1)$.
--
--   **Formalization Note** Both recursions are backward-induction values of finite-horizon MDPs (on $(s_t,e_t)$ and on $(s_{t,i},e_t)$ respectively). Only the periods $1 \le t \le T$ of $\lambda$ are read, and $\Lambda$ constrains only those periods.
-- source:
--   Brown & Zhang, On the Strength of Relaxations of Weakly Coupled Stochastic Dynamic Programs, SSRN 3849573 (Feb. 6, 2022), §3.2, p.8 (PDF p.9), the Lagrangian DP and Proposition 3.2(b); p.9 (PDF p.10), the dual problem

import Mathlib
import Definitions.Def_WeaklyCoupledDP_FiniteHorizonMDP
import Definitions.Def_WeaklyCoupledDP_Model

open Finset Matrix

namespace WeaklyCoupledDP

namespace Model

variable {N : ℕ} {S : ℕ → Fin N → Type*} {E : Type*} {Act : ℕ → Fin N → Type*} {L : ℕ → ℕ}
  [∀ t i, Fintype (S t i)] [Fintype E] (M : Model N S E Act L)

/-- A Lagrange multiplier array `λ = (λₜ(eₜ))`, with `λₜ(eₜ) ∈ ℝ^{Lₜ}` (§3.2, p.8). Only the periods
`1 ≤ t ≤ T` are ever read. -/
abbrev Multiplier (_M : Model N S E Act L) : Type _ := ∀ t, E → Fin (L t) → ℝ

/-- The feasible set of multipliers `Λ = {λ : λₜ(eₜ) ≥ 0, ∀ (t, eₜ)}` (§3.2, p.8). -/
def Lambda : Set M.Multiplier :=
  {lam | ∀ t, 1 ≤ t → t ≤ M.T → ∀ e l, 0 ≤ lam t e l}

/-- The Lagrangian relaxation as a Markov decision process on `(sₜ, eₜ)`: the linking constraints
are dropped, so the action sets are the product sets `𝐀ₜ(sₜ, eₜ)`, and the reward is
`rₜ(sₜ, eₜ, aₜ) + λₜ(eₜ)ᵀ[bₜ(eₜ) − ∑ᵢ ℓₜ,ᵢ(sₜ,ᵢ, eₜ, aₜ,ᵢ)]` (§3.2, p.8). -/
noncomputable def lagrangianMDP (lam : M.Multiplier) :
    FiniteHorizonMDP M.T (fun t => (∀ i, S t i) × E) (fun t => ∀ i, Act t i) where
  avail t x := M.prodActions t x.1 x.2
  reward t x a := M.reward t x.1 x.2 a + lam t x.2 ⬝ᵥ (M.b t x.2 - M.linkSum t x.1 x.2 a)
  kernel t x a y := (∏ i, M.P t i (x.1 i) x.2 (a i) (y.1 i)) * M.Q t x.2 y.2
  avail_nonempty t h1 hT x := by
    obtain ⟨a, ha, -⟩ := M.feasible_nonempty t h1 hT x.1 x.2
    exact ⟨a, by simpa [prodActions, Fintype.mem_piFinset] using ha⟩
  kernel_nonneg t h1 hT x a ha y :=
    M.jointLaw_nonneg h1 hT x.1 x.2 (by simpa [prodActions, Fintype.mem_piFinset] using ha) y.1 y.2
  kernel_sum t h1 hT x a ha :=
    M.jointLaw_sum h1 hT x.1 x.2 (by simpa [prodActions, Fintype.mem_piFinset] using ha)

/-- **The Lagrangian value function** `V^λₜ(sₜ, eₜ)` of §3.2, p.8:
`V^λₜ(sₜ, eₜ) = max_{aₜ ∈ 𝐀ₜ(sₜ, eₜ)} { rₜ(sₜ, eₜ, aₜ) + λₜ(eₜ)ᵀ[bₜ(eₜ) − ∑ᵢ ℓₜ,ᵢ(sₜ,ᵢ, eₜ, aₜ,ᵢ)]
+ E[V^λₜ₊₁(sₜ₊₁, eₜ₊₁) | (sₜ, eₜ, aₜ)] }` with `V^λ_{T+1} = 0`. The maximum is over the product
set: the linking constraints are relaxed. -/
noncomputable def lagrangianValue (lam : M.Multiplier) (t : ℕ) (s : ∀ i, S t i) (e : E) : ℝ :=
  (M.lagrangianMDP lam).value t (s, e)

/-- Subproblem `i` in isolation as a Markov decision process on `(sₜ,ᵢ, eₜ)`, with action sets
`Aₜ,ᵢ(sₜ,ᵢ, eₜ)` and reward `rₜ,ᵢ − λₜ(eₜ)ᵀ ℓₜ,ᵢ` (Proposition 3.2(b), p.8). -/
noncomputable def subproblemMDP (lam : M.Multiplier) (i : Fin N) :
    FiniteHorizonMDP M.T (fun t => S t i × E) (fun t => Act t i) where
  avail t x := M.A t i x.1 x.2
  reward t x a := M.r t i x.1 x.2 a - lam t x.2 ⬝ᵥ M.ℓ t i x.1 x.2 a
  kernel t x a y := M.P t i x.1 x.2 a y.1 * M.Q t x.2 y.2
  avail_nonempty t h1 hT x := by
    have hne := M.nonempty_S h1 (by omega : t ≤ M.T + 1)
    obtain ⟨a, ha, -⟩ := M.feasible_nonempty t h1 hT
      (Function.update (fun j => (hne j).some) i x.1) x.2
    exact ⟨a i, by simpa using ha i⟩
  kernel_nonneg t h1 hT x a ha y :=
    mul_nonneg (M.P_nonneg t h1 hT i _ _ _ ha _) (M.Q_nonneg t h1 hT _ _)
  kernel_sum t h1 hT x a ha := M.subLaw_sum h1 hT i x.1 x.2 ha

/-- **The subproblem value function** `V^λₜ,ᵢ(sₜ,ᵢ, eₜ)` of Proposition 3.2(b), p.8:
`V^λₜ,ᵢ(sₜ,ᵢ, eₜ) = max_{aₜ,ᵢ ∈ Aₜ,ᵢ(sₜ,ᵢ, eₜ)} { rₜ,ᵢ(sₜ,ᵢ, eₜ, aₜ,ᵢ) − λₜ(eₜ)ᵀ ℓₜ,ᵢ(sₜ,ᵢ, eₜ, aₜ,ᵢ)
+ E[V^λₜ₊₁,ᵢ(sₜ₊₁,ᵢ, eₜ₊₁) | (sₜ,ᵢ, eₜ, aₜ,ᵢ)] }` with `V^λ_{T+1,i} = 0`. -/
noncomputable def subproblemValue (lam : M.Multiplier) (t : ℕ) (i : Fin N) (s : S t i) (e : E) : ℝ :=
  (M.subproblemMDP lam i).value t (s, e)

end Model

end WeaklyCoupledDP


