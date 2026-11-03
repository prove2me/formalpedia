-- Prove2me | Definitions.Def_WeaklyCoupledDP_Model_integralityGap
-- name    : WeaklyCoupledDP_Model_integralityGap
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:13:39.916111+00:00
-- url     : https://prove2.me/theorems/35332382-d0e2-47ae-8d4b-20ba74054603
-- title:
--   The separation problem (6), its LP relaxation (9) and the integrality gap $\Delta^V_t(e_t,\ell_t,b_t)$
-- statement:
--   Fix a candidate ALP solution $V = (V_{t,i}(s_{t,i},e_t))$. Its **slack** at $(t,i,s_{t,i},e_t,a_{t,i})$ is
--   $$
--   \delta^V_{t,i}(s_{t,i},e_t,a_{t,i}) = V_{t,i}(s_{t,i},e_t) - r_{t,i}(s_{t,i},e_t,a_{t,i}) - \mathbb E\big[V_{t+1,i}(s_{t+1,i},e_{t+1}) \,\big|\, (s_{t,i},e_t,a_{t,i})\big].
--   $$
--   For a period $t$ and exogenous state $e_t$, let $\Gamma_{t,i}(e_t) = \{(s_{t,i},a_{t,i}) : a_{t,i} \in A_{t,i}(s_{t,i},e_t)\}$. The **$(t,e_t)$-separation problem** (6) is
--   $$
--   \begin{aligned}
--   \text{minimize}\quad & \sum_{i=1}^N \sum_{(s,a) \in \Gamma_{t,i}(e_t)} x_{t,i}(s,e_t,a)\, \delta^V_{t,i}(s,e_t,a)\\
--   \text{subject to}\quad & \sum_{i=1}^N \sum_{(s,a) \in \Gamma_{t,i}(e_t)} \ell_{t,i}(s,e_t,a)\, x_{t,i}(s,e_t,a) \le b_t(e_t), \qquad \sum_{(s,a) \in \Gamma_{t,i}(e_t)} x_{t,i}(s,e_t,a) = 1 \ \ \forall i,
--   \end{aligned}
--   $$
--   over $x_{t,i}(s,e_t,a) \in \{0,1\}$; its **LP relaxation** (9) is the same problem over $x_{t,i}(s,e_t,a) \in [0,1]$. The **integrality gap** is the optimal value of (6) minus the optimal value of (9):
--   $$
--   \Delta^V_t(e_t,\ell_t,b_t) = \min(6) - \min(9) \ \ge 0 .
--   $$
--
--   The integrality gap is the quantity that controls the distance between the ALP and Lagrangian bounds (Theorem 4.1).
--
--   **Formalization Note** The variables $x_{t,i}$ are real functions on $\Gamma_{t,i}(e_t)$. The two optimal values are infima (`sInf`) of the objective over the feasible sets. For $1 \le t \le T$ both feasible sets are nonempty (by the standing assumption) and compact, so both infima are attained minima; this is proved in the mission's verification file, together with $\Delta \ge 0$.
-- source:
--   Brown & Zhang, On the Strength of Relaxations of Weakly Coupled Stochastic Dynamic Programs, SSRN 3849573 (Feb. 6, 2022), δ^V and problem (6), p.6 (PDF p.7); LP (9), p.11 (PDF p.12); Δ^V_t, p.12 (PDF p.13)

import Mathlib
import Definitions.Def_WeaklyCoupledDP_Model_ALPFeasible

open Finset

namespace WeaklyCoupledDP

namespace Model

variable {N : ℕ} {S : ℕ → Fin N → Type*} {E : Type*} {Act : ℕ → Fin N → Type*} {L : ℕ → ℕ}
  [∀ t i, Fintype (S t i)] [Fintype E] (M : Model N S E Act L)

/-- The state-action set `Γₜ,ᵢ(eₜ) = {(sₜ,ᵢ, aₜ,ᵢ) : aₜ,ᵢ ∈ Aₜ,ᵢ(sₜ,ᵢ, eₜ)}` (§2, p.5). -/
abbrev Gamma (t : ℕ) (i : Fin N) (e : E) : Type _ :=
  Σ s : S t i, {a // a ∈ M.A t i s e}

/-- The slack `δ^V_{t,i}(sₜ,ᵢ, eₜ, aₜ,ᵢ) = Vₜ,ᵢ(sₜ,ᵢ, eₜ) − rₜ,ᵢ(sₜ,ᵢ, eₜ, aₜ,ᵢ)
− E[Vₜ₊₁,ᵢ(sₜ₊₁,ᵢ, eₜ₊₁) | (sₜ,ᵢ, eₜ, aₜ,ᵢ)]` of a candidate `V` (§3.1.1, p.6). -/
def delta (V : M.ValueArray) (t : ℕ) (i : Fin N) (s : S t i) (e : E) (a : Act t i) : ℝ :=
  V t i s e - M.r t i s e a - M.subExp t i s e a (V (t + 1) i)

/-- The objective `∑ᵢ ∑_{(sₜ,ᵢ, aₜ,ᵢ) ∈ Γₜ,ᵢ(eₜ)} xₜ,ᵢ(sₜ,ᵢ, eₜ, aₜ,ᵢ) δ^V_{t,i}(sₜ,ᵢ, eₜ, aₜ,ᵢ)` of the
separation problem (6), p.6, and of its LP relaxation (9a), p.11. -/
def sepObjective (V : M.ValueArray) (t : ℕ) (e : E) (x : ∀ i, M.Gamma t i e → ℝ) : ℝ :=
  ∑ i, ∑ p : M.Gamma t i e, x i p * M.delta V t i p.1 e p.2

/-- The constraints of (6) and of its relaxation, (9b) and (9c):
`∑ᵢ ∑_{(s, a) ∈ Γₜ,ᵢ(eₜ)} ℓₜ,ᵢ(s, eₜ, a) xₜ,ᵢ(s, eₜ, a) ≤ bₜ(eₜ)` (componentwise) and
`∑_{(s, a) ∈ Γₜ,ᵢ(eₜ)} xₜ,ᵢ(s, eₜ, a) = 1` for all `i`. -/
def SepConstraints (t : ℕ) (e : E) (x : ∀ i, M.Gamma t i e → ℝ) : Prop :=
  (∀ l, ∑ i, ∑ p : M.Gamma t i e, M.ℓ t i p.1 e p.2 l * x i p ≤ M.b t e l) ∧
    ∀ i, ∑ p : M.Gamma t i e, x i p = 1

/-- The feasible set of the binary separation problem (6), p.6: `xₜ,ᵢ ∈ {0, 1}`. -/
def sepIPFeasible (t : ℕ) (e : E) : Set (∀ i, M.Gamma t i e → ℝ) :=
  {x | (∀ i p, x i p = 0 ∨ x i p = 1) ∧ M.SepConstraints t e x}

/-- The feasible set of the LP relaxation (9), p.11: `xₜ,ᵢ ∈ [0, 1]`. -/
def sepLPFeasible (t : ℕ) (e : E) : Set (∀ i, M.Gamma t i e → ℝ) :=
  {x | (∀ i p, 0 ≤ x i p ∧ x i p ≤ 1) ∧ M.SepConstraints t e x}

/-- The optimal value of the separation problem (6), p.6. For `1 ≤ t ≤ T` the feasible set is
nonempty and finite, so the infimum is an attained minimum (proved in the mission's sanity file). -/
noncomputable def sepIPValue (V : M.ValueArray) (t : ℕ) (e : E) : ℝ :=
  sInf (M.sepObjective V t e '' M.sepIPFeasible t e)

/-- The optimal value of the LP relaxation (9), p.11. For `1 ≤ t ≤ T` the feasible set is nonempty
and compact, so the infimum is an attained minimum (proved in the mission's sanity file). -/
noncomputable def sepLPValue (V : M.ValueArray) (t : ℕ) (e : E) : ℝ :=
  sInf (M.sepObjective V t e '' M.sepLPFeasible t e)

/-- **The integrality gap** `Δ^V_t(eₜ, ℓₜ, bₜ)` (p.12): the difference between the optimal values of
the separation problem (6) and of its LP relaxation (9). It is `≥ 0`. -/
noncomputable def integralityGap (V : M.ValueArray) (t : ℕ) (e : E) : ℝ :=
  M.sepIPValue V t e - M.sepLPValue V t e

end Model

end WeaklyCoupledDP


