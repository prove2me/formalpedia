-- Prove2me | Definitions.Def_WeaklyCoupledDP_Model
-- name    : WeaklyCoupledDP_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:12:13.021387+00:00
-- url     : https://prove2.me/theorems/9c94e054-da55-47e1-ac5d-b53c6b4799aa
-- title:
--   Weakly coupled stochastic dynamic program (§2)
-- statement:
--   A **weakly coupled stochastic dynamic program** (Brown and Zhang, §2) has periods $t \in \{1,\dots,T\}$ and $N$ subproblems $i \in \{1,\dots,N\}$.
--
--   1. **States.** Subproblem $i$ has a finite state space $S_{t,i}$ in period $t$; the joint state is $s_t = (s_{t,1},\dots,s_{t,N}) \in S_t = \prod_i S_{t,i}$. An exogenous state $e_t$ lives in a finite set $E$. The initial state $(s_1, e_1)$ is given.
--   2. **Actions.** In state $(s_t, e_t)$ subproblem $i$ chooses $a_{t,i}$ from a finite set $A_{t,i}(s_{t,i}, e_t)$; the product set is $\mathbf A_t(s_t,e_t) = \prod_i A_{t,i}(s_{t,i}, e_t)$.
--   3. **Linking constraints.** There are $L_t$ constraints $\sum_{i=1}^N \ell_{t,i}(s_{t,i}, e_t, a_{t,i}) \le b_t(e_t)$ with $\ell_{t,i}(\cdot), b_t(e_t) \in \mathbb R^{L_t}$ (componentwise). The feasible action set is
--   $$
--   \mathcal A_t(s_t,e_t) = \Big\{ a_t \in \mathbf A_t(s_t,e_t) : \sum_{i=1}^N \ell_{t,i}(s_{t,i}, e_t, a_{t,i}) \le b_t(e_t) \Big\},
--   $$
--   and it is assumed nonempty in every period and every state (the standing assumption of §2).
--   4. **Rewards and transitions.** Subproblem $i$ earns $r_{t,i}(s_{t,i}, e_t, a_{t,i}) \in \mathbb R$ and moves to $s_{t+1,i}$ with probability $P_{t,i}(s_{t+1,i} \mid s_{t,i}, e_t, a_{t,i})$, independently across subproblems given $(s_t, e_t, a_t)$; the exogenous state moves with probability $Q_t(e_{t+1} \mid e_t)$, independently of the subproblems. So one-step conditional expectations are taken under the product law $\prod_i P_{t,i}(s'_i \mid s_{t,i}, e_t, a_{t,i})\, Q_t(e' \mid e_t)$.
--
--   The module also defines the total reward $r_t(s_t,e_t,a_t) = \sum_i r_{t,i}$, the joint and the single-subproblem one-step expectations, and the law of $e_\tau$ given $e_t$ through the time-dependent kernels $Q_t, \dots, Q_{\tau-1}$; the expectation $\mathbb E_{e_t}[\cdot]$ of the paper is the one given the initial $e_1$. It proves that every state space $S_{t,i}$, $1 \le t \le T+1$, is nonempty.
--
--   **Formalization Note** Periods are natural numbers, $1$-based; data at $t = 0$ and $t > T$ are never read. The functions $\ell$, $r$, $P$ are total, and their values at an action $a \notin A_{t,i}(s, e)$ are not part of the model: the probability conditions on $P$ are required only at available actions and only for $1 \le t \le T$, those on $Q$ only for $1 \le t \le T$. The action sets are `Finset`s of an arbitrary action type.
-- source:
--   Brown & Zhang, On the Strength of Relaxations of Weakly Coupled Stochastic Dynamic Programs, SSRN 3849573 (Feb. 6, 2022), §2, pp.3–4 (PDF pp.4–5); state-action sets Γ, p.5 (PDF p.6)

import Mathlib

open Finset

namespace WeaklyCoupledDP

/-- **A weakly coupled stochastic dynamic program** (Brown & Zhang, *On the Strength of
Relaxations of Weakly Coupled Stochastic Dynamic Programs*, SSRN 3849573 (Feb. 6, 2022), §2,
pp.3–4).

Periods are `t ∈ {1, …, T}`; there are `N` subproblems `i : Fin N`. Subproblem `i` has the finite
state space `S t i` in period `t`; the exogenous state lives in the finite set `E`. In period `t`
and state `(sₜ,ᵢ, eₜ)` subproblem `i` chooses an action in the finite set `A t i sₜ,ᵢ eₜ` (a
`Finset` of the action type `Act t i`). There are `L t` linking constraints
`∑ᵢ ℓₜ,ᵢ(sₜ,ᵢ, eₜ, aₜ,ᵢ) ≤ bₜ(eₜ)` in `ℝ^{Lₜ}` (componentwise). Subproblem `i` earns
`rₜ,ᵢ(sₜ,ᵢ, eₜ, aₜ,ᵢ)` and moves to `sₜ₊₁,ᵢ` with probability `Pₜ,ᵢ(sₜ₊₁,ᵢ | sₜ,ᵢ, eₜ, aₜ,ᵢ)`,
independently across subproblems; the exogenous state moves with probability `Qₜ(eₜ₊₁ | eₜ)`.
The initial state `(s₁, e₁)` is given.

**Formalization Note.**
* Periods are natural numbers, `1`-based as in the paper; the data at `t = 0` and `t > T` are never
  read by any statement (every hypothesis on the data is restricted to `1 ≤ t ≤ T`), except that
  `S (T+1) i` is the state space of the terminal period `T + 1`.
* `ℓ`, `r`, `P` are total functions; their values at an action `a ∉ A t i s e` are not part of the
  model and nothing constrains them. Likewise `P` and `Q` are required to be probability vectors
  only for `1 ≤ t ≤ T` and available actions.
* The state spaces are not assumed nonempty: `s₁` and the two conditions below give that in every
  period `1, …, T + 1` (`nonempty_S`).
* The standing assumption of §2 ("assume this set is nonempty in every period and state") is the
  field `feasible_nonempty`: for every `1 ≤ t ≤ T`, every joint state `s` and every `e`, some
  `a ∈ 𝐀ₜ(s, e)` satisfies the linking constraints. -/
structure Model (N : ℕ) (S : ℕ → Fin N → Type*) (E : Type*) (Act : ℕ → Fin N → Type*)
    (L : ℕ → ℕ) [∀ t i, Fintype (S t i)] [Fintype E] where
  /-- The horizon `T`. -/
  T : ℕ
  /-- The given initial joint state `s₁ = (s₁,₁, …, s₁,N)`. -/
  s₁ : ∀ i, S 1 i
  /-- The given initial exogenous state `e₁`. -/
  e₁ : E
  /-- The action sets `Aₜ,ᵢ(sₜ,ᵢ, eₜ)`. -/
  A : ∀ t i, S t i → E → Finset (Act t i)
  /-- The linking-constraint coefficient vectors `ℓₜ,ᵢ(sₜ,ᵢ, eₜ, aₜ,ᵢ) ∈ ℝ^{Lₜ}`. -/
  ℓ : ∀ t i, S t i → E → Act t i → Fin (L t) → ℝ
  /-- The linking-constraint right-hand sides `bₜ(eₜ) ∈ ℝ^{Lₜ}`. -/
  b : ∀ t, E → Fin (L t) → ℝ
  /-- The rewards `rₜ,ᵢ(sₜ,ᵢ, eₜ, aₜ,ᵢ)`. -/
  r : ∀ t i, S t i → E → Act t i → ℝ
  /-- The subproblem transition probabilities `Pₜ,ᵢ(sₜ₊₁,ᵢ | sₜ,ᵢ, eₜ, aₜ,ᵢ)`. -/
  P : ∀ t i, S t i → E → Act t i → S (t + 1) i → ℝ
  /-- The exogenous transition probabilities `Qₜ(eₜ₊₁ | eₜ)`. -/
  Q : ℕ → E → E → ℝ
  P_nonneg : ∀ t, 1 ≤ t → t ≤ T → ∀ i s e a, a ∈ A t i s e → ∀ s', 0 ≤ P t i s e a s'
  P_sum : ∀ t, 1 ≤ t → t ≤ T → ∀ i s e a, a ∈ A t i s e → ∑ s', P t i s e a s' = 1
  Q_nonneg : ∀ t, 1 ≤ t → t ≤ T → ∀ e e', 0 ≤ Q t e e'
  Q_sum : ∀ t, 1 ≤ t → t ≤ T → ∀ e, ∑ e', Q t e e' = 1
  feasible_nonempty : ∀ t, 1 ≤ t → t ≤ T → ∀ (s : ∀ i, S t i) (e : E),
    ∃ a : ∀ i, Act t i, (∀ i, a i ∈ A t i (s i) e) ∧
      ∀ l, ∑ i, ℓ t i (s i) e (a i) l ≤ b t e l

namespace Model

variable {N : ℕ} {S : ℕ → Fin N → Type*} {E : Type*} {Act : ℕ → Fin N → Type*} {L : ℕ → ℕ}
  [∀ t i, Fintype (S t i)] [Fintype E] (M : Model N S E Act L)

/-- The product action set `𝐀ₜ(sₜ, eₜ) = ⊗ᵢ Aₜ,ᵢ(sₜ,ᵢ, eₜ)` (§2, p.4). -/
def prodActions (t : ℕ) (s : ∀ i, S t i) (e : E) : Finset (∀ i, Act t i) :=
  Fintype.piFinset fun i => M.A t i (s i) e

/-- The total linking-constraint usage `∑ᵢ ℓₜ,ᵢ(sₜ,ᵢ, eₜ, aₜ,ᵢ) ∈ ℝ^{Lₜ}` (§2, p.4). -/
def linkSum (t : ℕ) (s : ∀ i, S t i) (e : E) (a : ∀ i, Act t i) : Fin (L t) → ℝ :=
  fun l => ∑ i, M.ℓ t i (s i) e (a i) l

/-- `a ∈ 𝒜ₜ(sₜ, eₜ)`: the joint action is in the product set and satisfies every linking
constraint `∑ᵢ ℓₜ,ᵢ ≤ bₜ(eₜ)` (§2, p.4). -/
def IsFeasibleAction (t : ℕ) (s : ∀ i, S t i) (e : E) (a : ∀ i, Act t i) : Prop :=
  (∀ i, a i ∈ M.A t i (s i) e) ∧ ∀ l, M.linkSum t s e a l ≤ M.b t e l

open Classical in
/-- The feasible action set `𝒜ₜ(sₜ, eₜ) = {aₜ ∈ 𝐀ₜ(sₜ, eₜ) : ∑ᵢ ℓₜ,ᵢ ≤ bₜ(eₜ)}` (§2, p.4), as a
`Finset`. -/
noncomputable def feasActions (t : ℕ) (s : ∀ i, S t i) (e : E) : Finset (∀ i, Act t i) :=
  (M.prodActions t s e).filter fun a => M.IsFeasibleAction t s e a

theorem mem_feasActions {t : ℕ} {s : ∀ i, S t i} {e : E} {a : ∀ i, Act t i} :
    a ∈ M.feasActions t s e ↔ M.IsFeasibleAction t s e a := by
  classical
  simp only [feasActions, mem_filter, prodActions, Fintype.mem_piFinset]
  exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩

/-- The total reward `rₜ(sₜ, eₜ, aₜ) = ∑ᵢ rₜ,ᵢ(sₜ,ᵢ, eₜ, aₜ,ᵢ)` (§2, p.4). -/
def reward (t : ℕ) (s : ∀ i, S t i) (e : E) (a : ∀ i, Act t i) : ℝ :=
  ∑ i, M.r t i (s i) e (a i)

/-- The one-step conditional expectation `E[f(sₜ₊₁, eₜ₊₁) | (sₜ, eₜ, aₜ)]` under the product law
`∏ᵢ Pₜ,ᵢ(s'ᵢ | sₜ,ᵢ, eₜ, aₜ,ᵢ) · Qₜ(e' | eₜ)` (§2, p.4: subproblem transitions independent given
`(sₜ, eₜ, aₜ)`, exogenous transitions independent of the subproblems). -/
def jointExp (t : ℕ) (s : ∀ i, S t i) (e : E) (a : ∀ i, Act t i)
    (f : (∀ i, S (t + 1) i) → E → ℝ) : ℝ :=
  ∑ s' : (∀ i, S (t + 1) i), ∑ e' : E,
    (∏ i, M.P t i (s i) e (a i) (s' i)) * M.Q t e e' * f s' e'

/-- The subproblem conditional expectation `E[f(sₜ₊₁,ᵢ, eₜ₊₁) | (sₜ,ᵢ, eₜ, aₜ,ᵢ)]
= ∑_{s', e'} Pₜ,ᵢ(s' | sₜ,ᵢ, eₜ, aₜ,ᵢ) Qₜ(e' | eₜ) f(s', e')`. -/
def subExp (t : ℕ) (i : Fin N) (s : S t i) (e : E) (a : Act t i) (f : S (t + 1) i → E → ℝ) : ℝ :=
  ∑ s', ∑ e', M.P t i s e a s' * M.Q t e e' * f s' e'

open Classical in
/-- `exoTrans t k e e'` is the probability that `e_{t+k} = e'` given `eₜ = e`, computed through the
time-dependent kernels `Qₜ, …, Q_{t+k−1}`. -/
noncomputable def exoTrans (t : ℕ) : ℕ → E → E → ℝ
  | 0 => fun e e' => if e' = e then 1 else 0
  | k + 1 => fun e e' => ∑ e'', exoTrans t k e e'' * M.Q (t + k) e'' e'

/-- `exoProb t e = P(eₜ = e | e₁)`, the law of `eₜ` given the initial exogenous state; the
expectation `E_{eₜ}[g(eₜ)]` of the paper is `∑ₑ exoProb t e · g e` (for `t ≥ 1`; at `t = 1` it is
evaluation at `e₁`). -/
noncomputable def exoProb (t : ℕ) (e : E) : ℝ :=
  M.exoTrans 1 (t - 1) M.e₁ e

/-- The joint transition law `∏ᵢ Pₜ,ᵢ(s'ᵢ | sₜ,ᵢ, eₜ, aₜ,ᵢ) · Qₜ(e' | eₜ)` is nonnegative at an
available joint action. -/
theorem jointLaw_nonneg {t : ℕ} (h1 : 1 ≤ t) (hT : t ≤ M.T) (s : ∀ i, S t i) (e : E)
    {a : ∀ i, Act t i} (ha : ∀ i, a i ∈ M.A t i (s i) e) (s' : ∀ i, S (t + 1) i) (e' : E) :
    0 ≤ (∏ i, M.P t i (s i) e (a i) (s' i)) * M.Q t e e' :=
  mul_nonneg (prod_nonneg fun i _ => M.P_nonneg t h1 hT i _ _ _ (ha i) _) (M.Q_nonneg t h1 hT e e')

/-- The joint transition law sums to one at an available joint action. -/
theorem jointLaw_sum {t : ℕ} (h1 : 1 ≤ t) (hT : t ≤ M.T) (s : ∀ i, S t i) (e : E)
    {a : ∀ i, Act t i} (ha : ∀ i, a i ∈ M.A t i (s i) e) :
    ∑ y : (∀ i, S (t + 1) i) × E, (∏ i, M.P t i (s i) e (a i) (y.1 i)) * M.Q t e y.2 = 1 := by
  rw [Fintype.sum_prod_type]
  simp only [← mul_sum, M.Q_sum t h1 hT e, mul_one]
  have := Finset.prod_univ_sum (fun _ => (Finset.univ : Finset _))
    (fun i (s' : S (t + 1) i) => M.P t i (s i) e (a i) s')
  rw [Fintype.piFinset_univ] at this
  rw [← this]
  exact prod_eq_one fun i _ => M.P_sum t h1 hT i _ _ _ (ha i)

/-- The subproblem transition law `Pₜ,ᵢ(s' | sₜ,ᵢ, eₜ, aₜ,ᵢ) · Qₜ(e' | eₜ)` sums to one at an
available action. -/
theorem subLaw_sum {t : ℕ} (h1 : 1 ≤ t) (hT : t ≤ M.T) (i : Fin N) (s : S t i) (e : E)
    {a : Act t i} (ha : a ∈ M.A t i s e) :
    ∑ y : S (t + 1) i × E, M.P t i s e a y.1 * M.Q t e y.2 = 1 := by
  rw [Fintype.sum_prod_type]
  simp only [← mul_sum, M.Q_sum t h1 hT e, mul_one]
  exact M.P_sum t h1 hT i s e a ha

/-- All state spaces of the periods `1, …, T + 1` are nonempty: `s₁` is given, and a transition from
a feasible action has to land somewhere. -/
theorem nonempty_S {t : ℕ} (h1 : 1 ≤ t) (hT : t ≤ M.T + 1) : ∀ i, Nonempty (S t i) := by
  induction t, h1 using Nat.le_induction with
  | base => exact fun i => ⟨M.s₁ i⟩
  | succ t h1 ih =>
    intro i
    have hne := ih (by omega)
    obtain ⟨a, ha, -⟩ := M.feasible_nonempty t h1 (by omega) (fun i => (hne i).some) M.e₁
    have hsum := M.P_sum t h1 (by omega) i _ _ _ (ha i)
    by_contra hemp
    rw [not_nonempty_iff] at hemp
    simp at hsum

end Model

end WeaklyCoupledDP


