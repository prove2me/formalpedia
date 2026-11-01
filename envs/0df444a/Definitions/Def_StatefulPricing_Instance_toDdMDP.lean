-- Prove2me | Definitions.Def_StatefulPricing_Instance_toDdMDP
-- name    : StatefulPricing_Instance_toDdMDP
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T08:25:22.923979+00:00
-- url     : https://prove2.me/theorems/44928734-3c32-4031-900f-82c238533606
-- title:
--   The Dd-MDP of a DRACC instance (§3.1, Eq. (4))
-- statement:
--   Every DRACC instance $I$ induces a Dd-MDP. A state is a pair $(A,\lambda)$ of an active set and an inventory vector, an action is a price vector, and the feasible actions at $(A,\lambda)$ are the price vectors feasible for $\lambda$ on $A$. The initial state is $(A_1,\lambda_1)$. The reward of round $t$ is the payment (Eq. (4))
--   $$
--   f_t(s,x)=\hat q^{x}_t,
--   $$
--   and the transition moves to $(A_{t+1},\lambda')$ with
--   $$
--   \lambda'(i)=\begin{cases}\lambda(i)-\mathbf 1_{i\in\hat A^x_t}, & i\in A_{t+1}\cap A_t,\\ c(i), & i\in A_{t+1}\setminus A_t.\end{cases}
--   $$
--   This is the bridge between posted pricing and the abstract Dd-MDP results (Theorems 3.6 and 3.8).
--
--   **Formalization Note** The paper identifies a state with an inventory vector $\lambda_t$, whose index set is $A_t$; here the index set is the first component of the state. Inventory is $0$ off $A_{t+1}$. The state space and the feasible sets are the same for all instances, so a single chasing oracle can be used on every instance.
-- source:
--   Emek, Lavi, Niazadeh, Shi, Stateful Posted Pricing with Vanishing Regret via Dynamic Deterministic Markov Decision Processes, arXiv:2005.01869v2, §3.1, p.7, Eq. (4) and the transition display

import Mathlib
import Definitions.Def_StatefulPricing_DdMDP
import Definitions.Def_StatefulPricing_Instance

set_option autoImplicit false

namespace StatefulPricing

/-- **The Dd-MDP of a DRACC instance** (arXiv:2005.01869v2, §3.1, p.7): "we identify the state set
S with the set of possible inventory vectors λt … If state s ∈ S is identified with inventory
vector λt, then we identify Xs with the set of price vectors feasible for λt. The reward function
ft is defined by setting ft(s, x) = q̂^x_t (4) … the new state s′ = gt(s, x) is the inventory
vector obtained by posting the price vector x to user t given the inventory vector s, namely,
s′(i) = s(i) − 1_{i∈Â^x_t} if i ∈ At+1 ∩ At; c(i) if i ∈ At+1 \ At."

**Formalization Note.** A state is a pair `(A, λ)` of an active set and an inventory vector on it
(the paper's inventory vector carries its index set `A_t`); actions are price vectors `ℕ → ℝ`.
The initial state is `(A₁, λ₁)`. The transition `g_t` moves to `A_{t+1}` and updates `λ` as in the
display; the reward is the payment `q̂^x_t`. The state space and the feasible sets are the same for
every instance, so one chasing oracle can serve all instances. -/
noncomputable def Instance.toDdMDP {T C W : ℕ} (rank : Finset ℕ → ℕ) (I : Instance T C W) :
    DdMDP (Finset ℕ × (ℕ → ℕ)) (ℕ → ℝ) where
  Xs s := {p | Feasible s.1 s.2 p}
  g t s x := (I.active (t + 1), I.step t s.2 (I.demand rank t x))
  f t _ x := I.pay rank t x
  s₁ := (I.active 1, I.initInv)

end StatefulPricing


