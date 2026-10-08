-- Prove2me | Definitions.Def_KallenbergLP_Transient_TotalReward
-- name    : KallenbergLP_Transient_TotalReward
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T10:19:08.458744+00:00
-- url     : https://prove2.me/theorems/58bd3cd5-fd17-4413-aeea-017338b74e67
-- title:
--   Expected total and discounted rewards, Assumption 3.2.1, p-summability and the functional equation
-- statement:
--   Let $r_{ja}$ be real rewards on the admissible state-action pairs. For a policy $R$ and an initial state $i$, the expected reward in period $t$ is
--
--   $$v_i^t(R)=\sum_{j\in E}\sum_{a\in A(j)}P_R(X_t=j,\,Y_t=a\mid X_1=i)\,r_{ja},$$
--
--   and the expected reward over the first $T$ periods is $V_{i,T}(R)=\sum_{t=1}^{T}v_i^t(R)$.
--
--   1. **Assumption 3.2.1** says that for every initial state $i$ and every policy $R$ the limit $v_i(R)=\lim_{T\to\infty}V_{i,T}(R)$ exists in $[-\infty,+\infty]$.
--   2. The **TMD-value-vector** is $v_i=\sup_{R\in C}v_i(R)$, the supremum over all history-dependent randomized policies, taken in $[-\infty,+\infty]$.
--   3. For a discount factor $\delta$, the **expected discounted reward** is $v_i^\delta(R)=\sum_{t=1}^\infty\delta^{t-1}v_i^t(R)$.
--   4. (**Definition 3.2.1**) With the convention $0\cdot c=0$ for $c\in[-\infty,+\infty]$, a vector $x\in[-\infty,+\infty]^E$ is **p-summable** if for every $i\in E$ and $a\in A(i)$ the sum $\sum_jp_{iaj}x_j$ does not contain both a $+\infty$ and a $-\infty$ term.
--   5. The right-hand side of the functional equation of Theorem 3.2.2 is
--
--   $$\max_{a\in A(i)}\Big\{r_{ia}+\sum_{j\in E}p_{iaj}x_j\Big\}.$$
--
--   These objects carry the standing assumption of Section 3.2 and the statements of Lemma 3.2.1 and Theorems 3.2.1–3.2.2.
--
--   **Formalization Note** Values live in `EReal`. The total reward $v_i(R)$ is encoded as the `limsup` of the partial sums, which is the limit whenever Assumption 3.2.1 holds; every theorem that uses it carries the assumption. Mathlib's `EReal` has $0\cdot(\pm\infty)=0$, matching the book's convention, but $\bot+\top=\bot$; the functional equation is only asserted for p-summable vectors, where no such sum occurs. Lean's period index $t$ is the book's period $t+1$, so the discounted value is $\sum_{t\ge0}\delta^t v_i^{t+1}(R)$. The discount factor is written $\delta$ because $\alpha$ names the action type.
-- source:
--   Kallenberg, Linear Programming and Finite Markovian Control Problems, Mathematical Centre Tracts 148, Mathematisch Centrum, Amsterdam 1983, p. 22, total and discounted reward criteria and TMD-value-vector; p. 37, Assumption 3.2.1; p. 39, Definition 3.2.1 and Theorem 3.2.2

import Definitions.Def_KallenbergLP_Transient_Policy
set_option autoImplicit false

namespace KallenbergLP.Transient

variable {N : ℕ} {α : Type} [Fintype α] [DecidableEq α]

/-- The expected reward `v^{t+1}_i(R)` in period `t + 1` (Lean index `t`), p. 22. -/
def periodReward (M : MDP N α) (r : Fin N → α → ℝ) (R : Policy M)
    (i : Fin N) (t : ℕ) : ℝ :=
  ∑ j : Fin N, ∑ a ∈ M.actions j, occupancy M R i j a t * r j a

/-- Expected reward over the first `T` epochs, using the occupancies of §2.2. -/
def cumulativeReward (M : MDP N α) (r : Fin N → α → ℝ) (R : Policy M)
    (i : Fin N) (T : ℕ) : ℝ :=
  ∑ t ∈ Finset.range T, periodReward M r R i t

/-- Assumption 3.2.1: every policy has an extended-real total reward limit. -/
def TotalRewardExists (M : MDP N α) (r : Fin N → α → ℝ) : Prop :=
  ∀ (R : Policy M) (i : Fin N),
    ∃ v : EReal,
      Filter.Tendsto (fun T : ℕ => (cumulativeReward M r R i T : EReal))
        Filter.atTop (nhds v)

/-- The extended-real total reward `v_i(R)` of one policy (the limit, under Assumption 3.2.1). -/
noncomputable def policyValue (M : MDP N α) (r : Fin N → α → ℝ) (R : Policy M)
    (i : Fin N) : EReal :=
  Filter.limsup (fun T : ℕ => (cumulativeReward M r R i T : EReal)) Filter.atTop

/-- The TMD value vector takes the supremum over every history-dependent randomized policy. -/
noncomputable def valueVector (M : MDP N α) (r : Fin N → α → ℝ) (i : Fin N) : EReal :=
  ⨆ R : Policy M, policyValue M r R i

/-- The expected discounted reward `v^δ_i(R) = ∑_{t ≥ 1} δ^{t-1} v^t_i(R)`, p. 22
(Lean index `t` is epoch `t + 1`). -/
noncomputable def discountedValue (M : MDP N α) (r : Fin N → α → ℝ) (R : Policy M)
    (i : Fin N) (δ : ℝ) : ℝ :=
  ∑' t : ℕ, δ ^ t * periodReward M r R i t

/-- Definition 3.2.1: an extended-real vector `x` is p-summable if no sum `∑_j p_iaj x_j`
with `a ∈ A(i)` contains both a `+∞` and a `−∞` term (terms with `p_iaj = 0` are `0`). -/
def PSummable (M : MDP N α) (x : Fin N → EReal) : Prop :=
  ∀ i a, a ∈ M.actions i →
    ¬ ((∃ j, 0 < M.transition i a j ∧ x j = ⊤) ∧
       (∃ k, 0 < M.transition i a k ∧ x k = ⊥))

/-- The right-hand side `max_{a ∈ A(i)} {r_ia + ∑_j p_iaj x_j}` of the functional equation
of Theorem 3.2.2, computed in `EReal`. -/
noncomputable def bellmanRHS (M : MDP N α) (r : Fin N → α → ℝ) (x : Fin N → EReal)
    (i : Fin N) : EReal :=
  (M.actions i).sup' (M.actions_nonempty i) fun a =>
    (r i a : EReal) + ∑ j : Fin N, (M.transition i a j : EReal) * x j

end KallenbergLP.Transient


