-- Prove2me | Definitions.Def_QLearning_Convergence_Setting
-- name    : QLearning_Convergence_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:53:20.377724+00:00
-- url     : https://prove2.me/theorems/197f841e-1921-4683-ab8f-53cd536b1a11
-- title:
--   §2 and Appendix, pp. 280–282, 287 — finite MDP, Q* (Bellman optimality), the Q-learning iteration (1)–(2), condition (3), the action-replay process, finite action-sequence values
-- statement:
--   This file fixes the objects of Watkins and Dayan's convergence proof for Q-learning.
--
--   **The real process (§2, p. 280).** A finite controlled Markov process consists of a finite state set $X$, a finite nonempty action set $\mathfrak A$ (the same in every state, note 1), mean rewards $\mathcal R_x(a)$ and transition probabilities $P_{xy}[a]\ge 0$ with $\sum_y P_{xy}[a]=1$. For $Q : X\times\mathfrak A\to\mathbb R$ write $V(y)=\max_b Q(y,b)$ (equation (2)). A function $Q$ is an **optimal action-value function** for discount $\gamma$ when it solves the Bellman optimality equation
--   $$Q(x,a)=\mathcal R_x(a)+\gamma\sum_y P_{xy}[a]\max_b Q(y,b)\qquad\text{for all }x,a;$$
--   for $0\le\gamma<1$ this equation has exactly one solution, the paper's $Q^*$ (pp. 280–281).
--
--   **Q-learning (1), p. 281.** Given episode data $(x_n,a_n,y_n,r_n,\alpha_n)_{n\ge1}$ and initial values $Q_0$, set
--   $$Q_n(x,a)=\begin{cases}(1-\alpha_n)Q_{n-1}(x,a)+\alpha_n\bigl[r_n+\gamma V_{n-1}(y_n)\bigr] & x=x_n,\ a=a_n,\\ Q_{n-1}(x,a) & \text{otherwise,}\end{cases}$$
--   with $V_{n-1}(y)=\max_b Q_{n-1}(y,b)$. The **visit rate** of $(x,a)$ at episode $n$ is $\alpha_n$ if $(x_n,a_n)=(x,a)$ and $0$ otherwise; summing it over $n$ gives the sums $\sum_i\alpha_{n^i(x,a)}$ over the visits $n^i(x,a)$ of condition (3).
--
--   **The action-replay process (ARP), p. 282 and Appendix p. 287.** At ARP state $\langle x,n\rangle$ with action $a$, the cards $k=1,\dots,n$ whose episode tried $a$ in $x$ are examined from the top; card $k$ is replayed with probability
--   $$w_n(x,a;k)=\alpha_k\prod_{\substack{k<j\le n\\ (x_j,a_j)=(x,a)}}(1-\alpha_j),$$
--   yielding reward $r_k$ and moving to $\langle y_k,k-1\rangle$; with the remaining probability $\prod_{1\le j\le n,\,(x_j,a_j)=(x,a)}(1-\alpha_j)$ the bottom card is reached, the reward is $Q_0(x,a)$ and the ARP absorbs. The discount is $\gamma$. For a deterministic Markov policy $\pi$ of the ARP (action $\pi(y,m)$ at $\langle y,m\rangle$) the value of taking $a$ at $\langle x,n\rangle$ and following $\pi$ is defined by recursion on the level, and the optimal ARP action value $Q^*_{\mathrm{ARP}}(\langle x,n\rangle,a)$ is its supremum over all such policies. The file also defines the ARP's expected immediate reward $\mathcal R^{(n)}_x(a)$, the aggregated transition probabilities $P^{(n)}_{xy}[a]=\sum_{m=1}^{n-1}P^{\mathrm{ARP}}_{\langle x,n\rangle,\langle y,m\rangle}[a]$, and the probability that the ARP is still at a level $\ge l$ after a given finite sequence of actions.
--
--   **Finite action sequences (note 3, Lemmas B.1, B.4).** $\bar Q(x,a_1,\dots,a_s)$ is the expected discounted reward of performing the fixed actions $a_1,\dots,a_s$ from $x$ in the real process, with $0$ terminal reward; the concatenated-chain value uses the $i$-th chain $(P^i,\mathcal R^i)$ at the $i$-th step; $V^\pi$ is the value $\sum_t\gamma^t(P_\pi^t\mathcal R_\pi)(x)$ of a stationary deterministic policy $\pi$, and the value of $a_1,\dots,a_s$ followed by $\pi$ uses $V^\pi$ as terminal value.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** Episode $n\ge1$ of the paper is Lean index $n$; index $0$ of the episode data is unused and `qIter … 0` is $Q_0$. The maximum in (2) is `Finset.sup'` over the nonempty finite action type. The ARP deck at level $n$ includes card $n$ (the card game of p. 282 and the proof of Lemma A; the appendix's $n^i<n$ is a slip). $P^{(n)}$ keeps the printed range $m=1,\dots,n-1$ (cards $2,\dots,n$). Optimality in the ARP is over deterministic Markov policies, which suffices for a process whose level strictly decreases at each step.
-- source:
--   Watkins & Dayan, Technical Note: Q-Learning, Machine Learning 8 (1992), pp. 280–282 and 287, §2, (1)–(3), §3, Appendix (the action-replay process), notes 1–3

import Mathlib

namespace QLearning.Convergence

open Finset

/-- A finite controlled Markov process (Watkins & Dayan, §2, p. 280): the mean reward `R x a` = ℛ_x(a)
of performing action `a` in state `x`, and the transition law `P x a y` = P_xy[a]. -/
structure FiniteMDP (X A : Type) [Fintype X] where
  /-- mean reward ℛ_x(a) -/
  R : X → A → ℝ
  /-- transition probability P_xy[a] -/
  P : X → A → X → ℝ
  P_nonneg : ∀ x a y, 0 ≤ P x a y
  P_sum : ∀ x a, ∑ y, P x a y = 1

variable {X A : Type} [Fintype X] [DecidableEq X] [Fintype A] [DecidableEq A] [Nonempty A]

/-- Equation (2): `V(y) = max_b Q(y, b)`, a genuine maximum over the finite nonempty action set. -/
noncomputable def vmax (Q : X → A → ℝ) (y : X) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (Q y)

/-- `Q` solves the Bellman optimality equation of pp. 280–281:
`Q(x, a) = ℛ_x(a) + γ Σ_y P_xy[a] max_b Q(y, b)` for all `x, a`. -/
def IsOptimalQ (M : FiniteMDP X A) (γ : ℝ) (Q : X → A → ℝ) : Prop :=
  ∀ x a, Q x a = M.R x a + γ * ∑ y, M.P x a y * vmax Q y

/-- The Q-learning iteration (1), pathwise. Lean index `n` is the paper's episode `n ≥ 1`
(index `0` of the episode data is unused); `qIter … n` is `Q_n` and `qIter … 0 = Q₀`. -/
noncomputable def qIter (γ : ℝ) (Q0 : X → A → ℝ) (xs : ℕ → X) (as : ℕ → A) (ys : ℕ → X)
    (rs : ℕ → ℝ) (αs : ℕ → ℝ) : ℕ → X → A → ℝ
  | 0 => Q0
  | n + 1 => fun x a =>
      if x = xs (n + 1) ∧ a = as (n + 1) then
        (1 - αs (n + 1)) * qIter γ Q0 xs as ys rs αs n x a
          + αs (n + 1) * (rs (n + 1) + γ * vmax (qIter γ Q0 xs as ys rs αs n) (ys (n + 1)))
      else qIter γ Q0 xs as ys rs αs n x a

omit [Fintype X] in
@[simp] theorem qIter_zero (γ : ℝ) (Q0 : X → A → ℝ) (xs : ℕ → X) (as : ℕ → A) (ys : ℕ → X)
    (rs : ℕ → ℝ) (αs : ℕ → ℝ) : qIter γ Q0 xs as ys rs αs 0 = Q0 := rfl

omit [Fintype X] in
theorem qIter_succ (γ : ℝ) (Q0 : X → A → ℝ) (xs : ℕ → X) (as : ℕ → A) (ys : ℕ → X)
    (rs : ℕ → ℝ) (αs : ℕ → ℝ) (n : ℕ) :
    qIter γ Q0 xs as ys rs αs (n + 1) = fun x a =>
      if x = xs (n + 1) ∧ a = as (n + 1) then
        (1 - αs (n + 1)) * qIter γ Q0 xs as ys rs αs n x a
          + αs (n + 1) * (rs (n + 1) + γ * vmax (qIter γ Q0 xs as ys rs αs n) (ys (n + 1)))
      else qIter γ Q0 xs as ys rs αs n x a := rfl

/-- The learning rate charged to the pair `(x, a)` at episode `n`: `α_n` if episode `n` tried `a` in `x`,
and `0` otherwise. Summing it over episodes gives the sums over visits `Σ_i α_{n^i(x,a)}` of (3). -/
def visitRate (xs : ℕ → X) (as : ℕ → A) (αs : ℕ → ℝ) (x : X) (a : A) (n : ℕ) : ℝ :=
  if xs n = x ∧ as n = a then αs n else 0

/-! ### The action-replay process (Appendix, p. 287; §3, p. 282)

The deck at level `n` holds the cards `k = 1, …, n` (card `n` included). At ARP state `⟨x, n⟩` with
action `a`, the matching cards are searched from the top; card `k` is replayed with probability
`α_k · Π_{matching j, k < j ≤ n} (1 - α_j)`, giving reward `r_k` and moving to `⟨y_k, k - 1⟩`; if every
matching card is passed over, the ARP absorbs with reward `Q₀(x, a)`. -/

/-- Probability that card `k` is the one replayed at ARP state `⟨x, n⟩` under action `a`. -/
noncomputable def arpWeight (xs : ℕ → X) (as : ℕ → A) (αs : ℕ → ℝ) (n : ℕ) (x : X) (a : A)
    (k : ℕ) : ℝ :=
  if 1 ≤ k ∧ k ≤ n ∧ xs k = x ∧ as k = a then
    αs k * ∏ j ∈ (Finset.Ioc k n).filter (fun j => xs j = x ∧ as j = a), (1 - αs j)
  else 0

/-- Probability that the bottom card is reached at ARP state `⟨x, n⟩` under action `a`
(the ARP absorbs, with reward `Q₀(x, a)`). -/
noncomputable def arpAbsorb (xs : ℕ → X) (as : ℕ → A) (αs : ℕ → ℝ) (n : ℕ) (x : X) (a : A) : ℝ :=
  ∏ j ∈ (Finset.Icc 1 n).filter (fun j => xs j = x ∧ as j = a), (1 - αs j)

/-- Expected discounted value in the ARP of taking action `a` at `⟨x, n⟩` and then following the
deterministic Markov policy `π` (action `π y m` at `⟨y, m⟩`). Replaying card `k + 1` (`k < n`) moves to
level `k`; the recursion is on the level, which strictly decreases. -/
noncomputable def arpQ (γ : ℝ) (Q0 : X → A → ℝ) (xs : ℕ → X) (as : ℕ → A) (ys : ℕ → X)
    (rs : ℕ → ℝ) (αs : ℕ → ℝ) (π : X → ℕ → A) : ℕ → X → A → ℝ
  | n, x, a =>
    (∑ k : Fin n, arpWeight xs as αs n x a (k + 1) *
        (rs (k + 1) + γ * arpQ γ Q0 xs as ys rs αs π k (ys (k + 1)) (π (ys (k + 1)) k)))
      + arpAbsorb xs as αs n x a * Q0 x a
  termination_by n => n
  decreasing_by exact k.isLt

/-- The optimal action value `Q*_ARP(⟨x, n⟩, a)` of the ARP: the supremum over deterministic Markov
policies of the ARP of `arpQ`. (Only the finitely many levels below `n` matter, so the set of values is
finite and the supremum is a maximum.) -/
noncomputable def arpQStar (γ : ℝ) (Q0 : X → A → ℝ) (xs : ℕ → X) (as : ℕ → A) (ys : ℕ → X)
    (rs : ℕ → ℝ) (αs : ℕ → ℝ) (n : ℕ) (x : X) (a : A) : ℝ :=
  ⨆ π : X → ℕ → A, arpQ γ Q0 xs as ys rs αs π n x a

/-- The expected immediate reward `ℛ^{(n)}_x(a)` of action `a` at ARP state `⟨x, n⟩`. -/
noncomputable def arpReward (xs : ℕ → X) (as : ℕ → A) (rs : ℕ → ℝ) (αs : ℕ → ℝ)
    (Q0 : X → A → ℝ) (n : ℕ) (x : X) (a : A) : ℝ :=
  (∑ k ∈ Finset.Icc 1 n, arpWeight xs as αs n x a k * rs k) + arpAbsorb xs as αs n x a * Q0 x a

/-- `P^{(n)}_{xy}[a] = Σ_{m=1}^{n-1} P^{ARP}_{⟨x,n⟩,⟨y,m⟩}[a]` (p. 282): the probability that action `a`
at `⟨x, n⟩` leads to real state `y` at one of the levels `1, …, n - 1` (reached by replaying the cards
`2, …, n`). -/
noncomputable def arpTrans (xs : ℕ → X) (as : ℕ → A) (ys : ℕ → X) (αs : ℕ → ℝ) (n : ℕ) (x : X)
    (a : A) (y : X) : ℝ :=
  ∑ k ∈ Finset.Icc 2 n, if ys k = y then arpWeight xs as αs n x a k else 0

/-- Probability that, starting from ARP state `⟨x, n⟩` and performing the actions of the list `bs` in
order, the ARP is still (not absorbed and) at a level `≥ l` after the last action. -/
noncomputable def arpProbAbove (xs : ℕ → X) (as : ℕ → A) (ys : ℕ → X) (αs : ℕ → ℝ) (l : ℕ) :
    List A → X → ℕ → ℝ
  | [], _, n => if l ≤ n then 1 else 0
  | b :: bs, x, n =>
      ∑ k ∈ Finset.Icc 1 n, arpWeight xs as αs n x b k * arpProbAbove xs as ys αs l bs (ys k) (k - 1)

/-! ### Values of finite action sequences (note 3, p. 287; Lemmas B.1, B.4) -/

/-- Expected discounted reward of the fixed action sequence `bs` from state `x` in the real process,
with terminal value `V` after the last action. -/
noncomputable def seqValueWith (M : FiniteMDP X A) (γ : ℝ) (V : X → ℝ) : X → List A → ℝ
  | x, [] => V x
  | x, b :: bs => M.R x b + γ * ∑ y, M.P x b y * seqValueWith M γ V y bs

/-- `Q̄(x, a₁, …, a_s)`: the expected discounted reward of the action sequence with `0` terminal
reward (note 3). -/
noncomputable def seqValue (M : FiniteMDP X A) (γ : ℝ) : X → List A → ℝ :=
  seqValueWith M γ (fun _ => 0)

omit [DecidableEq X] [Fintype A] [DecidableEq A] [Nonempty A] in
@[simp] theorem seqValue_nil (M : FiniteMDP X A) (γ : ℝ) (x : X) : seqValue M γ x [] = 0 := rfl

omit [DecidableEq X] [Fintype A] [DecidableEq A] [Nonempty A] in
theorem seqValue_cons (M : FiniteMDP X A) (γ : ℝ) (x : X) (b : A) (bs : List A) :
    seqValue M γ x (b :: bs) = M.R x b + γ * ∑ y, M.P x b y * seqValue M γ y bs := rfl

/-- Value of the actions `bs` in the concatenated chain of Lemma B.4, whose `i`-th step uses the
transition matrix `Ps i` and reward function `Rs i`; started with `i = 1`, `0` terminal reward. -/
noncomputable def chainValue (Ps : ℕ → X → A → X → ℝ) (Rs : ℕ → X → A → ℝ) (γ : ℝ) :
    ℕ → X → List A → ℝ
  | _, _, [] => 0
  | i, x, b :: bs => Rs i x b + γ * ∑ y, Ps i x b y * chainValue Ps Rs γ (i + 1) y bs

/-- Transition matrix `P^π_{xy} = P_xy[π(x)]` of a stationary deterministic policy `π`. -/
def policyMatrix (M : FiniteMDP X A) (π : X → A) : Matrix X X ℝ :=
  fun x y => M.P x (π x) y

/-- Value `V^π(x) = Σ_t γ^t ((P^π)^t ℛ^π)(x)` of a stationary deterministic policy `π`
(a convergent series for `0 ≤ γ < 1`, since the rewards are finitely many reals). -/
noncomputable def policyValue (M : FiniteMDP X A) (γ : ℝ) (π : X → A) (x : X) : ℝ :=
  ∑' t : ℕ, γ ^ t * (((policyMatrix M π) ^ t).mulVec (fun z => M.R z (π z))) x

/-- The value of the actions `bs` from `x` followed by the stationary policy `π` (Lemma B.1). -/
noncomputable def seqThenPolicy (M : FiniteMDP X A) (γ : ℝ) (π : X → A) : X → List A → ℝ :=
  seqValueWith M γ (policyValue M γ π)

end QLearning.Convergence


