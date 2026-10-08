-- Prove2me | Definitions.Def_SuttonBartoRL_AverageReward_AverageReward
-- name    : SuttonBartoRL_AverageReward_AverageReward
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T15:39:25.151412+00:00
-- url     : https://prove2.me/theorems/fcc2e5b8-ed61-475e-8db6-f2b3a678660b
-- title:
--   Average reward $r(\pi)$, stationary distributions (10.8), the discounted objective $J(\pi)$, differential values (10.13) and differential Bellman equations
-- statement:
--   Fix a finite MDP with dynamics $p(s', r\mid s, a)$ and a policy $\pi$.
--
--   1. A **stationary distribution** of $\pi$ is a probability vector $\mu$ on $\mathcal S$ ($\mu(s)\ge 0$, $\sum_s \mu(s) = 1$) such that, selecting actions according to $\pi$, one remains in the same distribution (10.8):
--   $$
--   \sum_s \mu(s) \sum_a \pi(a\mid s)\, p(s'\mid s, a) = \mu(s') \quad \text{for all } s'.
--   $$
--   2. The **average reward** of $\pi$ with respect to a state distribution $\mu$ is the last line of (10.7):
--   $$
--   r(\pi) = \sum_s \mu(s)\sum_a \pi(a\mid s) \sum_{s', r} p(s', r\mid s, a)\, r .
--   $$
--   3. For a discount rate $\gamma$, the **discounted objective** of the box on p. 254 is $J(\pi) = \sum_s \mu(s)\, v^\gamma_\pi(s)$, the discounted values averaged over $\mu$.
--   4. A number $v$ is the **differential value** of a state $s$ relative to an average reward $\rho$, in the sense of (10.13),
--   $$
--   v = \lim_{\gamma\to 1}\ \lim_{h\to\infty} \sum_{t=0}^{h} \gamma^t \big(\mathbb E_\pi[R_{t+1}\mid S_0 = s] - \rho\big),
--   $$
--   when for every $\gamma \in [0,1)$ the inner limit exists, equal to some $f(\gamma)$, and $f(\gamma) \to v$ as $\gamma \to 1$ from below.
--   5. The **differential Bellman equations** (p. 250) for a function $v$ on states or $q$ on state–action pairs and a constant $\rho$ are
--   $$
--   v(s) = \sum_a \pi(a\mid s)\sum_{r,s'} p(s', r\mid s,a)\big[r - \rho + v(s')\big], \qquad
--   q(s,a) = \sum_{r,s'} p(s', r\mid s,a)\Big[r - \rho + \sum_{a'} \pi(a'\mid s')\, q(s', a')\Big],
--   $$
--   and the optimality versions, with $\max_a$ in front of the sum for $v$ and $\max_{a'} q(s', a')$ inside it for $q$. The book takes $\rho = r(\pi)$ in the first two and $\rho = \max_\pi r(\pi)$ in the last two.
--   6. The **differential TD errors** (10.10), (10.11) are $\delta = R - \bar R + \hat v(s') - \hat v(s)$ and $\delta = R - \bar R + \hat q(s', a') - \hat q(s, a)$.
--
--   These are the quantities of §§10.3–10.4 of the book.
--
--   **Formalization Note** The book writes $r(\pi)$ and $J(\pi)$ with $\mu = \mu_\pi$, the steady-state distribution of an ergodic MDP; here the distribution $\mu$ is an explicit argument, and the theorems say which $\mu$ they use. The two limits in (10.13) are encoded as explicit existence of limits (a `Tendsto` statement), so no junk value of a nonexistent limit can enter; $\gamma \to 1$ is taken from below, where the discounted sums are defined. The maxima are `Finset.sup'` over the finite nonempty action set. In the TD errors `vhat`, `qhat` stand for $\hat v(\cdot, \mathbf w_t)$, $\hat q(\cdot,\cdot,\mathbf w_t)$ at the current weights.
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, Eqs. (10.7)–(10.8), p. 249; differential Bellman equations and (10.10)–(10.11), p. 250; (10.13), p. 251; box "The Futility of Discounting in Continuing Problems", p. 254

import Mathlib
import Definitions.Def_SuttonBartoRL_AverageReward_MDP

namespace SuttonBartoRL.AverageReward

open Filter Topology

variable {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]

/-- (10.8), p. 249: `μ` is a stationary (steady-state) distribution for `π`: a probability vector
on `S` under which, selecting actions according to `π`, one remains in the same distribution,
`Σ_s μ(s) Σ_a π(a | s) p(s' | s, a) = μ(s')` for every `s'`. -/
def IsStationaryDist (M : MDP S A) (π : SuttonBartoRL.FiniteMDP.Policy S A) (μ : S → ℝ) : Prop :=
  (∀ s, 0 ≤ μ s) ∧ (∑ s, μ s = 1) ∧
    ∀ s', ∑ s, μ s * ∑ a, π.prob s a * M.trans s a s' = μ s'

/-- The third line of (10.7), p. 249: the average reward of `π` computed from a state
distribution `μ`, `r(π) = Σ_s μ(s) Σ_a π(a | s) Σ_{s', r} p(s', r | s, a) r`. The book writes it
with `μ = μ_π`, the steady-state distribution; here `μ` is an explicit argument. -/
def avgReward (M : MDP S A) (π : SuttonBartoRL.FiniteMDP.Policy S A) (μ : S → ℝ) : ℝ :=
  ∑ s, μ s * ∑ a, π.prob s a * ∑ s', ∑ r ∈ M.R, M.p s a s' r * r

/-- Box "The Futility of Discounting in Continuing Problems", p. 254: the discounted objective
`J(π) = Σ_s μ_π(s) v^γ_π(s)`, the discounted values averaged over the state distribution `μ`
(the book's `μ_π`), with `v^γ_π` the return-defined discounted value function. -/
noncomputable def discountedObjective (M : MDP S A) (γ : ℝ) (π : SuttonBartoRL.FiniteMDP.Policy S A) (μ : S → ℝ) : ℝ :=
  ∑ s, μ s * M.stateValue γ π s

/-- (10.13), p. 251: `v` is the differential value of state `s` under `π` relative to the average
reward `ρ` (the book's `r(π)`), in the sense
`v = lim_{γ→1} lim_{h→∞} Σ_{t=0}^{h} γ^t (E_π[R_{t+1} | S_0 = s] − ρ)`.
Both limits are required to exist: for every `γ ∈ [0, 1)` the partial sums over `h` converge to
some `f(γ)`, and `f(γ) → v` as `γ → 1` from below. -/
def HasDifferentialValue (M : MDP S A) (π : SuttonBartoRL.FiniteMDP.Policy S A) (ρ : ℝ) (s : S) (v : ℝ) : Prop :=
  ∃ f : ℝ → ℝ,
    (∀ γ : ℝ, 0 ≤ γ → γ < 1 →
      Tendsto (fun h : ℕ => ∑ t ∈ Finset.range (h + 1),
        γ ^ t * (M.expectedRewardAt π t s - ρ)) atTop (𝓝 (f γ))) ∧
    Tendsto f (𝓝[<] 1) (𝓝 v)

/-- p. 250: `v` satisfies the differential Bellman equation for `v_π` with average reward `ρ`
(the book's `r(π)`): `v(s) = Σ_a π(a | s) Σ_{r, s'} p(s', r | s, a) [r − ρ + v(s')]` for all `s`. -/
def IsDiffBellmanV (M : MDP S A) (π : SuttonBartoRL.FiniteMDP.Policy S A) (ρ : ℝ) (v : S → ℝ) : Prop :=
  ∀ s, v s = ∑ a, π.prob s a * ∑ s', ∑ r ∈ M.R, M.p s a s' r * (r - ρ + v s')

/-- p. 250: `q` satisfies the differential Bellman equation for `q_π` with average reward `ρ`:
`q(s, a) = Σ_{r, s'} p(s', r | s, a) [r − ρ + Σ_{a'} π(a' | s') q(s', a')]` for all `s`, `a`. -/
def IsDiffBellmanQ (M : MDP S A) (π : SuttonBartoRL.FiniteMDP.Policy S A) (ρ : ℝ) (q : S → A → ℝ) : Prop :=
  ∀ s a, q s a = ∑ s', ∑ r ∈ M.R, M.p s a s' r * (r - ρ + ∑ a', π.prob s' a' * q s' a')

/-- p. 250: `v` satisfies the differential Bellman optimality equation for `v_*` with average
reward `ρ` (the book's `max_π r(π)`): `v(s) = max_a Σ_{r, s'} p(s', r | s, a) [r − ρ + v(s')]`,
the maximum over the finite nonempty action set taken with `Finset.sup'`. -/
def IsDiffBellmanOptV [Nonempty A] (M : MDP S A) (ρ : ℝ) (v : S → ℝ) : Prop :=
  ∀ s, v s = Finset.univ.sup' Finset.univ_nonempty
    (fun a => ∑ s', ∑ r ∈ M.R, M.p s a s' r * (r - ρ + v s'))

/-- p. 250: `q` satisfies the differential Bellman optimality equation for `q_*` with average
reward `ρ` (the book's `max_π r(π)`):
`q(s, a) = Σ_{r, s'} p(s', r | s, a) [r − ρ + max_{a'} q(s', a')]`. -/
def IsDiffBellmanOptQ [Nonempty A] (M : MDP S A) (ρ : ℝ) (q : S → A → ℝ) : Prop :=
  ∀ s a, q s a = ∑ s', ∑ r ∈ M.R, M.p s a s' r *
    (r - ρ + Finset.univ.sup' Finset.univ_nonempty (fun a' => q s' a'))

/-- (10.10), p. 250: the differential TD error for state values,
`δ_t = R_{t+1} − R̄_t + v̂(S_{t+1}, w_t) − v̂(S_t, w_t)`, with `vhat = v̂(·, w_t)`,
`R = R_{t+1}`, `Rbar = R̄_t`, `s = S_t`, `s' = S_{t+1}`. -/
def diffTDErrorV (R Rbar : ℝ) (vhat : S → ℝ) (s s' : S) : ℝ :=
  R - Rbar + vhat s' - vhat s

/-- (10.11), p. 250: the differential TD error for action values,
`δ_t = R_{t+1} − R̄_t + q̂(S_{t+1}, A_{t+1}, w_t) − q̂(S_t, A_t, w_t)`, with `qhat = q̂(·, ·, w_t)`. -/
def diffTDErrorQ (R Rbar : ℝ) (qhat : S → A → ℝ) (s : S) (a : A) (s' : S) (a' : A) : ℝ :=
  R - Rbar + qhat s' a' - qhat s a

end SuttonBartoRL.AverageReward


