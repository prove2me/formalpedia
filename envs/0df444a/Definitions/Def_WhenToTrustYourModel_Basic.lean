-- Prove2me | Definitions.Def_WhenToTrustYourModel_Basic
-- name    : WhenToTrustYourModel_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-24T11:03:44.27098+00:00
-- url     : https://prove2.me/theorems/41380681-4e96-42f5-af59-814c02e25c8b
-- title:
--   Finite MDPs, total variation, returns and branched rollouts (MBPO)
-- statement:
--   Objects of Sections 3-4 and Appendices A-B of Janner, Fu, Zhang and Levine (2019).
--
--   1. **Distributions and total variation.** A distribution on a finite set $X$ is a function $\mu:X\to[0,\infty)$ with $\sum_x\mu(x)=1$. The total variation distance is $D_{TV}(\mu\|\nu)=\tfrac12\sum_x|\mu(x)-\nu(x)|$. From a marginal $p(x)$ and a conditional $p(y\mid x)$ one forms the joint $p(x,y)=p(x)\,p(y\mid x)$.
--   2. **Markov chains.** For an initial distribution $\mu_0$ and transition kernels $K_t(s,s')$, the state marginals are $p^0=\mu_0$ and $p^{t+1}(s')=\sum_s p^t(s)K_t(s,s')$.
--   3. **Markov decision process.** Finite state and action sets $\mathcal S,\mathcal A$, a reward $r(s,a)$, an initial distribution $\rho_0$ and a discount $\gamma$. A policy is a family of distributions $\pi(\cdot\mid s)$ on $\mathcal A$; dynamics (the true $p$ or a learned model $\hat p$) are a family of distributions $p(\cdot\mid s,a)$ on $\mathcal S$. A process that acts with policy $\pi_t$ and moves with dynamics $p_t$ at time $t$ has state marginals $p^t$ given by the chain with kernel $K_t(s,s')=\sum_a\pi_t(a\mid s)p_t(s'\mid s,a)$, state-action marginals $p^t(s,a)=p^t(s)\pi_t(a\mid s)$, and return
--   $$\eta=\sum_{t\ge0}\gamma^t\sum_{s,a}p^t(s,a)\,r(s,a).$$
--   For a stationary policy $\pi$ this is $\eta[\pi]$ under the true dynamics and the model return $\hat\eta[\pi]$ under $\hat p$.
--   4. **Error quantities (Section 4.1).** For a state distribution $d$, a policy $\pi$ and two dynamics $p_1,p_2$, the expected total variation is $E_{s\sim d,\,a\sim\pi(\cdot\mid s)}\big[D_{TV}(p_1(\cdot\mid s,a)\|p_2(\cdot\mid s,a))\big]$.
--   5. **Branched rollouts (Section 4.2, Lemma B.4).** For a branch length $k$, a two-phase process uses the branch (post-branch) policy and dynamics at the time steps $t<k$ and the pre-branch policy and dynamics at the time steps $t\ge k$. The branched return $\eta^{\mathrm{branch}}[\pi]$ is the return of the process that runs $\pi$ under the model $\hat p$ for the $k$ branch steps and the data-collecting policy $\pi_D$ under the true dynamics $p$ otherwise.
--
--   **Formalization Note** The paper writes every expectation as a sum over states and actions; the state and action spaces are finite types. The paper never defines the branched return formally. Its text describes a rollout that follows $\pi_D$ until a branch point and then runs $k$ model steps under $\pi$, but the proof of Lemma B.4 bounds the marginals at the times $t\le k$ by the post-branch errors alone, which places the branch segment at the times $0,\dots,k-1$. The definitions follow the proof.
-- source:
--   Janner, Fu, Zhang and Levine, When to Trust Your Model: Model-Based Policy Optimization, arXiv:1906.08253v3 (NeurIPS 2019), Section 3, Sections 4.1-4.3, Appendix A (Theorems A.1-A.3) and Appendix B (Lemmas B.1-B.4)

import Mathlib

/-!
Janner, Fu, Zhang and Levine, *When to Trust Your Model: Model-Based Policy Optimization*,
arXiv:1906.08253v3 (NeurIPS 2019): discrete distributions and total variation (Appendix B),
Markov chains and their state marginals (Lemma B.2), the discounted Markov decision process of
Section 3, its returns, the model-error and policy-divergence quantities of Section 4.1, and the
two-phase (branched) rollouts of Section 4.2 and Lemma B.4.

State and action spaces are finite types: the paper writes every expectation as a sum over states
and actions. A distribution on a finite type is a nonnegative real function with total mass `1`.
-/

noncomputable section

namespace WhenToTrustYourModel

variable {S A : Type*} [Fintype S] [Fintype A]

/-- Appendix B: `μ` is a probability distribution on the finite type `X` (nonnegative, total mass
`1`). -/
def IsDist {X : Type*} [Fintype X] (μ : X → ℝ) : Prop :=
  (∀ x, 0 ≤ μ x) ∧ ∑ x, μ x = 1

/-- Appendix B, proof of Lemma B.1: the total variation distance
`D_TV(μ ‖ ν) = ½ ∑_x |μ(x) - ν(x)|`. -/
def tvDist {X : Type*} [Fintype X] (μ ν : X → ℝ) : ℝ :=
  (1 / 2) * ∑ x, |μ x - ν x|

/-- Lemma B.1: the joint distribution `p(x, y) = p(x) p(y | x)` built from a marginal `p` and a
conditional `q x y = p(y | x)`. -/
def jointDist {X Y : Type*} (p : X → ℝ) (q : X → Y → ℝ) : X × Y → ℝ :=
  fun z => p z.1 * q z.1 z.2

/-- Lemma B.2: the state marginal `p^t(s)` at time `t` of a Markov chain with initial distribution
`μ0` and (possibly time-dependent) transition kernels `K t s s' = p(s_{t+1} = s' | s_t = s)`:
`p^0 = μ0` and `p^{t+1}(s') = ∑_s p^t(s) K_t(s, s')`. -/
def chainDist (μ0 : S → ℝ) (K : ℕ → S → S → ℝ) : ℕ → S → ℝ
  | 0 => μ0
  | t + 1 => fun s' => ∑ s, chainDist μ0 K t s * K t s s'

/-- Section 3: `π s a = π(a | s)` is a policy, i.e. a distribution over actions in every state. -/
def IsPolicy (π : S → A → ℝ) : Prop :=
  ∀ s, IsDist (π s)

/-- Section 3: `P s a s' = p(s' | s, a)` is a transition distribution (true dynamics or a learned
model), i.e. a distribution over next states for every state-action pair. -/
def IsDynamics (P : S → A → S → ℝ) : Prop :=
  ∀ s a, IsDist (P s a)

/-- Section 4.2 and Lemma B.4: the state-to-state kernel at time `t` of the (possibly
nonstationary) process that acts with policy `πs t` and moves with dynamics `Ps t`:
`∑_a π_t(a | s) p_t(s' | s, a)`. -/
def inducedKernel (πs : ℕ → S → A → ℝ) (Ps : ℕ → S → A → S → ℝ) : ℕ → S → S → ℝ :=
  fun t s s' => ∑ a, πs t s a * Ps t s a s'

/-- Lemmas B.3 and B.4: the state marginal `p^t(s)` of the process started from `ρ0` that acts at
time `t` with policy `πs t` and moves with dynamics `Ps t`. -/
def stateDist (ρ0 : S → ℝ) (πs : ℕ → S → A → ℝ) (Ps : ℕ → S → A → S → ℝ) : ℕ → S → ℝ :=
  chainDist ρ0 (inducedKernel πs Ps)

/-- Proof of Lemma B.3: the expected reward `∑_{s,a} p^t(s, a) r(s, a)` at time `t`, where
`p^t(s, a) = p^t(s) π_t(a | s)`. -/
def expReward (r : S → A → ℝ) (ρ0 : S → ℝ) (πs : ℕ → S → A → ℝ) (Ps : ℕ → S → A → S → ℝ)
    (t : ℕ) : ℝ :=
  ∑ s, ∑ a, stateDist ρ0 πs Ps t s * πs t s a * r s a

/-- Section 3 and proof of Lemma B.3: the expected discounted return
`E[∑_{t ≥ 0} γ^t r(s_t, a_t)] = ∑_t γ^t ∑_{s,a} p^t(s, a) r(s, a)` of a (possibly nonstationary)
process. -/
def discReturn (γ : ℝ) (r : S → A → ℝ) (ρ0 : S → ℝ) (πs : ℕ → S → A → ℝ)
    (Ps : ℕ → S → A → S → ℝ) : ℝ :=
  ∑' t : ℕ, γ ^ t * expReward r ρ0 πs Ps t

/-- Section 3 and Section 4.1: the return `η[π]` of the stationary policy `π` under dynamics `P`
(the true dynamics give `η[π]`, a learned model `p̂` gives the model return `η̂[π]`). -/
def policyReturn (γ : ℝ) (r : S → A → ℝ) (ρ0 : S → ℝ) (π : S → A → ℝ) (P : S → A → S → ℝ) : ℝ :=
  discReturn γ r ρ0 (fun _ => π) (fun _ => P)

/-- Section 4.1 and Theorems A.1-A.3: the expected total variation between two transition
distributions, `E_{s ∼ d, a ∼ π(·|s)} [D_TV(P(·|s,a) ‖ Q(·|s,a))]`, for a state distribution `d`
and a policy `π`. -/
def expectedTV (d : S → ℝ) (π : S → A → ℝ) (P Q : S → A → S → ℝ) : ℝ :=
  ∑ s, d s * ∑ a, π s a * tvDist (P s a) (Q s a)

/-- Section 4.2 and Lemma B.4: a two-phase schedule that uses `post` (the `k`-step branch) at the
time steps `t < k` and `pre` at the time steps `t ≥ k`. This is the time ordering under which the
proof of Lemma B.4 bounds the marginals ("for `t ≤ k`" only the post-branch errors enter). -/
def phase {α : Type*} (k : ℕ) (post pre : α) (t : ℕ) : α :=
  if t < k then post else pre

/-- Section 4.2 and Theorems A.2-A.3: the return of a `k`-branched rollout whose branch runs policy
`πpost` with dynamics `Ppost` for `k` steps, the rest of the rollout running policy `πpre` with
dynamics `Ppre`. The branched return `η^branch[π]` is
`branchedReturn γ r ρ0 k π p̂ π_D p`. -/
def branchedReturn (γ : ℝ) (r : S → A → ℝ) (ρ0 : S → ℝ) (k : ℕ) (πpost : S → A → ℝ)
    (Ppost : S → A → S → ℝ) (πpre : S → A → ℝ) (Ppre : S → A → S → ℝ) : ℝ :=
  discReturn γ r ρ0 (phase k πpost πpre) (phase k Ppost Ppre)

end WhenToTrustYourModel


