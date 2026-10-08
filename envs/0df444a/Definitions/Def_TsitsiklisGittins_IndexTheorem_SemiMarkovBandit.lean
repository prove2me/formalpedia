-- Prove2me | Definitions.Def_TsitsiklisGittins_IndexTheorem_SemiMarkovBandit
-- name    : TsitsiklisGittins_IndexTheorem_SemiMarkovBandit
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:48:07.551984+00:00
-- url     : https://prove2.me/theorems/f077500f-2916-4606-92a9-315288ca025a
-- title:
--   Semi-Markov multi-armed bandit, reward rate (2.1), stationary policies, expected discounted reward J, optimality and priority rules
-- statement:
--   This module sets up the multi-armed bandit problem of Tsitsiklis (1994), §2.
--
--   There are $n\ge 1$ bandit processes. Bandit $i$ is a semi-Markov process with a finite state space $\mathcal X_i$, and $\mathcal X=\mathcal X_1\cup\cdots\cup\mathcal X_n$ is their disjoint union. If bandit $i$ is at the state $x\in\mathcal X_i$ and is played, a random reward $R(x)$ is received, the bandit stays busy for a random time $T(x)\ge 0$, and it then moves to a random state $Y(x)\in\mathcal X_i$; the other bandits do not move. The joint law of $(T(x),R(x),Y(x))$ depends only on $x$, and different plays are independent. It is assumed that $R(x)$ is integrable and that $\mathbb P(T(x)>0)>0$. Let $\beta>0$ be the discount rate. The module defines:
--
--   1. the one-play moments $\mathbb E[R(x)]$, $\mathbb E\big[\int_0^{T(x)}e^{-\beta t}\,dt\big]$ and $D(x,y)=\mathbb E\big[e^{-\beta T(x)};\,Y(x)=y\big]$;
--   2. the **reward rate** (2.1)
--   $$
--   r(x)=\frac{\mathbb E[R(x)]}{\mathbb E\Big[\int_0^{T(x)}e^{-\beta t}\,dt\Big]};
--   $$
--   3. a **policy**: a map $\pi:\mathcal X_1\times\cdots\times\mathcal X_n\to\{1,\dots,n\}$ that chooses, at time zero and at every play completion time, the bandit to play next as a function of the current states;
--   4. the **expected discounted reward** $J_\pi(z)=\mathbb E\big[\sum_{i\ge1}R_ie^{-\beta t_i}\big]$ of $\pi$ from the initial joint state $z$, where $t_i$ is the start of the $i$-th play and $R_i$ its reward. It is the limit of the expected discounted reward $V_k$ of the first $k$ plays, which satisfies $V_0=0$ and
--   $$
--   V_{k+1}(z)=\mathbb E[R(z_{\pi(z)})]+\sum_{y\in\mathcal X_{\pi(z)}}D\big(z_{\pi(z)},y\big)\,V_k\big(z\text{ with bandit }\pi(z)\text{ moved to }y\big);
--   $$
--   5. **optimality**: $\pi$ is optimal if $J_{\pi'}(z)\le J_\pi(z)$ for every policy $\pi'$ and every initial state $z$;
--   6. a **priority rule**: a policy for which there is an ordering of the elements of $\mathcal X$ such that, at each decision point, the bandit whose state is ordered highest is chosen.
--
--   These are the objects in which Theorems 2.1 and 2.2 and Lemma 2.1 are stated.
--
--   **Formalization Note** Bandits are indexed by `Fin n` (that is, $0,\dots,n-1$ rather than $1,\dots,n$). The disjoint union $\mathcal X$ is the sigma type `Σ i, X i`, so the state spaces are disjoint by construction. The law of $(T,R,Y)$ is a probability measure on $\mathbb R\times\mathbb R\times\mathcal X_i$, with $\mathcal X_i$ carrying a measurable structure in which singletons are measurable. The hypothesis $\mathbb P(T(x)>0)>0$ is not written on the page; it is what makes the denominator of (2.1) nonzero, and it makes $\sum_y D(x,y)=\mathbb E[e^{-\beta T(x)}]<1$, so that $V_k(z)$ converges (geometrically) and the limit used for $J_\pi$ is never the junk value of a divergent sequence. $J_\pi$ is computed from the moments $\mathbb E[R(x)]$ and $D(x,\cdot)$ through the first-step recursion instead of on a constructed path space; by the independence assumption these determine $\mathbb E[\sum_{i\le k}R_ie^{-\beta t_i}]$. The policy class is the paper's: stationary deterministic maps of the current joint state. An ordering of $\mathcal X$ is encoded as an injective ranking $\mathcal X\to\mathbb N$.
-- source:
--   Tsitsiklis, A Short Proof of the Gittins Index Theorem, Ann. Appl. Probab. 4 (1994), pp. 194–196 (PDF pp. 1–3), Section 2, model, policy, objective, equation (2.1), definition of a priority rule

import Mathlib

namespace TsitsiklisGittins.IndexTheorem

open MeasureTheory

/-- The multi-armed bandit problem of Tsitsiklis (1994), §2, pp. 194–195: `n` semi-Markov bandit
processes, bandit `i` having the finite state space `X i` (bandits are numbered `0, …, n-1`).
For a state `x` of bandit `i`, `law i x` is the joint law of the random vector
`(T(x), R(x), Y(x))`: the duration `T(x)` of a play, the reward `R(x)` received when the play
starts, and the state `Y(x) ∈ X i` the bandit moves to at the end of the play. The law depends only
on `x`, and the vectors of different plays are independent (this is what makes the first-step
recursion `playValue` below the expected discounted reward). `β > 0` is the discount rate.
The field `T_pos` (`P(T(x) > 0) > 0`) is what makes the denominator of (2.1) nonzero. -/
structure SemiMarkovBandit (n : ℕ) (X : Fin n → Type) [∀ i, Fintype (X i)]
    [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSingletonClass (X i)] where
  /-- the discount rate `β` -/
  β : ℝ
  β_pos : 0 < β
  /-- the joint law of `(T(x), R(x), Y(x))` for a state `x` of bandit `i` -/
  law : (i : Fin n) → X i → Measure (ℝ × ℝ × X i)
  isProb : ∀ i x, IsProbabilityMeasure (law i x)
  /-- the duration of a play is nonnegative -/
  T_nonneg : ∀ i x, ∀ᵐ ω ∂(law i x), 0 ≤ ω.1
  /-- the reward of a play has a finite expectation -/
  R_integrable : ∀ i x, Integrable (fun ω : ℝ × ℝ × X i => ω.2.1) (law i x)
  /-- a play takes positive time with positive probability (needed for (2.1) to be defined) -/
  T_pos : ∀ i x, 0 < law i x {ω | 0 < ω.1}

namespace SemiMarkovBandit

variable {n : ℕ} {X : Fin n → Type} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
  [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSingletonClass (X i)]

/-- `E[R(x)]`, the expected reward of one play at the state `q = ⟨i, x⟩` of `𝒳 = Σ i, X i`. -/
noncomputable def meanReward (B : SemiMarkovBandit n X) (q : Σ i, X i) : ℝ :=
  ∫ ω, ω.2.1 ∂(B.law q.1 q.2)

/-- `E[∫₀^{T(x)} e^{−βt} dt]`, the expected discounted duration of one play at `q = ⟨i, x⟩`. -/
noncomputable def discDuration (B : SemiMarkovBandit n X) (q : Σ i, X i) : ℝ :=
  ∫ ω, (∫ t in (0 : ℝ)..ω.1, Real.exp (-(B.β * t))) ∂(B.law q.1 q.2)

/-- `E[e^{−βT(x)} ; Y(x) = y]` for `q = ⟨i, x⟩` and `p = ⟨j, y⟩`: the expected discount factor of
one play at `q`, on the event that the play ends with the transition to `p`. It is `0` when `p`
belongs to another bandit (`j ≠ i`), since a play only moves the bandit that is played. -/
noncomputable def discKernel (B : SemiMarkovBandit n X) (q p : Σ i, X i) : ℝ :=
  ∫ ω, Real.exp (-(B.β * ω.1)) * (if (⟨q.1, ω.2.2⟩ : Σ i, X i) = p then 1 else 0)
    ∂(B.law q.1 q.2)

/-- The reward rate (2.1): `r(x) = E[R(x)] / E[∫₀^{T(x)} e^{−βt} dt]`. -/
noncomputable def rate (B : SemiMarkovBandit n X) (q : Σ i, X i) : ℝ :=
  B.meanReward q / B.discDuration q

end SemiMarkovBandit

/-- A joint state `(x₁, …, xₙ) ∈ 𝒳₁ × ⋯ × 𝒳ₙ`: the current states of the `n` bandits. -/
abbrev JointState (n : ℕ) (X : Fin n → Type) : Type := (i : Fin n) → X i

/-- A policy (p. 195): a map `π : 𝒳₁ × ⋯ × 𝒳ₙ ↦ {1, …, n}` choosing, at time zero and at every
play completion time, the bandit to be played next as a function of the current states. -/
abbrev Policy (n : ℕ) (X : Fin n → Type) : Type := JointState n X → Fin n

/-- Expected discounted reward of the first `k` plays of policy `π` from the joint state `z`, for a
problem given by its one-play moments: `ρ q` is the expected (discounted-to-the-start) reward of a
play at `q`, and `D q p` is the expected discount factor `e^{−β·(duration)}` of a play at `q` on the
event that it ends in `p`. First-step recursion:
`V₀ = 0`, `V_{k+1}(z) = ρ(z_{π z}) + Σ_y D(z_{π z}, y) · V_k(z with bandit π z moved to y)`. -/
noncomputable def playValue {n : ℕ} {X : Fin n → Type} [∀ i, Fintype (X i)]
    [∀ i, DecidableEq (X i)] (ρ : (Σ i, X i) → ℝ) (D : (Σ i, X i) → (Σ i, X i) → ℝ)
    (π : Policy n X) : ℕ → JointState n X → ℝ
  | 0, _ => 0
  | k + 1, z =>
      ρ ⟨π z, z (π z)⟩ +
        ∑ y : X (π z), D ⟨π z, z (π z)⟩ ⟨π z, y⟩ * playValue ρ D π k (Function.update z (π z) y)

/-- The infinite-horizon expected discounted reward of `π` from `z`: the limit, as `k → ∞`, of the
expected discounted reward of the first `k` plays. -/
noncomputable def momentValue {n : ℕ} {X : Fin n → Type} [∀ i, Fintype (X i)]
    [∀ i, DecidableEq (X i)] (ρ : (Σ i, X i) → ℝ) (D : (Σ i, X i) → (Σ i, X i) → ℝ)
    (π : Policy n X) (z : JointState n X) : ℝ :=
  Filter.limUnder Filter.atTop (fun k : ℕ => playValue ρ D π k z)

namespace SemiMarkovBandit

variable {n : ℕ} {X : Fin n → Type} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
  [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSingletonClass (X i)]

/-- `J(π)(z) = E[Σ_{i=1}^∞ Rᵢ e^{−βtᵢ}]` from the initial joint state `z`, computed from the
per-state moments `E[R(x)]` and `E[e^{−βT(x)}; Y(x) = y]`. -/
noncomputable def value (B : SemiMarkovBandit n X) (π : Policy n X) (z : JointState n X) : ℝ :=
  momentValue B.meanReward B.discKernel π z

/-- `π` is optimal: it maximizes the expected discounted reward for every initial state, among
all policies. -/
def IsOptimal (B : SemiMarkovBandit n X) (π : Policy n X) : Prop :=
  ∀ (π' : Policy n X) (z : JointState n X), B.value π' z ≤ B.value π z

end SemiMarkovBandit

/-- `π` follows the ranking `rank` of `𝒳 = Σ i, X i`: at every joint state it plays a bandit whose
current state has the highest rank among the current states of all bandits. -/
def FollowsRank {n : ℕ} {X : Fin n → Type} (rank : (Σ i, X i) → ℕ) (π : Policy n X) : Prop :=
  ∀ (z : JointState n X) (j : Fin n), rank ⟨j, z j⟩ ≤ rank ⟨π z, z (π z)⟩

/-- A priority rule (p. 196): there is an ordering of the elements of `𝒳 = 𝒳₁ ∪ ⋯ ∪ 𝒳ₙ` (an
injective ranking) such that at each decision point the bandit whose state is ordered highest is
chosen. -/
def IsPriorityRule {n : ℕ} {X : Fin n → Type} (π : Policy n X) : Prop :=
  ∃ rank : (Σ i, X i) → ℕ, Function.Injective rank ∧ FollowsRank rank π

end TsitsiklisGittins.IndexTheorem


