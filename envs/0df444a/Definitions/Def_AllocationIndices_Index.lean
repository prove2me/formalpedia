-- Prove2me | Definitions.Def_AllocationIndices_Index
-- name    : AllocationIndices_Index
-- status  : Definition
-- author  : @naimengye
-- created : 2026-09-24T02:25:56.661183+00:00
-- url     : https://prove2.me/theorems/1efcf3e8-faec-4001-ae13-a8a1b6f2e580
-- title:
--   Chapter 2 on the Bandit Algorithms model: R_τ, W_τ, ν_τ, positive stopping times, stopping sets, the fair-charge profit (2.5), restart value iteration, interchange value
-- statement:
--   The discrete-time setting of Chapter 2 (§2.4, p. 23), stated on top of the live *Bandit Algorithms* model (`Def_GittinsIndex`): a **bandit process** $B$ is a Markov reward process on a countable state space $E$ with transition kernel $P$, reward $r(x)$ collected at each application of the continuation control, and discount factor $a \in (0,1)$; $\mathbb{P}_x$ (`markovChainMeasure P x`) is its law from $x(0) = x$, a **stopping time** is an $\mathbb{N} \cup \{\infty\}$-valued map adapted to the coordinate filtration (`IsTrajStoppingTime`), and the **Gittins index** $\nu(B, x)$ is `gittinsIndex P r a x`, the supremum over stopping times $\tau \ge 1$ of $R_\tau / W_\tau$ (Eq. (2.6)). Time is indexed from $0$, so the book's decision times $0, 1, 2, \dots$ are the coordinates.
--
--   **Named quantities (pp. 25-26).** For a stopping time $\tau$ and initial state $x$:
--   $$R_\tau(B, x) = \mathbb{E}_x\Big[\sum_{t < \tau} a^t r(x(t))\Big] \ (\texttt{stoppedReward}), \qquad W_\tau(B, x) = \mathbb{E}_x\Big[\sum_{t < \tau} a^t\Big] \ (\texttt{stoppedTime}), \qquad \nu_\tau(B, x) = \frac{R_\tau}{W_\tau} \ (\texttt{stoppedRatio}, (2.7)).$$
--   `IsPositiveStoppingTime τ` says $\tau$ is a stopping time with $\tau \ge 1$ everywhere (the book's $\tau > 0$, so $W_\tau \ge 1$). `BoundedReward r` is the standing assumption that $|r|$ is bounded. `discountAtStop` is $\mathbb{E}_x[a^\tau]$ with $a^\infty = 0$.
--
--   **Stopping sets (p. 22, Lemma 2.2).** `hittingTime Σ₀ ω` is the first decision time $t \ge 1$ with $\omega(t) \in \Sigma_0$, and $\infty$ if there is none: the deterministic stationary Markov stopping rule with stopping set $\Sigma_0$.
--
--   **The fair charge (2.5).** `fairChargeProfit P r a x λ` $= \sup_{\tau > 0} \mathbb{E}_x[\sum_{t<\tau} a^t (r(x(t)) - \lambda)] = \sup_{\tau>0} (R_\tau - \lambda W_\tau)$, a real supremum over the nonempty set of positive stopping times, bounded by $(M + |\lambda|)/(1-a)$ for bounded rewards.
--
--   **Restart in state $\xi$ (§2.6.4, p. 31).** `restartIter P r a ξ` is the Katehakis–Veinott value iteration $\mu_0 = 0$, $\mu_{k+1}(x) = \max\{\mu_k(\xi),\ r(x) + a \sum_y P(y \mid x)\mu_k(y)\}$, the sum written as the integral of $\mu_k$ against $P(x)$.
--
--   **Interchange (Lemma 2.4, p. 34).** For two bandit processes $B_1, B_2$ on state spaces $S_1, S_2$ with stopping times $\tau, \sigma$: `interchangeValue P₁ r₁ P₂ r₂ a τ σ x₁ x₂` $= R_\tau(B_1) + \mathbb{E}[a^\tau] R_\sigma(B_2)$, the expected reward from continuing $B_1$ for time $\tau$ and then $B_2$ for time $\sigma$, the two processes being independent.
--
--   **Conventions.** All expectations are Bochner integrals under $\mathbb{P}_x$; with bounded rewards and $a < 1$ every integrand is bounded and, for a stopping time, measurable, so no junk value arises. The theorems of this mission take the state space countable with measurable singletons (every subset is then measurable, as the book's countable setting has it) and the reward bounded.
-- source:
--   Gittins, Glazebrook and Weber, Multi-armed Bandit Allocation Indices, 2nd ed., Wiley 2011, doi:10.1002/9780470980033, Chapter 2: §2.3-2.4 (bandit processes, stopping rules, SFABP, bounded rewards, pp. 21-23), §2.5 (2.4)-(2.7) (pp. 25-26), §2.6.3 stopping sets (p. 30), §2.6.4 restart-in-state iteration (p. 31), §2.7 Lemma 2.4 (p. 34)

import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Definitions.Def_GittinsIndex

/-!
Gittins, Glazebrook and Weber, *Multi-armed Bandit Allocation Indices* (2nd ed., Wiley 2011),
Chapter 2 (pp. 19-53): main ideas, the Gittins index.

The discrete-time setting of §2.4-2.6 (p. 23): a bandit process `B` is a Markov reward process on
a countable state space `E` with transition probabilities `P(y | x)`, a bounded reward `r(x)`
collected each time the continuation control is applied, and a discount factor `a ∈ (0,1)`. This
is exactly the single-arm model of the live *Bandit Algorithms* series (`Def_GittinsIndex`, L&S
§35.4): `markovChainMeasure P x` is the law of the process started at `x`, a stopping time is a
`Kernel`-trajectory stopping time (`IsTrajStoppingTime`), and `gittinsIndex P r a x` is the
index (2.6), `ν(B, x) = sup_{τ > 0} R_τ(B, x) / W_τ(B, x)`. Nothing of that model is restated
here; this module names the book's quantities on top of it.

* `stoppedReward P r a τ x = R_τ(B, x) = E[∑_{t<τ} a^t r(x(t)) | x(0) = x]`,
  `stoppedTime P a τ x = W_τ(B, x) = E[∑_{t<τ} a^t | x(0) = x]`,
  `stoppedRatio P r a τ x = ν_τ(B, x) = R_τ / W_τ` (2.7); `IsPositiveStoppingTime τ` — a
  stopping time taking values in `{1, 2, …} ∪ {∞}` (the book's `τ > 0`).
* `BoundedReward r` — the standing assumption `|r|` bounded (p. 23).
* `hittingTime Σ₀ ω` — the first decision time `t ≥ 1` at which the process is in the stopping
  set `Σ₀` (`∞` if never): the stopping rule with continuation set `Σ₀ᶜ` of Lemma 2.2.
* `fairChargeProfit P r a x λ = sup_{τ>0} E[∑_{t<τ} a^t (r(x(t)) − λ)]`, the maximal expected
  profit when a prevailing charge `λ` is paid per period of continuation (2.5).
* `restartIter P r a ξ k` — the Katehakis–Veinott value iteration of §2.6.4 for the restart-in-
  state problem: `μ_0 = 0`, `μ_{k+1}(x) = max{μ_k(ξ), r(x) + a ∑_y P(y | x) μ_k(y)}`.
* `interchangeValue` — the expected reward from continuing `B₁` for time `τ` and then `B₂` for
  time `σ`, `R_τ(B₁) + E[a^τ] R_σ(B₂)` (Lemma 2.4, p. 34), and `discountAtStop` — `E[a^τ]`.
-/

open MeasureTheory ProbabilityTheory BanditAlgorithm

noncomputable section

namespace AllocationIndices

variable {S : Type*} [MeasurableSpace S]

/-- `R_τ(B, x) = E[∑_{t<τ} a^t r(x(t)) | x(0) = x]`, the expected total discounted reward over
`τ` steps (p. 26). -/
def stoppedReward (P : Kernel S S) [IsMarkovKernel P] (r : S → ℝ) (a : ℝ)
    (τ : (ℕ → S) → ℕ∞) (x : S) : ℝ :=
  ∫ ω, discountedStoppedSum a r τ ω ∂markovChainMeasure P x

/-- `W_τ(B, x) = E[∑_{t<τ} a^t | x(0) = x] = (1 − a)⁻¹ E[1 − a^τ]`, the expected total discounted
time over `τ` steps (p. 26). -/
def stoppedTime (P : Kernel S S) [IsMarkovKernel P] (a : ℝ) (τ : (ℕ → S) → ℕ∞) (x : S) : ℝ :=
  ∫ ω, discountedStoppedSum a (fun _ ↦ 1) τ ω ∂markovChainMeasure P x

/-- `ν_τ(B, x) = R_τ(B, x) / W_τ(B, x)`, Eq. (2.7): the equivalent constant reward rate of the
portion of `B` up to `τ`. -/
def stoppedRatio (P : Kernel S S) [IsMarkovKernel P] (r : S → ℝ) (a : ℝ)
    (τ : (ℕ → S) → ℕ∞) (x : S) : ℝ :=
  stoppedReward P r a τ x / stoppedTime P a τ x

/-- A past-measurable stopping time taking values in the decision times `{1, 2, …}` (or `∞`):
the `τ > 0` over which (2.4)-(2.6) take their supremum. -/
def IsPositiveStoppingTime (τ : (ℕ → S) → ℕ∞) : Prop :=
  IsTrajStoppingTime τ ∧ ∀ ω, 1 ≤ τ ω

/-- The standing assumption of §2.4: the reward function is bounded. -/
def BoundedReward (r : S → ℝ) : Prop :=
  ∃ M : ℝ, ∀ x, |r x| ≤ M

/-- `E[a^τ | x(0) = x]`, the expected discount at the stopping time (`a^∞ = 0`). -/
def discountAtStop (P : Kernel S S) [IsMarkovKernel P] (a : ℝ) (τ : (ℕ → S) → ℕ∞) (x : S) :
    ℝ :=
  ∫ ω, (match τ ω with
    | (n : ℕ) => a ^ n
    | ⊤ => 0) ∂markovChainMeasure P x

/-- The stopping rule defined by a stopping set `Σ₀` (p. 22): stop at the first decision time
`t ≥ 1` at which the state lies in `Σ₀`, never if there is none. -/
def hittingTime (stopSet : Set S) (ω : ℕ → S) : ℕ∞ :=
  ⨅ t : {t : ℕ // 1 ≤ t ∧ ω t ∈ stopSet}, ((t : ℕ) : ℕ∞)

/-- The maximal expected profit from continuing `B` for one or more periods when a prevailing
charge `λ` is paid at each period of continuation (p. 25, the expression inside (2.5)):
`sup_{τ>0} E[∑_{t<τ} a^t (r(x(t)) − λ) | x(0) = x]`. -/
def fairChargeProfit (P : Kernel S S) [IsMarkovKernel P] (r : S → ℝ) (a : ℝ) (x : S) (lam : ℝ) :
    ℝ :=
  ⨆ τ : {τ : (ℕ → S) → ℕ∞ // IsPositiveStoppingTime τ},
    stoppedReward P r a τ x - lam * stoppedTime P a τ x

/-- The Katehakis–Veinott value iteration for the restart-in-state problem (§2.6.4, p. 31):
`μ_0 = 0` and `μ_{k+1}(x) = max{μ_k(ξ), r(x) + a ∑_y P(y | x) μ_k(y)}`, where `ξ` is the
state in which the bandit may be restarted. -/
def restartIter (P : Kernel S S) [IsMarkovKernel P] (r : S → ℝ) (a : ℝ) (ξ : S) :
    ℕ → S → ℝ
  | 0 => fun _ ↦ 0
  | k + 1 => fun x ↦ max (restartIter P r a ξ k ξ) (r x + a * ∫ y, restartIter P r a ξ k y ∂(P x))

/-- The expected reward from selecting `B₁` (state `x₁`) for time `τ` and then `B₂` (state `x₂`)
for time `σ`, the two processes being independent (Lemma 2.4, p. 34):
`R_τ(B₁) + E[a^τ] R_σ(B₂)`. -/
def interchangeValue {S₁ S₂ : Type*} [MeasurableSpace S₁] [MeasurableSpace S₂]
    (P₁ : Kernel S₁ S₁) [IsMarkovKernel P₁] (r₁ : S₁ → ℝ) (P₂ : Kernel S₂ S₂) [IsMarkovKernel P₂]
    (r₂ : S₂ → ℝ) (a : ℝ) (τ : (ℕ → S₁) → ℕ∞) (σ : (ℕ → S₂) → ℕ∞) (x₁ : S₁) (x₂ : S₂) : ℝ :=
  stoppedReward P₁ r₁ a τ x₁ + discountAtStop P₁ a τ x₁ * stoppedReward P₂ r₂ a σ x₂

end AllocationIndices

end


