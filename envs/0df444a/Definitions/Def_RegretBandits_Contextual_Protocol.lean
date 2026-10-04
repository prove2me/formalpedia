-- Prove2me | Definitions.Def_RegretBandits_Contextual_Protocol
-- name    : RegretBandits_Contextual_Protocol
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T09:38:51.106426+00:00
-- url     : https://prove2.me/theorems/6f31632b-88f5-400c-b6c9-694bd7403c1f
-- title:
--   Bandit protocol with adaptive adversary: play histories, path law and expectation
-- statement:
--   This file fixes the probabilistic model shared by the contextual-bandit results of Chapter 4 of Bubeck and Cesa-Bianchi.
--
--   There are $K$ arms $\{1,\dots,K\}$ and rounds $t = 1, 2, \dots$. A **play history** of length $t$ is the sequence $(I_1,\dots,I_t)$ of arms played so far. An **adaptive adversary** assigns at each round $t$ a loss vector $\ell_t = (\ell_{1,t},\dots,\ell_{K,t})$ that may depend on the past plays $I_1,\dots,I_{t-1}$; an oblivious adversary is the special case that ignores them. Against such an adversary every forecaster, whatever feedback it uses, is described by a **sampling rule**: at round $t$, given the past plays, it draws $I_t$ from a weight vector $p_t(\cdot \mid I_1,\dots,I_{t-1})$, using fresh randomness.
--
--   The **law of the plays** over the first $n$ rounds gives the sequence $\omega = (\omega_1,\dots,\omega_n)$ the probability
--   $$\mathbb P(\omega) = \prod_{t=1}^n p_t(\omega_t \mid \omega_1,\dots,\omega_{t-1}),$$
--   and the **expectation** of a quantity $F$ of the plays is $\mathbb E\,F = \sum_\omega \mathbb P(\omega)\,F(\omega)$, the sum running over all $K^n$ play sequences. When each $p_t$ is a probability vector this is exactly the expectation over the forecaster's randomization. The file also defines probability vectors and exponential weights
--   $$\mathrm{expWeights}_\eta(v)_i = \frac{e^{-\eta v_i}}{\sum_k e^{-\eta v_k}} .$$
--
--   **Formalization Note** Rounds are numbered from $0$ in Lean: Lean round $t$ is the book's round $t+1$, and a history of the first $t$ plays is a function `Fin t → Fin K`. Losses and sampling rules are functions of the round and the past plays. A randomized adversary whose randomness is independent of the forecaster's is a mixture of such deterministic adaptive adversaries.
-- source:
--   Bubeck, Cesa-Bianchi, Regret Analysis of Stochastic and Nonstochastic Multi-armed Bandit Problems, arXiv:1204.5721v2, p. 3, Eq. (1.3) and p. 21-22, Eq. (3.1) (adversarial protocol and pseudo-regret)

import Mathlib

namespace RegretBandits.Contextual

/-- The first `t` plays of a play sequence `ω : Fin n → Fin K`, for a round `t : Fin n`.
Rounds are numbered from `0`: round `t` (0-based) is the book's round `t + 1`, and the prefix
holds the plays of the rounds before it. -/
def playPrefix {K n : ℕ} (ω : Fin n → Fin K) (t : Fin n) : Fin (t : ℕ) → Fin K :=
  fun i => ω (Fin.castLE t.isLt.le i)

/-- A forecaster's sampling rule against a fixed environment: at round `t` (0-based), after the
plays `h : Fin t → Fin K` of rounds `0, …, t-1`, the arm is drawn from the weights
`rule t h : Fin K → ℝ`. Since the losses (and the expert advice) are themselves deterministic
functions of the past plays, a rule of this shape describes any forecaster run on a fixed
(possibly adaptive) adversary. -/
abbrev PlayRule (K : ℕ) := (t : ℕ) → (Fin t → Fin K) → Fin K → ℝ

/-- Adaptive loss assignment: `ℓ t h i` is the loss of arm `i` at round `t` (0-based) when the
plays of rounds `0, …, t-1` were `h`. An oblivious adversary is one that ignores `h`. -/
abbrev AdaptiveLosses (K : ℕ) := (t : ℕ) → (Fin t → Fin K) → Fin K → ℝ

/-- Probability that the forecaster with rule `p` produces the plays `ω` in the first `n` rounds,
when at every round it draws a fresh arm from `p t (history)`:
`∏_{t<n} p_t(ω_t | ω_0, …, ω_{t-1})`. -/
noncomputable def pathProb {K : ℕ} (p : PlayRule K) (n : ℕ) (ω : Fin n → Fin K) : ℝ :=
  ∏ t : Fin n, p t (playPrefix ω t) (ω t)

/-- Expectation over the forecaster's own randomization of a quantity `F` of the first `n` plays:
`E F = ∑_ω P(ω) F(ω)`. When every `p t h` is a probability vector this is the expectation under
the law of the play sequence `(I_1, …, I_n)`. -/
noncomputable def pathExpect {K : ℕ} (p : PlayRule K) (n : ℕ) (F : (Fin n → Fin K) → ℝ) : ℝ :=
  ∑ ω : Fin n → Fin K, pathProb p n ω * F ω

/-- `w` is a probability vector on `Fin m`. -/
def IsProbVec {m : ℕ} (w : Fin m → ℝ) : Prop :=
  (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1

/-- Exponential weights: the probability vector proportional to `exp (-η v_i)`,
`i ↦ exp (-η v_i) / ∑_k exp (-η v_k)`. -/
noncomputable def expWeights {m : ℕ} (η : ℝ) (v : Fin m → ℝ) (i : Fin m) : ℝ :=
  Real.exp (-η * v i) / ∑ k, Real.exp (-η * v k)

end RegretBandits.Contextual


