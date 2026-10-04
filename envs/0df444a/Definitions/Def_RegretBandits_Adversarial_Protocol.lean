-- Prove2me | Definitions.Def_RegretBandits_Adversarial_Protocol
-- name    : RegretBandits_Adversarial_Protocol
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T09:06:21.454647+00:00
-- url     : https://prove2.me/theorems/35a88cc6-4f0c-4171-8e69-731da41b7104
-- title:
--   Adversarial bandit protocol: adaptive adversaries, forecaster runs, regret and pseudo-regret
-- statement:
--   This file fixes the **adversarial bandit protocol** of Bubeck and Cesa-Bianchi (Chapter 1, pp. 5–6, and Chapter 3, pp. 21–22). There are $K$ arms $\{1,\dots,K\}$ and rounds $t = 1, 2, \dots$.
--
--   1. **Adaptive adversary.** At each round $t$ the adversary assigns to every arm $i$ a value $g_{i,t} \in [0,1]$ (a gain, or a loss $\ell_{i,t}$ in the loss version). The value may depend on the forecaster's past actions: $g_{i,t} = g_{i,t}(I_1,\dots,I_{t-1})$. An **oblivious** adversary is the special case in which the values do not depend on the past actions.
--   2. **Forecaster rule.** A forecaster is a rule that, at each round $t$, maps the past actions $I_1,\dots,I_{t-1}$ to a probability vector $p_t = (p_{1,t},\dots,p_{K,t})$ on the arms.
--   3. **Run.** Random arms $I_1, I_2, \dots$ on a probability space $(\Omega, \mathbb P)$ form a run of the rule $p$ if $I_t$ is drawn from $p_t$ given the past, that is, for every $t \ge 1$ and every action sequence $h$,
--   $$
--   \mathbb P(I_1 = h_1,\dots,I_t = h_t) = \mathbb P(I_1 = h_1,\dots,I_{t-1} = h_{t-1})\; p_t(h)(h_t).
--   $$
--   This determines the joint law of $(I_1,\dots,I_n)$ for every $n$.
--   4. **Regret** (gain version, p. 21), a random variable:
--   $$
--   R_n = \max_{i=1,\dots,K} \sum_{t=1}^n g_{i,t} - \sum_{t=1}^n g_{I_t,t},
--   $$
--   where the adaptive gains are evaluated along the realised actions.
--   5. **Pseudo-regret** (loss version, eq. (3.1), p. 22):
--   $$
--   \overline R_n = \mathbb E \sum_{t=1}^n \ell_{I_t,t} - \min_{i=1,\dots,K} \mathbb E \sum_{t=1}^n \ell_{i,t}.
--   $$
--   6. **Exponential weights**: $\mathrm{gibbs}(c, x)_i = e^{c x_i} / \sum_k e^{c x_k}$.
--
--   These objects are shared by all upper bounds of the chapter: Exp3, Exp3.P, Lemma 3.1 and Theorems 3.1–3.3.
--
--   **Formalization Note** Rounds are numbered from $1$ as in the book; actions are functions $h : \mathbb N \to \{1,\dots,K\}$ whose entry at index $0$ is never used, and the adversary and the forecaster rule are required to ignore it. The adversary is deterministic given the past actions. A randomized adversary whose external randomness is independent of the forecaster's reduces to this case by conditioning on its randomness, which is what the book means by "the randomization of the adversary is not very important here since we ask for bounds which hold for any opponent" (p. 6). Since every value is in $[0,1]$ and depends on finitely many discrete random variables, the regret is bounded and measurable, so the expectations above are genuine.
-- source:
--   Bubeck, Cesa-Bianchi, Regret Analysis of Stochastic and Nonstochastic Multi-armed Bandit Problems, arXiv:1204.5721v2, pp. 5–6 (adversarial protocol box, p. 6), p. 21 (regret), p. 22, Eq. (3.1)

import Mathlib

open MeasureTheory

namespace RegretBandits.Adversarial

/-- Two action sequences `h h' : ℕ → Fin K` agree on the rounds `1, …, t - 1`. Rounds are
numbered from `1` as in the book; the entry at index `0` is never used. -/
def AgreeBefore {K : ℕ} (t : ℕ) (h h' : ℕ → Fin K) : Prop :=
  ∀ s, 1 ≤ s → s < t → h s = h' s

/-- A (possibly non-oblivious, i.e. adaptive) adversary for the `K`-armed adversarial bandit
problem (Bubeck–Cesa-Bianchi, arXiv:1204.5721v2, p. 5 and the protocol box on p. 6): at every
round `t ≥ 1` it assigns to each arm `i` a value `val t h i ∈ [0, 1]` (a gain `g_{i,t}` or a loss
`ℓ_{i,t}`), which may depend on the forecaster's past actions `h 1, …, h (t - 1)` only,
`g_{i,t} = g_{i,t}(I_1, …, I_{t-1})`. An oblivious adversary is the special case where `val t h`
does not depend on `h`. -/
structure Adversary (K : ℕ) where
  /-- `val t h i`: the gain (or loss) of arm `i` at round `t` when the past actions are `h`. -/
  val : ℕ → (ℕ → Fin K) → Fin K → ℝ
  /-- Values lie in `[0, 1]`. -/
  val_mem : ∀ t h i, val t h i ∈ Set.Icc (0 : ℝ) 1
  /-- The value at round `t` depends only on the actions of rounds `1, …, t - 1`. -/
  nonanticipating : ∀ t h h', AgreeBefore t h h' → val t h = val t h'

/-- A forecaster rule: `p t h` is the probability vector `p_t = (p_{1,t}, …, p_{K,t})` from which
the arm `I_t` is drawn at round `t ≥ 1`, given the past actions `h 1, …, h (t - 1)`. It is a
probability vector and depends on the past actions only. -/
def IsForecasterRule {K : ℕ} (p : ℕ → (ℕ → Fin K) → Fin K → ℝ) : Prop :=
  (∀ t h i, 0 ≤ p t h i) ∧ (∀ t h, ∑ i, p t h i = 1) ∧
    ∀ t h h', AgreeBefore t h h' → p t h = p t h'

/-- `I` is a run of the forecaster rule `p` on the probability space `(Ω, P)`: every `I t` is a
random arm, and for every round `t ≥ 1` the arm `I_t` is drawn from `p_t` given the past actions,
i.e. for every action sequence `h`,
`P(I_1 = h_1, …, I_t = h_t) = P(I_1 = h_1, …, I_{t-1} = h_{t-1}) · p_t(h)(h_t)`.
This determines the joint law of `(I_1, …, I_n)` for every `n`; `I 0` is not used. -/
def IsRun {K : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (p : ℕ → (ℕ → Fin K) → Fin K → ℝ) (I : ℕ → Ω → Fin K) : Prop :=
  (∀ t, Measurable (I t)) ∧
    ∀ t, 1 ≤ t → ∀ h : ℕ → Fin K,
      P {ω | ∀ s, 1 ≤ s → s ≤ t → I s ω = h s} =
        P {ω | ∀ s, 1 ≤ s → s < t → I s ω = h s} * ENNReal.ofReal (p t h (h t))

/-- The regret (gain version) after `n` rounds, a random variable (p. 21):
`R_n = max_{i} ∑_{t=1}^n g_{i,t} - ∑_{t=1}^n g_{I_t,t}`, where the gains are evaluated along the
realised actions `(I_s ω)_s`. -/
noncomputable def regret {K : ℕ} {Ω : Type*} (g : Adversary K) (n : ℕ) (I : ℕ → Ω → Fin K)
    (ω : Ω) : ℝ :=
  (⨆ i : Fin K, ∑ t ∈ Finset.Icc 1 n, g.val t (fun s => I s ω) i) -
    ∑ t ∈ Finset.Icc 1 n, g.val t (fun s => I s ω) (I t ω)

/-- The pseudo-regret (loss version), eq. (3.1), p. 22:
`R̄_n = E ∑_{t=1}^n ℓ_{I_t,t} - min_{i} E ∑_{t=1}^n ℓ_{i,t}`. -/
noncomputable def pseudoRegret {K : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (ℓ : Adversary K) (n : ℕ) (I : ℕ → Ω → Fin K) : ℝ :=
  (∫ ω, ∑ t ∈ Finset.Icc 1 n, ℓ.val t (fun s => I s ω) (I t ω) ∂P) -
    ⨅ i : Fin K, ∫ ω, ∑ t ∈ Finset.Icc 1 n, ℓ.val t (fun s => I s ω) i ∂P

/-- Exponential weights: `gibbs c x i = exp(c x_i) / ∑_k exp(c x_k)`. -/
noncomputable def gibbs {K : ℕ} (c : ℝ) (x : Fin K → ℝ) (i : Fin K) : ℝ :=
  Real.exp (c * x i) / ∑ k, Real.exp (c * x k)

end RegretBandits.Adversarial


