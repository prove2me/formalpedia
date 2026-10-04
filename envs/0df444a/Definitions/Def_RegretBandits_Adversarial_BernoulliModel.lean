-- Prove2me | Definitions.Def_RegretBandits_Adversarial_BernoulliModel
-- name    : RegretBandits_Adversarial_BernoulliModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T09:06:40.780609+00:00
-- url     : https://prove2.me/theorems/91b132d8-5305-4fb6-a02a-b4ad37a20694
-- title:
--   Stochastic Bernoulli bandits, forecasters with bandit feedback, and the instances of Lemma 3.2
-- statement:
--   This file fixes the stochastic model of the lower bounds of Section 3.3 of Bubeck and Cesa-Bianchi (pp. 33–34), in which the rewards $Y_{i,t} \in \{0,1\}$ are random.
--
--   1. **Forecaster.** A forecaster is a rule that maps, at each round $t$, the past actions $I_1,\dots,I_{t-1}$ and the past observed rewards $Y_{I_1,1},\dots,Y_{I_{t-1},t-1}$ to a probability vector $q_t$ on the arms. Deterministic forecasters are those whose vectors are point masses.
--   2. **Bernoulli instance.** For means $\nu = (\nu_1,\dots,\nu_K) \in [0,1]^K$, the reward vectors $Y_t = (Y_{1,t},\dots,Y_{K,t})$, $t = 1, 2, \dots$, are i.i.d. and have independent Bernoulli($\nu_i$) coordinates.
--   3. **Run.** Random arms $I_t$ and rewards $Y_t$ on $(\Omega, \mathbb P)$ form a run of the forecaster $q$ on the instance $\nu$ if, for every $t \ge 1$, every action sequence $h$ and every reward table $y$,
--   $$
--   \mathbb P\bigl(I_s = h_s,\, Y_s = y_s,\ s \le t\bigr) = \mathbb P\bigl(I_s = h_s,\, Y_s = y_s,\ s \le t-1\bigr)\, q_t\bigl(h, (y_{h_s,s})_s\bigr)(h_t) \prod_{i=1}^K \nu_i^{y_{i,t}} (1-\nu_i)^{1-y_{i,t}}.
--   $$
--   So $I_t$ is drawn from $q_t$ given the observed past, and $Y_t$ is drawn independently of everything before it and of $I_t$.
--   4. **The instances of Lemma 3.2.** For $\varepsilon \in [0,1)$ and an arm $i$, all arms have mean $\frac{1-\varepsilon}{2}$ except arm $i$, which has mean $\frac{1+\varepsilon}{2}$.
--
--   These objects are used by Lemma 3.2 and Theorem 3.4.
--
--   **Formalization Note** Rewards are Booleans (`true` is the reward $1$) and are turned into real numbers by `rewardVal`. A forecaster that uses internal randomization beyond the current draw is described by the conditional law of $I_t$ given the observed past; its joint law with the rewards is the one above, so quantifying over all such rules $q$ covers all forecasters, deterministic and randomized.
-- source:
--   Bubeck, Cesa-Bianchi, Regret Analysis of Stochastic and Nonstochastic Multi-armed Bandit Problems, arXiv:1204.5721v2, pp. 33–34, Section 3.3 (Theorem 3.4 and Lemma 3.2)

import Mathlib

open MeasureTheory

namespace RegretBandits.Adversarial

/-- A forecaster for the stochastic bandit problem with `{0,1}` rewards (Section 3.3, pp. 33–34):
`q t h o` is the probability vector from which `I_t` is drawn at round `t ≥ 1`, given the past
actions `h 1, …, h (t - 1)` and the observed past rewards `o 1, …, o (t - 1)` (`o s` is the reward
`Y_{I_s,s}` of the arm played at round `s`). It is a probability vector and depends on nothing
else. Deterministic forecasters are those whose vectors are point masses; any internal
randomization of a forecaster is summarized by these conditional probabilities. -/
def IsBanditForecaster {K : ℕ} (q : ℕ → (ℕ → Fin K) → (ℕ → Bool) → Fin K → ℝ) : Prop :=
  (∀ t h o i, 0 ≤ q t h o i) ∧ (∀ t h o, ∑ i, q t h o i = 1) ∧
    ∀ t h h' o o', (∀ s, 1 ≤ s → s < t → h s = h' s ∧ o s = o' s) → q t h o = q t h' o'

/-- The `{0,1}` reward as a real number. -/
def rewardVal (b : Bool) : ℝ := if b then 1 else 0

/-- Probability mass of a Bernoulli(`μ`) variable at `b` (`true` = reward `1`). -/
def bernoulliMass (μ : ℝ) (b : Bool) : ℝ := if b then μ else 1 - μ

/-- The instance of Lemma 3.2 (p. 34): all arms Bernoulli with parameter `(1 - ε)/2` except arm `i`,
which has parameter `(1 + ε)/2`. -/
noncomputable def epsInstance {K : ℕ} (ε : ℝ) (i : Fin K) (j : Fin K) : ℝ :=
  if j = i then (1 + ε) / 2 else (1 - ε) / 2

/-- `(I, Y)` is a run of the forecaster `q` on the stochastic Bernoulli instance with means `ν`
on `(Ω, P)`: `Y t ω i` is the `{0,1}` reward of arm `i` at round `t`, the reward vectors
`Y_1, Y_2, …` are i.i.d. with independent Bernoulli(`ν_i`) coordinates, and `I_t` is drawn from
`q_t` given the past actions and the past observed rewards `Y_{I_s,s}`, `s < t`, independently of
`Y_t`. Formally, for every `t ≥ 1`, every action sequence `h` and every reward table `y`,
`P(I_s = h_s, Y_s = y_s, 1 ≤ s ≤ t) = P(I_s = h_s, Y_s = y_s, 1 ≤ s ≤ t - 1)
  · q_t(h, (y_s(h_s))_s)(h_t) · ∏_i ν_i^{y_t(i)} (1 - ν_i)^{1 - y_t(i)}`. -/
def IsBernoulliRun {K : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (ν : Fin K → ℝ)
    (q : ℕ → (ℕ → Fin K) → (ℕ → Bool) → Fin K → ℝ) (I : ℕ → Ω → Fin K)
    (Y : ℕ → Ω → Fin K → Bool) : Prop :=
  (∀ t, Measurable (I t)) ∧ (∀ t, Measurable (Y t)) ∧
    ∀ t, 1 ≤ t → ∀ (h : ℕ → Fin K) (y : ℕ → Fin K → Bool),
      P {ω | ∀ s, 1 ≤ s → s ≤ t → I s ω = h s ∧ Y s ω = y s} =
        P {ω | ∀ s, 1 ≤ s → s < t → I s ω = h s ∧ Y s ω = y s} *
          ENNReal.ofReal (q t h (fun s => y s (h s)) (h t)) *
            ∏ i, ENNReal.ofReal (bernoulliMass (ν i) (y t i))

end RegretBandits.Adversarial


