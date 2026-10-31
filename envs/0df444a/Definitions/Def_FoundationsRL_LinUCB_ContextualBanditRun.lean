-- Prove2me | Definitions.Def_FoundationsRL_LinUCB_ContextualBanditRun
-- name    : FoundationsRL_LinUCB_ContextualBanditRun
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:20:11.715533+00:00
-- url     : https://prove2.me/theorems/76b3d73b-b8c1-4480-827d-47d17161e3da
-- title:
--   A run of the stochastic-reward contextual bandit protocol, with adaptive contexts
-- statement:
--   Fix a reward model $M^\star(\cdot\mid x,\pi)$, a Markov kernel from $\mathcal X\times\Pi$ to $\mathbb R$. A **run** of the contextual bandit protocol on a probability space $(\Omega,\mathcal F,P)$ consists of a filtration $(\mathcal G_t)_t$ and processes $x^t$, $\pi^t$, $r^t$, $p^t$ such that, for every round $t$:
--
--   1. the context $x^t$ is $\mathcal G_t$-measurable, so it may depend on the past in an arbitrary, possibly adversarial, way;
--   2. the action $\pi^t$ has conditional law $p^t$ given $\mathcal G_t$;
--   3. the reward $r^t$ has conditional law $M^\star(\cdot\mid x^t,\pi^t)$ given $\mathcal G_t$ and $\pi^t$ (Eq. (3.1));
--   4. $\pi^t$ and $r^t$ are $\mathcal G_{t+1}$-measurable.
--
--   Here $\mathcal G_t$ plays the role of $(\mathcal H^{t-1},x^t)$, the history together with the current context. Every algorithm, deterministic or randomized, and every adaptive choice of contexts gives a run; nothing about how the learner computes $p^t$ is assumed. This object is the common setting of the chapter's results.
--
--   **Formalization Note** Rounds are indexed from $0$: round $t$ in Lean is round $t+1$ of the book. The book's filtration is $\sigma(\mathcal H^{t-1},x^t)$; any filtration with the properties above is allowed, which also covers private randomness of the learner or of the adversary.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, Contextual Bandit Protocol, p. 38; Assumption 2, Eq. (3.1), p. 39; E_{t−1} = E[· | H^{t−1}, x^t], p. 42

import Mathlib
import Definitions.Def_FoundationsRL_LinUCB_IsCondLaw

open MeasureTheory ProbabilityTheory

namespace FoundationsRL.LinUCB

/-- One run of the stochastic-reward contextual bandit protocol (Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*, arXiv:2312.16730v1, Contextual Bandit Protocol,
p. 38, and Assumption 2, Eq. (3.1), p. 39), on a probability space `(Ω, P)`, with reward model
`Mstar = M⋆(· | x, π)`.

Rounds are indexed by `t : ℕ`, so Lean's round `t` is the book's round `t + 1`. The σ-algebra
`𝓖 t` is what is known once the context of round `t` has been revealed, the book's
`(H^{t−1}, x^t)`:

* `x t` is the context, `𝓖 t`-measurable, so it may depend on the past in an arbitrary, also
  adversarial, way; a fixed sequence is the constant case;
* `p t` is the learner's action distribution `p^t`, and `act t ∼ p t` conditionally on `𝓖 t`;
* `r t ∼ M⋆(· | x t, act t)` conditionally on `𝓖 t` and `act t`.

**Formalization Note.** The book's filtration is `𝓖 t = σ(H^{t−1}, x^t)`; any filtration with
these properties is allowed, which also covers an adversary or a learner with private randomness.
`p`, the contexts and the rewards are data of the run, so the structure says nothing about
how the learner computes them: every (possibly randomized) algorithm gives such a run. -/
structure ContextualBanditRun {Ω X Act : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace X]
    [MeasurableSpace Act] (P : Measure Ω) (Mstar : Kernel (X × Act) ℝ) where
  /-- The information available when the action of round `t` is chosen. -/
  𝓖 : Filtration ℕ mΩ
  /-- The context `x^t`. -/
  x : ℕ → Ω → X
  /-- The action `π^t`. -/
  act : ℕ → Ω → Act
  /-- The reward `r^t`. -/
  r : ℕ → Ω → ℝ
  /-- The action distribution `p^t`. -/
  p : ℕ → Ω → Measure Act
  measurable_x : ∀ t, Measurable[𝓖 t] (x t)
  measurable_act : ∀ t, Measurable[𝓖 (t + 1)] (act t)
  measurable_r : ∀ t, Measurable[𝓖 (t + 1)] (r t)
  /-- `π^t ∼ p^t` given the history and `x^t`. -/
  act_law : ∀ t, IsCondLaw (𝓖 t) P (act t) (p t)
  /-- `r^t ∼ M⋆(· | x^t, π^t)` given the history, `x^t` and `π^t` (Eq. (3.1)). -/
  reward_law : ∀ t, IsCondLaw (𝓖 t ⊔ MeasurableSpace.comap (act t) inferInstance) P (r t)
    fun ω => Mstar (x t ω, act t ω)

end FoundationsRL.LinUCB


