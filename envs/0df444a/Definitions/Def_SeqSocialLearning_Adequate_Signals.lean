-- Prove2me | Definitions.Def_SeqSocialLearning_Adequate_Signals
-- name    : SeqSocialLearning_Adequate_Signals
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T01:13:29.175431+00:00
-- url     : https://prove2.me/theorems/8a448662-259f-41f1-ab40-3b3723d75305
-- title:
--   §2–§3, pp. 3–5 — information structure (F, µ): standing assumptions, posterior µF(E|s), unbounded and totally unbounded signals
-- statement:
--   Let $\Omega$ be a state space and $S$ a signal space, and let $F : \Omega \to \Delta(S)$ be a Markov kernel, $\omega \mapsto F_\omega$, giving the law of a private signal in each state. For a prior $\mu \in \Delta(\Omega)$, let $\mu F \in \Delta(\Omega \times S)$ be the joint law of $(\omega, s)$ with $\omega \sim \mu$ and $s \sim F_\omega$.
--
--   1. **Standing assumptions.** $F$ satisfies the standing assumptions if $F_\omega$ and $F_{\omega'}$ are mutually absolutely continuous for all states $\omega, \omega'$, and $F_\omega \neq F_{\omega'}$ whenever $\omega \neq \omega'$.
--   2. **Signal law.** The law of the signal under $\mu F$ is the mixture $\int F_\omega \, d\mu(\omega)$.
--   3. **Posterior.** For a measurable event $E \subseteq \Omega$, $\mu F(E \mid s) \in [0,1]$ is the posterior probability of $E$ given the signal $s$, read from a regular conditional distribution of the state given the signal under $\mu F$.
--   4. **Unbounded signals with respect to $E$.** $(F, \mu)$ features unbounded signals with respect to $E$ if the support of the law of $s \mapsto \mu F(E \mid s)$ contains both $0$ and $1$. Equivalently, for every $\varepsilon > 0$,
--   $$
--   \Pr_s\big(\mu F(E\mid s) < \varepsilon\big) > 0 \quad\text{and}\quad \Pr_s\big(\mu F(E\mid s) > 1-\varepsilon\big) > 0 .
--   $$
--   5. **Totally unbounded signals.** $(F, \mu)$ features totally unbounded signals if signals are unbounded with respect to every measurable event $E$ with $0 < \mu(E) < 1$.
--
--   Totally unbounded signals are the condition that Theorem 1 shows to be necessary and sufficient for adequate learning.
--
--   **Formalization Note** The posterior is Mathlib's posterior kernel `F†μ`; its law under the signal distribution does not depend on the chosen version. Because the posterior takes values in $[0,1]$, "the support contains $0$ and $1$" is stated in the equivalent $\varepsilon$-form above. The state space must be standard Borel and nonempty for the posterior kernel to exist; in the theorems this follows from the model's assumptions.
-- source:
--   Arieli & Mueller-Frank, A General Analysis of Sequential Social Learning, SSRN 2466903 (version of February 21, 2019), pp. 3–5, §2 (standing assumptions on F), §3 (unbounded and totally unbounded signals, footnote 5)

import Mathlib

namespace SeqSocialLearning.Adequate

open MeasureTheory ProbabilityTheory

variable {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]

/-- The standing assumptions on the signal kernel (§2, p. 3): any two signal distributions
`F ω`, `F ω'` are mutually absolutely continuous, and distinct states have distinct signal
distributions. -/
def Standing (F : Kernel Ω S) : Prop :=
  (∀ ω ω', F ω ≪ F ω') ∧ Function.Injective F

/-- The law of the private signal under `µF` (the `S`-marginal of `µF ∈ ∆(Ω × S)`), §3, p. 4. -/
noncomputable def signalLaw (μ : Measure Ω) (F : Kernel Ω S) : Measure S :=
  F ∘ₘ μ

/-- `µF(E | s)`, the posterior probability of the event `E ⊆ Ω` given the private signal `s`
(§3, p. 4), read off Mathlib's posterior kernel `F†μ` (a regular version of the conditional
law of the state given the signal under `µF`). -/
noncomputable def privPost [StandardBorelSpace Ω] [Nonempty Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (F : Kernel Ω S) [IsFiniteKernel F]
    (E : Set Ω) (s : S) : ℝ :=
  ((F†μ) s E).toReal

/-- `(F, µ)` features unbounded signals with respect to `E` (§3, pp. 4–5): the support of the
law of `s ↦ µF(E | s)` contains both `0` and `1`. Since `µF(E | s) ∈ [0, 1]`, this is
equivalently stated as: for every `ε > 0`, the posterior is below `ε` with positive probability
and above `1 - ε` with positive probability. -/
def UnboundedWrt [StandardBorelSpace Ω] [Nonempty Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (F : Kernel Ω S) [IsFiniteKernel F]
    (E : Set Ω) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    0 < signalLaw μ F {s | privPost μ F E s < ε} ∧
    0 < signalLaw μ F {s | 1 - ε < privPost μ F E s}

/-- `(F, µ)` features totally unbounded signals (§3, p. 5): signals are unbounded with respect
to every measurable event whose prior probability lies strictly between zero and one. -/
def TotallyUnbounded [StandardBorelSpace Ω] [Nonempty Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (F : Kernel Ω S) [IsFiniteKernel F] : Prop :=
  ∀ E : Set Ω, MeasurableSet E → 0 < μ E → μ E < 1 → UnboundedWrt μ F E

end SeqSocialLearning.Adequate


