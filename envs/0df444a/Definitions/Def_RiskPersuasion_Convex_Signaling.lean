-- Prove2me | Definitions.Def_RiskPersuasion_Convex_Signaling
-- name    : RiskPersuasion_Convex_Signaling
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T00:39:53.039998+00:00
-- url     : https://prove2.me/theorems/9cf96d95-15e3-48a4-b32a-e3866e2e5571
-- title:
--   Signaling schemes, Bayes posteriors, Bayes-plausible measures (Sec. 2.1, p. 10; Def. 2, p. 35)
-- statement:
--   This file sets up the information structure of Bayesian persuasion with a finite state space and an arbitrary signal space.
--
--   Let $\Omega$ be a finite set of states and let $\Delta(\Omega) = \{\mu \in \mathbb{R}^{\Omega} : \mu \ge 0,\ \sum_{\omega} \mu(\omega) = 1\}$ be the simplex of beliefs, with the Euclidean topology. Fix a prior $\mu^* \in \Delta(\Omega)$.
--
--   1. **Signaling scheme.** For a measurable signal space $S$, a signaling scheme is a probability measure $\pi$ on $\Omega \times S$ whose marginal on $\Omega$ is the prior:
--   $$\pi(\{\omega\} \times S) = \mu^*(\omega) \quad \text{for every } \omega \in \Omega.$$
--   2. **Posterior.** A map $s \mapsto \mu_s \in \Delta(\Omega)$ is a version of the receiver's Bayes posterior under $\pi$ if each coordinate $s \mapsto \mu_s(\omega)$ is measurable and, writing $\pi_S$ for the signal marginal of $\pi$,
--   $$\pi(\{\omega\} \times B) = \int_B \mu_s(\omega)\, \pi_S(ds) \quad \text{for every } \omega \in \Omega \text{ and measurable } B \subseteq S.$$
--   For a discrete signal of positive probability this is $\mu_s(\omega) = \pi(\omega,s)/\sum_{\omega'}\pi(\omega',s)$; on signals of probability zero the posterior is an arbitrary belief, as in the paper.
--   3. **Bayes plausibility (Definition 2).** A probability measure $\eta$ on $\Delta(\Omega)$ is Bayes-plausible for $\mu^*$ if $\mathbb{E}_\eta[\bar s(\omega)] = \mu^*(\omega)$ for every $\omega$, where $\bar s \sim \eta$.
--   4. A receiver strategy $a : S \to A$ into a finite action set is measurable if each event $\{a(\bar s) = b\}$ is measurable. The sender's expected utility is $\mathbb{E}_\pi[v(\bar\omega, a(\bar s))]$, and the objective of problem (14) is $\mathbb{E}_\eta\big[\sum_{\omega} \bar s(\omega)\, v(\omega, a(\bar s))\big]$.
--
--   These are the objects in terms of which problems (3), (4) and (14) of the paper are stated.
--
--   **Formalization Note** Beliefs are functions $\Omega \to \mathbb{R}$ in Mathlib's `stdSimplex ℝ Ω`; `Belief Ω` is that simplex as a measurable subtype of $\mathbb{R}^{\Omega}$. A posterior is any version of Bayes' rule (pinned only $\pi_S$-almost everywhere) that is simplex-valued everywhere, so no division by zero occurs. Measurability of posteriors and strategies is made explicit; the paper leaves it implicit.
-- source:
--   Anunrojwong, Iyer & Lingenbrink, Persuading Risk-Conscious Agents: A Geometric Approach, arXiv:2208.03758v3, p. 10, Section 2.1 (signaling scheme, Bayes posterior); p. 13, problem (3) objective; p. 35, Definition 2; p. 36, problem (14)

import Mathlib

open MeasureTheory

namespace RiskPersuasion.Convex

/-- The belief simplex `Δ(Ω) = stdSimplex ℝ Ω ⊆ ℝ^Ω`, as a type (a measurable subspace of `Ω → ℝ`). -/
abbrev Belief (Ω : Type) [Fintype Ω] : Type := ↥(stdSimplex ℝ Ω)

/-- A signaling scheme `(S, π)`: a probability measure `π` on `Ω × S` whose marginal on the
state space `Ω` is the prior `μstar`, i.e. `π({ω} × S) = μstar(ω)` for every state `ω`. -/
def IsSignalingScheme {Ω S : Type} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSpace S]
    (μstar : Ω → ℝ) (π : Measure (Ω × S)) : Prop :=
  IsProbabilityMeasure π ∧ ∀ ω : Ω, π ({ω} ×ˢ Set.univ) = ENNReal.ofReal (μstar ω)

/-- `post` is a version of the receiver's Bayes posterior under `π`: every `post s` is a belief,
each coordinate `s ↦ post s ω` is measurable, and for every state `ω` and measurable set of
signals `B`, `π({ω} × B) = ∫_B post(s)(ω) dπ_S(s)`, where `π_S` is the signal marginal of `π`.
A version is pinned only `π_S`-almost everywhere, which is the paper's "`μ_s` arbitrary if the
denominator is zero". -/
def IsPosterior {Ω S : Type} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSpace S]
    (π : Measure (Ω × S)) (post : S → Ω → ℝ) : Prop :=
  (∀ s, post s ∈ stdSimplex ℝ Ω) ∧ (∀ ω, Measurable fun s => post s ω) ∧
    ∀ (ω : Ω) (B : Set S), MeasurableSet B →
      (π ({ω} ×ˢ B)).toReal = ∫ s in B, post s ω ∂(π.map Prod.snd)

/-- Definition 2: a probability measure `η` on the belief simplex is Bayes-plausible for the
prior `μstar` if its mean is the prior: `E_η[s̄(ω)] = μstar(ω)` for every state `ω`. -/
def IsBayesPlausible {Ω : Type} [Fintype Ω] (μstar : Ω → ℝ) (η : Measure (Belief Ω)) : Prop :=
  IsProbabilityMeasure η ∧ ∀ ω : Ω, ∫ s, (s : Ω → ℝ) ω ∂η = μstar ω

/-- A receiver strategy `a : S → A` is measurable when every event `{a(s̄) = b}` is measurable
(`A` is finite, so no σ-algebra on `A` is needed). -/
def IsMeasurableStrategy {S A : Type} [MeasurableSpace S] (a : S → A) : Prop :=
  ∀ b : A, MeasurableSet (a ⁻¹' {b})

/-- The sender's expected utility `E_π[v(ω̄, a(s̄))]` under the scheme `π` and strategy `a`. -/
noncomputable def senderValue {Ω S A : Type} [MeasurableSpace Ω] [MeasurableSpace S]
    (v : Ω → A → ℝ) (π : Measure (Ω × S)) (a : S → A) : ℝ :=
  ∫ p, v p.1 (a p.2) ∂π

/-- The objective of problem (14): `E_η[∑_ω s̄(ω) v(ω, a(s̄))]` for a measure `η` on beliefs. -/
noncomputable def beliefValue {Ω A : Type} [Fintype Ω]
    (v : Ω → A → ℝ) (η : Measure (Belief Ω)) (a : Belief Ω → A) : ℝ :=
  ∫ s, ∑ ω, (s : Ω → ℝ) ω * v ω (a s) ∂η

end RiskPersuasion.Convex


