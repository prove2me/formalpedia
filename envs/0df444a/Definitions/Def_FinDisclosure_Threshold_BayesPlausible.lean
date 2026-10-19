-- Prove2me | Definitions.Def_FinDisclosure_Threshold_BayesPlausible
-- name    : FinDisclosure_Threshold_BayesPlausible
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T22:19:06.105149+00:00
-- url     : https://prove2.me/theorems/197a6134-635f-4f2f-804f-a8c812c34233
-- title:
--   (5), p. 9 — Bayes-plausible distributions over posteriors, and the policy that truthfully reveals whether the state lies in a set
-- statement:
--   Two general objects of Bayesian persuasion over a measurable state space $\Omega$ with prior $\mu_0$.
--
--   1. **Bayes plausibility.** A distribution $\tau$ over posteriors, that is, a measure on the space $\Delta(\Omega)$ of measures on $\Omega$, is *Bayes plausible* for $\mu_0$ if $\tau$ is a probability measure, $\tau$-almost every posterior $\mu$ is a probability measure, and the mean posterior is the prior:
--   $$\mathbb E_\tau\, \mu = \mu_0, \qquad\text{i.e.}\qquad \int \mu(E)\,\tau(d\mu) = \mu_0(E)\ \text{ for every measurable } E \subseteq \Omega.$$
--
--   2. **Revealing a cell.** For a measurable set $A \subseteq \Omega$, the policy that truthfully reveals whether the state lies in $A$ induces the two-point distribution over posteriors
--   $$\tau_A = \mu_0(A)\,\delta_{\mu_0(\cdot\mid A)} + \mu_0(A^{\mathrm c})\,\delta_{\mu_0(\cdot\mid A^{\mathrm c})},$$
--   which puts mass $\mu_0(A)$ on the prior conditioned on $A$ and mass $\mu_0(A^{\mathrm c})$ on the prior conditioned on the complement.
--
--   By Kamenica and Gentzkow (2011, Prop. 1), choosing a signal is equivalent to choosing a Bayes-plausible distribution over posteriors; this is how the paper states the entrepreneur's problem (6).
--
--   **Formalization Note** The space of measures carries Mathlib's Giry σ-algebra, and $\mathbb E_\tau \mu$ is the monadic join `τ.join`. A cell of prior mass $0$ gets weight $0$ in $\tau_A$; its conditional measure is then the zero measure, which does not affect Bayes plausibility.
-- source:
--   Szydlowski, Optimal Financing and Disclosure, working paper (version of March 2017), p. 9 (PDF 9), eqs. (5)–(6); p. 18 (PDF 18), threshold disclosure

import Mathlib

open MeasureTheory ProbabilityTheory

namespace FinDisclosure.Threshold

/-- Bayes plausibility (Szydlowski, (5), p. 9): a distribution `τ` over posteriors (a measure on the
space of measures, with Mathlib's Giry σ-algebra) is Bayes plausible for the prior `μ0` if it is a
probability measure, almost every posterior is a probability measure, and the mean posterior is the
prior, `E_τ μ = μ0`, i.e. `τ.join = μ0`. -/
def IsBayesPlausible {α : Type*} [MeasurableSpace α] (μ0 : Measure α) (τ : Measure (Measure α)) :
    Prop :=
  IsProbabilityMeasure τ ∧ (∀ᵐ μ ∂τ, IsProbabilityMeasure μ) ∧ τ.join = μ0

/-- The distribution over posteriors induced by truthfully revealing whether the state lies in `A`:
with probability `μ0 A` the posterior is `μ0` conditioned on `A`, with probability `μ0 Aᶜ` it is `μ0`
conditioned on `Aᶜ`. A null cell gets weight `0` (its conditional measure is then the zero measure). -/
noncomputable def revealPolicy {α : Type*} [MeasurableSpace α] (μ0 : Measure α) (A : Set α) :
    Measure (Measure α) :=
  μ0 A • Measure.dirac (μ0[|A]) + μ0 Aᶜ • Measure.dirac (μ0[|Aᶜ])

end FinDisclosure.Threshold


