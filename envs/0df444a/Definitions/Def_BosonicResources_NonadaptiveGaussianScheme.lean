-- Prove2me | Definitions.Def_BosonicResources_NonadaptiveGaussianScheme
-- name    : BosonicResources_NonadaptiveGaussianScheme
-- status  : Definition
-- author  : @Senrui Chen
-- created : 2026-11-27T05:41:16.971094+00:00
-- url     : https://prove2.me/theorems/8d75411c-96e1-4b5f-9c05-5eda7bb4f580
-- title:
--   Non-adaptive single-copy Gaussian measurement schemes (with shared randomness) and their success probability
-- statement:
--   A *non-adaptive single-copy Gaussian measurement scheme* on $N$ copies of an $n$-mode state, with shared randomness in a measurable space $\Lambda$, consists of the following data.
--
--   1. A probability measure $\lambda$ on $\Lambda$: the law of the scheme's own randomness $\omega$, drawn once, independently of the state and of all outcomes.
--   2. For every $\omega\in\Lambda$ and every copy $t\in\{1,\dots,N\}$, a POVM $E_{\omega,t}$ on the $n$-mode system with outcomes in $\mathbb R^{2n}$ that is a Gaussian (general-dyne) measurement with some seed covariance; it is applied to copy $t$ alone.
--   3. The joint law $T_\rho(\omega,\cdot)$ of the $N$ outcomes given $\omega$, a Markov kernel in $\omega$, which for every density operator $\rho$ is the product of the outcome distributions of $E_{\omega,1},\dots,E_{\omega,N}$ on $\rho$.
--
--   No measurement depends on the outcome of another. Given such a scheme, an estimator $\hat\rho$ (a possibly randomized map, i.e. a Markov kernel, from pairs $(\omega,y)$ with $y\in(\mathbb R^{2n})^N$ to density operators), a state $\rho$ and $\varepsilon$, the *success probability* is
--
--   $$
--   \int_{\Lambda}\int_{(\mathbb R^{2n})^N}\Pr\big[D_{\mathrm{tr}}(\hat\rho(\omega,y),\rho)\le\varepsilon\big]\;T_\rho(\omega,dy)\;\lambda(d\omega),
--   $$
--
--   the probability, over $\omega$, the outcomes $y$ and the internal randomness of the estimator, that the estimate is within trace distance $D_{\mathrm{tr}}(\hat\rho,\rho)=\tfrac12\|\hat\rho-\rho\|_1\le\varepsilon$ of $\rho$.
--
--   This is the class of protocols of Theorem 7 ("non-adaptive, non-entangling, Gaussian measurements"): the measurement setting cannot be chosen based on previous rounds of outcomes. The shared randomness covers probabilistic mixtures of such measurements (footnote 7) and the random homodyne angles of the paper's Algorithm 1.
--
--   **Formalization Note** $\Lambda$ may be a one-point space (a deterministic list of seeds). As in `BosonicLearn.AdaptiveScheme`, the outcome law is carried as a kernel together with the identity tying it to the POVMs; this is what makes the transcript measurable in $\omega$. On arrays that are not densities the outcome kernel is an arbitrary Markov kernel. The estimator sees $\omega$ (the measurement settings) as well as the outcomes. The file contains the structure `NonadaptiveGaussianScheme n N Λ` and the success probability `nonadaptiveSuccess S est ρ ε`, a number in $[0,\infty]$; each POVM is required to satisfy `IsGaussianMeasurement` for some seed covariance, which may depend on $\omega$ and $t$.
-- source:
--   Chen, Mele, Fanizza, Li, Mann, Huang, Chen, Preskill, What resources are needed for optimal learning of bosonic Gaussian states?, https://arxiv.org/abs/2603.18136, Sec. 1 (item 3 of the summary of results); Sec. 3.4, Theorem 7; App. E.1, Theorem S12 and footnote 7; App. E.2, Theorem S13 and Algorithm 1

import Mathlib
import Definitions.Def_BosonicLearn_traceDist
import Definitions.Def_BosonicResources_IsGaussianMeasurement

open QAlgorithms.Papers.Independent.Dependency50.P33 (State IsDensity traceSize)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open BosonicLearn (FockPOVM traceDist)

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace BosonicResources

/-- **Non-adaptive single-copy Gaussian measurement schemes (with shared randomness).**
Chen, Mele, Fanizza, Li, Mann, Huang, Chen, Preskill, *What resources are needed for optimal learning of bosonic
Gaussian states?*, arXiv:2603.18136, Theorem 7 ("non-adaptive, non-entangling, Gaussian measurements"), item 3 of the
summary in §1 ("non-adaptive schemes (which means the measurement setting cannot be chosen based on previous rounds of
outcomes)"), Theorem S12 ("non-adaptive, single-copy Gaussian seed measurements"), footnote 7 (probabilistic mixtures
of such measurements), Algorithm 1 / Theorem S13 ("Sample K angles {φ_i} i.i.d. uniformly from [0, π)").

A `NonadaptiveGaussianScheme n N Λ` on `N` copies of an `n`-mode state consists of
1. a probability measure `seedLaw` on a measurable space `Λ` (the scheme's own randomness, drawn once, independently
   of the state and of all outcomes);
2. for every `ω ∈ Λ` and every copy `t < N`, a POVM `povm ω t` that is a Gaussian measurement with some seed covariance
   (`IsGaussianMeasurement`), applied to copy `t` alone;
3. the joint law `outcome ρ ω` of the `N` outcomes given `ω`, a Markov kernel in `ω`, which on a density operator `ρ`
   is the product over `t` of the Born laws of `povm ω t` on `ρ`.
No measurement depends on the outcome of another.

**Formalization Note.** `Λ` may be a one-point space (a deterministic list of seeds). As in
`BosonicLearn.AdaptiveScheme`, the outcome law is carried as a kernel together with the identity tying it to the
POVMs; this is what makes the transcript measurable in `ω`. On arrays that are not densities `outcome` is an
arbitrary Markov kernel. -/
structure NonadaptiveGaussianScheme (n N : ℕ) (Λ : Type) [MeasurableSpace Λ] where
  /-- law of the scheme's shared randomness -/
  seedLaw : Measure Λ
  /-- the shared randomness has a probability law -/
  seedLaw_prob : IsProbabilityMeasure seedLaw
  /-- the measurement applied to copy `t` when the shared randomness is `ω` -/
  povm : Λ → Fin N → FockPOVM (Occupation (Fin n)) (EuclideanSpace ℝ (Fin n ⊕ Fin n))
  /-- every measurement is a Gaussian measurement with some seed covariance -/
  povm_gaussian : ∀ (ω : Λ) (t : Fin N),
    ∃ V : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ, IsGaussianMeasurement (povm ω t) V
  /-- joint law of the `N` outcomes on the state `ρ`, as a kernel in the shared randomness -/
  outcome : Matrix (Occupation (Fin n)) (Occupation (Fin n)) ℂ →
    Kernel Λ (Fin N → EuclideanSpace ℝ (Fin n ⊕ Fin n))
  /-- the outcome kernel is Markov -/
  outcome_markov : ∀ ρ, IsMarkovKernel (outcome ρ)
  /-- on densities the outcomes are independent, each with the Born law of its measurement -/
  outcome_born : ∀ ρ, IsDensity ρ → ∀ ω : Λ,
    outcome ρ ω = Measure.pi (fun t => (povm ω t).law ρ)

/-- **Success probability of a non-adaptive single-copy Gaussian learner.**
arXiv:2603.18136, Theorem 7 and Theorems S12–S13: "learn a Gaussian state ρ(µ,Σ) to ε trace distance closeness with
probability 2/3".

For a non-adaptive Gaussian scheme `S`, a (possibly randomized) estimator `est`, a Markov kernel from the shared
randomness `ω` and the `N` outcomes `y` to density operators, a state `ρ` and `ε`, `nonadaptiveSuccess S est ρ ε` is
the probability, over `ω`, the outcomes and the estimator's internal randomness, that `½‖ρ̂ − ρ‖₁ ≤ ε`.

**Formalization Note.** The estimator sees `ω` (the measurement settings) as well as the outcomes. -/
noncomputable def nonadaptiveSuccess {n N : ℕ} {Λ : Type} [MeasurableSpace Λ]
    (S : NonadaptiveGaussianScheme n N Λ)
    (est : Kernel (Λ × (Fin N → EuclideanSpace ℝ (Fin n ⊕ Fin n))) (State (Occupation (Fin n))))
    (ρ : Matrix (Occupation (Fin n)) (Occupation (Fin n)) ℂ) (ε : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ∫⁻ y, est (ω, y) {σ | traceDist σ.coefficients ρ ≤ ENNReal.ofReal ε} ∂(S.outcome ρ ω) ∂S.seedLaw

end BosonicResources


