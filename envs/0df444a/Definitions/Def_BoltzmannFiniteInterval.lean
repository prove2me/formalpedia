-- Prove2me | Definitions.Def_BoltzmannFiniteInterval
-- name    : BoltzmannFiniteInterval
-- status  : Definition
-- author  : @Mazecto
-- created : 2026-10-07T18:35:39.867975+00:00
-- url     : https://prove2.me/theorems/398f3327-f0d9-4205-b859-d6779b6e1f16
-- title:
--   Finite-interval entropy admissibility with terminal traces
-- statement:
--   This predicate describes a finite entropy-admissible solution segment of the periodic hard-sphere Boltzmann equation on $[0,T]$, with $T>0$. It retains the same densities, collision operator, Maxwellian, test functions, and entropy dissipation as the global model. All time bounds are restricted to the supplied interval. For every intermediate time, the weak renormalized and local-mass identities include both the initial boundary term and the terminal trace. Momentum is conserved and the energy and entropy inequalities hold at every time. No continuation or nonuniqueness assertion is included.
--
--   The terminal terms make this a reusable interface for concatenating a finite segment with a global solution starting at its last time section.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Nonuniqueness-for-the-periodic-hard-sphere-Boltzmann-equation-September-23-2026/build/sections/06-admissibility.tex; Proposition 6.1 and subsections “Every-time traces, entropy, and the chain rule” and “Continuation and inherited bounds”; Definition 2.1 in 02-framework.tex.

import Definitions.Def_BoltzmannNonuniqueness

noncomputable section
open MeasureTheory Set Filter
open scoped RealInnerProductSpace ENNReal Topology

namespace OAI.BoltzmannNonuniqueness

/-- Entropy admissibility on a closed finite interval. The weak identities include
the terminal trace at every intermediate time, so they can be concatenated with
a solution starting at that trace. No global continuation is built into this predicate.
Source: periodic hard-sphere nonuniqueness preprint, Definition 2.1 and Section 6. -/
structure AdmissibleOn (f₀ : Density) (T : ℝ) (F : Evolution) : Prop where
  positive_time : 0 < T
  datum : FiniteEntropyDatum f₀
  spacetime_measurable : AEStronglyMeasurable (fun p : SpaceTimePhase => F p.1 p.2)
    (volume.restrict (boundedTimes T))
  finite_each_time : ∀ t ∈ Icc (0 : ℝ) T, FiniteEntropyDatum (F t)
  initial : F 0 =ᵐ[volume] f₀
  weak_continuity : ∀ ψ : Phase → ℝ, Measurable ψ →
    (∃ C : ℝ, ∀ z, |ψ z| ≤ C) →
    ContinuousOn (fun t => ∫ z, F t z * ψ z) (Icc 0 T)
  uniform_moment : ∃ C : ℝ, ∀ t ∈ Icc 0 T, (∫ z, entropyMoment (F t) z) ≤ C
  collision_fibers : ∀ᵐ p ∂volume.restrict (boundedTimes T),
    Integrable (fun q : Velocity × Sphere =>
      collisionKernel p.2.2 q.1 q.2 *
        F p.1 (p.2.1, scatterLeft p.2.2 q.1 q.2) *
        F p.1 (p.2.1, scatterRight p.2.2 q.1 q.2))
      ((volume : Measure Velocity).prod sphereArea) ∧
    Integrable (fun q : Velocity × Sphere =>
      collisionKernel p.2.2 q.1 q.2 * F p.1 p.2 * F p.1 (p.2.1, q.1))
      ((volume : Measure Velocity).prod sphereArea)
  gain_integrable : IntegrableOn
    (fun p : SpaceTimePhase => gain (F p.1) p.2.1 p.2.2 /
      (1 + relativeDensity F p.1 p.2)) (boundedTimes T)
  loss_integrable : IntegrableOn
    (fun p : SpaceTimePhase => loss (F p.1) p.2.1 p.2.2 /
      (1 + relativeDensity F p.1 p.2)) (boundedTimes T)
  renormalized_integrable : ∀ β φ, IntegrableOn (renormalizedIntegrand F β φ)
    (boundedTimes T)
  renormalized_equation : ∀ t ∈ Icc (0 : ℝ) T, ∀ β : Renormalization,
    ∀ φ : KineticTest,
    (∫ p in boundedTimes t, renormalizedIntegrand F β φ p) +
      (∫ z, maxwellian z.2 * β.toFun (f₀ z / maxwellian z.2) *
        φ.toFun 0 z.1 z.2) =
      (∫ z, maxwellian z.2 * β.toFun (F t z / maxwellian z.2) *
        φ.toFun t z.1 z.2)
  local_mass_integrable : ∀ φ : MassTest, IntegrableOn
    (fun p : SpaceTimePhase => F p.1 p.2 * φ.transportDerivative p.1 p.2)
    (boundedTimes T)
  local_mass : ∀ t ∈ Icc (0 : ℝ) T, ∀ φ : MassTest,
    (∫ p in boundedTimes t, F p.1 p.2 * φ.transportDerivative p.1 p.2) +
      (∫ z, f₀ z * φ.toFun 0 z.1) = (∫ z, F t z * φ.toFun t z.1)
  momentum_conservation : ∀ t ∈ Icc (0 : ℝ) T, momentum (F t) = momentum f₀
  energy_inequality : ∀ t ∈ Icc (0 : ℝ) T, energy (F t) ≤ energy f₀
  entropy_inequality : ∀ t ∈ Icc (0 : ℝ) T,
    ENNReal.ofReal (relativeEntropy (F t)) +
      (∫⁻ s in Icc (0 : ℝ) t, entropyDissipation (F s)) ≤
        ENNReal.ofReal (relativeEntropy f₀)

end OAI.BoltzmannNonuniqueness


