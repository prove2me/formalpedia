-- Prove2me | Definitions.Def_BoltzmannNonuniqueness
-- name    : BoltzmannNonuniqueness
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:02.204267+00:00
-- url     : https://prove2.me/theorems/121d3537-d522-4ea6-9c7a-4a2161e5402d
-- statement:
--   The phase space is the unit three-dimensional torus times ℝ³, with velocities v and positions x. For a unit direction ω, collisions send (v,w) to (v′,w′)=(v−((v−w)·ω)ω,w+((v−w)·ω)ω). The hard-sphere kernel is |(v−w)·ω|, and Q(f)=Q⁺(f)−Q⁻(f), where gain and loss integrate this kernel times f(x,v′)f(x,w′) and f(x,v)f(x,w), respectively, over w and ordinary, unnormalized spherical area. A finite-entropy datum is almost everywhere nonnegative, almost everywhere strongly measurable, and has integrable f(1+|v|²+|log f|), with the zero-density contribution zero. Bounded velocity support means f vanishes almost everywhere outside some positive velocity radius. Energy and momentum are ∫|v|²f and ∫vf. With M(v)=(2π)^(−3/2)exp(−|v|²/2), relative entropy is H(f)=∫[f log(f/M)−f+M]. Entropy dissipation D(f) is one quarter of the integral of the collision kernel times E(f′f′*,ff*), where E(A,B)=(A−B)log(A/B) for positive A,B, E(0,0)=0, and E is infinite otherwise. A renormalization β is continuously differentiable on [0,∞), vanishes at zero, and satisfies |β′(z)|≤C/(1+z) for some C≥0, using the within-domain derivative at zero. Kinetic tests are smooth periodic functions compactly supported in time and velocity; mass tests are smooth periodic functions compactly supported in time and independent of velocity. Their transport derivative is L=∂t+v·∇x. The defined admissibility proposition for an evolution F and datum f₀ requires finite entropy at every nonnegative time, spacetime measurability, F(0)=f₀ almost everywhere, continuity of ∫F(t)ψ for every bounded measurable ψ, and uniformly bounded entropy moments on each finite time interval. It additionally requires almost-everywhere integrability of both collision fibers, separate spacetime integrability of Q⁺(F)/(1+F/M) and Q⁻(F)/(1+F/M) on every finite interval, and, for every β and kinetic test φ, integrability and the identity ∫[Mβ(F/M)Lφ+β′(F/M)Q(F)φ]+∫Mβ(f₀/M)φ(0)=0 over nonnegative times and phase space. For every mass test χ it requires integrability and ∫FLχ+∫f₀χ(0)=0. At every t≥0 it imposes conserved total momentum, energy no greater than its initial value, and H(F(t))⁺+∫₀ᵗD(F(s))ds≤H(f₀)⁺, interpreted in the extended nonnegative reals. Finally, the separate StrongEarly(T,F) proposition requires T>0, strong L¹ continuity throughout [0,T], including one-sided endpoint limits, and separate spacetime integrability of the unrenormalized collision gain and loss on that interval.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/BoltzmannNonuniqueness.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/BoltzmannNonuniqueness.lean; bytes 16..9345
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

/-!
# Nonuniqueness for the periodic hard-sphere Boltzmann equation

Theorem 1.1, with the full entropy-class admissibility of Definition 2.1 and
strong initial L¹ continuity with integrable collision gain and loss.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped RealInnerProductSpace ENNReal Topology

namespace BoltzmannNonuniqueness

abbrev Velocity := EuclideanSpace ℝ (Fin 3)
abbrev Position := Fin 3 → AddCircle (1 : ℝ)
abbrev Phase := Position × Velocity
abbrev Density := Phase → ℝ
abbrev Sphere := Metric.sphere (0 : Velocity) 1

/-- Ordinary surface area, rather than normalized probability on the sphere. -/
def sphereArea : Measure Sphere := (volume : Measure Velocity).toSphere

def normalComponent (v w ω : Velocity) : ℝ := inner ℝ (v - w) ω

def scatterLeft (v w ω : Velocity) : Velocity := v - normalComponent v w ω • ω

def scatterRight (v w ω : Velocity) : Velocity := w + normalComponent v w ω • ω

def collisionKernel (v w ω : Velocity) : ℝ := |normalComponent v w ω|

def gain (f : Density) (x : Position) (v : Velocity) : ℝ :=
  ∫ p : Velocity × Sphere,
    collisionKernel v p.1 p.2 * f (x, scatterLeft v p.1 p.2) *
      f (x, scatterRight v p.1 p.2)
    ∂((volume : Measure Velocity).prod sphereArea)

def loss (f : Density) (x : Position) (v : Velocity) : ℝ :=
  ∫ p : Velocity × Sphere,
    collisionKernel v p.1 p.2 * f (x, v) * f (x, p.1)
    ∂((volume : Measure Velocity).prod sphereArea)

def collision (f : Density) (x : Position) (v : Velocity) : ℝ :=
  gain f x v - loss f x v


abbrev Evolution := ℝ → Density
abbrev SpaceTimePhase := ℝ × Phase
abbrev LiftedSpaceTimePhase := ℝ × (Velocity × Velocity)

def torusProjection (x : Velocity) : Position := fun i => (x i : AddCircle (1 : ℝ))

/-- A representative in the fundamental half-open unit cube, used only to evaluate periodic
derivatives. Periodicity makes those derivatives independent of this choice. -/
def torusRepresentative (x : Position) : Velocity :=
  WithLp.toLp 2 (fun i => ((AddCircle.equivIco (1 : ℝ) 0) (x i) : ℝ))

def maxwellian (v : Velocity) : ℝ :=
  (2 * Real.pi) ^ (-(3 / 2 : ℝ)) * Real.exp (-‖v‖ ^ 2 / 2)

def entropyMoment (f : Density) (z : Phase) : ℝ :=
  f z * (1 + ‖z.2‖ ^ 2 + |Real.log (f z)|)

/-- The convention `0 |log 0| = 0` is automatic in this real-valued moment. -/
def FiniteEntropyDatum (f : Density) : Prop :=
  (∀ᵐ z, 0 ≤ f z) ∧ AEStronglyMeasurable f ∧ Integrable (entropyMoment f)

def BoundedVelocitySupport (f : Density) : Prop :=
  ∃ R : ℝ, 0 < R ∧ ∀ᵐ z, R < ‖z.2‖ → f z = 0

def energy (f : Density) : ℝ := ∫ z, ‖z.2‖ ^ 2 * f z

def momentum (f : Density) : Velocity := ∫ z, f z • z.2

def relativeEntropy (f : Density) : ℝ :=
  ∫ z, f z * Real.log (f z / maxwellian z.2) - f z + maxwellian z.2

/-- Lower semicontinuous extension of `(A-B) log(A/B)` on the nonnegative quadrant.
The off-quadrant value is immaterial for nonnegative densities. -/
def extendedEntropyProduction (A B : ℝ) : ℝ≥0∞ :=
  if A = 0 ∧ B = 0 then 0
  else if 0 < A ∧ 0 < B then ENNReal.ofReal ((A - B) * Real.log (A / B))
  else ⊤

def entropyDissipation (f : Density) : ℝ≥0∞ :=
  (4 : ℝ≥0∞)⁻¹ * ∫⁻ p : Position × (Velocity × (Velocity × Sphere)),
    ENNReal.ofReal (collisionKernel p.2.1 p.2.2.1 p.2.2.2) *
      extendedEntropyProduction
        (f (p.1, scatterLeft p.2.1 p.2.2.1 p.2.2.2) *
          f (p.1, scatterRight p.2.1 p.2.2.1 p.2.2.2))
        (f (p.1, p.2.1) * f (p.1, p.2.2.1))
    ∂((volume : Measure Position).prod ((volume : Measure Velocity).prod
      ((volume : Measure Velocity).prod sphereArea)))

/-- The renormalizations of Definition 2.1, with the right derivative at zero. -/
structure Renormalization where
  toFun : ℝ → ℝ
  regular : ContDiffOn ℝ 1 toFun (Ici 0)
  at_zero : toFun 0 = 0
  derivative_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ Ici (0 : ℝ),
    |derivWithin toFun (Ici 0) z| ≤ C / (1 + z)

/-- A smooth test, periodic in the spatial variable and compact in time and velocity. -/
structure KineticTest where
  toFun : ℝ → Position → Velocity → ℝ
  regular : ContDiff ℝ (⊤ : ℕ∞) (fun p : LiftedSpaceTimePhase =>
    toFun p.1 (torusProjection p.2.1) p.2.2)
  compact_time_velocity : ∃ R : ℝ, 0 < R ∧ ∀ t x v,
    R < |t| ∨ R < ‖v‖ → toFun t x v = 0

def KineticTest.transportDerivative (φ : KineticTest) (t : ℝ) (z : Phase) : ℝ :=
  fderiv ℝ (fun p : LiftedSpaceTimePhase => φ.toFun p.1 (torusProjection p.2.1) p.2.2)
    (t, torusRepresentative z.1, z.2) (1, z.2, 0)

/-- Smooth local mass tests have no velocity cutoff, since their velocity dependence is
introduced only by the transport derivative. -/
structure MassTest where
  toFun : ℝ → Position → ℝ
  regular : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Velocity => toFun p.1 (torusProjection p.2))
  compact_time : ∃ R : ℝ, 0 < R ∧ ∀ t x, R < |t| → toFun t x = 0

def MassTest.transportDerivative (φ : MassTest) (t : ℝ) (z : Phase) : ℝ :=
  fderiv ℝ (fun p : ℝ × Velocity => φ.toFun p.1 (torusProjection p.2))
    (t, torusRepresentative z.1) (1, z.2)

def relativeDensity (F : Evolution) (t : ℝ) (z : Phase) : ℝ := F t z / maxwellian z.2

def renormalizedIntegrand (F : Evolution) (β : Renormalization) (φ : KineticTest)
    (p : SpaceTimePhase) : ℝ :=
  maxwellian p.2.2 * β.toFun (relativeDensity F p.1 p.2) *
      φ.transportDerivative p.1 p.2 +
    derivWithin β.toFun (Ici 0) (relativeDensity F p.1 p.2) *
      collision (F p.1) p.2.1 p.2.2 * φ.toFun p.1 p.2.1 p.2.2

def nonnegativeTimes : Set SpaceTimePhase := Ici (0 : ℝ) ×ˢ univ
def boundedTimes (T : ℝ) : Set SpaceTimePhase := Icc 0 T ×ˢ univ

/-- Full global admissibility, including both separately renormalized collision terms,
local mass, total momentum, and the every-time energy and entropy inequalities. -/
structure AdmissibleGlobal (f₀ : Density) (F : Evolution) : Prop where
  datum : FiniteEntropyDatum f₀
  spacetime_measurable : AEStronglyMeasurable (fun p : SpaceTimePhase => F p.1 p.2)
    (volume.restrict nonnegativeTimes)
  finite_each_time : ∀ t ∈ Ici (0 : ℝ), FiniteEntropyDatum (F t)
  initial : F 0 =ᵐ[volume] f₀
  weak_continuity : ∀ ψ : Phase → ℝ, Measurable ψ →
    (∃ C : ℝ, ∀ z, |ψ z| ≤ C) →
    ContinuousOn (fun t => ∫ z, F t z * ψ z) (Ici 0)
  uniform_moment : ∀ T : ℝ, 0 ≤ T → ∃ C : ℝ, ∀ t ∈ Icc 0 T,
    (∫ z, entropyMoment (F t) z) ≤ C
  -- These finiteness conditions prevent the real Bochner integrals defining `gain` and
  -- `loss` from silently taking the value zero at divergent collision fibers.
  collision_fibers : ∀ T : ℝ, 0 ≤ T → ∀ᵐ p ∂volume.restrict (boundedTimes T),
    Integrable (fun q : Velocity × Sphere =>
      collisionKernel p.2.2 q.1 q.2 *
        F p.1 (p.2.1, scatterLeft p.2.2 q.1 q.2) *
        F p.1 (p.2.1, scatterRight p.2.2 q.1 q.2))
      ((volume : Measure Velocity).prod sphereArea) ∧
    Integrable (fun q : Velocity × Sphere =>
      collisionKernel p.2.2 q.1 q.2 * F p.1 p.2 * F p.1 (p.2.1, q.1))
      ((volume : Measure Velocity).prod sphereArea)
  gain_integrable : ∀ T : ℝ, 0 ≤ T → IntegrableOn
    (fun p : SpaceTimePhase => gain (F p.1) p.2.1 p.2.2 /
      (1 + relativeDensity F p.1 p.2)) (boundedTimes T)
  loss_integrable : ∀ T : ℝ, 0 ≤ T → IntegrableOn
    (fun p : SpaceTimePhase => loss (F p.1) p.2.1 p.2.2 /
      (1 + relativeDensity F p.1 p.2)) (boundedTimes T)
  renormalized_integrable : ∀ β φ, IntegrableOn (renormalizedIntegrand F β φ)
    nonnegativeTimes
  renormalized_equation : ∀ β : Renormalization, ∀ φ : KineticTest,
    (∫ p in nonnegativeTimes, renormalizedIntegrand F β φ p) +
      (∫ z, maxwellian z.2 * β.toFun (f₀ z / maxwellian z.2) *
        φ.toFun 0 z.1 z.2) = 0
  local_mass_integrable : ∀ φ : MassTest, IntegrableOn
    (fun p : SpaceTimePhase => F p.1 p.2 * φ.transportDerivative p.1 p.2)
    nonnegativeTimes
  local_mass : ∀ φ : MassTest,
    (∫ p in nonnegativeTimes, F p.1 p.2 * φ.transportDerivative p.1 p.2) +
      (∫ z, f₀ z * φ.toFun 0 z.1) = 0
  momentum_conservation : ∀ t ∈ Ici (0 : ℝ), momentum (F t) = momentum f₀
  energy_inequality : ∀ t ∈ Ici (0 : ℝ), energy (F t) ≤ energy f₀
  entropy_inequality : ∀ t ∈ Ici (0 : ℝ),
    ENNReal.ofReal (relativeEntropy (F t)) +
      (∫⁻ s in Icc (0 : ℝ) t, entropyDissipation (F s)) ≤
        ENNReal.ofReal (relativeEntropy f₀)

/-- Additional regularity asserted on the common initial interval. The `eLpNorm` statement
is strong `L¹` continuity and cannot be made vacuous by a nonintegrable Bochner integral. -/
structure StrongEarly (T : ℝ) (F : Evolution) : Prop where
  positive_time : 0 < T
  strong_continuity : ∀ t ∈ Icc 0 T,
    Tendsto (fun s => eLpNorm (fun z => F s z - F t z) 1 volume)
      (𝓝[Icc 0 T] t) (𝓝 0)
  gain_integrable : IntegrableOn (fun p : SpaceTimePhase => gain (F p.1) p.2.1 p.2.2)
    (boundedTimes T)
  loss_integrable : IntegrableOn (fun p : SpaceTimePhase => loss (F p.1) p.2.1 p.2.2)
    (boundedTimes T)



end BoltzmannNonuniqueness
end
end OAI


