-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Support21_P03
-- name    : QAlgorithms_Papers_Independent_Support21_P03
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-21T03:29:12.624723+00:00
-- url     : https://prove2.me/theorems/58169c3e-a8c7-43da-964d-0421787bd203
-- title:
--   Definitions for Entropic Fluctuations in Statistical Mechanics I. Classical Dynamical Systems
-- statement:
--   The objects the formalized statements of *Entropic Fluctuations in Statistical Mechanics I. Classical Dynamical Systems* (arXiv:1009.3248) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `TimeKind`: The two time domains permitted in §2.3, PDF p.7.
--   - `TimeKind.Carrier`: Discrete time is Z, continuous time is R; PDF p.7.
--   - `timeValue`: Time as a real number, for the denominator in (3.5), PDF p.9.
--   - `NonsingularSystem`: Exactly F1, F2 and C of §2.3--2.4, PDF p.7. The measurable space is arbitrary and the state is a countably additive probability.
--   - `pushedReference`: The actual evolved reference state, §2.3 p.7: omega_t(f)=omega(f composed with phi_t).
--   - `referenceRNReal`: The RN density, with its standard real representative, §2.1 p.6. Equivalence and probability normalization make it positive and finite a.e.
--   - `logDensity`: Natural log of the RN density, §2.1 p.6. All identities using this representative are a.e.; log's zero default is confined to a null set.
--   - `entropyCocycle`: The entropy cocycle constructed on PDF p.8, not a free additive cocycle.
--   - `meanEntropy`: Sigma^t=c^t/t, (3.5) p.9. Theorems using the mean require nonzero time.
--   - `entropyLaw`: The actual Borel law of Sigma^t, PDF p.9.
--   - `reflectedLaw`: Reflection of a law, PDF p.9.
--   - `ESIdentity`: Equivalence of laws together with the RN identity (3.9), p.10. Both directions of absolute continuity are retained.
--   - `IsTimeReversal`: TRI requires an involutive measurable reversal and preservation of omega, §2.5, PDF p.8. Dynamical reversibility alone is insufficient.
--   - `signedEntropy`: The nonpositive signed relative entropy of (2.1), p.6. Mathlib's finite-measure correction vanishes for the probability laws used here.
--   - `finiteES`: The actual extended logarithmic exponential moment (3.10), PDF p.10. The nonnegative integral retains divergence as +infinity.
--   - `ExtendedConvex`: Convexity of the real epigraph, pp.10,30, expressed using finite upper bounds. This includes extended-valued pressures without assigning a junk value to the indeterminate sum of opposite infinities.
--   - `discreteSigma`: Discrete instantaneous production is c^1, (3.15), PDF p.11.
--   - `RegularSystem`: E1, PDF p.12: actual RN densities are strongly C1 in L1; their actual derivative at zero has a strongly continuous transported L1 orbit. L1 representatives are pinned by a.e. equalities; no cocycle integral, entropy balance or fluctuation identity is an assumed field.
--   - `continuousSigma`: The E1 derivative at t=0, PDF p.12.
--   - `integratedSigma`: Forward or backward oriented integrated production, (3.16), pp.12--13.
--   - `pointMean`: Pointwise forward mean, pp.13,25; time-zero default is never used in a limit.
--   - `backwardPointMean`: Pointwise backward mean appearing in Lemma 5.4, p.25.
--   - `scalarMean`: The scalar averaged expectation defined in §4.3 p.20 and §5.1 p.24.
--   - `IsStationary`: Invariant probabilities, §2.3 p.7.
--   - `RegularSequence`: Regular sequences, immediately before Lemma 5.4, PDF p.25. Increasing means nondecreasing; no unsupported strict inequality is imposed.
--   - `LocallyAbsolutelyContinuous`: Local absolute continuity via its equivalent integral characterization on every compact interval, for Proposition 3.8, PDF pp.12--13.
--   - `AsymptoticES`: ES means an actual all-alpha scaled log-moment limit, PDF p.30. The value is uniquely pinned by convergence in EReal; it is not a free pressure.
--   - `upperMean`: Sigma^+ in Proposition 5.13, PDF p.30. The upper limit is extended real: section 5.3 does not assume E2 or a finite asymptotic mean.
--   - `FiniteDifferentiableAt`: Differentiability of an extended-valued function means finite real values on a neighborhood and ordinary differentiability there, pp.29--30.
--   - `concaveEntropyRate`: Concave rate in the source's nonpositive convention, PDF p.30.
--   - `continuousMeanLaw`: The actual law of the forward time-averaged entropy observable.
--   - `continuousScaledLogEvent`: Scaled log event probability; log(0)=-infinity, as required for LDPs. Time zero is immaterial under the atTop filter, PDF pp.27--29.
--   - `ExtendedConcave`: Concavity with endpoint conventions for a nonpositive extended rate.
--   - `NegativeRateLDP`: The full Borel LDP in the source's concave, nonpositive rate convention, §5.2 pp.27--29. Empty suprema in EReal equal -infinity.
--   - `TopologicalSystem`: NESS1--3, PDF p.37. The chosen bounded continuous representative of sigma is essential when integrating in a singular NESS. It is tied to the E1 derivative only modulo omega, as in the source's regime change.
--   - `cesaroTest`: Cesaro integration of bounded continuous tests, (6.59), PDF p.37.
--   - `CesaroPrecompact`: NESS4 in its equivalent sequential relative-compactness formulation in the metrizable probability space, PDF p.37. This is precompactness of the whole family at t>=1, without assuming any state is invariant.
--   - `IsSelectedNESS`: A selected subsequential Cesaro weak limit, Definition 6.1 p.37. Stationarity and entropy nonnegativity are conclusions, not definition fields.
--   - `topologicalIntegratedSigma`: The integrated chosen continuous observable, valid also in a singular NESS, PDF p.38.
--   - `steadyMeanLaw`: The actual NESS law of the mean entropy production, PDF pp.38--39.
--   - `finiteSteadyES`: The actual finite steady log moment, PDF p.38.
--   - `AsymptoticSteadyES`: GC is existence of the scaled moment limit, not its symmetry, PDF p.38.
-- source:
--   Entropic Fluctuations in Statistical Mechanics I. Classical Dynamical Systems, arXiv:1009.3248v2, https://arxiv.org/abs/1009.3248v2

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P01

/-! Faithful statement draft for arXiv:1009.3248v2.
New source-specific definitions are local to this paper; the exact generic
extended expectation is imported from the pinned accepted library. The reference probability is
nonsingular, and need not be invariant. Compilation is pending batch handoff. -/

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators

namespace QAlgorithms.Papers.Independent.Support21.P03

/-- The two time domains permitted in §2.3, PDF p.7. -/
inductive TimeKind
  | discrete
  | continuous

/-- Discrete time is Z, continuous time is R; PDF p.7. -/
def TimeKind.Carrier : TimeKind → Type
  | .discrete => ℤ
  | .continuous => ℝ

/-- The additive group on the source's Z/R time domains, PDF p.7. -/
instance timeAddCommGroup (K : TimeKind) : AddCommGroup K.Carrier := by
  cases K
  · exact inferInstanceAs (AddCommGroup ℤ)
  · exact inferInstanceAs (AddCommGroup ℝ)

/-- The standard measurable space on each source time domain, PDF p.7. -/
instance timeMeasurableSpace (K : TimeKind) : MeasurableSpace K.Carrier := by
  cases K
  · exact inferInstanceAs (MeasurableSpace ℤ)
  · exact inferInstanceAs (MeasurableSpace ℝ)

/-- Time as a real number, for the denominator in (3.5), PDF p.9. -/
def timeValue (K : TimeKind) : K.Carrier → ℝ := by
  cases K
  · exact fun n : ℤ => (n : ℝ)
  · exact fun t : ℝ => t

example : timeValue .discrete (1 : ℤ) = 1 := by
  norm_num [timeValue]

/-- Exactly F1, F2 and C of §2.3--2.4, PDF p.7. The measurable
space is arbitrary and the state is a countably additive probability. -/
structure NonsingularSystem (K : TimeKind) (M : Type*) [MeasurableSpace M] where
  flow : K.Carrier → M ≃ᵐ M
  flow_zero : ∀ x, flow 0 x = x
  flow_add : ∀ t s x, flow (t + s) x = flow t (flow s x)
  jointly_measurable : Measurable (fun z : K.Carrier × M => flow z.1 z.2)
  omega : ProbabilityMeasure M
  equivalent : ∀ t,
    Measure.map (flow t) (omega : Measure M) ≪ (omega : Measure M) ∧
      (omega : Measure M) ≪ Measure.map (flow t) (omega : Measure M)

variable {K : TimeKind} {M : Type*} [MeasurableSpace M]

/-- The actual evolved reference state, §2.3 p.7: omega_t(f)=omega(f composed with phi_t). -/
def pushedReference (D : NonsingularSystem K M) (t : K.Carrier) : Measure M :=
  Measure.map (D.flow t) (D.omega : Measure M)

/-- The RN density, with its standard real representative, §2.1 p.6.
Equivalence and probability normalization make it positive and finite a.e. -/
def referenceRNReal (D : NonsingularSystem K M) (t : K.Carrier) (x : M) : ℝ :=
  ((pushedReference D t).rnDeriv (D.omega : Measure M) x).toReal

/-- Natural log of the RN density, §2.1 p.6. All identities using this
representative are a.e.; log's zero default is confined to a null set. -/
def logDensity (D : NonsingularSystem K M) (t : K.Carrier) (x : M) : ℝ :=
  Real.log (referenceRNReal D t x)

/-- The entropy cocycle constructed on PDF p.8, not a free additive cocycle. -/
def entropyCocycle (D : NonsingularSystem K M) (t : K.Carrier) (x : M) : ℝ :=
  logDensity D t (D.flow t x)

/-- Sigma^t=c^t/t, (3.5) p.9. Theorems using the mean require nonzero time. -/
def meanEntropy (D : NonsingularSystem K M) (t : K.Carrier) (x : M) : ℝ :=
  entropyCocycle D t x / timeValue K t

/-- The actual Borel law of Sigma^t, PDF p.9. -/
def entropyLaw (D : NonsingularSystem K M) (t : K.Carrier) : Measure ℝ :=
  Measure.map (meanEntropy D t) (D.omega : Measure M)

/-- Reflection of a law, PDF p.9. -/
def reflectedLaw (mu : Measure ℝ) : Measure ℝ :=
  Measure.map (fun s : ℝ => -s) mu

/-- Equivalence of laws together with the RN identity (3.9), p.10.
Both directions of absolute continuity are retained. -/
def ESIdentity (mu : Measure ℝ) (t : ℝ) : Prop :=
  reflectedLaw mu ≪ mu ∧ mu ≪ reflectedLaw mu ∧
    ∀ᵐ s ∂mu, (reflectedLaw mu).rnDeriv mu s = ENNReal.ofReal (Real.exp (-t * s))

/-- TRI requires an involutive measurable reversal and preservation of omega,
§2.5, PDF p.8. Dynamical reversibility alone is insufficient. -/
def IsTimeReversal (D : NonsingularSystem K M) (theta : M ≃ᵐ M) : Prop :=
  Function.Involutive theta ∧
    (∀ t x, theta (D.flow t x) = D.flow (-t) (theta x)) ∧
    Measure.map theta (D.omega : Measure M) = (D.omega : Measure M)

/-- The nonpositive signed relative entropy of (2.1), p.6.
Mathlib's finite-measure correction vanishes for the probability laws used here. -/
def signedEntropy (nu mu : Measure M) : EReal :=
  -(InformationTheory.klDiv nu mu : EReal)

/-- The actual extended logarithmic exponential moment (3.10), PDF p.10.
The nonnegative integral retains divergence as +infinity. -/
def finiteES (D : NonsingularSystem K M) (t : K.Carrier) (alpha : ℝ) : EReal :=
  ENNReal.log (∫⁻ x, ENNReal.ofReal (Real.exp (alpha * logDensity D t x))
    ∂(D.omega : Measure M))

/-- Convexity of the real epigraph, pp.10,30, expressed using finite
upper bounds. This includes extended-valued pressures without assigning a
junk value to the indeterminate sum of opposite infinities. -/
def ExtendedConvex (f : ℝ → EReal) : Prop :=
  ∀ a b r s w : ℝ, f a ≤ (r : EReal) → f b ≤ (s : EReal) →
    0 ≤ w → w ≤ 1 →
    f (w * a + (1 - w) * b) ≤ ((w * r + (1 - w) * s : ℝ) : EReal)

example (mu : Measure M) [SigmaFinite mu] : signedEntropy mu mu = 0 := by
  simp [signedEntropy]

example : ExtendedConvex (fun _ => (0 : EReal)) := by
  intro a b r s w hr hs hw hw1
  have hrReal : (0 : ℝ) ≤ r := EReal.coe_le_coe_iff.mp hr
  have hsReal : (0 : ℝ) ≤ s := EReal.coe_le_coe_iff.mp hs
  exact EReal.coe_le_coe (add_nonneg (mul_nonneg hw hrReal)
    (mul_nonneg (sub_nonneg.mpr hw1) hsReal))

/-- Discrete instantaneous production is c^1, (3.15), PDF p.11. -/
def discreteSigma (D : NonsingularSystem .discrete M) : M → ℝ :=
  entropyCocycle D (1 : ℤ)

example (D : NonsingularSystem .discrete M) :
    discreteSigma D = entropyCocycle D (1 : ℤ) := rfl

/-- E1, PDF p.12: actual RN densities are strongly C1 in L1; their
actual derivative at zero has a strongly continuous transported L1 orbit.
L1 representatives are pinned by a.e. equalities; no cocycle integral,
entropy balance or fluctuation identity is an assumed field. -/
structure RegularSystem (M : Type*) [MeasurableSpace M]
    extends NonsingularSystem .continuous M where
  densityL1 : ℝ → Lp ℝ 1 (omega : Measure M)
  density_agrees : ∀ t, ∀ᵐ x ∂(omega : Measure M),
    densityL1 t x = referenceRNReal toNonsingularSystem t x
  density_c1 : ContDiff ℝ 1 densityL1
  sigmaOrbitL1 : ℝ → Lp ℝ 1 (omega : Measure M)
  orbit_agrees : ∀ t, ∀ᵐ x ∂(omega : Measure M),
    sigmaOrbitL1 t x = (deriv densityL1 (0 : ℝ) : Lp ℝ 1 (omega : Measure M)) (flow t x)
  orbit_continuous : Continuous sigmaOrbitL1

/-- The E1 derivative at t=0, PDF p.12. -/
def continuousSigma (D : RegularSystem M) : M → ℝ :=
  (deriv D.densityL1 (0 : ℝ) : Lp ℝ 1 (D.omega : Measure M))

/-- Forward or backward oriented integrated production, (3.16), pp.12--13. -/
def integratedSigma (D : RegularSystem M) (t : ℝ) (x : M) : ℝ :=
  ∫ s in 0..t, continuousSigma D (D.flow s x)

/-- Pointwise forward mean, pp.13,25; time-zero default is never used in a limit. -/
def pointMean (D : RegularSystem M) (t : ℝ) (x : M) : ℝ :=
  integratedSigma D t x / t

/-- Pointwise backward mean appearing in Lemma 5.4, p.25. -/
def backwardPointMean (D : RegularSystem M) (t : ℝ) (x : M) : ℝ :=
  (∫ s in 0..t, continuousSigma D (D.flow (-s) x)) / t

/-- The scalar averaged expectation defined in §4.3 p.20 and §5.1 p.24. -/
def scalarMean (D : RegularSystem M) (t : ℝ) : ℝ :=
  (∫ s in 0..t, ∫ x, continuousSigma D (D.flow s x) ∂(D.omega : Measure M)) / t

/-- Invariant probabilities, §2.3 p.7. -/
def IsStationary (D : NonsingularSystem K M) (nu : ProbabilityMeasure M) : Prop :=
  ∀ t, Measure.map (D.flow t) (nu : Measure M) = (nu : Measure M)

/-- Regular sequences, immediately before Lemma 5.4, PDF p.25.
Increasing means nondecreasing; no unsupported strict inequality is imposed. -/
def RegularSequence (tn : ℕ → ℝ) : Prop :=
  Monotone tn ∧ Tendsto tn atTop atTop ∧
    ∀ a : ℝ, 0 < a → Summable (fun n => Real.exp (-a * tn n))

example (D : RegularSystem M) (x : M) : integratedSigma D 0 x = 0 := by
  simp [integratedSigma]

/-- Local absolute continuity via its equivalent integral characterization
on every compact interval, for Proposition 3.8, PDF pp.12--13. -/
def LocallyAbsolutelyContinuous (f : ℝ → ℝ) : Prop :=
  ∀ a b : ℝ, ∃ v : ℝ → ℝ, IntervalIntegrable v volume a b ∧
    ∀ t ∈ uIcc a b, f t = f a + ∫ s in a..t, v s

example (c : ℝ) : LocallyAbsolutelyContinuous (fun _ => c) := by
  intro a b
  refine ⟨fun _ => 0, ?_, ?_⟩
  · simp
  · intro t ht
    simp

/-- ES means an actual all-alpha scaled log-moment limit, PDF p.30.
The value is uniquely pinned by convergence in EReal; it is not a free pressure. -/
structure AsymptoticES (D : RegularSystem M) where
  value : ℝ → EReal
  converges : ∀ alpha : ℝ,
    Tendsto (fun t : ℝ => ((1 / t : ℝ) : EReal) * finiteES D.toNonsingularSystem t alpha)
      atTop (𝓝 (value alpha))

/-- Sigma^+ in Proposition 5.13, PDF p.30. The upper limit is extended
real: section 5.3 does not assume E2 or a finite asymptotic mean. -/
def upperMean (D : RegularSystem M) : EReal :=
  Filter.limsup (fun t : ℝ => (scalarMean D t : EReal)) atTop

/-- Differentiability of an extended-valued function means finite real
values on a neighborhood and ordinary differentiability there, pp.29--30. -/
def FiniteDifferentiableAt (f : ℝ → EReal) (a : ℝ) : Prop :=
  (∀ᶠ b in 𝓝 a, f b ≠ ⊥ ∧ f b ≠ ⊤) ∧
    DifferentiableAt ℝ (fun b => (f b).toReal) a

/-- Concave rate in the source's nonpositive convention, PDF p.30. -/
def concaveEntropyRate (e : ℝ → EReal) (s : ℝ) : EReal :=
  ⨅ alpha : ℝ, ((alpha * s : ℝ) : EReal) + e alpha

/-- The actual law of the forward time-averaged entropy observable. -/
def continuousMeanLaw (D : RegularSystem M) (t : ℝ) : Measure ℝ :=
  Measure.map (pointMean D t) (D.omega : Measure M)

/-- Scaled log event probability; log(0)=-infinity, as required for LDPs.
Time zero is immaterial under the atTop filter, PDF pp.27--29. -/
def continuousScaledLogEvent (P : ℝ → Measure ℝ) (B : Set ℝ) (t : ℝ) : EReal :=
  ((1 / t : ℝ) : EReal) * ENNReal.log (P t B)

/-- Concavity with endpoint conventions for a nonpositive extended rate. -/
def ExtendedConcave (I : ℝ → EReal) : Prop :=
  ∀ a b w : ℝ, 0 ≤ w → w ≤ 1 →
    (w : EReal) * I a + ((1 - w : ℝ) : EReal) * I b ≤ I (w * a + (1 - w) * b)

/-- The full Borel LDP in the source's concave, nonpositive rate convention,
§5.2 pp.27--29. Empty suprema in EReal equal -infinity. -/
def NegativeRateLDP (P : ℝ → Measure ℝ) (I : ℝ → EReal) : Prop :=
  ExtendedConcave I ∧ UpperSemicontinuous I ∧
    (∀ s, I s ≤ 0) ∧ (∀ a : ℝ, IsCompact {s | (a : EReal) ≤ I s}) ∧
    ∀ B : Set ℝ, MeasurableSet B →
      sSup (I '' interior B) ≤ Filter.liminf (continuousScaledLogEvent P B) atTop ∧
      Filter.liminf (continuousScaledLogEvent P B) atTop ≤
        Filter.limsup (continuousScaledLogEvent P B) atTop ∧
      Filter.limsup (continuousScaledLogEvent P B) atTop ≤ sSup (I '' closure B)

example (e : ℝ → EReal) (s : ℝ) :
    concaveEntropyRate e s = ⨅ alpha : ℝ, ((alpha * s : ℝ) : EReal) + e alpha := rfl

section NESS

variable [MetricSpace M] [CompleteSpace M] [TopologicalSpace.SeparableSpace M] [BorelSpace M]

/-- NESS1--3, PDF p.37. The chosen bounded continuous representative
of sigma is essential when integrating in a singular NESS. It is tied to
the E1 derivative only modulo omega, as in the source's regime change. -/
structure TopologicalSystem (M : Type*) [MeasurableSpace M] [MetricSpace M]
    [CompleteSpace M] [TopologicalSpace.SeparableSpace M] [BorelSpace M] extends RegularSystem M where
  continuous_flow : Continuous (fun z : ℝ × M => flow z.1 z.2)
  sigma : BoundedContinuousFunction M ℝ
  sigma_agrees : ∀ᵐ x ∂(omega : Measure M), sigma x = continuousSigma toRegularSystem x

/-- Cesaro integration of bounded continuous tests, (6.59), PDF p.37. -/
def cesaroTest (D : TopologicalSystem M) (f : BoundedContinuousFunction M ℝ) (t : ℝ) : ℝ :=
  (∫ s in 0..t, ∫ x, f (D.flow s x) ∂(D.omega : Measure M)) / t

/-- NESS4 in its equivalent sequential relative-compactness formulation
in the metrizable probability space, PDF p.37. This is precompactness of the
whole family at t>=1, without assuming any state is invariant. -/
def CesaroPrecompact (D : TopologicalSystem M) : Prop :=
  ∀ tn : ℕ → ℝ, (∀ n, 1 ≤ tn n) →
    ∃ nu : ProbabilityMeasure M, ∃ sn : ℕ → ℕ, StrictMono sn ∧
      ∀ f : BoundedContinuousFunction M ℝ,
        Tendsto (fun n => cesaroTest D f (tn (sn n))) atTop
          (𝓝 (∫ x, f x ∂(nu : Measure M)))

/-- A selected subsequential Cesaro weak limit, Definition 6.1 p.37.
Stationarity and entropy nonnegativity are conclusions, not definition fields. -/
def IsSelectedNESS (D : TopologicalSystem M) (nu : ProbabilityMeasure M) : Prop :=
  ∃ tn : ℕ → ℝ, Tendsto tn atTop atTop ∧
    ∀ f : BoundedContinuousFunction M ℝ,
      Tendsto (fun n => cesaroTest D f (tn n)) atTop (𝓝 (∫ x, f x ∂(nu : Measure M)))

/-- The integrated chosen continuous observable, valid also in a singular
NESS, PDF p.38. -/
def topologicalIntegratedSigma (D : TopologicalSystem M) (t : ℝ) (x : M) : ℝ :=
  ∫ s in 0..t, D.sigma (D.flow s x)

/-- The actual NESS law of the mean entropy production, PDF pp.38--39. -/
def steadyMeanLaw (D : TopologicalSystem M) (nu : ProbabilityMeasure M) (t : ℝ) : Measure ℝ :=
  Measure.map (fun x => topologicalIntegratedSigma D t x / t) (nu : Measure M)

/-- The actual finite steady log moment, PDF p.38. -/
def finiteSteadyES (D : TopologicalSystem M) (nu : ProbabilityMeasure M)
    (t alpha : ℝ) : EReal :=
  ENNReal.log (∫⁻ x, ENNReal.ofReal (Real.exp (-alpha * topologicalIntegratedSigma D t x))
    ∂(nu : Measure M))

/-- GC is existence of the scaled moment limit, not its symmetry, PDF p.38. -/
structure AsymptoticSteadyES (D : TopologicalSystem M) (nu : ProbabilityMeasure M) where
  value : ℝ → EReal
  converges : ∀ alpha : ℝ,
    Tendsto (fun t : ℝ => ((1 / t : ℝ) : EReal) * finiteSteadyES D nu t alpha)
      atTop (𝓝 (value alpha))

example (D : TopologicalSystem M) (x : M) : topologicalIntegratedSigma D 0 x = 0 := by
  simp [topologicalIntegratedSigma]

end NESS

end QAlgorithms.Papers.Independent.Support21.P03


