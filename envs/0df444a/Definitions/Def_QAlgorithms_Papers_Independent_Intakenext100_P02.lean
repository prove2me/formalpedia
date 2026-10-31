-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P02
-- name    : QAlgorithms_Papers_Independent_Intakenext100_P02
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-30T23:51:59.49382+00:00
-- url     : https://prove2.me/theorems/13767382-5119-40bf-b6d1-6f23aac89724
-- title:
--   Definitions for Correlation measures of a quantum state and information characteristics of a quantum channel
-- statement:
--   The objects the formalized statements of *Correlation measures of a quantum state and information characteristics of a quantum channel* (arXiv:2304.05388) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `DiscretePOVM`: PDF pp.8,13: positive bounded effects with strong sum equal to identity. The outcome index is restricted to countable types at every optimization and theorem. Zero effects may be deleted; admitting them includes padding finite measurements.
--   - `discreteBornWeight`: PDF p.13: Born probabilities, computed from the actual trace pairing.
--   - `discreteOutcomeChannel`: PDF p.14, (35): the quantum-to-classical measurement channel on the full trace class. Its off-diagonal classical coefficients are zero.
--   - `entropyReduction`: PDF p.8, (13): entropy reduction of a measurement on its whole system.
--   - `localER`: PDF pp.8–9, (13): entropy reduction measuring the second factor B.
--   - `firstER`: PDF p.16, (42): entropy reduction measuring the first factor B of BC.
--   - `classicalM`: PDF p.14, (36): unoptimized classical correlation, with measured factor B.
--   - `discreteClassicalCorrelation`: PDF p.13, (33): supremum over every finite or countable POVM.
--   - `discordM`: PDF p.14, (36): used as discord only on classicalM M X < infinity.
--   - `discreteOptimizedDiscord`: PDF p.14, (34): used as discord only where discreteClassicalCorrelation X < infinity.
--   - `correctionG`: PDF p.10, (22): g(0)=0 and the stated positive-argument formula.
--   - `HasRankOneEffects`: PDF pp.9,21: rank-one effects; zero padding is harmless and can be removed. Every nonzero positive rank-one operator is |u><u| for a nonzero u.
--   - `QCInBasis`: PDF p.6, (5): a q-c state in a specified complete basis of B. The trace series has summable probability weights; the source permits mixed signals.
--   - `IsQC`: PDF pp.6,45: the union over ALL complete bases, not one diagonal slice.
--   - `tripartiteAC`: PDF p.15: AC marginal of a state grouped as (AB)C.
--   - `traceA`: PDF p.15: BC marginal of a state grouped as (AB)C.
--   - `chiA`: PDF pp.7,14–15: constrained Holevo capacity of partial trace to A. The accepted barycentricChi optimizes ALL countable ensembles with exact average.
--   - `conditionalAC`: PDF p.15, (40): unnormalized conditional AC state from the mixed-state Born rule. Zero-weight outcomes are omitted by conditionalHolevoA.
--   - `conditionalHolevoA`: PDF p.15, (40): Holevo sum of the ACTUAL conditional ensemble after tracing C. No independently supplied ensemble or zero-probability signal is used.
--   - `FiniteOutput`: PDF pp.18,21: finite-dimensional output SUPPORT, including a finite subspace of an infinite ambient A. No finite coordinate cutoff is imposed.
--   - `extendedDiscordM`: PDF p.21, equivalent expression (54): all-state unoptimized extension. Its l.s.c., agreement, uniqueness and every-sequence limit are theorem content.
--   - `infDiscord`: PDF p.23, (62): infimum of unoptimized all-state extensions.
--   - `supDiscord`: PDF p.23, (63): supremum of optimized finite-output discords.
--   - `LocalMonotone`: PDF pp.21,24: local-A-channel monotonicity on normalized input states.
--   - `ensembleInformationDeficit`: PDF p.39: the ensemble deficit with its natural finite-Holevo domain.
--   - `constrainedInformationDeficit`: PDF p.40: the constrained-capacity deficit; used when barycentricChi is finite.
--   - `TraceClassChannelSemigroup`: PDF p.39: an algebraic channel semigroup; no time regularity is assumed.
--   - `OrthogonalTuple`: PDF p.47: an m-tuple of mutually orthogonal rank-one projectors.
--   - `RankMProjection`: PDF p.47: a rank-m orthogonal projection, without default-valued finrank.
--   - `SpectralExpansion`: PDF pp.46–47: sorted rank-one spectral expansion, padded by zero TERMS when the support is finite. Only positive eigenvalues require a rank-one projector, so finite systems never require an infinite orthonormal family.
--   - `SpectralExpansion.term`: PDF p.46, (118): weighted projector; zero eigenvalues produce zero.
--   - `cqCoefficients`: PDF p.9: the explicit q-c mixture, computed from its signals and basis.
--   - `indexShannonNats`: PDF p.9: Shannon entropy in nats, allowing infinity.
--   - `purifiedDilationCoefficients`: PDF pp.26–27: the state built from the GIVEN Stinespring isometry and purification.
--   - `countableAverageCoefficients`: PDF p.27: the actual average of a countable discrete ensemble.
--   - `countableOutputHolevo`: PDF pp.6,27: relative-entropy Holevo sum, valid at infinite entropy.
--   - `conditionalInput`: PDF p.27: unnormalized conditional input from the reference measurement.
--   - `Induces`: PDF p.27, before (75): M induces the ACTUAL ensemble, including its weights.
--   - `halfTraceClassDiamondDistance`: PDF p.28, (79): HALF diamond norm, on a reference COPY of the input.
--   - `uniformDensityCoefficients`: PDF pp.11,29: chaotic density operator in nonzero finite dimension.
--   - `flaggedTraceClassErasure`: PDF p.29, (85): erasure channel with a new orthogonal flag none. The complex trace is used even on non-self-adjoint trace-class inputs.
--   - `privacy`: PDF p.30, (86): signed privacy. Used only where both Holevo terms are finite.
--   - `generalizedHolevoCapacity`: PDF p.34: all-generalized-ensemble Holevo capacity, allowing infinity.
--   - `oneShotPrivateCapacityNats`: PDF pp.36–37: unregularized private capacity in FINITE input dimension. The feasible privacy set contains zero and is bounded by ln(dim A) for channels and their complements. No real supremum on infinite-input capacities is used.
--   - `HolevoComparison`: PDF pp.28–29: finite-valued Holevo comparison. Finiteness is part of the CONCLUSION, so toReal never silently discards infinite information.
--   - `CapacityComparison`: PDF p.34: capacity comparison with finite capacities in the conclusion.
--   - `IsErasureWitness`: PDF pp.29–30: actual channels realizing the erasure family at 0 and eps, including the corresponding complements at 1 and 1-eps.
--   - `correlatedUniform`: PDF p.11: the uniform diagonal correlated state and a pure diagonal signal.
--   - `diagonalPure`: PDF p.11: |i,i><i,i|; d=0 has no chosen index and is never used.
--   - `basisDephasingCoefficients`: PDF p.35: dephasing in an arbitrary complete finite basis.
--   - `resetQubit`: PDF p.35: reset to the chosen first basis vector.
--   - `MaximallyEntangled`: PDF p.41, (112): maximally entangled PURE inputs on A and its copy.
--   - `UniformQC`: PDF p.41: all uniform q-c comparison states, allowing EVERY reference basis.
--   - `qcProximity`: PDF pp.41–42: the DOUBLE infimum of actual trace distances. Infima are extended nonnegative; the feasible sets are nonempty for nonzero finite A and nonzero E, and all distances lie in [0,1]. No optimizer is assumed.
--   - `entangledCoeff`: PDF p.42, Example 2: the actual maximally entangled input coefficients.
--   - `PartitionGrowth`: PDF pp.7–8,11, (23): the full spectral form of the positive self-adjoint observable, finite Gibbs partition functions and their precise beta→0+ growth. Under (23) the discrete spectral representation is automatic; including its witness identifies the trace exponential rather than assuming any entropy bound.
--   - `energyEnvelope`: PDF p.8, (10): the ACTUAL constrained entropy supremum. No Gibbs formula outside its regime or arbitrary externally supplied envelope is substituted.
--   - `traceClassSquaredFidelity`: PDF p.11: squared fidelity ||sqrt(rho)sqrt(sigma)||_1^2 of actual densities.
--   - `simpleEnergyBound`: PDF p.11, (25): simple energy bound. The zero-radius value is explicitly zero; division is evaluated only at a positive radius in theorem use.
--   - `EnergyConstraint`: PDF p.11: the energy-constrained subsystem is either B or the whole AB. Separate constructors preserve the two possible domains of the observable.
--   - `EnergyConstraint.mean`: PDF p.11: extended mean energy on precisely the constrained subsystem.
--   - `EnergyConstraint.regular`: PDF p.11: condition (23) on the constrained subsystem's observable.
--   - `EnergyConstraint.bound`: PDF p.11, (25): the bound associated with that SAME observable.
--   - `oscillatorSpectrum`: PDF pp.11–12, (26): complete multi-mode number basis and grounded energy. frequency i denotes the positive energy quantum hbar*omega_i, absorbing hbar.
--   - `oscillatorGibbs`: PDF p.8, (11), specialized to the oscillator. Positive E uses the accepted constructed beta(E), not a free state constrained to be optimal. At E=0 the unique ground state is used; no nonexistent positive-temperature solution.
--   - `oscillatorG`: PDF p.12, (27): the oscillator envelope G. The vacuum offset in the numerator is sum_i frequency_i, twice the ungrounded vacuum energy; it is NOT the grounded Hamiltonian's minimum, which is zero. Used only for l>0.
--   - `oscillatorEntropySupremum`: PDF p.8, (10), for the actual grounded oscillator spectrum.
-- source:
--   Correlation measures of a quantum state and information characteristics of a quantum channel, arXiv:2304.05388v3, https://arxiv.org/abs/2304.05388v3

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P01
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P07
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P08
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P18
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P45
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P13
import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P46
import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P08
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P18

/-!
Shirokov, arXiv:2304.05388v3. Natural logarithms, normalized trace-class
states, completed tensor products, and finite or countable measurements.
New definitions belong only to this paper. Frozen definitions are reused.
Infinite information values are retained in ENNReal; subtraction statements
carry their finite-subtrahend domains. Compilation is pending the batch handoff.
-/

noncomputable section

open Filter MeasureTheory
open scoped ENNReal NNReal Topology BigOperators

namespace QAlgorithms.Papers.Independent.Intakenext100.P02

open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33
  (State PureState IsDensity IsTraceClass traceSize rankOne productCoeff tensorApply)
open QAlgorithms.Papers.Independent.Frontier18.P01
  (Channel Complementary Purifies traceFirst traceSecond mutualInformation
   barycentricChi CountableStateEnsemble Barycenter convexOperatorMixture channelTensorAction)
open QAlgorithms.Papers.Independent.Frontier18.P07
  (GeneralizedEnsemble HasAverage HasFiniteSupport averageCoefficients
   extendedEntropyNats extendedRelativeEntropyNats ensembleHolevo pureStates)
open QAlgorithms.Papers.Independent.Frontier18.P08
  (IsQuantumOperation operatorTrace StronglyConverges TraceNormConverges)
open QAlgorithms.Papers.Independent.Frontier18.P18
  (operatorCoeff boundedOperator conjugateCoeff)
open QAlgorithms.Papers.Independent.Gap48.P45
  (boundedTracePair dimensionCount generatedSpace outputSpace coefficientTraceHasSum)

open QAlgorithms.Papers.Independent.Renew46.P08 (qmi)
open QAlgorithms.Papers.Independent.Claimed50.P18 (swapCoeff associateRight dropMiddle)
open QAlgorithms.Papers.Independent.Frontier18.P01 (binaryEntropy)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.8,13: positive bounded effects with strong sum equal to identity.
The outcome index is restricted to countable types at every optimization and theorem.
Zero effects may be deleted; admitting them includes padding finite measurements. -/
structure DiscretePOVM (B K : Type) where
  effect : K → (Hilbert B →L[ℂ] Hilbert B)
  positive : ∀ k u, (inner ℂ u (effect k u)).im = 0 ∧
    0 ≤ (inner ℂ u (effect k u)).re
  total : ∀ u, HasSum (fun k => effect k u) u

/-- PDF p.13: Born probabilities, computed from the actual trace pairing. -/
def discreteBornWeight {B K : Type} (M : DiscretePOVM B K) (X : Matrix B B ℂ) (k : K) : ℝ≥0∞ :=
  ENNReal.ofReal (boundedTracePair X (M.effect k)).re

/-- PDF p.14, (35): the quantum-to-classical measurement channel on the full
trace class. Its off-diagonal classical coefficients are zero. -/
def discreteOutcomeChannel {B K : Type} (M : DiscretePOVM B K)
    (X : Matrix B B ℂ) : Matrix K K ℂ :=
  fun i j => if i = j then boundedTracePair X (M.effect i) else 0

/-- PDF p.8, (13): entropy reduction of a measurement on its whole system. -/
def entropyReduction {B K : Type} (M : DiscretePOVM B K)
    (X : Matrix B B ℂ) : ℝ≥0∞ := mutualInformation X (discreteOutcomeChannel M)

/-- PDF pp.8–9, (13): entropy reduction measuring the second factor B. -/
def localER {A B K : Type} (M : DiscretePOVM B K)
    (X : Matrix (A × B) (A × B) ℂ) : ℝ≥0∞ :=
  mutualInformation X (fun Y => discreteOutcomeChannel M (traceFirst Y))

/-- PDF p.16, (42): entropy reduction measuring the first factor B of BC. -/
def firstER {B C K : Type} (M : DiscretePOVM B K)
    (X : Matrix (B × C) (B × C) ℂ) : ℝ≥0∞ :=
  mutualInformation X (fun Y => discreteOutcomeChannel M (traceSecond Y))

/-- PDF p.14, (36): unoptimized classical correlation, with measured factor B. -/
def classicalM {A B K : Type} (M : DiscretePOVM B K)
    (X : Matrix (A × B) (A × B) ℂ) : ℝ≥0∞ :=
  qmi (channelTensorAction id (discreteOutcomeChannel M) X)

/-- PDF p.13, (33): supremum over every finite or countable POVM. -/
def discreteClassicalCorrelation {A B : Type} (X : Matrix (A × B) (A × B) ℂ) : ℝ≥0∞ :=
  ⨆ (K : Type) (_ : Countable K) (M : DiscretePOVM B K), classicalM M X

/-- PDF p.14, (36): used as discord only on classicalM M X < infinity. -/
def discordM {A B K : Type} (M : DiscretePOVM B K)
    (X : Matrix (A × B) (A × B) ℂ) : ℝ≥0∞ := qmi X - classicalM M X

/-- PDF p.14, (34): used as discord only where discreteClassicalCorrelation X < infinity. -/
def discreteOptimizedDiscord {A B : Type} (X : Matrix (A × B) (A × B) ℂ) : ℝ≥0∞ :=
  qmi X - discreteClassicalCorrelation X

/-- PDF p.10, (22): g(0)=0 and the stated positive-argument formula. -/
def correctionG (x : ℝ) : ℝ := (x+1) * Real.log (x+1) - x * Real.log x

/-- PDF pp.9,21: rank-one effects; zero padding is harmless and can be removed.
Every nonzero positive rank-one operator is |u><u| for a nonzero u. -/
def HasRankOneEffects {B K : Type} (M : DiscretePOVM B K) : Prop :=
  ∀ k, M.effect k = 0 ∨ ∃ u : Hilbert B, u ≠ 0 ∧
    ∀ v, M.effect k v = (inner ℂ u v) • u

/-- PDF p.6, (5): a q-c state in a specified complete basis of B. The trace
series has summable probability weights; the source permits mixed signals. -/
def QCInBasis {A B : Type} (b : HilbertBasis B ℂ (Hilbert B))
    (X : Matrix (A × B) (A × B) ℂ) : Prop :=
  ∃ (w : B → ℝ) (rho : B → State A),
    (∀ i, 0 ≤ w i) ∧ HasSum w 1 ∧
    ∀ p q, X p q = ∑' i, (w i : ℂ) *
      (rho i).coefficients p.1 q.1 * b i p.2 * star (b i q.2)

/-- PDF pp.6,45: the union over ALL complete bases, not one diagonal slice. -/
def IsQC {A B : Type} (X : Matrix (A × B) (A × B) ℂ) : Prop :=
  ∃ b : HilbertBasis B ℂ (Hilbert B), QCInBasis b X

/-- PDF p.15: AC marginal of a state grouped as (AB)C. -/
def tripartiteAC {A B C : Type} (X : Matrix ((A × B) × C) ((A × B) × C) ℂ) :
    Matrix (A × C) (A × C) ℂ :=
  dropMiddle (associateRight X)

/-- PDF p.15: BC marginal of a state grouped as (AB)C. -/
def traceA {A B C : Type} (X : Matrix ((A × B) × C) ((A × B) × C) ℂ) :
    Matrix (B × C) (B × C) ℂ :=
  fun p q => ∑' a, X ((a,p.1),p.2) ((a,q.1),q.2)

/-- PDF pp.7,14–15: constrained Holevo capacity of partial trace to A. The
accepted barycentricChi optimizes ALL countable ensembles with exact average. -/
def chiA {A C : Type} (X : Matrix (A × C) (A × C) ℂ) : ℝ≥0∞ :=
  barycentricChi X traceSecond

/-- PDF p.15, (40): unnormalized conditional AC state from the mixed-state
Born rule. Zero-weight outcomes are omitted by conditionalHolevoA. -/
def conditionalAC {A B C K : Type} (M : DiscretePOVM B K)
    (X : Matrix ((A × B) × C) ((A × B) × C) ℂ) (k : K) :
    Matrix (A × C) (A × C) ℂ :=
  fun p q => boundedTracePair
    (fun i j => X ((p.1,i),p.2) ((q.1,j),q.2)) (M.effect k)

/-- PDF p.15, (40): Holevo sum of the ACTUAL conditional ensemble after
tracing C. No independently supplied ensemble or zero-probability signal is used. -/
def conditionalHolevoA {A B C K : Type} (M : DiscretePOVM B K)
    (X : Matrix ((A × B) × C) ((A × B) × C) ℂ) : ℝ≥0∞ :=
  let w := discreteBornWeight M (traceFirst (traceSecond X))
  ∑' k : {k : K // w k ≠ 0}, w k.val * extendedRelativeEntropyNats
    (traceSecond (((w k.val).toReal⁻¹ : ℂ) • conditionalAC M X k.val))
    (traceSecond (traceSecond X))

/-- PDF pp.18,21: finite-dimensional output SUPPORT, including a finite
subspace of an infinite ambient A. No finite coordinate cutoff is imposed. -/
def FiniteOutput {A : Type} (Phi : Channel A A) : Prop :=
  FiniteDimensional ℂ (outputSpace Phi.val)

/-- PDF p.21, equivalent expression (54): all-state unoptimized extension.
Its l.s.c., agreement, uniqueness and every-sequence limit are theorem content. -/
def extendedDiscordM {A B K : Type} (M : DiscretePOVM B K)
    (X : Matrix (A × B) (A × B) ℂ) : ℝ≥0∞ :=
  ⨆ Phi : {Phi : Channel A A // FiniteOutput Phi},
    discordM M (tensorApply Phi.val.val X)

/-- PDF p.23, (62): infimum of unoptimized all-state extensions. -/
def infDiscord {A B : Type} (X : Matrix (A × B) (A × B) ℂ) : ℝ≥0∞ :=
  ⨅ (K : Type) (_ : Countable K) (M : DiscretePOVM B K), extendedDiscordM M X

/-- PDF p.23, (63): supremum of optimized finite-output discords. -/
def supDiscord {A B : Type} (X : Matrix (A × B) (A × B) ℂ) : ℝ≥0∞ :=
  ⨆ Phi : {Phi : Channel A A // FiniteOutput Phi},
    discreteOptimizedDiscord (tensorApply Phi.val.val X)

/-- PDF pp.21,24: local-A-channel monotonicity on normalized input states. -/
def LocalMonotone {A B : Type} (f : Matrix (A × B) (A × B) ℂ → ℝ≥0∞) : Prop :=
  ∀ (Phi : Channel A A) (rho : State (A × B)),
    f (tensorApply Phi.val rho.coefficients) ≤ f rho.coefficients

/-- PDF p.39: the ensemble deficit with its natural finite-Holevo domain. -/
def ensembleInformationDeficit {A B : Type} (Phi : Matrix A A ℂ → Matrix B B ℂ)
    (mu : GeneralizedEnsemble A) : ℝ≥0∞ :=
  mutualInformation (averageCoefficients mu) Phi - ensembleHolevo Phi mu

/-- PDF p.40: the constrained-capacity deficit; used when barycentricChi is finite. -/
def constrainedInformationDeficit {A B : Type} (Phi : Matrix A A ℂ → Matrix B B ℂ)
    (rho : Matrix A A ℂ) : ℝ≥0∞ := mutualInformation rho Phi - barycentricChi rho Phi

/-- PDF p.39: an algebraic channel semigroup; no time regularity is assumed. -/
structure TraceClassChannelSemigroup (A : Type) where
  channel : ℝ≥0 → Channel A A
  zero : ∀ rho : State A, (channel 0).val rho.coefficients = rho.coefficients
  add : ∀ s t (rho : State A), (channel (t+s)).val rho.coefficients =
    (channel s).val ((channel t).val rho.coefficients)

/-- PDF p.47: an m-tuple of mutually orthogonal rank-one projectors. -/
def OrthogonalTuple {I : Type} {m : ℕ} (P : Fin m → Matrix I I ℂ) : Prop :=
  ∃ u : Fin m → Hilbert I, Orthonormal ℂ u ∧ ∀ i, P i = rankOne (u i)

/-- PDF p.47: a rank-m orthogonal projection, without default-valued finrank. -/
def RankMProjection {I : Type} (m : ℕ) (Q : Matrix I I ℂ) : Prop :=
  ∃ P : Fin m → Matrix I I ℂ, OrthogonalTuple P ∧ Q = ∑ i, P i

/-- PDF pp.46–47: sorted rank-one spectral expansion, padded by zero TERMS
when the support is finite. Only positive eigenvalues require a rank-one
projector, so finite systems never require an infinite orthonormal family. -/
structure SpectralExpansion {I : Type} (rho : State I) where
  weight : ℕ → ℝ
  nonnegative : ∀ i, 0 ≤ weight i
  sorted : Antitone weight
  mass : HasSum weight 1
  vector : ℕ → Hilbert I
  unit : ∀ i, 0 < weight i → ‖vector i‖ = 1
  orthogonal : ∀ i j, i ≠ j → 0 < weight i → 0 < weight j →
    inner ℂ (vector i) (vector j) = 0
  expansion : coefficientTraceHasSum (fun i => (weight i : ℂ) • rankOne (vector i))
    rho.coefficients

/-- PDF p.46, (118): weighted projector; zero eigenvalues produce zero. -/
def SpectralExpansion.term {I : Type} {rho : State I} (s : SpectralExpansion rho)
    (i : ℕ) : Matrix I I ℂ := (s.weight i : ℂ) • rankOne (s.vector i)

example : binaryEntropy 0 = 0 := by simp [QAlgorithms.Papers.Independent.Frontier18.P01.binaryEntropy]

example : binaryEntropy 1 = 0 := by simp [QAlgorithms.Papers.Independent.Frontier18.P01.binaryEntropy]

example : correctionG 0 = 0 := by simp [correctionG]

example {A B : Type} (X : Matrix (A × B) (A × B) ℂ) :
    swapCoeff (swapCoeff X) = X := rfl

example {B K : Type} (M : DiscretePOVM B K) (X : Matrix B B ℂ) (i : K) :
    discreteOutcomeChannel M X i i = boundedTracePair X (M.effect i) := by
  simp [discreteOutcomeChannel]

example {A B : Type} (X : Matrix (A × B) (A × B) ℂ) :
    discreteOptimizedDiscord X = qmi X - discreteClassicalCorrelation X := rfl

example {I : Type} {rho : State I} (s : SpectralExpansion rho) (i : ℕ)
    (h : s.weight i = 0) : s.term i = 0 := by simp [SpectralExpansion.term, h]

/-- PDF p.9: the explicit q-c mixture, computed from its signals and basis. -/
def cqCoefficients {A B : Type} (b : HilbertBasis B ℂ (Hilbert B))
    (w : B → ℝ) (rho : B → State A) : Matrix (A × B) (A × B) ℂ :=
  fun p q => ∑' i, (w i : ℂ) * (rho i).coefficients p.1 q.1 * b i p.2 * star (b i q.2)

/-- PDF p.9: Shannon entropy in nats, allowing infinity. -/
def indexShannonNats {B : Type} (w : B → ℝ) : ℝ≥0∞ :=
  ∑' i, ENNReal.ofReal (-w i * Real.log (w i))

/-- PDF pp.26–27: the state built from the GIVEN Stinespring isometry and purification. -/
def purifiedDilationCoefficients {A B E R : Type} (V : Hilbert A →ₗᵢ[ℂ] Hilbert (B × E))
    (psi : PureState (A × R)) : Matrix ((B × E) × R) ((B × E) × R) ℂ :=
  tensorApply (conjugateCoeff V.toContinuousLinearMap) psi.val.coefficients

/-- PDF p.27: the actual average of a countable discrete ensemble. -/
def countableAverageCoefficients {A : Type} (e : CountableStateEnsemble A) : Matrix A A ℂ :=
  fun i j => ∑' n, ((e.weight n).toReal : ℂ) * (e.state n).coefficients i j

/-- PDF pp.6,27: relative-entropy Holevo sum, valid at infinite entropy. -/
def countableOutputHolevo {A B : Type} (Phi : Matrix A A ℂ → Matrix B B ℂ)
    (e : CountableStateEnsemble A) : ℝ≥0∞ :=
  ∑' n, e.weight n * extendedRelativeEntropyNats
    (Phi (e.state n).coefficients) (Phi (countableAverageCoefficients e))

/-- PDF p.27: unnormalized conditional input from the reference measurement. -/
def conditionalInput {A R K : Type} (M : DiscretePOVM R K)
    (X : Matrix (A × R) (A × R) ℂ) (k : K) : Matrix A A ℂ :=
  fun a b => boundedTracePair (fun i j => X (a,i) (b,j)) (M.effect k)

/-- PDF p.27, before (75): M induces the ACTUAL ensemble, including its weights. -/
def Induces {A R : Type} (M : DiscretePOVM R ℕ) (psi : PureState (A × R))
    (e : CountableStateEnsemble A) : Prop :=
  ∀ i, conditionalInput M psi.val.coefficients i =
    ((e.weight i).toReal : ℂ) • (e.state i).coefficients

/-- PDF p.28, (79): HALF diamond norm, on a reference COPY of the input. -/
def halfTraceClassDiamondDistance {A B : Type} (Phi Psi : Matrix A A ℂ → Matrix B B ℂ) : ℝ≥0∞ :=
  (1/2 : ℝ≥0∞) * ⨆ rho : State (A × A),
    traceSize (tensorApply (fun X => Phi X - Psi X) rho.coefficients)

/-- PDF pp.11,29: chaotic density operator in nonzero finite dimension. -/
def uniformDensityCoefficients (A : Type) [Fintype A] : Matrix A A ℂ :=
  fun i j => if i = j then ((Fintype.card A : ℂ)⁻¹) else 0

/-- PDF p.29, (85): erasure channel with a new orthogonal flag none. The
complex trace is used even on non-self-adjoint trace-class inputs. -/
def flaggedTraceClassErasure {A : Type} (p : ℝ) (X : Matrix A A ℂ) : Matrix (Option A) (Option A) ℂ :=
  fun i j => match i, j with
  | some a, some b => ((1-p : ℝ) : ℂ) * X a b
  | none, none => (p : ℂ) * ∑' a, X a a
  | _, _ => 0

/-- PDF p.30, (86): signed privacy. Used only where both Holevo terms are finite. -/
def privacy {A B E : Type} (Phi : Matrix A A ℂ → Matrix B B ℂ)
    (PhiC : Matrix A A ℂ → Matrix E E ℂ) (mu : GeneralizedEnsemble A) : ℝ :=
  (ensembleHolevo Phi mu).toReal - (ensembleHolevo PhiC mu).toReal

/-- PDF p.34: all-generalized-ensemble Holevo capacity, allowing infinity. -/
def generalizedHolevoCapacity {A B : Type} (Phi : Matrix A A ℂ → Matrix B B ℂ) : ℝ≥0∞ :=
  ⨆ mu : GeneralizedEnsemble A, ensembleHolevo Phi mu

/-- PDF pp.36–37: unregularized private capacity in FINITE input dimension.
The feasible privacy set contains zero and is bounded by ln(dim A) for channels
and their complements. No real supremum on infinite-input capacities is used. -/
def oneShotPrivateCapacityNats {A B E : Type} [Fintype A]
    (Phi : Matrix A A ℂ → Matrix B B ℂ) (PhiC : Matrix A A ℂ → Matrix E E ℂ) : ℝ :=
  sSup {r | ∃ mu : GeneralizedEnsemble A, r = privacy Phi PhiC mu}

/-- PDF pp.28–29: finite-valued Holevo comparison. Finiteness is part of the
CONCLUSION, so toReal never silently discards infinite information. -/
def HolevoComparison {A B C : Type} (Phi : Matrix A A ℂ → Matrix B B ℂ)
    (Psi : Matrix A A ℂ → Matrix C C ℂ)
    (mu : GeneralizedEnsemble A) (bound : ℝ) : Prop :=
  ensembleHolevo Phi mu < ⊤ ∧ ensembleHolevo Psi mu < ⊤ ∧
    |(ensembleHolevo Phi mu).toReal - (ensembleHolevo Psi mu).toReal| ≤ bound

/-- PDF p.34: capacity comparison with finite capacities in the conclusion. -/
def CapacityComparison {A B : Type} (Phi Psi : Matrix A A ℂ → Matrix B B ℂ)
    (bound : ℝ) : Prop :=
  generalizedHolevoCapacity Phi < ⊤ ∧ generalizedHolevoCapacity Psi < ⊤ ∧
    |(generalizedHolevoCapacity Phi).toReal - (generalizedHolevoCapacity Psi).toReal| ≤ bound

/-- PDF pp.29–30: actual channels realizing the erasure family at 0 and eps,
including the corresponding complements at 1 and 1-eps. -/
def IsErasureWitness {A : Type}
    (Phi Psi PhiC PsiC : Channel A (Option A)) (eps : ℝ) : Prop :=
  Complementary Phi PhiC ∧ Complementary Psi PsiC ∧
  (∀ X, IsTraceClass X → Phi.val X = flaggedTraceClassErasure 0 X ∧ Psi.val X = flaggedTraceClassErasure eps X ∧
    PhiC.val X = flaggedTraceClassErasure 1 X ∧ PsiC.val X = flaggedTraceClassErasure (1-eps) X)

/-- PDF p.11: the uniform diagonal correlated state and a pure diagonal signal. -/
def correlatedUniform (d : ℕ) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  fun p q => if p = q ∧ p.1 = p.2 then (d : ℂ)⁻¹ else 0

/-- PDF p.11: |i,i><i,i|; d=0 has no chosen index and is never used. -/
def diagonalPure {d : ℕ} (i : Fin d) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  fun p q => if p = (i,i) ∧ q = (i,i) then 1 else 0

/-- PDF p.35: dephasing in an arbitrary complete finite basis. -/
def basisDephasingCoefficients {A : Type} [Fintype A] (b : HilbertBasis A ℂ (Hilbert A))
    (X : Matrix A A ℂ) : Matrix A A ℂ :=
  fun i j => ∑ k, (inner ℂ (b k) (boundedOperator X (b k))) * b k i * star (b k j)

/-- PDF p.35: reset to the chosen first basis vector. -/
def resetQubit (b : HilbertBasis (Fin 2) ℂ (Hilbert (Fin 2)))
    (X : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (∑ i, X i i) • rankOne (b 0)

/-- PDF p.41, (112): maximally entangled PURE inputs on A and its copy. -/
def MaximallyEntangled {A : Type} [Fintype A] (psi : PureState (A × A)) : Prop :=
  traceSecond psi.val.coefficients = uniformDensityCoefficients A

/-- PDF p.41: all uniform q-c comparison states, allowing EVERY reference basis. -/
def UniformQC {A E : Type} [Fintype A] (X : Matrix (E × A) (E × A) ℂ) : Prop :=
  ∃ (b : HilbertBasis A ℂ (Hilbert A)) (rho : A → State E),
    X = cqCoefficients b (fun _ => (Fintype.card A : ℝ)⁻¹) rho

/-- PDF pp.41–42: the DOUBLE infimum of actual trace distances. Infima are
extended nonnegative; the feasible sets are nonempty for nonzero finite A and
nonzero E, and all distances lie in [0,1]. No optimizer is assumed. -/
def qcProximity {A E : Type} [Fintype A]
    (PhiC : Matrix A A ℂ → Matrix E E ℂ) : ℝ :=
  (⨅ psi : {psi : PureState (A × A) // MaximallyEntangled psi},
    ⨅ theta : {theta : State (E × A) // UniformQC theta.coefficients},
      (1/2 : ℝ≥0∞) * traceSize (tensorApply PhiC psi.val.val.coefficients - theta.val.coefficients)).toReal

/-- PDF p.42, Example 2: the actual maximally entangled input coefficients. -/
def entangledCoeff {A : Type} [Fintype A]
    (b c : HilbertBasis A ℂ (Hilbert A)) : Matrix (A × A) (A × A) ℂ :=
  fun p q => (Fintype.card A : ℂ)⁻¹ *
    ∑ k, ∑ j, b k p.1 * star (b j q.1) * c k p.2 * star (c j q.2)

example {A : Type} (X : Matrix A A ℂ) (a b : A) :
    flaggedTraceClassErasure 0 X (some a) (some b) = X a b := by simp [flaggedTraceClassErasure]

example {A : Type} [Fintype A] (a : A) : uniformDensityCoefficients A a a = (Fintype.card A : ℂ)⁻¹ := by
  simp [uniformDensityCoefficients]

open QAlgorithms.Papers.Independent.Claimed50.P13 (PositiveObservable closedFormExpectation)
open QAlgorithms.Papers.Independent.Frontier18.P18 (stateSquareRoot)

/-- PDF pp.7–8,11, (23): the full spectral form of the positive self-adjoint
observable, finite Gibbs partition functions and their precise beta→0+ growth.
Under (23) the discrete spectral representation is automatic; including its
witness identifies the trace exponential rather than assuming any entropy bound. -/
def PartitionGrowth {I : Type} (H : PositiveObservable I) : Prop :=
  ∃ (b : HilbertBasis I ℂ (Hilbert I)) (energy : I → ℝ),
    (∀ i, 0 ≤ energy i) ∧
    (∀ u, H.form u = ∑' i, ENNReal.ofReal (energy i * ‖inner ℂ (b i) u‖^2)) ∧
    (∀ beta : ℝ, 0 < beta → (∑' i, ENNReal.ofReal (Real.exp (-beta * energy i))) < ⊤) ∧
    Tendsto (fun beta : ℝ => (∑' i, ENNReal.ofReal (Real.exp (-beta * energy i))) ^ beta)
      (𝓝[>] 0) (𝓝 1)

/-- PDF p.8, (10): the ACTUAL constrained entropy supremum. No Gibbs formula
outside its regime or arbitrary externally supplied envelope is substituted. -/
def energyEnvelope {I : Type} (H : PositiveObservable I) (E : ℝ) : ℝ≥0∞ :=
  ⨆ rho : {rho : State I // closedFormExpectation H rho.coefficients ≤ ENNReal.ofReal E},
    extendedEntropyNats rho.val.coefficients

/-- PDF p.11: squared fidelity ||sqrt(rho)sqrt(sigma)||_1^2 of actual densities. -/
def traceClassSquaredFidelity {I : Type} (rho sigma : State I) : ℝ≥0∞ :=
  traceSize (operatorCoeff ((stateSquareRoot rho).comp (stateSquareRoot sigma))) ^ 2

/-- PDF p.11, (25): simple energy bound. The zero-radius value is explicitly
zero; division is evaluated only at a positive radius in theorem use. -/
def simpleEnergyBound {I : Type} (H : PositiveObservable I) (E radius : ℝ) : ℝ≥0∞ :=
  if radius = 0 then 0 else
    ENNReal.ofReal radius * energyEnvelope H (2*E/radius^2) + ENNReal.ofReal (correctionG radius)

/-- PDF p.11: the energy-constrained subsystem is either B or the whole AB.
Separate constructors preserve the two possible domains of the observable. -/
inductive EnergyConstraint (A B : Type) where
  | onB (H : PositiveObservable B)
  | onAB (H : PositiveObservable (A × B))

/-- PDF p.11: extended mean energy on precisely the constrained subsystem. -/
def EnergyConstraint.mean {A B : Type} (constraint : EnergyConstraint A B)
    (X : Matrix (A × B) (A × B) ℂ) : ℝ≥0∞ :=
  match constraint with
  | .onB H => closedFormExpectation H (traceFirst X)
  | .onAB H => closedFormExpectation H X

/-- PDF p.11: condition (23) on the constrained subsystem's observable. -/
def EnergyConstraint.regular {A B : Type} (constraint : EnergyConstraint A B) : Prop :=
  match constraint with
  | .onB H => PartitionGrowth H
  | .onAB H => PartitionGrowth H

/-- PDF p.11, (25): the bound associated with that SAME observable. -/
def EnergyConstraint.bound {A B : Type} (constraint : EnergyConstraint A B)
    (E radius : ℝ) : ℝ≥0∞ :=
  match constraint with
  | .onB H => simpleEnergyBound H E radius
  | .onAB H => simpleEnergyBound H E radius

example {I : Type} (H : PositiveObservable I) (E : ℝ) : simpleEnergyBound H E 0 = 0 := by
  simp [simpleEnergyBound]

/-- PDF pp.11–12, (26): complete multi-mode number basis and grounded energy.
frequency i denotes the positive energy quantum hbar*omega_i, absorbing hbar. -/
def oscillatorSpectrum {l : ℕ} (frequency : Fin l → ℝ) (hf : ∀ i, 0 < frequency i) :
    QAlgorithms.Papers.Independent.Frontier18.P01.Hamiltonian (Fin l → ℕ) where
  energy := fun n => ∑ i, frequency i * (n i : ℝ)
  lower := 0
  bounded_below := by
    intro n
    exact Finset.sum_nonneg (fun i _ => mul_nonneg (le_of_lt (hf i)) (Nat.cast_nonneg (n i)))

/-- PDF p.8, (11), specialized to the oscillator. Positive E uses the accepted
constructed beta(E), not a free state constrained to be optimal. At E=0 the
unique ground state is used; no nonexistent positive-temperature solution. -/
def oscillatorGibbs {l : ℕ} (frequency : Fin l → ℝ) (hf : ∀ i, 0 < frequency i)
    (E : ℝ) : Matrix (Fin l → ℕ) (Fin l → ℕ) ℂ :=
  if E = 0 then rankOne (lp.single 2 (fun _ : Fin l => 0) 1)
  else QAlgorithms.Papers.Independent.Advance50.P46.gibbsCoefficients (oscillatorSpectrum frequency hf) E

/-- PDF p.12, (27): the oscillator envelope G. The vacuum offset in the
numerator is sum_i frequency_i, twice the ungrounded vacuum energy; it is
NOT the grounded Hamiltonian's minimum, which is zero. Used only for l>0. -/
def oscillatorG {l : ℕ} (frequency : Fin l → ℝ) (E : ℝ) : ℝ :=
  (l : ℝ) * Real.log ((E + ∑ i, frequency i) /
    ((l : ℝ) * (∏ i, frequency i) ^ (1 / (l : ℝ)))) + l

/-- PDF p.8, (10), for the actual grounded oscillator spectrum. -/
def oscillatorEntropySupremum {l : ℕ} (frequency : Fin l → ℝ) (hf : ∀ i, 0 < frequency i)
    (E : ℝ) : ℝ≥0∞ :=
  QAlgorithms.Papers.Independent.Advance50.P46.thermalEnvelope (oscillatorSpectrum frequency hf) E

example {l : ℕ} (frequency : Fin l → ℝ) (hf : ∀ i, 0 < frequency i) :
    oscillatorGibbs frequency hf 0 = rankOne (lp.single 2 (fun _ : Fin l => 0) 1) := by
  simp [oscillatorGibbs]

end QAlgorithms.Papers.Independent.Intakenext100.P02


