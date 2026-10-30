-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P41
-- name    : QAlgorithms_Papers_Independent_Extend50_P41
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T20:35:10.980442+00:00
-- url     : https://prove2.me/theorems/2a6b0a13-3d35-42b8-a14a-c81918c90255
-- title:
--   Definitions for Quantum state estimation and large deviations
-- statement:
--   The objects the formalized statements of *Quantum state estimation and large deviations* (arXiv:quant-ph/0412053) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `conjugateState`: PDF p.4, (7)-(8): the action rho ↦ U rho U*.
--   - `OrderedProbability`: PDF p.3, (4): the ordered probability simplex.
--   - `OrderedSpectrum`: PDF p.3, (4): Sigma with its usual subspace topology.
--   - `spectrumVector`: PDF p.3, (4): decreasing eigenvalues. The Fin.cast only removes card(Fin d).
--   - `diagonalStateMatrix`: PDF p.7, (21): rho_x, as an actual diagonal matrix.
--   - `CopyIndex`: PDF p.4, (3): positive-copy tensor register.
--   - `Scheme`: PDF pp.3-4: a scheme, fixed before the input state. The scalar laws and their Born identity are redundant data: the identity on all Borel events uniquely determines each law from the normalized operator POVM. This avoids making a tensor-PSD proof part of a new definition body.
--   - `GoodRate`: PDF p.37, A.1: good, nonnegative extended rate.
--   - `logMass`: PDF pp.37-38: extended natural logarithm, including log(0)=-infinity.
--   - `scaledLog`: PDF p.37, (215)-(216): 1/N log probability, with N=k+1.
--   - `HasLDP`: PDF p.37, A.2: closed upper and open lower bounds, with a good rate. The infimum over an empty event is infinity. No Borel-set exact limit is asserted.
--   - `SchemeLDP`: PDF pp.4-5, Def.2.2. The relation `target rho x` is p(rho)=x; using a relation also permits the spectral projection without an auxiliary choice.
--   - `FullTarget`: PDF p.4: full estimation has target map Id.
--   - `SpectralTarget`: PDF p.3, (4): the spectral target is the decreasing eigenvalue vector.
--   - `AdmissibleRate`: PDF p.5, Def.2.3: admissibility requires a single witnessing scheme.
--   - `JointLSC`: PDF p.5, (9): joint lower semicontinuity in both arguments.
--   - `optimalRate`: PDF p.5, (12): unrestricted or regular optimal rate, as an extended supremum.
--   - `PermutationInvariantAt`: PDF p.4, (6): permutation invariance at a fixed copy count.
--   - `CovariantAt`: PDF p.4, (7): covariance of the full-state observable at a fixed copy count.
--   - `CovariantAdmissible`: PDF p.5, (10): covariance requires a covariant witnessing scheme.
--   - `covariantOptimal`: PDF p.5, (13): supremum over rates with a covariant full-estimation witness.
--   - `InvariantRate`: PDF p.5, (11): simultaneous conjugation, in the same orientation.
--   - `weightedNegLog`: PDF pp.8,25: weighted -log, with zero weight contributing zero even at p=0.
--   - `principalMinor`: PDF p.8, (26): the leading (k+1)-by-(k+1) principal minor.
--   - `nextCoordinate`: PDF p.8, (26): the final coordinate is followed by zero.
--   - `minorFormula`: PDF pp.8,25, (26),(131): the formula in a specified eigenbasis of the estimate.
--   - `fullRate`: PDF p.8, (26): the full rate, defined from all spectral representations. Lemma 4.15 states basis independence and equality with the displayed formula; its equality also rules out any clamping by toENNReal.
--   - `spectralRate`: PDF p.7, (19): the classical divergence D(x||s(rho)) with zero conventions.
--   - `SchurCoordinateIndex`: PDF pp.6-7: actual Schur and Specht coordinate dimensions.
--   - `highestCoordinates`: PDF pp.6-7: coordinates of the actual highest-weight vector.
--   - `schurAction`: PDF p.6, (14): pi_Y computed on the actual Schur module, in its public basis.
--   - `embedBlock`: PDF p.6, (14): embed Q_Y tensor I_K into the physical tensor space. The accepted transform is Specht-first, so the Specht index is matched first.
--   - `matrixInEvent`: PDF pp.7-8: Borel event pullback along a matrix-valued decoder. No arbitrary state decoder or certificate is supplied.
--   - `fullEstimatorOperator`: PDF p.7, (20): the explicit raw full-estimation POVM on Borel events. Normalized-POVM and Born-law witnesses are conclusions of Theorem 3.2.
--   - `spectralEstimatorOperator`: PDF p.7, (17): the explicit spectral estimator using physical central projectors.
--   - `spectralPreimage`: PDF p.7, (22): the preimage of a spectral event under s.
--   - `SpectralCovariantAt`: PDF p.7: covariance for spectral estimation has trivial outcome action.
--   - `spectralCovariantOptimal`: PDF p.5, (13), for the spectral projection.
--   - `logLaplaceMoment`: PDF p.11, (35): the scaled negative log Laplace logLaplaceMoment. Continuous f on compact S is bounded; under the scheme assumptions the integral is finite and positive.
--   - `limitMomentExtended`: PDF p.11, (36): extended infimum; continuous f and an admissible rate make it finite.
--   - `limitMoment`: PDF p.11, (36): the real-valued limiting logLaplaceMoment. The LDP hypotheses and compactness ensure that this toReal never discards an infinite value in our theorems.
--   - `actionTest`: PDF p.15, (64): alpha_U f(sigma)=f(U sigma U*).
--   - `permutationAverageOperator`: PDF p.17, (79): permutation average, exactly 1/N! times the sum.
--   - `unitaryAverageOperator`: PDF p.17, (81): normalized Haar average of the translated observable.
--   - `orbitRate`: PDF p.17, (82): simultaneous inverse-conjugation orbit infimum.
--   - `FiniteOperatorMeasure`: PDF pp.21-23: finite positive operator measures for the non-normalized seeds.
--   - `seedObservable`: PDF p.22, (111): event form of the single-Schur-factor orbit disintegration.
--   - `discreteSeedObservable`: PDF p.24, (124): the discrete seed representation of a fixed observable.
--   - `youngDimensionLaw`: PDF p.27, (142): the explicit dimension-weighted probability measures. The branch merely avoids needing a separate proof in the definition that every valid normalized Young shape belongs to Sigma; Lemma 4.16 asserts mass one.
--   - `maximallyMixedRate`: PDF p.27, (147): entropy rate at the maximally mixed input.
--   - `blochDensityMatrix`: PDF p.9, (29): Bloch matrix with the standard Pauli orientation.
--   - `blochLength`: PDF p.9, (29): Euclidean length of a Bloch vector.
--   - `blochDirectionalComponent`: PDF p.9, (29): extension of r cos(theta) at zero Bloch vectors. If y=0 its value is irrelevant because its weight is zero.
--   - `PureDensityState`: PDF p.32, (183): purity means a unit-vector rank-one density matrix.
--   - `SymmetricVector`: PDF p.33: the symmetric subspace consists of permutation-fixed vectors.
--   - `PureTestProperties`: PDF p.33, (185)-(186): the two asymptotic requirements on a pure local test.
--   - `Consistent`: PDF p.4, Def.2.1: weak consistency for full estimation. All continuous real test functions are bounded because the finite-dimensional state space is compact.
-- source:
--   Quantum state estimation and large deviations, arXiv:quant-ph/0412053v2, https://arxiv.org/abs/quant-ph/0412053v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_GeneralPOVMs
import Definitions.Def_QAlgorithms_Defs_TomographyOutcomes
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Defs_ExtendedQuantumEntropy
import Definitions.Def_QAlgorithms_Defs_SchurWeylDecomposition
import Definitions.Def_QAlgorithms_Defs_SchurUnitaryEnsembles

/-!
Statements from M. Keyl, Quantum state estimation and large deviations,
arXiv:quant-ph/0412053v2. All page citations below are PDF page numbers.
The local definitions implement this paper's statistical model; N is always k+1.
DensityOutcome, tensorPow and Umegaki entropy are imported frozen APIs.
Von Neumann entropy in nats is the frozen bit entropy multiplied by log 2.
No theorem is imported from another paper chunk. Compilation is pending.
-/

noncomputable section

open MeasureTheory Filter
open scoped Matrix ComplexOrder ENNReal Topology Matrix.Norms.Frobenius

namespace QAlgorithms.Papers.Independent.Extend50.P41

open QAlgorithms.Tomography (DensityOutcome)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.4, (7)-(8): the action rho ↦ U rho U*. -/
def conjugateState {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℂ) (rho : DensityOutcome d) : DensityOutcome d :=
  ⟨(U : Matrix (Fin d) (Fin d) ℂ) * rho.val * star (U : Matrix (Fin d) (Fin d) ℂ), by
    refine ⟨rho.property.1.mul_mul_conjTranspose_same (U : Matrix (Fin d) (Fin d) ℂ), ?_⟩
    rw [Matrix.trace_mul_cycle, Unitary.star_mul_self_of_mem U.property, one_mul]
    exact rho.property.2⟩

/-- PDF p.3, (4): the ordered probability simplex. -/
def OrderedProbability {d : ℕ} (x : Fin d → ℝ) : Prop :=
  Antitone x ∧ (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1

/-- PDF p.3, (4): Sigma with its usual subspace topology. -/
abbrev OrderedSpectrum (d : ℕ) := {x : Fin d → ℝ // OrderedProbability x}

/-- PDF p.3, (4): Borel events in Sigma. -/
instance spectrumMeasurable (d : ℕ) : MeasurableSpace (OrderedSpectrum d) := borel _

/-- PDF p.3, (4): compatibility of the topology and Borel events. -/
instance spectrumBorel (d : ℕ) : BorelSpace (OrderedSpectrum d) := ⟨rfl⟩

/-- PDF p.3, (4): decreasing eigenvalues. The Fin.cast only removes card(Fin d). -/
def spectrumVector {d : ℕ} (rho : DensityOutcome d) : Fin d → ℝ :=
  fun i => rho.property.1.isHermitian.eigenvalues₀ (Fin.cast (Fintype.card_fin d).symm i)

/-- PDF p.7, (21): rho_x, as an actual diagonal matrix. -/
def diagonalStateMatrix {d : ℕ} (x : OrderedSpectrum d) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.diagonal fun i => (x.val i : ℂ)

/-- PDF p.4, (3): positive-copy tensor register. -/
abbrev CopyIndex (d k : ℕ) := Fin (k+1) → Fin d

/-- PDF pp.3-4: a scheme, fixed before the input state.
The scalar laws and their Born identity are redundant data: the identity on all
Borel events uniquely determines each law from the normalized operator POVM.
This avoids making a tensor-PSD proof part of a new definition body. -/
structure Scheme (d : ℕ) (X : Type*) [MeasurableSpace X] where
  observable : ∀ k, Measurements.OperatorPOVM (CopyIndex d k) X
  law : ℕ → DensityOutcome d → Measure X
  probability : ∀ k rho, IsProbabilityMeasure (law k rho)
  born : ∀ k rho B, MeasurableSet B →
    law k rho B = ENNReal.ofReal
      (effectProb ((observable k).operator B) (piKron (k+1) rho.val))

/-- PDF p.37, A.1: good, nonnegative extended rate. -/
def GoodRate {X : Type*} [TopologicalSpace X] (I : X → ℝ≥0∞) : Prop :=
  LowerSemicontinuous I ∧ (∃ x, I x ≠ ⊤) ∧
    ∀ c : ℝ, IsCompact {x | (I x : EReal) ≤ (c : EReal)}

/-- PDF pp.37-38: extended natural logarithm, including log(0)=-infinity. -/
def logMass (p : ℝ≥0∞) : EReal :=
  if p = 0 then ⊥ else if p = ⊤ then ⊤ else (Real.log p.toReal : EReal)

/-- PDF p.37, (215)-(216): 1/N log probability, with N=k+1. -/
def scaledLog (k : ℕ) (p : ℝ≥0∞) : EReal :=
  ((1 / (k+1 : ℝ) : ℝ) : EReal) * logMass p

/-- PDF p.37, A.2: closed upper and open lower bounds, with a good rate.
The infimum over an empty event is infinity. No Borel-set exact limit is asserted. -/
def HasLDP {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    (mu : ℕ → Measure X) (I : X → ℝ≥0∞) : Prop :=
  (∀ k, IsProbabilityMeasure (mu k)) ∧ GoodRate I ∧
  (∀ B : Set X, IsClosed B →
    Filter.limsup (fun k => scaledLog k (mu k B)) atTop ≤
      -(↑(⨅ x : B, I x.val) : EReal)) ∧
  (∀ B : Set X, IsOpen B →
    -(↑(⨅ x : B, I x.val) : EReal) ≤
      Filter.liminf (fun k => scaledLog k (mu k B)) atTop)

/-- PDF pp.4-5, Def.2.2. The relation `target rho x` is p(rho)=x;
using a relation also permits the spectral projection without an auxiliary choice. -/
def SchemeLDP {d : ℕ} {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    (E : Scheme d X) (target : DensityOutcome d → X → Prop) (I : DensityOutcome d → X → ℝ≥0∞) : Prop :=
  (∀ rho, HasLDP (fun k => E.law k rho) (I rho)) ∧
    ∀ rho x, I rho x = 0 ↔ target rho x

/-- PDF p.4: full estimation has target map Id. -/
def FullTarget {d : ℕ} (rho sigma : DensityOutcome d) : Prop := rho = sigma

/-- PDF p.3, (4): the spectral target is the decreasing eigenvalue vector. -/
def SpectralTarget {d : ℕ} (rho : DensityOutcome d) (x : OrderedSpectrum d) : Prop :=
  spectrumVector rho = x.val

/-- PDF p.5, Def.2.3: admissibility requires a single witnessing scheme. -/
def AdmissibleRate {d : ℕ} {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    (target : DensityOutcome d → X → Prop) (I : DensityOutcome d → X → ℝ≥0∞) : Prop :=
  ∃ E : Scheme d X, SchemeLDP E target I

/-- PDF p.5, (9): joint lower semicontinuity in both arguments. -/
def JointLSC {d : ℕ} {X : Type*} [TopologicalSpace X]
    (I : DensityOutcome d → X → ℝ≥0∞) : Prop := LowerSemicontinuous (Function.uncurry I)

/-- PDF p.5, (12): unrestricted or regular optimal rate, as an extended supremum. -/
def optimalRate {d : ℕ} {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    (target : DensityOutcome d → X → Prop) (regular : Bool) (rho : DensityOutcome d) (x : X) : ℝ≥0∞ :=
  ⨆ I : DensityOutcome d → X → ℝ≥0∞,
    ⨆ (_h : AdmissibleRate target I ∧ (regular = true → JointLSC I)), I rho x

/-- PDF p.4, (6): permutation invariance at a fixed copy count. -/
def PermutationInvariantAt {d k : ℕ}
    (E : Measurements.OperatorPOVM (CopyIndex d k) (DensityOutcome d)) : Prop :=
  ∀ (p : Equiv.Perm (Fin (k+1))) B, MeasurableSet B →
    Schur.tensorPermutation d (k+1) p * E.operator B *
      star (Schur.tensorPermutation d (k+1) p) = E.operator B

/-- PDF p.4, (7): covariance of the full-state observable at a fixed copy count. -/
def CovariantAt {d k : ℕ}
    (E : Measurements.OperatorPOVM (CopyIndex d k) (DensityOutcome d)) : Prop :=
  ∀ (U : Matrix.unitaryGroup (Fin d) ℂ) B, MeasurableSet B →
    E.operator (conjugateState U '' B) =
      piKron (k+1) (U : Matrix (Fin d) (Fin d) ℂ) * E.operator B * star (piKron (k+1) (U : Matrix (Fin d) (Fin d) ℂ))

/-- PDF p.5, (10): covariance requires a covariant witnessing scheme. -/
def CovariantAdmissible {d : ℕ} (I : DensityOutcome d → DensityOutcome d → ℝ≥0∞) : Prop :=
  ∃ E : Scheme d (DensityOutcome d), SchemeLDP E FullTarget I ∧ ∀ k, CovariantAt (E.observable k)

/-- PDF p.5, (13): supremum over rates with a covariant full-estimation witness. -/
def covariantOptimal {d : ℕ} (rho sigma : DensityOutcome d) : ℝ≥0∞ :=
  ⨆ I : DensityOutcome d → DensityOutcome d → ℝ≥0∞, ⨆ (_h : CovariantAdmissible I), I rho sigma

/-- PDF p.5, (11): simultaneous conjugation, in the same orientation. -/
def InvariantRate {d : ℕ} (I : DensityOutcome d → DensityOutcome d → ℝ≥0∞) : Prop :=
  ∀ U rho sigma, I (conjugateState U rho) (conjugateState U sigma) = I rho sigma

/-- PDF pp.8,25: weighted -log, with zero weight contributing zero even at p=0. -/
def weightedNegLog (w p : ℝ) : EReal :=
  if w = 0 then 0 else if p ≤ 0 then ⊤ else (-(w * Real.log p) : ℝ)

/-- PDF p.8, (26): the leading (k+1)-by-(k+1) principal minor. -/
def principalMinor {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (k : Fin d) : ℝ :=
  (Matrix.det (A.submatrix
    (fun i : Fin (k.val+1) => (⟨i.val, by omega⟩ : Fin d))
    (fun i : Fin (k.val+1) => (⟨i.val, by omega⟩ : Fin d)))).re

/-- PDF p.8, (26): the final coordinate is followed by zero. -/
def nextCoordinate {d : ℕ} (x : Fin d → ℝ) (k : Fin d) : ℝ :=
  if h : k.val+1 < d then x ⟨k.val+1,h⟩ else 0

/-- PDF pp.8,25, (26),(131): the formula in a specified eigenbasis of the estimate. -/
def minorFormula {d : ℕ} (rho : DensityOutcome d) (U : Matrix.unitaryGroup (Fin d) ℂ)
    (x : OrderedSpectrum d) : EReal :=
  ((∑ j, x.val j * Real.log (x.val j) : ℝ) : EReal) +
    ∑ j, weightedNegLog (x.val j - nextCoordinate x.val j)
      (principalMinor (star (U : Matrix (Fin d) (Fin d) ℂ) * rho.val * (U : Matrix (Fin d) (Fin d) ℂ)) j)

/-- PDF p.8, (26): the full rate, defined from all spectral representations.
Lemma 4.15 states basis independence and equality with the displayed formula;
its equality also rules out any clamping by toENNReal. -/
def fullRate {d : ℕ} (rho sigma : DensityOutcome d) : ℝ≥0∞ :=
  (⨅ x : OrderedSpectrum d, ⨅ U : Matrix.unitaryGroup (Fin d) ℂ,
    ⨅ (_h : sigma.val = (U : Matrix (Fin d) (Fin d) ℂ) * diagonalStateMatrix x * star (U : Matrix (Fin d) (Fin d) ℂ)),
      minorFormula rho U x).toENNReal

/-- PDF p.7, (19): the classical divergence D(x||s(rho)) with zero conventions. -/
def spectralRate {d : ℕ} (rho : DensityOutcome d) (x : OrderedSpectrum d) : ℝ≥0∞ :=
  (((∑ j, x.val j * Real.log (x.val j) : ℝ) : EReal) +
    ∑ j, weightedNegLog (x.val j) (spectrumVector rho j)).toENNReal

/-- PDF pp.6-7: actual Schur and Specht coordinate dimensions. -/
abbrev SchurCoordinateIndex {d n : ℕ} (Y : Schur.Partition d n) :=
  Fin (Module.finrank ℂ (Schur.schurModule Y))

/-- PDF pp.6-7: coordinates of the actual highest-weight vector. -/
def highestCoordinates {d n : ℕ} (Y : Schur.Partition d n) :
    EuclideanSpace ℂ (SchurCoordinateIndex Y) :=
  WithLp.toLp 2 fun i => inner ℂ (stdOrthonormalBasis ℂ (Schur.schurModule Y) i)
    (Schur.highestWeightVector Y)

/-- PDF p.6, (14): pi_Y computed on the actual Schur module, in its public basis. -/
def schurAction {d n : ℕ} (Y : Schur.Partition d n) (U : Matrix.unitaryGroup (Fin d) ℂ) :
    Matrix (SchurCoordinateIndex Y) (SchurCoordinateIndex Y) ℂ :=
  fun i j => inner ℂ (stdOrthonormalBasis ℂ (Schur.schurModule Y) i)
    (Schur.polynomialRepresentation Y (U : Matrix (Fin d) (Fin d) ℂ)
      (stdOrthonormalBasis ℂ (Schur.schurModule Y) j))

/-- PDF p.6, (14): embed Q_Y tensor I_K into the physical tensor space.
The accepted transform is Specht-first, so the Specht index is matched first. -/
def embedBlock {d n : ℕ} (Y : Schur.Partition d n)
    (Q : Matrix (SchurCoordinateIndex Y) (SchurCoordinateIndex Y) ℂ) :
    Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ :=
  (Schur.decomposition d n)ᴴ *
    (Matrix.of fun a b : Schur.DecompositionIndex d n =>
      if ha : a.1 = Y then if hb : b.1 = Y then
        if (ha ▸ a.2.1) = (hb ▸ b.2.1) then Q (ha ▸ a.2.2) (hb ▸ b.2.2) else 0
      else 0 else 0) * Schur.decomposition d n

/-- PDF pp.7-8: Borel event pullback along a matrix-valued decoder.
No arbitrary state decoder or certificate is supplied. -/
def matrixInEvent {d : ℕ} (B : Set (DensityOutcome d)) (A : Matrix (Fin d) (Fin d) ℂ) : Prop :=
  ∃ rho ∈ B, rho.val = A

/-- PDF p.7, (20): the explicit raw full-estimation POVM on Borel events.
Normalized-POVM and Born-law witnesses are conclusions of Theorem 3.2. -/
def fullEstimatorOperator {d : ℕ} (hd : 0 < d) (k : ℕ) (B : Set (DensityOutcome d)) :
    Matrix (CopyIndex d k) (CopyIndex d k) ℂ :=
  ∑ Y : Schur.Partition d (k+1),
    ∫ U : Matrix.unitaryGroup (Fin d) ℂ,
      if matrixInEvent B (Schur.estimate hd (by omega) Y U) then
        (Module.finrank ℂ (Schur.schurModule Y) : ℂ) •
          embedBlock Y (pureDensity (act (schurAction Y U) (highestCoordinates Y)))
      else 0
      ∂Schur.unitaryHaar d

/-- PDF p.7, (17): the explicit spectral estimator using physical central projectors. -/
def spectralEstimatorOperator {d : ℕ} (hd : 0 < d) (k : ℕ)
    (B : Set (OrderedSpectrum d)) : Matrix (CopyIndex d k) (CopyIndex d k) ℂ :=
  ∑ Y : Schur.Partition d (k+1),
    if ∃ x ∈ B, x.val = Schur.normalizedRows hd (by omega) Y then
      Schur.isotypicProjector Y else 0

/-- PDF p.7, (22): the preimage of a spectral event under s. -/
def spectralPreimage {d : ℕ} (B : Set (OrderedSpectrum d)) : Set (DensityOutcome d) :=
  {rho | ∃ x ∈ B, spectrumVector rho = x.val}

/-- PDF p.7: covariance for spectral estimation has trivial outcome action. -/
def SpectralCovariantAt {d k : ℕ}
    (E : Measurements.OperatorPOVM (CopyIndex d k) (OrderedSpectrum d)) : Prop :=
  ∀ (U : Matrix.unitaryGroup (Fin d) ℂ) B, MeasurableSet B →
    piKron (k+1) (U : Matrix (Fin d) (Fin d) ℂ) * E.operator B * star (piKron (k+1) (U : Matrix (Fin d) (Fin d) ℂ)) = E.operator B

/-- PDF p.5, (13), for the spectral projection. -/
def spectralCovariantOptimal {d : ℕ} (rho : DensityOutcome d) (x : OrderedSpectrum d) : ℝ≥0∞ :=
  ⨆ I : DensityOutcome d → OrderedSpectrum d → ℝ≥0∞,
    ⨆ (_h : ∃ E : Scheme d (OrderedSpectrum d), SchemeLDP E SpectralTarget I ∧
      ∀ k, SpectralCovariantAt (E.observable k)), I rho x

/-- PDF p.11, (35): the scaled negative log Laplace logLaplaceMoment. Continuous f on
compact S is bounded; under the scheme assumptions the integral is finite and positive. -/
def logLaplaceMoment {d : ℕ} (E : Scheme d (DensityOutcome d)) (k : ℕ)
    (rho : DensityOutcome d) (f : DensityOutcome d → ℝ) : ℝ :=
  -(Real.log (∫ sigma, Real.exp (-(k+1 : ℝ) * f sigma) ∂E.law k rho)) / (k+1 : ℝ)

/-- PDF p.11, (36): extended infimum; continuous f and an admissible rate make it finite. -/
def limitMomentExtended {d : ℕ} (I : DensityOutcome d → DensityOutcome d → ℝ≥0∞)
    (rho : DensityOutcome d) (f : DensityOutcome d → ℝ) : EReal :=
  ⨅ sigma, (I rho sigma : EReal) + (f sigma : EReal)

/-- PDF p.11, (36): the real-valued limiting logLaplaceMoment. The LDP hypotheses and
compactness ensure that this toReal never discards an infinite value in our theorems. -/
def limitMoment {d : ℕ} (I : DensityOutcome d → DensityOutcome d → ℝ≥0∞)
    (rho : DensityOutcome d) (f : DensityOutcome d → ℝ) : ℝ := (limitMomentExtended I rho f).toReal

/-- PDF p.15, (64): alpha_U f(sigma)=f(U sigma U*). -/
def actionTest {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℂ)
    (f : DensityOutcome d → ℝ) (sigma : DensityOutcome d) : ℝ := f (conjugateState U sigma)

/-- PDF p.17, (79): permutation average, exactly 1/N! times the sum. -/
def permutationAverageOperator {d : ℕ} (E : Scheme d (DensityOutcome d)) (k : ℕ)
    (B : Set (DensityOutcome d)) : Matrix (CopyIndex d k) (CopyIndex d k) ℂ :=
  (((k+1).factorial : ℂ)⁻¹) •
    ∑ p : Equiv.Perm (Fin (k+1)), Schur.tensorPermutation d (k+1) p *
      (E.observable k).operator B * star (Schur.tensorPermutation d (k+1) p)

/-- PDF p.17, (81): normalized Haar average of the translated observable. -/
def unitaryAverageOperator {d : ℕ} (E : Scheme d (DensityOutcome d)) (k : ℕ)
    (B : Set (DensityOutcome d)) : Matrix (CopyIndex d k) (CopyIndex d k) ℂ :=
  ∫ U : Matrix.unitaryGroup (Fin d) ℂ,
    piKron (k+1) (U : Matrix (Fin d) (Fin d) ℂ) * (E.observable k).operator (conjugateState U ⁻¹' B) *
      star (piKron (k+1) (U : Matrix (Fin d) (Fin d) ℂ)) ∂Schur.unitaryHaar d

/-- PDF p.17, (82): simultaneous inverse-conjugation orbit infimum. -/
def orbitRate {d : ℕ} (I : DensityOutcome d → DensityOutcome d → ℝ≥0∞) (rho sigma : DensityOutcome d) : ℝ≥0∞ :=
  ⨅ U : Matrix.unitaryGroup (Fin d) ℂ,
    I (conjugateState U⁻¹ rho) (conjugateState U⁻¹ sigma)

/-- PDF pp.21-23: finite positive operator measures for the non-normalized seeds. -/
structure FiniteOperatorMeasure (J X : Type*) [Fintype J] [DecidableEq J]
    [MeasurableSpace X] where
  operator : Set X → Matrix J J ℂ
  empty : operator ∅ = 0
  positive : ∀ B, MeasurableSet B → (operator B).PosSemidef
  additive : ∀ B : ℕ → Set X, (∀ i, MeasurableSet (B i)) →
    Pairwise (fun i j => Disjoint (B i) (B j)) →
    HasSum (fun i => operator (B i)) (operator (⋃ i, B i))

/-- PDF p.22, (111): event form of the single-Schur-factor orbit disintegration. -/
def seedObservable {d n : ℕ} (Y : Schur.Partition d n)
    (q : FiniteOperatorMeasure (SchurCoordinateIndex Y) (OrderedSpectrum d)) (B : Set (DensityOutcome d)) :
    Matrix (SchurCoordinateIndex Y) (SchurCoordinateIndex Y) ℂ :=
  ∫ U : Matrix.unitaryGroup (Fin d) ℂ,
    schurAction Y U *
      q.operator {x | matrixInEvent B ((U : Matrix (Fin d) (Fin d) ℂ) * diagonalStateMatrix x * star (U : Matrix (Fin d) (Fin d) ℂ))} *
      star (schurAction Y U) ∂Schur.unitaryHaar d

/-- PDF p.24, (124): the discrete seed representation of a fixed observable. -/
def discreteSeedObservable {d : ℕ} (hd : 0 < d) (k : ℕ)
    (Q : (Y : Schur.Partition d (k+1)) → Matrix (SchurCoordinateIndex Y) (SchurCoordinateIndex Y) ℂ)
    (B : Set (DensityOutcome d)) : Matrix (CopyIndex d k) (CopyIndex d k) ℂ :=
  ∑ Y : Schur.Partition d (k+1),
    ∫ U : Matrix.unitaryGroup (Fin d) ℂ,
      if matrixInEvent B (Schur.estimate hd (by omega) Y U) then
        piKron (k+1) (U : Matrix (Fin d) (Fin d) ℂ) * embedBlock Y (Q Y) * star (piKron (k+1) (U : Matrix (Fin d) (Fin d) ℂ))
      else 0 ∂Schur.unitaryHaar d

/-- PDF p.27, (142): the explicit dimension-weighted probability measures.
The branch merely avoids needing a separate proof in the definition that every
valid normalized Young shape belongs to Sigma; Lemma 4.16 asserts mass one. -/
def youngDimensionLaw {d : ℕ} (hd : 0 < d) (k : ℕ) : Measure (OrderedSpectrum d) :=
  ∑ Y : Schur.Partition d (k+1),
    ENNReal.ofReal
      (((Module.finrank ℂ (Schur.schurModule Y) : ℝ) *
        (Module.finrank ℂ (Schur.spechtSpace Y) : ℝ)) / (d : ℝ) ^ (k+1)) •
      (if h : OrderedProbability (Schur.normalizedRows hd (by omega) Y) then
        Measure.dirac ⟨Schur.normalizedRows hd (by omega) Y, h⟩ else 0)

/-- PDF p.27, (147): entropy rate at the maximally mixed input. -/
def maximallyMixedRate {d : ℕ} (x : OrderedSpectrum d) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.log d + ∑ j, x.val j * Real.log (x.val j))

/-- PDF p.9, (29): Bloch matrix with the standard Pauli orientation. -/
def blochDensityMatrix (x : Fin 3 → ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![((1+x 2)/2 : ℝ), ((x 0 : ℂ) - Complex.I * (x 1 : ℂ))/2;
    ((x 0 : ℂ) + Complex.I * (x 1 : ℂ))/2, ((1-x 2)/2 : ℝ)]

/-- PDF p.9, (29): Euclidean length of a Bloch vector. -/
def blochLength (x : Fin 3 → ℝ) : ℝ := Real.sqrt (∑ i, (x i)^2)

/-- PDF p.9, (29): extension of r cos(theta) at zero Bloch vectors.
If y=0 its value is irrelevant because its weight is zero. -/
def blochDirectionalComponent (x y : Fin 3 → ℝ) : ℝ :=
  (∑ i, x i * y i) / blochLength y

/-- PDF p.32, (183): purity means a unit-vector rank-one density matrix. -/
def PureDensityState {d : ℕ} (rho : DensityOutcome d) : Prop :=
  ∃ psi : EuclideanSpace ℂ (Fin d), ‖psi‖ = 1 ∧ rho.val = pureDensity psi

/-- PDF p.33: the symmetric subspace consists of permutation-fixed vectors. -/
def SymmetricVector {d k : ℕ} (v : EuclideanSpace ℂ (CopyIndex d k)) : Prop :=
  ∀ p : Equiv.Perm (Fin (k+1)), act (Schur.tensorPermutation d (k+1) p) v = v

/-- PDF p.33, (185)-(186): the two asymptotic requirements on a pure local test. -/
def PureTestProperties {d : ℕ} (I : DensityOutcome d → DensityOutcome d → ℝ≥0∞)
    (rho sigma : DensityOutcome d) (phi psi : EuclideanSpace ℂ (Fin d))
    (v : (k : ℕ) → EuclideanSpace ℂ (CopyIndex d k)) : Prop :=
  (∀ k, ‖v k‖ = 1 ∧ SymmetricVector (v k)) ∧
  (I rho sigma : EReal) ≤ Filter.liminf
    (fun k => -scaledLog k (ENNReal.ofReal (Complex.normSq (inner ℂ (tensorPow (k+1) phi) (v k))))) atTop ∧
  Tendsto (fun k => Complex.normSq (inner ℂ (v k) (tensorPow (k+1) psi))) atTop (nhds 1)

/-- Definition sanity: zero-weight vanishing minors contribute zero (PDF p.8). -/
example : weightedNegLog 0 0 = 0 := by simp [weightedNegLog]

/-- Definition sanity: zero event probabilities have logarithm minus infinity (PDF p.37). -/
example : logMass 0 = ⊥ := by simp [logMass]

/-- Definition sanity: a scheme gives zero mass to the empty event (PDF p.3). -/
example {d : ℕ} {X : Type*} [MeasurableSpace X] (E : Scheme d X) (k : ℕ) (rho : DensityOutcome d) :
    E.law k rho ∅ = 0 := measure_empty

/-- Definition sanity: the one-dimensional identity is a valid state (PDF p.3). -/
example : IsDensityMatrix (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
  exact ⟨Matrix.PosSemidef.one, by simp [Matrix.trace]⟩

/-- Definition sanity: identity conjugation fixes every state (PDF p.4). -/
example {d : ℕ} (rho : DensityOutcome d) : conjugateState 1 rho = rho := by
  apply Subtype.ext
  simp [conjugateState]

/-- Definition sanity: one-copy tensor coordinates have no normalization factor (PDF p.3). -/
example {d : ℕ} (psi : EuclideanSpace ℂ (Fin d)) (x : Fin 1 → Fin d) :
    tensorPow 1 psi x = psi (x 0) := by simp [tensorPow]

/-- Definition sanity: a zero continuous test has logarithmic moment zero (PDF p.11). -/
example {d : ℕ} (E : Scheme d (DensityOutcome d)) (k : ℕ) (rho : DensityOutcome d) :
    logLaplaceMoment E k rho (fun _ => 0) = 0 := by
  letI : IsProbabilityMeasure (E.law k rho) := E.probability k rho
  simp [logLaplaceMoment]

/-- Definition sanity: the zero Bloch vector gives I/2 (PDF p.9). -/
example : blochDensityMatrix (fun _ => 0) = (1/2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [blochDensityMatrix, Matrix.smul_apply, Matrix.one_apply]

/-- PDF p.4, Def.2.1: weak consistency for full estimation. All continuous real
test functions are bounded because the finite-dimensional state space is compact. -/
def Consistent {d : ℕ} (E : Scheme d (DensityOutcome d)) : Prop :=
  ∀ rho (f : DensityOutcome d → ℝ), Continuous f →
    Tendsto (fun k => ∫ sigma, f sigma ∂E.law k rho) atTop (nhds (f rho))

end QAlgorithms.Papers.Independent.Extend50.P41


