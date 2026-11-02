-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P54
-- name    : QAlgorithms_Papers_Independent_Intakethird100_P54
-- status  : Definition
-- author  : @Gohan
-- created : 2026-11-01T06:01:03.715022+00:00
-- url     : https://prove2.me/theorems/a6d8a224-bd9e-42d6-9dbc-537e0bd8b9aa
-- title:
--   Definitions for Discriminating quantum-optical beam-splitter channels with number-diagonal signal states: Applications to quantum reading and target detection
-- statement:
--   The objects the formalized statements of *Discriminating quantum-optical beam-splitter channels with number-diagonal signal states: Applications to quantum reading and target detection* (arXiv:1105.4063) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `opticalKernel`: Fock coefficients of an operator; validity is supplied by its construction.
--   - `fockVector`: A full Fock vector from coefficients. Off l² only, the total extension is zero. The stated construction clauses rule this branch out for every physical input.
--   - `Splitter`: A single-mode vacuum-environment splitter, PDF p.1, (1).
--   - `Splitter.r`: Nonnegative field reflection magnitude.
--   - `Splitter.t`: Nonnegative field transmission magnitude.
--   - `Splitter.field`: Complex returned field coefficient, PDF p.1.
--   - `Channels`: Two candidate splitters; the prior is built into the error definition.
--   - `ValidSplitters`: The paper's ordering and distinctness assumptions, PDF pp.1–2.
--   - `Reading`: Section IV's common phase removed by the same known unitary.
--   - `splitterOverlap`: The common real overlap coefficient of (17),(49).
--   - `photons`: Total signal photon number, with no idler energy charged, PDF p.4, (18).
--   - `lossAmplitude`: Vacuum-environment binomial amplitude (12). The phase multiplies the entire input occupation, not just the returned photon count. The guard precedes subtraction.
--   - `sectorCoefficients`: Loss-sector coefficients (11),(25); idlers are retained without change.
--   - `lossSector`: The unnormalized retained state in a loss sector, PDF p.4, (25).
--   - `returned`: Actual returned density after tracing inaccessible independent vacuum modes, PDF pp.1,3–5, (2),(11),(32). Every series is over full Fock labels.
--   - `signalLaw`: Reduced signal number law, PDF p.4, before (17).
--   - `totalLaw`: Total signal photon law (18), distinct from the multimode occupation law.
--   - `HasSignalEnergy`: Finite mean SIGNAL energy, PDF pp.6–7. Summability rules out totalized tsum.
--   - `IsNDS`: Source definition of NDS: the signal marginal is number diagonal, PDF p.4. For pure probes this is equivalent to orthogonal occupied idler Schmidt vectors.
--   - `purificationMarginal`: Reduced density of a normalized countable-ancilla purification.
--   - `PurifiesOpticalKernel`: Purification as actual norm-one amplitudes, not an assumed fidelity value.
--   - `squaredOpticalFidelity`: Squared Uhlmann fidelity (4),(19), as the supremum over all purifications. For physical densities here this set is nonempty and bounded in [0,1]; the countable ancilla suffices because the optical Hilbert spaces are separable.
--   - `Resolution`: A spectral resolution of a normalized positive trace-class density. Only positive-weight vectors are required to be orthonormal. The kernel equality is part of a spectral representation, not an assumption on any source theorem.
--   - `IsOpticalEffect`: A binary measurement effect is a bounded complex-linear positive contraction. E is the decision-zero effect; 1-E is the decision-one effect, PDF pp.3,5.
--   - `opticalBayesRisk`: Binary Bayesian error for actual spectral states and an effect; arbitrary joint signal-idler effects are admitted, including non-projective measurements.
--   - `bayesError`: Operational minimum Bayesian error. For normalized physical densities and priors this is a nonempty infimum of numbers in [0,1]; spectral representations do not constrain the allowed receiver. Equal priors are used except in (42).
--   - `opticalError`: Equal-prior minimum average error, PDF p.3, (5).
--   - `supportWeightPower`: Support spectral power: the zero eigenspace contributes zero even at t=0. This implements the support-projection convention on PDF p.6.
--   - `chernoffAt`: Tr(rho^s sigma^(1-s)), defined independently from NDS formulas (45). For densities and 0<=s<=1 every spectral representation gives the same absolutely convergent nonnegative double series, in [0,1]. Hence this supremum is nonempty and bounded; it does not optimize the probe or the receiver.
--   - `opticalChernoff`: Chernoff coefficient WITHOUT prior factor, including both support endpoints (9).
--   - `outputFidelity`: Pure-input output fidelity, for the actual channels.
--   - `outputError`: Pure-input operational output error.
--   - `outputChernoffAt`: Pure-input Chernoff-type coefficient.
--   - `outputChernoff`: Pure-input optimized Chernoff coefficient.
--   - `purificationOverlapTerm`: Complex overlap series in the TOTAL photon law, PDF p.4, (17).
--   - `purificationOverlap`: Squared overlap (17); the absolute value encloses the WHOLE complex sum.
--   - `lowerError`: Fidelity-based LOWER error envelope (6),(20),(53).
--   - `lossProbability`: Loss-sector probability (27) directly from its actual vector.
--   - `lossOverlap`: Loss-sector overlap (30); the first argument is conjugated.
--   - `lossOverlapTerm`: Explicit complex binomial summand (31), with componentwise loss guard.
--   - `lossBlock`: The at-most-two-dimensional block H_k of (33)–(35).
--   - `lossBlockDifference`: Weighted block difference; equal priors use weights 1,1 for rho0-rho1.
--   - `BlockReceiver`: A complete block spectral receiver, (40)–(42). E is the zero decision. It is projective, preserves every loss block, and decides the positive/negative spectra correctly. Zero eigenvectors may be assigned either decision.
--   - `sectorRisk`: Risk of a concrete effect, directly on unnormalized output loss vectors.
--   - `ndsChernoffTerm`: Term of (45), explicitly omitting either zero-probability sector.
--   - `opticalPureKernel`: Rank-one full-Fock density.
--   - `fock`: A Fock signal with no retained idlers; the empty idler occupation has one value.
--   - `productOpticalProbe`: Independent product probes with arbitrary finite idler count J_m per signal, PDF p.6, (46)–(47). The idler register is grouped, without tracing any factors.
--   - `opticalCopies`: Independent copies of a joint multimode probe, with all signals grouped.
--   - `coherentOpticalProbe`: Product coherent probe; arbitrary classical idler amplitudes are retained.
--   - `coherentEnergy`: Total signal energy of a product coherent state.
--   - `tmsvCoefficients`: Multimode EPR coefficients (73), with N the per-pair SIGNAL energy. Natural powers preserve the vacuum convention 0^0=1.
--   - `tmsvProbe`: Product of M identical EPR pairs, with no photon cutoff.
--   - `countLaw`: Product law of observed RETURNED counts, PDF p.8, (62) with j=N-k.
--   - `totalCountLaw`: Binomial law of the total returned photon count.
--   - `countingError`: Equal-prior overlap of the total count distributions, not an assumed quantum optimum.
--   - `CountsAs`: Photon counting followed by d(j), where true means decision one. E is the zero-decision effect and acts trivially on every retained idler.
--   - `countThreshold`: Interior logarithmic threshold (65); endpoint rules are separate theorems.
--   - `fockCoefficient`: One-photon classical Chernoff coefficient, PDF p.8, (66).
--   - `fockOptimizer`: Explicit optimizer (67); theorem hypotheses restrict it to strict interior channels.
--   - `numberExponent`: Per-photon number-state exponent, with natural logarithm, (66).
--   - `coherentExponent`: Per-photon coherent exponent (68).
--   - `exponentGain`: Exponent gain (69); no claim that it is large in every regime.
--   - `eprAlpha`: Parameters (78)–(81); beta is used only when R1<1.
--   - `eprBeta`: Parameter beta in (79).
--   - `eprC`: Parameter C in (80).
--   - `eprD`: Parameter D in (81).
--   - `eprDerivativeSign`: Equivalent logarithmic case test (84)–(85): no exponent/product ambiguity.
--   - `eprOptimizer`: Optimizer (85)–(86). N=0 and ideal memory are handled outside this definition.
--   - `classicalReturned`: Classical positive-P probes include arbitrary probability measures and Dirac masses. Signal and idler amplitudes may be classically correlated, (3), pp.2,8.
--   - `vacuumEfficiency`: An additional uniform independent vacuum attenuator, PDF p.12, IV.E.2.
--   - `efficiencyScaled`: A uniform receiver efficiency multiplies energy reflectance. Eta=0 is allowed and makes the two effective returned channels identical.
--   - `attenuate`: Vacuum attenuator on a full joint operator kernel, retaining every idler.
--   - `weightedTraceNorm`: Dual trace norm of a weighted Hermitian difference, used in (42). The supremum ranges over ALL bounded self-adjoint contractions. Spectral resolutions merely evaluate traces of the actual two states.
--   - `kernelProduct`: Composition of full Fock operator kernels on the physical trace-class arguments.
--   - `targetLower`: Target-detection universal envelope (59), with fixed real signal energy N.
--   - `targetCoherent`: Coherent target-detection error envelope (60).
-- source:
--   Discriminating quantum-optical beam-splitter channels with number-diagonal signal states: Applications to quantum reading and target detection, arXiv:1105.4063v3, https://arxiv.org/abs/1105.4063v3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_RealLabelRegisters
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P47
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P39

/-!
Statements from R. Nair, arXiv:1105.4063v3. PDF pages are cited throughout.
The optical space is full l² of occupation strings, with retained idlers first.
The accepted Hilbert, occupation labels and coherent coefficients are imported.
The remaining optical definitions below have complete bodies; their domains differ
from accepted declarations sharing their former short names. Only source results use sorry.
Fidelity is squared; Q excludes the equal-prior factor 1/2. Spectral zero powers
are support projections. Compilation is delegated to the batch handoff.
-/

noncomputable section

open scoped BigOperators ComplexConjugate
open MeasureTheory Filter

namespace QAlgorithms.Papers.Independent.Intakethird100.P54

open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open QAlgorithms.Papers.Independent.Dependency50.P39 (coherentCoefficient)

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

/-- Fock coefficients of an operator; validity is supplied by its construction. -/
abbrev opticalKernel (X : Type) := X → X → ℂ

/-- A full Fock vector from coefficients. Off l² only, the total extension is zero.
The stated construction clauses rule this branch out for every physical input. -/
def fockVector {X : Type} (a : X → ℂ) : Hilbert X :=
  if h : Memℓp a 2 then ⟨a, h⟩ else 0

/-- A single-mode vacuum-environment splitter, PDF p.1, (1). -/
structure Splitter where
  reflectance : ℝ
  phase : ℝ
  nonnegative : 0 ≤ reflectance
  atMostOne : reflectance ≤ 1

/-- Nonnegative field reflection magnitude. -/
def Splitter.r (a : Splitter) : ℝ := Real.sqrt a.reflectance

/-- Nonnegative field transmission magnitude. -/
def Splitter.t (a : Splitter) : ℝ := Real.sqrt (1 - a.reflectance)

/-- Complex returned field coefficient, PDF p.1. -/
def Splitter.field (a : Splitter) : ℂ :=
  (a.r : ℂ) * Complex.exp (Complex.I * (a.phase : ℂ))

/-- Two candidate splitters; the prior is built into the error definition. -/
abbrev Channels := Bool → Splitter

/-- The paper's ordering and distinctness assumptions, PDF pp.1–2. -/
def ValidSplitters (c : Channels) : Prop :=
  (c false).reflectance ≤ (c true).reflectance ∧
    (c false).field ≠ (c true).field

/-- Section IV's common phase removed by the same known unitary. -/
def Reading (c : Channels) : Prop :=
  (c false).phase = 0 ∧ (c true).phase = 0

/-- The common real overlap coefficient of (17),(49). -/
def splitterOverlap (c : Channels) : ℝ :=
  (c false).r * (c true).r + (c false).t * (c true).t

/-- Total signal photon number, with no idler energy charged, PDF p.4, (18). -/
def photons {M : ℕ} (n : Occupation (Fin M)) : ℕ := ∑ m, n m

/-- Vacuum-environment binomial amplitude (12). The phase multiplies the entire
input occupation, not just the returned photon count. The guard precedes subtraction. -/
def lossAmplitude {M : ℕ} (a : Splitter) (n k : Occupation (Fin M)) : ℂ :=
  if ∀ m, k m ≤ n m then
    ∏ m, (Real.sqrt (Nat.choose (n m) (k m) : ℝ) : ℂ) *
      Complex.exp (Complex.I * (n m : ℂ) * (a.phase : ℂ)) *
      (a.r : ℂ) ^ (n m - k m) * (a.t : ℂ) ^ k m
  else 0

/-- Loss-sector coefficients (11),(25); idlers are retained without change. -/
def sectorCoefficients {I : Type} {M : ℕ}
    (a : Splitter) (psi : Hilbert (I × Occupation (Fin M)))
    (k : Occupation (Fin M)) (x : I × Occupation (Fin M)) : ℂ :=
  psi (x.1, x.2 + k) * lossAmplitude a (x.2 + k) k

/-- The unnormalized retained state in a loss sector, PDF p.4, (25). -/
def lossSector {I : Type} {M : ℕ} (a : Splitter)
    (psi : Hilbert (I × Occupation (Fin M))) (k : Occupation (Fin M)) :
    Hilbert (I × Occupation (Fin M)) := fockVector (sectorCoefficients a psi k)

/-- Actual returned density after tracing inaccessible independent vacuum modes,
PDF pp.1,3–5, (2),(11),(32). Every series is over full Fock labels. -/
def returned {I : Type} {M : ℕ} (a : Splitter)
    (psi : Hilbert (I × Occupation (Fin M))) : opticalKernel (I × Occupation (Fin M)) :=
  fun x y => ∑' k : Occupation (Fin M),
    sectorCoefficients a psi k x * star (sectorCoefficients a psi k y)

/-- Reduced signal number law, PDF p.4, before (17). -/
def signalLaw {I : Type} {M : ℕ} (psi : Hilbert (I × Occupation (Fin M)))
    (n : Occupation (Fin M)) : ℝ := ∑' i : I, Complex.normSq (psi (i, n))

/-- Total signal photon law (18), distinct from the multimode occupation law. -/
def totalLaw {I : Type} {M : ℕ} (psi : Hilbert (I × Occupation (Fin M)))
    (n : ℕ) : ℝ :=
  ∑' q : Occupation (Fin M), if photons q = n then signalLaw psi q else 0

/-- Finite mean SIGNAL energy, PDF pp.6–7. Summability rules out totalized tsum. -/
def HasSignalEnergy {I : Type} {M : ℕ} (psi : Hilbert (I × Occupation (Fin M))) (N : ℝ) : Prop :=
  0 ≤ N ∧ Summable (fun n : ℕ => (n : ℝ) * totalLaw psi n) ∧
    (∑' n : ℕ, (n : ℝ) * totalLaw psi n) = N

/-- Source definition of NDS: the signal marginal is number diagonal, PDF p.4.
For pure probes this is equivalent to orthogonal occupied idler Schmidt vectors. -/
def IsNDS {I : Type} {M : ℕ} (psi : Hilbert (I × Occupation (Fin M))) : Prop :=
  ∀ n q : Occupation (Fin M), n ≠ q →
    (∑' i : I, psi (i, n) * star (psi (i, q))) = 0

/-- Reduced density of a normalized countable-ancilla purification. -/
def purificationMarginal {X : Type} (z : Hilbert (X × ℕ)) : opticalKernel X :=
  fun x y => ∑' e : ℕ, z (x, e) * star (z (y, e))

/-- Purification as actual norm-one amplitudes, not an assumed fidelity value. -/
def PurifiesOpticalKernel {X : Type} (rho : opticalKernel X) (z : Hilbert (X × ℕ)) : Prop :=
  ‖z‖ = 1 ∧ purificationMarginal z = rho

/-- Squared Uhlmann fidelity (4),(19), as the supremum over all purifications.
For physical densities here this set is nonempty and bounded in [0,1]; the
countable ancilla suffices because the optical Hilbert spaces are separable. -/
def squaredOpticalFidelity {X : Type} (rho sigma : opticalKernel X) : ℝ :=
  sSup {v : ℝ | ∃ z w : Hilbert (X × ℕ),
    PurifiesOpticalKernel rho z ∧ PurifiesOpticalKernel sigma w ∧
      v = Complex.normSq (inner ℂ z w)}

/-- A spectral resolution of a normalized positive trace-class density. Only
positive-weight vectors are required to be orthonormal. The kernel equality is
part of a spectral representation, not an assumption on any source theorem. -/
structure Resolution {X : Type} (rho : opticalKernel X) where
  weight : ℕ → ℝ
  ket : ℕ → Hilbert X
  nonnegative : ∀ n, 0 ≤ weight n
  summable : Summable weight
  mass : ∑' n, weight n = 1
  normalized : ∀ n, 0 < weight n → ‖ket n‖ = 1
  orthogonal : ∀ n m, n ≠ m → 0 < weight n → 0 < weight m →
    inner ℂ (ket n) (ket m) = 0
  represents : ∀ x y, rho x y =
    ∑' n : ℕ, (weight n : ℂ) * ket n x * star (ket n y)

/-- A binary measurement effect is a bounded complex-linear positive contraction.
E is the decision-zero effect; 1-E is the decision-one effect, PDF pp.3,5. -/
def IsOpticalEffect {X : Type} (E : Hilbert X →L[ℂ] Hilbert X) : Prop :=
  (∀ u v, inner ℂ u (E v) = star (inner ℂ v (E u))) ∧
    ∀ v, 0 ≤ (inner ℂ v (E v)).re ∧ (inner ℂ v (E v)).re ≤ ‖v‖ ^ 2

/-- Binary Bayesian error for actual spectral states and an effect; arbitrary
joint signal-idler effects are admitted, including non-projective measurements. -/
def opticalBayesRisk {X : Type} {rho sigma : opticalKernel X}
    (A : Resolution rho) (B : Resolution sigma)
    (E : Hilbert X →L[ℂ] Hilbert X) (pi0 pi1 : ℝ) : ℝ :=
  pi0 * (∑' n : ℕ, A.weight n * (1 - (inner ℂ (A.ket n) (E (A.ket n))).re)) +
  pi1 * (∑' n : ℕ, B.weight n * (inner ℂ (B.ket n) (E (B.ket n))).re)

/-- Operational minimum Bayesian error. For normalized physical densities and
priors this is a nonempty infimum of numbers in [0,1]; spectral representations
do not constrain the allowed receiver. Equal priors are used except in (42). -/
def bayesError {X : Type} (rho sigma : opticalKernel X) (pi0 pi1 : ℝ) : ℝ :=
  sInf {v : ℝ | ∃ (A : Resolution rho) (B : Resolution sigma)
    (E : Hilbert X →L[ℂ] Hilbert X), IsOpticalEffect E ∧ v = opticalBayesRisk A B E pi0 pi1}

/-- Equal-prior minimum average error, PDF p.3, (5). -/
def opticalError {X : Type} (rho sigma : opticalKernel X) : ℝ := bayesError rho sigma (1/2) (1/2)

/-- Support spectral power: the zero eigenspace contributes zero even at t=0.
This implements the support-projection convention on PDF p.6. -/
def supportWeightPower (p t : ℝ) : ℝ := if p = 0 then 0 else Real.rpow p t

/-- Tr(rho^s sigma^(1-s)), defined independently from NDS formulas (45).
For densities and 0<=s<=1 every spectral representation gives the same absolutely
convergent nonnegative double series, in [0,1]. Hence this supremum is nonempty
and bounded; it does not optimize the probe or the receiver. -/
def chernoffAt {X : Type} (rho sigma : opticalKernel X) (s : ℝ) : ℝ :=
  sSup {v : ℝ | ∃ (A : Resolution rho) (B : Resolution sigma),
    v = ∑' nm : ℕ × ℕ,
      supportWeightPower (A.weight nm.1) s * supportWeightPower (B.weight nm.2) (1-s) *
        Complex.normSq (inner ℂ (A.ket nm.1) (B.ket nm.2))}

/-- Chernoff coefficient WITHOUT prior factor, including both support endpoints (9). -/
def opticalChernoff {X : Type} (rho sigma : opticalKernel X) : ℝ :=
  sInf {v : ℝ | ∃ s ∈ Set.Icc (0 : ℝ) 1, v = chernoffAt rho sigma s}

/-- Pure-input output fidelity, for the actual channels. -/
def outputFidelity {I : Type} {M : ℕ} (c : Channels)
    (psi : Hilbert (I × Occupation (Fin M))) : ℝ :=
  squaredOpticalFidelity (returned (c false) psi) (returned (c true) psi)

/-- Pure-input operational output error. -/
def outputError {I : Type} {M : ℕ} (c : Channels)
    (psi : Hilbert (I × Occupation (Fin M))) : ℝ :=
  opticalError (returned (c false) psi) (returned (c true) psi)

/-- Pure-input Chernoff-type coefficient. -/
def outputChernoffAt {I : Type} {M : ℕ} (c : Channels)
    (psi : Hilbert (I × Occupation (Fin M))) (s : ℝ) : ℝ :=
  chernoffAt (returned (c false) psi) (returned (c true) psi) s

/-- Pure-input optimized Chernoff coefficient. -/
def outputChernoff {I : Type} {M : ℕ} (c : Channels)
    (psi : Hilbert (I × Occupation (Fin M))) : ℝ :=
  opticalChernoff (returned (c false) psi) (returned (c true) psi)

/-- Complex overlap series in the TOTAL photon law, PDF p.4, (17). -/
def purificationOverlapTerm {I : Type} {M : ℕ} (c : Channels)
    (psi : Hilbert (I × Occupation (Fin M))) (n : ℕ) : ℂ :=
  (totalLaw psi n : ℂ) *
    Complex.exp (Complex.I * (n : ℂ) * ((c true).phase - (c false).phase : ℝ)) *
    (splitterOverlap c : ℂ) ^ n

/-- Squared overlap (17); the absolute value encloses the WHOLE complex sum. -/
def purificationOverlap {I : Type} {M : ℕ} (c : Channels)
    (psi : Hilbert (I × Occupation (Fin M))) : ℝ :=
  Complex.normSq (∑' n : ℕ, purificationOverlapTerm c psi n)

/-- Fidelity-based LOWER error envelope (6),(20),(53). -/
def lowerError (F : ℝ) : ℝ := (1 - Real.sqrt (1-F)) / 2

/-- Loss-sector probability (27) directly from its actual vector. -/
def lossProbability {I : Type} {M : ℕ} (c : Channels)
    (psi : Hilbert (I × Occupation (Fin M))) (b : Bool) (k : Occupation (Fin M)) : ℝ :=
  ‖lossSector (c b) psi k‖ ^ 2

/-- Loss-sector overlap (30); the first argument is conjugated. -/
def lossOverlap {I : Type} {M : ℕ} (c : Channels)
    (psi : Hilbert (I × Occupation (Fin M))) (k : Occupation (Fin M)) : ℂ :=
  inner ℂ (lossSector (c false) psi k) (lossSector (c true) psi k)

/-- Explicit complex binomial summand (31), with componentwise loss guard. -/
def lossOverlapTerm {I : Type} {M : ℕ} (c : Channels)
    (psi : Hilbert (I × Occupation (Fin M))) (k n : Occupation (Fin M)) : ℂ :=
  (signalLaw psi n : ℂ) * star (lossAmplitude (c false) n k) * lossAmplitude (c true) n k

/-- The at-most-two-dimensional block H_k of (33)–(35). -/
def lossBlock {I : Type} {M : ℕ} (c : Channels)
    (psi : Hilbert (I × Occupation (Fin M))) (k : Occupation (Fin M)) :
    Submodule ℂ (Hilbert (I × Occupation (Fin M))) :=
  Submodule.span ℂ {lossSector (c false) psi k, lossSector (c true) psi k}

/-- Weighted block difference; equal priors use weights 1,1 for rho0-rho1. -/
def lossBlockDifference {I : Type} {M : ℕ} (c : Channels)
    (psi : Hilbert (I × Occupation (Fin M))) (k : Occupation (Fin M)) (w0 w1 : ℝ)
    (v : Hilbert (I × Occupation (Fin M))) : Hilbert (I × Occupation (Fin M)) :=
  ((w0 : ℂ) * inner ℂ (lossSector (c false) psi k) v) • lossSector (c false) psi k -
  ((w1 : ℂ) * inner ℂ (lossSector (c true) psi k) v) • lossSector (c true) psi k

/-- A complete block spectral receiver, (40)–(42). E is the zero decision.
It is projective, preserves every loss block, and decides the positive/negative
spectra correctly. Zero eigenvectors may be assigned either decision. -/
def BlockReceiver {I : Type} {M : ℕ} (c : Channels)
    (psi : Hilbert (I × Occupation (Fin M))) (w0 w1 : ℝ)
    (E : Hilbert (I × Occupation (Fin M)) →L[ℂ] Hilbert (I × Occupation (Fin M))) : Prop :=
  IsOpticalEffect E ∧ E.comp E = E ∧
    (∀ k v, v ∈ lossBlock c psi k → E v ∈ lossBlock c psi k) ∧
    (∀ k v (a : ℝ), v ∈ lossBlock c psi k →
      lossBlockDifference c psi k w0 w1 v = (a : ℂ) • v →
        (0 < a → E v = v) ∧ (a < 0 → E v = 0))

/-- Risk of a concrete effect, directly on unnormalized output loss vectors. -/
def sectorRisk {I : Type} {M : ℕ} (c : Channels)
    (psi : Hilbert (I × Occupation (Fin M)))
    (E : Hilbert (I × Occupation (Fin M)) →L[ℂ] Hilbert (I × Occupation (Fin M)))
    (pi0 pi1 : ℝ) : ℝ :=
  pi0 * (∑' k : Occupation (Fin M), (lossProbability c psi false k -
    (inner ℂ (lossSector (c false) psi k) (E (lossSector (c false) psi k))).re)) +
  pi1 * (∑' k, (inner ℂ (lossSector (c true) psi k) (E (lossSector (c true) psi k))).re)

/-- Term of (45), explicitly omitting either zero-probability sector. -/
def ndsChernoffTerm {I : Type} {M : ℕ} (c : Channels)
    (psi : Hilbert (I × Occupation (Fin M))) (s : ℝ) (k : Occupation (Fin M)) : ℝ :=
  if lossProbability c psi false k = 0 ∨ lossProbability c psi true k = 0 then 0
  else Real.rpow (lossProbability c psi false k) (s-1) *
    Real.rpow (lossProbability c psi true k) (-s) * Complex.normSq (lossOverlap c psi k)

/-- Rank-one full-Fock density. -/
def opticalPureKernel {X : Type} (psi : Hilbert X) : opticalKernel X :=
  fun x y => psi x * star (psi y)

/-- A Fock signal with no retained idlers; the empty idler occupation has one value. -/
def fock {M : ℕ} (N : Occupation (Fin M)) : Hilbert (Occupation (Fin 0) × Occupation (Fin M)) :=
  lp.single 2 (0, N) 1

/-- Independent product probes with arbitrary finite idler count J_m per signal,
PDF p.6, (46)–(47). The idler register is grouped, without tracing any factors. -/
def productOpticalProbe {M : ℕ} (J : Fin M → ℕ)
    (psi : ∀ m, Hilbert (Occupation (Fin (J m)) × Occupation (Fin 1))) :
    Hilbert ((∀ m, Occupation (Fin (J m))) × Occupation (Fin M)) :=
  fockVector (fun x => ∏ m, psi m (x.1 m, fun _ => x.2 m))

/-- Independent copies of a joint multimode probe, with all signals grouped. -/
def opticalCopies {J M : ℕ} (psi : Hilbert (Occupation (Fin J) × Occupation (Fin M))) (L : ℕ) :
    Hilbert ((Fin L → Occupation (Fin J)) × Occupation (Fin (L*M))) :=
  fockVector (fun x => ∏ l : Fin L,
    psi (x.1 l, fun m : Fin M => x.2 ⟨l.val*M+m.val, by
      calc
        l.val*M+m.val < l.val*M+M := Nat.add_lt_add_left m.isLt _
        _ = (l.val+1)*M := (Nat.succ_mul _ _).symm
        _ ≤ L*M := Nat.mul_le_mul_right M (Nat.succ_le_of_lt l.isLt)⟩))

/-- Product coherent probe; arbitrary classical idler amplitudes are retained. -/
def coherentOpticalProbe {J M : ℕ} (beta : Fin J → ℂ) (alpha : Fin M → ℂ) :
    Hilbert (Occupation (Fin J) × Occupation (Fin M)) :=
  fockVector (fun x => (∏ j, coherentCoefficient (beta j) (x.1 j)) *
    ∏ m, coherentCoefficient (alpha m) (x.2 m))

/-- Total signal energy of a product coherent state. -/
def coherentEnergy {M : ℕ} (alpha : Fin M → ℂ) : ℝ :=
  ∑ m, Complex.normSq (alpha m)

/-- Multimode EPR coefficients (73), with N the per-pair SIGNAL energy.
Natural powers preserve the vacuum convention 0^0=1. -/
def tmsvCoefficients (M : ℕ) (N : ℝ) (x : Occupation (Fin M) × Occupation (Fin M)) : ℂ :=
  if x.1 = x.2 then
    ∏ m, ((Real.sqrt (1/(N+1)) : ℝ) : ℂ) *
      ((Real.sqrt (N/(N+1)) : ℝ) : ℂ) ^ x.2 m
  else 0

/-- Product of M identical EPR pairs, with no photon cutoff. -/
def tmsvProbe (M : ℕ) (N : ℝ) : Hilbert (Occupation (Fin M) × Occupation (Fin M)) :=
  fockVector (tmsvCoefficients M N)

/-- Product law of observed RETURNED counts, PDF p.8, (62) with j=N-k. -/
def countLaw {M : ℕ} (a : Splitter) (N j : Occupation (Fin M)) : ℝ :=
  if ∀ m, j m ≤ N m then
    ∏ m, (Nat.choose (N m) (j m) : ℝ) *
      a.reflectance ^ j m * (1-a.reflectance) ^ (N m-j m)
  else 0

/-- Binomial law of the total returned photon count. -/
def totalCountLaw (a : Splitter) (K j : ℕ) : ℝ :=
  if j ≤ K then (Nat.choose K j : ℝ) * a.reflectance ^ j *
    (1-a.reflectance) ^ (K-j) else 0

/-- Equal-prior overlap of the total count distributions, not an assumed quantum optimum. -/
def countingError (c : Channels) (K : ℕ) : ℝ :=
  (∑ j ∈ Finset.range (K+1),
    min (totalCountLaw (c false) K j) (totalCountLaw (c true) K j)) / 2

/-- Photon counting followed by d(j), where true means decision one.
E is the zero-decision effect and acts trivially on every retained idler. -/
def CountsAs {I : Type} {M : ℕ}
    (E : Hilbert (I × Occupation (Fin M)) →L[ℂ] Hilbert (I × Occupation (Fin M)))
    (d : Occupation (Fin M) → Bool) : Prop :=
  ∀ v x, (E v) x = if d x.2 then 0 else v x

/-- Interior logarithmic threshold (65); endpoint rules are separate theorems. -/
def countThreshold (c : Channels) (K : ℕ) : ℝ :=
  (K : ℝ) * Real.log ((1-(c false).reflectance)/(1-(c true).reflectance)) /
    Real.log ((c true).reflectance*(1-(c false).reflectance) /
      ((c false).reflectance*(1-(c true).reflectance)))

/-- One-photon classical Chernoff coefficient, PDF p.8, (66). -/
def fockCoefficient (c : Channels) (s : ℝ) : ℝ :=
  Real.rpow (c false).reflectance s * Real.rpow (c true).reflectance (1-s) +
  Real.rpow (1-(c false).reflectance) s * Real.rpow (1-(c true).reflectance) (1-s)

/-- Explicit optimizer (67); theorem hypotheses restrict it to strict interior channels. -/
def fockOptimizer (c : Channels) : ℝ :=
  Real.log (-(c true).reflectance * Real.log ((c false).reflectance/(c true).reflectance) /
    ((1-(c true).reflectance) * Real.log ((1-(c false).reflectance)/(1-(c true).reflectance)))) /
  Real.log ((1-(c false).reflectance)*(c true).reflectance /
    ((1-(c true).reflectance)*(c false).reflectance))

/-- Per-photon number-state exponent, with natural logarithm, (66). -/
def numberExponent (c : Channels) : ℝ := -Real.log (fockCoefficient c (fockOptimizer c))

/-- Per-photon coherent exponent (68). -/
def coherentExponent (c : Channels) : ℝ := ((c true).r-(c false).r)^2

/-- Exponent gain (69); no claim that it is large in every regime. -/
def exponentGain (c : Channels) : ℝ := numberExponent c / coherentExponent c

/-- Parameters (78)–(81); beta is used only when R1<1. -/
def eprAlpha (c : Channels) (N : ℝ) : ℝ :=
  ((1-(c false).reflectance)*N+1) / ((1-(c true).reflectance)*N+1)

/-- Parameter beta in (79). -/
def eprBeta (c : Channels) : ℝ := (1-(c false).reflectance)/(1-(c true).reflectance)

/-- Parameter C in (80). -/
def eprC (c : Channels) (N : ℝ) : ℝ :=
  ((1-(c false).r*(c true).r)*N+1)^2 / ((1-(c false).reflectance)*N+1)

/-- Parameter D in (81). -/
def eprD (c : Channels) (N : ℝ) : ℝ := (1-(c true).reflectance)*N

/-- Equivalent logarithmic case test (84)–(85): no exponent/product ambiguity. -/
def eprDerivativeSign (c : Channels) (N : ℝ) : ℝ :=
  eprD c N * Real.log (eprBeta c) - eprC c N * Real.log (eprAlpha c N)

/-- Optimizer (85)–(86). N=0 and ideal memory are handled outside this definition. -/
def eprOptimizer (c : Channels) (N : ℝ) : ℝ :=
  if 0 ≤ eprDerivativeSign c N then 0 else
    min 1 (Real.log (eprC c N * Real.log (eprAlpha c N) /
      (eprD c N * Real.log (eprBeta c))) /
        Real.log (eprBeta c / eprAlpha c N))

/-- Classical positive-P probes include arbitrary probability measures and Dirac
masses. Signal and idler amplitudes may be classically correlated, (3), pp.2,8. -/
def classicalReturned {J M : ℕ} (a : Splitter)
    (nu : Measure ((Fin J → ℂ) × (Fin M → ℂ))) :
    opticalKernel (Occupation (Fin J) × Occupation (Fin M)) :=
  fun x y => ∫ alpha,
    opticalPureKernel (coherentOpticalProbe alpha.1 (fun m => a.field * alpha.2 m)) x y ∂nu

/-- An additional uniform independent vacuum attenuator, PDF p.12, IV.E.2. -/
def vacuumEfficiency (eta : ℝ) (h0 : 0 ≤ eta) (h1 : eta ≤ 1) : Splitter :=
  ⟨eta, 0, h0, h1⟩

/-- A uniform receiver efficiency multiplies energy reflectance. Eta=0 is allowed
and makes the two effective returned channels identical. -/
def efficiencyScaled (a : Splitter) (eta : ℝ) (h0 : 0 ≤ eta) (h1 : eta ≤ 1) : Splitter :=
  ⟨eta*a.reflectance, a.phase, mul_nonneg h0 a.nonnegative,
    by
      calc
        eta*a.reflectance ≤ 1*a.reflectance := mul_le_mul_of_nonneg_right h1 a.nonnegative
        _ = a.reflectance := one_mul _
        _ ≤ 1 := a.atMostOne⟩

/-- Vacuum attenuator on a full joint operator kernel, retaining every idler. -/
def attenuate {I : Type} {M : ℕ} (a : Splitter)
    (rho : opticalKernel (I × Occupation (Fin M))) : opticalKernel (I × Occupation (Fin M)) :=
  fun x y => ∑' k : Occupation (Fin M),
    lossAmplitude a (x.2+k) k * star (lossAmplitude a (y.2+k) k) *
      rho (x.1, x.2+k) (y.1, y.2+k)

/-! Small sanity tests pin definitions without proving source results. -/

example (p : ℝ) : supportWeightPower 0 p = 0 := by simp [supportWeightPower]

example {M : ℕ} (N : Occupation (Fin M)) : fock N (0, N) = 1 := by
  simp [fock]

example {M : ℕ} (N : Occupation (Fin M)) : ‖fock N‖ = 1 := by
  simp [fock, lp.norm_single (by norm_num : (0 : ENNReal) < 2)]

example (a : Splitter) : totalCountLaw a 0 0 = 1 := by
  simp [totalCountLaw]

example (s : ℝ) : lowerError 1 = 1/2 := by norm_num [lowerError]

example (eta : ℝ) (h0 : 0 ≤ eta) (h1 : eta ≤ 1) (a : Splitter) :
    (efficiencyScaled a eta h0 h1).reflectance = eta*a.reflectance := rfl

example {X : Type} (rho : opticalKernel X) : ¬ PurifiesOpticalKernel rho (0 : Hilbert (X × ℕ)) := by
  simp [PurifiesOpticalKernel]

example {X : Type} : IsOpticalEffect (0 : Hilbert X →L[ℂ] Hilbert X) := by
  simp [IsOpticalEffect, sq_nonneg]

example (c : Channels) : countingError c 0 = 1/2 := by
  simp [countingError, totalCountLaw]

example (M : ℕ) : tmsvCoefficients M 0 (0, 0) = 1 := by
  simp [tmsvCoefficients]

example {M : ℕ} (a : Splitter) : lossAmplitude a (0 : Occupation (Fin M)) 0 = 1 := by
  simp [lossAmplitude]

example : supportWeightPower 1 0 = 1 := by
  simp [supportWeightPower]

/-- Dual trace norm of a weighted Hermitian difference, used in (42).
The supremum ranges over ALL bounded self-adjoint contractions. Spectral
resolutions merely evaluate traces of the actual two states. -/
def weightedTraceNorm {X : Type} (rho sigma : opticalKernel X) (w0 w1 : ℝ) : ℝ :=
  sSup {v : ℝ | ∃ (A : Resolution rho) (B : Resolution sigma)
    (T : Hilbert X →L[ℂ] Hilbert X),
    (∀ u v, inner ℂ u (T v) = star (inner ℂ v (T u))) ∧
    (∀ u, |(inner ℂ u (T u)).re| ≤ ‖u‖^2) ∧
    v = w0 * (∑' n, A.weight n * (inner ℂ (A.ket n) (T (A.ket n))).re) -
      w1 * (∑' n, B.weight n * (inner ℂ (B.ket n) (T (B.ket n))).re)}

/-- Composition of full Fock operator kernels on the physical trace-class arguments. -/
def kernelProduct {X : Type} (rho sigma : opticalKernel X) : opticalKernel X :=
  fun x y => ∑' z : X, rho x z * sigma z y

/-- Target-detection universal envelope (59), with fixed real signal energy N. -/
def targetLower (R N : ℝ) : ℝ := lowerError (Real.rpow (1-R) N)

/-- Coherent target-detection error envelope (60). -/
def targetCoherent (R N : ℝ) : ℝ := lowerError (Real.exp (-R*N))

end QAlgorithms.Papers.Independent.Intakethird100.P54


