-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P44
-- name    : QAlgorithms_Papers_Independent_Renew46_P44
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T21:21:57.695159+00:00
-- url     : https://prove2.me/theorems/c48b3fdd-c909-4e63-94b5-0e0cfab223ec
-- title:
--   Definitions for Coding Theorems for Quantum Channels
-- statement:
--   The objects the formalized statements of *Coding Theorems for Quantum Channels* (arXiv:quant-ph/9809023) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `DiscreteInputLaw`: Discrete laws, including infinite alphabets; PDF pp.4,11. Only countably many weights can be nonzero, without a countability restriction on the alphabet.
--   - `discreteStateAverage`: Scalar coefficient barycenter, (6), PDF p.4. On states and probability laws the series converges absolutely. No entropy finiteness is required.
--   - `discreteHolevoInformation`: Equation (5), PDF p.4: relative entropy avoids infinity minus infinity.
--   - `Receiver`: Bounded positive collective receiver, (21),(25), PDF pp.8-9. The unused effect is I minus the finite sum and represents erasure.
--   - `collectiveAverageError`: Uniform average error, (21),(25), PDF pp.8-9; used only for M>0.
--   - `optimalCollectiveError`: Minimum over all collective receivers, (26), PDF p.9. An extended infimum cannot acquire a default zero from an unbounded real set.
--   - `wordOutput`: Genuine memoryless product outputs, (25), PDF p.9.
--   - `wordCost`: Per-word additive cost, (54), PDF p.18; every word must obey it.
--   - `cqError`: Product-letter code minimum with a separate constraint on every message; (25),(54),(61 corrected), PDF pp.9,18,20.
--   - `natMessagesNats`: Positive integer interpretation of the source's informal exp(nR).
--   - `averageErrorCqCapacity`: Operational average-error capacity in nats, (49),(54), PDF pp.16,18-19. The supremum is extended and the limit ranges over all sufficiently large n.
--   - `HasMeanCostBound`: Ensemble-average cost, (53),(55), PDF p.18. This does not constrain individual support letters or individual codewords.
--   - `cqHolevoBlock`: Constrained block Holevo supremum, (55), PDF p.18.
--   - `cqHolevoCapacity`: Positive-block regularization, (14),(56), PDF pp.5,18.
--   - `cqHolevoSingle`: One-letter constrained Holevo supremum, (56), PDF p.18.
--   - `BoundedLetterEntropy`: Condition (24)/(66), PDF pp.8,20: individual entropies have one finite bound. Mixture entropies are not assumed bounded.
--   - `wordWeight`: Equation (32), PDF p.11, corrected indices pi_(i1)...pi_(in).
--   - `expectedDecodingError`: Independent random codewords, (32), PDF p.11; the whole code is fixed before any transmitted message is selected.
--   - `pureSignalGram`: Finite Gram matrix, (27), PDF p.10, with conjugate linear first argument.
--   - `pureCollisionTrace`: Collision trace of the mean pure state, (34), PDF p.11.
--   - `pureCutoffRate`: Cutoff supremum. Its extended form also covers infimum collision zero; no Real.log(0) is used for an unbounded cutoff. Equation (34), PDF p.11.
--   - `discretePureMean`: Mean bounded operator for a normalized pure ensemble, (6), PDF p.4. The series is norm summable since the rank-one summands have norm pi(a).
--   - `compactApproximationValue`: Approximation numbers of a positive compact operator: its decreasing nonzero eigenvalues, padded by zero. The infimum set is nonempty and bounded below by zero. This is the same spectral prescription as accepted Claimed50.P39.
--   - `pureMeanPowerTrace`: Trace of the (1+s)-power for a normalized positive compact mean; (39),(41), PDF pp.12-13. All uses have s>=0, hence a finite trace.
--   - `numberMean`: Extended photon mean, PDF p.24, (86); infinite moments stay infinite.
--   - `DecisionRule`: Countable complete decision rule; weak resolution of identity as quadratic forms, PDF p.2. Any discrete rule on a countably supported ensemble can be relabelled in this way without changing its information.
--   - `scalarDivergence`: Nonnegative scalar relative entropy integrand. The linear correction cancels after summation over probability laws, recovering (9), PDF p.4.
--   - `discreteReceiverInformation`: Discrete mutual information in nats, (9), PDF p.4; infinity is retained.
--   - `informationBlock`: Equation (12), PDF p.5: all block-state ensembles, including entangled inputs, and collective receivers.
--   - `holevoBlock`: Holevo counterpart of (12), PDF p.5; discrete ensembles need not be finite.
--   - `informationCapacity`: Equation (13), PDF p.5; positive blocks only.
--   - `regularizedChannelHolevo`: Equation (14), PDF p.5, with an extended supremum.
--   - `quantumCodeError`: General quantum code minimum, (21), PDF p.8; arbitrary block densities.
--   - `IsCq`: The source's c-q form (17), PDF p.6, relative to the fixed complete basis. This is narrower than the full measure-and-prepare class.
--   - `IsQc`: The source's q-c form (19), PDF p.7. Arbitrary bounded effects form a weak resolution of the identity; outputs are diagonal in the fixed complete basis.
--   - `integralAverage`: Integral barycenter, (65), PDF p.20; valid on weakly continuous density families and Borel probability laws. Every scalar integrand is bounded.
--   - `integralChi`: Equations (64)-(65), PDF p.20; extended relative entropy, never an unrestricted subtraction of infinite output entropies.
--   - `AdmissibleMeasure`: Borel probability law with finite expected cost, (60), PDF p.20.
--   - `gaussianOperator`: Actual displaced thermal density, (82)-(84), PDF pp.23-24. Thermal mean parameter N corresponds to 2N+1 in the accepted oscillator convention.
--   - `gaussianOutput`: Coefficients of that same full-space output, without attenuation or squeezing.
--   - `gaussianLaw`: Normalized circular Gaussian modulation (91), PDF p.25; E=0 is Dirac. No singular Lebesgue density is evaluated at zero modulation energy.
--   - `photonOutput`: Photon alphabet (92), PDF pp.25-26: the unilateral shift of thermal number probabilities. This shift is an isometry, not a unitary.
--   - `photonPrior`: Optimal photon law printed below (95), PDF p.26, with a vacuum endpoint.
--   - `multimodeOutput`: Finite joint Gaussian output, (102), PDF p.28, with one collective receiver.
--   - `modeCost`: Transmitted modulation energy, (106), PDF p.29; thermal noise is excluded.
--   - `planck`: Planck occupation, (104), PDF p.28; used only with positive arguments.
--   - `waterfill`: Water-filling allocation, (110), PDF p.29.
--   - `modeLaw`: Independent normalized circular Gaussians, including Dirac factors when an allocation vanishes. Restores the missing product of 1/(pi m_j) in (109).
--   - `thermalEntropyBudget`: Finite-mode entropy at a total energy budget, s(P), PDF p.30. Under the positive frequency hypotheses the feasible set is nonempty and compact, so this real supremum is the attained finite maximum, including P=0.
--   - `periodicAngularFrequency`: Positive periodic frequency grid, (118), PDF p.31.
--   - `bandModes`: Explicit finite periodic/truncated mode collection, PDF p.31.
--   - `waveformError`: Finite-T waveform code error, (123)-(124), PDF pp.31-32. T is observation time; each message is one full finite-mode amplitude vector, not T channel uses.
--   - `waveformCapacity`: Operational waveform capacity in nats per unit time, PDF p.32. The limit uses all real T tending to infinity.
--   - `waveformInformation`: Total finite-mode information CT, (129),(143), PDF pp.32,35. It is total information, not information per unit time.
--   - `spectralAllocation`: Band water-filling allocation, (131), PDF p.33.
--   - `FrequencyWindows`: Finite windows increasing to the infinite band, PDF p.31.
--   - `FeasibleSpectrum`: Frequency-space mean-energy admissibility, (142), PDF p.34. The energy integral is genuine, and values outside positive frequencies are irrelevant.
--   - `spectralInformation`: Integrable entropy DIFFERENCE in (141), PDF p.34; separate infinite noise and total entropies are never subtracted after integration.
--   - `equilibriumNoise`: Equilibrium noise occupation with a separate vacuum endpoint, PDF p.36.
--   - `errorExponent`: Error exponent, (38), PDF p.12. Zero error has exponent infinity; positive-block division is used in limits, never Real.log(1/0).
--   - `reliability`: The limsup reliability function (38), PDF p.12.
--   - `pureMu`: Random-coding scalar (41), with its exact s=0 endpoint, PDF p.13.
--   - `pureExpurgatedMu`: Expurgated scalar, PDF pp.13-14, s>=1.
--   - `entropySlope`: Right entropy slope. Infinite entropy gives an infinite right slope, not the zero returned by a nonexistent finite real derivative.
--   - `squareRootCodeError`: Square-root decision rule (27)-(28), PDF p.10, in its Gram-diagonal error formula. Zero eigenvalues of the Gram matrix are allowed; this is the Moore-Penrose rule, not a matrix inverse that vanishes on the whole singular matrix.
--   - `cqInformationBlock`: One-use and block accessible information for a c-q alphabet, PDF pp.5,15.
--   - `bernoulliInputLaw`: Bernoulli prior with pi=P(letter 1), PDF p.14.
--   - `binaryLambdaLow`: Smaller/larger eigenvalues of the binary mean density, PDF p.14.
--   - `binaryLambdaHigh`
--   - `binaryMu`: Uniform-prior random exponent scalar, PDF pp.14-15.
--   - `binaryExpurgatedMu`: Uniform-prior expurgated scalar, s>=1, PDF p.15.
--   - `binaryCapacityValue`: Closed binary capacity, including orthogonal and identical signals.
--   - `binaryOneShotValue`: Product-measurement capacity in nats, PDF p.15.
--   - `operatorPowerTrace`: Trace of a positive compact operator's real power; PDF pp.22,26.
--   - `tiltedAverage`: Tilted pure average, (74), PDF p.22; finite tilted mass is a domain guard.
--   - `tiltedMu`: Equations (74),(77), PDF pp.22-23.
--   - `tiltedExpurgatedMu`
--   - `shellProbability`: Shell probability (75), PDF p.22. No asymptotic assertion is built in.
--   - `integralTilt`: Continuous tilted operator in (78), PDF p.23; the projectors, rather than arbitrarily phased vector representatives, have to be weakly continuous.
--   - `integralTiltMu`
--   - `integralExpurgatedMu`: Continuous expurgated integral (79), PDF p.23.
--   - `integralShell`: Continuous shell conditioning, using a genuine product probability law.
--   - `finiteRandomBound`: Integer-message form of (73): R is the exact rate log M/n. This avoids rounding a noninteger array size while retaining the squared prefactor.
--   - `finiteExpurgatedBound`: Integer-message form of (76): the correction is (2/n)log(2exp(p delta)/nu).
--   - `gaussianMu`: Fixed-Gaussian-prior scalar functions, (78)-(79),(91), PDF pp.25-27.
--   - `gaussianExpurgatedMu`
--   - `gaussianQ`: The positive root q, PDF p.27: (1+sqrt(4E^2+1))/2.
--   - `gaussianP`: Fixed-prior optimizing p at s=1 and expurgated s>=1, PDF p.27.
--   - `gaussianExpurgatedP`
-- source:
--   Coding Theorems for Quantum Channels, arXiv:quant-ph/9809023v1, https://arxiv.org/abs/quant-ph/9809023v1

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P33
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P39
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P07
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P39
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P16
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P14

/-! Holevo, Coding Theorems for Quantum Channels, quant-ph/9809023v1.
Natural logarithms, arbitrary basis cardinalities, completed Hilbert spaces,
positive trace-class densities, collective sub-POVMs and uniform average error.
Source ambiguities and deferred interfaces are recorded in the unit artifacts.
Compilation is pending the mechanical batch handoff. -/

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P44

open Filter MeasureTheory
open scoped ENNReal NNReal Topology BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Claimed50.P39 (g)
open QAlgorithms.Papers.Independent.Claimed50.P16 (tracePair)
open QAlgorithms.Papers.Independent.Frontier30.P14 (traceClassTensorPower)

namespace TC
export QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsDensity IsTraceClass IsTraceClassChannel rankOne)
end TC

namespace QE
export QAlgorithms.Papers.Independent.Frontier18.P07
  (extendedEntropyNats extendedRelativeEntropyNats)
end QE

namespace F
export QAlgorithms.Papers.Independent.Dependency50.P39
  (Fock FockOperator fockKet IsDensity thermalDensity thermalMatrix ThermalRealized
   photonProbability photonMean HasFockMatrix operatorOfMatrix displacement)
end F

attribute [local instance] Classical.propDecidable Classical.decEq

/-! Reuse audit for this repair: g, the trace-class/bounded tracePair and
traceClassTensorPower are imported directly. The other formerly colliding names
were inspected in the pinned index: their frozen signatures impose finite laws,
finite Hilbert spaces, bits, private tasks, or different information concepts.
The distinct local names below retain this paper's arbitrary-carrier,
average-error, natural-logarithm and real-power domains. See ASSESSMENT.json. -/

/-- Discrete laws, including infinite alphabets; PDF pp.4,11. Only countably
many weights can be nonzero, without a countability restriction on the alphabet. -/
structure DiscreteInputLaw (A : Type) where
  weight : A → ℝ
  nonnegative : ∀ a, 0 ≤ weight a
  summable : Summable weight
  total : ∑' a, weight a = 1

/-- Scalar coefficient barycenter, (6), PDF p.4. On states and probability laws
the series converges absolutely. No entropy finiteness is required. -/
def discreteStateAverage {A I : Type} (S : A → Matrix I I ℂ) (pi : DiscreteInputLaw A) : Matrix I I ℂ :=
  fun i j => ∑' a, (pi.weight a : ℂ) * S a i j

/-- Equation (5), PDF p.4: relative entropy avoids infinity minus infinity. -/
def discreteHolevoInformation {A I : Type} (S : A → Matrix I I ℂ) (pi : DiscreteInputLaw A) : ℝ≥0∞ :=
  ∑' a, ENNReal.ofReal (pi.weight a) *
    QE.extendedRelativeEntropyNats (S a) (discreteStateAverage S pi)

/-- Bounded positive collective receiver, (21),(25), PDF pp.8-9.
The unused effect is I minus the finite sum and represents erasure. -/
structure Receiver (I : Type) (M : ℕ) where
  effect : Fin M → (Hilbert I →L[ℂ] Hilbert I)
  selfAdjoint : ∀ k, (effect k).adjoint = effect k
  positive : ∀ k v, 0 ≤ (inner ℂ v (effect k v)).re
  subidentity : ∀ v, (∑ k, (inner ℂ v (effect k v)).re) ≤ ‖v‖ ^ 2

/-- Uniform average error, (21),(25), PDF pp.8-9; used only for M>0. -/
def collectiveAverageError {I : Type} {M : ℕ} (S : Fin M → Matrix I I ℂ)
    (X : Receiver I M) : ℝ :=
  (∑ k, (1 - tracePair (X.effect k) (S k))) / (M : ℝ)

/-- Minimum over all collective receivers, (26), PDF p.9.
An extended infimum cannot acquire a default zero from an unbounded real set. -/
def optimalCollectiveError {I : Type} {M : ℕ} (S : Fin M → Matrix I I ℂ) : ℝ≥0∞ :=
  ⨅ X : Receiver I M, ENNReal.ofReal (collectiveAverageError S X)

/-- Genuine memoryless product outputs, (25), PDF p.9. -/
def wordOutput {A I : Type} (S : A → Matrix I I ℂ) {n : ℕ}
    (w : Fin n → A) : Matrix (Fin n → I) (Fin n → I) ℂ :=
  fun a b => ∏ k, S (w k) (a k) (b k)

/-- Per-word additive cost, (54), PDF p.18; every word must obey it. -/
def wordCost {A : Type} (f : A → ℝ) {n : ℕ} (w : Fin n → A) : ℝ :=
  ∑ k, f (w k)

/-- Product-letter code minimum with a separate constraint on every message;
(25),(54),(61 corrected), PDF pp.9,18,20. -/
def cqError {A I : Type} (S : A → Matrix I I ℂ) (f : A → ℝ)
    (E : ℝ) (n M : ℕ) : ℝ≥0∞ :=
  ⨅ W : {W : Fin M → Fin n → A // ∀ k, wordCost f (W k) ≤ (n : ℝ) * E},
    optimalCollectiveError (fun k => wordOutput S (W.val k))

/-- Positive integer interpretation of the source's informal exp(nR). -/
def natMessagesNats (n : ℕ) (R : ℝ) : ℕ := Nat.ceil (Real.exp ((n : ℝ) * R))

/-- Operational average-error capacity in nats, (49),(54), PDF pp.16,18-19.
The supremum is extended and the limit ranges over all sufficiently large n. -/
def averageErrorCqCapacity {A I : Type} (S : A → Matrix I I ℂ) (f : A → ℝ)
    (E : ℝ) : ℝ≥0∞ :=
  ⨆ R : {R : ℝ // 0 ≤ R ∧ Tendsto
      (fun n : ℕ => cqError S f E n (natMessagesNats n R)) atTop (nhds 0)},
    ENNReal.ofReal R.val

/-- Ensemble-average cost, (53),(55), PDF p.18. This does not constrain
individual support letters or individual codewords. -/
def HasMeanCostBound {A : Type} (f : A → ℝ) (E : ℝ) (pi : DiscreteInputLaw A) : Prop :=
  Summable (fun a => pi.weight a * f a) ∧ (∑' a, pi.weight a * f a) ≤ E

/-- Constrained block Holevo supremum, (55), PDF p.18. -/
def cqHolevoBlock {A I : Type} (S : A → Matrix I I ℂ) (f : A → ℝ)
    (E : ℝ) (n : ℕ) : ℝ≥0∞ :=
  ⨆ pi : {pi : DiscreteInputLaw (Fin n → A) // HasMeanCostBound (wordCost f) ((n : ℝ) * E) pi},
    discreteHolevoInformation (fun w => wordOutput S w) pi.val

/-- Positive-block regularization, (14),(56), PDF pp.5,18. -/
def cqHolevoCapacity {A I : Type} (S : A → Matrix I I ℂ) (f : A → ℝ)
    (E : ℝ) : ℝ≥0∞ :=
  ⨆ n : ℕ+, cqHolevoBlock S f E n / (n : ℝ≥0∞)

/-- One-letter constrained Holevo supremum, (56), PDF p.18. -/
def cqHolevoSingle {A I : Type} (S : A → Matrix I I ℂ) (f : A → ℝ)
    (E : ℝ) : ℝ≥0∞ :=
  ⨆ pi : {pi : DiscreteInputLaw A // HasMeanCostBound f E pi}, discreteHolevoInformation S pi.val

/-- Condition (24)/(66), PDF pp.8,20: individual entropies have one finite
bound. Mixture entropies are not assumed bounded. -/
def BoundedLetterEntropy {A I : Type} (S : A → Matrix I I ℂ) : Prop :=
  ∃ B : ℝ≥0, ∀ a, QE.extendedEntropyNats (S a) ≤ (B : ℝ≥0∞)

/-- Equation (32), PDF p.11, corrected indices pi_(i1)...pi_(in). -/
def wordWeight {A : Type} (pi : DiscreteInputLaw A) {n : ℕ} (w : Fin n → A) : ℝ :=
  ∏ k, pi.weight (w k)

/-- Independent random codewords, (32), PDF p.11; the whole code is fixed
before any transmitted message is selected. -/
def expectedDecodingError {A I : Type} (S : A → Matrix I I ℂ)
    (pi : DiscreteInputLaw A) (n M : ℕ) : ℝ≥0∞ :=
  ∑' W : Fin M → Fin n → A,
    ENNReal.ofReal (∏ k, wordWeight pi (W k)) *
      optimalCollectiveError (fun k => wordOutput S (W k))

/-- Finite Gram matrix, (27), PDF p.10, with conjugate linear first argument. -/
def pureSignalGram {I : Type} {M : ℕ} (v : Fin M → Hilbert I) : Matrix (Fin M) (Fin M) ℂ :=
  fun i j => inner ℂ (v i) (v j)

/-- Collision trace of the mean pure state, (34), PDF p.11. -/
def pureCollisionTrace {A I : Type} (psi : A → Hilbert I) (pi : DiscreteInputLaw A) : ℝ :=
  ∑' a, ∑' b, pi.weight a * pi.weight b * ‖inner ℂ (psi a) (psi b)‖ ^ 2

/-- Cutoff supremum. Its extended form also covers infimum collision zero;
no Real.log(0) is used for an unbounded cutoff. Equation (34), PDF p.11. -/
def pureCutoffRate {A I : Type} (psi : A → Hilbert I) : ℝ≥0∞ :=
  ⨆ pi : DiscreteInputLaw A, ENNReal.ofReal (-Real.log (pureCollisionTrace psi pi))

/-- Mean bounded operator for a normalized pure ensemble, (6), PDF p.4.
The series is norm summable since the rank-one summands have norm pi(a). -/
def discretePureMean {A I : Type} (psi : A → Hilbert I) (pi : DiscreteInputLaw A) :
    Hilbert I →L[ℂ] Hilbert I :=
  ∑' a, (pi.weight a : ℂ) • InnerProductSpace.rankOne ℂ (psi a) (psi a)

/-- Approximation numbers of a positive compact operator: its decreasing
nonzero eigenvalues, padded by zero. The infimum set is nonempty and bounded
below by zero. This is the same spectral prescription as accepted Claimed50.P39. -/
def compactApproximationValue {I : Type} (T : Hilbert I →L[ℂ] Hilbert I) (j : ℕ) : ℝ :=
  sInf {r : ℝ | ∃ u v : Fin j → Hilbert I,
    r = ‖T - ∑ k, InnerProductSpace.rankOne ℂ (u k) (v k)‖}

/-- Trace of the (1+s)-power for a normalized positive compact mean;
(39),(41), PDF pp.12-13. All uses have s>=0, hence a finite trace. -/
def pureMeanPowerTrace {A I : Type} (psi : A → Hilbert I) (pi : DiscreteInputLaw A) (s : ℝ) : ℝ :=
  ∑' j : ℕ, (compactApproximationValue (discretePureMean psi pi) j) ^ (1 + s)

/-- Extended photon mean, PDF p.24, (86); infinite moments stay infinite. -/
def numberMean (S : F.FockOperator) : ℝ≥0∞ :=
  ∑' j : ℕ, ENNReal.ofReal ((j : ℝ) * F.photonProbability S j)

example {A : Type} (w : Fin 0 → A) : wordCost (fun _ => 0) w = 0 := by
  simp [wordCost]

example {A I : Type} (S : A → Matrix I I ℂ) (w : Fin 0 → A)
    (a b : Fin 0 → I) : wordOutput S w a b = 1 := by simp [wordOutput]

example : g 0 = 0 := by simp [g]

example {I : Type} {M : ℕ} : pureSignalGram (fun _ : Fin M => (0 : Hilbert I)) = 0 := by
  funext i j
  simp [pureSignalGram]

/-- Countable complete decision rule; weak resolution of identity as quadratic
forms, PDF p.2. Any discrete rule on a countably supported ensemble can be
relabelled in this way without changing its information. -/
structure DecisionRule (I : Type) where
  effect : ℕ → (Hilbert I →L[ℂ] Hilbert I)
  selfAdjoint : ∀ k, (effect k).adjoint = effect k
  positive : ∀ k v, 0 ≤ (inner ℂ v (effect k v)).re
  complete : ∀ v, HasSum (fun k => (inner ℂ v (effect k v)).re) (‖v‖ ^ 2)

/-- Nonnegative scalar relative entropy integrand. The linear correction
cancels after summation over probability laws, recovering (9), PDF p.4. -/
def scalarDivergence (a b : ℝ) : ℝ≥0∞ :=
  if b = 0 then (if a = 0 then 0 else ⊤)
  else ENNReal.ofReal (a * Real.log (a / b) + b - a)

/-- Discrete mutual information in nats, (9), PDF p.4; infinity is retained. -/
def discreteReceiverInformation {A I : Type} (S : A → Matrix I I ℂ)
    (pi : DiscreteInputLaw A) (X : DecisionRule I) : ℝ≥0∞ :=
  ∑' a, ∑' k, scalarDivergence
    (pi.weight a * tracePair (X.effect k) (S a))
    (pi.weight a * ∑' b, pi.weight b * tracePair (X.effect k) (S b))

/-- Equation (12), PDF p.5: all block-state ensembles, including entangled
inputs, and collective receivers. -/
def informationBlock {I : Type} (Phi : Matrix I I ℂ → Matrix I I ℂ)
    (n : ℕ) : ℝ≥0∞ :=
  ⨆ rho : ℕ → TC.State (Fin n → I), ⨆ pi : DiscreteInputLaw ℕ,
    ⨆ X : DecisionRule (Fin n → I),
      discreteReceiverInformation (fun a => traceClassTensorPower Phi n (rho a).coefficients) pi X

/-- Holevo counterpart of (12), PDF p.5; discrete ensembles need not be finite. -/
def holevoBlock {I : Type} (Phi : Matrix I I ℂ → Matrix I I ℂ)
    (n : ℕ) : ℝ≥0∞ :=
  ⨆ rho : ℕ → TC.State (Fin n → I), ⨆ pi : DiscreteInputLaw ℕ,
    discreteHolevoInformation (fun a => traceClassTensorPower Phi n (rho a).coefficients) pi

/-- Equation (13), PDF p.5; positive blocks only. -/
def informationCapacity {I : Type} (Phi : Matrix I I ℂ → Matrix I I ℂ) : ℝ≥0∞ :=
  ⨆ n : ℕ+, informationBlock Phi n / (n : ℝ≥0∞)

/-- Equation (14), PDF p.5, with an extended supremum. -/
def regularizedChannelHolevo {I : Type} (Phi : Matrix I I ℂ → Matrix I I ℂ) : ℝ≥0∞ :=
  ⨆ n : ℕ+, holevoBlock Phi n / (n : ℝ≥0∞)

/-- General quantum code minimum, (21), PDF p.8; arbitrary block densities. -/
def quantumCodeError {I : Type} (Phi : Matrix I I ℂ → Matrix I I ℂ)
    (n M : ℕ) : ℝ≥0∞ :=
  ⨅ rho : Fin M → TC.State (Fin n → I),
    optimalCollectiveError (fun k => traceClassTensorPower Phi n (rho k).coefficients)

/-- The source's c-q form (17), PDF p.6, relative to the fixed complete basis.
This is narrower than the full measure-and-prepare class. -/
def IsCq {I : Type} (Phi : Matrix I I ℂ → Matrix I I ℂ) : Prop :=
  ∃ S : I → TC.State I, ∀ rho : TC.State I, ∀ i j,
    Phi rho.coefficients i j = ∑' a,
      ((rho.coefficients a a).re : ℂ) * (S a).coefficients i j

/-- The source's q-c form (19), PDF p.7. Arbitrary bounded effects form a weak
resolution of the identity; outputs are diagonal in the fixed complete basis. -/
def IsQc {I : Type} (Phi : Matrix I I ℂ → Matrix I I ℂ) : Prop :=
  ∃ X : I → (Hilbert I →L[ℂ] Hilbert I),
    (∀ k, (X k).adjoint = X k) ∧
    (∀ k v, 0 ≤ (inner ℂ v (X k v)).re) ∧
    (∀ v, HasSum (fun k => (inner ℂ v (X k v)).re) (‖v‖ ^ 2)) ∧
    ∀ rho : TC.State I, ∀ i j,
      Phi rho.coefficients i j = if i = j then (tracePair (X i) rho.coefficients : ℂ) else 0

example : scalarDivergence 0 0 = 0 := by simp [scalarDivergence]

/-- Integral barycenter, (65), PDF p.20; valid on weakly continuous density
families and Borel probability laws. Every scalar integrand is bounded. -/
def integralAverage {A I : Type} [MeasurableSpace A]
    (S : A → Matrix I I ℂ) (pi : Measure A) : Matrix I I ℂ :=
  fun i j => ∫ a, S a i j ∂pi

/-- Equations (64)-(65), PDF p.20; extended relative entropy, never an
unrestricted subtraction of infinite output entropies. -/
def integralChi {A I : Type} [MeasurableSpace A]
    (S : A → Matrix I I ℂ) (pi : Measure A) : ℝ≥0∞ :=
  ∫⁻ a, QE.extendedRelativeEntropyNats (S a) (integralAverage S pi) ∂pi

/-- Borel probability law with finite expected cost, (60), PDF p.20. -/
def AdmissibleMeasure {A : Type} [MeasurableSpace A]
    (f : A → ℝ) (E : ℝ) (pi : Measure A) : Prop :=
  IsProbabilityMeasure pi ∧ Integrable f pi ∧ (∫ a, f a ∂pi) ≤ E

/-- Actual displaced thermal density, (82)-(84), PDF pp.23-24. Thermal mean
parameter N corresponds to 2N+1 in the accepted oscillator convention. -/
def gaussianOperator (N : ℝ) (z : ℂ) : F.FockOperator :=
  ((F.displacement z).comp (F.thermalDensity (2 * N + 1))).comp
    (F.displacement z).adjoint

/-- Coefficients of that same full-space output, without attenuation or squeezing. -/
def gaussianOutput (N : ℝ) (z : ℂ) : Matrix ℕ ℕ ℂ :=
  fun i j => gaussianOperator N z (F.fockKet j) i

/-- Normalized circular Gaussian modulation (91), PDF p.25; E=0 is Dirac.
No singular Lebesgue density is evaluated at zero modulation energy. -/
def gaussianLaw (E : ℝ) : Measure ℂ :=
  if E = 0 then Measure.dirac 0 else
    volume.withDensity (fun z : ℂ =>
      ENNReal.ofReal (Real.exp (-Complex.normSq z / E) / (Real.pi * E)))

/-- Photon alphabet (92), PDF pp.25-26: the unilateral shift of thermal
number probabilities. This shift is an isometry, not a unitary. -/
def photonOutput (N : ℝ) (m : ℕ) : Matrix ℕ ℕ ℂ :=
  fun i j => if i = j ∧ m ≤ i then
    ((N / (N + 1)) ^ (i - m) / (N + 1) : ℝ) else 0

/-- Optimal photon law printed below (95), PDF p.26, with a vacuum endpoint. -/
def photonPrior (N E : ℝ) (m : ℕ) : ℝ :=
  if N + E = 0 then (if m = 0 then 1 else 0) else
    N / (N + E) * (if m = 0 then 1 else 0) +
      E / (N + E) * (N + E) ^ m / (N + E + 1) ^ (m + 1)

example (z : ℂ) : gaussianLaw 0 = Measure.dirac 0 := by simp [gaussianLaw]

example : photonPrior 0 0 0 = 1 := by simp [photonPrior]

example : photonOutput 0 0 0 0 = 1 := by simp [photonOutput]

/-- Finite joint Gaussian output, (102), PDF p.28, with one collective receiver. -/
def multimodeOutput {J : Type} [Fintype J] (N : J → ℝ) (z : J → ℂ) :
    Matrix (J → ℕ) (J → ℕ) ℂ :=
  fun a b => ∏ j, gaussianOutput (N j) (z j) (a j) (b j)

/-- Transmitted modulation energy, (106), PDF p.29; thermal noise is excluded. -/
def modeCost {J : Type} [Fintype J] (hbar : ℝ) (omega : J → ℝ) (z : J → ℂ) : ℝ :=
  ∑ j, hbar * omega j * Complex.normSq (z j)

/-- Planck occupation, (104), PDF p.28; used only with positive arguments. -/
def planck (hbar theta omega : ℝ) : ℝ := 1 / (Real.exp (theta * hbar * omega) - 1)

/-- Water-filling allocation, (110), PDF p.29. -/
def waterfill {J : Type} (hbar theta : ℝ) (omega N : J → ℝ) : J → ℝ :=
  fun j => max (planck hbar theta (omega j) - N j) 0

/-- Independent normalized circular Gaussians, including Dirac factors when
an allocation vanishes. Restores the missing product of 1/(pi m_j) in (109). -/
def modeLaw {J : Type} [Fintype J] (m : J → ℝ) : Measure (J → ℂ) :=
  Measure.pi (fun j => gaussianLaw (m j))

/-- Finite-mode entropy at a total energy budget, s(P), PDF p.30. Under the
positive frequency hypotheses the feasible set is nonempty and compact,
so this real supremum is the attained finite maximum, including P=0. -/
def thermalEntropyBudget {J : Type} [Fintype J]
    (hbar : ℝ) (omega : J → ℝ) (P : ℝ) : ℝ :=
  sSup {r : ℝ | ∃ m : J → ℝ, (∀ j, 0 ≤ m j) ∧
    (∑ j, hbar * omega j * m j) ≤ P ∧ r = ∑ j, g (m j)}

example {J : Type} [Fintype J] (hbar : ℝ) (omega : J → ℝ) :
    modeCost hbar omega (fun _ => 0) = 0 := by simp [modeCost]

/-- Positive periodic frequency grid, (118), PDF p.31. -/
def periodicAngularFrequency (T : ℝ) (j : ℕ) : ℝ := 2 * Real.pi * (j : ℝ) / T

/-- Explicit finite periodic/truncated mode collection, PDF p.31. -/
def bandModes (T low high : ℝ) : Finset ℕ :=
  (Finset.range (Nat.floor (T * high / (2 * Real.pi)) + 1)).filter
    (fun j => 0 < j ∧ low ≤ periodicAngularFrequency T j ∧ periodicAngularFrequency T j ≤ high)

/-- Finite-T waveform code error, (123)-(124), PDF pp.31-32. T is observation
time; each message is one full finite-mode amplitude vector, not T channel uses. -/
def waveformError (hbar : ℝ) (N : ℝ → ℝ) (low high E T : ℝ)
    (M : ℕ) : ℝ≥0∞ :=
  let J := ↥(bandModes T low high)
  let omega : J → ℝ := fun j => periodicAngularFrequency T j.val
  ⨅ W : {W : Fin M → J → ℂ // ∀ k, modeCost hbar omega (W k) ≤ T * E},
    optimalCollectiveError (fun k => multimodeOutput (fun j => N (omega j)) (W.val k))

/-- Operational waveform capacity in nats per unit time, PDF p.32.
The limit uses all real T tending to infinity. -/
def waveformCapacity (hbar : ℝ) (N : ℝ → ℝ)
    (low high : ℝ → ℝ) (E : ℝ) : ℝ≥0∞ :=
  ⨆ R : {R : ℝ // 0 ≤ R ∧ Tendsto
      (fun T : ℝ => waveformError hbar N (low T) (high T) E T
        (Nat.ceil (Real.exp (T * R)))) atTop (nhds 0)}, ENNReal.ofReal R.val

/-- Total finite-mode information CT, (129),(143), PDF pp.32,35.
It is total information, not information per unit time. -/
def waveformInformation (hbar : ℝ) (N : ℝ → ℝ) (low high E T : ℝ) : ℝ :=
  let J := ↥(bandModes T low high)
  sSup {r : ℝ | ∃ m : J → ℝ, (∀ j, 0 ≤ m j) ∧
    (∑ j, hbar * periodicAngularFrequency T j.val * m j) ≤ T * E ∧
    r = ∑ j, (g (N (periodicAngularFrequency T j.val) + m j) - g (N (periodicAngularFrequency T j.val)))}

/-- Band water-filling allocation, (131), PDF p.33. -/
def spectralAllocation (hbar theta : ℝ) (N : ℝ → ℝ) (omega : ℝ) : ℝ :=
  max (planck hbar theta omega - N omega) 0

/-- Finite windows increasing to the infinite band, PDF p.31. -/
structure FrequencyWindows where
  low : ℝ → ℝ
  high : ℝ → ℝ
  positive : ∀ T, 0 < T → 0 < low T ∧ low T < high T
  decreasing : AntitoneOn low (Set.Ioi 0)
  increasing : MonotoneOn high (Set.Ioi 0)
  lowLimit : Tendsto low atTop (nhds 0)
  highLimit : Tendsto high atTop atTop

/-- Frequency-space mean-energy admissibility, (142), PDF p.34.
The energy integral is genuine, and values outside positive frequencies are irrelevant. -/
def FeasibleSpectrum (hbar E : ℝ) (m : ℝ → ℝ) : Prop :=
  AEStronglyMeasurable m (volume.restrict (Set.Ioi 0)) ∧
  (∀ omega, 0 < omega → 0 ≤ m omega) ∧
  Integrable (fun omega => hbar * omega * m omega) (volume.restrict (Set.Ioi 0)) ∧
  (∫ omega in Set.Ioi (0 : ℝ), hbar * omega * m omega) / (2 * Real.pi) ≤ E

/-- Integrable entropy DIFFERENCE in (141), PDF p.34; separate infinite
noise and total entropies are never subtracted after integration. -/
def spectralInformation (N m : ℝ → ℝ) : ℝ :=
  (∫ omega in Set.Ioi (0 : ℝ), g (N omega + m omega) - g (N omega)) / (2 * Real.pi)

/-- Equilibrium noise occupation with a separate vacuum endpoint, PDF p.36. -/
def equilibriumNoise (hbar P : ℝ) (omega : ℝ) : ℝ :=
  if P = 0 then 0 else planck hbar (Real.sqrt (Real.pi / (12 * hbar * P))) omega

/-- Error exponent, (38), PDF p.12. Zero error has exponent infinity;
positive-block division is used in limits, never Real.log(1/0). -/
def errorExponent (p : ℝ≥0∞) (n : ℕ) : ℝ≥0∞ :=
  if p = 0 then ⊤ else ENNReal.ofReal (-Real.log p.toReal / (n : ℝ))

/-- The limsup reliability function (38), PDF p.12. -/
def reliability {A I : Type} (S : A → Matrix I I ℂ) (f : A → ℝ)
    (E R : ℝ) : ℝ≥0∞ :=
  limsup (fun n : ℕ => errorExponent (cqError S f E n (natMessagesNats n R)) n) atTop

/-- Random-coding scalar (41), with its exact s=0 endpoint, PDF p.13. -/
def pureMu {A I : Type} (psi : A → Hilbert I) (pi : DiscreteInputLaw A) (s : ℝ) : ℝ :=
  if s = 0 then 0 else -Real.log (pureMeanPowerTrace psi pi s)

/-- Expurgated scalar, PDF pp.13-14, s>=1. -/
def pureExpurgatedMu {A I : Type} (psi : A → Hilbert I) (pi : DiscreteInputLaw A) (s : ℝ) : ℝ :=
  -s * Real.log (∑' a, ∑' b,
    pi.weight a * pi.weight b * ‖inner ℂ (psi a) (psi b)‖ ^ (2 / s))

/-- Right entropy slope. Infinite entropy gives an infinite right slope,
not the zero returned by a nonexistent finite real derivative. -/
def entropySlope {A I : Type} (psi : A → Hilbert I) (pi : DiscreteInputLaw A) : ℝ≥0∞ :=
  limsup (fun s : ℝ => ENNReal.ofReal (pureMu psi pi s / s))
    (nhdsWithin 0 (Set.Ioi 0))

/-- Square-root decision rule (27)-(28), PDF p.10, in its Gram-diagonal
error formula. Zero eigenvalues of the Gram matrix are allowed; this is the
Moore-Penrose rule, not a matrix inverse that vanishes on the whole singular matrix. -/
def squareRootCodeError {A I : Type} (psi : A → Hilbert I) (n M : ℕ) : ℝ≥0∞ :=
  ⨅ W : Fin M → Fin n → A,
    ENNReal.ofReal (1 - (∑ k : Fin M,
      ‖(CFC.sqrt (fun r t : Fin M =>
        ∏ j : Fin n, inner ℂ (psi (W r j)) (psi (W t j)))) k k‖ ^ 2) / (M : ℝ))

example (n : ℕ) : errorExponent 0 n = ⊤ := by simp [errorExponent]

/-- One-use and block accessible information for a c-q alphabet, PDF pp.5,15. -/
def cqInformationBlock {A I : Type} (S : A → Matrix I I ℂ) (n : ℕ) : ℝ≥0∞ :=
  ⨆ W : ℕ → Fin n → A, ⨆ pi : DiscreteInputLaw ℕ, ⨆ X : DecisionRule (Fin n → I),
    discreteReceiverInformation (fun a => wordOutput S (W a)) pi X

/-- Bernoulli prior with pi=P(letter 1), PDF p.14. -/
def bernoulliInputLaw (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : DiscreteInputLaw Bool where
  weight := fun b => if b then p else 1 - p
  nonnegative := by
    intro b
    cases b
    · exact sub_nonneg.mpr hp1
    · exact hp0
  summable := Summable.of_finite
  total := by simp [tsum_fintype] <;> ring

/-- Smaller/larger eigenvalues of the binary mean density, PDF p.14. -/
def binaryLambdaLow (epsilon p : ℝ) : ℝ :=
  (1 - Real.sqrt (1 - 4 * (1 - epsilon ^ 2) * p * (1 - p))) / 2

def binaryLambdaHigh (epsilon p : ℝ) : ℝ :=
  (1 + Real.sqrt (1 - 4 * (1 - epsilon ^ 2) * p * (1 - p))) / 2

/-- Uniform-prior random exponent scalar, PDF pp.14-15. -/
def binaryMu (epsilon s : ℝ) : ℝ :=
  -Real.log (((1 - epsilon) / 2) ^ (1 + s) + ((1 + epsilon) / 2) ^ (1 + s))

/-- Uniform-prior expurgated scalar, s>=1, PDF p.15. -/
def binaryExpurgatedMu (epsilon s : ℝ) : ℝ :=
  -s * Real.log ((1 + epsilon ^ (2 / s)) / 2)

/-- Closed binary capacity, including orthogonal and identical signals. -/
def binaryCapacityValue (epsilon : ℝ) : ℝ :=
  -((1 - epsilon) / 2) * Real.log ((1 - epsilon) / 2) -
    ((1 + epsilon) / 2) * Real.log ((1 + epsilon) / 2)

/-- Product-measurement capacity in nats, PDF p.15. -/
def binaryOneShotValue (epsilon : ℝ) : ℝ :=
  ((1 + Real.sqrt (1 - epsilon ^ 2)) * Real.log (1 + Real.sqrt (1 - epsilon ^ 2)) +
    (1 - Real.sqrt (1 - epsilon ^ 2)) * Real.log (1 - Real.sqrt (1 - epsilon ^ 2))) / 2

/-- Trace of a positive compact operator's real power; PDF pp.22,26. -/
def operatorPowerTrace {I : Type} (T : Hilbert I →L[ℂ] Hilbert I) (a : ℝ) : ℝ :=
  ∑' j : ℕ, (compactApproximationValue T j) ^ a

/-- Tilted pure average, (74), PDF p.22; finite tilted mass is a domain guard. -/
def tiltedAverage {A I : Type} (psi : A → Hilbert I) (pi : DiscreteInputLaw A)
    (f : A → ℝ) (E p : ℝ) : Hilbert I →L[ℂ] Hilbert I :=
  ∑' a, ((pi.weight a * Real.exp (p * (f a - E)) : ℝ) : ℂ) •
    InnerProductSpace.rankOne ℂ (psi a) (psi a)

/-- Equations (74),(77), PDF pp.22-23. -/
def tiltedMu {A I : Type} (psi : A → Hilbert I) (pi : DiscreteInputLaw A)
    (f : A → ℝ) (E s p : ℝ) : ℝ :=
  -Real.log (operatorPowerTrace (tiltedAverage psi pi f E p) (1 + s))

def tiltedExpurgatedMu {A I : Type} (psi : A → Hilbert I) (pi : DiscreteInputLaw A)
    (f : A → ℝ) (E s p : ℝ) : ℝ :=
  -s * Real.log (∑' a, ∑' b, pi.weight a * pi.weight b *
    Real.exp (p * (f a + f b - 2 * E)) * ‖inner ℂ (psi a) (psi b)‖ ^ (2 / s))

/-- Shell probability (75), PDF p.22. No asymptotic assertion is built in. -/
def shellProbability {A : Type} (pi : DiscreteInputLaw A) (f : A → ℝ)
    (E delta : ℝ) (n : ℕ) : ℝ :=
  ∑' w : Fin n → A, if (n : ℝ) * E - delta ≤ wordCost f w ∧
    wordCost f w ≤ (n : ℝ) * E then wordWeight pi w else 0

/-- Continuous tilted operator in (78), PDF p.23; the projectors, rather than
arbitrarily phased vector representatives, have to be weakly continuous. -/
def integralTilt {A I : Type} [MeasurableSpace A] (psi : A → Hilbert I)
    (pi : Measure A) (f : A → ℝ) (E p : ℝ) : Hilbert I →L[ℂ] Hilbert I :=
  ∫ a, ((Real.exp (p * (f a - E)) : ℝ) : ℂ) •
    InnerProductSpace.rankOne ℂ (psi a) (psi a) ∂pi

def integralTiltMu {A I : Type} [MeasurableSpace A] (psi : A → Hilbert I)
    (pi : Measure A) (f : A → ℝ) (E s p : ℝ) : ℝ :=
  -Real.log (operatorPowerTrace (integralTilt psi pi f E p) (1 + s))

/-- Continuous expurgated integral (79), PDF p.23. -/
def integralExpurgatedMu {A I : Type} [MeasurableSpace A] (psi : A → Hilbert I)
    (pi : Measure A) (f : A → ℝ) (E s p : ℝ) : ℝ :=
  -s * Real.log (∫ a, ∫ b, Real.exp (p * (f a + f b - 2 * E)) *
    ‖inner ℂ (psi a) (psi b)‖ ^ (2 / s) ∂pi ∂pi)

/-- Continuous shell conditioning, using a genuine product probability law. -/
def integralShell {A : Type} [MeasurableSpace A] (pi : Measure A)
    (f : A → ℝ) (E delta : ℝ) (n : ℕ) : ℝ :=
  ((Measure.pi (fun _ : Fin n => pi))
    {w | (n : ℝ) * E - delta ≤ wordCost f w ∧ wordCost f w ≤ (n : ℝ) * E}).toReal

/-- Integer-message form of (73): R is the exact rate log M/n.
This avoids rounding a noninteger array size while retaining the squared prefactor. -/
def finiteRandomBound (n M : ℕ) (mu s p delta nu : ℝ) : ℝ :=
  2 * (Real.exp (p * delta) / nu) ^ 2 *
    Real.exp (-(n : ℝ) * (mu - s * (Real.log (M : ℝ) / (n : ℝ))))

/-- Integer-message form of (76): the correction is (2/n)log(2exp(p delta)/nu). -/
def finiteExpurgatedBound (n M : ℕ) (mu s p delta nu : ℝ) : ℝ :=
  Real.exp (-(n : ℝ) * (mu - s * (Real.log (M : ℝ) / (n : ℝ) +
    2 / (n : ℝ) * Real.log (2 * Real.exp (p * delta) / nu))))

/-- Fixed-Gaussian-prior scalar functions, (78)-(79),(91), PDF pp.25-27. -/
def gaussianMu (E s p : ℝ) : ℝ :=
  integralTiltMu (fun z =>
    QAlgorithms.Papers.Independent.Dependency50.P39.coherentKet z)
    (gaussianLaw E) Complex.normSq E s p

def gaussianExpurgatedMu (E s p : ℝ) : ℝ :=
  integralExpurgatedMu (fun z =>
    QAlgorithms.Papers.Independent.Dependency50.P39.coherentKet z)
    (gaussianLaw E) Complex.normSq E s p

/-- The positive root q, PDF p.27: (1+sqrt(4E^2+1))/2. -/
def gaussianQ (E : ℝ) : ℝ := (1 + Real.sqrt (4 * E ^ 2 + 1)) / 2

/-- Fixed-prior optimizing p at s=1 and expurgated s>=1, PDF p.27. -/
def gaussianP (E : ℝ) : ℝ := 1 + 1 / E - gaussianQ E / E

def gaussianExpurgatedP (E s : ℝ) : ℝ := 1 / s + 1 / E - gaussianQ (E / s) / E

example : gaussianQ 0 = 1 := by norm_num [gaussianQ]

end QAlgorithms.Papers.Independent.Renew46.P44


