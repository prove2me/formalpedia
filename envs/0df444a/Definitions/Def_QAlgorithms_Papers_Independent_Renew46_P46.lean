-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P46
-- name    : QAlgorithms_Papers_Independent_Renew46_P46
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T21:46:47.456982+00:00
-- url     : https://prove2.me/theorems/d3bb6c72-2770-46e2-8ece-0e8006d47922
-- title:
--   Definitions for On Quantum Communication Channels with Constrained Inputs
-- statement:
--   The objects the formalized statements of *On Quantum Communication Channels with Constrained Inputs* (arXiv:quant-ph/9705054) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `constrainedCqOperator`: Bounded operators on the completed space, p.1.
--   - `constrainedCqKet`: The fixed orthonormal coordinate basis.
--   - `constrainedCqCoefficient`: Matrix coefficient <i|X|j>, with conjugate-linear first inner argument.
--   - `opTrace`: Trace; every use on a trace-class operator has an absolutely summable diagonal.
--   - `constrainedCqDensity`: Normalized positive trace-class density operators, pp.1,7.
--   - `constrainedCqState`: A density, including its normalization and positivity.
--   - `ofCoefficients`: Unique bounded realization of coefficients when it exists. Every constructed signal theorem below concludes its coefficient realization, so a fallback cannot serve as an unnormalized signal. Tensor and probability barycenters of densities always have bounded realizations.
--   - `constrainedCqEigenvalue`: Approximation numbers, equal to decreasing eigenvalues for positive compact operators. The set is nonempty and bounded below by zero for every X and j.
--   - `constrainedCqEntropy`: Von Neumann entropy in nats, including infinity and 0 log 0 = 0 (pp.3,7). Approximation-number construction matches checked Claimed50.P39.fockEntropyNats, extended here from one Fock space to arbitrary Hilbert-space coordinates.
--   - `wordCoefficients`: Full memoryless word-state coefficients on H tensor n, p.2.
--   - `wordSignal`: Actual bounded tensor-product output for a classical input word, p.2.
--   - `wordCost`: Additive real cost of a word, (3),(7), p.2-3.
--   - `constrainedCqAdmissible`: Genuine signed expectation domain, avoiding a default-zero divergent sum.
--   - `constrainedCqMeasurement`: Discrete resolution of identity, p.1-2. Countable outputs suffice: for any input ensemble only countably many outputs have positive marginal probability; all other outputs can be merged without changing the information.
--   - `outcome`: Executed output probability Tr(S X_j), (1).
--   - `relativeTerm`: Nonnegative scalar relative-entropy summand, with its support boundary. The -p+q correction sums to zero for probability laws.
--   - `constrainedCqInformation`: Shannon information in nats, (1). An extended nonnegative KL expression retains infinite information without summing an undefined signed series.
--   - `constrainedCqBlockCapacity`: Measured n-use capacity with an ensemble-average total-cost bound, (3),(4). The prior can correlate input positions; the measurement is collective.
--   - `constrainedCqCapacity`: Capacity (5), initially an extended limsup; capacityLimit establishes that this is an actual limit. Positive blocklengths are n+1.
--   - `discreteAverage`: Discrete barycenter, (9). On probability laws its coefficient sums converge.
--   - `discreteChi`: Entropy difference (9). Under (8) both terms are finite and subtraction is ordinary nonnegative subtraction, not an infinity-minus-infinity convention.
--   - `EntropyBound`: The uniform bound (8), without optimizer attainment.
--   - `constrainedCqCode`: A finite code and its collective sub-POVM, (6),(7). The residual effect is an erasure; each encoded word satisfies the cost constraint.
--   - `constrainedCqCodeError`: Uniform-message average error; erasure counts as error, (6).
--   - `constrainedCqError`: Infimal operational error; no minimizing code is assumed to exist, p.3. Feasibility and M>0 guarantee a nonempty bounded subset of [0,1].
--   - `constrainedCqMessages`: Integer interpretation of exp(nR), used only at nonnegative rates.
--   - `MeasureAdmissible`: Borel-law admissibility with a genuine signed cost integral, (11).
--   - `constrainedCqAverage`: Weak/operator barycenter (14), defined by actual scalar coefficient integrals.
--   - `constrainedCqChi`: Continuous entropy difference (13); all Borel laws, not just density laws.
--   - `MeasureEntropyBound`: Continuous version of (8).
--   - `WeaklyContinuous`: All matrix elements continuous, exactly the weak continuity on p.5.
--   - `constrainedCqShell`: Product-prior shell probability, (35). Works for arbitrary Borel laws.
--   - `tilted`: Weighted operator integral in (38). The convergence guards below ensure all scalar integrals and the bounded positive operator are genuine.
--   - `WeightedDomain`: A sufficient finite-exponential-moment condition, established for the Gaussian example; the general bounds use their exact convergence domains.
--   - `constrainedCqPowerTrace`: Trace of a positive real power, evaluated spectrally on full Hilbert space.
--   - `mu`: Random exponent functional (34),(38), using the actual weighted operator.
--   - `constrainedCqOverlap`: Phase-independent pure-state overlap Tr(S_x S_y) = |<psi_x|psi_y>|^2.
--   - `overlapIntegrand`: The phase-independent positive overlap integrand in (39).
--   - `overlapIntegral`: Actual double integral in (37),(39), without a density restriction on pi.
--   - `muEx`: Expurgated functional (37),(39).
--   - `reliability`: Extended reliability, p.12; zero error gives +infinity, not log(1/0)=0.
--   - `h`: Thermal entropy function, (22), with its continuous zero value.
--   - `gaussian`: Circular Gaussian of variance V, (20),(28); zero variance is Dirac.
--   - `gaussianSignal`: Concrete displaced thermal signal (20), including the coherent projector at N=0. Its realization/normalization is a conclusion of gaussianSignalMoments.
--   - `constrainedCqThermal`: Thermal number-basis state (21),(32).
--   - `constrainedCqPhotonMean`: Nonnegative extended photon number expectation, never a default-zero sum.
--   - `photonSignal`: Photon channel (29): shift of the thermal diagonal by m, on the full Fock basis. This is P^m S_0 (P*)^m, not a photon cutoff.
--   - `stateFamily`: Turn any realized density family into states. The proof argument is only a normalization certificate; every concrete-channel theorem supplies it as a conclusion.
--   - `photonWeight`: Photon optimizer weights, p.10; the common zero endpoint is delta_0.
--   - `photonPrior`: The actual optimizer measure from the weights, not an assumed probability law.
--   - `energyCost`: Gaussian input cost, (24).
--   - `gaussianMu`: Fixed Gaussian-prior random functional, not a closed-form surrogate for (38).
--   - `gaussianMuEx`: Fixed Gaussian-prior expurgated functional (39).
--   - `q`: Algebraic root denoted g in Section V; distinguished from entropy h.
--   - `bestP`: Optimizing p for fixed s in the expurgated calculation, p.14.
--   - `Avalue`: Common value at s=1, first equality (45).
--   - `Bvalue`: Random-functional s derivative at s=1, second equality (45).
--   - `Lvalue`: Expurgated transition rate, p.15.
--   - `randomEnvelope`: Fixed-prior random envelope, with the exact source parameter domains.
--   - `expurgatedEnvelope`: Fixed-prior expurgated envelope; bounded above and nonempty for E,R>0. No assertion about the defective unrestricted optimization over all priors.
--   - `tiltedDiscrete`: Discrete tilted operator, exactly (34), on the summable-weight domain.
--   - `muDiscrete`: Discrete version of (34), using its actual signal operator.
--   - `overlapTerm`: Prior-weighted discrete overlap summand in (37).
--   - `overlapSum`: Actual double series of (37).
--   - `muExDiscrete`: Discrete expurgated functional, (37). The power is on squared overlap.
--   - `shellDiscrete`: Discrete shell probability from the n-fold product prior, p.11.
--   - `randomDiscreteDomain`: Exact convergence domain for (34): an actual bounded positive weighted operator, with summable positive power trace. Finite scalar exponential mass is not required when the operator power still has a finite trace.
--   - `expurgatedDiscreteDomain`: Exact finite positive overlap-series domain for the real logarithm in (37).
--   - `randomDomain`: Exact convergence domain of (38), including coefficient-integral realization and the finite positive spectral trace of the power.
--   - `expurgatedDomain`: Exact finite positive overlap-integral domain for (39), allowing singular pi. Product integrability ensures that both iterated integrals are genuine a.e.
-- source:
--   On Quantum Communication Channels with Constrained Inputs, arXiv:quant-ph/9705054v1, https://arxiv.org/abs/quant-ph/9705054v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_RealLabelRegisters
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P13
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P39

/-!
Holevo, arXiv:quant-ph/9705054v1, pp.1-15. All logarithms are natural.
The full completed Hilbert carrier, nuclear trace-class predicate, positivity,
and coherent coefficients are imported from the pinned accepted library.
Other local interfaces have paper-specific names: same short names in the
accepted index denote different domains or operational quantities. Only the
source theorem statements below are admitted; local definitions are complete.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P46

open Filter MeasureTheory QAlgorithms.RealRegisters
open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

/-- Bounded operators on the completed space, p.1. -/
abbrev constrainedCqOperator (I : Type) := Hilbert I →L[ℂ] Hilbert I

/-- The fixed orthonormal coordinate basis. -/
def constrainedCqKet {I : Type} (i : I) : Hilbert I := lp.single 2 i 1

/-- Matrix coefficient <i|X|j>, with conjugate-linear first inner argument. -/
def constrainedCqCoefficient {I : Type} (X : constrainedCqOperator I) (i j : I) : ℂ := X (constrainedCqKet j) i

/-- Trace; every use on a trace-class operator has an absolutely summable diagonal. -/
def opTrace {I : Type} (X : constrainedCqOperator I) : ℂ := ∑' i, constrainedCqCoefficient X i i

/-- Normalized positive trace-class density operators, pp.1,7. -/
def constrainedCqDensity {I : Type} (X : constrainedCqOperator I) : Prop :=
  QAlgorithms.Papers.Independent.Dependency50.P13.IsTraceClass X ∧ QAlgorithms.Papers.Independent.Dependency50.P13.IsPositive X ∧ Summable (fun i => constrainedCqCoefficient X i i) ∧ opTrace X = 1

/-- A density, including its normalization and positivity. -/
abbrev constrainedCqState (I : Type) := {X : constrainedCqOperator I // constrainedCqDensity X}

/-- Unique bounded realization of coefficients when it exists. Every constructed
signal theorem below concludes its coefficient realization, so a fallback cannot
serve as an unnormalized signal. Tensor and probability barycenters of densities
always have bounded realizations. -/
def ofCoefficients {I : Type} (a : I → I → ℂ) : constrainedCqOperator I :=
  if h : ∃ X : constrainedCqOperator I, ∀ i j, constrainedCqCoefficient X i j = a i j then
    Classical.choose h else 0

/-- Approximation numbers, equal to decreasing eigenvalues for positive compact
operators. The set is nonempty and bounded below by zero for every X and j. -/
def constrainedCqEigenvalue {I : Type} (X : constrainedCqOperator I) (j : ℕ) : ℝ :=
  sInf {r : ℝ | ∃ u v : Fin j → Hilbert I,
    r = ‖X - ∑ k, InnerProductSpace.rankOne ℂ (u k) (v k)‖}

/-- Von Neumann entropy in nats, including infinity and 0 log 0 = 0 (pp.3,7).
Approximation-number construction matches checked Claimed50.P39.fockEntropyNats,
extended here from one Fock space to arbitrary Hilbert-space coordinates. -/
def constrainedCqEntropy {I : Type} (X : constrainedCqOperator I) : ℝ≥0∞ :=
  ∑' j : ℕ, ENNReal.ofReal (-constrainedCqEigenvalue X j * Real.log (constrainedCqEigenvalue X j))

/-- Full memoryless word-state coefficients on H tensor n, p.2. -/
def wordCoefficients {I A : Type} (S : A → constrainedCqState I) (n : ℕ)
    (u : Fin n → A) (a b : Fin n → I) : ℂ :=
  ∏ k, constrainedCqCoefficient (S (u k)).val (a k) (b k)

/-- Actual bounded tensor-product output for a classical input word, p.2. -/
def wordSignal {I A : Type} (S : A → constrainedCqState I) (n : ℕ)
    (u : Fin n → A) : constrainedCqOperator (Fin n → I) := ofCoefficients (wordCoefficients S n u)

/-- Additive real cost of a word, (3),(7), p.2-3. -/
def wordCost {A : Type} (f : A → ℝ) (n : ℕ) (u : Fin n → A) : ℝ := ∑ k, f (u k)

/-- Genuine signed expectation domain, avoiding a default-zero divergent sum. -/
def constrainedCqAdmissible {A : Type} (f : A → ℝ) (E : ℝ) (pi : PMF A) : Prop :=
  Summable (fun a => (pi a).toReal * |f a|) ∧
    (∑' a, (pi a).toReal * f a) ≤ E

/-- Discrete resolution of identity, p.1-2. Countable outputs suffice: for any
input ensemble only countably many outputs have positive marginal probability;
all other outputs can be merged without changing the information. -/
structure constrainedCqMeasurement (I : Type) where
  effect : ℕ → constrainedCqOperator I
  positive : ∀ j, QAlgorithms.Papers.Independent.Dependency50.P13.IsPositive (effect j)
  complete : ∀ v, HasSum (fun j => effect j v) v

/-- Executed output probability Tr(S X_j), (1). -/
def outcome {I : Type} (S : constrainedCqOperator I) (X : constrainedCqMeasurement I) (j : ℕ) : ℝ :=
  (opTrace ((X.effect j).comp S)).re

/-- Nonnegative scalar relative-entropy summand, with its support boundary.
The -p+q correction sums to zero for probability laws. -/
def relativeTerm (p q : ℝ) : ℝ≥0∞ :=
  if 0 < q then ENNReal.ofReal (p * Real.log (p / q) - p + q)
  else if p = 0 then 0 else ⊤

/-- Shannon information in nats, (1). An extended nonnegative KL expression
retains infinite information without summing an undefined signed series. -/
def constrainedCqInformation {I A : Type} (S : A → constrainedCqOperator I) (pi : PMF A)
    (X : constrainedCqMeasurement I) : ℝ≥0∞ :=
  ∑' a, pi a * ∑' j, relativeTerm (outcome (S a) X j)
    (∑' b, (pi b).toReal * outcome (S b) X j)

/-- Measured n-use capacity with an ensemble-average total-cost bound, (3),(4).
The prior can correlate input positions; the measurement is collective. -/
def constrainedCqBlockCapacity {I A : Type} (S : A → constrainedCqState I) (f : A → ℝ) (E : ℝ)
    (n : ℕ) : ℝ≥0∞ :=
  ⨆ pi : {pi : PMF (Fin n → A) // constrainedCqAdmissible (wordCost f n) ((n : ℝ) * E) pi},
    ⨆ X : constrainedCqMeasurement (Fin n → I), constrainedCqInformation (wordSignal S n) pi.val X

/-- Capacity (5), initially an extended limsup; capacityLimit establishes that
this is an actual limit. Positive blocklengths are n+1. -/
def constrainedCqCapacity {I A : Type} (S : A → constrainedCqState I) (f : A → ℝ) (E : ℝ) : ℝ≥0∞ :=
  Filter.limsup (fun n : ℕ => constrainedCqBlockCapacity S f E (n + 1) / (n + 1 : ℕ)) atTop

/-- Discrete barycenter, (9). On probability laws its coefficient sums converge. -/
def discreteAverage {I A : Type} (S : A → constrainedCqOperator I) (pi : PMF A) : constrainedCqOperator I :=
  ofCoefficients (fun i j => ∑' a, ((pi a).toReal : ℂ) * constrainedCqCoefficient (S a) i j)

/-- Entropy difference (9). Under (8) both terms are finite and subtraction is
ordinary nonnegative subtraction, not an infinity-minus-infinity convention. -/
def discreteChi {I A : Type} (S : A → constrainedCqOperator I) (pi : PMF A) : ℝ≥0∞ :=
  constrainedCqEntropy (discreteAverage S pi) - ∑' a, pi a * constrainedCqEntropy (S a)

/-- The uniform bound (8), without optimizer attainment. -/
def EntropyBound {I A : Type} (S : A → constrainedCqOperator I) (f : A → ℝ) (E : ℝ) : Prop :=
  (⨆ pi : {pi : PMF A // constrainedCqAdmissible f E pi}, constrainedCqEntropy (discreteAverage S pi.val)) < ⊤

/-- A finite code and its collective sub-POVM, (6),(7). The residual effect is
an erasure; each encoded word satisfies the cost constraint. -/
structure constrainedCqCode {I A : Type} (S : A → constrainedCqState I) (f : A → ℝ) (E : ℝ) (n M : ℕ) where
  positive_messages : 0 < M
  word : Fin M → Fin n → A
  affordable : ∀ m, wordCost f n (word m) ≤ (n : ℝ) * E
  effect : Fin M → constrainedCqOperator (Fin n → I)
  positive : ∀ m, QAlgorithms.Papers.Independent.Dependency50.P13.IsPositive (effect m)
  subidentity : QAlgorithms.Papers.Independent.Dependency50.P13.IsPositive (1 - ∑ m, effect m)

/-- Uniform-message average error; erasure counts as error, (6). -/
def constrainedCqCodeError {I A : Type} {S : A → constrainedCqState I} {f : A → ℝ} {E : ℝ} {n M : ℕ}
    (c : constrainedCqCode S f E n M) : ℝ :=
  (∑ m : Fin M, (1 - (opTrace ((c.effect m).comp
    (wordSignal S n (c.word m)))).re)) / (M : ℝ)

/-- Infimal operational error; no minimizing code is assumed to exist, p.3.
Feasibility and M>0 guarantee a nonempty bounded subset of [0,1]. -/
def constrainedCqError {I A : Type} (S : A → constrainedCqState I) (f : A → ℝ) (E : ℝ) (n M : ℕ) : ℝ :=
  sInf {e | ∃ c : constrainedCqCode S f E n M, e = constrainedCqCodeError c}

/-- Integer interpretation of exp(nR), used only at nonnegative rates. -/
def constrainedCqMessages (n : ℕ) (R : ℝ) : ℕ := max 1 ⌊Real.exp ((n : ℝ) * R)⌋₊

/-- Borel-law admissibility with a genuine signed cost integral, (11). -/
def MeasureAdmissible {A : Type} [MeasurableSpace A]
    (f : A → ℝ) (E : ℝ) (pi : Measure A) : Prop :=
  IsProbabilityMeasure pi ∧ Integrable f pi ∧ (∫ x, f x ∂pi) ≤ E

/-- Weak/operator barycenter (14), defined by actual scalar coefficient integrals. -/
def constrainedCqAverage {I A : Type} [MeasurableSpace A] (S : A → constrainedCqOperator I)
    (pi : Measure A) : constrainedCqOperator I :=
  ofCoefficients (fun i j => ∫ x, constrainedCqCoefficient (S x) i j ∂pi)

/-- Continuous entropy difference (13); all Borel laws, not just density laws. -/
def constrainedCqChi {I A : Type} [MeasurableSpace A] (S : A → constrainedCqOperator I)
    (pi : Measure A) : ℝ≥0∞ :=
  constrainedCqEntropy (constrainedCqAverage S pi) - ∫⁻ x, constrainedCqEntropy (S x) ∂pi

/-- Continuous version of (8). -/
def MeasureEntropyBound {I A : Type} [MeasurableSpace A]
    (S : A → constrainedCqOperator I) (f : A → ℝ) (E : ℝ) : Prop :=
  (⨆ pi : {pi : Measure A // MeasureAdmissible f E pi}, constrainedCqEntropy (constrainedCqAverage S pi.val)) < ⊤

/-- All matrix elements continuous, exactly the weak continuity on p.5. -/
def WeaklyContinuous {I A : Type} [TopologicalSpace A] (S : A → constrainedCqOperator I) : Prop :=
  ∀ u v : Hilbert I, Continuous (fun x => inner (𝕜 := ℂ) u (S x v))

/-- Product-prior shell probability, (35). Works for arbitrary Borel laws. -/
def constrainedCqShell {A : Type} [MeasurableSpace A] (pi : Measure A) (f : A → ℝ)
    (E : ℝ) (n : ℕ) (delta : ℝ) : ℝ :=
  ((Measure.pi (fun _ : Fin n => pi))
    {u | (n : ℝ) * E - delta ≤ wordCost f n u ∧ wordCost f n u ≤ (n : ℝ) * E}).toReal

/-- Weighted operator integral in (38). The convergence guards below ensure
all scalar integrals and the bounded positive operator are genuine. -/
def tilted {I A : Type} [MeasurableSpace A] (S : A → constrainedCqOperator I)
    (pi : Measure A) (f : A → ℝ) (E p : ℝ) : constrainedCqOperator I :=
  ofCoefficients (fun i j => ∫ x,
    (Real.exp (p * (f x - E)) : ℂ) * constrainedCqCoefficient (S x) i j ∂pi)

/-- A sufficient finite-exponential-moment condition, established for the
Gaussian example; the general bounds use their exact convergence domains. -/
def WeightedDomain {A : Type} [MeasurableSpace A]
    (pi : Measure A) (f : A → ℝ) (E p : ℝ) : Prop :=
  Integrable (fun x => Real.exp (p * (f x - E))) pi

/-- Trace of a positive real power, evaluated spectrally on full Hilbert space. -/
def constrainedCqPowerTrace {I : Type} (X : constrainedCqOperator I) (r : ℝ) : ℝ :=
  ∑' j : ℕ, (constrainedCqEigenvalue X j) ^ r

/-- Random exponent functional (34),(38), using the actual weighted operator. -/
def mu {I A : Type} [MeasurableSpace A] (S : A → constrainedCqOperator I)
    (pi : Measure A) (f : A → ℝ) (E s p : ℝ) : ℝ :=
  -Real.log (constrainedCqPowerTrace (tilted S pi f E p) (1 + s))

/-- Phase-independent pure-state overlap Tr(S_x S_y) = |<psi_x|psi_y>|^2. -/
def constrainedCqOverlap {I : Type} (X Y : constrainedCqOperator I) : ℝ := (opTrace (X.comp Y)).re

/-- The phase-independent positive overlap integrand in (39). -/
def overlapIntegrand {I A : Type} (S : A → constrainedCqOperator I)
    (f : A → ℝ) (E s p : ℝ) (xy : A × A) : ℝ :=
  Real.exp (p * (f xy.1 + f xy.2 - 2 * E)) *
    (constrainedCqOverlap (S xy.1) (S xy.2)) ^ (1 / s)

/-- Actual double integral in (37),(39), without a density restriction on pi. -/
def overlapIntegral {I A : Type} [MeasurableSpace A] (S : A → constrainedCqOperator I)
    (pi : Measure A) (f : A → ℝ) (E s p : ℝ) : ℝ :=
  ∫ x, ∫ y, overlapIntegrand S f E s p (x, y) ∂pi ∂pi

/-- Expurgated functional (37),(39). -/
def muEx {I A : Type} [MeasurableSpace A] (S : A → constrainedCqOperator I)
    (pi : Measure A) (f : A → ℝ) (E s p : ℝ) : ℝ :=
  -s * Real.log (overlapIntegral S pi f E s p)

/-- Extended reliability, p.12; zero error gives +infinity, not log(1/0)=0. -/
def reliability {I A : Type} (S : A → constrainedCqState I) (f : A → ℝ) (E R : ℝ) : EReal :=
  Filter.limsup (fun k : ℕ =>
    if constrainedCqError S f E (k + 1) (constrainedCqMessages (k + 1) R) = 0 then ⊤
    else ((-Real.log (constrainedCqError S f E (k + 1) (constrainedCqMessages (k + 1) R)) / (k + 1 : ℕ) : ℝ) : EReal)) atTop

/-- Thermal entropy function, (22), with its continuous zero value. -/
def h (N : ℝ) : ℝ := (N + 1) * Real.log (N + 1) - N * Real.log N

/-- Circular Gaussian of variance V, (20),(28); zero variance is Dirac. -/
def gaussian (V : ℝ) : Measure ℂ :=
  if V = 0 then Measure.dirac 0 else volume.withDensity
    (fun z => ENNReal.ofReal (Real.exp (-Complex.normSq z / V) / (Real.pi * V)))

/-- Concrete displaced thermal signal (20), including the coherent projector
at N=0. Its realization/normalization is a conclusion of gaussianSignalMoments. -/
def gaussianSignal (N : ℝ) (alpha : ℂ) : constrainedCqOperator ℕ :=
  ofCoefficients (fun i j => ∫ z : ℂ,
    QAlgorithms.Papers.Independent.Dependency50.P39.coherentCoefficient (z + alpha) i * star (QAlgorithms.Papers.Independent.Dependency50.P39.coherentCoefficient (z + alpha) j) ∂gaussian N)

/-- Thermal number-basis state (21),(32). -/
def constrainedCqThermal (N : ℝ) : constrainedCqOperator ℕ :=
  ofCoefficients (fun i j => if i = j then ((N / (N + 1)) ^ i / (N + 1) : ℝ) else 0)

/-- Nonnegative extended photon number expectation, never a default-zero sum. -/
def constrainedCqPhotonMean (X : constrainedCqOperator ℕ) : ℝ≥0∞ :=
  ∑' m : ℕ, ENNReal.ofReal ((m : ℝ) * (constrainedCqCoefficient X m m).re)

/-- Photon channel (29): shift of the thermal diagonal by m, on the full Fock
basis. This is P^m S_0 (P*)^m, not a photon cutoff. -/
def photonSignal (N : ℝ) (m : ℕ) : constrainedCqOperator ℕ :=
  ofCoefficients (fun i j => if i = j ∧ m ≤ i then
    ((N / (N + 1)) ^ (i - m) / (N + 1) : ℝ) else 0)

/-- Turn any realized density family into states. The proof argument is only a
normalization certificate; every concrete-channel theorem supplies it as a conclusion. -/
def stateFamily {I A : Type} (S : A → constrainedCqOperator I) (hS : ∀ a, constrainedCqDensity (S a)) : A → constrainedCqState I :=
  fun a => ⟨S a, hS a⟩

/-- Photon optimizer weights, p.10; the common zero endpoint is delta_0. -/
def photonWeight (N E : ℝ) (m : ℕ) : ℝ :=
  if N + E = 0 then (if m = 0 then 1 else 0)
  else N / (N + E) * (if m = 0 then 1 else 0) +
    E / (N + E) * (N + E) ^ m / (N + E + 1) ^ (m + 1)

/-- The actual optimizer measure from the weights, not an assumed probability law. -/
def photonPrior (N E : ℝ) : Measure ℕ :=
  Measure.sum (fun m => ENNReal.ofReal (photonWeight N E m) • Measure.dirac m)

/-- Gaussian input cost, (24). -/
def energyCost (alpha : ℂ) : ℝ := Complex.normSq alpha

/-- Fixed Gaussian-prior random functional, not a closed-form surrogate for (38). -/
def gaussianMu (E s p : ℝ) : ℝ := mu (gaussianSignal 0) (gaussian E) energyCost E s p

/-- Fixed Gaussian-prior expurgated functional (39). -/
def gaussianMuEx (E s p : ℝ) : ℝ := muEx (gaussianSignal 0) (gaussian E) energyCost E s p

/-- Algebraic root denoted g in Section V; distinguished from entropy h. -/
def q (E : ℝ) : ℝ := (1 + Real.sqrt (1 + 4 * E ^ 2)) / 2

/-- Optimizing p for fixed s in the expurgated calculation, p.14. -/
def bestP (E s : ℝ) : ℝ := 1 / s + 1 / E - q (E / s) / E

/-- Common value at s=1, first equality (45). -/
def Avalue (E : ℝ) : ℝ := 2 * (E + 1 - q E) + Real.log (q E)

/-- Random-functional s derivative at s=1, second equality (45). -/
def Bvalue (E : ℝ) : ℝ := E + 1 - q E +
  ((q E) ^ 2 * Real.log (q E) - E ^ 2 * Real.log E) / ((q E) ^ 2 - E ^ 2)

/-- Expurgated transition rate, p.15. -/
def Lvalue (E : ℝ) : ℝ := Real.log (q E)

/-- Fixed-prior random envelope, with the exact source parameter domains. -/
def randomEnvelope (E R : ℝ) : ℝ :=
  sSup {v | ∃ s p : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ 0 ≤ p ∧ p < 1 / E ∧
    v = gaussianMu E s p - s * R}

/-- Fixed-prior expurgated envelope; bounded above and nonempty for E,R>0.
No assertion about the defective unrestricted optimization over all priors. -/
def expurgatedEnvelope (E R : ℝ) : ℝ :=
  sSup {v | ∃ s p : ℝ, 1 ≤ s ∧ 0 ≤ p ∧ p < 1 / E ∧
    v = gaussianMuEx E s p - s * R}

/-! Small exact sanity checks. -/

example {A : Type} (f : A → ℝ) (u : Fin 0 → A) : wordCost f 0 u = 0 := by
  simp [wordCost]

example {I A : Type} (S : A → constrainedCqState I) (u : Fin 0 → A) (a b : Fin 0 → I) :
    wordCoefficients S 0 u a b = 1 := by
  simp [wordCoefficients]

example : h 0 = 0 := by simp [h]

example : gaussian 0 = Measure.dirac 0 := by simp [gaussian]

example : photonWeight 0 0 0 = 1 := by simp [photonWeight]

example {I : Type} : ¬ constrainedCqDensity (0 : constrainedCqOperator I) := by
  simp [constrainedCqDensity, opTrace, constrainedCqCoefficient]

/-- Discrete tilted operator, exactly (34), on the summable-weight domain. -/
def tiltedDiscrete {I A : Type} (S : A → constrainedCqOperator I) (pi : PMF A)
    (f : A → ℝ) (E p : ℝ) : constrainedCqOperator I :=
  ofCoefficients (fun i j => ∑' a,
    ((pi a).toReal * Real.exp (p * (f a - E)) : ℝ) * constrainedCqCoefficient (S a) i j)

/-- Discrete version of (34), using its actual signal operator. -/
def muDiscrete {I A : Type} (S : A → constrainedCqOperator I) (pi : PMF A)
    (f : A → ℝ) (E s p : ℝ) : ℝ :=
  -Real.log (constrainedCqPowerTrace (tiltedDiscrete S pi f E p) (1 + s))

/-- Prior-weighted discrete overlap summand in (37). -/
def overlapTerm {I A : Type} (S : A → constrainedCqOperator I) (pi : PMF A)
    (f : A → ℝ) (E s p : ℝ) (ab : A × A) : ℝ :=
  (pi ab.1).toReal * (pi ab.2).toReal * overlapIntegrand S f E s p ab

/-- Actual double series of (37). -/
def overlapSum {I A : Type} (S : A → constrainedCqOperator I) (pi : PMF A)
    (f : A → ℝ) (E s p : ℝ) : ℝ := ∑' a, ∑' b, overlapTerm S pi f E s p (a, b)

/-- Discrete expurgated functional, (37). The power is on squared overlap. -/
def muExDiscrete {I A : Type} (S : A → constrainedCqOperator I) (pi : PMF A)
    (f : A → ℝ) (E s p : ℝ) : ℝ := -s * Real.log (overlapSum S pi f E s p)

/-- Discrete shell probability from the n-fold product prior, p.11. -/
def shellDiscrete {A : Type} (pi : PMF A) (f : A → ℝ) (E : ℝ)
    (n : ℕ) (delta : ℝ) : ℝ :=
  ∑' u : Fin n → A, if (n : ℝ) * E - delta ≤ wordCost f n u ∧
    wordCost f n u ≤ (n : ℝ) * E then ∏ k, (pi (u k)).toReal else 0

/-- Exact convergence domain for (34): an actual bounded positive weighted
operator, with summable positive power trace. Finite scalar exponential mass is
not required when the operator power still has a finite trace. -/
def randomDiscreteDomain {I A : Type} (S : A → constrainedCqOperator I) (pi : PMF A)
    (f : A → ℝ) (E s p : ℝ) : Prop :=
  (∀ i j, Summable (fun a =>
    ((pi a).toReal * Real.exp (p * (f a - E)) : ℂ) * constrainedCqCoefficient (S a) i j)) ∧
  (∀ i j, constrainedCqCoefficient (tiltedDiscrete S pi f E p) i j = ∑' a,
    ((pi a).toReal * Real.exp (p * (f a - E)) : ℂ) * constrainedCqCoefficient (S a) i j) ∧
  QAlgorithms.Papers.Independent.Dependency50.P13.IsPositive (tiltedDiscrete S pi f E p) ∧
  Summable (fun j => (constrainedCqEigenvalue (tiltedDiscrete S pi f E p) j) ^ (1 + s)) ∧
  0 < constrainedCqPowerTrace (tiltedDiscrete S pi f E p) (1 + s)

/-- Exact finite positive overlap-series domain for the real logarithm in (37). -/
def expurgatedDiscreteDomain {I A : Type} (S : A → constrainedCqOperator I) (pi : PMF A)
    (f : A → ℝ) (E s p : ℝ) : Prop :=
  Summable (overlapTerm S pi f E s p) ∧ 0 < overlapSum S pi f E s p

/-- Exact convergence domain of (38), including coefficient-integral realization
and the finite positive spectral trace of the power. -/
def randomDomain {I A : Type} [MeasurableSpace A] (S : A → constrainedCqOperator I)
    (pi : Measure A) (f : A → ℝ) (E s p : ℝ) : Prop :=
  (∀ i j, Integrable (fun x =>
    (Real.exp (p * (f x - E)) : ℂ) * constrainedCqCoefficient (S x) i j) pi) ∧
  (∀ i j, constrainedCqCoefficient (tilted S pi f E p) i j = ∫ x,
    (Real.exp (p * (f x - E)) : ℂ) * constrainedCqCoefficient (S x) i j ∂pi) ∧
  QAlgorithms.Papers.Independent.Dependency50.P13.IsPositive (tilted S pi f E p) ∧
  Summable (fun j => (constrainedCqEigenvalue (tilted S pi f E p) j) ^ (1 + s)) ∧
  0 < constrainedCqPowerTrace (tilted S pi f E p) (1 + s)

/-- Exact finite positive overlap-integral domain for (39), allowing singular pi.
Product integrability ensures that both iterated integrals are genuine a.e. -/
def expurgatedDomain {I A : Type} [MeasurableSpace A] (S : A → constrainedCqOperator I)
    (pi : Measure A) (f : A → ℝ) (E s p : ℝ) : Prop :=
  Integrable (overlapIntegrand S f E s p) (pi.prod pi) ∧
    0 < overlapIntegral S pi f E s p

end QAlgorithms.Papers.Independent.Renew46.P46


