-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P08
-- name    : QAlgorithms_Papers_Independent_Renew46_P08
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-21T02:43:27.272812+00:00
-- url     : https://prove2.me/theorems/19fb22bf-6ab6-4314-9c21-2ab8b19f7907
-- title:
--   Definitions for Tight continuity bounds for the quantum conditional mutual information, for the Holevo quantity and for capacities of quantum channels
-- statement:
--   The objects the formalized statements of *Tight continuity bounds for the quantum conditional mutual information, for the Holevo quantity and for capacities of quantum channels* (arXiv:1512.09047) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `extendedHalfTraceDistance`: PDF p.6: half the FULL trace norm, extended off the trace class. P76.halfDistance instead requires a finite matrix index and returns a real.
--   - `qmi`: PDF p.7, (8): QMI as relative entropy to the product of actual marginals.
--   - `homogeneousQmi`: PDF p.7, after (13): homogeneous QMI, explicitly zero on zero trace. Used only on positive trace-class operators.
--   - `countableMarginalAC`: PDF p.7: AC marginal in the register order A x (B x C), including infinite middle registers. P35.marginalAC instead requires Fintype B.
--   - `FiniteProjection`: PDF p.7, (12): every finite-rank orthogonal projector, including rank zero.
--   - `FiniteProjection.kernel`: PDF p.7: kernel of the actual orthogonal projector onto the given finite range.
--   - `qcmi`: PDF p.7, (12): supremum over ALL finite-rank A-projectors. For every projected positive trace-class input both homogeneous QMIs are finite by the finite rank of A; only these finite values are converted to reals. The outer extended supremum retains infinite QCMI.
--   - `coefficientEnergy`: PDF pp.12–13: actual nonnegative spectral energy, retaining infinity. This coefficient interface also accepts marginals/barycenters before packaging trace-class witnesses; P32.spectralMeanEnergy takes a TraceOperator subtype.
--   - `ground`: PDF p.13: ground energy, used only on nonempty nonnegative spectra.
--   - `SpectralGibbsCondition`: PDF p.12, (30): finite partition trace for EVERY positive inverse temperature.
--   - `entropySupremum`: PDF p.13, (31): entropy supremum over ALL normalized energy-admissible states.
--   - `EntropyMajorant`: PDF p.13, (33)–(34): actual domination and strict derivative/sublinear conditions. No o(sqrt(E)) condition is imported. Nonnegativity on feasible budgets ensures that ofReal faithfully expresses a real upper bound.
--   - `qcmiBoundWith`: PDF p.14, (35): complete QCMI bound with a specified ratio.
--   - `holevoBoundWith`: PDF p.28, (68): complete Holevo bound with a specified ratio.
--   - `oscillatorMain`: PDF pp.16,28, (44),(69): oscillator main term, k=2 for QCMI, k=1 for chi.
--   - `optimizationFactor`: PDF p.17, Lemma 1: the scalar optimization factor.
--   - `countableAverage`: PDF p.20: actual trace-norm average, specified by its convergent coefficients.
--   - `countableHolevo`: PDF p.20: relative-entropy Holevo quantity, with extended nonnegative sum.
--   - `ensembleLaw`: PDF p.21: atomic law identifies repeated states and ignores zero weights.
--   - `distance0`: PDF p.20: D0 is a pseudometric on raw presentations with zero labels.
--   - `distanceStar`: PDF p.21, (53): quotient infimum over presentations of the same atomic laws.
--   - `EHSFeasible`: PDF p.22, (54): TWO arrays; only P's left and Q's right marginals are fixed.
--   - `ehsCost`: PDF p.22, (54): half trace-norm cost for the two EHS arrays.
--   - `distanceEHS`: PDF p.22, (54): EHS infimum, different from single-array transport.
--   - `distanceK`: PDF p.22, (56): ONE coupling array with BOTH marginals fixed.
--   - `WeakConverges`: PDF p.23, (58): weak convergence against all bounded trace-norm continuous real test functions. The probability law and boundedness ensure summability.
--   - `AtMostLabels`: PDF p.22: at most m labels, as a zero-padded presentation.
--   - `countableShannonNats`: PDF p.12: extended Shannon entropy in nats, including zero probabilities.
--   - `qcState`: PDF p.4, (1): actual qc block coefficients with the countable label basis.
--   - `qqcState`: PDF p.11, (26): same qqc state reordered as A x (B x C), B classical.
--   - `marginalChi`: PDF p.12: Holevo quantity of the C-marginal ensemble, without choosing unrelated marginal states or assuming finite entropy.
--   - `UniformChiOn`: PDF p.25: uniform continuity for a specified distance; finiteness precedes all real differences. Raw ordered presentations need only a pseudometric.
--   - `generalizedK`: PDF p.30, (73): all Borel probability couplings, including non-atomic laws.
--   - `FiniteMinDimension`: PDF p.11: finite minimum dimension; no use of default infinite finrank.
-- source:
--   Tight continuity bounds for the quantum conditional mutual information, for the Holevo quantity and for capacities of quantum channels, arXiv:1512.09047v7, https://arxiv.org/abs/1512.09047v7

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P01
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P07
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P08
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P07
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P08

/-!
Shirokov, arXiv:1512.09047v7. Nonempty countable orthonormal-basis labels
represent all separable complex Hilbert spaces and their completed tensor products.
Accepted nuclear states, trace norm, actual partial traces and entropy in nats
are reused. Paper-local definitions have complete bodies. The accepted countable ensemble
and binary convex mixture are imported directly. Distinct countable/extended
interfaces below are not finite-matrix, bit-entropy, or closed-form namesakes;
exact comparisons are recorded in ASSESSMENT.json. Full nodes not yet
expressible, including their sharpness clauses, are individually deferred.
Compilation is pending the separate batch handoff.
-/

noncomputable section

open Filter MeasureTheory
open scoped ENNReal NNReal BigOperators Topology

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Renew46.P08

open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Frontier18.P01
  (CountableStateEnsemble convexOperatorMixture)
open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsDensity traceSize tensorApply productCoeff)
open QAlgorithms.Papers.Independent.Frontier18.P07
  (GeneralizedEnsemble averageCoefficients extendedEntropyNats
    extendedRelativeEntropyNats ensembleHolevo)
open QAlgorithms.Papers.Independent.Frontier18.P08
  (partialTraceFirst partialTraceSecond operatorTrace)
open QAlgorithms.Papers.Independent.Frontier30.P14 (conjugateKernel)
open QAlgorithms.Papers.Independent.Claimed50.P07
  (boundedCoefficients oscillatorGround oscillatorLevels oscillatorEnvelope oscillatorEntropyBounded)
open QAlgorithms.Papers.Independent.Next46.P08 (continuityRatio MajorantRegularity)
open QAlgorithms.Papers.Independent.Claimed50.P39 (g)

/-- PDF p.6: half the FULL trace norm, extended off the trace class.
P76.halfDistance instead requires a finite matrix index and returns a real. -/
def extendedHalfTraceDistance {I : Type} (X Y : Matrix I I ℂ) : ℝ≥0∞ := traceSize (X - Y) / 2

/-- PDF p.7, (8): QMI as relative entropy to the product of actual marginals. -/
def qmi {I J : Type} (X : Matrix (I × J) (I × J) ℂ) : ℝ≥0∞ :=
  extendedRelativeEntropyNats X
    (productCoeff (partialTraceSecond X) (partialTraceFirst X))

/-- PDF p.7, after (13): homogeneous QMI, explicitly zero on zero trace.
Used only on positive trace-class operators. -/
def homogeneousQmi {I J : Type} (X : Matrix (I × J) (I × J) ℂ) : ℝ≥0∞ :=
  let c := operatorTrace X
  if c = 0 then 0 else ENNReal.ofReal c * qmi (((c : ℂ)⁻¹) • X)

/-- PDF p.7: AC marginal in the register order A x (B x C), including
infinite middle registers. P35.marginalAC instead requires Fintype B. -/
def countableMarginalAC {I J K : Type} (X : Matrix (I × (J × K)) (I × (J × K)) ℂ) :
    Matrix (I × K) (I × K) ℂ :=
  fun p q => ∑' j : J, X (p.1, (j, p.2)) (q.1, (j, q.2))

/-- PDF p.7, (12): every finite-rank orthogonal projector, including rank zero. -/
structure FiniteProjection (I : Type) where
  rank : ℕ
  vector : Fin rank → Hilbert I
  orthonormal : Orthonormal ℂ vector

/-- PDF p.7: kernel of the actual orthogonal projector onto the given finite range. -/
def FiniteProjection.kernel {I : Type} (P : FiniteProjection I) : Matrix I I ℂ :=
  fun i j => ∑ k, P.vector k i * star (P.vector k j)

/-- PDF p.7, (12): supremum over ALL finite-rank A-projectors.
For every projected positive trace-class input both homogeneous QMIs are finite
by the finite rank of A; only these finite values are converted to reals.
The outer extended supremum retains infinite QCMI. -/
def qcmi {I J K : Type} (X : Matrix (I × (J × K)) (I × (J × K)) ℂ) : ℝ≥0∞ :=
  ⨆ P : FiniteProjection I,
    let Y := tensorApply (conjugateKernel P.kernel) X
    ENNReal.ofReal ((homogeneousQmi Y).toReal - (homogeneousQmi (countableMarginalAC Y)).toReal)

/-- PDF pp.12–13: actual nonnegative spectral energy, retaining infinity.
This coefficient interface also accepts marginals/barycenters before packaging
trace-class witnesses; P32.spectralMeanEnergy takes a TraceOperator subtype. -/
def coefficientEnergy {I : Type} (e : I → ℝ≥0) (X : Matrix I I ℂ) : ℝ≥0∞ :=
  ∑' i, (e i : ℝ≥0∞) * ENNReal.ofReal (X i i).re

/-- PDF p.13: ground energy, used only on nonempty nonnegative spectra. -/
def ground {I : Type} (e : I → ℝ≥0) : ℝ := sInf (Set.range (fun i => (e i : ℝ)))

/-- PDF p.12, (30): finite partition trace for EVERY positive inverse temperature. -/
def SpectralGibbsCondition {I : Type} (e : I → ℝ≥0) : Prop :=
  ∀ beta : ℝ, 0 < beta → (∑' i, ENNReal.ofReal (Real.exp (-beta * (e i : ℝ)))) < ⊤

/-- PDF p.13, (31): entropy supremum over ALL normalized energy-admissible states. -/
def entropySupremum {I : Type} (e : I → ℝ≥0) (E : ℝ) : ℝ≥0∞ :=
  ⨆ rho : {rho : State I // coefficientEnergy e rho.coefficients ≤ ENNReal.ofReal E},
    extendedEntropyNats rho.val.coefficients

/-- PDF p.13, (33)–(34): actual domination and strict derivative/sublinear
conditions. No o(sqrt(E)) condition is imported. Nonnegativity on feasible
budgets ensures that ofReal faithfully expresses a real upper bound. -/
def EntropyMajorant {I : Type} (e : I → ℝ≥0) (F : ℝ → ℝ) : Prop :=
  MajorantRegularity F ∧ ∀ E : ℝ, ground e ≤ E →
    0 ≤ F E ∧ entropySupremum e E ≤ ENNReal.ofReal (F E)

/-- PDF p.14, (35): complete QCMI bound with a specified ratio. -/
def qcmiBoundWith (F : ℝ → ℝ) (E epsilon t r : ℝ) : ℝ :=
  2 * epsilon * (2 * t + r) * F (E / (epsilon * t)) +
    2 * g (epsilon * r) + 4 * Real.binEntropy (epsilon * t)

/-- PDF p.28, (68): complete Holevo bound with a specified ratio. -/
def holevoBoundWith (F : ℝ → ℝ) (E epsilon t r : ℝ) : ℝ :=
  epsilon * (2 * t + r) * F (E / (epsilon * t)) +
    2 * g (epsilon * r) + 2 * Real.binEntropy (epsilon * t)

/-- PDF pp.16,28, (44),(69): oscillator main term, k=2 for QCMI, k=1 for chi. -/
def oscillatorMain {ell : ℕ} (k hbar : ℝ) (omega : Fin ell → ℝ)
    (E epsilon t : ℝ) : ℝ :=
  k * epsilon * (2 * t + continuityRatio epsilon t) *
    (oscillatorEnvelope hbar omega E - (ell : ℝ) * Real.log (epsilon * t))

/-- PDF p.17, Lemma 1: the scalar optimization factor. -/
def optimizationFactor (t : ℝ) : ℝ := 2 * t + (1 + t / 2) / (1 - t)

/-- PDF p.20: actual trace-norm average, specified by its convergent coefficients. -/
def countableAverage {I : Type} (mu : CountableStateEnsemble I) : Matrix I I ℂ :=
  fun i j => ∑' n, ((mu.weight n).toReal : ℂ) * (mu.state n).coefficients i j

/-- PDF p.20: relative-entropy Holevo quantity, with extended nonnegative sum. -/
def countableHolevo {I : Type} (mu : CountableStateEnsemble I) : ℝ≥0∞ :=
  ∑' n, mu.weight n * extendedRelativeEntropyNats (mu.state n).coefficients (countableAverage mu)

/-- PDF p.21: atomic law identifies repeated states and ignores zero weights. -/
def ensembleLaw {I : Type} (mu : CountableStateEnsemble I) : Measure (State I) :=
  Measure.sum (fun n => mu.weight n • Measure.dirac (mu.state n))

/-- PDF p.20: D0 is a pseudometric on raw presentations with zero labels. -/
def distance0 {I : Type} (mu nu : CountableStateEnsemble I) : ℝ≥0∞ :=
  (∑' n, traceSize (((mu.weight n).toReal : ℂ) • (mu.state n).coefficients -
    ((nu.weight n).toReal : ℂ) • (nu.state n).coefficients)) / 2

/-- PDF p.21, (53): quotient infimum over presentations of the same atomic laws. -/
def distanceStar {I : Type} (mu nu : CountableStateEnsemble I) : ℝ≥0∞ :=
  ⨅ a : {a : CountableStateEnsemble I // ensembleLaw a = ensembleLaw mu},
    ⨅ b : {b : CountableStateEnsemble I // ensembleLaw b = ensembleLaw nu}, distance0 a.val b.val

/-- PDF p.22, (54): TWO arrays; only P's left and Q's right marginals are fixed. -/
def EHSFeasible {I : Type} (mu nu : CountableStateEnsemble I) (P Q : ℕ → ℕ → ℝ≥0∞) : Prop :=
  (∀ i, ∑' j, P i j = mu.weight i) ∧ (∀ j, ∑' i, Q i j = nu.weight j)

/-- PDF p.22, (54): half trace-norm cost for the two EHS arrays. -/
def ehsCost {I : Type} (mu nu : CountableStateEnsemble I) (P Q : ℕ → ℕ → ℝ≥0∞) : ℝ≥0∞ :=
  (∑' i, ∑' j, traceSize (((P i j).toReal : ℂ) • (mu.state i).coefficients -
    ((Q i j).toReal : ℂ) • (nu.state j).coefficients)) / 2

/-- PDF p.22, (54): EHS infimum, different from single-array transport. -/
def distanceEHS {I : Type} (mu nu : CountableStateEnsemble I) : ℝ≥0∞ :=
  ⨅ PQ : {PQ : (ℕ → ℕ → ℝ≥0∞) × (ℕ → ℕ → ℝ≥0∞) //
    EHSFeasible mu nu PQ.1 PQ.2}, ehsCost mu nu PQ.val.1 PQ.val.2

/-- PDF p.22, (56): ONE coupling array with BOTH marginals fixed. -/
def distanceK {I : Type} (mu nu : CountableStateEnsemble I) : ℝ≥0∞ :=
  ⨅ P : {P : ℕ → ℕ → ℝ≥0∞ // EHSFeasible mu nu P P},
    ∑' i, ∑' j, P.val i j * extendedHalfTraceDistance (mu.state i).coefficients (nu.state j).coefficients

/-- PDF p.23, (58): weak convergence against all bounded trace-norm continuous
real test functions. The probability law and boundedness ensure summability. -/
def WeakConverges {I : Type} (mu : ℕ → CountableStateEnsemble I) (mu0 : CountableStateEnsemble I) : Prop :=
  ∀ f : State I → ℝ, Continuous f → (∃ M : ℝ, ∀ rho, |f rho| ≤ M) →
    Tendsto (fun n => ∑' i, ((mu n).weight i).toReal * f ((mu n).state i))
      atTop (nhds (∑' i, (mu0.weight i).toReal * f (mu0.state i)))

/-- PDF p.22: at most m labels, as a zero-padded presentation. -/
def AtMostLabels {I : Type} (m : ℕ) (mu : CountableStateEnsemble I) : Prop :=
  ∀ i, m ≤ i → mu.weight i = 0

/-- PDF p.12: extended Shannon entropy in nats, including zero probabilities. -/
def countableShannonNats (p : ℕ → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' i, ENNReal.ofReal (-(p i).toReal * Real.log (p i).toReal)

/-- PDF p.4, (1): actual qc block coefficients with the countable label basis. -/
def qcState {I : Type} (mu : CountableStateEnsemble I) : Matrix (I × ℕ) (I × ℕ) ℂ :=
  fun p q => if p.2 = q.2 then
    ((mu.weight p.2).toReal : ℂ) * (mu.state p.2).coefficients p.1 q.1 else 0

/-- PDF p.11, (26): same qqc state reordered as A x (B x C), B classical. -/
def qqcState {I K : Type} (mu : CountableStateEnsemble (I × K)) :
    Matrix (I × (ℕ × K)) (I × (ℕ × K)) ℂ :=
  fun p q => qcState mu ((p.1, p.2.2), p.2.1) ((q.1, q.2.2), q.2.1)

/-- PDF p.12: Holevo quantity of the C-marginal ensemble, without choosing
unrelated marginal states or assuming finite entropy. -/
def marginalChi {I K : Type} (mu : CountableStateEnsemble (I × K)) : ℝ≥0∞ :=
  ∑' i, mu.weight i * extendedRelativeEntropyNats
    (partialTraceFirst (mu.state i).coefficients) (partialTraceFirst (countableAverage mu))

/-- PDF p.25: uniform continuity for a specified distance; finiteness precedes
all real differences. Raw ordered presentations need only a pseudometric. -/
def UniformChiOn {I : Type} (D : CountableStateEnsemble I → CountableStateEnsemble I → ℝ≥0∞)
    (S : Set (CountableStateEnsemble I)) : Prop :=
  (∀ mu ∈ S, countableHolevo mu < ⊤) ∧ ∀ eta : ℝ, 0 < eta →
    ∃ delta : ℝ, 0 < delta ∧ ∀ mu ∈ S, ∀ nu ∈ S,
      D mu nu < ENNReal.ofReal delta → |(countableHolevo mu).toReal - (countableHolevo nu).toReal| < eta

/-- PDF p.30, (73): all Borel probability couplings, including non-atomic laws. -/
def generalizedK {I : Type} (mu nu : GeneralizedEnsemble I) : ℝ≥0∞ :=
  ⨅ L : {L : Measure (State I × State I) // IsProbabilityMeasure L ∧
    Measure.map Prod.fst L = (mu : Measure (State I)) ∧
    Measure.map Prod.snd L = (nu : Measure (State I))},
    ∫⁻ p, extendedHalfTraceDistance p.1.coefficients p.2.coefficients ∂L.val

/-- PDF p.11: finite minimum dimension; no use of default infinite finrank. -/
def FiniteMinDimension (I J : Type) (d : ℕ) : Prop :=
  (Finite I ∧ Nat.card I = d ∧ (d : Cardinal) ≤ Cardinal.mk J) ∨
    (Finite J ∧ Nat.card J = d ∧ (d : Cardinal) ≤ Cardinal.mk I)

example {I J : Type} : homogeneousQmi (0 : Matrix (I × J) (I × J) ℂ) = 0 := by
  simp [homogeneousQmi, operatorTrace]

example {I : Type} (e : I → ℝ≥0) : coefficientEnergy e 0 = 0 := by
  simp [coefficientEnergy]

example (t : ℝ) : optimizationFactor t = 2 * t + continuityRatio 1 t := by
  simp [optimizationFactor, continuityRatio]

example (F : ℝ → ℝ) (E t r : ℝ) : qcmiBoundWith F E 0 t r = 0 := by
  simp [qcmiBoundWith, g]

example {I : Type} (mu : CountableStateEnsemble I) (i j : I) (n m : ℕ) (h : n ≠ m) :
    qcState mu (i,n) (j,m) = 0 := by
  simp [qcState, h]

example {I : Type} (mu nu : CountableStateEnsemble I) :
    (∃ a : CountableStateEnsemble I, ensembleLaw a = ensembleLaw mu) ∧
    (∃ b : CountableStateEnsemble I, ensembleLaw b = ensembleLaw nu) := ⟨⟨mu, rfl⟩, ⟨nu, rfl⟩⟩

example {I : Type} (mu nu : CountableStateEnsemble I) (P : ℕ → ℕ → ℝ≥0∞)
    (h : EHSFeasible mu nu P P) :
    (∀ i, ∑' j, P i j = mu.weight i) ∧ (∀ j, ∑' i, P i j = nu.weight j) := h

end QAlgorithms.Papers.Independent.Renew46.P08


