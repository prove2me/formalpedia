-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P32
-- name    : QAlgorithms_Papers_Independent_Advance50_P32
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T13:15:00.79427+00:00
-- url     : https://prove2.me/theorems/6d99d594-d5e4-42e5-adc9-a61c39a53dfa
-- title:
--   Definitions for Squeezing the limit: Quantum benchmarks for the teleportation and storage of squeezed states
-- statement:
--   The objects the formalized statements of *Squeezing the limit: Quantum benchmarks for the teleportation and storage of squeezed states* (arXiv:0808.2260) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `FockOperatorArray`: Section 2, p.3: full coefficient arrays, with separate operator-domain predicates.
--   - `NumberLabel`: Section 2, p.3: the complete n-mode number basis, without a photon cutoff.
--   - `QuadraturePoint`: Section 2, p.3: real (q,p) coordinates for each mode.
--   - `BoundedKernel`: Section 2, p.3: actual bounded operators, pinned by every number-basis entry.
--   - `fockUnitaryConjugation`: Section 2, p.3: bounded-unitary conjugation on complete coordinates.
--   - `oscillatorWeylEntries`: Section 2, p.3: W_xi=exp(i(qP-pX))=D(-(q+ip)/sqrt(2)); exact Fock entries.
--   - `oscillatorNumberConjugation`: Section 4.1, p.5: U_theta=exp(i theta n_hat).
--   - `squeezedAmplitude`: Section 4.1, p.6: the specified squeezed seed, covariance diag(s,1/s), s>0.
--   - `squeezedSeed`: Section 4.1, pp.5–6: actual pure density coefficients, not a covariance witness.
--   - `squeezedOrbit`: Section 4.1, p.5: W_xi U_theta rho_s U_theta* W_xi*.
--   - `priorOrbit`: Section 5.1, p.10: the prior ensemble rotates AFTER displacing the seed.
--   - `heterodyneCoherentState`: Section 4.1, p.7, (18): coherent state prepared at heterodyne outcome xi.
--   - `heterodyne`: Section 4.1, p.7, (18): complex-linear heterodyne map, measure d^2 xi/(2pi). The trace stays complex on nonpositive inputs.
--   - `additiveNoise`: Section 4.2, pp.7–9: covariance noise eta I, displacement variance eta/2. The zero-noise map is explicitly the identity.
--   - `benchmarkChannel`: Sections 3–4, pp.4–6: false selects all EB channels; true selects all channels remaining completely positive after LINEAR matrix transposition. Its trace preservation is automatic and is retained in the channel predicate.
--   - `worstOverlap`: Sections 3–4, pp.4–6: worst case over every displacement and allowed phase.
--   - `flatBenchmark`: Sections 3–4, pp.4–6: choose the channel before the unknown input. No normalized flat Lebesgue probability law is introduced.
--   - `fixedPhaseBenchmark`: Section 4.1, p.7: known phase is fixed before optimizing the strategy.
--   - `PhaseCovariant`: Appendix A, p.17: covariance on EVERY complex trace-class input.
--   - `WeylMultiplier`: Appendix A, p.17: T*(W_xi)=f(xi)W_xi by normal trace duality on ALL trace class.
--   - `ClassicalCharacteristic`: Appendix A, p.17: symplectic Fourier characteristic of any probability law, with the sign in W_eta* W_xi W_eta. No Gaussian restriction.
--   - `ReversibleMultiplier`: Appendix A, p.18, corrected using (15), p.6: quantum characteristic at sqrt(2)xi.
--   - `InputMarginal`: Theorem 4, p.11: full input marginal, including off-diagonal tests. For positive bounded operators this basis formulation is equivalent to all-vector tests.
--   - `inputFirstEntries`: Theorem 4, pp.11,18: input-first coefficients of the accepted OUTPUT-FIRST completed Hilbert tensor operator. Swapping the two ket coordinates is exactly the tensor flip, with no complex conjugation or matrix transposition.
--   - `NormalizedSeparableCJ`: Theorem 4 and Appendix B, pp.11,18: REUSE the accepted normalized weak-operator separable CJ predicate after the tensor flip. Its positivity, all-vector input marginal, and weak approximation by finite positive resolutions are retained. This coordinate transport neither imposes finite rank nor a finite Kraus family.
--   - `NormalizedPPT`: Section 5.2, p.11: bounded positive PPT objects with full normalized input marginal. Partial-transpose positivity is tested on its algebraic finite-support form.
--   - `cjOutput`: Theorem 4, (24), pp.11,18: normal reconstruction on arbitrary trace-class A. Each fixed output entry pairs A with a bounded input block of O. This is the partial-transposed CJ convention: no extra transpose of A appears in (24).
--   - `normalCJPair`: Theorem 4, (24), pp.11,18: the normal trace-dual product pairing. It is NOT the trace of the possibly non-trace-class raw tensor product. Every use below supplies trace class of cjOutput O A.
--   - `CJCorresponds`: Theorem 4, pp.11,18: full trace-class correspondence and ordinary finite-rank tests. Trace-class output makes the B-functional normal and forbids a default-zero trace.
--   - `DisplacementDensity`: Section 5.1, pp.9–10: a genuine Lebesgue probability density; no isotropy is assumed.
--   - `RotationCovariantNoise`: Section 5.1, p.10: genuine rotationally covariant noise, independent of the input.
--   - `averageScore`: Section 5.1, p.10, (23): average overlap under density q and uniform common phase.
--   - `averageBenchmark`: Section 5.1, p.10: optimize over all entanglement-breaking channels.
--   - `ensembleOperator`: Section 5.2, p.11, (26): trace-class ensemble operator, with INPUT FIRST. The same phase rotates both factors. Theorem hypotheses ensure integrability.
--   - `unrotatedEnsemble`: Section 5.2, p.12, (27): ensemble before the common rotation integral.
--   - `separableOptimum`: Section 5.2, p.11, first line of (25): exact normalized separable optimum.
--   - `pptOptimum`: Section 5.2, p.11, second line of (25): infinite PPT relaxation, not EB equality.
--   - `totalNumber`: Section 5.2, p.12: total photon number in the two tensor factors.
--   - `numberBlock`: Section 5.2, p.12, (27): Q_c E Q_c, total number EXACTLY c.
--   - `triangularCut`: Section 5.2, p.12: P_c E P_c, total number at most c (triangular cutoff).
--   - `RectangularLabel`: Section 5.2, p.12: supp R_c has dimension (c+1)^2, including c=0.
--   - `liftRectangular`: Section 5.2, p.12: embed the rectangular cutoff into the complete two-mode basis.
--   - `FinitePPTFeasible`: Theorem 5, p.12, (30): positivity, PPT, and SUBnormalized input marginal.
--   - `finiteObjective`: Theorem 5, p.12: finite objective Tr(O P_c E P_c) on supp R_c.
--   - `finitePPTOptimum`: Theorem 5, p.12: finite SDP optimum, with marginal <= I.
--   - `SymmetricFinitePPTOptimum`: Section 5.2, p.13: lossless total-number symmetry imposed on the finite SDP.
--   - `retainedEnsembleProbability`: Section 5.2, pp.12–13: exact retained probability Tr(P_c E P_c).
--   - `certifiedBound`: Section 5.2, pp.12–13, (30),(31): certified bound includes the omitted probability.
--   - `gaussianPrior`: Section 5.2, p.11: normalized Gaussian displacement density, alpha>0. Alpha=0 is not a probability density and never denotes the flat ensemble.
--   - `measureScore`: Section 5.3, p.15: average under an actual displacement probability law, allowing a point mass at zero rather than treating a delta as a Lebesgue density.
--   - `measureBenchmark`: Section 5.3, p.15: EB optimum for the measure-law ensemble, with identity noise.
--   - `vacuumReplacement`: Section 5.3, p.15: discard the input and prepare the known vacuum. The complex trace makes this a channel on the full complex trace-class domain.
-- source:
--   Squeezing the limit: Quantum benchmarks for the teleportation and storage of squeezed states, arXiv:0808.2260v1, https://arxiv.org/abs/0808.2260v1

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P33
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P39
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P11
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P35
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P32
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P13
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P32

/-!
Owari et al., arXiv:0808.2260v1. Complete Fock coordinates, full complex trace-class
channels, all EB competitors including continuous measurements. Tensor order is
INPUT FIRST, as in (24). Theorem 3 and two remarks are deferred. Lemma 1 is exact
accepted-library reuse with no duplicate theorem. Compilation is pending handoff.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P32

open MeasureTheory Filter
open scoped BigOperators ENNReal Topology TensorProduct
open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33
  (IsTraceClass IsDensity State IsTraceClassChannel BreaksTraceClassEntanglement
   productCoeff traceSize rotationMeasure)
open QAlgorithms.Papers.Independent.Dependency50.P39 (displacementMatrix)
open QAlgorithms.Papers.Independent.Claimed50.P35 (tracePair)
open QAlgorithms.Papers.Independent.Dependency50.P32 (partialTranspose)
open QAlgorithms.Papers.Independent.Next46.P13 (coordinateBasis)
open QAlgorithms.Papers.Independent.Next46.P32 (PositiveKernel vacuum realFockTracePair)

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

/-- Section 2, p.3: full coefficient arrays, with separate operator-domain predicates. -/
abbrev FockOperatorArray (I : Type) := Matrix I I ℂ

/-- Section 2, p.3: the complete n-mode number basis, without a photon cutoff. -/
abbrev NumberLabel (n : ℕ) := Fin n → ℕ

/-- Section 2, p.3: real (q,p) coordinates for each mode. -/
abbrev QuadraturePoint (n : ℕ) := Fin n → ℝ × ℝ

/-- Section 2, p.3: actual bounded operators, pinned by every number-basis entry. -/
def BoundedKernel {I : Type} (K : FockOperatorArray I) : Prop :=
  ∃ A : Hilbert I →L[ℂ] Hilbert I, ∀ i j, A (lp.single 2 j 1) i = K i j

/-- Section 2, p.3: bounded-unitary conjugation on complete coordinates. -/
def fockUnitaryConjugation {I : Type} (U X : FockOperatorArray I) : FockOperatorArray I :=
  fun i j => ∑' a, ∑' b, U i a * X a b * star (U j b)

/-- Section 2, p.3: W_xi=exp(i(qP-pX))=D(-(q+ip)/sqrt(2)); exact Fock entries. -/
def oscillatorWeylEntries (n : ℕ) (xi : QuadraturePoint n) : FockOperatorArray (NumberLabel n) :=
  fun i j => ∏ k, displacementMatrix
    (-(((xi k).1 : ℂ) + Complex.I * ((xi k).2 : ℂ)) / (Real.sqrt 2 : ℂ)) (i k) (j k)

/-- Section 4.1, p.5: U_theta=exp(i theta n_hat). -/
def oscillatorNumberConjugation {n : ℕ} (theta : ℝ) (X : FockOperatorArray (NumberLabel n)) : FockOperatorArray (NumberLabel n) :=
  fun i j => Complex.exp (Complex.I * (theta : ℂ) *
    (((∑ k, i k : ℕ) : ℂ) - ((∑ k, j k : ℕ) : ℂ))) * X i j

/-- Section 4.1, p.6: the specified squeezed seed, covariance diag(s,1/s), s>0. -/
def squeezedAmplitude (s : ℝ) (k : ℕ) : ℝ :=
  if k % 2 = 0 then
    Real.sqrt (2 * Real.sqrt s / (1 + s)) *
      Real.sqrt (Nat.factorial (2 * (k / 2)) : ℝ) / (Nat.factorial (k / 2) : ℝ) *
      ((s - 1) / (2 * s + 2)) ^ (k / 2)
  else 0

/-- Section 4.1, pp.5–6: actual pure density coefficients, not a covariance witness. -/
def squeezedSeed (s : ℝ) : FockOperatorArray (NumberLabel 1) :=
  fun i j => (squeezedAmplitude s (i 0) : ℂ) * (squeezedAmplitude s (j 0) : ℂ)

/-- Section 4.1, p.5: W_xi U_theta rho_s U_theta* W_xi*. -/
def squeezedOrbit (s : ℝ) (xi : ℝ × ℝ) (theta : ℝ) : FockOperatorArray (NumberLabel 1) :=
  fockUnitaryConjugation (oscillatorWeylEntries 1 (fun _ => xi)) (oscillatorNumberConjugation theta (squeezedSeed s))

/-- Section 5.1, p.10: the prior ensemble rotates AFTER displacing the seed. -/
def priorOrbit (s : ℝ) (xi : ℝ × ℝ) (theta : ℝ) : FockOperatorArray (NumberLabel 1) :=
  oscillatorNumberConjugation theta (fockUnitaryConjugation (oscillatorWeylEntries 1 (fun _ => xi)) (squeezedSeed s))

/-- Section 4.1, p.7, (18): coherent state prepared at heterodyne outcome xi. -/
def heterodyneCoherentState (xi : ℝ × ℝ) : FockOperatorArray (NumberLabel 1) :=
  fockUnitaryConjugation (oscillatorWeylEntries 1 (fun _ => xi)) (vacuum 1)

/-- Section 4.1, p.7, (18): complex-linear heterodyne map, measure d^2 xi/(2pi).
The trace stays complex on nonpositive inputs. -/
def heterodyne (X : FockOperatorArray (NumberLabel 1)) : FockOperatorArray (NumberLabel 1) :=
  fun i j => (1 / (2 * Real.pi) : ℂ) *
    ∫ xi : ℝ × ℝ, tracePair X (heterodyneCoherentState xi) * heterodyneCoherentState xi i j

/-- Section 4.2, pp.7–9: covariance noise eta I, displacement variance eta/2.
The zero-noise map is explicitly the identity. -/
def additiveNoise (eta : ℝ) (X : FockOperatorArray (NumberLabel 1)) : FockOperatorArray (NumberLabel 1) :=
  if eta = 0 then X else fun i j => ∫ xi : ℝ × ℝ,
    ((Real.exp (-(xi.1 ^ 2 + xi.2 ^ 2) / eta) / (Real.pi * eta) : ℝ) : ℂ) *
      fockUnitaryConjugation (oscillatorWeylEntries 1 (fun _ => xi)) X i j

/-- Sections 3–4, pp.4–6: false selects all EB channels; true selects all channels
remaining completely positive after LINEAR matrix transposition. Its trace
preservation is automatic and is retained in the channel predicate. -/
def benchmarkChannel (reversible : Bool)
    (T : FockOperatorArray (NumberLabel 1) → FockOperatorArray (NumberLabel 1)) : Prop :=
  IsTraceClassChannel T ∧
    if reversible then IsTraceClassChannel (fun X => T X.transpose)
    else BreaksTraceClassEntanglement T

/-- Sections 3–4, pp.4–6: worst case over every displacement and allowed phase. -/
def worstOverlap (s eta : ℝ) (T : FockOperatorArray (NumberLabel 1) → FockOperatorArray (NumberLabel 1)) : ℝ :=
  sInf {r : ℝ | ∃ (xi : ℝ × ℝ) (theta : ℝ), theta ∈ Set.Icc 0 (2 * Real.pi) ∧
    r = realFockTracePair (T (additiveNoise eta (squeezedOrbit s xi theta))) (squeezedOrbit s xi theta)}

/-- Sections 3–4, pp.4–6: choose the channel before the unknown input.
No normalized flat Lebesgue probability law is introduced. -/
def flatBenchmark (reversible : Bool) (s eta : ℝ) : ℝ :=
  sSup {r : ℝ | ∃ T, benchmarkChannel reversible T ∧ r = worstOverlap s eta T}

/-- Section 4.1, p.7: known phase is fixed before optimizing the strategy. -/
def fixedPhaseBenchmark (reversible : Bool) (s theta : ℝ) : ℝ :=
  sSup {r : ℝ | ∃ T, benchmarkChannel reversible T ∧
    r = sInf {v : ℝ | ∃ xi : ℝ × ℝ,
      v = realFockTracePair (T (squeezedOrbit s xi theta)) (squeezedOrbit s xi theta)}}

/-- Appendix A, p.17: covariance on EVERY complex trace-class input. -/
def PhaseCovariant {n : ℕ}
    (T : FockOperatorArray (NumberLabel n) → FockOperatorArray (NumberLabel n)) : Prop :=
  ∀ xi X, IsTraceClass X →
    T (fockUnitaryConjugation (oscillatorWeylEntries n xi) X) = fockUnitaryConjugation (oscillatorWeylEntries n xi) (T X)

/-- Appendix A, p.17: T*(W_xi)=f(xi)W_xi by normal trace duality on ALL trace class. -/
def WeylMultiplier {n : ℕ}
    (T : FockOperatorArray (NumberLabel n) → FockOperatorArray (NumberLabel n)) (f : QuadraturePoint n → ℂ) : Prop :=
  ∀ xi X, IsTraceClass X →
    tracePair (T X) (oscillatorWeylEntries n xi) = f xi * tracePair X (oscillatorWeylEntries n xi)

/-- Appendix A, p.17: symplectic Fourier characteristic of any probability law,
with the sign in W_eta* W_xi W_eta. No Gaussian restriction. -/
def ClassicalCharacteristic {n : ℕ} (f : QuadraturePoint n → ℂ) : Prop :=
  ∃ mu : Measure (QuadraturePoint n), IsProbabilityMeasure mu ∧
    ∀ xi, f xi = ∫ eta, Complex.exp (-Complex.I *
      ((∑ k, ((xi k).1 * (eta k).2 - (xi k).2 * (eta k).1) : ℝ) : ℂ)) ∂mu

/-- Appendix A, p.18, corrected using (15), p.6: quantum characteristic at sqrt(2)xi. -/
def ReversibleMultiplier {n : ℕ}
    (T : FockOperatorArray (NumberLabel n) → FockOperatorArray (NumberLabel n)) : Prop :=
  ∃ tau : State (NumberLabel n), WeylMultiplier T
    (fun xi => tracePair tau.coefficients (oscillatorWeylEntries n (fun k =>
      (Real.sqrt 2 * (xi k).1, Real.sqrt 2 * (xi k).2))))

example (X : FockOperatorArray (NumberLabel 1)) : additiveNoise 0 X = X := by
  simp [additiveNoise]

example : squeezedAmplitude 1 0 = 1 := by
  norm_num [squeezedAmplitude]

example : squeezedAmplitude 1 2 = 0 := by
  norm_num [squeezedAmplitude]

example (i j : NumberLabel 0) : vacuum 0 i j = 1 := by
  have hi : i = 0 := Subsingleton.elim _ _
  have hj : j = 0 := Subsingleton.elim _ _
  simp [vacuum, hi, hj]

/-- Theorem 4, p.11: full input marginal, including off-diagonal tests.
For positive bounded operators this basis formulation is equivalent to all-vector tests. -/
def InputMarginal {I : Type} (O : FockOperatorArray (I × I)) : Prop :=
  ∀ i j, HasSum (fun k => O (i, k) (j, k)) (if i = j then 1 else 0)

/-- Theorem 4, pp.11,18: input-first coefficients of the accepted OUTPUT-FIRST
completed Hilbert tensor operator. Swapping the two ket coordinates is exactly
the tensor flip, with no complex conjugation or matrix transposition. -/
def inputFirstEntries {I : Type}
    (O : QAlgorithms.Papers.Independent.Frontier18.P11.JointHilbert (Hilbert I) (Hilbert I) →L[ℂ]
      QAlgorithms.Papers.Independent.Frontier18.P11.JointHilbert (Hilbert I) (Hilbert I)) :
    FockOperatorArray (I × I) :=
  fun i j => inner ℂ
    (↑((coordinateBasis I i.2) ⊗ₜ[ℂ] (coordinateBasis I i.1)) :
      QAlgorithms.Papers.Independent.Frontier18.P11.JointHilbert (Hilbert I) (Hilbert I))
    (O (↑((coordinateBasis I j.2) ⊗ₜ[ℂ] (coordinateBasis I j.1)) :
      QAlgorithms.Papers.Independent.Frontier18.P11.JointHilbert (Hilbert I) (Hilbert I)))

/-- Theorem 4 and Appendix B, pp.11,18: REUSE the accepted normalized weak-operator
separable CJ predicate after the tensor flip. Its positivity, all-vector input
marginal, and weak approximation by finite positive resolutions are retained.
This coordinate transport neither imposes finite rank nor a finite Kraus family. -/
def NormalizedSeparableCJ {I : Type} (K : FockOperatorArray (I × I)) : Prop :=
  ∃ O : QAlgorithms.Papers.Independent.Frontier18.P11.JointHilbert (Hilbert I) (Hilbert I) →L[ℂ]
      QAlgorithms.Papers.Independent.Frontier18.P11.JointHilbert (Hilbert I) (Hilbert I),
    QAlgorithms.Papers.Independent.Frontier18.P11.separableCJ (coordinateBasis I) O ∧
      inputFirstEntries O = K

/-- Section 5.2, p.11: bounded positive PPT objects with full normalized input marginal.
Partial-transpose positivity is tested on its algebraic finite-support form. -/
def NormalizedPPT {I : Type} (O : FockOperatorArray (I × I)) : Prop :=
  BoundedKernel O ∧ PositiveKernel O ∧ PositiveKernel (partialTranspose O) ∧ InputMarginal O

/-- Theorem 4, (24), pp.11,18: normal reconstruction on arbitrary trace-class A.
Each fixed output entry pairs A with a bounded input block of O. This is the
partial-transposed CJ convention: no extra transpose of A appears in (24). -/
def cjOutput {I : Type} (O : FockOperatorArray (I × I)) (A : FockOperatorArray I) : FockOperatorArray I :=
  fun k l => ∑' i, ∑' j, A i j * O (j, k) (i, l)

/-- Theorem 4, (24), pp.11,18: the normal trace-dual product pairing.
It is NOT the trace of the possibly non-trace-class raw tensor product.
Every use below supplies trace class of cjOutput O A. -/
def normalCJPair {I : Type} (O : FockOperatorArray (I × I)) (A B : FockOperatorArray I) : ℂ :=
  tracePair (cjOutput O A) B

/-- Theorem 4, pp.11,18: full trace-class correspondence and ordinary finite-rank tests.
Trace-class output makes the B-functional normal and forbids a default-zero trace. -/
def CJCorresponds {I : Type} (T : FockOperatorArray I → FockOperatorArray I) (O : FockOperatorArray (I × I)) : Prop :=
  (∀ A, IsTraceClass A → IsTraceClass (cjOutput O A) ∧ T A = cjOutput O A ∧
    ∀ B, BoundedKernel B → tracePair (T A) B = normalCJPair O A B) ∧
  (∀ i j k l, O (i, k) (j, l) = T (Matrix.single j i 1) k l)

/-- Section 5.1, pp.9–10: a genuine Lebesgue probability density; no isotropy is assumed. -/
def DisplacementDensity (q : ℝ × ℝ → ℝ) : Prop :=
  Measurable q ∧ (∀ xi, 0 ≤ q xi) ∧ Integrable q ∧ (∫ xi, q xi) = 1

/-- Section 5.1, p.10: genuine rotationally covariant noise, independent of the input. -/
def RotationCovariantNoise
    (N : FockOperatorArray (NumberLabel 1) → FockOperatorArray (NumberLabel 1)) : Prop :=
  IsTraceClassChannel N ∧ ∀ theta X, IsTraceClass X →
    N (oscillatorNumberConjugation theta X) = oscillatorNumberConjugation theta (N X)

/-- Section 5.1, p.10, (23): average overlap under density q and uniform common phase. -/
def averageScore (s : ℝ) (q : ℝ × ℝ → ℝ)
    (N T : FockOperatorArray (NumberLabel 1) → FockOperatorArray (NumberLabel 1)) : ℝ :=
  ∫ theta, (∫ xi : ℝ × ℝ, q xi *
    realFockTracePair (T (N (priorOrbit s xi theta))) (priorOrbit s xi theta)) ∂rotationMeasure

/-- Section 5.1, p.10: optimize over all entanglement-breaking channels. -/
def averageBenchmark (s : ℝ) (q : ℝ × ℝ → ℝ)
    (N : FockOperatorArray (NumberLabel 1) → FockOperatorArray (NumberLabel 1)) : ℝ :=
  sSup {r : ℝ | ∃ T, benchmarkChannel false T ∧ r = averageScore s q N T}

/-- Section 5.2, p.11, (26): trace-class ensemble operator, with INPUT FIRST.
The same phase rotates both factors. Theorem hypotheses ensure integrability. -/
def ensembleOperator (s : ℝ) (q : ℝ × ℝ → ℝ)
    (N : FockOperatorArray (NumberLabel 1) → FockOperatorArray (NumberLabel 1)) :
    FockOperatorArray (NumberLabel 1 × NumberLabel 1) :=
  fun i j => ∫ theta, (∫ xi : ℝ × ℝ, (q xi : ℂ) *
    productCoeff (N (priorOrbit s xi theta)) (priorOrbit s xi theta) i j) ∂rotationMeasure

/-- Section 5.2, p.12, (27): ensemble before the common rotation integral. -/
def unrotatedEnsemble (s : ℝ) (q : ℝ × ℝ → ℝ)
    (N : FockOperatorArray (NumberLabel 1) → FockOperatorArray (NumberLabel 1)) :
    FockOperatorArray (NumberLabel 1 × NumberLabel 1) :=
  fun i j => ∫ xi : ℝ × ℝ, (q xi : ℂ) *
    productCoeff (N (priorOrbit s xi 0)) (priorOrbit s xi 0) i j

/-- Section 5.2, p.11, first line of (25): exact normalized separable optimum. -/
def separableOptimum (E : FockOperatorArray (NumberLabel 1 × NumberLabel 1)) : ℝ :=
  sSup {r : ℝ | ∃ O, NormalizedSeparableCJ O ∧ r = realFockTracePair E O}

/-- Section 5.2, p.11, second line of (25): infinite PPT relaxation, not EB equality. -/
def pptOptimum (E : FockOperatorArray (NumberLabel 1 × NumberLabel 1)) : ℝ :=
  sSup {r : ℝ | ∃ O, NormalizedPPT O ∧ r = realFockTracePair E O}

/-- Section 5.2, p.12: total photon number in the two tensor factors. -/
def totalNumber (i : NumberLabel 1 × NumberLabel 1) : ℕ := i.1 0 + i.2 0

/-- Section 5.2, p.12, (27): Q_c E Q_c, total number EXACTLY c. -/
def numberBlock (c : ℕ) (E : FockOperatorArray (NumberLabel 1 × NumberLabel 1)) :
    FockOperatorArray (NumberLabel 1 × NumberLabel 1) :=
  fun i j => if totalNumber i = c ∧ totalNumber j = c then E i j else 0

/-- Section 5.2, p.12: P_c E P_c, total number at most c (triangular cutoff). -/
def triangularCut (c : ℕ) (E : FockOperatorArray (NumberLabel 1 × NumberLabel 1)) :
    FockOperatorArray (NumberLabel 1 × NumberLabel 1) :=
  fun i j => if totalNumber i ≤ c ∧ totalNumber j ≤ c then E i j else 0

/-- Section 5.2, p.12: supp R_c has dimension (c+1)^2, including c=0. -/
abbrev RectangularLabel (c : ℕ) := Fin (c + 1) × Fin (c + 1)

/-- Section 5.2, p.12: embed the rectangular cutoff into the complete two-mode basis. -/
def liftRectangular {c : ℕ} (i : RectangularLabel c) : NumberLabel 1 × NumberLabel 1 :=
  (fun _ => i.1.val, fun _ => i.2.val)

/-- Theorem 5, p.12, (30): positivity, PPT, and SUBnormalized input marginal. -/
def FinitePPTFeasible (c : ℕ) (O : FockOperatorArray (RectangularLabel c)) : Prop :=
  PositiveKernel O ∧ PositiveKernel (partialTranspose O) ∧
    PositiveKernel (fun i j : Fin (c + 1) => (if i = j then 1 else 0) -
      ∑ k : Fin (c + 1), O (i, k) (j, k))

/-- Theorem 5, p.12: finite objective Tr(O P_c E P_c) on supp R_c. -/
def finiteObjective (c : ℕ) (E : FockOperatorArray (NumberLabel 1 × NumberLabel 1))
    (O : FockOperatorArray (RectangularLabel c)) : ℝ :=
  (∑ i, ∑ j, O i j * triangularCut c E (liftRectangular j) (liftRectangular i)).re

/-- Theorem 5, p.12: finite SDP optimum, with marginal <= I. -/
def finitePPTOptimum (c : ℕ) (E : FockOperatorArray (NumberLabel 1 × NumberLabel 1)) : ℝ :=
  sSup {r : ℝ | ∃ O, FinitePPTFeasible c O ∧ r = finiteObjective c E O}

/-- Section 5.2, p.13: lossless total-number symmetry imposed on the finite SDP. -/
def SymmetricFinitePPTOptimum (c : ℕ) (E : FockOperatorArray (NumberLabel 1 × NumberLabel 1)) : ℝ :=
  sSup {r : ℝ | ∃ O, FinitePPTFeasible c O ∧
    (∀ i j : RectangularLabel c, i.1.val + i.2.val ≠ j.1.val + j.2.val → O i j = 0) ∧
    r = finiteObjective c E O}

/-- Section 5.2, pp.12–13: exact retained probability Tr(P_c E P_c). -/
def retainedEnsembleProbability (c : ℕ) (E : FockOperatorArray (NumberLabel 1 × NumberLabel 1)) : ℝ :=
  (∑ i : RectangularLabel c,
    triangularCut c E (liftRectangular i) (liftRectangular i)).re

/-- Section 5.2, pp.12–13, (30),(31): certified bound includes the omitted probability. -/
def certifiedBound (c : ℕ) (E : FockOperatorArray (NumberLabel 1 × NumberLabel 1)) : ℝ :=
  finitePPTOptimum c E + 1 - retainedEnsembleProbability c E

/-- Section 5.2, p.11: normalized Gaussian displacement density, alpha>0.
Alpha=0 is not a probability density and never denotes the flat ensemble. -/
def gaussianPrior (alpha : ℝ) (xi : ℝ × ℝ) : ℝ :=
  alpha / Real.pi * Real.exp (-alpha * (xi.1 ^ 2 + xi.2 ^ 2))

example {I : Type} (O : FockOperatorArray (I × I)) : partialTranspose (partialTranspose O) = O := by
  rfl

example : Fintype.card (RectangularLabel 0) = 1 := by
  simp [RectangularLabel]

example (i : RectangularLabel 0) : totalNumber (liftRectangular i) = 0 := by
  have hi : i.1.val = 0 := by omega
  have hj : i.2.val = 0 := by omega
  simp [totalNumber, liftRectangular, hi, hj]

/-- Section 5.3, p.15: average under an actual displacement probability law,
allowing a point mass at zero rather than treating a delta as a Lebesgue density. -/
def measureScore (s : ℝ) (mu : Measure (ℝ × ℝ))
    (T : FockOperatorArray (NumberLabel 1) → FockOperatorArray (NumberLabel 1)) : ℝ :=
  ∫ theta, (∫ xi, realFockTracePair (T (priorOrbit s xi theta))
    (priorOrbit s xi theta) ∂mu) ∂rotationMeasure

/-- Section 5.3, p.15: EB optimum for the measure-law ensemble, with identity noise. -/
def measureBenchmark (s : ℝ) (mu : Measure (ℝ × ℝ)) : ℝ :=
  sSup {r : ℝ | ∃ T, benchmarkChannel false T ∧ r = measureScore s mu T}

/-- Section 5.3, p.15: discard the input and prepare the known vacuum.
The complex trace makes this a channel on the full complex trace-class domain. -/
def vacuumReplacement (X : FockOperatorArray (NumberLabel 1)) : FockOperatorArray (NumberLabel 1) :=
  (∑' i, X i i) • vacuum 1

end QAlgorithms.Papers.Independent.Advance50.P32


