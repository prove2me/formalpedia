-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P46
-- name    : QAlgorithms_Papers_Independent_Extend50_P46
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T21:03:57.16778+00:00
-- url     : https://prove2.me/theorems/7a2de333-ff9b-45d4-80f8-ec2e03001862
-- title:
--   Definitions for Learning Quantum Processes and Hamiltonians via the Pauli Transfer Matrix
-- statement:
--   The objects the formalized statements of *Learning Quantum Processes and Hamiltonians via the Pauli Transfer Matrix* (arXiv:2212.04471) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `normalizedChoiMatrix`: PDF p.11, Eq.(2.1): normalized reference-first Choi operator of an arbitrary complex-linear superoperator, in the fixed computational bases. The input maximally entangled density has entries delta_(i,j) delta_(k,l) / din.
--   - `ptm`: PDF p.12, Eq.(2.5): the accepted real PTM coordinates.
--   - `HermitianBasis`: PDF p.12, Definition 2.4: a complete Hermitian Hilbert-Schmidt ONB. There are exactly 4^n basis elements; completeness comes from `Module.Basis`.
--   - `coeff`: PDF p.15: real expansion coefficients of a Hermitian operator.
--   - `tm`: PDF p.12, Eq.(2.2): transfer coordinates, output index first.
--   - `basisNorm`: PDF p.16, Eq.(3.10): the maximum operator norm; a nonempty finite range.
--   - `supportCount`: PDF pp.16-19: number of nonzero coefficients, including the identity coefficient.
--   - `predict`: PDF p.16, Eq.(3.3): the estimator computed from the supplied table.
--   - `predictOn`: PDF p.19, Eq.(3.16): estimator using only the supplied known support.
--   - `predictPauli`: PDF p.22: prediction in the source's unnormalized Pauli coefficient lists.
--   - `ChoiLearner`: PDF pp.10,15, Definition 2.10: an actual finite-outcome joint POVM on exactly `copies` fresh normalized Choi states, with a classical report decoder. The unknown channel is absent from every field.
--   - `choiReportEventProbability`: PDF pp.10-11,14-15: the finite Born sum for the preimage of a report event on the actual tensor-power input, without renormalization. Every preimage is a subset of the finite physical outcome space, so no measurability default occurs.
--   - `tableGood`: PDF p.21: the simultaneous absolute-error event on a table of estimates.
--   - `sparseListGood`: PDF pp.23-24: all four guarantees for the finite list computed by thresholding.
--   - `softFactor`: PDF pp.39-41: soft-O suppresses fixed powers of logarithms of the listed parameters. The exponent is quantified uniformly before every instance.
--   - `generalCost`: PDF pp.39-41: the common general-basis sample bound before task-specific factors.
--   - `eigenspaceState`: PDF p.18: (I plus or minus sigma_A)/2^n; `minus` chooses the minus sign.
--   - `hamiltonianCoeff`: PDF p.28: the unnormalized Hamiltonian expansion coefficient.
--   - `singleSite`: PDF p.29: the single-site witness B_j=b and B_k=I for k different from j.
--   - `pauliCoefficientProbe`: PDF p.29, Lemma 6.1: the constructed input state, with +i[Pauli_A,Pauli_B]/2.
--   - `hamiltonianDensityFlow`: PDF p.28, Eq.(6.1): exp(-itH) rho exp(+itH), defined on all real times.
--   - `fullEnsemble`: PDF p.44: all distinct positive Paulis whose output half is nonidentity.
--   - `sparseEnsemble`: PDF p.45: all distinct positive Paulis nonidentity on both halves.
--   - `signedPauli`: PDF pp.44-45: positive and negative halves, paired by the same label.
--   - `shadowValues`: PDF p.43, Eq.(D.2): values averaged over the whole positive half, without repetition, on normalized pure states only.
--   - `shadowParameter`: PDF p.43: the real supremum; its nonempty bounded domain is a conclusion of each theorem that uses it, rather than an implicit default-value assumption.
--   - `choiInputContraction`: PDF pp.46-49: the response tr_input[(rho^T_input tensor I)(I tensor O)], written entrywise with ancilla first. This formula contracts matrix units of rho against the reference/input indices of O.
--   - `likelihoodValues`: PDF pp.46-49: the operational likelihood-ratio values. Only positive baseline-probability branches are included, so no 0/0 convention enters.
--   - `likelihoodParameter`: PDF p.49, Eq.(D.50): Delta, with positive-denominator operational semantics. Nonemptiness and boundedness are explicitly asserted where its bounds are stated.
--   - `choiEnsembleValid`: PDF pp.43-45: the signed enumeration satisfies (i)-(iii). Tensor-product form is already part of `signedPauli`, and its negative half is paired canonically.
--   - `sparseEnsembleValid`: PDF p.45: additional zero input marginal, giving conditions (i)-(v) for this explicitly Pauli-product, hence one-sparse, enumeration.
-- source:
--   Learning Quantum Processes and Hamiltonians via the Pauli Transfer Matrix, arXiv:2212.04471v2, https://arxiv.org/abs/2212.04471v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_MitigationPauliCoordinates
import Definitions.Def_QAlgorithms_Defs_TomographyOutcomes
import Definitions.Def_QAlgorithms_Defs_MatrixDistances

/-!
Statements from Caro, arXiv:2212.04471v2. All pages are PDF pages.
Local definitions implement source-specific operator coordinates and experiments.
No runtime, storage, adaptive-query, or Hamiltonian-oracle claim is hidden in a field.
The omitted nodes and their precise outstanding interfaces are in the unit's HARD.md.
-/

noncomputable section

open MeasureTheory
open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Extend50.P46

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.11, Eq.(2.1): normalized reference-first Choi operator of an arbitrary
complex-linear superoperator, in the fixed computational bases. The input
maximally entangled density has entries delta_(i,j) delta_(k,l) / din. -/
def normalizedChoiMatrix {din dout : ℕ}
    (N : Matrix (Fin din) (Fin din) ℂ →ₗ[ℂ] Matrix (Fin dout) (Fin dout) ℂ) :
    Matrix (Fin din × Fin dout) (Fin din × Fin dout) ℂ :=
  idTensorSuperop (R := Fin din) N
    (Matrix.of fun p q : Fin din × Fin din =>
      if p.1 = p.2 ∧ q.1 = q.2 then (din : ℂ)⁻¹ else 0)

/-- Sanity check for Eq.(2.1): the zero superoperator has zero Choi operator. -/
example (din dout : ℕ) :
    normalizedChoiMatrix (0 : Matrix (Fin din) (Fin din) ℂ →ₗ[ℂ]
      Matrix (Fin dout) (Fin dout) ℂ) = 0 := by
  ext p q
  simp [normalizedChoiMatrix, idTensorSuperop]

/-- PDF p.12, Eq.(2.5): the accepted real PTM coordinates. -/
def ptm {n : ℕ} (N : {F : (Matrix (Qubits n) (Qubits n) ℂ) →ₗ[ℂ] (Matrix (Qubits n) (Qubits n) ℂ) // IsChannel F}) : Matrix (ErrorMitigation.PauliIndex n) (ErrorMitigation.PauliIndex n) ℝ :=
  ErrorMitigation.pauliTransferMatrix N.val

/-- PDF p.12, Definition 2.4: a complete Hermitian Hilbert-Schmidt ONB.
There are exactly 4^n basis elements; completeness comes from `Module.Basis`. -/
structure HermitianBasis (n : ℕ) where
  basis : Module.Basis (Fin (4 ^ n)) ℂ (Matrix (Qubits n) (Qubits n) ℂ)
  hermitian : ∀ i, (basis i).IsHermitian
  orthogonal : ∀ i j, ((basis i) * (basis j)).trace = if i = j then 1 else 0

/-- PDF p.15: real expansion coefficients of a Hermitian operator. -/
def coeff {n : ℕ} (Q : HermitianBasis n) (X : (Matrix (Qubits n) (Qubits n) ℂ)) (i : Fin (4 ^ n)) : ℝ :=
  ((Q.basis i) * X).trace.re

/-- PDF p.12, Eq.(2.2): transfer coordinates, output index first. -/
def tm {n : ℕ} (Q : HermitianBasis n) (N : {F : (Matrix (Qubits n) (Qubits n) ℂ) →ₗ[ℂ] (Matrix (Qubits n) (Qubits n) ℂ) // IsChannel F}) :
    Matrix (Fin (4 ^ n)) (Fin (4 ^ n)) ℝ :=
  fun i j => ((Q.basis i) * N.val (Q.basis j)).trace.re

/-- PDF p.16, Eq.(3.10): the maximum operator norm; a nonempty finite range. -/
def basisNorm {n : ℕ} (Q : HermitianBasis n) : ℝ :=
  sSup (Set.range fun i : Fin (4 ^ n) => specNorm (Q.basis i))

/-- PDF pp.16-19: number of nonzero coefficients, including the identity coefficient. -/
def supportCount {I : Type*} [Fintype I] (f : I → ℝ) : ℕ :=
  (Finset.univ.filter fun i => f i ≠ 0).card

/-- PDF p.16, Eq.(3.3): the estimator computed from the supplied table. -/
def predict {n : ℕ} (Q : HermitianBasis n)
    (r : Matrix (Fin (4 ^ n)) (Fin (4 ^ n)) ℝ) (rho O : (Matrix (Qubits n) (Qubits n) ℂ)) : ℝ :=
  ∑ i, ∑ j, coeff Q O i * r i j * coeff Q rho j

/-- PDF p.19, Eq.(3.16): estimator using only the supplied known support. -/
def predictOn {n : ℕ} (Q : HermitianBasis n)
    (S : Finset (Fin (4 ^ n) × Fin (4 ^ n)))
    (r : Matrix (Fin (4 ^ n)) (Fin (4 ^ n)) ℝ) (rho O : (Matrix (Qubits n) (Qubits n) ℂ)) : ℝ :=
  ∑ p ∈ S, coeff Q O p.1 * r p.1 p.2 * coeff Q rho p.2

/-- PDF p.22: prediction in the source's unnormalized Pauli coefficient lists. -/
def predictPauli {n : ℕ} (r : Matrix (ErrorMitigation.PauliIndex n) (ErrorMitigation.PauliIndex n) ℝ) (rho O : (Matrix (Qubits n) (Qubits n) ℂ)) : ℝ :=
  ∑ A, ∑ B, ErrorMitigation.pauliObservableRow O A * r A B *
    ErrorMitigation.pauliStateVector rho B

/-- PDF pp.10,15, Definition 2.10: an actual finite-outcome joint POVM on
exactly `copies` fresh normalized Choi states, with a classical report decoder.
The unknown channel is absent from every field. -/
structure ChoiLearner (n : ℕ) (Out : Type*) where
  copies : ℕ
  outcomes : ℕ
  measurement : Fin outcomes →
    Matrix (Fin copies → (Qubits n × Qubits n))
      (Fin copies → (Qubits n × Qubits n)) ℂ
  valid : IsPOVM measurement
  decode : Fin outcomes → Out

/-- PDF pp.10-11,14-15: the finite Born sum for the preimage of a report
event on the actual tensor-power input, without renormalization. Every preimage
is a subset of the finite physical outcome space, so no measurability default occurs. -/
def choiReportEventProbability {n : ℕ} {Out : Type*}
    (P : ChoiLearner n Out) (N : {F : (Matrix (Qubits n) (Qubits n) ℂ) →ₗ[ℂ] (Matrix (Qubits n) (Qubits n) ℂ) // IsChannel F}) (E : Set Out) : ℝ :=
  povmEventProb P.measurement (piKron P.copies (idTensorSuperop (R := Qubits n) N.val (pureDensity (maxEntangled n)))) (fun o => P.decode o ∈ E)

/-- PDF p.21: the simultaneous absolute-error event on a table of estimates. -/
def tableGood {I : Type*} (r t : Matrix I I ℝ) (eps : ℝ) : Prop :=
  ∀ i j, |r i j - t i j| ≤ eps

/-- PDF pp.23-24: all four guarantees for the finite list computed by thresholding. -/
def sparseListGood {I : Type*} [Fintype I] (r t : Matrix I I ℝ)
    (eps : ℝ) (s : ℕ) : Prop :=
  (∀ i j, (i,j) ∉ (Finset.univ.filter fun p : I × I => eps / 2 < |r p.1 p.2|) → |t i j| ≤ eps) ∧
  (∀ i j, (i,j) ∈ (Finset.univ.filter fun p : I × I => eps / 2 < |r p.1 p.2|) → eps / 6 < |t i j|) ∧
  (Finset.univ.filter fun p : I × I => eps / 2 < |r p.1 p.2|).card ≤ s ∧
  (∀ i j, (i,j) ∈ (Finset.univ.filter fun p : I × I => eps / 2 < |r p.1 p.2|) → |r i j - t i j| ≤ eps)

/-- PDF pp.39-41: soft-O suppresses fixed powers of logarithms of the
listed parameters. The exponent is quantified uniformly before every instance. -/
def softFactor (p n : ℕ) (eps delta scale : ℝ) : ℝ :=
  (1 + Real.log (n + 2) + |Real.log eps| + |Real.log delta| + Real.log (max 1 scale)) ^ p

/-- PDF pp.39-41: the common general-basis sample bound before task-specific factors. -/
def generalCost {n : ℕ} (Q : HermitianBasis n) (eps delta : ℝ) : ℝ :=
  ((n : ℝ)^3 + n * Real.log delta⁻¹) / eps^4 *
    ((2 : ℝ)^n * basisNorm Q ^ 2)^4

/-- PDF p.18: (I plus or minus sigma_A)/2^n; `minus` chooses the minus sign. -/
def eigenspaceState {n : ℕ} (A : ErrorMitigation.PauliIndex n) (minus : Bool) : (Matrix (Qubits n) (Qubits n) ℂ) :=
  (((2 : ℝ)^n)⁻¹ : ℂ) •
    (1 + (if minus then (-1 : ℂ) else 1) • pauliOps A)

/-- PDF p.28: the unnormalized Hamiltonian expansion coefficient. -/
def hamiltonianCoeff {n : ℕ} (H : (Matrix (Qubits n) (Qubits n) ℂ)) (A : ErrorMitigation.PauliIndex n) : ℝ :=
  ((2 : ℝ)^n)⁻¹ * (H * pauliOps A).trace.re

/-- PDF p.29: the single-site witness B_j=b and B_k=I for k different from j. -/
def singleSite {n : ℕ} (j : Fin n) (b : Stabilizer.Pauli) : ErrorMitigation.PauliIndex n :=
  fun k => if k = j then b else .I

/-- PDF p.29, Lemma 6.1: the constructed input state, with +i[Pauli_A,Pauli_B]/2. -/
def pauliCoefficientProbe {n : ℕ} (A B : ErrorMitigation.PauliIndex n) : (Matrix (Qubits n) (Qubits n) ℂ) :=
  (((2 : ℝ)^n)⁻¹ : ℂ) •
    (1 + (Complex.I / 2) • (pauliOps A * pauliOps B - pauliOps B * pauliOps A))

/-- PDF p.28, Eq.(6.1): exp(-itH) rho exp(+itH), defined on all real times. -/
def hamiltonianDensityFlow {n : ℕ} (H : (Matrix (Qubits n) (Qubits n) ℂ)) (t : ℝ) (rho : (Matrix (Qubits n) (Qubits n) ℂ)) : (Matrix (Qubits n) (Qubits n) ℂ) :=
  NormedSpace.exp ((((-t : ℝ) : ℂ) * Complex.I) • H) * rho *
    NormedSpace.exp (((t : ℂ) * Complex.I) • H)

/-- PDF p.44: all distinct positive Paulis whose output half is nonidentity. -/
def fullEnsemble (n : ℕ) : Finset (ErrorMitigation.PauliIndex n × ErrorMitigation.PauliIndex n) :=
  Finset.univ.filter fun p => p.2 ≠ (fun _ => .I)

/-- PDF p.45: all distinct positive Paulis nonidentity on both halves. -/
def sparseEnsemble (n : ℕ) : Finset (ErrorMitigation.PauliIndex n × ErrorMitigation.PauliIndex n) :=
  Finset.univ.filter fun p => p.1 ≠ (fun _ => .I) ∧ p.2 ≠ (fun _ => .I)

/-- PDF pp.44-45: positive and negative halves, paired by the same label. -/
def signedPauli {n : ℕ} (minus : Bool) (p : ErrorMitigation.PauliIndex n × ErrorMitigation.PauliIndex n) :
    Matrix (Qubits n × Qubits n) (Qubits n × Qubits n) ℂ :=
  (if minus then (-1 : ℂ) else 1) • Matrix.kronecker (pauliOps p.1) (pauliOps p.2)

/-- PDF p.43, Eq.(D.2): values averaged over the whole positive half,
without repetition, on normalized pure states only. -/
def shadowValues {n : ℕ} (S : Finset (ErrorMitigation.PauliIndex n × ErrorMitigation.PauliIndex n)) : Set ℝ :=
  {v | ∃ psi : EuclideanSpace ℂ (Qubits n × Qubits n), IsState psi ∧
    v = (S.card : ℝ)⁻¹ * ∑ p ∈ S,
      (inner ℂ psi (act (signedPauli false p) psi)).re ^ 2}

/-- PDF p.43: the real supremum; its nonempty bounded domain is a conclusion
of each theorem that uses it, rather than an implicit default-value assumption. -/
def shadowParameter {n : ℕ} (S : Finset (ErrorMitigation.PauliIndex n × ErrorMitigation.PauliIndex n)) : ℝ :=
  sSup (shadowValues S)

/-- PDF pp.46-49: the response tr_input[(rho^T_input tensor I)(I tensor O)],
written entrywise with ancilla first. This formula contracts matrix units of rho
against the reference/input indices of O. -/
def choiInputContraction {n a : ℕ}
    (rho : Matrix (Qubits a × Qubits n) (Qubits a × Qubits n) ℂ)
    (O : Matrix (Qubits n × Qubits n) (Qubits n × Qubits n) ℂ) :
    Matrix (Qubits a × Qubits n) (Qubits a × Qubits n) ℂ :=
  fun x y => ∑ i, ∑ j, rho (x.1,i) (y.1,j) * O (i,x.2) (j,y.2)

/-- PDF pp.46-49: the operational likelihood-ratio values. Only positive
baseline-probability branches are included, so no 0/0 convention enters. -/
def likelihoodValues {n : ℕ} (S : Finset (ErrorMitigation.PauliIndex n × ErrorMitigation.PauliIndex n)) : Set ℝ :=
  {v | ∃ a : ℕ,
    ∃ rho : Matrix (Qubits a × Qubits n) (Qubits a × Qubits n) ℂ,
    ∃ psi : EuclideanSpace ℂ (Qubits a × Qubits n),
      IsDensityMatrix rho ∧ IsState psi ∧
      0 < (inner ℂ psi (act (Matrix.kronecker (traceRight rho)
        (1 : (Matrix (Qubits n) (Qubits n) ℂ))) psi)).re ∧
      v = (S.card : ℝ)⁻¹ * ∑ p ∈ S,
        ((inner ℂ psi (act (choiInputContraction rho (signedPauli false p)) psi)).re /
          (inner ℂ psi (act (Matrix.kronecker (traceRight rho)
            (1 : (Matrix (Qubits n) (Qubits n) ℂ))) psi)).re)^2}

/-- PDF p.49, Eq.(D.50): Delta, with positive-denominator operational semantics.
Nonemptiness and boundedness are explicitly asserted where its bounds are stated. -/
def likelihoodParameter {n : ℕ} (S : Finset (ErrorMitigation.PauliIndex n × ErrorMitigation.PauliIndex n)) : ℝ :=
  sSup (likelihoodValues S)

/-- PDF pp.43-45: the signed enumeration satisfies (i)-(iii). Tensor-product
form is already part of `signedPauli`, and its negative half is paired canonically. -/
def choiEnsembleValid {n : ℕ} (S : Finset (ErrorMitigation.PauliIndex n × ErrorMitigation.PauliIndex n)) : Prop :=
  ∀ p ∈ S, ∀ minus : Bool,
    (signedPauli minus p).IsHermitian ∧
    signedPauli minus p * signedPauli minus p = 1 ∧
    (signedPauli minus p).trace = 0 ∧ traceRight (signedPauli minus p) = 0 ∧
    signedPauli (!minus) p = - signedPauli minus p

/-- PDF p.45: additional zero input marginal, giving conditions (i)-(v) for
this explicitly Pauli-product, hence one-sparse, enumeration. -/
def sparseEnsembleValid {n : ℕ} (S : Finset (ErrorMitigation.PauliIndex n × ErrorMitigation.PauliIndex n)) : Prop :=
  choiEnsembleValid S ∧ ∀ p ∈ S, ∀ minus : Bool,
    (Matrix.of fun y z => ∑ x : Qubits n, signedPauli minus p (x,y) (x,z)) =
      (0 : (Matrix (Qubits n) (Qubits n) ℂ))

/-- Sanity check (PDF p.16): zero supplied table gives the zero estimator. -/
example {n : ℕ} (Q : HermitianBasis n) (rho O : (Matrix (Qubits n) (Qubits n) ℂ)) :
    predict Q 0 rho O = 0 := by simp [predict]

/-- Sanity check (PDF p.23): no estimated zero entry passes a positive cutoff. -/
example {I : Type*} [Fintype I] {eps : ℝ} (h : 0 < eps) :
    (Finset.univ.filter fun p : I × I => eps / 2 < |(0 : Matrix I I ℝ) p.1 p.2|) = ∅ := by
  ext p
  simp [show ¬ eps / 2 < 0 by linarith]

/-- Sanity check (PDF p.15): zero-copy inputs are independent of the channel. -/
example {n : ℕ} (N M : {F : (Matrix (Qubits n) (Qubits n) ℂ) →ₗ[ℂ] (Matrix (Qubits n) (Qubits n) ℂ) // IsChannel F}) : piKron 0 (idTensorSuperop (R := Qubits n) N.val (pureDensity (maxEntangled n))) = piKron 0 (idTensorSuperop (R := Qubits n) M.val (pureDensity (maxEntangled n))) := by
  ext x y
  simp [piKron]

/-- Sanity check (PDF pp.46-49): the entrywise response is linear in a zero observable. -/
example {n a : ℕ}
    (rho : Matrix (Qubits a × Qubits n) (Qubits a × Qubits n) ℂ) :
    choiInputContraction rho 0 = 0 := by ext x y; simp [choiInputContraction]

/-- Sanity check (PDF p.18): the plus-state normalization is explicit. -/
example {n : ℕ} (A : ErrorMitigation.PauliIndex n) :
    eigenspaceState A false = (((2 : ℝ)^n)⁻¹ : ℂ) • (1 + pauliOps A) := by
  simp [eigenspaceState]

/-- Sanity check (PDF p.28): zero evolution time is the identity channel. -/
example {n : ℕ} (H rho : (Matrix (Qubits n) (Qubits n) ℂ)) : hamiltonianDensityFlow H 0 rho = rho := by
  simp [hamiltonianDensityFlow]

/-- Sanity check (PDF pp.16-19): a zero coefficient vector has empty support. -/
example {I : Type*} [Fintype I] : supportCount (fun _ : I => (0 : ℝ)) = 0 := by
  simp [supportCount]

end QAlgorithms.Papers.Independent.Extend50.P46


