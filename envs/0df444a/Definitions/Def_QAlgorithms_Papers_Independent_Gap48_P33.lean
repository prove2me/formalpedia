-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P33
-- name    : QAlgorithms_Papers_Independent_Gap48_P33
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-22T04:29:22.805752+00:00
-- url     : https://prove2.me/theorems/bb0d4894-9995-4505-be88-15ac0b05099a
-- title:
--   Definitions for On the von Neumann capacity of noisy quantum channels
-- statement:
--   The objects the formalized statements of *On the von Neumann capacity of noisy quantum channels* (arXiv:quant-ph/9609024) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `ProbabilityWeights`: PDF pp.6,9: finite probability weights, allowing zero-probability labels.
--   - `referenceOutput`: PDF p.5: channel applied only to the signal of the input purification.
--   - `loss`: PDF p.5, (3.9): quantum loss, distinct from classicalized loss.
--   - `informationValues`: PDF p.5, (3.15): values over ALL input densities. Maxima use IsGreatest, avoiding the empty/unbounded real-supremum default and retaining attainment.
--   - `dilationVector`: PDF pp.4,6: isometry from a normalized Kraus family and a pure ancilla.
--   - `dilationReference`: PDF pp.4–5: the same isometry with an untouched, entangled reference.
--   - `discardLast`: PDF p.5: discard the last register of R × (B × E).
--   - `discardMiddle`: PDF p.5: discard the middle register, retaining reference and final environment.
--   - `middleConditionalInformation`: PDF p.5: I(R:E|B), transporting the accepted CMI from ((R,E),B) to R,(B,E).
--   - `mixedChannel`: PDF p.6, (3.20)–(3.22): mixing full maps keeps reference-output correlations.
--   - `productChannel`: PDF p.7: finite product, allowing a different dimension in each register.
--   - `productMarginal`: PDF p.7: actual single-factor marginal of a finite product register.
--   - `referenceFidelity`: PDF p.8, (3.38): squared purification overlap, transporting the accepted Fin-indexed overlap through Fintype.equivFin on both registers; no root fidelity or normalization change.
--   - `classicalLoss`: PDF pp.9,12: classical loss H(record|output).
--   - `pauliDepolarizing`: PDF p.10, (5.2): total nonidentity Pauli probability p, distinct from frozen replacement depolarization. The accepted Z differs by a sign from the printed Z; conjugation is identical.
--   - `phaseFlipChannel`: PDF p.13: partial dephasing with phase-flip probability p, distinct from complete dephasing.
--   - `diagonalSource`: PDF p.10, (5.3): diagonal mixed source q|0><0|+(1-q)|1><1|, distinct from frozen pure/coherent families.
--   - `qBasis`: PDF p.10, (5.5): order Psi-minus, Phi-minus, Phi-plus, Psi-plus; coordinates (reference,signal) transpose the printed (signal,reference).
--   - `depolarizingOutput`: PDF p.11: actual reference-output state on the specified q-purification.
--   - `discriminant`: PDF p.11, (5.14): nonnegative discriminant square root.
--   - `depolarizingSpectrum`: PDF p.11, (5.13): eigenvalue multiset, without artificial sorting.
--   - `classicalInput`: PDF p.12: copying and discarding the label dephases the q-purification.
--   - `classicalOutput`: PDF p.12, (5.21): channel after the eigenbasis was recorded.
--   - `classicalSpectrum`: PDF p.12, (5.23): four probabilities, including the second term 2pq/3.
--   - `measuredLoss`: PDF p.12: classicalized q-family loss is conditional record entropy.
--   - `measurementInformation`: PDF p.13: Shannon mutual information obtained by a specific POVM.
--   - `bellOutputs`: PDF p.13: uniform four-Bell-state ensemble after the Pauli channel.
--   - `bellMeasurement`: PDF p.13: projective Bell measurement on reference and output jointly.
--   - `pauliLabel`: PDF pp.13–14: phase-free Pauli representatives.
--   - `ErrorWords`: PDF p.14: distinct Pauli errors of weight at most t.
--   - `pauliWord`: PDF p.14: tensor Pauli on the n transmitted qubits.
--   - `ordinaryDescendants`: PDF p.14: ordinary Pauli error descendants of actual codewords.
--   - `extendedDescendants`: PDF p.14, (6.11): errors act on Q only; the first reference factor is noiseless.
--   - `OrdinaryCode`: PDF p.14: exact nondegenerate codes have orthonormal error descendants.
--   - `ExtendedCode`: PDF p.14: inherited exact orthogonal-packing hypothesis for Q tensor R.
--   - `ballVolume`: PDF pp.13–14: binary or Pauli error-ball volume (a=1 or a=3).
--   - `BinaryCode`: PDF p.13: binary codewords whose radius-t Hamming balls are pairwise disjoint.
--   - `messageRate`: PDF pp.13–14: message-bit rate k/n; distinct from operational optimized rates. n=0 is unused in finite claims.
--   - `binomialLowerTail`: PDF p.14, (6.6): binomial LOWER-tail probability with an integer cutoff; the accepted binomialTail is an UPPER tail.
--   - `binaryDivergence`: PDF p.14, (6.6): binary relative entropy in bits; used for 0<r<1.
-- source:
--   On the von Neumann capacity of noisy quantum channels, arXiv:quant-ph/9609024v3, https://arxiv.org/abs/quant-ph/9609024v3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P03
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P19
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P24
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P40
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P45
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P27

/-! Adami–Cerf, arXiv:quant-ph/9609024v3. Finite nonempty registers, entropy in bits.
References precede signals, transposing the printed Q,R order. The accepted finite
Kraus model is equivalent to an independent pure ancilla with unitary interaction.
Compilation and independent moderation are pending the batch handoff. -/

namespace QAlgorithms.Papers.Independent.Gap48.P33

open scoped BigOperators Matrix ComplexConjugate

-- Reuse only definitions from the pinned accepted library; no imported theorem is used.
open QAlgorithms.Papers.Independent.Information100.P27 (shannon average labelInformation)
open QAlgorithms.Papers.Independent.Information100.P08 (canonicalPurification)
open QAlgorithms.Papers.Independent.Dependency50.P19 (mutualInformation first both)
open QAlgorithms.Papers.Independent.Dependency50.P24 (cqState)
open QAlgorithms.Papers.Independent.Dependency50.P45 (entropyExchange inputMutualInfo)
open QAlgorithms.Papers.Independent.Claimed50.P03 (pauliWeight wordSupport)

/-- PDF pp.6,9: finite probability weights, allowing zero-probability labels. -/
def ProbabilityWeights {J : Type*} [Fintype J] (w : J → ℝ) : Prop :=
  (∀ j, 0 ≤ w j) ∧ ∑ j, w j = 1

/-- PDF p.5: channel applied only to the signal of the input purification. -/
noncomputable def referenceOutput {A B : Type} [Fintype A] [DecidableEq A]
    (N : Superop A B) (rho : Matrix A A ℂ) : Matrix (A × B) (A × B) ℂ :=
  idTensorSuperop N (pureDensity (canonicalPurification rho))

/-- PDF p.5, (3.9): quantum loss, distinct from classicalized loss. -/
noncomputable def loss {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (N : Superop A B) (rho : Matrix A A ℂ) : ℝ :=
  vnEntropy rho + entropyExchange N rho - vnEntropy (N rho)

/-- PDF p.5, (3.15): values over ALL input densities. Maxima use IsGreatest,
avoiding the empty/unbounded real-supremum default and retaining attainment. -/
def informationValues {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (N : Superop A B) : Set ℝ :=
  {z | ∃ rho : Matrix A A ℂ, IsDensityMatrix rho ∧ z = inputMutualInfo N rho}

/-- PDF pp.4,6: isometry from a normalized Kraus family and a pure ancilla. -/
noncomputable def dilationVector {A B K : Type*} [Fintype A]
    (E : K → Matrix B A ℂ) (psi : EuclideanSpace ℂ A) : EuclideanSpace ℂ (B × K) :=
  WithLp.toLp 2 fun bk => ∑ a, E bk.2 bk.1 a * psi a

/-- PDF pp.4–5: the same isometry with an untouched, entangled reference. -/
noncomputable def dilationReference {R A B K : Type*} [Fintype A]
    (E : K → Matrix B A ℂ) (psi : EuclideanSpace ℂ (R × A)) :
    EuclideanSpace ℂ (R × (B × K)) :=
  WithLp.toLp 2 fun rbk => ∑ a, E rbk.2.2 rbk.2.1 a * psi (rbk.1, a)

/-- PDF p.5: discard the last register of R × (B × E). -/
def discardLast {R B E : Type*} [Fintype E]
    (rho : Matrix (R × (B × E)) (R × (B × E)) ℂ) : Matrix (R × B) (R × B) ℂ :=
  Matrix.of fun rb rb2 => ∑ e, rho (rb.1, (rb.2, e)) (rb2.1, (rb2.2, e))

/-- PDF p.5: discard the middle register, retaining reference and final environment. -/
def discardMiddle {R B E : Type*} [Fintype B]
    (rho : Matrix (R × (B × E)) (R × (B × E)) ℂ) : Matrix (R × E) (R × E) ℂ :=
  Matrix.of fun re re2 => ∑ b, rho (re.1, (b, re.2)) (re2.1, (b, re2.2))

/-- PDF p.5: I(R:E|B), transporting the accepted CMI from ((R,E),B) to R,(B,E). -/
noncomputable def middleConditionalInformation {R B E : Type*}
    [Fintype R] [Fintype B] [Fintype E]
    [DecidableEq R] [DecidableEq B] [DecidableEq E]
    (rho : Matrix (R × (B × E)) (R × (B × E)) ℂ) : ℝ :=
  let reordered : Matrix ((R × E) × B) ((R × E) × B) ℂ :=
    fun x y => rho (x.1.1, (x.2, x.1.2)) (y.1.1, (y.2, y.1.2))
  QAlgorithms.Papers.Independent.Dependency50.P19.conditionalMutual reordered

/-- PDF p.6, (3.20)–(3.22): mixing full maps keeps reference-output correlations. -/
noncomputable def mixedChannel {J A B : Type} [Fintype J]
    (w : J → ℝ) (N : J → Superop A B) : Superop A B :=
  fun rho => average w (fun j => N j rho)

/-- PDF p.7: finite product, allowing a different dimension in each register. -/
noncomputable def productChannel {n : ℕ} {A B : Fin n → Type*}
    [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    (N : ∀ i, Superop (A i) (B i)) : Superop (∀ i, A i) (∀ i, B i) :=
  fun rho => Matrix.of fun y y2 =>
    ∑ x : ∀ i, A i, ∑ x2 : ∀ i, A i,
      rho x x2 * ∏ i, N i (Matrix.single (x i) (x2 i) 1) (y i) (y2 i)

/-- PDF p.7: actual single-factor marginal of a finite product register. -/
noncomputable def productMarginal {n : ℕ} {A : Fin n → Type*}
    [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    (rho : Matrix (∀ i, A i) (∀ i, A i) ℂ) (i : Fin n) : Matrix (A i) (A i) ℂ :=
  Matrix.of fun a b => ∑ x : ∀ j, A j,
    if x i = a then rho x (Function.update x i b) else 0

/-- PDF p.8, (3.38): squared purification overlap, transporting the accepted Fin-indexed overlap
through Fintype.equivFin on both registers; no root fidelity or normalization change. -/
noncomputable def referenceFidelity {R A : Type*} [Fintype R] [Fintype A]
    (N : Superop A A) (psi : EuclideanSpace ℂ (R × A)) : ℝ :=
  let r := Fintype.equivFin R
  let a := Fintype.equivFin A
  let psiFin : EuclideanSpace ℂ (Fin (Fintype.card R) × Fin (Fintype.card A)) :=
    WithLp.toLp 2 fun x => psi (r.symm x.1, a.symm x.2)
  let channelFin : Superop (Fin (Fintype.card A)) (Fin (Fintype.card A)) :=
    fun X i j => N (fun x y => X (a x) (a y)) (a.symm i) (a.symm j)
  QAlgorithms.Papers.Independent.Dependency50.P40.purificationFidelity psiFin channelFin

/-- PDF pp.9,12: classical loss H(record|output). -/
noncomputable def classicalLoss {J A : Type} [Fintype J] [Fintype A]
    [DecidableEq J] [DecidableEq A] (w : J → ℝ) (rho : J → Matrix A A ℂ) : ℝ :=
  vnEntropy (cqState w rho) - vnEntropy (average w rho)

/-- PDF p.10, (5.2): total nonidentity Pauli probability p, distinct from frozen replacement depolarization.
The accepted Z differs by a sign from the printed Z; conjugation is identical. -/
noncomputable def pauliDepolarizing (p : ℝ) : Superop Bool Bool :=
  fun rho => ((1 - p : ℝ) : ℂ) • rho + ((p / 3 : ℝ) : ℂ) •
    (pauliX * rho * pauliXᴴ + pauliY * rho * pauliYᴴ + pauliZ * rho * pauliZᴴ)

/-- PDF p.13: partial dephasing with phase-flip probability p, distinct from complete dephasing. -/
noncomputable def phaseFlipChannel (p : ℝ) : Superop Bool Bool :=
  fun rho => ((1 - p : ℝ) : ℂ) • rho + (p : ℂ) • (pauliZ * rho * pauliZᴴ)

/-- PDF p.10, (5.3): diagonal mixed source q|0><0|+(1-q)|1><1|, distinct from frozen pure/coherent families. -/
noncomputable def diagonalSource (q : ℝ) : Matrix Bool Bool ℂ :=
  Matrix.diagonal fun b => if b then ((1 - q : ℝ) : ℂ) else (q : ℂ)

/-- PDF p.10, (5.5): order Psi-minus, Phi-minus, Phi-plus, Psi-plus;
coordinates (reference,signal) transpose the printed (signal,reference). -/
noncomputable def qBasis (j : Fin 4) (q : ℝ) : EuclideanSpace ℂ (Bool × Bool) :=
  WithLp.toLp 2 fun rq =>
    if j = 0 then
      if rq = (false, true) then (Real.sqrt (1 - q) : ℂ)
      else if rq = (true, false) then -(Real.sqrt q : ℂ) else 0
    else if j = 1 then
      if rq = (false, false) then (Real.sqrt (1 - q) : ℂ)
      else if rq = (true, true) then -(Real.sqrt q : ℂ) else 0
    else if j = 2 then
      if rq = (false, false) then (Real.sqrt q : ℂ)
      else if rq = (true, true) then (Real.sqrt (1 - q) : ℂ) else 0
    else
      if rq = (false, true) then (Real.sqrt q : ℂ)
      else if rq = (true, false) then (Real.sqrt (1 - q) : ℂ) else 0

/-- PDF p.11: actual reference-output state on the specified q-purification. -/
noncomputable def depolarizingOutput (p q : ℝ) : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  idTensorSuperop (pauliDepolarizing p) (pureDensity (qBasis 0 q))

/-- PDF p.11, (5.14): nonnegative discriminant square root. -/
noncomputable def discriminant (p q : ℝ) : ℝ :=
  Real.sqrt ((1 - 2 * p / 3) ^ 2 - (16 / 3 : ℝ) * p * (1 - p) * q * (1 - q))

/-- PDF p.11, (5.13): eigenvalue multiset, without artificial sorting. -/
noncomputable def depolarizingSpectrum (p q : ℝ) : Fin 4 → ℝ :=
  ![2 * p * (1 - q) / 3, 2 * p * q / 3,
    (1 - 2 * p / 3 + discriminant p q) / 2,
    (1 - 2 * p / 3 - discriminant p q) / 2]

/-- PDF p.12: copying and discarding the label dephases the q-purification. -/
noncomputable def classicalInput (q : ℝ) : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  Matrix.of fun a b => if a = b then pureDensity (qBasis 0 q) a b else 0

/-- PDF p.12, (5.21): channel after the eigenbasis was recorded. -/
noncomputable def classicalOutput (p q : ℝ) : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  idTensorSuperop (pauliDepolarizing p) (classicalInput q)

/-- PDF p.12, (5.23): four probabilities, including the second term 2pq/3. -/
noncomputable def classicalSpectrum (p q : ℝ) : Fin 4 → ℝ :=
  ![2 * p * (1 - q) / 3, 2 * p * q / 3,
    (1 - 2 * p / 3) * (1 - q), (1 - 2 * p / 3) * q]

/-- PDF p.12: classicalized q-family loss is conditional record entropy. -/
noncomputable def measuredLoss (p q : ℝ) : ℝ :=
  vnEntropy (classicalOutput p q) - vnEntropy (traceLeft (classicalOutput p q))

/-- PDF p.13: Shannon mutual information obtained by a specific POVM. -/
noncomputable def measurementInformation {J O A : Type} [Fintype J] [Fintype O] [Fintype A]
    (w : J → ℝ) (rho : J → Matrix A A ℂ) (M : O → Matrix A A ℂ) : ℝ :=
  shannon (fun o => ∑ j, w j * effectProb (M o) (rho j)) -
    ∑ j, w j * shannon (fun o => effectProb (M o) (rho j))

/-- PDF p.13: uniform four-Bell-state ensemble after the Pauli channel. -/
noncomputable def bellOutputs (p : ℝ) (j : Fin 4) : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  idTensorSuperop (pauliDepolarizing p) (pureDensity (qBasis j (1 / 2)))

/-- PDF p.13: projective Bell measurement on reference and output jointly. -/
noncomputable def bellMeasurement (j : Fin 4) : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  pureDensity (qBasis j (1 / 2))

/-- PDF pp.13–14: phase-free Pauli representatives. -/
def pauliLabel (j : Fin 4) : Matrix Bool Bool ℂ :=
  if j = 0 then 1 else if j = 1 then pauliX else if j = 2 then pauliY else pauliZ

/-- PDF p.14: distinct Pauli errors of weight at most t. -/
def ErrorWords (n t : ℕ) := {e : Fin n → Fin 4 // pauliWeight e ≤ t}

/-- PDF p.14: tensor Pauli on the n transmitted qubits. -/
noncomputable def pauliWord {n : ℕ} (e : Fin n → Fin 4) : Matrix (Qubits n) (Qubits n) ℂ :=
  Matrix.of fun a b => ∏ i, pauliLabel (e i) (a i) (b i)

/-- PDF p.14: ordinary Pauli error descendants of actual codewords. -/
noncomputable def ordinaryDescendants {n k t : ℕ}
    (v : Fin (2 ^ k) → EuclideanSpace ℂ (Qubits n))
    (je : Fin (2 ^ k) × ErrorWords n t) : EuclideanSpace ℂ (Qubits n) :=
  act (pauliWord je.2.1) (v je.1)

/-- PDF p.14, (6.11): errors act on Q only; the first reference factor is noiseless. -/
noncomputable def extendedDescendants {n k t : ℕ}
    (v : Fin (2 ^ k) → EuclideanSpace ℂ (Qubits n × Qubits n))
    (je : Fin (2 ^ k) × ErrorWords n t) : EuclideanSpace ℂ (Qubits n × Qubits n) :=
  act (Matrix.kronecker (1 : Matrix (Qubits n) (Qubits n) ℂ) (pauliWord je.2.1)) (v je.1)

/-- PDF p.14: exact nondegenerate codes have orthonormal error descendants. -/
def OrdinaryCode (n k t : ℕ) : Prop :=
  ∃ v : Fin (2 ^ k) → EuclideanSpace ℂ (Qubits n),
    Orthonormal ℂ (ordinaryDescendants (t := t) v)

/-- PDF p.14: inherited exact orthogonal-packing hypothesis for Q tensor R. -/
def ExtendedCode (n k t : ℕ) : Prop :=
  ∃ v : Fin (2 ^ k) → EuclideanSpace ℂ (Qubits n × Qubits n),
    Orthonormal ℂ (extendedDescendants (t := t) v)

/-- PDF pp.13–14: binary or Pauli error-ball volume (a=1 or a=3). -/
def ballVolume (a n t : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (t + 1), a ^ i * n.choose i

/-- PDF p.13: binary codewords whose radius-t Hamming balls are pairwise disjoint. -/
def BinaryCode (n k t : ℕ) : Prop :=
  ∃ v : Fin (2 ^ k) → (Fin n → Bool),
    ∀ j l, j ≠ l → ∀ x : Fin n → Bool,
      ¬ ((Finset.univ.filter (fun i => x i ≠ v j i)).card ≤ t ∧
         (Finset.univ.filter (fun i => x i ≠ v l i)).card ≤ t)

/-- PDF pp.13–14: message-bit rate k/n; distinct from operational optimized rates. n=0 is unused in finite claims. -/
noncomputable def messageRate (k n : ℕ) : ℝ := (k : ℝ) / (n : ℝ)

/-- PDF p.14, (6.6): binomial LOWER-tail probability with an integer cutoff; the accepted binomialTail is an UPPER tail. -/
noncomputable def binomialLowerTail (r : ℝ) (n t : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (t + 1), (n.choose i : ℝ) * r ^ i * (1 - r) ^ (n - i)

/-- PDF p.14, (6.6): binary relative entropy in bits; used for 0<r<1. -/
noncomputable def binaryDivergence (p r : ℝ) : ℝ :=
  p * Real.logb 2 (p / r) + (1 - p) * Real.logb 2 ((1 - p) / (1 - r))

/-! Small sanity cases for the local interfaces. Target statements below are unproved. -/

example : shannon (fun _ : Unit => (1 : ℝ)) = 0 := by simp [shannon]

example : ProbabilityWeights (fun _ : Unit => (1 : ℝ)) := by simp [ProbabilityWeights]

example {A : Type} (rho : Matrix A A ℂ) :
    average (fun _ : Unit => (1 : ℝ)) (fun _ => rho) = rho := by simp [average]

example {A B : Type*} (rho : Matrix (A × B) (A × B) ℂ) :
    first (id : Superop A A) rho = rho := by rfl

example (rho : Matrix Bool Bool ℂ) : pauliDepolarizing 0 rho = rho := by simp [pauliDepolarizing]

example (rho : Matrix Bool Bool ℂ) : phaseFlipChannel 0 rho = rho := by simp [phaseFlipChannel]

example : qBasis 0 0 (false, true) = 1 := by simp [qBasis]

example : qBasis 0 0 (true, false) = 0 := by simp [qBasis]

example : classicalSpectrum 0 (1 / 2) = ![0, 0, 1 / 2, 1 / 2] := by
  norm_num [classicalSpectrum]

example : pauliWeight (fun _ : Fin 0 => (0 : Fin 4)) = 0 := by simp [pauliWeight, wordSupport]

example (n : ℕ) : ballVolume 3 n 0 = 1 := by simp [ballVolume]

example (r : ℝ) : binomialLowerTail r 0 0 = 1 := by simp [binomialLowerTail]

example : canonicalPurification (1 : Matrix Unit Unit ℂ) ((), ()) = 1 := by simp [canonicalPurification]

example {A : Type} [Fintype A] [DecidableEq A] (rho : Matrix A A ℂ) :
    referenceOutput (id : Superop A A) rho = pureDensity (canonicalPurification rho) := by rfl

example {A : Type*} [Fintype A] [DecidableEq A] (rho : Matrix A A ℂ) :
    loss (id : Superop A A) rho = entropyExchange (id : Superop A A) rho := by simp [loss]

example {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (N : Superop A B) (rho : Matrix A A ℂ) (hrho : IsDensityMatrix rho) :
    inputMutualInfo N rho ∈ informationValues N := ⟨rho, hrho, rfl⟩

example (psi : EuclideanSpace ℂ Unit) :
    dilationVector (fun _ : Unit => (1 : Matrix Unit Unit ℂ)) psi ((), ()) = psi () := by
  simp [dilationVector]

example (psi : EuclideanSpace ℂ (Unit × Unit)) :
    dilationReference (fun _ : Unit => (1 : Matrix Unit Unit ℂ)) psi ((), ((), ())) =
      psi ((), ()) := by simp [dilationReference]

example {R B : Type*} (rho : Matrix (R × (B × Unit)) (R × (B × Unit)) ℂ)
    (r s : R) (b c : B) :
    discardLast rho (r, b) (s, c) = rho (r, (b, ())) (s, (c, ())) := by
  simp [discardLast]

example {R E : Type*} (rho : Matrix (R × (Unit × E)) (R × (Unit × E)) ℂ)
    (r s : R) (e f : E) :
    discardMiddle rho (r, e) (s, f) = rho (r, ((), e)) (s, ((), f)) := by
  simp [discardMiddle]

example {A B : Type} (N : Superop A B) (rho : Matrix A A ℂ) :
    mixedChannel (fun _ : Unit => (1 : ℝ)) (fun _ => N) rho = N rho := by
  simp [mixedChannel, average]

example {A B : Type*} (rho : Matrix (A × B) (A × B) ℂ) :
    both (id : Superop A A) (id : Superop B B) rho = rho := by rfl

example {A : Type*} (rho : Matrix A A ℂ) (a b : A) :
    cqState (fun _ : Unit => (1 : ℝ)) (fun _ => rho) ((), a) ((), b) = rho a b := by
  simp [cqState]

example {A : Type} [Fintype A] [DecidableEq A] (rho : Matrix A A ℂ) :
    labelInformation (fun _ : Unit => (1 : ℝ)) (fun _ => rho) = 0 := by simp [labelInformation, average]

example : diagonalSource 0 false false = 0 ∧ diagonalSource 0 true true = 1 := by
  simp [diagonalSource]

example : discriminant 0 0 = 1 := by norm_num [discriminant]

example : depolarizingSpectrum 0 0 = ![0, 0, 1, 0] := by
  norm_num [depolarizingSpectrum, discriminant]

example : classicalInput 0 (false, true) (false, true) = 1 := by
  simp [classicalInput, pureDensity, qBasis]

example : classicalOutput 0 0 (false, true) (false, true) = 1 := by
  simp [classicalOutput, idTensorSuperop, pauliDepolarizing, classicalInput, pureDensity, qBasis]

example (j : Fin 4) : bellOutputs 0 j = pureDensity (qBasis j (1 / 2)) := by
  ext a b
  simp [bellOutputs, idTensorSuperop, pauliDepolarizing]

example : pauliLabel 0 = 1 := by simp [pauliLabel]

example : Nonempty (ErrorWords 0 0) := by
  exact ⟨⟨fun i => Fin.elim0 i, by simp [pauliWeight, wordSupport]⟩⟩

example (a b : Qubits 0) : pauliWord (fun i : Fin 0 => Fin.elim0 i) a b = 1 := by
  simp [pauliWord]

example : BinaryCode 0 0 0 := by
  refine ⟨fun _ i => Fin.elim0 i, ?_⟩
  intro j l h
  have hjl : j = l := by
    haveI : Subsingleton (Fin (2 ^ 0)) := by
      change Subsingleton (Fin 1)
      infer_instance
    exact Subsingleton.elim j l
  exact (h hjl).elim

example (k : ℕ) : messageRate k 0 = 0 := by simp [messageRate]

example : binaryDivergence (1 / 2) (1 / 2) = 0 := by norm_num [binaryDivergence]

section FiniteRegisters

variable {A B C D R K J : Type}
variable [Fintype A] [Fintype B] [Fintype C] [Fintype D]
variable [Fintype R] [Fintype K] [Fintype J]
variable [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]
variable [DecidableEq R] [DecidableEq K] [DecidableEq J]

end FiniteRegisters

end QAlgorithms.Papers.Independent.Gap48.P33


