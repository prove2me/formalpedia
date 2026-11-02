-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P66
-- name    : QAlgorithms_Papers_Independent_Intakethird100_P66
-- status  : Definition
-- author  : @Gohan
-- created : 2026-11-01T08:43:10.398621+00:00
-- url     : https://prove2.me/theorems/92ca5b55-9809-4306-9aac-54ddea24d1af
-- title:
--   Definitions for Classical Shadows for Quantum Process Tomography on Near-term Quantum Computers
-- statement:
--   The objects the formalized statements of *Classical Shadows for Quantum Process Tomography on Near-term Quantum Computers* (arXiv:2110.02965) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `appendMatrixTensor`: Reference-first tensor product on the frozen bit-string register; p.2 Eq.(1).
--   - `processChoi`: Unnormalized Choi matrix, p.2 Eq.(1), constructed by matrix units.
--   - `processChoiState`: Trace-one Choi matrix rho_Lambda=Lambda/2^n, p.2; append-register adapter.
--   - `processMarginal`: Retain both copies of the same physical subsystem, pp.2,14. Summation strings are zero on retained coordinates, counting each outside configuration once. The induced environment is maximally mixed.
--   - `embedProcessObservable`: Extend a subsystem observable by identity on both complements, p.14 A7,A9.
--   - `BasisChoiceFrame`: Finite basis-choice frame, pp.2,4,15. Only `PaperFrame` constructors supply frames in the named-ensemble claims; arbitrary projectors are not allowed.
--   - `pauliFrame`: Pauli-6, p.2, with redundant outcome relabeling bits for preparation. Averaging gives exactly (1/3)|v><v| on each wire. Fixed outcome zero then prepares all six eigenstates as in the two-sided circuit, p.4.
--   - `globalFrame`: Uniform global Clifford basis on all measured wires, pp.2,4. Finiteness enumerates the entire phase quotient, never a design subset.
--   - `tensorFrame`: Independent fixed blocks, pp.4,15; no gate crosses the block boundary.
--   - `singleCliffordFrame`: Product one-qubit Clifford measurement on m wires, pp.2,13.
--   - `CliffordBlocks`: Fixed partitions into Clifford blocks, pp.4,15. No Pauli/Clifford hybrid ensemble is introduced. The empty frame is the zero-block product.
--   - `PaperFrame`: Exactly Pauli-6 or a fixed Clifford-block partition, Appendix B. Reference and output use independent choices from the same named frame.
--   - `basisBornWeight`: One shot: uniform basis choice followed by its Born outcome, pp.2,4.
--   - `recordProbability`: N independent actual shots, without renormalizing arbitrary weights. For named frames on density matrices these are Born probabilities.
--   - `basisMeasurementChannel`: Constructed complex-linear measurement channel, pp.4,15: the finite coefficient version of the accepted measurement channel.
--   - `frameInverse`: Actual linear inverse, pp.4,15. Zero only totalizes incomplete frames; named PaperFrames are informationally complete. The inverse is linear (d+1)X-Tr(X)I, not the affine formula restricted to rank-one projectors.
--   - `frameSnapshot`: Normalized single-shot reconstruction, pp.4,15.
--   - `choiSnapshot`: Eq.(7): external scale is 2^n for n physical channel qubits.
--   - `meanChoiSnapshot`: Expectation of Eq.(7), permitting indefinite reconstructed matrices.
--   - `ancillaReconstruction`: Appendix B1 expectation, reference first; independent basis choices.
--   - `twoSidedReconstruction`: Appendix B2 expectation: prepare Ui†|0><0|Ui and transpose its reconstructed input factor. Every choice is followed by a fresh channel use.
--   - `ErrorNorm`: Source norms, pp.2,14; trace norm has no factor 1/2.
--   - `matrixError`: The two ordinary matrix norms in II.1/A.3.
--   - `ReducedRecovers`: Uniform recovery of every k-subsystem in one simultaneous event. The estimator precedes the unknown CPTP map and sees exactly N shots.
--   - `sampleCount`: Exact k=0 scalar uses no samples; other real sufficient counts are rounded upward.
--   - `reducedLog`: Common Frobenius logarithm, pp.2,14.
--   - `traceSampleLog`: Trace-norm logarithm: the exponent is 2k, pp.2,14.
--   - `finiteMax`: Finite real maximum, zero only for an empty index type. The theorem families are nonempty (M>0 or k<=n), with nonnegative entries.
--   - `centeredVariance`: Accepted centered shadow variance, extended to raw matrices without a proof binder. The non-Hermitian fallback is never used by a theorem observable. Centering divides by the full measured dimension, not by two.
--   - `primitiveShotLaw`: Frozen oneShotLaw without its unused density-proof parameter: this avoids assuming Choi normalization as a new theorem hypothesis. For CPTP E it is exactly the accepted law on processChoiState E, pp.2,13.
--   - `primitiveRecordLaw`: Independent fresh preparations, counted by actual record length N.
--   - `PrimitiveReducedRecovers`: Generic-primitive simultaneous reduced-process recovery, p.14. The estimator is measurable, as required for the statistical success event.
--   - `reducedVariance`: Full family of ambient embedded 2k-wire Paulis, p.14 A5,A7-A9. Identity coefficients are known exactly.
--   - `pauliNormEnvelope`: Retain the printed Pauli spectral-norm factor, p.14.
--   - `overlapObservable`: Proof-defined observable with transposed input, p.13 A4, fixing the p.2 shorthand.
--   - `OverlapsRecover`: One simultaneous event for all normalized overlaps, II.2. The physical process overlap is 2^n times this target.
--   - `PrimitiveOverlapsRecover`: Same simultaneous task for an arbitrary informationally complete fixed primitive. Measurability rules out interpreting nonmeasurable success sets by outer measure.
-- source:
--   Classical Shadows for Quantum Process Tomography on Near-term Quantum Computers, arXiv:2110.02965v3, https://arxiv.org/abs/2110.02965v3

import Definitions.Def_QAlgorithms_Defs_ClassicalShadowPrediction
import Definitions.Def_QAlgorithms_Defs_LocalPauliShadows
import Definitions.Def_QAlgorithms_Defs_ProjectiveCliffords
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QAlgorithms_Defs_QECC

/-!
Statements from Levy, Luo and Clark, arXiv:2110.02965v3.
Only the five nodes marked `state` have theorem declarations. Six deferred nodes
are inventoried in HARD.md. All new definitions are paper-local. Each sample
uses a fresh normalized Choi preparation. Compilation is pending batch handoff.
-/

noncomputable section

open MeasureTheory QAlgorithms ClassicalShadows
open scoped Matrix ComplexConjugate ENNReal

namespace QAlgorithms.Papers.Independent.Intakethird100.P66

attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

/-- Reference-first tensor product on the frozen bit-string register; p.2 Eq.(1). -/
def appendMatrixTensor {a b : ℕ} (A : Space a) (B : Space b) : Space (a + b) :=
  (Matrix.kronecker A B).submatrix (qubitsAppendEquiv a b) (qubitsAppendEquiv a b)

/-- Unnormalized Choi matrix, p.2 Eq.(1), constructed by matrix units. -/
def processChoi {n : ℕ} (E : Superop (Qubits n) (Qubits n)) : Space (n + n) :=
  Matrix.of fun x y =>
    E (Matrix.single (qubitsAppendEquiv n n x).1
      (qubitsAppendEquiv n n y).1 1)
      (qubitsAppendEquiv n n x).2 (qubitsAppendEquiv n n y).2

/-- Trace-one Choi matrix rho_Lambda=Lambda/2^n, p.2; append-register adapter. -/
def processChoiState {n : ℕ} (E : Superop (Qubits n) (Qubits n)) : Space (n + n) :=
  ((2 : ℂ) ^ n)⁻¹ • processChoi E

/-- Retain both copies of the same physical subsystem, pp.2,14.
Summation strings are zero on retained coordinates, counting each outside
configuration once. The induced environment is maximally mixed. -/
def processMarginal {n k : ℕ} (rho : Space (n + n)) (w : Fin k ↪ Fin n) : Space (k + k) :=
  Matrix.of fun x y => ∑ a : Qubits n, ∑ b : Qubits n,
    if (∀ i, a (w i) = false) ∧ (∀ i, b (w i) = false) then
      rho (Fin.append (overwrite w a (qubitsAppendEquiv k k x).1)
        (overwrite w b (qubitsAppendEquiv k k x).2))
        (Fin.append (overwrite w a (qubitsAppendEquiv k k y).1)
        (overwrite w b (qubitsAppendEquiv k k y).2))
    else 0

/-- Extend a subsystem observable by identity on both complements, p.14 A7,A9. -/
def embedProcessObservable {n k : ℕ} (w : Fin k ↪ Fin n) (O : Space (k + k)) : Space (n + n) :=
  Matrix.of fun x y =>
    let a := qubitsAppendEquiv n n x
    let b := qubitsAppendEquiv n n y
    if ∀ j, (¬ ∃ i, w i = j) → a.1 j = b.1 j ∧ a.2 j = b.2 j then
      O (Fin.append (a.1 ∘ w) (a.2 ∘ w)) (Fin.append (b.1 ∘ w) (b.2 ∘ w))
    else 0

/-- Finite basis-choice frame, pp.2,4,15. Only `PaperFrame` constructors
supply frames in the named-ensemble claims; arbitrary projectors are not allowed. -/
structure BasisChoiceFrame (n : ℕ) where
  Basis : Type
  finite : Fintype Basis
  inhabited : Nonempty Basis
  projector : Basis → Qubits n → Space n

attribute [instance] BasisChoiceFrame.finite BasisChoiceFrame.inhabited

/-- Pauli-6, p.2, with redundant outcome relabeling bits for preparation.
Averaging gives exactly (1/3)|v><v| on each wire. Fixed outcome zero then
prepares all six eigenstates as in the two-sided circuit, p.4. -/
def pauliFrame (m : ℕ) : BasisChoiceFrame m where
  Basis := GroundStateLearning.ShadowLabel m
  finite := inferInstance
  inhabited := ⟨fun _ => (.Z, true)⟩
  projector a b := ((3 : ℂ) ^ m) • GroundStateLearning.pauliPOVM
    (fun j => ((a j).1, if b j then !(a j).2 else (a j).2))

/-- Uniform global Clifford basis on all measured wires, pp.2,4.
Finiteness enumerates the entire phase quotient, never a design subset. -/
def globalFrame (m : ℕ) [Fintype (Clifford.ProjectiveGroup m)] : BasisChoiceFrame m where
  Basis := Clifford.ProjectiveGroup m
  finite := inferInstance
  inhabited := inferInstance
  projector a b :=
    let U : Space m := (Clifford.representative a).val
    Matrix.of fun x y => conj (U b x) * U b y

/-- Independent fixed blocks, pp.4,15; no gate crosses the block boundary. -/
def tensorFrame {a b : ℕ} (F : BasisChoiceFrame a) (G : BasisChoiceFrame b) : BasisChoiceFrame (a + b) where
  Basis := F.Basis × G.Basis
  finite := inferInstance
  inhabited := inferInstance
  projector u x := appendMatrixTensor (F.projector u.1 (qubitsAppendEquiv a b x).1)
    (G.projector u.2 (qubitsAppendEquiv a b x).2)

/-- Product one-qubit Clifford measurement on m wires, pp.2,13. -/
def singleCliffordFrame [Fintype (Clifford.ProjectiveGroup 1)] : (m : ℕ) → BasisChoiceFrame m
  | 0 => pauliFrame 0
  | m + 1 => tensorFrame (singleCliffordFrame m) (globalFrame 1)

/-- Fixed partitions into Clifford blocks, pp.4,15. No Pauli/Clifford
hybrid ensemble is introduced. The empty frame is the zero-block product. -/
inductive CliffordBlocks : {m : ℕ} → BasisChoiceFrame m → Prop
  | empty : CliffordBlocks (pauliFrame 0)
  | global (m : ℕ) [Fintype (Clifford.ProjectiveGroup m)] :
      CliffordBlocks (globalFrame m)
  | blocks {a b : ℕ} {F : BasisChoiceFrame a} {G : BasisChoiceFrame b} :
      CliffordBlocks F → CliffordBlocks G → CliffordBlocks (tensorFrame F G)

/-- Exactly Pauli-6 or a fixed Clifford-block partition, Appendix B.
Reference and output use independent choices from the same named frame. -/
inductive PaperFrame : {m : ℕ} → BasisChoiceFrame m → Prop
  | pauli (m : ℕ) : PaperFrame (pauliFrame m)
  | clifford {m : ℕ} {F : BasisChoiceFrame m} : CliffordBlocks F → PaperFrame F

/-- One shot: uniform basis choice followed by its Born outcome, pp.2,4. -/
def basisBornWeight {m : ℕ} (F : BasisChoiceFrame m) (rho : Space m) (s : F.Basis × Qubits m) : ℝ :=
  (Fintype.card F.Basis : ℝ)⁻¹ * effectProb (F.projector s.1 s.2) rho

/-- N independent actual shots, without renormalizing arbitrary weights.
For named frames on density matrices these are Born probabilities. -/
def recordProbability {m N : ℕ} (F : BasisChoiceFrame m) (rho : Space m)
    (event : (Fin N → F.Basis × Qubits m) → Prop) : ℝ :=
  ∑ r : Fin N → F.Basis × Qubits m,
    if event r then ∏ j, basisBornWeight F rho (r j) else 0

/-- Constructed complex-linear measurement channel, pp.4,15:
the finite coefficient version of the accepted measurement channel. -/
def basisMeasurementChannel {m : ℕ} (F : BasisChoiceFrame m) : Space m →ₗ[ℂ] Space m where
  toFun X := Matrix.of fun i j => ∑ k, ∑ l,
    ((Fintype.card F.Basis : ℂ)⁻¹ *
      ∑ a : F.Basis, ∑ b : Qubits m,
        F.projector a b l k * F.projector a b i j) * X k l
  map_add' X Y := by ext i j; simp [mul_add, Finset.sum_add_distrib]
  map_smul' c X := by ext i j; simp [Finset.mul_sum, mul_left_comm]

/-- Actual linear inverse, pp.4,15. Zero only totalizes incomplete frames;
named PaperFrames are informationally complete. The inverse is linear
(d+1)X-Tr(X)I, not the affine formula restricted to rank-one projectors. -/
def frameInverse {m : ℕ} (F : BasisChoiceFrame m) : Space m →ₗ[ℂ] Space m :=
  if h : Function.Injective (basisMeasurementChannel F) then
    (LinearEquiv.ofBijective (basisMeasurementChannel F)
      ⟨h, LinearMap.injective_iff_surjective.mp h⟩).symm.toLinearMap
  else 0

/-- Normalized single-shot reconstruction, pp.4,15. -/
def frameSnapshot {m : ℕ} (F : BasisChoiceFrame m) (s : F.Basis × Qubits m) : Space m :=
  frameInverse F (F.projector s.1 s.2)

/-- Eq.(7): external scale is 2^n for n physical channel qubits. -/
def choiSnapshot {n : ℕ} (F : BasisChoiceFrame (n + n))
    (s : F.Basis × Qubits (n + n)) : Space (n + n) :=
  ((2 : ℂ) ^ n) • frameSnapshot F s

/-- Expectation of Eq.(7), permitting indefinite reconstructed matrices. -/
def meanChoiSnapshot {n : ℕ} (F : BasisChoiceFrame (n + n))
    (E : Superop (Qubits n) (Qubits n)) : Space (n + n) :=
  ∑ s : F.Basis × Qubits (n + n),
    (basisBornWeight F (processChoiState E) s : ℂ) • choiSnapshot F s

/-- Appendix B1 expectation, reference first; independent basis choices. -/
def ancillaReconstruction {n : ℕ} (F : BasisChoiceFrame n)
    (E : Superop (Qubits n) (Qubits n)) : Space (n + n) :=
  ((Fintype.card F.Basis : ℂ) ^ 2)⁻¹ •
    ∑ a : F.Basis, ∑ c : F.Basis, ∑ b : Qubits n, ∑ d : Qubits n,
      (effectProb (appendMatrixTensor (F.projector a b) (F.projector c d))
        (processChoiState E) : ℂ) •
        appendMatrixTensor (frameInverse F (F.projector a b)) (frameInverse F (F.projector c d))

/-- Appendix B2 expectation: prepare Ui†|0><0|Ui and transpose its
reconstructed input factor. Every choice is followed by a fresh channel use. -/
def twoSidedReconstruction {n : ℕ} (F : BasisChoiceFrame n)
    (E : Superop (Qubits n) (Qubits n)) : Space (n + n) :=
  ((Fintype.card F.Basis : ℂ) ^ 2)⁻¹ •
    ∑ a : F.Basis, ∑ c : F.Basis, ∑ d : Qubits n,
      (effectProb (F.projector c d) (E (F.projector a (fun _ => false))) : ℂ) •
        appendMatrixTensor (frameInverse F ((F.projector a (fun _ => false)).transpose))
          (frameInverse F (F.projector c d))

/-- Source norms, pp.2,14; trace norm has no factor 1/2. -/
inductive ErrorNorm where
  | frobenius | trace

/-- The two ordinary matrix norms in II.1/A.3. -/
def matrixError {m : ℕ} : ErrorNorm → Space m → ℝ
  | .frobenius, X => frobNorm X
  | .trace, X => traceNorm X

/-- Uniform recovery of every k-subsystem in one simultaneous event.
The estimator precedes the unknown CPTP map and sees exactly N shots. -/
def ReducedRecovers {n : ℕ} (F : BasisChoiceFrame (n + n)) (k N : ℕ)
    (norm : ErrorNorm) (eps delta : ℝ) : Prop :=
  ∃ estimate : (Fin N → F.Basis × Qubits (n + n)) → (Fin k ↪ Fin n) → Space (k + k),
    ∀ E : Superop (Qubits n) (Qubits n), IsChannel E →
      1 - delta ≤ recordProbability F (processChoiState E)
        (fun r => ∀ w, matrixError norm (estimate r w - processMarginal (processChoiState E) w) ≤ eps)

/-- Exact k=0 scalar uses no samples; other real sufficient counts are rounded upward. -/
def sampleCount (k : ℕ) (B : ℝ) : ℕ := if k = 0 then 0 else ⌈B⌉₊

/-- Common Frobenius logarithm, pp.2,14. -/
def reducedLog (n k : ℕ) (delta : ℝ) : ℝ :=
  Real.log (2 * (8 * (n : ℝ)) ^ (2 * k) / delta)

/-- Trace-norm logarithm: the exponent is 2k, pp.2,14. -/
def traceSampleLog (n k : ℕ) (delta : ℝ) : ℝ :=
  Real.log ((24 * (n : ℝ)) ^ (2 * k) / delta)

/-- Finite real maximum, zero only for an empty index type.
The theorem families are nonempty (M>0 or k<=n), with nonnegative entries. -/
def finiteMax {A : Type*} [Fintype A] (f : A → ℝ) : ℝ :=
  if h : (Finset.univ : Finset A).Nonempty then Finset.univ.sup' h f else 0

/-- Accepted centered shadow variance, extended to raw matrices without a
proof binder. The non-Hermitian fallback is never used by a theorem observable.
Centering divides by the full measured dimension, not by two. -/
def centeredVariance {m : ℕ} (P : MeasurementPrimitive m) (O : Space m) : ℝ :=
  if h : O.IsHermitian then
    shadowNorm P (tracelessPart O) (tracelessPart_hermitian O h) ^ 2
  else 0

/-- Frozen oneShotLaw without its unused density-proof parameter: this avoids
assuming Choi normalization as a new theorem hypothesis. For CPTP E it is
exactly the accepted law on processChoiState E, pp.2,13. -/
def primitiveShotLaw {m : ℕ} (P : MeasurementPrimitive m) (rho : Space m) :
    Measure (Matrix.unitaryGroup (Qubits m) ℂ × Qubits m) :=
  ∑ b : Qubits m,
    (P.ensemble.withDensity (fun U => ENNReal.ofReal
      (((U : Space m) * rho * star (U : Space m)) b b).re)).map (fun U => (U, b))

/-- Independent fresh preparations, counted by actual record length N. -/
def primitiveRecordLaw {m : ℕ} (P : MeasurementPrimitive m) (rho : Space m) (N : ℕ) :=
  Measure.pi fun _ : Fin N => primitiveShotLaw P rho

/-- Generic-primitive simultaneous reduced-process recovery, p.14.
The estimator is measurable, as required for the statistical success event. -/
def PrimitiveReducedRecovers {n : ℕ} (P : MeasurementPrimitive (n + n))
    (k N : ℕ) (eps delta : ℝ) : Prop :=
  ∃ estimate : (Fin N → Matrix.unitaryGroup (Qubits (n + n)) ℂ × Qubits (n + n)) →
      (Fin k ↪ Fin n) → Space (k + k),
    Measurable estimate ∧
    ∀ E : Superop (Qubits n) (Qubits n), IsChannel E →
      ENNReal.ofReal (1 - delta) ≤ primitiveRecordLaw P (processChoiState E) N
        {r | ∀ w, frobNorm (estimate r w - processMarginal (processChoiState E) w) ≤ eps}

/-- Full family of ambient embedded 2k-wire Paulis, p.14 A5,A7-A9.
Identity coefficients are known exactly. -/
def reducedVariance {n : ℕ} (P : MeasurementPrimitive (n + n)) (k : ℕ) : ℝ :=
  finiteMax fun p : (Fin k ↪ Fin n) × (Fin (k + k) → Stabilizer.Pauli) =>
    centeredVariance P (embedProcessObservable p.1 (pauliOps p.2))

/-- Retain the printed Pauli spectral-norm factor, p.14. -/
def pauliNormEnvelope (k : ℕ) : ℝ :=
  finiteMax fun p : Fin (k + k) → Stabilizer.Pauli => specNorm (pauliOps p) ^ 2

/-- Proof-defined observable with transposed input, p.13 A4, fixing the p.2 shorthand. -/
def overlapObservable {n : ℕ} (rho sigma : Space n) : Space (n + n) :=
  appendMatrixTensor rho.transpose sigma

/-- One simultaneous event for all normalized overlaps, II.2.
The physical process overlap is 2^n times this target. -/
def OverlapsRecover {n M : ℕ} (F : BasisChoiceFrame (n + n)) (O : Fin M → Space (n + n))
    (N : ℕ) (eps delta : ℝ) : Prop :=
  ∃ estimate : (Fin N → F.Basis × Qubits (n + n)) → Fin M → ℝ,
    ∀ E : Superop (Qubits n) (Qubits n), IsChannel E →
      1 - delta ≤ recordProbability F (processChoiState E)
        (fun r => ∀ i, |estimate r i - (O i * processChoiState E).trace.re| ≤ eps)

/-- Same simultaneous task for an arbitrary informationally complete fixed primitive.
Measurability rules out interpreting nonmeasurable success sets by outer measure. -/
def PrimitiveOverlapsRecover {n M : ℕ} (P : MeasurementPrimitive (n + n))
    (O : Fin M → Space (n + n)) (N : ℕ) (eps delta : ℝ) : Prop :=
  ∃ estimate : (Fin N → Matrix.unitaryGroup (Qubits (n + n)) ℂ × Qubits (n + n)) →
      Fin M → ℝ,
    Measurable estimate ∧
    ∀ E : Superop (Qubits n) (Qubits n), IsChannel E →
      ENNReal.ofReal (1 - delta) ≤ primitiveRecordLaw P (processChoiState E) N
        {r | ∀ i, |estimate r i - (O i * processChoiState E).trace.re| ≤ eps}

/-! Small boundary/structural sanity checks, not proofs of paper results. -/

example (B : ℝ) : sampleCount 0 B = 0 := by simp [sampleCount]

example (m : ℕ) (F : BasisChoiceFrame m) : frameInverse F 0 = 0 := map_zero _

example {m : ℕ} (P : MeasurementPrimitive m) (rho : Space m) (h : IsDensityMatrix rho) :
    primitiveShotLaw P rho = oneShotLaw P rho h := rfl

example {a b : ℕ} (A : Space a) (B : Space b) (x y : Qubits (a + b)) :
    appendMatrixTensor A B x y = A (qubitsAppendEquiv a b x).1 (qubitsAppendEquiv a b y).1 *
      B (qubitsAppendEquiv a b x).2 (qubitsAppendEquiv a b y).2 := rfl

example (a : GroundStateLearning.ShadowLabel 0) (b : Qubits 0) :
    (pauliFrame 0).projector a b = 1 := by
  ext x y
  simp [pauliFrame, GroundStateLearning.pauliPOVM, kronAll,
    Matrix.one_apply, Subsingleton.elim x y]

example : finiteMax (fun _ : Fin 0 => (7 : ℝ)) = 0 := by simp [finiteMax]

example {n : ℕ} (F : BasisChoiceFrame (n + n)) (s : F.Basis × Qubits (n + n)) :
    choiSnapshot F s = ((2 : ℂ) ^ n) • frameSnapshot F s := rfl

example {n : ℕ} (rho sigma : Space n) :
    overlapObservable rho sigma = appendMatrixTensor rho.transpose sigma := rfl

/-- Identity-channel normalization sanity check, p.2 Eq.(1). -/
example (n : ℕ) (a b : Qubits n) :
    processChoiState (fun X : Space n => X) (Fin.append a a) (Fin.append b b) =
      ((2 : ℂ) ^ n)⁻¹ := by
  have ha : qubitsAppendEquiv n n (Fin.append a a) = (a, a) :=
    (qubitsAppendEquiv n n).apply_symm_apply (a, a)
  have hb : qubitsAppendEquiv n n (Fin.append b b) = (b, b) :=
    (qubitsAppendEquiv n n).apply_symm_apply (b, b)
  simp [processChoiState, processChoi, ha, hb, Matrix.single_apply]

/-- The zero-shot event is deterministic even when the matrix argument is not a state. -/
example {m : ℕ} (F : BasisChoiceFrame m) (rho : Space m) :
    recordProbability (N := 0) F rho (fun _ => True) = 1 := by
  simp [recordProbability]

/-- Invertibility is constructed, not replaced by an unrelated reconstruction map. -/
example {m : ℕ} (F : BasisChoiceFrame m) (h : Function.Injective (basisMeasurementChannel F)) (X : Space m) :
    frameInverse F (basisMeasurementChannel F X) = X := by
  unfold frameInverse
  rw [dif_pos h]
  exact (LinearEquiv.ofBijective (basisMeasurementChannel F)
    ⟨h, LinearMap.injective_iff_surjective.mp h⟩).symm_apply_apply X

/-- Empty tensor product is a legitimate zero-block Clifford frame. -/
example [Fintype (Clifford.ProjectiveGroup 1)] : PaperFrame (singleCliffordFrame 0) :=
  PaperFrame.clifford CliffordBlocks.empty

end QAlgorithms.Papers.Independent.Intakethird100.P66


