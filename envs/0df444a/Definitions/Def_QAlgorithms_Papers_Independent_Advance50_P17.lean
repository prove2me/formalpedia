-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P17
-- name    : QAlgorithms_Papers_Independent_Advance50_P17
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T11:18:20.49674+00:00
-- url     : https://prove2.me/theorems/b823f378-9f20-4986-90c6-720a48297f42
-- title:
--   Definitions for Distance measures to compare real and ideal quantum processes
-- statement:
--   The objects the formalized statements of *Distance measures to compare real and ideal quantum processes* (arXiv:quant-ph/0408063) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `ProcessDensityInput`: Normalized density operators; source PDF pp.3--4.
--   - `FiniteProcess`: CPTP maps, using the accepted finite normalized Kraus convention; PDF p.3.
--   - `ProcessPureInput`: Pure inputs are unit vectors; the distances act on their densities, PDF pp.3--4.
--   - `MetricAxioms`: The four metric axioms, including separation, PDF p.1.
--   - `FiniteStateDistance`: A state-distance family on finite registers, PDF pp.4--5.
--   - `ProcessDistance`: A process-distance family, allowing compatible input and output registers, PDF pp.1--2.
--   - `ProcessMetrics`: Metric property on actual CPTP maps, PDF pp.1--2.
--   - `ProcessChaining`: Chaining is uniform over compatible CPTP maps, PDF p.2.
--   - `StateMetrics`: State metric axioms hold in every positive finite dimension, PDF p.5.
--   - `StateContinuous`: Continuity on normalized states, the regularity implicit in the Haar integral, PDF p.7.
--   - `StateContractive`: Contractivity includes changing finite registers, PDF pp.4--6.
--   - `StateStable`: Tensor stability and invariance under canonical basis permutations, PDF pp.3,5. The latter identifies the reference-first Choi tensor order with the product order.
--   - `StateDoublyConvex`: Joint convexity under common finite probability mixtures, PDF pp.5,8. This is a genuine additional premise for the generic pure-input conclusion; it is NOT assumed of A,B,C, whose printed joint-convexity claim is deferred.
--   - `Choice`: The paper's four candidate state metrics, PDF pp.4--5.
--   - `stateDistance`: A, B, C are decreasing transforms of squared quantum fidelity, PDF p.4.
--   - `normalizedProcessState`: Reference-first normalized Choi state, Eq.(3), PDF p.3.
--   - `proDistance`: Process-state distance, Eq.(6), PDF p.5.
--   - `proFidelity`: Process fidelity is squared fidelity of normalized Choi states, PDF pp.5--6.
--   - `haarColumnInput`: Haar input obtained from one column of Haar U(card I), transported to I, PDF p.7. The column is fixed independently of the channels.
--   - `pureInputAverage`: Normalized Haar pure-state average, PDF p.7.
--   - `aveDistance`: Eq.(13): average the distance, PDF p.7.
--   - `aveFidelity`: Eq.(14): average squared fidelity before any transform, PDF p.7.
--   - `maxDistance`: Eq.(16), supremum over the nonempty compact unit sphere, PDF p.8. Attainment and equality with mixed-input optimization are conclusions below.
--   - `minFidelity`: Eq.(17), minimum squared fidelity over pure inputs, PDF p.8.
--   - `stabDistance`: Eq.(18): input-sized identity ancilla, PDF p.8.
--   - `stabFidelity`: Stabilized minimum squared fidelity, PDF p.8.
--   - `stabC`: C_stab = sqrt(1-F_stab), PDF pp.8--9.
--   - `purifiedFidelity`: Actual purified channel-pair fidelity objective, PDF pp.12--13.
--   - `purifiedChannelTraceDistance`: Actual purified trace-distance objective; this is not D(E(rho),F(rho)), PDF p.13.
--   - `binarySuccess`: Success for the binary POVM {M,I-M}, guessing E at M, PDF pp.4,7--8.
--   - `optimalSuccess`: Optimized equal-prior success; the effect set is nonempty and bounded on states, PDF p.4.
--   - `basisOutputLaw`: Classical computational-basis output law, Section V, PDF pp.9--10.
--   - `jointLaw`: Uniform joint law retains the input label, PDF p.10.
--   - `worstFunctionErrorProbability`: Actual worst-case function error, PDF p.9.
--   - `meanError`: Uniform finite-instance average, not a Haar average, PDF p.9.
--   - `classicalVariation`: Classical total variation, PDF p.10.
--   - `bhattacharyya`: UNSQUARED Bhattacharyya overlap, explicitly defined on PDF p.10.
--   - `fidelityTransform`: Transform an already averaged fidelity, a different construction from Eq.(13), PDF p.7.
--   - `reconstructionCoefficients`: Corrected Eq.(11) coefficient matrix, computed from two operator bases, PDF p.6. The b coefficient uses U V_j^dagger U^dagger as forced by Eq.(10), correcting the printed typo.
--   - `pairedOperator`: Corrected Eq.(12) paired operators; coefficients are computed independently of E, PDF p.6.
--   - `hermitianImag`: Hermitian imaginary part, reference note [45], PDF p.15.
--   - `inputPauliLabel`: Fixed labels I,X,Y,Z for the qubit construction, PDF pp.6--7.
--   - `tomographyQubitInput`: Normalize the source's four one-qubit input matrices to trace one, PDF p.6.
--   - `tomographyProductInput`: Product density inputs with wire 0 first, PDF pp.6--7.
--   - `productPauli`: Pauli product from the accepted fixed tensor convention, PDF pp.6--7.
--   - `productCoefficient`: Real expansion coefficients in the NORMALIZED density basis: I=2rho_0, P=2rho_P-2rho_0, tensorized over the wires, PDF pp.6--7.
--   - `productObservable`: Paired Hermitian observables for the normalized n-qubit basis, PDF pp.6--7.
-- source:
--   Distance measures to compare real and ideal quantum processes, arXiv:quant-ph/0408063v2, https://arxiv.org/abs/quant-ph/0408063v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_QuantumOutputMetrics
import Definitions.Def_QAlgorithms_Defs_QuditChannelFidelities
import Definitions.Def_QAlgorithms_Defs_Stabilizer
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P53
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P08
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P75
import Definitions.Def_QAlgorithms_Defs_LocalHamiltonian

noncomputable section

open MeasureTheory Filter
open scoped Matrix ComplexConjugate Topology

namespace QAlgorithms.Papers.Independent.Advance50.P17

open QAlgorithms.Papers.Independent.Information100.P53 (fidelity)
open QAlgorithms.Papers.Independent.Information100.P08 (canonicalPurification)
open QAlgorithms.Papers.Independent.Information100.P75 (hermitianReal)

/-- Normalized density operators; source PDF pp.3--4. -/
abbrev ProcessDensityInput (I : Type) [Fintype I] [Nonempty I] := {rho : Matrix I I ℂ // IsDensityMatrix rho}

/-- CPTP maps, using the accepted finite normalized Kraus convention; PDF p.3. -/
abbrev FiniteProcess (I J : Type) [Fintype I] [Fintype J] [DecidableEq I]
    [Nonempty I] [Nonempty J] :=
  {E : Superop I J // IsChannel E}

/-- Pure inputs are unit vectors; the distances act on their densities, PDF pp.3--4. -/
abbrev ProcessPureInput (I : Type) [Fintype I] [Nonempty I] := {psi : EuclideanSpace ℂ I // IsState psi}

/-- The four metric axioms, including separation, PDF p.1. -/
def MetricAxioms {X : Type*} (delta : X → X → ℝ) : Prop :=
  (∀ x y, 0 ≤ delta x y) ∧ (∀ x y, delta x y = 0 ↔ x = y) ∧
  (∀ x y, delta x y = delta y x) ∧
  (∀ x y z, delta x z ≤ delta x y + delta y z)

/-- A state-distance family on finite registers, PDF pp.4--5. -/
abbrev FiniteStateDistance := ∀ {I : Type} [Fintype I] [DecidableEq I],
  Matrix I I ℂ → Matrix I I ℂ → ℝ

/-- A process-distance family, allowing compatible input and output registers, PDF pp.1--2. -/
abbrev ProcessDistance := ∀ {I J : Type} [Fintype I] [Fintype J]
  [DecidableEq I] [DecidableEq J], Superop I J → Superop I J → ℝ

/-- Metric property on actual CPTP maps, PDF pp.1--2. -/
def ProcessMetrics (delta : ProcessDistance) : Prop :=
  ∀ (I J : Type) [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    [Nonempty I] [Nonempty J], MetricAxioms (fun E F : FiniteProcess I J => delta E.val F.val)

/-- Chaining is uniform over compatible CPTP maps, PDF p.2. -/
def ProcessChaining (delta : ProcessDistance) : Prop :=
  ∀ (I J K : Type) [Fintype I] [Fintype J] [Fintype K]
    [DecidableEq I] [DecidableEq J] [DecidableEq K]
    [Nonempty I] [Nonempty J] [Nonempty K],
    ∀ E1 F1 : FiniteProcess I J, ∀ E2 F2 : FiniteProcess J K,
      delta (E2.val ∘ E1.val) (F2.val ∘ F1.val) ≤ delta E1.val F1.val + delta E2.val F2.val

/-- State metric axioms hold in every positive finite dimension, PDF p.5. -/
def StateMetrics (delta : FiniteStateDistance) : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] [Nonempty I],
    MetricAxioms (fun rho sigma : ProcessDensityInput I => delta rho.val sigma.val)

/-- Continuity on normalized states, the regularity implicit in the Haar integral, PDF p.7. -/
def StateContinuous (delta : FiniteStateDistance) : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] [Nonempty I],
    Continuous (fun p : ProcessDensityInput I × ProcessDensityInput I => delta p.1.val p.2.val)

/-- Contractivity includes changing finite registers, PDF pp.4--6. -/
def StateContractive (delta : FiniteStateDistance) : Prop :=
  ∀ (I J : Type) [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    [Nonempty I] [Nonempty J], ∀ E : FiniteProcess I J, ∀ rho sigma : ProcessDensityInput I,
      delta (E.val rho.val) (E.val sigma.val) ≤ delta rho.val sigma.val

/-- Tensor stability and invariance under canonical basis permutations, PDF pp.3,5.
The latter identifies the reference-first Choi tensor order with the product order. -/
def StateStable (delta : FiniteStateDistance) : Prop :=
  (∀ (I J : Type) [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    [Nonempty I] [Nonempty J], ∀ rho sigma : ProcessDensityInput I, ∀ tau : ProcessDensityInput J,
      delta (Matrix.kronecker tau.val rho.val) (Matrix.kronecker tau.val sigma.val) =
        delta rho.val sigma.val) ∧
  (∀ (I J : Type) [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    [Nonempty I] [Nonempty J], ∀ e : I ≃ J, ∀ rho sigma : ProcessDensityInput I,
      delta (Matrix.reindex e e rho.val) (Matrix.reindex e e sigma.val) = delta rho.val sigma.val)

/-- Joint convexity under common finite probability mixtures, PDF pp.5,8.
This is a genuine additional premise for the generic pure-input conclusion; it is NOT
assumed of A,B,C, whose printed joint-convexity claim is deferred. -/
def StateDoublyConvex (delta : FiniteStateDistance) : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] [Nonempty I],
    ∀ (L : Type) [Fintype L], ∀ p : L → ℝ, (∀ j, 0 ≤ p j) → (∑ j, p j) = 1 →
    ∀ rho sigma : L → ProcessDensityInput I,
      delta (∑ j, (p j : ℂ) • (rho j).val) (∑ j, (p j : ℂ) • (sigma j).val) ≤
        ∑ j, p j * delta (rho j).val (sigma j).val

/-- The paper's four candidate state metrics, PDF pp.4--5. -/
inductive Choice where
  | trace
  | angle
  | bures
  | sine
  deriving DecidableEq

/-- A, B, C are decreasing transforms of squared quantum fidelity, PDF p.4. -/
def stateDistance (c : Choice) {I : Type} [Fintype I] [DecidableEq I]
    (rho sigma : Matrix I I ℂ) : ℝ :=
  match c with
  | .trace => traceDistance rho sigma
  | .angle => Real.arccos (Real.sqrt (fidelity rho sigma))
  | .bures => Real.sqrt (2 - 2 * Real.sqrt (fidelity rho sigma))
  | .sine => Real.sqrt (1 - fidelity rho sigma)

variable {I J K : Type} [Fintype I] [Fintype J] [Fintype K]
  [DecidableEq I] [DecidableEq J] [DecidableEq K]
  [Nonempty I] [Nonempty J] [Nonempty K]

/-- Reference-first normalized Choi state, Eq.(3), PDF p.3. -/
def normalizedProcessState (E : Superop I I) : Matrix (I × I) (I × I) ℂ :=
  idTensorSuperop E (pureDensity (finiteMaxEntangled I))

/-- Process-state distance, Eq.(6), PDF p.5. -/
def proDistance (delta : FiniteStateDistance) (E F : Superop I I) : ℝ :=
  delta (normalizedProcessState E) (normalizedProcessState F)

/-- Process fidelity is squared fidelity of normalized Choi states, PDF pp.5--6. -/
def proFidelity (E F : Superop I I) : ℝ := fidelity (normalizedProcessState E) (normalizedProcessState F)

/-- Haar input obtained from one column of Haar U(card I), transported to I, PDF p.7.
The column is fixed independently of the channels. -/
def haarColumnInput (U : Matrix.unitaryGroup (Fin (Fintype.card I)) ℂ) : EuclideanSpace ℂ I :=
  WithLp.toLp 2 fun i => (U : Matrix (Fin (Fintype.card I)) (Fin (Fintype.card I)) ℂ)
    (Fintype.equivFin I i) (Fintype.equivFin I (Classical.choice (inferInstance : Nonempty I)))

/-- Normalized Haar pure-state average, PDF p.7. -/
def pureInputAverage (g : EuclideanSpace ℂ I → ℝ) : ℝ :=
  ∫ U, g (haarColumnInput U) ∂Schur.unitaryHaar (Fintype.card I)

/-- Eq.(13): average the distance, PDF p.7. -/
def aveDistance (delta : FiniteStateDistance) (E F : Superop I I) : ℝ :=
  pureInputAverage (fun psi => delta (E (pureDensity psi)) (F (pureDensity psi)))

/-- Eq.(14): average squared fidelity before any transform, PDF p.7. -/
def aveFidelity (E F : Superop I I) : ℝ :=
  pureInputAverage (fun psi => fidelity (E (pureDensity psi)) (F (pureDensity psi)))

/-- Eq.(16), supremum over the nonempty compact unit sphere, PDF p.8.
Attainment and equality with mixed-input optimization are conclusions below. -/
def maxDistance (delta : FiniteStateDistance) (E F : Superop I I) : ℝ :=
  sSup (Set.range (fun psi : ProcessPureInput I => delta (E (pureDensity psi.val)) (F (pureDensity psi.val))))

/-- Eq.(17), minimum squared fidelity over pure inputs, PDF p.8. -/
def minFidelity (E F : Superop I I) : ℝ :=
  sInf (Set.range (fun psi : ProcessPureInput I => fidelity (E (pureDensity psi.val)) (F (pureDensity psi.val))))

/-- Eq.(18): input-sized identity ancilla, PDF p.8. -/
def stabDistance (delta : FiniteStateDistance) (E F : Superop I I) : ℝ :=
  maxDistance delta (idTensorSuperop (R := I) E) (idTensorSuperop (R := I) F)

/-- Stabilized minimum squared fidelity, PDF p.8. -/
def stabFidelity (E F : Superop I I) : ℝ :=
  minFidelity (idTensorSuperop (R := I) E) (idTensorSuperop (R := I) F)

/-- C_stab = sqrt(1-F_stab), PDF pp.8--9. -/
def stabC (E F : Superop I I) : ℝ := Real.sqrt (1 - stabFidelity E F)

/-- Actual purified channel-pair fidelity objective, PDF pp.12--13. -/
def purifiedFidelity (E F : Superop I I) (rho : Matrix I I ℂ) : ℝ :=
  fidelity (idTensorSuperop E (pureDensity (canonicalPurification rho)))
    (idTensorSuperop F (pureDensity (canonicalPurification rho)))

/-- Actual purified trace-distance objective; this is not D(E(rho),F(rho)), PDF p.13. -/
def purifiedChannelTraceDistance (E F : Superop I I) (rho : Matrix I I ℂ) : ℝ :=
  traceDistance (idTensorSuperop E (pureDensity (canonicalPurification rho)))
    (idTensorSuperop F (pureDensity (canonicalPurification rho)))

/-- Success for the binary POVM {M,I-M}, guessing E at M, PDF pp.4,7--8. -/
def binarySuccess (rho sigma M : Matrix I I ℂ) : ℝ :=
  (effectProb M rho + effectProb (1 - M) sigma) / 2

/-- Optimized equal-prior success; the effect set is nonempty and bounded on states, PDF p.4. -/
def optimalSuccess (rho sigma : Matrix I I ℂ) : ℝ :=
  sSup (Set.range (fun M : {M : Matrix I I ℂ // IsEffect M} => binarySuccess rho sigma M.val))

/-- Classical computational-basis output law, Section V, PDF pp.9--10. -/
def basisOutputLaw (E : Superop I I) (x y : I) : ℝ := (E (pureDensity (ket x)) y y).re

/-- Uniform joint law retains the input label, PDF p.10. -/
def jointLaw (E : Superop I I) (xy : I × I) : ℝ :=
  basisOutputLaw E xy.1 xy.2 / Fintype.card I

/-- Actual worst-case function error, PDF p.9. -/
def worstFunctionErrorProbability (E : Superop I I) (f : I → I) : ℝ :=
  sSup (Set.range (fun x => 1 - basisOutputLaw E x (f x)))

/-- Uniform finite-instance average, not a Haar average, PDF p.9. -/
def meanError (E : Superop I I) (f : I → I) : ℝ :=
  (∑ x, (1 - basisOutputLaw E x (f x))) / Fintype.card I

/-- Classical total variation, PDF p.10. -/
def classicalVariation {X : Type} [Fintype X] (p q : X → ℝ) : ℝ :=
  (∑ x, |p x - q x|) / 2

/-- UNSQUARED Bhattacharyya overlap, explicitly defined on PDF p.10. -/
def bhattacharyya {X : Type} [Fintype X] (p q : X → ℝ) : ℝ :=
  ∑ x, Real.sqrt (p x * q x)

/-- Transform an already averaged fidelity, a different construction from Eq.(13), PDF p.7. -/
def fidelityTransform (c : Choice) (f : ℝ) : ℝ :=
  match c with
  | .trace => f
  | .angle => Real.arccos (Real.sqrt f)
  | .bures => Real.sqrt (2 - 2 * Real.sqrt f)
  | .sine => Real.sqrt (1 - f)

/-- Corrected Eq.(11) coefficient matrix, computed from two operator bases, PDF p.6.
The b coefficient uses U V_j^dagger U^dagger as forced by Eq.(10), correcting the printed typo. -/
def reconstructionCoefficients (r s : Module.Basis (I × I) ℂ (Matrix I I ℂ))
    (V : I × I → Matrix.unitaryGroup I ℂ) (U : Matrix.unitaryGroup I ℂ) (k l : I × I) : ℂ :=
  ∑ j, s.repr ((U : Matrix I I ℂ) * (V j : Matrix I I ℂ)ᴴ * (U : Matrix I I ℂ)ᴴ) l *
    r.repr (V j : Matrix I I ℂ) k

/-- Corrected Eq.(12) paired operators; coefficients are computed independently of E, PDF p.6. -/
def pairedOperator (r : Module.Basis (I × I) ℂ (Matrix I I ℂ))
    (V : I × I → Matrix.unitaryGroup I ℂ) (U : Matrix.unitaryGroup I ℂ) (k : I × I) : Matrix I I ℂ :=
  ∑ j, r.repr (V j : Matrix I I ℂ) k •
    ((U : Matrix I I ℂ) * (V j : Matrix I I ℂ)ᴴ * (U : Matrix I I ℂ)ᴴ)

/-- Hermitian imaginary part, reference note [45], PDF p.15. -/
def hermitianImag (A : Matrix I I ℂ) : Matrix I I ℂ := (2 * Complex.I)⁻¹ • (A - Aᴴ)

/-- Fixed labels I,X,Y,Z for the qubit construction, PDF pp.6--7. -/
def inputPauliLabel (k : Fin 4) : QAlgorithms.Stabilizer.Pauli := ![QAlgorithms.Stabilizer.Pauli.I, QAlgorithms.Stabilizer.Pauli.X, QAlgorithms.Stabilizer.Pauli.Y, QAlgorithms.Stabilizer.Pauli.Z] k

/-- Normalize the source's four one-qubit input matrices to trace one, PDF p.6. -/
def tomographyQubitInput (k : Fin 4) : Matrix Bool Bool ℂ :=
  if k = 0 then (2⁻¹ : ℂ) • 1 else (2⁻¹ : ℂ) • (1 + (inputPauliLabel k).mat)

/-- Product density inputs with wire 0 first, PDF pp.6--7. -/
def tomographyProductInput (n : ℕ) (k : Fin n → Fin 4) : Matrix (Qubits n) (Qubits n) ℂ :=
  Matrix.of fun x y => ∏ t, tomographyQubitInput (k t) (x t) (y t)

/-- Pauli product from the accepted fixed tensor convention, PDF pp.6--7. -/
def productPauli (n : ℕ) (j : Fin n → Fin 4) : Matrix (Qubits n) (Qubits n) ℂ :=
  QAlgorithms.Stabilizer.PauliString.toMatrix ⟨0, fun t => inputPauliLabel (j t)⟩

/-- Real expansion coefficients in the NORMALIZED density basis: I=2rho_0,
P=2rho_P-2rho_0, tensorized over the wires, PDF pp.6--7. -/
def productCoefficient (n : ℕ) (j k : Fin n → Fin 4) : ℝ :=
  ∏ t, if j t = 0 then (if k t = 0 then 2 else 0)
    else if k t = j t then 2 else if k t = 0 then -2 else 0

/-- Paired Hermitian observables for the normalized n-qubit basis, PDF pp.6--7. -/
def productObservable (n : ℕ) (U : Matrix.unitaryGroup (Qubits n) ℂ)
    (k : Fin n → Fin 4) : Matrix (Qubits n) (Qubits n) ℂ :=
  ∑ j : Fin n → Fin 4, (productCoefficient n j k : ℂ) •
    ((U : Matrix (Qubits n) (Qubits n) ℂ) * (productPauli n j)ᴴ *
      (U : Matrix (Qubits n) (Qubits n) ℂ)ᴴ)

/-! Sanity checks for the complete local definitions and imported reuse interfaces. -/

example (rho sigma : Matrix I I ℂ) : fidelity rho sigma = rootFidelity rho sigma ^ 2 := rfl

example (rho : Matrix I I ℂ) : stateDistance .trace rho rho = 0 := by
  simp [stateDistance, traceDistance, traceNorm, cfc_zero]

example (E F : Superop I I) : proDistance (stateDistance .sine) E F =
    Real.sqrt (1 - proFidelity E F) := rfl

example (E : Superop I I) (x y : I) : jointLaw E (x,y) =
    basisOutputLaw E x y / Fintype.card I := rfl

example (psi : EuclideanSpace ℂ I) :
    pureInputAverage (I := I) (fun _ => (0 : ℝ)) = 0 := by simp [pureInputAverage]

example (rho : Matrix I I ℂ) (a i : I) : canonicalPurification rho (a,i) =
    cfc Real.sqrt rho i a := rfl

example : tomographyQubitInput 0 false false = (2⁻¹ : ℂ) := by simp [tomographyQubitInput]

example (x y : Qubits 0) : tomographyProductInput 0 (fun i => Fin.elim0 i) x y = 1 := by
  simp [tomographyProductInput]

example : productCoefficient 0 (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) = 1 := by
  simp [productCoefficient]

end QAlgorithms.Papers.Independent.Advance50.P17


