-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Support50_P30
-- name    : QAlgorithms_Papers_Independent_Support50_P30
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-23T21:18:31.423485+00:00
-- url     : https://prove2.me/theorems/08c3d4f4-e3aa-4285-af9c-ee895231734f
-- title:
--   Definitions for Theoretical Guarantees for Permutation-Equivariant Quantum Neural Networks
-- statement:
--   The objects the formalized statements of *Theoretical Guarantees for Permutation-Equivariant Quantum Neural Networks* (arXiv:2210.09974) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `QnnOperator`
--   - `QnnDensity`
--   - `qubitPermutationMatrix`: PDF p.4, Eq.(8): inverse permutation on tensor positions.
--   - `PermutationEquivariant`: PDF pp.3-4: the commutant of the actual permutation action.
--   - `unitaryFamily`: PDF p.15: the full commuting unitary family, including block phases.
--   - `pauliString`: PDF pp.4,27: place a fixed Pauli on each site of a subset.
--   - `collective`: PDF p.29, Eq.(61): sum over each k-element subset once.
--   - `qnnGenerator`: PDF p.4, Eq.(9); used only for n at least two.
--   - `qnnMeasurementFamily`: PDF p.4, Eq.(10), with an unscaled n-body product.
--   - `qnnLayer`: PDF p.2, Eq.(1): exp(-i t H).
--   - `circuit`: PDF p.2, Eq.(1): the last layer acts on the left.
--   - `circuitHalf`: PDF p.23, Eq.(18): false gives U_A; true gives U_B, including mu.
--   - `qnnLoss`: PDF p.2, Eq.(2): real Hermitian expectation.
--   - `dataOperator`: PDF pp.2,6: arbitrary real weights; sigma need not be a density matrix.
--   - `empiricalLoss`: PDF p.2, Eq.(3).
--   - `partialLoss`: PDF pp.6,23: actual coordinate derivative of the empirical loss.
--   - `Sector`
--   - `blockDim`: PDF p.4, Eq.(12): dimension of the U(2) block.
--   - `qnnSectorMultiplicity`: PDF p.4, Eq.(12): number of copies, with the predecessor zero at m=0.
--   - `QnnSchurIndex`
--   - `qnnSchurBlockDiagonal`: PDF p.4, Eq.(13): identical blocks in all multiplicity copies.
--   - `spinCasimir`: PDF pp.13,28: four times the total-spin Casimir.
--   - `SchurFrame`: PDF pp.4,6,23,28: fixed orthonormal Schur coordinates. The commutant condition specifies Schur coordinates, without assuming variance or spectra. The Casimir pins spin (n-2m)/2, preventing sector relabelling.
--   - `rowMap`: PDF p.23, Eq.(10): row coisometry for a copy.
--   - `schurCompression`: PDF p.6, Eq.(15): unnormalized compression.
--   - `aggregate`: PDF p.6, Eq.(16): sum of data compressions, not their average.
--   - `commonBlock`: PDF p.4, Eq.(13): the common equivariant block; averaging identical copies avoids a distinguished copy. Data use aggregate instead.
--   - `deltaPair`: PDF p.26, Eq.(38): centered trace pairing, real on Hermitian inputs.
--   - `centeredDelta`: PDF p.6: unnormalized centered squared Hilbert-Schmidt statistic.
--   - `DesignKey`
--   - `conjugationMonomial`: Balanced entry monomial of conjugation degree r.
--   - `IndependentBlockTwoDesign`: PDF pp.14,24-26: joint exact conjugation 2-design moments for both halves and all blocks, including cross-sector products. No depth-convergence claim.
--   - `variance`: PDF p.24, Eq.(23): variance. Used on bounded measurable circuit losses.
--   - `tangentCommutant`: PDF pp.5,22: real tangent commutant, including the scalar phase direction.
--   - `stateDerivative`: PDF p.9: derivative of the actual output state.
--   - `qfi`: PDF p.9: pure-state QFIM, removing the global phase direction.
--   - `qnnPopulationRisk`: PDF pp.3,15: a is the composed measurable label weight a(f(rho)).
--   - `empiricalRisk`: PDF pp.2-3,15: empirical coefficients a(f(rho_i))/M.
--   - `generalizationEvent`: PDF pp.7,15: one event controls every possible trained unitary.
--   - `dynamicalLie`: PDF p.13, Definition 5: use -i times Hermitian generators, as Eq.(1) requires. This is the actual Lie closure rather than the whole commutant.
--   - `krawtchouk`: PDF p.29, Eq.(62): binary Krawtchouk value in signed real arithmetic.
--   - `symmetricSector`: PDF pp.4,29: the symmetric spin sector.
--   - `haarQubitUnitary`: PDF pp.15,31: transfer Haar U(2^n) to the fixed bit ordering.
--   - `haarPureInput`: PDF p.31: one seed fixed before Haar V.
--   - `classifierFamily`: PDF pp.32-33: a fixed architecture and real threshold.
--   - `uniformParameters`: PDF pp.13,33-34: uniform sampling of the parameter box.
--   - `InversePolynomialLower`: PDF p.34, Eq.(96): eventual inverse-polynomial lower bound.
--   - `HasNarrowGorge`: PDF pp.33-34: below-mean point condition AND exponential tail envelope, with constants before size and tail threshold.
-- source:
--   Theoretical Guarantees for Permutation-Equivariant Quantum Neural Networks, arXiv:2210.09974v3, https://arxiv.org/abs/2210.09974v3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Gates
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_PACSampleComplexity
import Definitions.Def_QAlgorithms_Defs_SchurUnitaryEnsembles

/-! Statements from arXiv:2210.09974v3. All citations are PDF pages.
Schur coordinates are fixed before data and parameters. No state compression
is renormalized. Local definitions belong to this paper only. -/

noncomputable section

open MeasureTheory
open scoped BigOperators ComplexConjugate Matrix.Norms.L2Operator NNReal ENNReal

namespace QAlgorithms.Papers.Independent.Support50.P30

abbrev QnnOperator (n : ℕ) := Matrix (Qubits n) (Qubits n) ℂ

abbrev QnnDensity (n : ℕ) := {rho : QnnOperator n // IsDensityMatrix rho}

instance densityMeasurable (n : ℕ) : MeasurableSpace (QnnDensity n) := borel _

instance densityBorel (n : ℕ) : BorelSpace (QnnDensity n) := ⟨rfl⟩

/-- PDF p.4, Eq.(8): inverse permutation on tensor positions. -/
def qubitPermutationMatrix (n : ℕ) (p : Equiv.Perm (Fin n)) : QnnOperator n :=
  fun x y => if x = (fun j => y (p.symm j)) then 1 else 0

/-- PDF pp.3-4: the commutant of the actual permutation action. -/
def PermutationEquivariant {n : ℕ} (A : QnnOperator n) : Prop :=
  ∀ p : Equiv.Perm (Fin n), A * qubitPermutationMatrix n p = qubitPermutationMatrix n p * A

/-- PDF p.15: the full commuting unitary family, including block phases. -/
def unitaryFamily (n : ℕ) : Set (QnnOperator n) :=
  {U | U ∈ Matrix.unitaryGroup (Qubits n) ℂ ∧ PermutationEquivariant U}

/-- PDF pp.4,27: place a fixed Pauli on each site of a subset. -/
def pauliString (n : ℕ) (chi : Matrix Bool Bool ℂ) (s : Finset (Fin n)) : QnnOperator n :=
  fun x y => ∏ j : Fin n, if j ∈ s then chi (x j) (y j) else if x j = y j then 1 else 0

/-- PDF p.29, Eq.(61): sum over each k-element subset once. -/
def collective (n : ℕ) (chi : Matrix Bool Bool ℂ) (k : ℕ) : QnnOperator n :=
  ∑ s ∈ (Finset.univ : Finset (Fin n)).powersetCard k, pauliString n chi s

/-- PDF p.4, Eq.(9); used only for n at least two. -/
def qnnGenerator (n : ℕ) (j : Fin 3) : QnnOperator n :=
  if j.val = 0 then (1 / (n : ℂ)) • collective n pauliX 1
  else if j.val = 1 then (1 / (n : ℂ)) • collective n pauliY 1
  else (2 / ((n : ℂ) * ((n : ℂ) - 1))) • collective n pauliZ 2

/-- PDF p.4, Eq.(10), with an unscaled n-body product. -/
def qnnMeasurementFamily (n : ℕ) : Set (QnnOperator n) :=
  {O | ∃ chi ∈ ({pauliX, pauliY, pauliZ} : Set (Matrix Bool Bool ℂ)),
    O = (1 / (n : ℂ)) • collective n chi 1 ∨
    O = (2 / ((n : ℂ) * ((n : ℂ) - 1))) • collective n chi 2 ∨
    O = collective n chi n}

/-- PDF p.2, Eq.(1): exp(-i t H). -/
def qnnLayer {n : ℕ} (H : QnnOperator n) (t : ℝ) : QnnOperator n :=
  NormedSpace.exp ((-Complex.I * (t : ℂ)) • H)

/-- PDF p.2, Eq.(1): the last layer acts on the left. -/
def circuit {n L : ℕ} (H : Fin L → QnnOperator n) (theta : Fin L → ℝ) : QnnOperator n :=
  orderedProd (fun j => qnnLayer (H j) (theta j))

/-- PDF p.23, Eq.(18): false gives U_A; true gives U_B, including mu. -/
def circuitHalf {n L : ℕ} (H : Fin L → QnnOperator n) (theta : Fin L → ℝ)
    (mu : Fin L) (before : Bool) : QnnOperator n :=
  let gates := List.ofFn (fun j => qnnLayer (H j) (theta j))
  (if before then gates.take (mu.val + 1) else gates.drop (mu.val + 1)).reverse.prod

/-- PDF p.2, Eq.(2): real Hermitian expectation. -/
def qnnLoss {n : ℕ} (U rho O : QnnOperator n) : ℝ := (U * rho * U.conjTranspose * O).trace.re

/-- PDF pp.2,6: arbitrary real weights; sigma need not be a density matrix. -/
def dataOperator {n M : ℕ} (c : Fin M → ℝ) (rho : Fin M → QnnDensity n) : QnnOperator n :=
  ∑ i, (c i : ℂ) • (rho i).val

/-- PDF p.2, Eq.(3). -/
def empiricalLoss {n L M : ℕ} (H : Fin L → QnnOperator n) (theta : Fin L → ℝ)
    (c : Fin M → ℝ) (rho : Fin M → QnnDensity n) (O : QnnOperator n) : ℝ :=
  ∑ i, c i * qnnLoss (circuit H theta) (rho i).val O

/-- PDF pp.6,23: actual coordinate derivative of the empirical loss. -/
def partialLoss {n L M : ℕ} (H : Fin L → QnnOperator n) (mu : Fin L)
    (c : Fin M → ℝ) (rho : Fin M → QnnDensity n) (O : QnnOperator n) (theta : Fin L → ℝ) : ℝ :=
  deriv (fun t => empiricalLoss H (Function.update theta mu t) c rho O) (theta mu)

abbrev Sector (n : ℕ) := Fin (n / 2 + 1)

/-- PDF p.4, Eq.(12): dimension of the U(2) block. -/
def blockDim (n : ℕ) (m : Sector n) : ℕ := n - 2 * m.val + 1

/-- PDF p.4, Eq.(12): number of copies, with the predecessor zero at m=0. -/
def qnnSectorMultiplicity (n : ℕ) (m : Sector n) : ℕ :=
  n.choose m.val - if m.val = 0 then 0 else n.choose (m.val - 1)

abbrev QnnSchurIndex (n : ℕ) :=
  (m : Sector n) × (Fin (qnnSectorMultiplicity n m) × Fin (blockDim n m))

/-- PDF p.4, Eq.(13): identical blocks in all multiplicity copies. -/
def qnnSchurBlockDiagonal {n : ℕ} (B : (m : Sector n) → Matrix (Fin (blockDim n m))
    (Fin (blockDim n m)) ℂ) : Matrix (QnnSchurIndex n) (QnnSchurIndex n) ℂ :=
  fun x y => if h : x.1 = y.1 then
    if x.2.1.val = y.2.1.val then B x.1 x.2.2 (h.symm ▸ y.2.2) else 0 else 0

/-- PDF pp.13,28: four times the total-spin Casimir. -/
def spinCasimir (n : ℕ) : QnnOperator n :=
  collective n pauliX 1 ^ 2 + collective n pauliY 1 ^ 2 + collective n pauliZ 1 ^ 2

/-- PDF pp.4,6,23,28: fixed orthonormal Schur coordinates. The commutant
condition specifies Schur coordinates, without assuming variance or spectra.
The Casimir pins spin (n-2m)/2, preventing sector relabelling. -/
structure SchurFrame (n : ℕ) where
  matrix : Matrix (QnnSchurIndex n) (Qubits n) ℂ
  rows : matrix * matrix.conjTranspose = 1
  columns : matrix.conjTranspose * matrix = 1
  commutant : ∀ A : QnnOperator n, PermutationEquivariant A →
    ∃ B : (m : Sector n) → Matrix (Fin (blockDim n m)) (Fin (blockDim n m)) ℂ,
      matrix * A * matrix.conjTranspose = qnnSchurBlockDiagonal B
  spin : matrix * spinCasimir n * matrix.conjTranspose =
    qnnSchurBlockDiagonal (fun m =>
      (((n - 2 * m.val : ℕ) : ℂ) * (((n - 2 * m.val : ℕ) : ℂ) + 2)) • 1)

/-- PDF p.23, Eq.(10): row coisometry for a copy. -/
def rowMap {n : ℕ} (S : SchurFrame n) (m : Sector n) (nu : Fin (qnnSectorMultiplicity n m)) :
    Matrix (Fin (blockDim n m)) (Qubits n) ℂ :=
  fun j x => S.matrix ⟨m, (nu, j)⟩ x

/-- PDF p.6, Eq.(15): unnormalized compression. -/
def schurCompression {n : ℕ} (S : SchurFrame n) (m : Sector n)
    (nu : Fin (qnnSectorMultiplicity n m)) (A : QnnOperator n) :
    Matrix (Fin (blockDim n m)) (Fin (blockDim n m)) ℂ :=
  rowMap S m nu * A * (rowMap S m nu).conjTranspose

/-- PDF p.6, Eq.(16): sum of data compressions, not their average. -/
def aggregate {n : ℕ} (S : SchurFrame n) (m : Sector n) (A : QnnOperator n) :
    Matrix (Fin (blockDim n m)) (Fin (blockDim n m)) ℂ :=
  ∑ nu, schurCompression S m nu A

/-- PDF p.4, Eq.(13): the common equivariant block; averaging identical
copies avoids a distinguished copy. Data use aggregate instead. -/
def commonBlock {n : ℕ} (S : SchurFrame n) (m : Sector n) (A : QnnOperator n) :
    Matrix (Fin (blockDim n m)) (Fin (blockDim n m)) ℂ :=
  (1 / (qnnSectorMultiplicity n m : ℂ)) • aggregate S m A

/-- PDF p.26, Eq.(38): centered trace pairing, real on Hermitian inputs. -/
def deltaPair {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  ((A * B).trace - A.trace * B.trace / (d : ℂ)).re

/-- PDF p.6: unnormalized centered squared Hilbert-Schmidt statistic. -/
def centeredDelta {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) : ℝ := deltaPair A A

abbrev DesignKey (n : ℕ) := Bool × Sector n

/-- Balanced entry monomial of conjugation degree r. -/
def conjugationMonomial {d : ℕ} (U : Matrix (Fin d) (Fin d) ℂ) (r : ℕ)
    (a b c e : Fin r → Fin d) : ℂ :=
  (∏ t, U (a t) (b t)) * ∏ t, conj (U (c t) (e t))

/-- PDF pp.14,24-26: joint exact conjugation 2-design moments for both halves
and all blocks, including cross-sector products. No depth-convergence claim. -/
def IndependentBlockTwoDesign {n L : ℕ} (S : SchurFrame n)
    (H : Fin L → QnnOperator n) (mu : Fin L) (P : Measure (Fin L → ℝ)) : Prop :=
  ∀ r : DesignKey n → Fin 3,
  ∀ a b c e : (k : DesignKey n) → Fin (r k).val → Fin (blockDim n k.2),
    (∫ theta, ∏ k : DesignKey n,
      conjugationMonomial (commonBlock S k.2 (circuitHalf H theta mu k.1))
        (r k).val (a k) (b k) (c k) (e k) ∂P) =
    ∏ k : DesignKey n, ∫ V : Matrix.unitaryGroup (Fin (blockDim n k.2)) ℂ,
      conjugationMonomial V.val (r k).val (a k) (b k) (c k) (e k)
        ∂(QAlgorithms.Schur.unitaryHaar (blockDim n k.2))

/-- PDF p.24, Eq.(23): variance. Used on bounded measurable circuit losses. -/
def variance {X : Type*} [MeasurableSpace X] (P : Measure X) (f : X → ℝ) : ℝ :=
  (∫ x, f x ^ 2 ∂P) - (∫ x, f x ∂P) ^ 2

/-- PDF pp.5,22: real tangent commutant, including the scalar phase direction. -/
def tangentCommutant (n : ℕ) : Submodule ℝ (QnnOperator n) :=
  Submodule.span ℝ {A | A.conjTranspose = -A ∧ PermutationEquivariant A}

/-- PDF p.9: derivative of the actual output state. -/
def stateDerivative {n L : ℕ} (H : Fin L → QnnOperator n) (theta : Fin L → ℝ)
    (psi : EuclideanSpace ℂ (Qubits n)) (mu : Fin L) : EuclideanSpace ℂ (Qubits n) :=
  fderiv ℝ (fun t : Fin L → ℝ => act (circuit H t) psi) theta (Pi.single mu 1)

/-- PDF p.9: pure-state QFIM, removing the global phase direction. -/
def qfi {n L : ℕ} (H : Fin L → QnnOperator n) (theta : Fin L → ℝ)
    (psi : EuclideanSpace ℂ (Qubits n)) : Matrix (Fin L) (Fin L) ℝ :=
  fun j k => 4 * (inner ℂ (stateDerivative H theta psi j) (stateDerivative H theta psi k) -
    inner ℂ (stateDerivative H theta psi j) (act (circuit H theta) psi) *
    inner ℂ (act (circuit H theta) psi) (stateDerivative H theta psi k)).re

/-- PDF pp.3,15: a is the composed measurable label weight a(f(rho)). -/
def qnnPopulationRisk {n : ℕ} (P : Measure (QnnDensity n)) (a : QnnDensity n → ℝ)
    (O U : QnnOperator n) : ℝ := ∫ rho, a rho * qnnLoss U rho.val O ∂P

/-- PDF pp.2-3,15: empirical coefficients a(f(rho_i))/M. -/
def empiricalRisk {n M : ℕ} (a : QnnDensity n → ℝ) (O U : QnnOperator n)
    (xs : Fin M → QnnDensity n) : ℝ :=
  (1 / (M : ℝ)) * ∑ i, a (xs i) * qnnLoss U (xs i).val O

/-- PDF pp.7,15: one event controls every possible trained unitary. -/
def generalizationEvent {n M : ℕ} (P : Measure (QnnDensity n)) (a : QnnDensity n → ℝ)
    (O : QnnOperator n) (bound : ℝ) : Set (Fin M → QnnDensity n) :=
  {xs | ∀ U ∈ unitaryFamily n,
    |qnnPopulationRisk P a O U - empiricalRisk a O U xs| ≤ bound}

attribute [local instance] LieRing.ofAssociativeRing

/-- PDF p.13, Definition 5: use -i times Hermitian generators, as Eq.(1)
requires. This is the actual Lie closure rather than the whole commutant. -/
def dynamicalLie (n : ℕ) : LieSubalgebra ℝ (QnnOperator n) :=
  LieSubalgebra.lieSpan ℝ (QnnOperator n) (Set.range (fun j : Fin 3 => (-Complex.I) • qnnGenerator n j))

/-- PDF p.29, Eq.(62): binary Krawtchouk value in signed real arithmetic. -/
def krawtchouk (n k w : ℕ) : ℝ :=
  ∑ l ∈ Finset.range (k + 1), ((n - w).choose (k - l) : ℝ) *
    (w.choose l : ℝ) * (-1 : ℝ) ^ l

/-- PDF pp.4,29: the symmetric spin sector. -/
def symmetricSector (n : ℕ) : Sector n := ⟨0, by omega⟩

/-- PDF pp.15,31: transfer Haar U(2^n) to the fixed bit ordering. -/
def haarQubitUnitary {n : ℕ} (V : Matrix.unitaryGroup (Fin (2 ^ n)) ℂ) : QnnOperator n :=
  fun x y => V.val (bitsEquivFin n x) (bitsEquivFin n y)

/-- PDF p.31: one seed fixed before Haar V. -/
def haarPureInput {n : ℕ} (psi : EuclideanSpace ℂ (Qubits n))
    (V : Matrix.unitaryGroup (Fin (2 ^ n)) ℂ) : QnnOperator n :=
  pureDensity (act (haarQubitUnitary V) psi)

/-- PDF pp.32-33: a fixed architecture and real threshold. -/
def classifierFamily {n L : ℕ} (word : Fin L → Fin 3) (O : QnnOperator n) (b : ℝ) :
    Set (QnnDensity n → Bool) :=
  Set.range (fun theta : Fin L → ℝ => fun rho : QnnDensity n =>
    decide (b ≤ qnnLoss (circuit (fun j => qnnGenerator n (word j)) theta) rho.val O))

/-- PDF pp.13,33-34: uniform sampling of the parameter box. -/
def uniformParameters (L : ℕ) : Measure (Fin L → ℝ) :=
  Measure.pi (fun _ : Fin L =>
    (ENNReal.ofReal (1 / (2 * Real.pi))) • volume.restrict (Set.Icc 0 (2 * Real.pi)))

/-- PDF p.34, Eq.(96): eventual inverse-polynomial lower bound. -/
def InversePolynomialLower (f : ℕ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ k N : ℕ, ∀ n ≥ N, c / (n : ℝ) ^ k ≤ f n

/-- PDF pp.33-34: below-mean point condition AND exponential tail envelope,
with constants before size and tail threshold. -/
def HasNarrowGorge (L : ℕ → ℕ) (f : (n : ℕ) → (Fin (L n) → ℝ) → ℝ) : Prop :=
  (∃ gap : ℕ → ℝ, InversePolynomialLower gap ∧ ∃ N : ℕ, ∀ n ≥ N,
    ∃ theta, f n theta ≤ (∫ t, f n t ∂(uniformParameters (L n))) - gap n) ∧
  ∃ C b : ℝ, 0 < C ∧ 1 < b ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ d : ℝ, 0 < d →
    ((uniformParameters (L n))
      {theta | d ≤ |f n theta - (∫ t, f n t ∂(uniformParameters (L n)))|}).toReal ≤
        C / (b ^ n * d ^ 2)

section SanityChecks

/-! Small checks for definition conventions; source results remain unproved. -/

example (n : ℕ) (A B : QnnOperator n) : ⁅A, B⁆ = A * B - B * A := by
  rfl

example (n : ℕ) : blockDim n (symmetricSector n) = n + 1 := by
  simp [blockDim, symmetricSector]

example (n : ℕ) : qnnSectorMultiplicity n (symmetricSector n) = 1 := by
  simp [qnnSectorMultiplicity, symmetricSector]

example {n : ℕ} (S : SchurFrame n) (m : Sector n) (nu : Fin (qnnSectorMultiplicity n m)) :
    schurCompression S m nu 0 = 0 := by simp [schurCompression]

example : centeredDelta (0 : Matrix (Fin 1) (Fin 1) ℂ) = 0 := by simp [centeredDelta, deltaPair]

example {n : ℕ} (rho : Fin 0 → QnnDensity n) (c : Fin 0 → ℝ) :
    dataOperator c rho = 0 := by simp [dataOperator]

example {n : ℕ} (H : Fin 0 → QnnOperator n) (theta : Fin 0 → ℝ) : circuit H theta = 1 := by
  simp [circuit, orderedProd]

example (U : Matrix (Fin 1) (Fin 1) ℂ) (a b c e : Fin 0 → Fin 1) :
    conjugationMonomial U 0 a b c e = 1 := by simp [conjugationMonomial]

example (n : ℕ) : (1 : QnnOperator n) ∈ unitaryFamily n := by
  simp [unitaryFamily, PermutationEquivariant]

example : collective 0 pauliZ 1 = 0 := by
  simp [collective, Finset.powersetCard_one]

example : krawtchouk 0 0 0 = 1 := by
  norm_num [krawtchouk]

example : centeredDelta (1 : Matrix (Fin 1) (Fin 1) ℂ) = 0 := by
  simp [centeredDelta, deltaPair]

example {n L : ℕ} (H : Fin L → QnnOperator n) (theta : Fin L → ℝ) (O : QnnOperator n)
    (rho : Fin 0 → QnnDensity n) (c : Fin 0 → ℝ) : empiricalLoss H theta c rho O = 0 := by
  simp [empiricalLoss]

example {n : ℕ} (P : Measure (QnnDensity n)) (O U : QnnOperator n) :
    qnnPopulationRisk P (fun _ => 0) O U = 0 := by simp [qnnPopulationRisk]

example {n : ℕ} (a : QnnDensity n → ℝ) (O U : QnnOperator n) (xs : Fin 0 → QnnDensity n) :
    empiricalRisk a O U xs = 0 := by simp [empiricalRisk]

example {n : ℕ} (H : Fin 0 → QnnOperator n) (theta : Fin 0 → ℝ)
    (psi : EuclideanSpace ℂ (Qubits n)) : qfi H theta psi = 0 := by
  ext i j
  exact Fin.elim0 i

end SanityChecks

end QAlgorithms.Papers.Independent.Support50.P30


