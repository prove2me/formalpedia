-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P09_Model
-- name    : QAlgorithms_Papers_Independent_Independent1_P09_Model
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:22:20.184148+00:00
-- url     : https://prove2.me/theorems/af18a5ba-aa6f-43d3-af40-066e1ca1ffd2
-- title:
--   Practical Quantum Error Mitigation for Near-Future Applications: supporting definitions
-- statement:
--   Reviewed paper-local supporting definitions and conventions. The attached text aggregates the existing blind readbacks of every definition; it makes no theorem proof claim.
-- source:
--   Practical Quantum Error Mitigation for Near-Future Applications, arXiv:1712.09271v2. PDF SHA-256: 6911d403c4bf7ec58c8dade31dfb949dd3b31bdeee17d4a1f85bb8f80e504bb7. Exact locators remain in declaration docstrings.

import Definitions.Def_QAlgorithms_Defs_MitigationTrials
import Definitions.Def_QAlgorithms_Defs_MitigationTomography
import Definitions.Def_QAlgorithms_Defs_MitigationDecompositions
import Definitions.Def_QAlgorithms_Defs_Hamiltonian
/-! Endo, Benjamin and Li, arXiv:1712.09271v2; citations use PDF pages.
Source defects and construction deferrals are recorded in the assigned chunk. -/

noncomputable section

open scoped Matrix ComplexOrder NNReal ENNReal

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Independent1.P09

open ErrorMitigation

def pauliOrder : Fin 4 → Stabilizer.Pauli :=
  ![Stabilizer.Pauli.I, Stabilizer.Pauli.X, Stabilizer.Pauli.Y, Stabilizer.Pauli.Z]

def localTransfer (i : Fin 16) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun a b => (2⁻¹ : ℝ) *
    ((pauliOrder a).mat * tableIBasis i (pauliOrder b).mat).trace.re

def localFlat (B : Fin 16 → Matrix (Fin 4) (Fin 4) ℝ) : Matrix (Fin 16) (Fin 16) ℝ :=
  Matrix.of fun p i => localBasisMatrix B (finProdFinEquiv.symm p) i

def tensorFlat {n : ℕ} (B : Fin n → Fin 16 → Matrix (Fin 4) (Fin 4) ℝ) :
    Matrix (Fin n → Fin 16) (Fin n → Fin 16) ℝ :=
  Matrix.of fun p i => ∏ j, localFlat (B j) (p j) (i j)

/-- Column-then-row coordinates agree with Eq. (2). Printed D3 varies the column first;
we transpose each local index pair in D3 to preserve the reconstruction identity D1. -/
def interleave {n : ℕ} (E : Matrix (Fin n → Fin 4) (Fin n → Fin 4) ℝ) :
    (Fin n → Fin 16) → ℝ :=
  fun p => E (fun j => ((finProdFinEquiv : Fin 4 × Fin 4 ≃ Fin 16).symm (p j)).2)
    (fun j => ((finProdFinEquiv : Fin 4 × Fin 4 ≃ Fin 16).symm (p j)).1)

def tensorCoordinates {n : ℕ} (B : Fin n → Fin 16 → Matrix (Fin 4) (Fin 4) ℝ)
    (E : Matrix (Fin n → Fin 4) (Fin n → Fin 4) ℝ) : (Fin n → Fin 16) → ℝ :=
  (tensorFlat B)⁻¹.mulVec (interleave E)

def tensorOperation {n : ℕ} (B : Fin n → Fin 16 → Matrix (Fin 4) (Fin 4) ℝ)
    (i : Fin n → Fin 16) : Matrix (Fin n → Fin 4) (Fin n → Fin 4) ℝ :=
  Matrix.of fun a b => ∏ j, B j (i j) (a j) (b j)

def entryMax {I J : Type*} [Fintype I] [Fintype J] (A : Matrix I J ℝ) : ℝ :=
  (Finset.univ.sup fun p : I × J => ‖A p.1 p.2‖₊ : ℝ≥0)

def leastSingular {d : ℕ} (hd : 0 < d) (A : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  Real.sqrt (ascEigenvalues (A.transpose * A) ⟨0, by simpa using hd⟩)

def tensorMatrix {n : ℕ} (A : Fin n → Matrix (Fin 4) (Fin 4) ℝ) :
    Matrix (Fin n → Fin 4) (Fin n → Fin 4) ℝ :=
  Matrix.of fun a b => ∏ j, A j (a j) (b j)

def maxLocalError {n : ℕ} (A : Fin n → Matrix (Fin 4) (Fin 4) ℝ)
    (reference : Matrix (Fin 4) (Fin 4) ℝ) : ℝ :=
  (Finset.univ.sup fun j => Real.toNNReal (specNorm (A j - reference)) : ℝ≥0)

def idealPreparation (i : Fin 4) : Matrix Bool Bool ℂ :=
  pureDensity ((![ket false, ket true, act hadamard (ket false),
    act (phaseS * hadamard) (ket false)] : Fin 4 → EuclideanSpace ℂ Bool) i)

def referenceInput : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun a i => ((pauliOrder a).mat * idealPreparation i).trace.re

def referenceOutput : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun i a => (2⁻¹ : ℝ) * ((pauliOrder a).mat * (pauliOrder i).mat).trace.re

example : pauliOrder 0 = Stabilizer.Pauli.I ∧ pauliOrder 3 = Stabilizer.Pauli.Z := ⟨rfl,rfl⟩

example : localFlat (fun _ => (0 : Matrix (Fin 4) (Fin 4) ℝ)) = 0 := rfl

example : interleave (0 : Matrix (Fin 1 → Fin 4) (Fin 1 → Fin 4) ℝ) = 0 := rfl

example (B : Fin 0 → Fin 16 → Matrix (Fin 4) (Fin 4) ℝ) (i : Fin 0 → Fin 16)
    (a b : Fin 0 → Fin 4) : tensorOperation B i a b = 1 := by simp [tensorOperation]

example (B : Fin 0 → Fin 16 → Matrix (Fin 4) (Fin 4) ℝ)
    (i j : Fin 0 → Fin 16) : tensorFlat B i j = 1 := by simp [tensorFlat]

example {I J : Type*} [Fintype I] [Fintype J] : entryMax (0 : Matrix I J ℝ) = 0 := by
  simp [entryMax]

example (A : Fin 0 → Matrix (Fin 4) (Fin 4) ℝ) : tensorMatrix A = 1 := by
  ext a b
  simp [tensorMatrix, Matrix.one_apply, Subsingleton.elim a b]

example (reference : Matrix (Fin 4) (Fin 4) ℝ) :
    maxLocalError (fun i : Fin 0 => Fin.elim0 i) reference = 0 := by
  simp [maxLocalError]

example : referenceInput 0 0 = 1 := by
  norm_num [referenceInput,idealPreparation,pauliOrder,Stabilizer.Pauli.mat,
    pureDensity,ket,Matrix.trace,Fintype.sum_bool]

example : referenceOutput 0 0 = 1 := by
  norm_num [referenceOutput,pauliOrder,Stabilizer.Pauli.mat,Matrix.trace,Fintype.sum_bool]

/-! Table I uses algebraic words, executed from right to left. -/

inductive TableLetter where
  | h | s | project

def TableLetter.mat : TableLetter → Matrix Bool Bool ℂ
  | .h => hadamard
  | .s => phaseS
  | .project => Matrix.single false false 1

def tableWord (i : Fin 16) : List TableLetter :=
  let rz : List TableLetter := [.s,.s,.s]
  let rx : List TableLetter := [.h,.s,.s,.s,.h]
  let pi : List TableLetter := [.project]
  (![[], rx++rx, rx++rx++rz++rz, rz++rz,
    rx, rz++rz++rz++rx++rz, rz, rx++rz++rz, rz++rx++rz, rx++rx++rz,
    rz++rz++rz++rx++rx++rx++pi++rx++rz,
    rx++pi++rx++rx++rx, pi,
    rz++rz++rz++rx++rx++rx++pi++rx++rx++rx++rz,
    rx++pi++rx++rx++rx++rz++rz, pi++rx++rx] : Fin 16 → List TableLetter) i

def tableWordMap (i : Fin 16) : Matrix Bool Bool ℂ →ₗ[ℂ] Matrix Bool Bool ℂ :=
  krausLinearMap (fun _ : Fin 1 => ((tableWord i).map TableLetter.mat).prod)

example : tableWord 0 = [] ∧ tableWord 12 = [.project] := ⟨rfl,rfl⟩

example (X : Matrix Bool Bool ℂ) : tableWordMap 0 X = X := by
  simp [tableWordMap,tableWord,krausLinearMap,krausApply]

def tCoefficients : Fin 3 → ℝ := ![1/2,-(Real.sqrt 2-1)/2,Real.sqrt 2/2]

def tMatrices : Fin 3 → Matrix Bool Bool ℂ := ![1,pauliZ,tableIMatrix 6 ^ 3]

def cnotTerms : Fin 12 → (Fin 16 × Fin 16) × ℝ :=
  ![((0,1),1/2),((3,0),1/2),((0,4),-1/2),((6,0),-1/2),
    ((3,4),-1/2),((6,1),-1/2),((3,1),1),((6,4),1),
    ((0,10),1),((12,0),1),((3,10),-1),((12,1),-1)]

def leakageFactor (p : ℝ) : ℝ := (Real.sqrt (1-p)-(1-p))/p

def leakageMap (p : ℝ) : Matrix Bool Bool ℂ →ₗ[ℂ] Matrix Bool Bool ℂ :=
  krausLinearMap (fun _ : Fin 1 => Matrix.diagonal fun b : Bool =>
    if b then (Real.sqrt (1-p) : ℂ) else 1)

def leakageComponent (p : ℝ) : Matrix Bool Bool ℂ →ₗ[ℂ] Matrix Bool Bool ℂ where
  toFun X := Matrix.single false false (X false false) + (leakageFactor p : ℂ) •
    (Matrix.single false true (X false true) + Matrix.single true false (X true false))
  map_add' X Y := by simp [Matrix.single_add,smul_add]; abel
  map_smul' a X := by
    ext i j
    simp [Matrix.single_apply, mul_add, mul_assoc, mul_left_comm, mul_comm]

example : tCoefficients 0 = 1/2 ∧ tMatrices 0 = 1 := ⟨rfl,rfl⟩

example : cnotTerms 0 = ((0,1),1/2) := rfl

example (X : Matrix Bool Bool ℂ) : leakageMap 0 X = X := by
  simp [leakageMap,krausLinearMap,krausApply]

example : leakageFactor 0 = 0 := by simp [leakageFactor]

example (p : ℝ) : leakageComponent p 0 = 0 := map_zero _






















end QAlgorithms.Papers.Independent.Independent1.P09


