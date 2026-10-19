-- Prove2me | Definitions.Def_QAlgorithms_Defs_MitigationOperationBasis
-- name    : QAlgorithms_Defs_MitigationOperationBasis
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:16:36.186113+00:00
-- url     : https://prove2.me/theorems/7f634d42-2dc3-4e91-9ff9-0299a112d1ab
-- title:
--   MitigationOperationBasis
-- statement:
--   MitigationOperationBasis
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\MitigationOperationBasis.lean

import Definitions.Def_QAlgorithms_Defs_MitigationPauliCoordinates
import Definitions.Def_QAlgorithms_Defs_QuantumInstruments
noncomputable section

open scoped Matrix ComplexOrder

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

namespace QAlgorithms.ErrorMitigation

/-- Table I's sixteen matrices, 0-based in precisely its printed order (1712.09271 p.4). -/
def tableIMatrix : Fin 16 → Matrix Bool Bool ℂ :=
  let R := fun P => ((Real.sqrt 2)⁻¹ : ℂ) • (1+Complex.I • P)
  let S := fun P Q => ((Real.sqrt 2)⁻¹ : ℂ) • (P+Q)
  let pi := fun P => (2⁻¹ : ℂ) • (1+P)
  let pi2 := fun P Q => (2⁻¹ : ℂ) • (P+Complex.I • Q)
  ![1,pauliX,pauliY,pauliZ,R pauliX,R pauliY,R pauliZ,
    S pauliY pauliZ,S pauliZ pauliX,S pauliX pauliY,
    pi pauliX,pi pauliY,pi pauliZ,pi2 pauliY pauliZ,pi2 pauliZ pauliX,pi2 pauliX pauliY]

/-- arxiv-1712.09271v2 PDF p.4; arxiv-1712.09271v2 PDF p.5. -/
def tableIBasis (i : Fin 16) : Matrix Bool Bool ℂ →ₗ[ℂ] Matrix Bool Bool ℂ :=
  krausLinearMap (fun _ : Fin 1 => tableIMatrix i)

/-- Column stacking of actual one-qubit operation matrices (1712.09271 p.5, Eq.(2)).
arxiv-1712.09271v2 PDF p.5; arxiv-1712.09271v2 PDF p.13. -/
def localBasisMatrix (B : Fin 16 → Matrix (Fin 4) (Fin 4) ℝ) :
    Matrix (Fin 4 × Fin 4) (Fin 16) ℝ := Matrix.of fun p i => B i p.2 p.1

/-- arxiv-1712.09271v2 PDF p.5; arxiv-1712.09271v2 PDF p.13. -/
def tensorVectorization (n : ℕ) :
    ((Fin n → Fin 4) × (Fin n → Fin 4)) ≃ (Fin n → Fin 4 × Fin 4) where
  toFun p := fun j => (p.2 j,p.1 j)
  invFun p := (fun j => (p j).2,fun j => (p j).1)
  left_inv p := rfl
  right_inv p := by funext j; exact Prod.eta _

/-- Tensor synthesis with local (column,row) indices (1712.09271 p.13, D1--D3). -/
def tensorBasisMatrix {n : ℕ} (B : Fin n → Fin 16 → Matrix (Fin 4) (Fin 4) ℝ) :
    Matrix (Fin n → Fin 4 × Fin 4) (Fin n → Fin 16) ℝ :=
  Matrix.of fun p i => ∏ j, localBasisMatrix (B j) (p j) (i j)

/-- arxiv-1712.09271v2 PDF p.5; arxiv-1712.09271v2 PDF p.6. -/
def localizedOperation {k n : ℕ}
    (w : Fin k ↪ Fin n) (M : CopyMeasurements.QuantumInstrument (Qubits k) Bool)
    (accepted : Bool) : Matrix (Qubits n) (Qubits n) ℂ →ₗ[ℂ] Matrix (Qubits n) (Qubits n) ℂ :=
  krausLinearMap (fun j => embedOp (M.kraus accepted j) w)

/-- Sanity check for the source model (arxiv-1712.09271v2 PDF p.4). -/
example (X : Matrix Bool Bool ℂ) : tableIBasis 0 X = X := by
  simp [tableIBasis,tableIMatrix,krausLinearMap,krausApply]

/-- Sanity check for the source model (arxiv-1712.09271v2 PDF p.4). -/
example (n : ℕ) (p : (Fin n → Fin 4) × (Fin n → Fin 4)) :
    (tensorVectorization n).symm (tensorVectorization n p) = p := rfl

end QAlgorithms.ErrorMitigation


