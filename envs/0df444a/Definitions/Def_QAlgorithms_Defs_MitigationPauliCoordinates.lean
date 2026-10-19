-- Prove2me | Definitions.Def_QAlgorithms_Defs_MitigationPauliCoordinates
-- name    : QAlgorithms_Defs_MitigationPauliCoordinates
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T18:59:56.443614+00:00
-- url     : https://prove2.me/theorems/ec11ab13-debc-4369-862b-80b606d2e7e8
-- title:
--   MitigationPauliCoordinates
-- statement:
--   MitigationPauliCoordinates
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\MitigationPauliCoordinates.lean

import Definitions.Def_QAlgorithms_Defs_QECC
noncomputable section

open scoped Matrix ComplexOrder

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

namespace QAlgorithms.ErrorMitigation

/-- Labels use the source Pauli order I,X,Y,Z (1712.09271 pp.12--13). -/
abbrev PauliIndex (n : ℕ) := Fin n → Stabilizer.Pauli

/-- arxiv-1712.09271v2 PDF p.12. -/
def pauliStateVector {n : ℕ} (rho : Matrix (Qubits n) (Qubits n) ℂ) : PauliIndex n → ℝ :=
  fun sigma => (pauliOps sigma*rho).trace.re

/-- arxiv-1712.09271v2 PDF p.13. -/
def pauliObservableRow {n : ℕ} (Q : Matrix (Qubits n) (Qubits n) ℂ) : PauliIndex n → ℝ :=
  fun sigma => ((2 : ℝ)^n)⁻¹*(pauliOps sigma*Q).trace.re

/-- arxiv-1712.09271v2 PDF p.3; arxiv-1712.09271v2 PDF p.13. -/
def pauliTransferMatrix {n : ℕ}
    (O : Matrix (Qubits n) (Qubits n) ℂ →ₗ[ℂ] Matrix (Qubits n) (Qubits n) ℂ) :
    Matrix (PauliIndex n) (PauliIndex n) ℝ :=
  Matrix.of fun sigma tau => ((2 : ℝ)^n)⁻¹*(pauliOps sigma*O (pauliOps tau)).trace.re

/-- The computed complex-linear Kraus map (1712.09271 p.3). -/
def krausLinearMap {K I J : Type*} [Fintype K] [Fintype I]
    (E : K → Matrix J I ℂ) : Matrix I I ℂ →ₗ[ℂ] Matrix J J ℂ where
  toFun := krausApply E
  map_add' X Y := by simp [krausApply,Matrix.mul_add,Matrix.add_mul,Finset.sum_add_distrib]
  map_smul' a X := by simp [krausApply,Matrix.mul_smul,Matrix.smul_mul,Finset.smul_sum]

/-- Sanity check for the source model (arxiv-1712.09271v2 PDF p.12). -/
example {n : ℕ} : pauliStateVector (0 : Matrix (Qubits n) (Qubits n) ℂ) = 0 := by
  funext i; simp [pauliStateVector]

end QAlgorithms.ErrorMitigation


