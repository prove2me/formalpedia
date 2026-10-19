-- Prove2me | Definitions.Def_QAlgorithms_Defs_PauliDesigns
-- name    : QAlgorithms_Defs_PauliDesigns
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T18:37:17.723978+00:00
-- url     : https://prove2.me/theorems/8ddd8798-5d14-49fd-8917-e0410c361db3
-- title:
--   PauliDesigns
-- statement:
--   PauliDesigns
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\PauliDesigns.lean

import Definitions.Def_QAlgorithms_Defs_QECC
noncomputable section

namespace QAlgorithms.PauliDesign

/-- Phase-free n-qubit Pauli settings (0909.3304 p.2; 1205.2300 p.4). Identity is included. -/
abbrev Label (n : ℕ) := Fin n → Stabilizer.Pauli

/-- Independent uniform settings with replacement (0909.3304 p.2; 1205.2300 p.4). -/
def uniformDesign (n m : ℕ) : PMF (Fin m → Label n) :=
  letI : Nonempty Stabilizer.Pauli := ⟨.I⟩
  PMF.uniformOfFintype _

/-- Unscaled expectation data for the recorded design (0909.3304 p.2, Eq.(1)). -/
def expectationData {n m : ℕ} (A : Fin m → Label n)
    (X : Matrix (Qubits n) (Qubits n) ℂ) (_hermitian : X.IsHermitian) : Fin m → ℝ :=
  fun i => (pauliOps (A i)*X).trace.re

example (n : ℕ) (a : Fin 0 → Label n) : uniformDesign n 0 a = 1 := by
  unfold uniformDesign
  rw [PMF.uniformOfFintype_apply]
  simp

example {n m : ℕ} (A : Fin m → Label n) :
    expectationData A 0 Matrix.isHermitian_zero = 0 := by
  funext i
  simp [expectationData]

end QAlgorithms.PauliDesign


