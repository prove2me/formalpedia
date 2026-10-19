-- Prove2me | Definitions.Def_QAlgorithms_Defs_ExactPauliRecovery
-- name    : QAlgorithms_Defs_ExactPauliRecovery
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:21:11.820719+00:00
-- url     : https://prove2.me/theorems/8d2f88e5-c5d7-4969-ad77-4b077fcf8027
-- title:
--   ExactPauliRecovery
-- statement:
--   ExactPauliRecovery
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\ExactPauliRecovery.lean

import Definitions.Def_QAlgorithms_Defs_PauliDesigns
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
noncomputable section

namespace QAlgorithms.LowRankTomography

/-- Hermitian trace-one competitors matching the exact data; positivity is not a constraint
(0909.3304 p.2, Eq.(1)). -/
def feasibleSet {n m : ℕ} (A : Fin m → PauliDesign.Label n) (y : Fin m → ℝ) :
    Set (Matrix (Qubits n) (Qubits n) ℂ) :=
  {X | X.IsHermitian ∧ X.trace = 1 ∧ ∀ i, (pauliOps (A i)*X).trace.re = y i}

/-- Attained trace-norm minimizers of the exact program (0909.3304 p.2, Eq.(1)).
An infeasible data vector has no optimizer; there is no default selected matrix. -/
def optimizerSet {n m : ℕ} (A : Fin m → PauliDesign.Label n) (y : Fin m → ℝ) :
    Set (Matrix (Qubits n) (Qubits n) ℂ) :=
  {X | X ∈ feasibleSet A y ∧ ∀ Y ∈ feasibleSet A y, traceNorm X ≤ traceNorm Y}

example (A : Fin 0 → PauliDesign.Label 0) (y : Fin 0 → ℝ) :
    (1 : Matrix (Qubits 0) (Qubits 0) ℂ) ∈ feasibleSet A y := by
  refine ⟨Matrix.isHermitian_one, by simp [Matrix.trace_one], fun i => Fin.elim0 i⟩

example {n m : ℕ} (A : Fin m → PauliDesign.Label n) (y : Fin m → ℝ)
    (h : feasibleSet A y = ∅) : optimizerSet A y = ∅ := by
  ext X
  simp [optimizerSet, h]

end QAlgorithms.LowRankTomography


