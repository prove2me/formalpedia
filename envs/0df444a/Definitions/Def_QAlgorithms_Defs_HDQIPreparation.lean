-- Prove2me | Definitions.Def_QAlgorithms_Defs_HDQIPreparation
-- name    : QAlgorithms_Defs_HDQIPreparation
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:26:11.184029+00:00
-- url     : https://prove2.me/theorems/244aecd0-341c-43ed-8790-618a82a30f90
-- title:
--   HDQIPreparation
-- statement:
--   HDQIPreparation
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\HDQIPreparation.lean

import Definitions.Def_QAlgorithms_Defs_SingleQubitCert
import Definitions.Def_QAlgorithms_Defs_HamiltonianDQI
import Definitions.Def_QAlgorithms_Defs_MatrixProductStates
import Definitions.Def_QAlgorithms_Defs_IdealArithmetic
import Definitions.Def_QAlgorithms_Defs_ExactChannelCircuits
noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

namespace QAlgorithms

/-- An exact zero-ancilla preparation circuit builds the reference from H,P, prepares Bell pairs, applies controlled terms, Bell change, one plain forward decoder step and inverse Bell change; discard label/purification/workspace registers and retain B. Source: arxiv-2601.18773v1 PDF p.8; arxiv-2601.18773v1 PDF p.9. -/
structure HDQIPreparation (n m : ℕ) where
  work : ℕ
  preprocessing : ArithmeticProgram
  classicalInput : ℕ → ℝ
  circuit : OracleCircuit oneTwoQubitGateSet (fun _ : Fin 1 => m + (n + n)) (m + (n + n) + work)
  outputOrder : Fin (n + (m + n + work)) ≃ Fin (m + (n + n) + work)
  gateEntries : ∀ s ∈ circuit, ∀ g, s = OracleStep.gate g →
    ∃ result, preprocessing.eval classicalInput = some result ∧
      ∀ y z : Qubits g.gate.arity, ∃ a b : ℕ,
        g.gate.mat y z = (result a : ℂ) + (result b : ℂ) * Complex.I

/-- Operational helper HDQIPreparation.output for the source construction. Source: arxiv-2601.18773v1 PDF p.8; arxiv-2601.18773v1 PDF p.9. -/
def HDQIPreparation.output {n m : ℕ} (P : HDQIPreparation n m)
    (D : Matrix (Qubits m × Qubits (n + n)) (Qubits m × Qubits (n + n)) ℂ) :
    Matrix (Qubits n) (Qubits n) ℂ :=
  let oracle := D.submatrix (qubitsAppendEquiv m (n + n)) (qubitsAppendEquiv m (n + n))
  let psi := act (P.circuit.unitary fun _ => oracle) (zeroKet _)
  traceRight ((pureDensity psi).submatrix
    (fun p => Fin.append p.1 p.2 ∘ P.outputOrder.symm)
    (fun p => Fin.append p.1 p.2 ∘ P.outputOrder.symm))

/-- Operational helper HDQIPreparation.classicalCost for the source construction. Source: arxiv-2601.18773v1 PDF p.8; arxiv-2601.18773v1 PDF p.9. -/
def HDQIPreparation.classicalCost {n m : ℕ} (P : HDQIPreparation n m) : ℕ :=
  P.preprocessing.cost P.classicalInput

/-- Sanity test. Source: arxiv-2601.18773v1 PDF p.8; arxiv-2601.18773v1 PDF p.9. -/
example {n m : ℕ} (P : HDQIPreparation n m) :
    P.classicalCost = P.preprocessing.cost P.classicalInput := rfl

/-- Sanity test. Source: arxiv-2601.18773v1 PDF p.8; arxiv-2601.18773v1 PDF p.9. -/
example {N n m : ℕ} (w : Fin (m + (n + n)) ↪ Fin N) :
    OracleCircuit.plainQueryCount ([OracleStep.query 0 false none w (fun c h => by cases h)] :
      OracleCircuit oneTwoQubitGateSet (fun _ : Fin 1 => m + (n + n)) N) 0 = 1 := rfl

end QAlgorithms


