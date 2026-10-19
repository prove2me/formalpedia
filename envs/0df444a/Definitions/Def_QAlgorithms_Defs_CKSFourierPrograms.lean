-- Prove2me | Definitions.Def_QAlgorithms_Defs_CKSFourierPrograms
-- name    : QAlgorithms_Defs_CKSFourierPrograms
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:27:17.636391+00:00
-- url     : https://prove2.me/theorems/cbe68730-2197-4b77-b352-5a765af9b188
-- title:
--   CKSFourierPrograms
-- statement:
--   CKSFourierPrograms
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\CKSFourierPrograms.lean

import Definitions.Def_QAlgorithms_Defs_CKSFourierSimulation
import Definitions.Def_QAlgorithms_Defs_HeraldedLinearSystems
noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.CKSFourier

/-- QAlgorithms.CKSFourier.AlgorithmConstruction: arxiv-1511.02306v2 PDF p.8, arxiv-1511.02306v2 PDF p.9, arxiv-1511.02306v2 PDF p.10, arxiv-1511.02306v2 PDF p.12, arxiv-1511.02306v2 PDF p.14, arxiv-1511.02306v2 PDF p.15. Source domains are explicit below. -/
structure AlgorithmConstruction (N : ℕ) where
  grid : Grid
  selectorWires : Finset (Fin N)
  labels : grid.Index ↪ Qubits N
  labels_supported : ∀ j q, q ∉ selectorWires → labels j q = false
  coefficientPrep : Circuit oneTwoQubitGateSet N
  prep_support : ActsWithin selectorWires coefficientPrep.unitary
  prep_state : ∀ z, act coefficientPrep.unitary (zeroKet N) z =
    ∑ j, if labels j = z then coefficientState grid j else 0
  coefficientUnprep : Circuit oneTwoQubitGateSet N
  unprep_eq : coefficientUnprep.unitary = star coefficientPrep.unitary
  goodReflection : Circuit oneTwoQubitGateSet N
  startReflection : Circuit oneTwoQubitGateSet N
  goodProjector : Matrix (Qubits N) (Qubits N) ℂ
  goodProjector_eq : goodProjector = Matrix.diagonal fun z =>
    if ∀ q ∈ selectorWires, z q = false then 1 else 0
  goodReflection_eq : goodReflection.unitary = 1-2 • goodProjector
  startReflection_eq : startReflection.unitary = 1-2 • pureDensity (zeroKet N)
  amplificationSchedule : List ℕ

/-- QAlgorithms.CKSFourier.AlgorithmConstruction.call: arxiv-1511.02306v2 PDF p.8, arxiv-1511.02306v2 PDF p.9, arxiv-1511.02306v2 PDF p.10, arxiv-1511.02306v2 PDF p.12, arxiv-1511.02306v2 PDF p.14, arxiv-1511.02306v2 PDF p.15. Source domains are explicit below. -/
def AlgorithmConstruction.call {N : ℕ} (P : AlgorithmConstruction N) (label : Fin 2) (adj : Bool) :
    OracleCircuit oneTwoQubitGateSet (fun _ : Fin 2 => N) N :=
  [.query label adj none (Function.Embedding.refl _) (fun _ h => by cases h)]

/-- QAlgorithms.CKSFourier.AlgorithmConstruction.core: arxiv-1511.02306v2 PDF p.8, arxiv-1511.02306v2 PDF p.9, arxiv-1511.02306v2 PDF p.10, arxiv-1511.02306v2 PDF p.12, arxiv-1511.02306v2 PDF p.14, arxiv-1511.02306v2 PDF p.15. Source domains are explicit below. -/
def AlgorithmConstruction.core {N : ℕ} (P : AlgorithmConstruction N) (inverse : Bool) :
    OracleCircuit oneTwoQubitGateSet (fun _ : Fin 2 => N) N :=
  P.coefficientPrep.map OracleStep.gate ++ P.call 0 inverse ++ P.coefficientUnprep.map OracleStep.gate

/-- QAlgorithms.CKSFourier.AlgorithmConstruction.attempt: arxiv-1511.02306v2 PDF p.8, arxiv-1511.02306v2 PDF p.9, arxiv-1511.02306v2 PDF p.10, arxiv-1511.02306v2 PDF p.12, arxiv-1511.02306v2 PDF p.14, arxiv-1511.02306v2 PDF p.15. Source domains are explicit below. -/
def AlgorithmConstruction.attempt {N : ℕ} (P : AlgorithmConstruction N) (iterations : ℕ) :
    OracleCircuit oneTwoQubitGateSet (fun _ : Fin 2 => N) N :=
  P.call 1 false ++ P.core false ++
    (List.replicate iterations (P.goodReflection.map OracleStep.gate ++ P.core true ++
      P.call 1 true ++ P.startReflection.map OracleStep.gate ++ P.call 1 false ++ P.core false)).flatten

/-- QAlgorithms.CKSFourier.AlgorithmConstruction.successDensity: arxiv-1511.02306v2 PDF p.8, arxiv-1511.02306v2 PDF p.9, arxiv-1511.02306v2 PDF p.10, arxiv-1511.02306v2 PDF p.12, arxiv-1511.02306v2 PDF p.14, arxiv-1511.02306v2 PDF p.15. Source domains are explicit below. -/
def AlgorithmConstruction.successDensity {N : ℕ} (P : AlgorithmConstruction N)
    (O : Fin 2 → Matrix (Qubits N) (Qubits N) ℂ) :
    List ℕ → Matrix (Qubits N) (Qubits N) ℂ
  | [] => 0
  | k::rest =>
      let rho := conjSuperop ((P.attempt k).unitary O) (pureDensity (zeroKet N))
      let success := conjSuperop P.goodProjector rho
      success+((1-success.trace.re : ℝ) : ℂ) • P.successDensity O rest

/-- QAlgorithms.CKSFourier.AlgorithmConstruction.queryBudget: arxiv-1511.02306v2 PDF p.8, arxiv-1511.02306v2 PDF p.9, arxiv-1511.02306v2 PDF p.10, arxiv-1511.02306v2 PDF p.12, arxiv-1511.02306v2 PDF p.14, arxiv-1511.02306v2 PDF p.15. Source domains are explicit below. -/
def AlgorithmConstruction.queryBudget {N : ℕ} (P : AlgorithmConstruction N) (label : Fin 2) : ℕ :=
  (P.amplificationSchedule.map fun k => (P.attempt k).queryCount label).sum

example {N : ℕ} (P : AlgorithmConstruction N) (O : Fin 2 → Matrix (Qubits N) (Qubits N) ℂ) :
    P.successDensity O [] = 0 := rfl

example {N : ℕ} (P : AlgorithmConstruction N) : (P.call 0 false).queryCount 0 = 1 := rfl

end QAlgorithms.CKSFourier


