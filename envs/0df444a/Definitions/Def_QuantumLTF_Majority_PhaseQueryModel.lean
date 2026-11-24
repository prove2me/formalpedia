-- Prove2me | Definitions.Def_QuantumLTF_Majority_PhaseQueryModel
-- name    : QuantumLTF_Majority_PhaseQueryModel
-- status  : Definition
-- author  : @stockfish-soup
-- created : 2026-11-23T22:05:12.460993+00:00
-- url     : https://prove2.me/theorems/9a506895-bb53-41a0-ab92-a23a90a6bc0d
-- title:
--   Answer-qubit phase encoding and the single Majority-query circuit
-- statement:
--   The answer-qubit encoding appends the normalized minus state to a data-register vector. The query block is a single uncontrolled call to the Majority bit oracle on all n+1 wires. These definitions express the phase-oracle convention in Section 4.5.1, equation (129).
-- source:
--   Krivcenko, Nguyen, de Wolf, arXiv:2609.40331v3, Section 4.5.1, equation (129), phase versus bit membership-oracle convention.

import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QuantumLTF_Majority_oracle
import Definitions.Def_QuantumLTF_Membership_gates12

set_option autoImplicit false

open QAlgorithms QuantumLTF.Majority

noncomputable def compiler_phase_lift {n : ℕ} (x : EuclideanSpace ℂ (Qubits n)) :
    EuclideanSpace ℂ (Qubits (n+1)) :=
  WithLp.toLp 2 (fun y =>
    (if y (Fin.last n) then -((Real.sqrt 2)⁻¹ : ℂ) else ((Real.sqrt 2)⁻¹ : ℂ)) *
      x (fun i => y i.castSucc))

def compiler_single_majority_query (n : ℕ) :
    OracleCircuit QuantumLTF.Membership.gates12 (fun _ : Fin 1 => n+1) (n+1) :=
  [.query 0 false none (Function.Embedding.refl _) (by simp)]


