-- Prove2me | Definitions.Def_QEC_Results_QuantumMemory_TwoDimensionalEnergyBarrier
-- name    : QEC_Results_QuantumMemory_TwoDimensionalEnergyBarrier
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T13:09:22.054148+00:00
-- url     : https://prove2.me/theorems/ead0af7e-8c2f-47ad-995f-27a735da068e
-- title:
--   Two Dimensional Energy Barrier
-- statement:
--   Definitions and structural lemmas for Two Dimensional Energy Barrier, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Results/QuantumMemory/TwoDimensionalEnergyBarrier.lean

import Definitions.Def_QEC_Coding_Stabilizer_TwoDimensional_StripLogicalPath
set_option autoImplicit false
noncomputable section
namespace QEC
namespace Coding
namespace StabilizerCode
namespace LocalStabilizerHamiltonian
open PauliSymplectic
open scoped Classical
universe u
variable {κ : Type u} [Fintype κ]
end LocalStabilizerHamiltonian
end StabilizerCode
end Coding
end QEC


