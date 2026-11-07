-- Prove2me | Definitions.Def_QEC_Results_QuantumMemory_FourDimensionalEnergyBarrier
-- name    : QEC_Results_QuantumMemory_FourDimensionalEnergyBarrier
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T04:25:37.013194+00:00
-- url     : https://prove2.me/theorems/8be93c3d-23f8-49ed-a5b3-be7fa6802d48
-- title:
--   Four Dimensional Energy Barrier
-- statement:
--   Definitions and structural lemmas for Four Dimensional Energy Barrier, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Results/QuantumMemory/FourDimensionalEnergyBarrier.lean

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_CoordinateSymmetry
set_option autoImplicit false
noncomputable section
namespace QEC.Coding.PeriodicCubical4
open scoped Classical
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
variable {L : Nat} [NeZero L] [Fact (1 < L)]
end QEC.Coding.PeriodicCubical4


