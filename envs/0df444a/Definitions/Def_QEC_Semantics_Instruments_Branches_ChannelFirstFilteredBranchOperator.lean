-- Prove2me | Definitions.Def_QEC_Semantics_Instruments_Branches_ChannelFirstFilteredBranchOperator
-- name    : QEC_Semantics_Instruments_Branches_ChannelFirstFilteredBranchOperator
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T11:53:09.285025+00:00
-- url     : https://prove2.me/theorems/f743e8b6-b431-4b9f-b3fb-ab9727d14c8c
-- title:
--   Channel First Filtered Branch Operator
-- statement:
--   Definitions and structural lemmas for Channel First Filtered Branch Operator, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Branches/ChannelFirstFilteredBranchOperator.lean

import Definitions.Def_QEC_Semantics_Instruments_TensorPower_BranchOperator
set_option autoImplicit false
universe u v w
namespace QEC
namespace Semantics
open Classical
open scoped BigOperators
noncomputable section
namespace FiniteInstrument
variable {kappa : Type v} [Fintype kappa]
variable {Omega : Type w} [Fintype Omega]
variable {H K L : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
variable [NormedAddCommGroup L] [InnerProductSpace Complex L] [FiniteQuantumSystem L]
end FiniteInstrument
end
end Semantics
end QEC


