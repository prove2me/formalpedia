-- Prove2me | Definitions.Def_QEC_Semantics_Instruments_NestedTensor_FilteredMarginalBranchOperator
-- name    : QEC_Semantics_Instruments_NestedTensor_FilteredMarginalBranchOperator
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T12:44:10.603989+00:00
-- url     : https://prove2.me/theorems/ab2b2f30-d2ac-49e8-b503-d61962710ca0
-- title:
--   Filtered Marginal Branch Operator
-- statement:
--   Definitions and structural lemmas for Filtered Marginal Branch Operator, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/NestedTensor/FilteredMarginalBranchOperator.lean

import Definitions.Def_QEC_Semantics_Instruments_NestedTensor_MarginalBranchOperator
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
variable {H K : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
end FiniteInstrument
end
end Semantics
end QEC


