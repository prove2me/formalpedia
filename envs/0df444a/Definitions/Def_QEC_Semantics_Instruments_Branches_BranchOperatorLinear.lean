-- Prove2me | Definitions.Def_QEC_Semantics_Instruments_Branches_BranchOperatorLinear
-- name    : QEC_Semantics_Instruments_Branches_BranchOperatorLinear
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T10:23:47.703636+00:00
-- url     : https://prove2.me/theorems/1a6253db-0367-4f1c-b093-65dbb129974a
-- title:
--   Branch Operator Linear
-- statement:
--   Definitions and structural lemmas for Branch Operator Linear, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Branches/BranchOperatorLinear.lean

import Definitions.Def_QEC_Semantics_Instruments_Core
set_option autoImplicit false
universe u v w x
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


