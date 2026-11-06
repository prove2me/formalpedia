-- Prove2me | Definitions.Def_QEC_Semantics_Instruments_Selection_SelectedBranchOperator
-- name    : QEC_Semantics_Instruments_Selection_SelectedBranchOperator
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T11:53:17.689681+00:00
-- url     : https://prove2.me/theorems/2f106e6f-bdc9-466b-a7d7-b592862ccfb3
-- title:
--   Selected Branch Operator
-- statement:
--   Definitions and structural lemmas for Selected Branch Operator, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Selection/SelectedBranchOperator.lean

import Definitions.Def_QEC_Semantics_Instruments_TensorPower_BranchOperator
import Definitions.Def_QEC_Semantics_Instruments_Selection_SelectedSubsystemOperator
import Definitions.Def_QEC_Semantics_Instruments_Selection_SelectedTrialProduct
set_option autoImplicit false
universe u v
namespace QEC
namespace Semantics
open Classical
open scoped BigOperators
noncomputable section
namespace FiniteInstrument
end FiniteInstrument
end
end Semantics
end QEC


