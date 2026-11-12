-- Prove2me | Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Records_EnoughBranchSum
-- name    : QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Records_EnoughBranchSum
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T19:57:54.305085+00:00
-- url     : https://prove2.me/theorems/443b6af9-d1bd-40fe-8390-7b57fc82792c
-- title:
--   Enough Branch Sum
-- statement:
--   Definitions and structural lemmas for Enough Branch Sum, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Records/EnoughBranchSum.lean

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Records_AcceptedProduct
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_SuccessEvent
set_option autoImplicit false
noncomputable section
namespace QEC
namespace Distillation
namespace HH18Parameterized
open Coding Semantics
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.FiniteInstrument
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
local instance instEnoughBranchSumClassicalDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p
attribute [local instance] QEC.Distillation.HH18Parameterized.instEnoughBranchSumClassicalDecidable
end HH18Parameterized
end Distillation
end QEC


