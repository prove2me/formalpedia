-- Prove2me | Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Paths_NestedPathRouting
-- name    : QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Paths_NestedPathRouting
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T19:35:40.443193+00:00
-- url     : https://prove2.me/theorems/12010551-6be1-472b-be9b-8ff951cdc00e
-- title:
--   Nested Path Routing
-- statement:
--   Definitions and structural lemmas for Nested Path Routing, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Paths/NestedPathRouting.lean

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_Regrouping
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PathEnvelope
import Definitions.Def_QEC_Semantics_Instruments_NestedTensor_Power
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm

set_option autoImplicit false
noncomputable section
namespace QEC
namespace Distillation
namespace HH18Parameterized
open Coding Semantics
open Semantics.FiniteInstrument
attribute [local instance 100] Fintype.ofFinite
noncomputable def decodedRetryPoolNestedPathEquiv (m w depth : Nat) :
    nestedTensorPath (logicalOutputCount m w) depth ≃
      routedDepthOutputSlots m w depth :=
  (nestedTensorPathEquiv (logicalOutputCount m w) depth).trans
    { toFun := fun path index =>
        (decodedRetryPoolLogicalSiteFinEquiv m w).symm (path index)
      invFun := fun path index =>
        decodedRetryPoolLogicalSiteFinEquiv m w (path index)
      left_inv := by
        intro path
        funext index
        exact (decodedRetryPoolLogicalSiteFinEquiv m w).apply_symm_apply (path index)
      right_inv := by
        intro path
        funext index
        exact (decodedRetryPoolLogicalSiteFinEquiv m w).symm_apply_apply (path index) }
end HH18Parameterized
end Distillation
end QEC


