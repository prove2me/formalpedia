-- Prove2me | Definitions.Def_QEC_Results_QLDPC_LiftedProductAlmostLinear
-- name    : QEC_Results_QLDPC_LiftedProductAlmostLinear
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T11:18:45.939988+00:00
-- url     : https://prove2.me/theorems/0d98e94f-0d0e-4fd5-b229-4388a849e26a
-- title:
--   Lifted Product Almost Linear
-- statement:
--   Definitions and structural lemmas for Lifted Product Almost Linear, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Results/QLDPC/LiftedProductAlmostLinear.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_Tradeoff
set_option autoImplicit false
namespace QEC.Coding.ExpanderCodes.PK20
def LiftedProductAlmostLinearDistance : Prop :=
  FirstAlmostLinearFamily ∧ TwoProductConstructionFamily
end QEC.Coding.ExpanderCodes.PK20


