-- Prove2me | Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_DecodedErrorSupport
-- name    : QEC_Distillation_LowOverheadProtocol_Parameterized_DecodedErrorSupport
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T12:38:25.619334+00:00
-- url     : https://prove2.me/theorems/272e53b9-1578-4a4a-97fd-4e34f03bb0c0
-- title:
--   Decoded Error Support
-- statement:
--   Definitions and structural lemmas for Decoded Error Support, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/DecodedErrorSupport.lean

import Definitions.Def_QEC_Distillation_Core_FiniteDecodedTrace
set_option autoImplicit false
noncomputable section
namespace QEC
namespace Distillation
namespace HH18Parameterized
open Semantics
open scoped BigOperators
universe u v w
end HH18Parameterized
end Distillation
end QEC


