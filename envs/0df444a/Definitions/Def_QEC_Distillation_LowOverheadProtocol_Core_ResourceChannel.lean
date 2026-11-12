-- Prove2me | Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_ResourceChannel
-- name    : QEC_Distillation_LowOverheadProtocol_Core_ResourceChannel
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T17:05:20.653906+00:00
-- url     : https://prove2.me/theorems/a110ff94-838e-4d2d-ac0c-bf6f1c60107a
-- title:
--   Resource Channel
-- statement:
--   Definitions and structural lemmas for Resource Channel, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/ResourceChannel.lean

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_ResourceDiagonal
set_option autoImplicit false
noncomputable section
namespace QEC
namespace Distillation
namespace HH18Protocol
open Coding Semantics
open Coding.PauliSymplectic
open Semantics.Qubit
open scoped BigOperators
universe u
local instance instChannelClassicalDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p
end HH18Protocol
end Distillation
end QEC


