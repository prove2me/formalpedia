-- Prove2me | Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_PhysicalTypes
-- name    : QEC_Distillation_LowOverheadProtocol_Core_PhysicalTypes
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T15:31:21.683659+00:00
-- url     : https://prove2.me/theorems/99149f40-28c7-4ecf-bb00-8c532550f774
-- title:
--   Physical Types
-- statement:
--   Definitions and structural lemmas for Physical Types, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/PhysicalTypes.lean

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_NoisyInput
set_option autoImplicit false
noncomputable section
namespace QEC
namespace Distillation
namespace HH18Protocol
open Coding Semantics
open Coding.PauliSymplectic
open Semantics.Qubit
universe u
attribute [local instance 100] Fintype.ofFinite
abbrev PhysicalSite := HH18PuncturedReedMuller.PhysicalSite 4 0
abbrev PhysicalRegister := QubitRegister PhysicalSite
abbrev LogicalRegister := QubitRegister (HH18PuncturedReedMuller.LogicalSite 4 0)
abbrev PhysicalErrorWord := HH18NoisyInput.PhysicalErrorWord 4 0
end HH18Protocol
end Distillation
end QEC


