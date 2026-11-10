-- Prove2me | Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryCubicBridge
-- name    : QEC_Distillation_MultiplicativeQuditProtocol_BinaryCubicBridge
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-09T11:49:36.252597+00:00
-- url     : https://prove2.me/theorems/2031d592-bf33-46be-949b-a1d9878f4303
-- title:
--   Binary Cubic Bridge
-- statement:
--   Definitions and structural lemmas for Binary Cubic Bridge, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryCubicBridge.lean

import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryTaggedEncoding
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryPhysicalCCZ
import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_BinaryConversion
set_option autoImplicit false
noncomputable section
namespace QEC.Distillation.Ngu24Binary
open Coding Semantics Ngu24MultiplicativeCSS Ngu24MultiplicativeCCZ
open Coding.AlgebraicGeometry.F256GarciaStichtenoth
open scoped BigOperators
variable {J : Type} [Fintype J] [DecidableEq J]
def binaryLogicalCCZ : UnitaryTransport (TaggedThreeCopyRegister (ZMod 2) J)
    (TaggedThreeCopyRegister (ZMod 2) J) :=
  taggedCubicPhysicalTransport (LinearMap.id : (ZMod 2) →ₗ[ZMod 2] ZMod 2)
section SourceEncoding
variable {I Logical : Type} [Fintype I] [Fintype Logical]
local instance binaryCubicLogicalDecidableEq : DecidableEq Logical := Classical.decEq _
end SourceEncoding
end QEC.Distillation.Ngu24Binary


