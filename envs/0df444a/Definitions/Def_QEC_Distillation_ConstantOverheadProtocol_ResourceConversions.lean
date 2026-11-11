-- Prove2me | Definitions.Def_QEC_Distillation_ConstantOverheadProtocol_ResourceConversions
-- name    : QEC_Distillation_ConstantOverheadProtocol_ResourceConversions
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T11:59:11.514196+00:00
-- url     : https://prove2.me/theorems/57ea0ea5-2c48-41ec-a9fd-7a853af3d1b8
-- title:
--   Resource Conversions
-- statement:
--   Definitions and structural lemmas for Resource Conversions, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/ConstantOverheadProtocol/ResourceConversions.lean

import Definitions.Def_QEC_Distillation_Universality_AdaptiveIdealClifford
set_option autoImplicit false
noncomputable section
namespace QEC.Distillation.Why24ConstantOverhead
inductive Why24MagicResourceToken
  | t
  | ccz
  deriving DecidableEq, Repr
structure Why24MagicInventory where
  tCount : Nat
  cczCount : Nat
  deriving DecidableEq, Repr
inductive Why24FiniteConversionPrimitive
  | fourTToCCZ
  | cczCatalyticT
  deriving DecidableEq, Repr
namespace Why24FiniteConversionPrimitive
def inputLedger : Why24FiniteConversionPrimitive ->
    AdaptiveIdealClifford.ResourceLedger Why24MagicResourceToken
  | .fourTToCCZ => Multiset.replicate 4 .t
  | .cczCatalyticT => {.ccz, .t}
def outputLedger : Why24FiniteConversionPrimitive ->
    AdaptiveIdealClifford.ResourceLedger Why24MagicResourceToken
  | .fourTToCCZ => {.ccz}
  | .cczCatalyticT => Multiset.replicate 3 .t
def apply : Why24FiniteConversionPrimitive -> Why24MagicInventory ->
    Option Why24MagicInventory
  | .fourTToCCZ, inventory =>
      if 4 <= inventory.tCount then
        some
          { tCount := inventory.tCount - 4
            cczCount := inventory.cczCount + 1 }
      else none
  | .cczCatalyticT, inventory =>
      if 1 <= inventory.tCount && 1 <= inventory.cczCount then
        some
          { tCount := inventory.tCount + 2
            cczCount := inventory.cczCount - 1 }
      else none
end Why24FiniteConversionPrimitive
def why24RunConversionProgram : List Why24FiniteConversionPrimitive ->
    Why24MagicInventory -> Option Why24MagicInventory
  | [], inventory => some inventory
  | primitive :: program, inventory =>
      (primitive.apply inventory).bind (why24RunConversionProgram program)
def why24FourTToCCZBatch (batch : Nat) :
    List Why24FiniteConversionPrimitive :=
  List.replicate batch .fourTToCCZ
def why24CCZCatalyticTBatch (batch : Nat) :
    List Why24FiniteConversionPrimitive :=
  List.replicate batch .cczCatalyticT
end QEC.Distillation.Why24ConstantOverhead


