-- Prove2me | Definitions.Def_PricingWithTips3DM_c67ece6c69d5b0ef567eae8d
-- name    : PricingWithTips3DM_c67ece6c69d5b0ef567eae8d
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T00:02:19.394413+00:00
-- url     : https://prove2.me/theorems/e6041563-add2-4e58-bb9c-9afb2f2a9ee9
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionCfgStructuredValues
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_68c5fb77697279bbfde458e3
import Definitions.Def_PricingWithTips3DM_115d16e341305c7dc06321b7
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Structured flattening of transition configuration rows

This file factors the canonical flat row into its fixed status/state prefix
and one block per verifier stack.  It is intentionally independent of any
particular statement action or TM2 controller.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

/-- Halted, label, and state wires in canonical prefix order. -/
def transitionCfgPrefixWireValues
    (tm : _root_.Turing.FinTM2) (height : Nat)
    (source : CfgWires tm height) : List Nat :=
  (transitionEqPrefixSlots tm height).map source

/-- One canonical flat wire block for every stack in fixed-machine order. -/
def transitionCfgStackWireBlocks
    (tm : _root_.Turing.FinTM2) (height : Nat)
    (source : CfgWires tm height) : List (List Nat) :=
  (arithmeticRuntimeStackSourceIndices tm).map fun position =>
    transitionStackWireValues
      (source.stack ((arithmeticStackEquiv tm).symm position))

/-- Structured row flattening: fixed prefix followed by all stack blocks. -/
def transitionCfgStructuredWireValues
    (tm : _root_.Turing.FinTM2) (height : Nat)
    (source : CfgWires tm height) : List Nat :=
  transitionCfgPrefixWireValues tm height source ++
    (transitionCfgStackWireBlocks tm height source).flatten

/-- The structured factorization is literally the canonical coordinate-order
row used by every transition controller. -/
theorem transitionCfgStructuredWireValues_eq_canonical
    (tm : _root_.Turing.FinTM2) (height : Nat)
    (source : CfgWires tm height) :
    transitionCfgStructuredWireValues tm height source =
      transitionCfgWireValues tm height source := by
  have hstructured :
      transitionCfgStructuredWireValues tm height source =
        (transitionEqPublicSlots tm height).map source := by
    unfold transitionCfgStructuredWireValues
      transitionCfgPrefixWireValues transitionCfgStackWireBlocks
      transitionEqPublicSlots
    rw [List.map_append, List.map_flatten, List.map_map]
    congr 1
    apply congrArg List.flatten
    apply List.map_congr_left
    intro position hposition
    exact transitionStackWireValues_eq_slot_map tm height source
      ((arithmeticStackEquiv tm).symm position)
  rw [hstructured, transitionEqPublicSlots_eq_canonical]
  unfold transitionCfgWireValues
  rw [List.map_ofFn]
  rfl

end CLRS.Chapter34.Turing.CookLevin


