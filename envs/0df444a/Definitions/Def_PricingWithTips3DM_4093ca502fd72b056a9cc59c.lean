-- Prove2me | Definitions.Def_PricingWithTips3DM_4093ca502fd72b056a9cc59c
-- name    : PricingWithTips3DM_4093ca502fd72b056a9cc59c
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T00:03:27.452832+00:00
-- url     : https://prove2.me/theorems/5eec0a18-6789-4a98-8ec2-27ae8cf2bab8
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementTerminalValues
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_4bc768e3be9f86ad3801aa72
import Definitions.Def_PricingWithTips3DM_c67ece6c69d5b0ef567eae8d
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Structured flat values of terminal transition statements

Terminal statement rows now have two independent descriptions: their typed
status/state/stack-action layout and the canonical flat row consumed by the
transition controller.  This file proves the exact assembly equation between
those descriptions.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

/-- Closed halted/label/state prefix of a terminal row layout. -/
def TransitionStmtTerminalRowLayout.prefixValues
    (tm : _root_.Turing.FinTM2) (start height falseWire trueWire : Nat)
    (source : CfgWires tm height)
    (layout : TransitionStmtTerminalRowLayout tm) : List Nat :=
  layout.terminal.terminal.haltedWire tm falseWire trueWire ::
    List.ofFn (layout.terminal.terminal.labelWires tm falseWire trueWire
      (start + layout.terminal.offset.eval height)) ++
    List.ofFn (layout.state.wires tm start height source)

/-- Stack-action outputs, kept in the fixed machine-stack block order. -/
def TransitionStmtTerminalRowLayout.stackBlocks
    (tm : _root_.Turing.FinTM2) (start height falseWire trueWire : Nat)
    (source : CfgWires tm height)
    (layout : TransitionStmtTerminalRowLayout tm) : List (List Nat) :=
  let stackCfg := transitionStmtStackActions_eval tm start height falseWire
    trueWire source layout.stackActions
  (arithmeticRuntimeStackSourceIndices tm).map fun position =>
    transitionStackWireValues
      (stackCfg.stack ((arithmeticStackEquiv tm).symm position))

/-- Complete structured flat value row of one terminal layout. -/
def TransitionStmtTerminalRowLayout.structuredValues
    (tm : _root_.Turing.FinTM2) (start height falseWire trueWire : Nat)
    (source : CfgWires tm height)
    (layout : TransitionStmtTerminalRowLayout tm) : List Nat :=
  layout.prefixValues tm start height falseWire trueWire source ++
    (layout.stackBlocks tm start height falseWire trueWire source).flatten

/-- Flattening the actual terminal row's fixed prefix yields the closed
status/state prefix above. -/
theorem TransitionStmtTerminalRowLayout.prefixValues_eq
    (tm : _root_.Turing.FinTM2) (start height falseWire trueWire : Nat)
    (source : CfgWires tm height)
    (layout : TransitionStmtTerminalRowLayout tm) :
    transitionCfgPrefixWireValues tm height
        (layout.wires tm start height falseWire trueWire source) =
      layout.prefixValues tm start height falseWire trueWire source := by
  unfold transitionCfgPrefixWireValues transitionEqPrefixSlots
    TransitionStmtTerminalRowLayout.prefixValues
  rw [List.map_append, List.map_cons, List.map_ofFn, List.map_ofFn]
  change
    (layout.wires tm start height falseWire trueWire source).halted ::
        List.ofFn (layout.wires tm start height falseWire trueWire source).label ++
        List.ofFn (layout.wires tm start height falseWire trueWire source).state =
      layout.terminal.terminal.haltedWire tm falseWire trueWire ::
        List.ofFn (layout.terminal.terminal.labelWires tm falseWire trueWire
          (start + layout.terminal.offset.eval height)) ++
        List.ofFn (layout.state.wires tm start height source)
  simp only [TransitionStmtTerminalRowLayout.wires,
    CfgBundle.replaceStatus_halted]
  congr 1

/-- Status and state replacement preserve every stack block, leaving exactly
the sequential stack-action result. -/
theorem TransitionStmtTerminalRowLayout.stackBlocks_eq
    (tm : _root_.Turing.FinTM2) (start height falseWire trueWire : Nat)
    (source : CfgWires tm height)
    (layout : TransitionStmtTerminalRowLayout tm) :
    transitionCfgStackWireBlocks tm height
        (layout.wires tm start height falseWire trueWire source) =
      layout.stackBlocks tm start height falseWire trueWire source := by
  unfold transitionCfgStackWireBlocks
    TransitionStmtTerminalRowLayout.stackBlocks
    TransitionStmtTerminalRowLayout.wires
  apply List.map_congr_left
  intro position hposition
  congr 1

/-- The structured terminal layout is exactly the canonical controller row,
with no hidden coordinate permutation. -/
theorem TransitionStmtTerminalRowLayout.structuredValues_eq_canonical
    (tm : _root_.Turing.FinTM2) (start height falseWire trueWire : Nat)
    (source : CfgWires tm height)
    (layout : TransitionStmtTerminalRowLayout tm) :
    layout.structuredValues tm start height falseWire trueWire source =
      transitionCfgWireValues tm height
        (layout.wires tm start height falseWire trueWire source) := by
  rw [← transitionCfgStructuredWireValues_eq_canonical]
  unfold TransitionStmtTerminalRowLayout.structuredValues
    transitionCfgStructuredWireValues
  rw [layout.prefixValues_eq, layout.stackBlocks_eq]

end CLRS.Chapter34.Turing.CookLevin


