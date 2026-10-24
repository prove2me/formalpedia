-- Prove2me | Definitions.Def_PricingWithTips3DM_2b2043d97c6219d5e9e3ac58
-- name    : PricingWithTips3DM_2b2043d97c6219d5e9e3ac58
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T00:09:34.538381+00:00
-- url     : https://prove2.me/theorems/b8b317c4-5347-4639-8d8a-c7e99e3f03b1
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxTrueArmTerminalPrefixAffine
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_20b8755a66e9405218e1fb7f
import Definitions.Def_PricingWithTips3DM_965b45da5c516cd6bc7eb8b7
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Fixed affine table for all terminal true-arm prefixes

The unified true-arm layout contains both branch-ending and terminal-ending
program labels.  This module filters that fixed layout table without changing
label order, retaining exactly the affine halted/label/state prefix of every
terminal entry.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Fixed forms contributed by one normalized true-arm entry.  Branch rows
have no terminal prefix; terminal rows contribute their complete fixed prefix
table. -/
noncomputable def
    TransitionDispatchTrueArmNormalizedLayout.terminalPrefixForms
    (tm : _root_.Turing.FinTM2) :
    TransitionDispatchTrueArmNormalizedLayout tm →
      List AffineUnaryTripleForm
  | .branch _ _ _ _ => []
  | .terminal labelOffset _ rowLayout _ =>
      transitionStmtTerminalPrefixForms tm labelOffset rowLayout

/-- Semantic prefix values selected by the same fixed terminal mask. -/
def TransitionDispatchTrueArmNormalizedLayout.terminalPrefixValues
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    TransitionDispatchTrueArmNormalizedLayout tm → List Nat
  | .branch _ _ _ _ => []
  | .terminal labelOffset _ rowLayout _ =>
      rowLayout.prefixValues tm
        (seed.start + labelOffset.eval seed.height)
        (workHeight tm seed.height) seed.start (seed.start + 1)
        (arithmeticWidenedCfgWires tm seed.height seed.start seed.rowBase)

/-- Each entry's fixed form table evaluates exactly to its selected semantic
prefix values. -/
theorem
    TransitionDispatchTrueArmNormalizedLayout.terminalPrefixForms_value
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (layout : TransitionDispatchTrueArmNormalizedLayout tm) :
    affineUnaryTripleMap (layout.terminalPrefixForms tm)
        (transitionTailAffineSeed seed) =
      layout.terminalPrefixValues tm seed := by
  cases layout with
  | branch labelOffset label branchOffset hbranch => rfl
  | terminal labelOffset label rowLayout hlayout =>
      exact transitionStmtTerminalPrefixForms_value tm seed labelOffset
        rowLayout

/-- Complete verifier-fixed affine form table for all terminal entries, in
original program-label order. -/
noncomputable def transitionDispatchTerminalPrefixForms
    (tm : _root_.Turing.FinTM2) : List AffineUnaryTripleForm :=
  (transitionDispatchTrueArmNormalizedLayouts tm).flatMap
    (TransitionDispatchTrueArmNormalizedLayout.terminalPrefixForms tm)

/-- Complete semantic terminal-prefix value stream for one transition row. -/
def transitionDispatchTerminalPrefixValues
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) : List Nat :=
  (transitionDispatchTrueArmNormalizedLayouts tm).flatMap
    (TransitionDispatchTrueArmNormalizedLayout.terminalPrefixValues tm seed)

/-- Evaluating the complete fixed table yields exactly all terminal prefixes
for one transition row. -/
theorem transitionDispatchTerminalPrefixForms_value
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    affineUnaryTripleMap (transitionDispatchTerminalPrefixForms tm)
        (transitionTailAffineSeed seed) =
      transitionDispatchTerminalPrefixValues tm seed := by
  unfold transitionDispatchTerminalPrefixForms
    transitionDispatchTerminalPrefixValues affineUnaryTripleMap
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro layout hlayout
  exact layout.terminalPrefixForms_value tm seed

end CLRS.Chapter34.Turing.CookLevin


