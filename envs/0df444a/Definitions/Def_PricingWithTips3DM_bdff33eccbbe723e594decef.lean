-- Prove2me | Definitions.Def_PricingWithTips3DM_bdff33eccbbe723e594decef
-- name    : PricingWithTips3DM_bdff33eccbbe723e594decef
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T00:29:59.424393+00:00
-- url     : https://prove2.me/theorems/a2e3c819-78e5-468b-9160-9ea776b10bf0
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementStackRouteAffineSpanTerminal
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_5d6b309648e852b00d2baa62
import Definitions.Def_PricingWithTips3DM_68256059a3447c2893af340b
import Definitions.Def_PricingWithTips3DM_9409f68c5b12b634945ab4cc
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Compact affine spans for real terminal statement rows

The generic affine-span fold needs a static capacity inequality.  Verifier
rows satisfy it automatically: terminal layouts contain at most the uniform
machine action bound, while `verifierHeight` reserves two coordinates per
such action plus a sentinel.  This module discharges that last semantic side
condition for the actual Cook--Levin transition rows.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

/-- Static compact route selected for one stack of a terminal statement. -/
def TransitionStmtTerminalRowLayout.stackAffineSpanRoute
    (tm : _root_.Turing.FinTM2) (k : tm.K)
    (labelOffset : TransitionAffineNat)
    (layout : TransitionStmtTerminalRowLayout tm) :
    TransitionStackAffineRouteSpanBlock :=
  transitionStmtSelectedStackAffineActionSpans tm k labelOffset
    TransitionStackAffineRouteSpanBlock.identity
    (transitionStmtStackActionsFor tm k layout.stackActions)

/-- On every verifier-produced transition seed, the compact affine span for a
real terminal row evaluates exactly to the established sequential stack route.
-/
theorem TransitionStmtTerminalRowLayout.stackAffineSpanRoute_eval
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) (seed : TransitionRowSeed)
    (hseed : seed ∈ verifierTransitionRowSeeds W input)
    (label : W.machine.tm.Λ) (labelOffset : TransitionAffineNat)
    (layout : TransitionStmtTerminalRowLayout W.machine.tm)
    (hlayout : transitionStmtTerminalRowLayout W.machine.tm
      (W.machine.tm.m label) (stmtPushSet_program_subset W.machine.tm label) =
        some layout)
    (k : W.machine.tm.K) :
    (layout.stackAffineSpanRoute W.machine.tm k labelOffset).eval seed
        (transitionStackRouteSourceBlock W.machine.tm seed k) =
      transitionStackRouteActionValues W.machine.tm k
        (seed.start + labelOffset.eval seed.height) seed
        (transitionStmtStackActionsFor W.machine.tm k
          layout.stackActions) := by
  let actions := transitionStmtStackActionsFor W.machine.tm k
    layout.stackActions
  have hcount : actions.length ≤
      maxStackActionsPerStep W.machine.tm := by
    exact layout.selectedActionCount_le_maxStackActionsPerStep
      W.machine.tm label (stmtPushSet_program_subset W.machine.tm label)
      hlayout k
  have hheight := verifierTransitionRowSeeds_height_eq W input seed hseed
  have hpadding := verifierHeight_actionPadding_le W input.length
  have hcapacity :
      2 * actions.length + 1 ≤ workHeight W.machine.tm seed.height := by
    rw [hheight]
    unfold workHeight
    omega
  have hshape :
      (transitionStackRouteSourceBlock W.machine.tm seed k).HasShape
        W.machine.tm k (workHeight W.machine.tm seed.height) := by
    rw [transitionStackRouteSourceBlock_eq]
    exact TransitionStackValueBlock.hasShape_ofWires W.machine.tm k
      (workHeight W.machine.tm seed.height)
      ((arithmeticWidenedCfgWires W.machine.tm seed.height seed.start
        seed.rowBase).stack k)
  unfold TransitionStmtTerminalRowLayout.stackAffineSpanRoute
    transitionStackRouteActionValues
  exact transitionStmtSelectedStackAffineActionSpans_values W.machine.tm seed k
    labelOffset (transitionStackRouteSourceBlock W.machine.tm seed k) actions
    hshape hcapacity

end CLRS.Chapter34.Turing.CookLevin


