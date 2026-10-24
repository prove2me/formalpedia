-- Prove2me | Definitions.Def_PricingWithTips3DM_1aa7e7d15a9a122dff2540ccPart1Basic
-- name    : PricingWithTips3DM_1aa7e7d15a9a122dff2540ccPart1Basic
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T01:20:41.988307+00:00
-- url     : https://prove2.me/theorems/81c42148-8465-4dc2-97d9-83d75d36988b
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Machine.CompatibilityEdgesEmitEdge.Part1.Basic
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_e34d3207674f3658401966de
import Mathlib.Tactic
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open StateTransition

namespace CLRS
namespace Chapter34
namespace Turing
namespace TMClique

open PolyBuilder

theorem replicate_clique_tick_append_tick (count : Nat)
    (tail : List CliqueSym) :
    List.replicate count .tick ++ .tick :: tail =
      List.replicate (count + 1) .tick ++ tail := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [List.replicate_succ, List.cons_append, ih]

theorem prependCliqueTicks_eq (count : Nat)
    (tail : List CliqueSym) :
    prependCliqueTicks count tail = List.replicate count .tick ++ tail := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp [prependCliqueTicks, List.replicate_succ, ih]

inductive CompatibilityEdgeCounter
  | upper | lower
  deriving DecidableEq

def compatibilityEdgeCopyLabel :
    CompatibilityEdgeCounter → CompatibilityEdgesLabel
  | .upper => .copyUpper
  | .lower => .copyLower

def compatibilityEdgeSaveLabel :
    CompatibilityEdgeCounter → CompatibilityEdgesLabel
  | .upper => .saveUpper
  | .lower => .saveLower

def compatibilityEdgePushTickLabel :
    CompatibilityEdgeCounter → CompatibilityEdgesLabel
  | .upper => .pushUpperTick
  | .lower => .pushLowerTick

def compatibilityEdgeRestoreLabel :
    CompatibilityEdgeCounter → CompatibilityEdgesLabel
  | .upper => .restoreUpper
  | .lower => .restoreLower

def compatibilityEdgeRestoreIncLabel :
    CompatibilityEdgeCounter → CompatibilityEdgesLabel
  | .upper => .restoreUpperInc
  | .lower => .restoreLowerInc

def compatibilityEdgeAfterRestoreLabel :
    CompatibilityEdgeCounter → CompatibilityEdgesLabel
  | .upper => .pushPairSeparator
  | .lower => .pushEdgeMark

def compatibilityEdgeCounterCfg
    (counter : CompatibilityEdgeCounter) (label : CompatibilityEdgesLabel)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (input : List UnaryFrameSym) (output : List CliqueSym)
    (work₁ work₂ : List UnaryFrameSym)
    (primary other saved : Nat) : BuilderCfg compatibilityEdgesProgram :=
  match counter with
  | .upper => compatibilityEdgesCfg label buffer₁ buffer₂ test input output
      work₁ work₂ primary other saved
  | .lower => compatibilityEdgesCfg label buffer₁ buffer₂ test input output
      work₁ work₂ other primary saved
end TMClique
end Turing
end Chapter34
end CLRS


