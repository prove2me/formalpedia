-- Prove2me | Definitions.Def_PricingWithTips3DM_114cb9bce6cb86acfefc9202Part1
-- name    : PricingWithTips3DM_114cb9bce6cb86acfefc9202Part1
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T23:33:24.472662+00:00
-- url     : https://prove2.me/theorems/e914a72e-9689-4778-b0b3-9128240f06df
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Machine.CompatibilityEdgesRestoreRow.Part1
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_4f60ac48a0a67c9dfda69c97
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

theorem replicate_tick_append_tick (count : Nat)
    (tail : List UnaryFrameSym) :
    List.replicate count .tick ++ .tick :: tail =
      List.replicate (count + 1) .tick ++ tail := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [List.replicate_succ, List.cons_append, ih]

theorem separator_replicate_tick_append_tick (count : Nat)
    (tail : List UnaryFrameSym) :
    (.separator :: List.replicate count .tick) ++ .tick :: tail =
      (.separator :: List.replicate (count + 1) .tick) ++ tail := by
  simp only [List.cons_append, replicate_tick_append_tick]

inductive CompatibilityRestoreField
  | variable | polarity | clause
  deriving DecidableEq

def compatibilityRestoreFieldLabel :
    CompatibilityRestoreField → CompatibilityEdgesLabel
  | .variable => .taggedRestoreVariable
  | .polarity => .taggedRestorePolarity
  | .clause => .taggedRestoreClause

def compatibilityRestoreFieldNext :
    CompatibilityRestoreField → CompatibilityEdgesLabel
  | .variable => .taggedRestorePolarity
  | .polarity => .taggedRestoreClause
  | .clause => .taggedRestoreVertex
end TMClique
end Turing
end Chapter34
end CLRS


