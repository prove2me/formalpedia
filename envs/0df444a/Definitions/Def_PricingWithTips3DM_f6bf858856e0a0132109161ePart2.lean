-- Prove2me | Definitions.Def_PricingWithTips3DM_f6bf858856e0a0132109161ePart2
-- name    : PricingWithTips3DM_f6bf858856e0a0132109161ePart2
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T09:25:41.220012+00:00
-- url     : https://prove2.me/theorems/235c6f72-a9d0-490e-a598-fd439d1a2324
-- title:
--   PricingWithTips 3DM dependency: Scratch_PricingWithTips_FixedShapeGuardedKeysTM2.Part2
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://arxiv.org/abs/2507.10872

import Definitions.Def_PricingWithTips3DM_f6bf858856e0a0132109161ePart1

noncomputable section

namespace PricingWithTips.FixedShapeGuardedKeysTM2

open CLRS.Chapter34
open CLRS.Chapter34.Turing
open CLRS.Chapter34.Turing.PolyBuilder
open CLRS.Chapter34.Turing.TMClique
open PricingWithTips.FixedShapeOccurrenceKeysTM2
open PricingWithTips.FixedShapeLiteralKeySemantics
open _root_.Turing

abbrev KeyGateMode := Bool × Bool

private def startMode : KeyGateMode := (false, false)
private def copyMode : KeyGateMode := (true, false)
private def discardMode : KeyGateMode := (false, true)

def gateSpec : StatefulFlatMapSpec KeyGateMode CliqueSym CliqueSym where
  initial := startMode
  action mode symbol :=
    if mode = startMode then
      if symbol = .instanceMark then ([], copyMode) else ([], discardMode)
    else if mode = copyMode then ([symbol], copyMode)
    else ([], discardMode)
  finish _ := []

def gate (input : List CliqueSym) : List CliqueSym :=
  rewriteStatefulFlatMap gateSpec input

noncomputable def gate_computableInPolyTime :
    TM2ComputableInPolyTime id id gate :=
  statefulFlatMap_computableInPolyTime gateSpec

private theorem gate_copy (input : List CliqueSym) :
    rewriteStatefulFlatMapFrom gateSpec copyMode input = input := by
  induction input with
  | nil => rfl
  | cons symbol input ih =>
      rw [rewriteStatefulFlatMapFrom.eq_def]
      change symbol :: rewriteStatefulFlatMapFrom gateSpec copyMode input = _
      rw [ih]

private theorem gate_drop (input : List CliqueSym) :
    rewriteStatefulFlatMapFrom gateSpec discardMode input = [] := by
  induction input with
  | nil => rfl
  | cons symbol input ih =>
      rw [rewriteStatefulFlatMapFrom.eq_def]
      change rewriteStatefulFlatMapFrom gateSpec discardMode input = []
      exact ih

theorem gate_flag (valid : Bool) (input : List CliqueSym) :
    gate (flagSymbol valid :: input) = if valid then input else [] := by
  cases valid with
  | false =>
      change rewriteStatefulFlatMapFrom gateSpec discardMode input = []
      exact gate_drop input
  | true =>
      change rewriteStatefulFlatMapFrom gateSpec copyMode input = input
      exact gate_copy input
end PricingWithTips.FixedShapeGuardedKeysTM2


