-- Prove2me | Definitions.Def_PricingWithTips3DM_f6bf858856e0a0132109161ePart1
-- name    : PricingWithTips3DM_f6bf858856e0a0132109161ePart1
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T09:21:04.144073+00:00
-- url     : https://prove2.me/theorems/4af3f46f-60b0-42a2-8c5c-c2bfd591950b
-- title:
--   PricingWithTips 3DM dependency: Scratch_PricingWithTips_FixedShapeGuardedKeysTM2.Part1
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://arxiv.org/abs/2507.10872

import Definitions.Def_PricingWithTips3DM_907e19bdbe7b9bc0babe86ad
import Definitions.Def_PricingWithTips3DM_2798896aededebbb99960a8c
import Definitions.Def_PricingWithTips3DM_8169be64da1591889851249c
import Definitions.Def_PricingWithTips3DM_66c095df44f03ac8a1bcce5e

/-! Native validity gate for the fixed-shape base literal-key table. -/

noncomputable section

namespace PricingWithTips.FixedShapeGuardedKeysTM2

open CLRS.Chapter34
open CLRS.Chapter34.Turing
open CLRS.Chapter34.Turing.PolyBuilder
open CLRS.Chapter34.Turing.TMClique
open PricingWithTips.FixedShapeOccurrenceKeysTM2
open PricingWithTips.FixedShapeLiteralKeySemantics
open _root_.Turing

def flagSymbol : Bool → CliqueSym
  | true => .instanceMark
  | false => .certificateMark

def canonicalFlagStream (input : List CNFSym) : List CliqueSym :=
  (canonicalThreeCNFFlag input).map flagSymbol

noncomputable def canonicalFlagStream_computableInPolyTime :
    TM2ComputableInPolyTime id id canonicalFlagStream := by
  let mapper := listMap_computableInPolyTime flagSymbol
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    canonicalThreeCNFFlag_computableInPolyTime mapper
  change TM2ComputableInPolyTime id id
    (fun input => (canonicalThreeCNFFlag input).map flagSymbol)
  simpa [Function.comp_def] using Classical.choice composed

def flaggedKeyInput (input : List CNFSym) : List CliqueSym :=
  canonicalFlagStream input ++ canonicalOccurrenceKeyStream input

def encodePair : CliqueSym → UnaryFrameSym × UnaryFrameSym
  | .instanceMark => (.tick, .tick)
  | .certificateMark => (.tick, .separator)
  | .tick => (.tick, .frameEnd)
  | .fieldSep => (.separator, .tick)
  | .edgeMark => (.separator, .separator)
  | .vertexMark => (.separator, .frameEnd)
  | .pairSep => (.frameEnd, .tick)
  | .recordEnd => (.frameEnd, .separator)

def decodePair : UnaryFrameSym → UnaryFrameSym → CliqueSym
  | .tick, .tick => .instanceMark
  | .tick, .separator => .certificateMark
  | .tick, .frameEnd => .tick
  | .separator, .tick => .fieldSep
  | .separator, .separator => .edgeMark
  | .separator, .frameEnd => .vertexMark
  | .frameEnd, .tick => .pairSep
  | .frameEnd, .separator => .recordEnd
  | .frameEnd, .frameEnd => .recordEnd

@[simp] theorem decode_encodePair (symbol : CliqueSym) :
    decodePair (encodePair symbol).1 (encodePair symbol).2 = symbol := by
  cases symbol <;> rfl

noncomputable def flaggedKeyInput_computableInPolyTime :
    TM2ComputableInPolyTime id id flaggedKeyInput := by
  exact fixedPairSameInputConcat_computableInPolyTime
    encodePair decodePair decode_encodePair
    canonicalFlagStream_computableInPolyTime
    canonicalOccurrenceKeyStream_computableInPolyTime
end PricingWithTips.FixedShapeGuardedKeysTM2


