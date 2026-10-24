-- Prove2me | Definitions.Def_PricingWithTips3DM_c64b728cccfb325d8721b92b
-- name    : PricingWithTips3DM_c64b728cccfb325d8721b92b
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T20:27:55.13773+00:00
-- url     : https://prove2.me/theorems/2df839d3-653d-418b-853a-e092f4dfd25f
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameLengthPrefixedFourWaySplitSectionBlockSimulation
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_979f762546f4670ee92d6565
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# One payload block of the length-prefixed four-way splitter

All three variable-width payload channels share the same unary-block scanner.
This file proves that reusable scanner before reasoning about the three
different counters.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

private abbrev splitStep :=
  step unaryFrameLengthPrefixedFourWaySplitRevProgram

/-- Scanning one payload field copies its complete unary block and returns to
the counter check for the same channel. -/
def unaryFrameLengthPrefixedFourWaySplit_sectionBlock
    (channel : UnaryFrameLengthPrefixedFourWaySplitSection)
    (value coordinateFields trueFields falseFields : Nat)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (tail output : List UnaryFrameSym) :
    EvalsToInTime splitStep
      (unaryFrameLengthPrefixedFourWaySplitCfg (.sectionScan channel)
        buffer₁ buffer₂ test (encodeUnaryFrameBlock value ++ tail) output
        coordinateFields trueFields falseFields)
      (some (unaryFrameLengthPrefixedFourWaySplitCfg (.sectionCheck channel)
        (some .separator) buffer₂ test tail
        ((encodeUnaryFrameBlock value).reverse ++ output)
        coordinateFields trueFields falseFields))
      (2 * (value + 1)) := by
  induction value generalizing buffer₁ output with
  | zero =>
      exact ⟨⟨2, rfl⟩, le_rfl⟩
  | succ value ih =>
      let afterPop := unaryFrameLengthPrefixedFourWaySplitCfg
        (.sectionTick channel) (some UnaryFrameSym.tick) buffer₂ test
        (encodeUnaryFrameBlock value ++ tail) output
        coordinateFields trueFields falseFields
      let afterPush := unaryFrameLengthPrefixedFourWaySplitCfg
        (.sectionScan channel) (some UnaryFrameSym.tick) buffer₂ test
        (encodeUnaryFrameBlock value ++ tail) (.tick :: output)
        coordinateFields trueFields falseFields
      have hpop : EvalsToInTime splitStep
          (unaryFrameLengthPrefixedFourWaySplitCfg (.sectionScan channel)
            buffer₁ buffer₂ test
            (encodeUnaryFrameBlock (value + 1) ++ tail) output
            coordinateFields trueFields falseFields)
          (some afterPop) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
      have hpush : EvalsToInTime splitStep afterPop (some afterPush) 1 :=
        ⟨⟨1, rfl⟩, le_rfl⟩
      have hfirst := EvalsToInTime.trans splitStep 1 1 _ afterPop _ hpop hpush
      have hrest := ih (some UnaryFrameSym.tick) (.tick :: output)
      let full := EvalsToInTime.trans splitStep 2 (2 * (value + 1))
        _ afterPush _ hfirst hrest
      convert full using 1
      · simp [encodeUnaryFrameBlock,
          List.replicate_succ, List.reverse_append, List.append_assoc]
      · omega

end CLRS.Chapter34.Turing.PolyBuilder


