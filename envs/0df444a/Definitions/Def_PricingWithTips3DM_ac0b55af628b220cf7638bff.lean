-- Prove2me | Definitions.Def_PricingWithTips3DM_ac0b55af628b220cf7638bff
-- name    : PricingWithTips3DM_ac0b55af628b220cf7638bff
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T20:21:26.425388+00:00
-- url     : https://prove2.me/theorems/63a28a70-2cea-4c74-867b-22d795573fca
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameLengthPrefixedFourWaySplitSimulation
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_5e69ea7ca26d3fead719bc26
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Exact simulation of the length-prefixed four-way splitter

The proof is factored by runtime phase: width loading, selector copying, and
the three counter-delimited payload sections.  This keeps the fixed-machine
argument independent of Cook--Levin-specific mux views.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

private abbrev splitStep :=
  step unaryFrameLengthPrefixedFourWaySplitRevProgram

/-- Loading one unary width creates `3 * width` coordinate-field tokens and
one token per arm field. -/
def unaryFrameLengthPrefixedFourWaySplit_loadWidth
    (width coordinateFields trueFields falseFields : Nat)
    (buffer₁ buffer₂ : Option UnaryFrameSym)
    (tail output : List UnaryFrameSym) :
    EvalsToInTime splitStep
      (unaryFrameLengthPrefixedFourWaySplitCfg .loadWidth buffer₁ buffer₂
        false (List.replicate width .tick ++ .separator :: tail) output
        coordinateFields trueFields falseFields)
      (some (unaryFrameLengthPrefixedFourWaySplitCfg .selectorScan
        (some .separator) buffer₂ false tail output
        (coordinateFields + 3 * width) (trueFields + width)
        (falseFields + width)))
      (6 * width + 1) := by
  induction width generalizing buffer₁ coordinateFields trueFields
      falseFields with
  | zero =>
      refine ⟨⟨1, ?_⟩, le_rfl⟩
      rfl
  | succ width ih =>
      let rest := List.replicate width UnaryFrameSym.tick ++
        UnaryFrameSym.separator :: tail
      let afterPop := unaryFrameLengthPrefixedFourWaySplitCfg .incCoordinate₁
        (some UnaryFrameSym.tick) buffer₂ false rest output
        coordinateFields trueFields falseFields
      let afterCoordinate₁ :=
        unaryFrameLengthPrefixedFourWaySplitCfg .incCoordinate₂
          (some UnaryFrameSym.tick) buffer₂ false rest output
          (coordinateFields + 1) trueFields falseFields
      let afterCoordinate₂ :=
        unaryFrameLengthPrefixedFourWaySplitCfg .incCoordinate₃
          (some UnaryFrameSym.tick) buffer₂ false rest output
          (coordinateFields + 2) trueFields falseFields
      let afterCoordinate₃ :=
        unaryFrameLengthPrefixedFourWaySplitCfg .incTrue
          (some UnaryFrameSym.tick) buffer₂ false rest output
          (coordinateFields + 3) trueFields falseFields
      let afterTrue := unaryFrameLengthPrefixedFourWaySplitCfg .incFalse
        (some UnaryFrameSym.tick) buffer₂ false rest output
        (coordinateFields + 3) (trueFields + 1) falseFields
      let middle := unaryFrameLengthPrefixedFourWaySplitCfg .loadWidth
        (some UnaryFrameSym.tick) buffer₂ false
        rest output
        (coordinateFields + 3) (trueFields + 1) (falseFields + 1)
      have hfirst : EvalsToInTime splitStep
          (unaryFrameLengthPrefixedFourWaySplitCfg .loadWidth buffer₁
            buffer₂ false
            (List.replicate (width + 1) .tick ++ .separator :: tail) output
            coordinateFields trueFields falseFields)
          (some middle) 6 := by
        have hpop : EvalsToInTime splitStep
            (unaryFrameLengthPrefixedFourWaySplitCfg .loadWidth buffer₁
              buffer₂ false
              (List.replicate (width + 1) .tick ++ .separator :: tail)
              output coordinateFields trueFields falseFields)
            (some afterPop) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
        have hcoordinate₁ : EvalsToInTime splitStep afterPop
            (some afterCoordinate₁) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
        have hcoordinate₂ : EvalsToInTime splitStep afterCoordinate₁
            (some afterCoordinate₂) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
        have hcoordinate₃ : EvalsToInTime splitStep afterCoordinate₂
            (some afterCoordinate₃) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
        have htrue : EvalsToInTime splitStep afterCoordinate₃
            (some afterTrue) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
        have hfalse : EvalsToInTime splitStep afterTrue
            (some middle) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
        let h₁ := EvalsToInTime.trans splitStep 1 1 _ afterPop _
          hpop hcoordinate₁
        let h₂ := EvalsToInTime.trans splitStep 2 1 _ afterCoordinate₁ _
          h₁ hcoordinate₂
        let h₃ := EvalsToInTime.trans splitStep 3 1 _ afterCoordinate₂ _
          h₂ hcoordinate₃
        let h₄ := EvalsToInTime.trans splitStep 4 1 _ afterCoordinate₃ _
          h₃ htrue
        exact EvalsToInTime.trans splitStep 5 1 _ afterTrue _ h₄ hfalse
      have hrest := ih (coordinateFields + 3) (trueFields + 1)
        (falseFields + 1) (some .tick)
      let full := EvalsToInTime.trans splitStep 6 (6 * width + 1)
        _ middle _ hfirst hrest
      have htarget :
          coordinateFields + 3 + 3 * width =
            coordinateFields + 3 * (width + 1) ∧
          trueFields + 1 + width = trueFields + (width + 1) ∧
          falseFields + 1 + width = falseFields + (width + 1) := by
        omega
      rcases htarget with ⟨hcoordinate, htrue, hfalse⟩
      simpa [middle, hcoordinate, htrue, hfalse, Nat.mul_add,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full

end CLRS.Chapter34.Turing.PolyBuilder


