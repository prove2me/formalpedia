-- Prove2me | Definitions.Def_PricingWithTips3DM_7019935caab4d9733d34fc99
-- name    : PricingWithTips3DM_7019935caab4d9733d34fc99
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T20:27:01.205598+00:00
-- url     : https://prove2.me/theorems/8a6cf5e1-aa9a-404d-83aa-5d9b6919d87d
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineUnaryTripleProgressionRowMark
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_1a1974f54f1a1e0128c37c0a
import Definitions.Def_PricingWithTips3DM_3799fd79c9b0b4d68c438353
import Definitions.Def_PricingWithTips3DM_a109ba81e03654d2e3b00464
import Definitions.Def_PricingWithTips3DM_f6afa4e253c60b6b5fa62b42
import Definitions.Def_PricingWithTips3DM_4901b5edb9039a7b71dab674
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Row markers for affine progression descriptors

An affine unary-triple progression has exactly seven unary fields.  Raw affine
sources emit adjacent descriptors with ordinary separators only.  This module
supplies the fixed streaming bridge which preserves those seven separators and
adds one outer `frameEnd` after every complete descriptor.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- The seventh ordinary separator is temporarily replaced by `frameEnd`. -/
def affineUnaryTripleProgressionRowDelimiterTable : List UnaryFrameSym :=
  [.separator, .separator, .separator, .separator, .separator, .separator,
    .frameEnd]

@[simp] theorem affineUnaryTripleProgressionRowDelimiterTable_length :
    affineUnaryTripleProgressionRowDelimiterTable.length = 7 := by rfl

theorem affineUnaryTripleProgressionRowDelimiterTable_nonempty :
    0 < affineUnaryTripleProgressionRowDelimiterTable.length := by simp

/-- Restore the seventh ordinary separator and append the outer marker. -/
def affineUnaryTripleProgressionRowMarkBody :
    LoopBody UnaryFrameSym UnaryFrameSym where
  emit
    | .tick => [.tick]
    | .separator => [.separator]
    | .frameEnd => [.separator, .frameEnd]
  cost
    | .tick => 1
    | .separator => 1
    | .frameEnd => 2
  emit_length_le_cost := by intro symbol; cases symbol <;> simp

/-- Insert one outer marker after every seven-field descriptor. -/
def markAffineUnaryTripleProgressionRows
    (input : List UnaryFrameSym) : List UnaryFrameSym :=
  (rewriteUnaryFrameDelimiters
      affineUnaryTripleProgressionRowDelimiterTable
      affineUnaryTripleProgressionRowDelimiterTable_nonempty input).flatMap
    affineUnaryTripleProgressionRowMarkBody.emit

/-- Canonical marked descriptor-family encoding. -/
def encodeAffineUnaryTripleProgressionMarkedFamily
    (progressions : List AffineUnaryTripleProgression) :
    List UnaryFrameSym :=
  progressions.flatMap fun progression =>
    encodeAffineUnaryTripleProgression progression ++ [.frameEnd]

/-- The seven unary values stored in one progression descriptor. -/
def affineUnaryTripleProgressionFields
    (progression : AffineUnaryTripleProgression) : List Nat :=
  [progression.base₁, progression.base₂, progression.base₃,
    progression.step₁, progression.step₂, progression.step₃,
    progression.count]

/-- A progression-family descriptor stream is the ordinary unary-frame
encoding of its flattened seven-field descriptors. -/
theorem encodeAffineUnaryTripleProgressionFamily_eq_encodeUnaryFrame
    (progressions : List AffineUnaryTripleProgression) :
    encodeAffineUnaryTripleProgressionFamily progressions =
      encodeUnaryFrame
        (progressions.flatMap affineUnaryTripleProgressionFields) := by
  induction progressions with
  | nil => rfl
  | cons progression rest ih =>
      simp only [encodeAffineUnaryTripleProgressionFamily,
        List.flatMap_cons, encodeAffineUnaryTripleProgression]
      rw [ih]
      simp [affineUnaryTripleProgressionFields, encodeUnaryFrame]

private theorem progressionDelimiterCycle_rows
    (progressions : List AffineUnaryTripleProgression) :
    encodeUnaryFrameWithDelimiterCycle
        affineUnaryTripleProgressionRowDelimiterTable
        affineUnaryTripleProgressionRowDelimiterTable_nonempty
        (progressions.flatMap affineUnaryTripleProgressionFields) =
      progressions.flatMap fun progression =>
        encodeUnaryFrameWithFixedDelimiters
          (affineUnaryTripleProgressionFields progression)
          affineUnaryTripleProgressionRowDelimiterTable := by
  induction progressions with
  | nil => rfl
  | cons progression rest ih =>
      rcases progression with
        ⟨base₁, base₂, base₃, step₁, step₂, step₃, count⟩
      simp only [List.flatMap_cons,
        affineUnaryTripleProgressionFields]
      rw [show
        encodeUnaryFrameWithDelimiterCycle
            affineUnaryTripleProgressionRowDelimiterTable
            affineUnaryTripleProgressionRowDelimiterTable_nonempty
            ([base₁, base₂, base₃, step₁, step₂, step₃,
                count] ++
              rest.flatMap affineUnaryTripleProgressionFields) =
          encodeUnaryFrameWithFixedDelimiters
              [base₁, base₂, base₃, step₁, step₂, step₃,
                count]
              affineUnaryTripleProgressionRowDelimiterTable ++
            encodeUnaryFrameWithDelimiterCycle
              affineUnaryTripleProgressionRowDelimiterTable
              affineUnaryTripleProgressionRowDelimiterTable_nonempty
              (rest.flatMap affineUnaryTripleProgressionFields) by
        simp [affineUnaryTripleProgressionRowDelimiterTable,
          encodeUnaryFrameWithDelimiterCycle,
          encodeUnaryFrameWithDelimiterCycleFrom,
          encodeUnaryFrameWithFixedDelimiters,
          unaryFrameDelimiterNext, List.append_assoc]]
      rw [ih]
      simp [affineUnaryTripleProgressionFields]

private theorem progressionRowMarkBody_ticks (count : Nat) :
    (List.replicate count UnaryFrameSym.tick).flatMap
        affineUnaryTripleProgressionRowMarkBody.emit =
      List.replicate count UnaryFrameSym.tick := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [List.replicate_succ, List.flatMap_cons, ih]
      rfl

private theorem progressionRowMarkBody_fixedFrame
    (progression : AffineUnaryTripleProgression) :
    (encodeUnaryFrameWithFixedDelimiters
        (affineUnaryTripleProgressionFields progression)
        affineUnaryTripleProgressionRowDelimiterTable).flatMap
        affineUnaryTripleProgressionRowMarkBody.emit =
      encodeAffineUnaryTripleProgression progression ++ [.frameEnd] := by
  rcases progression with
    ⟨base₁, base₂, base₃, step₁, step₂, step₃, count⟩
  simp only [affineUnaryTripleProgressionFields,
    affineUnaryTripleProgressionRowDelimiterTable,
    encodeUnaryFrameWithFixedDelimiters,
    encodeAffineUnaryTripleProgression, encodeUnaryFrame,
    encodeUnaryFrameBlock, List.flatMap_cons, List.flatMap_nil,
    List.flatMap_append, List.append_nil]
  rw [progressionRowMarkBody_ticks, progressionRowMarkBody_ticks,
    progressionRowMarkBody_ticks, progressionRowMarkBody_ticks,
    progressionRowMarkBody_ticks, progressionRowMarkBody_ticks,
    progressionRowMarkBody_ticks]
  simp [affineUnaryTripleProgressionRowMarkBody, List.append_assoc]

/-- Exact action on every well-formed adjacent descriptor family. -/
theorem markAffineUnaryTripleProgressionRows_encode
    (progressions : List AffineUnaryTripleProgression) :
    markAffineUnaryTripleProgressionRows
        (encodeAffineUnaryTripleProgressionFamily progressions) =
      encodeAffineUnaryTripleProgressionMarkedFamily progressions := by
  unfold markAffineUnaryTripleProgressionRows
  rw [encodeAffineUnaryTripleProgressionFamily_eq_encodeUnaryFrame]
  rw [rewriteUnaryFrameDelimiters_encodeUnaryFrame]
  rw [progressionDelimiterCycle_rows]
  unfold encodeAffineUnaryTripleProgressionMarkedFamily
  rw [List.flatMap_assoc]
  apply List.flatMap_congr
  intro progression hprogression
  exact progressionRowMarkBody_fixedFrame progression

/-- The symbol-local expansion is a verified fixed linear pass. -/
noncomputable def
    affineUnaryTripleProgressionRowMarkExpand_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id
      (fun input : List UnaryFrameSym =>
        input.flatMap affineUnaryTripleProgressionRowMarkBody.emit) :=
  boundedLoop_computableInPolyTime affineUnaryTripleProgressionRowMarkBody

/-- A concrete polynomial-time TM2 adds descriptor boundaries. -/
noncomputable def
    markAffineUnaryTripleProgressionRows_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id
      markAffineUnaryTripleProgressionRows := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      (unaryFrameDelimiterMap_computableInPolyTime
        affineUnaryTripleProgressionRowDelimiterTable
        affineUnaryTripleProgressionRowDelimiterTable_nonempty)
      affineUnaryTripleProgressionRowMarkExpand_computableInPolyTime
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input : List UnaryFrameSym =>
      (rewriteUnaryFrameDelimiters
        affineUnaryTripleProgressionRowDelimiterTable
        affineUnaryTripleProgressionRowDelimiterTable_nonempty input).flatMap
          affineUnaryTripleProgressionRowMarkBody.emit)
  simpa [Function.comp_def] using Classical.choice composed

end CLRS.Chapter34.Turing.PolyBuilder


