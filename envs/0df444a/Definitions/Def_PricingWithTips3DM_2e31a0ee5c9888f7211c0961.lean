-- Prove2me | Definitions.Def_PricingWithTips3DM_2e31a0ee5c9888f7211c0961
-- name    : PricingWithTips3DM_2e31a0ee5c9888f7211c0961
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T20:28:31.424126+00:00
-- url     : https://prove2.me/theorems/1983935b-233a-4fe0-959c-8c6b72685e83
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineUnaryTripleProgressionRowUnmark
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_7019935caab4d9733d34fc99
import Definitions.Def_PricingWithTips3DM_3799fd79c9b0b4d68c438353
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Removing affine progression descriptor row markers

The periodic selector keeps the outer `frameEnd` attached to every selected
seven-field descriptor.  The standard progression-family executor expects the
same descriptors concatenated with only their ordinary separators.  This file
supplies the fixed linear bridge between those two encodings.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- Preserve ordinary descriptor symbols and erase outer row markers. -/
def affineUnaryTripleProgressionRowUnmarkBody :
    LoopBody UnaryFrameSym UnaryFrameSym where
  emit
    | .tick => [.tick]
    | .separator => [.separator]
    | .frameEnd => []
  cost _ := 1
  emit_length_le_cost := by intro symbol; cases symbol <;> simp

/-- Remove every outer descriptor marker in one streaming pass. -/
def unmarkAffineUnaryTripleProgressionRows
    (input : List UnaryFrameSym) : List UnaryFrameSym :=
  input.flatMap affineUnaryTripleProgressionRowUnmarkBody.emit

/-- Marked descriptor encoding preserves concatenation. -/
theorem encodeAffineUnaryTripleProgressionMarkedFamily_append
    (left right : List AffineUnaryTripleProgression) :
    encodeAffineUnaryTripleProgressionMarkedFamily (left ++ right) =
      encodeAffineUnaryTripleProgressionMarkedFamily left ++
        encodeAffineUnaryTripleProgressionMarkedFamily right := by
  simp [encodeAffineUnaryTripleProgressionMarkedFamily,
    List.flatMap_append]

/-- Encoding separately marked descriptor groups is the marked encoding of
their flattened progression family. -/
theorem encodeAffineUnaryTripleProgressionMarkedFamily_flatMap
    {ι : Type} (indices : List ι)
    (progressions : ι → List AffineUnaryTripleProgression) :
    indices.flatMap (fun index =>
        encodeAffineUnaryTripleProgressionMarkedFamily
          (progressions index)) =
      encodeAffineUnaryTripleProgressionMarkedFamily
        (indices.flatMap progressions) := by
  induction indices with
  | nil => rfl
  | cons index indices ih =>
      simp only [List.flatMap_cons]
      rw [encodeAffineUnaryTripleProgressionMarkedFamily_append, ih]

private theorem progressionRowUnmarkBody_ticks (count : Nat) :
    (List.replicate count UnaryFrameSym.tick).flatMap
        affineUnaryTripleProgressionRowUnmarkBody.emit =
      List.replicate count UnaryFrameSym.tick := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [List.replicate_succ, List.flatMap_cons, ih]
      rfl

private theorem progressionRowUnmarkBody_frame (values : List Nat) :
    (encodeUnaryFrame values).flatMap
        affineUnaryTripleProgressionRowUnmarkBody.emit =
      encodeUnaryFrame values := by
  induction values with
  | nil => rfl
  | cons value values ih =>
      rw [show encodeUnaryFrame (value :: values) =
          List.replicate value .tick ++ .separator ::
            encodeUnaryFrame values by
        simp [encodeUnaryFrame, encodeUnaryFrameBlock]]
      rw [List.flatMap_append, progressionRowUnmarkBody_ticks]
      change List.replicate value .tick ++
          .separator :: (encodeUnaryFrame values).flatMap
            affineUnaryTripleProgressionRowUnmarkBody.emit =
        List.replicate value .tick ++ .separator :: encodeUnaryFrame values
      rw [ih]

/-- Removing the outer boundary from each arbitrary marked unary row preserves
all ordinary fields and concatenates their values. -/
theorem unmarkAffineUnaryTripleProgressionRows_markedValues
    (rows : List (List Nat)) :
    unmarkAffineUnaryTripleProgressionRows
        (rows.flatMap fun row => encodeUnaryFrame row ++ [.frameEnd]) =
      encodeUnaryFrame rows.flatten := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      unfold unmarkAffineUnaryTripleProgressionRows at ih ⊢
      simp only [List.flatMap_cons, List.flatMap_append]
      rw [progressionRowUnmarkBody_frame]
      change encodeUnaryFrame row ++ [] ++
          (rows.flatMap fun other =>
            encodeUnaryFrame other ++ [.frameEnd]).flatMap
              affineUnaryTripleProgressionRowUnmarkBody.emit = _
      simp only [List.append_nil]
      rw [ih]
      simp [encodeUnaryFrame, List.flatten_cons, List.flatMap_append]

private theorem progressionRowUnmarkBody_descriptor
    (progression : AffineUnaryTripleProgression) :
    (encodeAffineUnaryTripleProgression progression ++
        [UnaryFrameSym.frameEnd]).flatMap
        affineUnaryTripleProgressionRowUnmarkBody.emit =
      encodeAffineUnaryTripleProgression progression := by
  rcases progression with
    ⟨base₁, base₂, base₃, step₁, step₂, step₃, count⟩
  simp only [encodeAffineUnaryTripleProgression, encodeUnaryFrame,
    encodeUnaryFrameBlock, List.flatMap_append, List.flatMap_cons,
    List.flatMap_nil, List.append_nil]
  rw [progressionRowUnmarkBody_ticks, progressionRowUnmarkBody_ticks,
    progressionRowUnmarkBody_ticks, progressionRowUnmarkBody_ticks,
    progressionRowUnmarkBody_ticks, progressionRowUnmarkBody_ticks,
    progressionRowUnmarkBody_ticks]
  simp [affineUnaryTripleProgressionRowUnmarkBody, List.append_assoc]

/-- Removing the outer markers recovers the canonical adjacent descriptor
family exactly. -/
theorem unmarkAffineUnaryTripleProgressionRows_encode
    (progressions : List AffineUnaryTripleProgression) :
    unmarkAffineUnaryTripleProgressionRows
        (encodeAffineUnaryTripleProgressionMarkedFamily progressions) =
      encodeAffineUnaryTripleProgressionFamily progressions := by
  induction progressions with
  | nil => rfl
  | cons progression rest ih =>
      unfold unmarkAffineUnaryTripleProgressionRows
      simp only [encodeAffineUnaryTripleProgressionMarkedFamily,
        List.flatMap_cons]
      rw [List.flatMap_append]
      change
        (encodeAffineUnaryTripleProgression progression ++
            [UnaryFrameSym.frameEnd]).flatMap
              affineUnaryTripleProgressionRowUnmarkBody.emit ++
          unmarkAffineUnaryTripleProgressionRows
            (encodeAffineUnaryTripleProgressionMarkedFamily rest) =
        encodeAffineUnaryTripleProgressionFamily (progression :: rest)
      rw [progressionRowUnmarkBody_descriptor]
      rw [ih]
      rfl

/-- A concrete fixed polynomial-time TM2 removes all descriptor row markers. -/
noncomputable def
    unmarkAffineUnaryTripleProgressionRows_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id
      unmarkAffineUnaryTripleProgressionRows := by
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input : List UnaryFrameSym =>
      input.flatMap affineUnaryTripleProgressionRowUnmarkBody.emit)
  exact boundedLoop_computableInPolyTime
    affineUnaryTripleProgressionRowUnmarkBody

end CLRS.Chapter34.Turing.PolyBuilder


