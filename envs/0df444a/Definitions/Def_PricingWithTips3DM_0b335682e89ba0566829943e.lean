-- Prove2me | Definitions.Def_PricingWithTips3DM_0b335682e89ba0566829943e
-- name    : PricingWithTips3DM_0b335682e89ba0566829943e
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T23:50:59.685621+00:00
-- url     : https://prove2.me/theorems/8e7e55be-97a4-47b3-b16a-d157b6aaf846
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionWidenedFallbackAffine
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_f5cd994ce679938ea5a5f401
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Fixed affine segment table for widened transition fallbacks

The widened source row is a fixed family of affine progressions.  Public
coordinates advance by one, while overflow height bits and blank-cell bits
are constant progressions from the local false/true wires.  Only bases and
counts depend on the runtime transition-row seed.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- One fixed progression segment of the widened fallback row. -/
structure TransitionWidenedFallbackSegment where
  base : AffineUnaryTripleForm
  step : Nat
  count : TransitionAffineNat
deriving DecidableEq, Repr

/-- Embed a height-affine offset as an absolute public-row coordinate. -/
def transitionAbsoluteRowBaseForm
    (offset : TransitionAffineNat) : AffineUnaryTripleForm :=
  { constant := offset.constant
    first := offset.coefficient
    second := 0
    third := 1 }

@[simp] theorem transitionAbsoluteRowBaseForm_value
    (offset : TransitionAffineNat) (seed : TransitionRowSeed) :
    affineUnaryTripleFormValue (transitionAbsoluteRowBaseForm offset)
        (transitionTailAffineSeed seed) =
      seed.rowBase + offset.eval seed.height := by
  simp [transitionAbsoluteRowBaseForm, transitionTailAffineSeed,
    affineUnaryTripleFormValue, TransitionAffineNat.eval]
  ring

/-- Runtime triple progression denoted by one fixed fallback segment.  The
second and third tracks are deliberately zero; the first track is the source
wire stream. -/
def transitionWidenedFallbackSegmentProgression
    (seed : TransitionRowSeed)
    (segment : TransitionWidenedFallbackSegment) :
    AffineUnaryTripleProgression :=
  { base₁ := affineUnaryTripleFormValue segment.base
      (transitionTailAffineSeed seed)
    base₂ := 0
    base₃ := 0
    step₁ := segment.step
    step₂ := 0
    step₃ := 0
    count := segment.count.eval seed.height }

/-- Fixed common prefix segment. -/
def transitionWidenedFallbackPrefixSegment
    (tm : _root_.Turing.FinTM2) : TransitionWidenedFallbackSegment :=
  { base := transitionAbsoluteRowBaseForm (TransitionAffineNat.const 0)
    step := 1
    count := TransitionAffineNat.const (transitionEqPrefixWidth tm) }

/-- Public height coordinates of one fixed stack. -/
noncomputable def transitionWidenedFallbackPublicHeightSegment
    (tm : _root_.Turing.FinTM2) (k : tm.K) :
    TransitionWidenedFallbackSegment :=
  { base := transitionAbsoluteRowBaseForm
      ((TransitionAffineNat.const (transitionEqPrefixWidth tm)).add
        (transitionStackBitOffsetAffine tm k))
    step := 1
    count := { constant := 1, coefficient := 1 } }

/-- Fixed false overflow suffix of one stack's height vector. -/
def transitionWidenedFallbackOverflowHeightSegment
    (tm : _root_.Turing.FinTM2) : TransitionWidenedFallbackSegment :=
  { base := transitionAbsoluteStartForm (TransitionAffineNat.const 0)
    step := 0
    count := TransitionAffineNat.const (maxPushesPerStep tm) }

/-- Public cell-symbol coordinates of one fixed stack. -/
noncomputable def transitionWidenedFallbackPublicCellSegment
    (tm : _root_.Turing.FinTM2) (k : tm.K) :
    TransitionWidenedFallbackSegment :=
  let heightSucc : TransitionAffineNat :=
    { constant := 1, coefficient := 1 }
  { base := transitionAbsoluteRowBaseForm
      (((TransitionAffineNat.const (transitionEqPrefixWidth tm)).add
        (transitionStackBitOffsetAffine tm k)).add heightSucc)
    step := 1
    count := { constant := 0
               coefficient := (reachableAlphabet tm k).card + 1 } }

/-- False-symbol prefix of one extra blank cell. -/
def transitionWidenedFallbackBlankFalseSegment
    (tm : _root_.Turing.FinTM2) (k : tm.K) :
    TransitionWidenedFallbackSegment :=
  { base := transitionAbsoluteStartForm (TransitionAffineNat.const 0)
    step := 0
    count := TransitionAffineNat.const (reachableAlphabet tm k).card }

/-- Final true-symbol coordinate of one extra blank cell. -/
def transitionWidenedFallbackBlankTrueSegment :
    TransitionWidenedFallbackSegment :=
  { base := transitionAbsoluteStartForm (TransitionAffineNat.const 1)
    step := 0
    count := TransitionAffineNat.const 1 }

/-- Two fixed progression segments spelling one blank one-hot vector. -/
def transitionWidenedFallbackBlankCellSegments
    (tm : _root_.Turing.FinTM2) (k : tm.K) :
    List TransitionWidenedFallbackSegment :=
  [transitionWidenedFallbackBlankFalseSegment tm k,
    transitionWidenedFallbackBlankTrueSegment]

/-- Complete fixed segment table for one stack. -/
noncomputable def transitionWidenedFallbackStackSegments
    (tm : _root_.Turing.FinTM2) (k : tm.K) :
    List TransitionWidenedFallbackSegment :=
  [transitionWidenedFallbackPublicHeightSegment tm k,
    transitionWidenedFallbackOverflowHeightSegment tm,
    transitionWidenedFallbackPublicCellSegment tm k] ++
    (List.replicate (maxPushesPerStep tm)
      (transitionWidenedFallbackBlankCellSegments tm k)).flatten

/-- Complete machine-fixed segment table, in canonical workspace order. -/
noncomputable def transitionWidenedFallbackSegments
    (tm : _root_.Turing.FinTM2) :
    List TransitionWidenedFallbackSegment :=
  transitionWidenedFallbackPrefixSegment tm ::
    ((arithmeticRuntimeStackSourceIndices tm).map fun position =>
      transitionWidenedFallbackStackSegments tm
        ((arithmeticStackEquiv tm).symm position)).flatten

/-- Runtime progression family for one widened fallback row. -/
noncomputable def transitionWidenedFallbackProgressions
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    List AffineUnaryTripleProgression :=
  (transitionWidenedFallbackSegments tm).map
    (transitionWidenedFallbackSegmentProgression seed)

/-- Seven affine forms encoding one segment descriptor. -/
def transitionWidenedFallbackSegmentDescriptorForms
    (segment : TransitionWidenedFallbackSegment) :
    List AffineUnaryTripleForm :=
  [ segment.base, transitionZeroForm, transitionZeroForm,
    transitionHeightAffineForm (TransitionAffineNat.const segment.step),
    transitionZeroForm, transitionZeroForm,
    transitionHeightAffineForm segment.count ]

/-- Complete fixed descriptor-form table for a widened fallback row. -/
noncomputable def transitionWidenedFallbackDescriptorForms
    (tm : _root_.Turing.FinTM2) : List AffineUnaryTripleForm :=
  (transitionWidenedFallbackSegments tm).flatMap
    transitionWidenedFallbackSegmentDescriptorForms

/-- A segment's fixed forms evaluate literally to its runtime descriptor. -/
theorem transitionWidenedFallbackSegmentDescriptorForms_value
    (seed : TransitionRowSeed)
    (segment : TransitionWidenedFallbackSegment) :
    affineUnaryTripleMap
        (transitionWidenedFallbackSegmentDescriptorForms segment)
        (transitionTailAffineSeed seed) =
      let progression :=
        transitionWidenedFallbackSegmentProgression seed segment
      [ progression.base₁, progression.base₂, progression.base₃,
        progression.step₁, progression.step₂, progression.step₃,
        progression.count ] := by
  simp [transitionWidenedFallbackSegmentDescriptorForms,
    transitionWidenedFallbackSegmentProgression, affineUnaryTripleMap,
    transitionZeroForm, transitionHeightAffineForm,
    transitionTailAffineSeed, affineUnaryTripleFormValue,
    TransitionAffineNat.const, TransitionAffineNat.eval]

/-- Evaluating the whole fixed form table gives the concatenated runtime
progression descriptors. -/
theorem transitionWidenedFallbackDescriptorForms_value
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    affineUnaryTripleMap (transitionWidenedFallbackDescriptorForms tm)
        (transitionTailAffineSeed seed) =
      (transitionWidenedFallbackProgressions tm seed).flatMap
        fun progression =>
          [ progression.base₁, progression.base₂, progression.base₃,
            progression.step₁, progression.step₂, progression.step₃,
            progression.count ] := by
  unfold transitionWidenedFallbackDescriptorForms
    transitionWidenedFallbackProgressions affineUnaryTripleMap
  rw [List.map_flatMap, List.flatMap_map]
  apply List.flatMap_congr
  intro segment hsegment
  exact transitionWidenedFallbackSegmentDescriptorForms_value seed segment

/-- The descriptor bytes are exactly the generic progression-family input. -/
theorem encode_transitionWidenedFallbackDescriptorForms
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    encodeUnaryFrame
        (affineUnaryTripleMap (transitionWidenedFallbackDescriptorForms tm)
          (transitionTailAffineSeed seed)) =
      encodeAffineUnaryTripleProgressionFamily
        (transitionWidenedFallbackProgressions tm seed) := by
  rw [transitionWidenedFallbackDescriptorForms_value]
  unfold encodeUnaryFrame
  induction transitionWidenedFallbackProgressions tm seed with
  | nil => rfl
  | cons progression rest ih =>
      simp only [List.flatMap_cons,
        encodeAffineUnaryTripleProgressionFamily,
        encodeAffineUnaryTripleProgression, List.flatMap_append]
      rw [ih]
      simp [encodeUnaryFrame, List.append_assoc]

end CLRS.Chapter34.Turing.CookLevin


