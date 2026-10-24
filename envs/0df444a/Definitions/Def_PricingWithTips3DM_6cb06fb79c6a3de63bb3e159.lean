-- Prove2me | Definitions.Def_PricingWithTips3DM_6cb06fb79c6a3de63bb3e159
-- name    : PricingWithTips3DM_6cb06fb79c6a3de63bb3e159
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T00:14:50.165112+00:00
-- url     : https://prove2.me/theorems/2c2a864f-45ab-4591-a5a2-ce1b9dceb8a1
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionAffineSegmentRows
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_fcac0fb729b928d3bd42b05a
import Definitions.Def_PricingWithTips3DM_0306f51dc568c965b1a88480
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Raw-input affine segment rows

The ordinary affine segment compiler merges a fixed table into one marked
value row.  Stack pop needs the individual segment boundaries long enough to
delete fixed prefixes at selected positions.  This variant executes every
segment as a singleton descriptor group and therefore emits one marked unary
row per segment, still from the original verifier input and in polynomial
time.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- One first-coordinate value row per affine segment. -/
def transitionAffineSegmentValueRows
    (seed : TransitionRowSeed)
    (segments : List TransitionWidenedFallbackSegment) :
    List (List Nat) :=
  segments.map (transitionWidenedFallbackSegmentValues seed)

private theorem fixedGroupZeroFirstFrameStream
    (progressions : List AffineUnaryTripleProgression) :
    affineUnaryTripleProgressionFixedGroupFirstFrameStream 0 progressions =
      progressions.flatMap fun progression =>
        encodeUnaryFrame
          ((affineUnaryTripleProgressionRows progression).map fun row =>
            row.1) ++ [.frameEnd] := by
  induction progressions with
  | nil => rfl
  | cons progression rest ih =>
      simp only [affineUnaryTripleProgressionFixedGroupFirstFrameStream,
        affineUnaryTripleProgressionFixedGroupFirstFrameStreamFrom,
        List.flatMap_cons]
      change encodeUnaryFrame
            ((affineUnaryTripleProgressionRows progression).map fun row =>
              row.1) ++
          .frameEnd ::
            affineUnaryTripleProgressionFixedGroupFirstFrameStream 0 rest = _
      rw [ih]
      simp [List.append_assoc]

/-- Execute each fixed affine segment separately and project its first
coordinate. -/
noncomputable def verifierTransitionAffineSegmentRowFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (segments : List TransitionWidenedFallbackSegment)
    (input : List Γ) : List UnaryFrameSym :=
  projectUnaryTripleGroupFirst
    (affineUnaryTripleProgressionFixedGroupFrameStream 0
      ((verifierTransitionRowSeeds W input).flatMap fun seed =>
        transitionAffineSegmentProgressions seed segments))

/-- The raw row source is exactly the segment-major encoding expected by the
fixed-position prefix-drop controller. -/
theorem verifierTransitionAffineSegmentRowFrames_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (segments : List TransitionWidenedFallbackSegment)
    (input : List Γ) :
    verifierTransitionAffineSegmentRowFrames W segments input =
      encodeUnaryFrameFixedGroupPrefixDropInput
        ((verifierTransitionRowSeeds W input).map fun seed =>
          transitionAffineSegmentValueRows seed segments) := by
  unfold verifierTransitionAffineSegmentRowFrames
  rw [projectUnaryTripleGroupFirst_fixedGroupStream]
  rw [fixedGroupZeroFirstFrameStream]
  unfold encodeUnaryFrameFixedGroupPrefixDropInput
    transitionAffineSegmentValueRows
    transitionAffineSegmentProgressions
  generalize verifierTransitionRowSeeds W input = seeds
  induction seeds with
  | nil => rfl
  | cons seed rest ih =>
      simp only [List.flatMap_cons, List.map_cons,
        List.flatMap_append]
      rw [ih]
      congr 1
      rw [List.flatMap_map, List.flatMap_map]
      apply List.flatMap_congr
      intro segment hsegment
      rfl

/-- The separated segment rows are polynomial-time computable from the
original verifier word. -/
noncomputable def
    verifierTransitionAffineSegmentRowFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (segments : List TransitionWidenedFallbackSegment) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionAffineSegmentRowFrames W segments) := by
  let descriptors :=
    verifierTransitionAffineSegmentDescriptorFrames_computableInPolyTime
      W segments
  let structured : _root_.Turing.TM2ComputableInPolyTime id
      encodeAffineUnaryTripleProgressionFamily
      (fun input =>
        (verifierTransitionRowSeeds W input).flatMap fun seed =>
          transitionAffineSegmentProgressions seed segments) :=
    { tm := descriptors.tm
      inputAlphabet := descriptors.inputAlphabet
      outputAlphabet := descriptors.outputAlphabet
      time := descriptors.time
      outputsFun := fun input => by
        have run := descriptors.outputsFun input
        simpa only [id_eq,
          verifierTransitionAffineSegmentDescriptorFrames_eq
            W segments input] using run }
  let executed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch structured
      (affineUnaryTripleProgressionFixedGroupFrameStream_computableInPolyTime 0)
  let projected :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      (Classical.choice executed)
      projectUnaryTripleGroupFirst_computableInPolyTime
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input => projectUnaryTripleGroupFirst
      (affineUnaryTripleProgressionFixedGroupFrameStream 0
        ((verifierTransitionRowSeeds W input).flatMap fun seed =>
          transitionAffineSegmentProgressions seed segments)))
  simpa [Function.comp_def] using Classical.choice projected

end CLRS.Chapter34.Turing.CookLevin


