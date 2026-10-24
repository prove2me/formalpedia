-- Prove2me | Definitions.Def_PricingWithTips3DM_a79ce5303af3440f3d4b538fPart3
-- name    : PricingWithTips3DM_a79ce5303af3440f3d4b538fPart3
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T23:27:22.16102+00:00
-- url     : https://prove2.me/theorems/1544dba8-09e8-43d4-a0df-2bd3d333a266
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionEqSource.Part3
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_a79ce5303af3440f3d4b538fPart2
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- The first progression coordinate is the equality carry immediately before
the segment's first public coordinate. -/
theorem transitionEqSegmentProgression_base₁
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (segment : TransitionEqSegment)
    (hwork : 0 < workHeight tm seed.height) :
    (transitionEqSegmentProgression tm seed segment).base₁ =
      transitionEqStart tm seed.height seed.start +
        6 * segment.publicBase.eval seed.height := by
  have hstart : seed.start +
      (transitionEqStartOffsetAffine tm).eval seed.height =
      transitionEqStart tm seed.height seed.start := by
    calc
      seed.start + (transitionEqStartOffsetAffine tm).eval seed.height =
          affineUnaryTripleFormValue (transitionEqStartForm tm)
            (transitionTailAffineSeed seed) := by
        symm
        exact transitionAbsoluteStartForm_value
          (transitionEqStartOffsetAffine tm) seed
      _ = transitionEqStart tm seed.height seed.start :=
        transitionEqStartForm_value tm seed hwork
  unfold transitionEqSegmentProgression transitionEqPreviousForm
  rw [transitionAbsoluteStartForm_value,
    TransitionAffineNat.eval_add, TransitionAffineNat.eval_scale]
  change seed.start +
      ((transitionEqStartOffsetAffine tm).eval seed.height +
        6 * segment.publicBase.eval seed.height) = _
  omega

/-- The second progression coordinate is the exact arithmetic final-mux wire
at the corresponding workspace segment base. -/
theorem transitionEqSegmentProgression_base₂
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (segment : TransitionEqSegment)
    (hwork : 0 < workHeight tm seed.height) :
    (transitionEqSegmentProgression tm seed segment).base₂ =
      seed.start + 2 +
          transitionDispatchListFinalMuxOffset tm seed.height
            (programLabels tm) + 3 +
        3 * segment.workspaceBase.eval seed.height := by
  unfold transitionEqSegmentProgression
  rw [transitionFinalMuxWireForm_value,
    transitionFinalMuxStartForm_value tm seed hwork]
  rfl

/-- The third progression coordinate is the exact source wire in the next
public tableau row. -/
theorem transitionEqSegmentProgression_base₃
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (segment : TransitionEqSegment) :
    (transitionEqSegmentProgression tm seed segment).base₃ =
      seed.rowBase + cfgBitCount tm seed.height +
        segment.publicBase.eval seed.height := by
  unfold transitionEqSegmentProgression transitionEqNextRowForm
    transitionTailAffineSeed affineUnaryTripleFormValue
    TransitionAffineNat.eval
  rw [← transitionCfgBitAffine_eval tm seed.height]
  unfold TransitionAffineNat.eval
  ring

/-- All three fixed strides and the runtime segment length are represented
literally in the progression descriptor. -/
theorem transitionEqSegmentProgression_steps_count
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (segment : TransitionEqSegment) :
    ((transitionEqSegmentProgression tm seed segment).step₁,
      (transitionEqSegmentProgression tm seed segment).step₂,
      (transitionEqSegmentProgression tm seed segment).step₃,
      (transitionEqSegmentProgression tm seed segment).count) =
      (6, 3, 1, segment.count.eval seed.height) := by
  rfl
end CLRS.Chapter34.Turing.CookLevin


