-- Prove2me | Definitions.Def_PricingWithTips3DM_b05d2e179e08555d98d2588b
-- name    : PricingWithTips3DM_b05d2e179e08555d98d2588b
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T20:49:11.365839+00:00
-- url     : https://prove2.me/theorems/95ac7055-0372-43a9-9b43-b7f248a79006
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameMarkedOrPairFormatRuntime
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_d43256e2a1daad1acd3ffb2a
import Definitions.Def_PricingWithTips3DM_b8c03f33e84411dcd1343113
import Definitions.Def_PricingWithTips3DM_4901b5edb9039a7b71dab674
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Formatting marked operand pairs as finite-OR frames: polynomial runtime
-/

noncomputable section

namespace CLRS.Chapter34.Turing.PolyBuilder

theorem unaryFrameMarkedOrPairFormatRevSteps_le
    (frames : List AffineOrFinPairFrame) :
    unaryFrameMarkedOrPairFormatRevSteps frames ≤
      3 * (encodeAffineOrFinMarkedPairFrames frames).length + 2 := by
  unfold unaryFrameMarkedOrPairFormatRevSteps
    encodeAffineOrFinMarkedPairFrames
  induction frames with
  | nil => simp
  | cons frame rest ih =>
      simp only [List.map_cons, List.sum_cons, List.flatMap_cons,
        List.length_append]
      have hframeLength :
          (encodeAffineOrFinMarkedPairFrame frame).length =
            frame.left + frame.right + 3 := by
        simp [encodeAffineOrFinMarkedPairFrame]
        omega
      rw [hframeLength]
      have ih' :
          (rest.map fun item =>
            2 * (item.left + item.right) + 9).sum + 2 ≤
          3 * (rest.flatMap encodeAffineOrFinMarkedPairFrame).length + 2 := by
        simpa only using ih
      omega

/-- The prepend-order formatter is a concrete linear-time TM2. -/
noncomputable def unaryFrameMarkedOrPairFormatRev_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime
      encodeAffineOrFinMarkedPairFrames id
      (fun frames : List AffineOrFinPairFrame =>
        (encodeAffineOrFinFrames frames).reverse) where
  tm := compile unaryFrameMarkedOrPairFormatRevProgram
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 3 * Polynomial.X + 2
  outputsFun := fun frames => by
    have builderRun := unaryFrameMarkedOrPairFormatRev_run frames
    have compiledRun := compile_evalsToInTime
      unaryFrameMarkedOrPairFormatRevProgram builderRun
    have machineRun : _root_.StateTransition.EvalsToInTime
        (compile unaryFrameMarkedOrPairFormatRevProgram).step
        (_root_.Turing.initList
          (compile unaryFrameMarkedOrPairFormatRevProgram)
          (encodeAffineOrFinMarkedPairFrames frames))
        (some (_root_.Turing.haltList
          (compile unaryFrameMarkedOrPairFormatRevProgram)
          (encodeAffineOrFinFrames frames).reverse))
        (unaryFrameMarkedOrPairFormatRevSteps frames) := by
      simpa only [encodeCfg_initialCfg, encodeCfg_haltCfg] using compiledRun
    have htime : unaryFrameMarkedOrPairFormatRevSteps frames ≤
        (3 * Polynomial.X + 2).eval
          (encodeAffineOrFinMarkedPairFrames frames).length := by
      simpa only [Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_X, Polynomial.eval_ofNat] using
        unaryFrameMarkedOrPairFormatRevSteps_le frames
    have boundedRun : _root_.StateTransition.EvalsToInTime
        (compile unaryFrameMarkedOrPairFormatRevProgram).step
        (_root_.Turing.initList
          (compile unaryFrameMarkedOrPairFormatRevProgram)
          (encodeAffineOrFinMarkedPairFrames frames))
        (some (_root_.Turing.haltList
          (compile unaryFrameMarkedOrPairFormatRevProgram)
          (encodeAffineOrFinFrames frames).reverse))
        ((3 * Polynomial.X + 2).eval
          (encodeAffineOrFinMarkedPairFrames frames).length) :=
      ⟨machineRun.toEvalsTo, machineRun.steps_le_m.trans htime⟩
    simpa [_root_.Turing.TM2OutputsInTime, compile] using boundedRun

/-- Forward canonical finite-OR frame formatting in polynomial time. -/
noncomputable def unaryFrameMarkedOrPairFormat_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime
      encodeAffineOrFinMarkedPairFrames id encodeAffineOrFinFrames := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      unaryFrameMarkedOrPairFormatRev_computableInPolyTime
      (reverse_computableInPolyTime (Γ := UnaryFrameSym))
  simpa [Function.comp_def] using Classical.choice composed

end CLRS.Chapter34.Turing.PolyBuilder


