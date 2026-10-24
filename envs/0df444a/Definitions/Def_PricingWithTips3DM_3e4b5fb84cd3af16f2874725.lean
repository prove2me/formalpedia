-- Prove2me | Definitions.Def_PricingWithTips3DM_3e4b5fb84cd3af16f2874725
-- name    : PricingWithTips3DM_3e4b5fb84cd3af16f2874725
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T20:29:43.274811+00:00
-- url     : https://prove2.me/theorems/65fca256-1081-4618-a3bc-7d86670e81b0
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameMarkedRowPresentRuntime
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_8b09f47f7ca25a98af8eeccd
import Definitions.Def_PricingWithTips3DM_b8c03f33e84411dcd1343113
import Definitions.Def_PricingWithTips3DM_4901b5edb9039a7b71dab674
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Marking every delimited row as present: polynomial runtime
-/

noncomputable section

namespace CLRS.Chapter34.Turing.PolyBuilder

theorem unaryFrameMarkedRowPresentRevSteps_le
    (family : UnaryFrameMarkedRowFamily) :
    unaryFrameMarkedRowPresentRevSteps family ≤
      3 * (encodeUnaryFrameMarkedRowFamily family).length + 3 := by
  unfold unaryFrameMarkedRowPresentRevSteps
    encodeUnaryFrameMarkedRowFamily
  induction family.rows with
  | nil => simp
  | cons row rest ih =>
      simp only [List.map_cons, List.sum_cons, List.flatMap_cons,
        List.length_append, List.length_cons, List.length_nil]
      have ih' : (rest.map fun item => 2 * item.length + 3).sum + 3 ≤
          3 * (rest.flatMap fun item => item ++ [.frameEnd]).length + 3 := by
        simpa only using ih
      omega

/-- The prepend-order formatter is a concrete linear-time TM2. -/
noncomputable def unaryFrameMarkedRowPresentRev_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime
      encodeUnaryFrameMarkedRowFamily id
      (fun family : UnaryFrameMarkedRowFamily =>
        (encodeUnaryFramePresentMarkedRowFamily family).reverse) where
  tm := compile unaryFrameMarkedRowPresentRevProgram
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 3 * Polynomial.X + 3
  outputsFun := fun family => by
    have builderRun := unaryFrameMarkedRowPresentRev_run family
    have compiledRun := compile_evalsToInTime
      unaryFrameMarkedRowPresentRevProgram builderRun
    have machineRun : _root_.StateTransition.EvalsToInTime
        (compile unaryFrameMarkedRowPresentRevProgram).step
        (_root_.Turing.initList
          (compile unaryFrameMarkedRowPresentRevProgram)
          (encodeUnaryFrameMarkedRowFamily family))
        (some (_root_.Turing.haltList
          (compile unaryFrameMarkedRowPresentRevProgram)
          (encodeUnaryFramePresentMarkedRowFamily family).reverse))
        (unaryFrameMarkedRowPresentRevSteps family) := by
      simpa only [encodeCfg_initialCfg, encodeCfg_haltCfg] using compiledRun
    have htime : unaryFrameMarkedRowPresentRevSteps family ≤
        (3 * Polynomial.X + 3).eval
          (encodeUnaryFrameMarkedRowFamily family).length := by
      simpa only [Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_X, Polynomial.eval_ofNat] using
        unaryFrameMarkedRowPresentRevSteps_le family
    have boundedRun : _root_.StateTransition.EvalsToInTime
        (compile unaryFrameMarkedRowPresentRevProgram).step
        (_root_.Turing.initList
          (compile unaryFrameMarkedRowPresentRevProgram)
          (encodeUnaryFrameMarkedRowFamily family))
        (some (_root_.Turing.haltList
          (compile unaryFrameMarkedRowPresentRevProgram)
          (encodeUnaryFramePresentMarkedRowFamily family).reverse))
        ((3 * Polynomial.X + 3).eval
          (encodeUnaryFrameMarkedRowFamily family).length) :=
      ⟨machineRun.toEvalsTo, machineRun.steps_le_m.trans htime⟩
    simpa [_root_.Turing.TM2OutputsInTime, compile] using boundedRun

/-- Forward all-present marked-row formatting in polynomial time. -/
noncomputable def unaryFrameMarkedRowPresent_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime
      encodeUnaryFrameMarkedRowFamily id
      encodeUnaryFramePresentMarkedRowFamily := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      unaryFrameMarkedRowPresentRev_computableInPolyTime
      (reverse_computableInPolyTime (Γ := UnaryFrameSym))
  simpa [Function.comp_def] using Classical.choice composed

end CLRS.Chapter34.Turing.PolyBuilder


