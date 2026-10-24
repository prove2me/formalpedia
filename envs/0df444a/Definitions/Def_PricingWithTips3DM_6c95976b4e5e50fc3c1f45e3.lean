-- Prove2me | Definitions.Def_PricingWithTips3DM_6c95976b4e5e50fc3c1f45e3
-- name    : PricingWithTips3DM_6c95976b4e5e50fc3c1f45e3
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T20:26:55.773016+00:00
-- url     : https://prove2.me/theorems/7443fbe1-1eb3-4843-9835-950d3a1376c0
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameUnquoteRuntime
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_e54fd9f21278f9dc24c110df
import Definitions.Def_PricingWithTips3DM_b8c03f33e84411dcd1343113
import Definitions.Def_PricingWithTips3DM_4901b5edb9039a7b71dab674
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Polynomial runtime of unary-frame unquoting
-/

noncomputable section

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- The concrete total decoder, before forward-order restoration. -/
noncomputable def unaryFrameUnquoteRev_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id
      (fun input : List UnaryFrameSym =>
        (unquoteUnaryFrameStream input).reverse) where
  tm := compile unaryFrameUnquoteRevProgram
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 3 * Polynomial.X + 3
  outputsFun := fun input => by
    have builderRun := unaryFrameUnquoteRev_run input
    have compiledRun := compile_evalsToInTime
      unaryFrameUnquoteRevProgram builderRun
    have machineRun : _root_.StateTransition.EvalsToInTime
        (compile unaryFrameUnquoteRevProgram).step
        (_root_.Turing.initList
          (compile unaryFrameUnquoteRevProgram) input)
        (some (_root_.Turing.haltList
          (compile unaryFrameUnquoteRevProgram)
          (unquoteUnaryFrameStream input).reverse))
        (unaryFrameUnquoteSteps input) := by
      simpa only [encodeCfg_initialCfg, encodeCfg_haltCfg] using compiledRun
    have htime : unaryFrameUnquoteSteps input ≤
        (3 * Polynomial.X + 3).eval input.length := by
      simpa using unaryFrameUnquoteSteps_le input
    have boundedRun : _root_.StateTransition.EvalsToInTime
        (compile unaryFrameUnquoteRevProgram).step
        (_root_.Turing.initList
          (compile unaryFrameUnquoteRevProgram) input)
        (some (_root_.Turing.haltList
          (compile unaryFrameUnquoteRevProgram)
          (unquoteUnaryFrameStream input).reverse))
        ((3 * Polynomial.X + 3).eval input.length) :=
      ⟨machineRun.toEvalsTo, machineRun.steps_le_m.trans htime⟩
    simpa [_root_.Turing.TM2OutputsInTime, compile] using boundedRun

/-- Total forward-order unary-frame decoding is polynomial-time computable. -/
noncomputable def unaryFrameUnquote_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id
      unquoteUnaryFrameStream := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      unaryFrameUnquoteRev_computableInPolyTime
      (reverse_computableInPolyTime (Γ := UnaryFrameSym))
  let raw := Classical.choice composed
  exact
    { tm := raw.tm
      inputAlphabet := raw.inputAlphabet
      outputAlphabet := raw.outputAlphabet
      time := raw.time
      outputsFun := fun input => by
        have run := raw.outputsFun input
        simpa [Function.comp_def] using run }

end CLRS.Chapter34.Turing.PolyBuilder


