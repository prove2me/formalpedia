-- Prove2me | Definitions.Def_PricingWithTips3DM_6a5db86dcfbe2e4d5a525200
-- name    : PricingWithTips3DM_6a5db86dcfbe2e4d5a525200
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T20:24:58.981788+00:00
-- url     : https://prove2.me/theorems/8ecd6fe3-c07e-4c9e-8dfb-598c0be1807a
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameQuoteRuntime
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_2edb7f26b0fd9cd1b939c01f
import Definitions.Def_PricingWithTips3DM_b8c03f33e84411dcd1343113
import Definitions.Def_PricingWithTips3DM_4901b5edb9039a7b71dab674
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Polynomial runtime of unary-frame quoting
-/

noncomputable section

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- The concrete quoting controller, before forward-order restoration. -/
noncomputable def unaryFrameQuoteMarkedRev_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id
      (fun input : List UnaryFrameSym =>
        (encodeUnaryFrameMarkedRowFamily
          (quotedUnaryFrameSingleton input)).reverse) where
  tm := compile unaryFrameQuoteMarkedRevProgram
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 3 * Polynomial.X + 3
  outputsFun := fun input => by
    have builderRun := unaryFrameQuoteMarkedRev_run input
    have compiledRun := compile_evalsToInTime
      unaryFrameQuoteMarkedRevProgram builderRun
    have machineRun : _root_.StateTransition.EvalsToInTime
        (compile unaryFrameQuoteMarkedRevProgram).step
        (_root_.Turing.initList
          (compile unaryFrameQuoteMarkedRevProgram) input)
        (some (_root_.Turing.haltList
          (compile unaryFrameQuoteMarkedRevProgram)
          (encodeUnaryFrameMarkedRowFamily
            (quotedUnaryFrameSingleton input)).reverse))
        (unaryFrameQuoteMarkedSteps input) := by
      simpa only [encodeCfg_initialCfg, encodeCfg_haltCfg] using compiledRun
    have htime : unaryFrameQuoteMarkedSteps input ≤
        (3 * Polynomial.X + 3).eval input.length := by
      simp [unaryFrameQuoteMarkedSteps]
    have boundedRun : _root_.StateTransition.EvalsToInTime
        (compile unaryFrameQuoteMarkedRevProgram).step
        (_root_.Turing.initList
          (compile unaryFrameQuoteMarkedRevProgram) input)
        (some (_root_.Turing.haltList
          (compile unaryFrameQuoteMarkedRevProgram)
          (encodeUnaryFrameMarkedRowFamily
            (quotedUnaryFrameSingleton input)).reverse))
        ((3 * Polynomial.X + 3).eval input.length) :=
      ⟨machineRun.toEvalsTo, machineRun.steps_le_m.trans htime⟩
    simpa [_root_.Turing.TM2OutputsInTime, compile] using boundedRun

/-- Forward marked singleton quoting in polynomial time. -/
noncomputable def unaryFrameQuoteMarked_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id
      encodeUnaryFrameMarkedRowFamily quotedUnaryFrameSingleton := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      unaryFrameQuoteMarkedRev_computableInPolyTime
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

/-- Quote the output of any concrete unary-frame transducer as one safe outer
row, while preserving the original raw input. -/
noncomputable def unaryFrameQuoteAfter_computableInPolyTime
    {α Γ : Type} [Fintype Γ] {encode : α → List Γ}
    {f : α → List UnaryFrameSym}
    (M : _root_.Turing.TM2ComputableInPolyTime encode id f) :
    _root_.Turing.TM2ComputableInPolyTime encode
      encodeUnaryFrameMarkedRowFamily
      (fun input => quotedUnaryFrameSingleton (f input)) := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch M
      unaryFrameQuoteMarked_computableInPolyTime
  simpa [Function.comp_def] using Classical.choice composed

end CLRS.Chapter34.Turing.PolyBuilder


