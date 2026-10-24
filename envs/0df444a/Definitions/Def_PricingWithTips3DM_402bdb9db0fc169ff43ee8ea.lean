-- Prove2me | Definitions.Def_PricingWithTips3DM_402bdb9db0fc169ff43ee8ea
-- name    : PricingWithTips3DM_402bdb9db0fc169ff43ee8ea
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T20:46:21.472797+00:00
-- url     : https://prove2.me/theorems/798d85ce-aab8-4acc-8819-281c75c69832
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.InputShapeRuntime
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_0ea761f958a4534503fff87f
import Definitions.Def_PricingWithTips3DM_b8c03f33e84411dcd1343113
import Definitions.Def_PricingWithTips3DM_4901b5edb9039a7b71dab674
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Polynomial-time packaging of the continuous input-shape controller

The underlying controller already executes separator NOTs, optional
conjunction arms, and the final disjunction without intermediate halts.  This
module exposes its exact simulation and quadratic input-size envelope through
the fixed-TM2 polynomial-time interface.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- Native prepend-order execution of the complete input-shape script. -/
noncomputable def affineInputShapeRev_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime
      encodeAffineInputShapeScript id
      (fun script : AffineInputShapeScript =>
        (affineInputShapeGateStream script).reverse) where
  tm := compile affineInputShapeRevProgram
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 1200 * Polynomial.X ^ 2 + 20
  outputsFun := fun script => by
    have builderRun := affineInputShape_run script []
    have compiledRun := compile_evalsToInTime
      affineInputShapeRevProgram builderRun
    rw [show affineInputShapeLoopCfg
        (encodeAffineInputShapeScript script) [] =
          initialCfg affineInputShapeRevProgram
            (encodeAffineInputShapeScript script) by rfl] at compiledRun
    have machineRun : _root_.StateTransition.EvalsToInTime
        (compile affineInputShapeRevProgram).step
        (_root_.Turing.initList (compile affineInputShapeRevProgram)
          (encodeAffineInputShapeScript script))
        (some (_root_.Turing.haltList (compile affineInputShapeRevProgram)
          (affineInputShapeGateStream script).reverse))
        (affineInputShapeRevSteps script) := by
      simpa only [encodeCfg_initialCfg, encodeCfg_haltCfg,
        List.append_nil] using compiledRun
    have htime : affineInputShapeRevSteps script ≤
        (1200 * Polynomial.X ^ 2 + 20).eval
          (encodeAffineInputShapeScript script).length := by
      simpa only [Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_pow, Polynomial.eval_X,
        Polynomial.eval_ofNat] using affineInputShapeRev_steps_le script
    have boundedRun : _root_.StateTransition.EvalsToInTime
        (compile affineInputShapeRevProgram).step
        (_root_.Turing.initList (compile affineInputShapeRevProgram)
          (encodeAffineInputShapeScript script))
        (some (_root_.Turing.haltList (compile affineInputShapeRevProgram)
          (affineInputShapeGateStream script).reverse))
        ((1200 * Polynomial.X ^ 2 + 20).eval
          (encodeAffineInputShapeScript script).length) :=
      ⟨machineRun.toEvalsTo, machineRun.steps_le_m.trans htime⟩
    simpa [_root_.Turing.TM2OutputsInTime, compile] using boundedRun

/-- Forward complete input-shape circuit serialization. -/
noncomputable def affineInputShapeGateStream_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime
      encodeAffineInputShapeScript id affineInputShapeGateStream := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      affineInputShapeRev_computableInPolyTime
      (reverse_computableInPolyTime (Γ := CircuitSym))
  simpa [Function.comp_def] using Classical.choice composed

end CLRS.Chapter34.Turing.PolyBuilder


