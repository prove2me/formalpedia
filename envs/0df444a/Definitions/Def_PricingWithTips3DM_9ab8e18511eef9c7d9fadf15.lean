-- Prove2me | Definitions.Def_PricingWithTips3DM_9ab8e18511eef9c7d9fadf15
-- name    : PricingWithTips3DM_9ab8e18511eef9c7d9fadf15
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T20:45:39.324207+00:00
-- url     : https://prove2.me/theorems/27a708a2-d952-4c96-a21a-f037d2cd113d
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.OrFinRuntime
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_a46ec1070e8b9fcb3ebc4d0c
import Definitions.Def_PricingWithTips3DM_b8c03f33e84411dcd1343113
import Definitions.Def_PricingWithTips3DM_4901b5edb9039a7b71dab674
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Polynomial-time packaging of the finite OR-family controller

The controller in `OrFin` has an exact simulation and a linear runtime bound.
This module exposes those facts through the fixed-TM2 polynomial-time
interface, both for its native reverse output and for the forward circuit
stream used by Cook--Levin circuit generation.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- The fixed controller compiles arbitrary runtime OR frames to the reverse
gate stream in linear time in the explicit unary encoding. -/
noncomputable def affineOrFinRev_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime
      encodeAffineOrFinFrames id
      (fun frames : List AffineOrFinPairFrame =>
        (affineOrFinGateStream frames).reverse) where
  tm := compile affineOrFinRevProgram
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 100 * Polynomial.X + 3
  outputsFun := fun frames => by
    have builderRun := affineOrFin_run frames []
    have compiledRun := compile_evalsToInTime
      affineOrFinRevProgram builderRun
    rw [show affineOrFinLoopCfg (encodeAffineOrFinFrames frames) [] =
        initialCfg affineOrFinRevProgram
          (encodeAffineOrFinFrames frames) by rfl] at compiledRun
    have machineRun : _root_.StateTransition.EvalsToInTime
        (compile affineOrFinRevProgram).step
        (_root_.Turing.initList (compile affineOrFinRevProgram)
          (encodeAffineOrFinFrames frames))
        (some (_root_.Turing.haltList (compile affineOrFinRevProgram)
          (affineOrFinGateStream frames).reverse))
        (affineOrFinRevSteps frames) := by
      simpa only [encodeCfg_initialCfg, encodeCfg_haltCfg,
        List.append_nil] using compiledRun
    have htime : affineOrFinRevSteps frames ≤
        (100 * Polynomial.X + 3).eval
          (encodeAffineOrFinFrames frames).length := by
      simpa only [Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_X, Polynomial.eval_ofNat] using
        affineOrFinRev_steps_le frames
    have boundedRun : _root_.StateTransition.EvalsToInTime
        (compile affineOrFinRevProgram).step
        (_root_.Turing.initList (compile affineOrFinRevProgram)
          (encodeAffineOrFinFrames frames))
        (some (_root_.Turing.haltList (compile affineOrFinRevProgram)
          (affineOrFinGateStream frames).reverse))
        ((100 * Polynomial.X + 3).eval
          (encodeAffineOrFinFrames frames).length) :=
      ⟨machineRun.toEvalsTo, machineRun.steps_le_m.trans htime⟩
    simpa [_root_.Turing.TM2OutputsInTime, compile] using boundedRun

/-- Forward finite OR-family gate serialization in polynomial time. -/
noncomputable def affineOrFinGateStream_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime
      encodeAffineOrFinFrames id affineOrFinGateStream := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      affineOrFinRev_computableInPolyTime
      (reverse_computableInPolyTime (Γ := CircuitSym))
  simpa [Function.comp_def] using Classical.choice composed

end CLRS.Chapter34.Turing.PolyBuilder


