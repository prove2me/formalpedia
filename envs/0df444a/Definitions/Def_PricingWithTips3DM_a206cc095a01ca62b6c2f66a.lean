-- Prove2me | Definitions.Def_PricingWithTips3DM_a206cc095a01ca62b6c2f66a
-- name    : PricingWithTips3DM_a206cc095a01ca62b6c2f66a
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T20:37:21.660644+00:00
-- url     : https://prove2.me/theorems/78c0c4cf-55c0-4365-867c-b6f3ac2eabe0
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.OptionalConjunctionFamilyRuntime
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_3218c687821ca8b4e6c264b4
import Definitions.Def_PricingWithTips3DM_b8c03f33e84411dcd1343113
import Definitions.Def_PricingWithTips3DM_4901b5edb9039a7b71dab674
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Polynomial-time packaging of the optional conjunction-family controller
-/

noncomputable section

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- The compiled controller computes the reversed optional-family gate stream
within its established quadratic bound. -/
noncomputable def affineOptionalConjunctionFamilyRev_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime
      encodeAffineOptionalConjunctionFamily id
      (fun frames : List (Option AffineConjunctionFrame) =>
        (affineOptionalConjunctionFamilyGateStream frames).reverse) where
  tm := compile affineOptionalConjunctionFamilyRevProgram
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 1005 * Polynomial.X ^ 2 + 2
  outputsFun := fun frames => by
    have builderRun := affineOptionalConjunctionFamily_run frames []
    have compiledRun := compile_evalsToInTime
      affineOptionalConjunctionFamilyRevProgram builderRun
    rw [show affineOptionalConjunctionFamilyLoopCfg
        (encodeAffineOptionalConjunctionFamily frames) [] =
          initialCfg affineOptionalConjunctionFamilyRevProgram
            (encodeAffineOptionalConjunctionFamily frames) by rfl] at compiledRun
    have machineRun : _root_.StateTransition.EvalsToInTime
        (compile affineOptionalConjunctionFamilyRevProgram).step
        (_root_.Turing.initList
          (compile affineOptionalConjunctionFamilyRevProgram)
          (encodeAffineOptionalConjunctionFamily frames))
        (some (_root_.Turing.haltList
          (compile affineOptionalConjunctionFamilyRevProgram)
          (affineOptionalConjunctionFamilyGateStream frames).reverse))
        (affineOptionalConjunctionFamilyRevSteps frames) := by
      simpa only [encodeCfg_initialCfg, encodeCfg_haltCfg,
        List.append_nil] using compiledRun
    have htime : affineOptionalConjunctionFamilyRevSteps frames ≤
        (1005 * Polynomial.X ^ 2 + 2).eval
          (encodeAffineOptionalConjunctionFamily frames).length := by
      simpa only [Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_ofNat] using
        affineOptionalConjunctionFamilyRev_steps_le frames
    have boundedRun : _root_.StateTransition.EvalsToInTime
        (compile affineOptionalConjunctionFamilyRevProgram).step
        (_root_.Turing.initList
          (compile affineOptionalConjunctionFamilyRevProgram)
          (encodeAffineOptionalConjunctionFamily frames))
        (some (_root_.Turing.haltList
          (compile affineOptionalConjunctionFamilyRevProgram)
          (affineOptionalConjunctionFamilyGateStream frames).reverse))
        ((1005 * Polynomial.X ^ 2 + 2).eval
          (encodeAffineOptionalConjunctionFamily frames).length) :=
      ⟨machineRun.toEvalsTo, machineRun.steps_le_m.trans htime⟩
    simpa [_root_.Turing.TM2OutputsInTime, compile] using boundedRun

/-- Forward optional conjunction-family gate generation in polynomial time. -/
noncomputable def
    affineOptionalConjunctionFamilyGateStream_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime
      encodeAffineOptionalConjunctionFamily id
      affineOptionalConjunctionFamilyGateStream := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      affineOptionalConjunctionFamilyRev_computableInPolyTime
      (reverse_computableInPolyTime (Γ := CircuitSym))
  simpa [Function.comp_def] using Classical.choice composed

end CLRS.Chapter34.Turing.PolyBuilder


