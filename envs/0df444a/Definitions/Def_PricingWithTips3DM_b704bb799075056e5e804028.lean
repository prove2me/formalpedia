-- Prove2me | Definitions.Def_PricingWithTips3DM_b704bb799075056e5e804028
-- name    : PricingWithTips3DM_b704bb799075056e5e804028
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T20:38:04.658851+00:00
-- url     : https://prove2.me/theorems/443f2863-2f50-418f-a43f-aa904018a206
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameLengthPrefixedFourWaySplitRuntime
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_8f19129848b25a45a212d372
import Definitions.Def_PricingWithTips3DM_b8c03f33e84411dcd1343113
import Definitions.Def_PricingWithTips3DM_4901b5edb9039a7b71dab674
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Polynomial-time TM2 for the dynamic four-way splitter

The verified builder is compiled to one concrete TM2.  Its reversed stack
output is then composed with the existing polynomial-time list reverser to
expose the forward four-row family stream.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- Concrete linear-time TM2 producing the reversed four-row stream. -/
noncomputable def
    unaryFrameLengthPrefixedFourWayPacketFamilyOutputRev_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime
      encodeUnaryFrameLengthPrefixedFourWayPacketFamily id
      (fun packets =>
        (unaryFrameLengthPrefixedFourWayPacketFamilyOutput packets).reverse) where
  tm := compile unaryFrameLengthPrefixedFourWaySplitRevProgram
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 6 * Polynomial.X + 2
  outputsFun := fun packets => by
    have builderRun :=
      unaryFrameLengthPrefixedFourWaySplitRev_haltRun packets
    have compiledRun := compile_evalsToInTime
      unaryFrameLengthPrefixedFourWaySplitRevProgram builderRun
    have machineRun : _root_.StateTransition.EvalsToInTime
        (compile unaryFrameLengthPrefixedFourWaySplitRevProgram).step
        (_root_.Turing.initList
          (compile unaryFrameLengthPrefixedFourWaySplitRevProgram)
          (encodeUnaryFrameLengthPrefixedFourWayPacketFamily packets))
        (some (_root_.Turing.haltList
          (compile unaryFrameLengthPrefixedFourWaySplitRevProgram)
          (unaryFrameLengthPrefixedFourWayPacketFamilyOutput packets).reverse))
        (unaryFrameLengthPrefixedFourWayPacketFamilySteps packets + 2) := by
      simpa only [encodeCfg_initialCfg, encodeCfg_haltCfg] using compiledRun
    have htime :
        unaryFrameLengthPrefixedFourWayPacketFamilySteps packets + 2 ≤
          (6 * Polynomial.X + 2).eval
            (encodeUnaryFrameLengthPrefixedFourWayPacketFamily packets).length := by
      have hbound :=
        unaryFrameLengthPrefixedFourWayPacketFamilySteps_le packets
      simp only [Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_X, Polynomial.eval_ofNat]
      omega
    have boundedRun : _root_.StateTransition.EvalsToInTime
        (compile unaryFrameLengthPrefixedFourWaySplitRevProgram).step
        (_root_.Turing.initList
          (compile unaryFrameLengthPrefixedFourWaySplitRevProgram)
          (encodeUnaryFrameLengthPrefixedFourWayPacketFamily packets))
        (some (_root_.Turing.haltList
          (compile unaryFrameLengthPrefixedFourWaySplitRevProgram)
          (unaryFrameLengthPrefixedFourWayPacketFamilyOutput packets).reverse))
        ((6 * Polynomial.X + 2).eval
          (encodeUnaryFrameLengthPrefixedFourWayPacketFamily packets).length) :=
      ⟨machineRun.toEvalsTo, machineRun.steps_le_m.trans htime⟩
    simpa [_root_.Turing.TM2OutputsInTime, compile] using boundedRun

/-- Forward four-row packet-family stream, exposed as a concrete
polynomial-time TM2 computation. -/
noncomputable def
    unaryFrameLengthPrefixedFourWayPacketFamilyOutput_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime
      encodeUnaryFrameLengthPrefixedFourWayPacketFamily id
      unaryFrameLengthPrefixedFourWayPacketFamilyOutput := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      unaryFrameLengthPrefixedFourWayPacketFamilyOutputRev_computableInPolyTime
      (reverse_computableInPolyTime (Γ := UnaryFrameSym))
  simpa [Function.comp_def] using Classical.choice composed

end CLRS.Chapter34.Turing.PolyBuilder


