-- Prove2me | Definitions.Def_PricingWithTips3DM_df340fab2c3612cc62392383
-- name    : PricingWithTips3DM_df340fab2c3612cc62392383
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T20:29:05.299055+00:00
-- url     : https://prove2.me/theorems/ecc80fae-f19f-4a4f-b1d8-1089502b8601
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameMarkedRowFieldReverseRuntime
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_a80e2831c8e90477e51de425
import Definitions.Def_PricingWithTips3DM_b8c03f33e84411dcd1343113
import Definitions.Def_PricingWithTips3DM_4901b5edb9039a7b71dab674
import Mathlib.Tactic
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Reversing unary fields inside marked rows: polynomial-time interface
-/

noncomputable section

namespace CLRS.Chapter34.Turing.PolyBuilder

private theorem fieldReverse_buildSteps_le (values : List Nat) :
    unaryFrameMarkedRowFieldReverseBuildSteps values ≤
      4 * (encodeUnaryFrame values).length := by
  induction values with
  | nil => rfl
  | cons value values ih =>
      simp only [unaryFrameMarkedRowFieldReverseBuildSteps]
      have hlength : (encodeUnaryFrame (value :: values)).length =
          value + 1 + (encodeUnaryFrame values).length := by
        simp [encodeUnaryFrame, encodeUnaryFrameBlock]
        omega
      rw [hlength]
      omega

private theorem fieldReverse_rowSteps_le (values : List Nat) :
    unaryFrameMarkedRowFieldReverseRowSteps values ≤
      6 * ((encodeUnaryFrame values).length + 1) := by
  unfold unaryFrameMarkedRowFieldReverseRowSteps
  have hbuild := fieldReverse_buildSteps_le values
  have hreverse : (encodeUnaryFrame values.reverse).length =
      (encodeUnaryFrame values).length := by
    simp only [encodeUnaryFrame_length, List.map_reverse, List.sum_reverse]
  rw [hreverse]
  omega

private theorem fieldReverse_steps_le_rows (rows : List (List Nat)) :
    unaryFrameMarkedRowFieldReverseSteps rows ≤
      6 * ((rows.map encodeUnaryFrame).flatMap
        (fun row => row ++ [UnaryFrameSym.frameEnd])).length + 2 := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      simp only [unaryFrameMarkedRowFieldReverseSteps, List.map_cons,
        List.flatMap_cons, List.length_append, List.length_cons,
        List.length_nil]
      have hrow := fieldReverse_rowSteps_le row
      omega

/-- The prepend-only first pass is linear in the complete marked source. -/
theorem unaryFrameMarkedRowFieldReverseSteps_le
    (family : UnaryFrameValueRowFamily) :
    unaryFrameMarkedRowFieldReverseSteps family.rows ≤
      6 * (encodeUnaryFrameValueRowFamily family).length + 2 := by
  simpa [encodeUnaryFrameValueRowFamily,
    UnaryFrameValueRowFamily.marked,
    encodeUnaryFrameMarkedRowFamily] using
      fieldReverse_steps_le_rows family.rows

/-- Concrete first pass producing the reverse target stream. -/
noncomputable def unaryFrameMarkedRowFieldReverseRev_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime encodeUnaryFrameValueRowFamily id
      (fun family : UnaryFrameValueRowFamily =>
        (unaryFrameMarkedRowFieldReverseStream family).reverse) where
  tm := compile unaryFrameMarkedRowFieldReverseRevProgram
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 6 * Polynomial.X + 2
  outputsFun := fun family => by
    have builderRun := unaryFrameMarkedRowFieldReverseRev_run family
    have compiledRun := compile_evalsToInTime
      unaryFrameMarkedRowFieldReverseRevProgram builderRun
    have htime := unaryFrameMarkedRowFieldReverseSteps_le family
    have machineRun : _root_.StateTransition.EvalsToInTime
        (compile unaryFrameMarkedRowFieldReverseRevProgram).step
        (_root_.Turing.initList
          (compile unaryFrameMarkedRowFieldReverseRevProgram)
          (encodeUnaryFrameValueRowFamily family))
        (some (_root_.Turing.haltList
          (compile unaryFrameMarkedRowFieldReverseRevProgram)
          (unaryFrameMarkedRowFieldReverseStream family).reverse))
        (unaryFrameMarkedRowFieldReverseSteps family.rows) := by
      simpa only [encodeCfg_initialCfg, encodeCfg_haltCfg] using compiledRun
    have htime' : unaryFrameMarkedRowFieldReverseSteps family.rows ≤
        (6 * Polynomial.X + 2).eval
          (encodeUnaryFrameValueRowFamily family).length := by
      simpa using htime
    have boundedRun : _root_.StateTransition.EvalsToInTime
        (compile unaryFrameMarkedRowFieldReverseRevProgram).step
        (_root_.Turing.initList
          (compile unaryFrameMarkedRowFieldReverseRevProgram)
          (encodeUnaryFrameValueRowFamily family))
        (some (_root_.Turing.haltList
          (compile unaryFrameMarkedRowFieldReverseRevProgram)
          (unaryFrameMarkedRowFieldReverseStream family).reverse))
        ((6 * Polynomial.X + 2).eval
          (encodeUnaryFrameValueRowFamily family).length) :=
      ⟨machineRun.toEvalsTo, machineRun.steps_le_m.trans htime'⟩
    simpa [_root_.Turing.TM2OutputsInTime, compile] using boundedRun

/-- A fixed polynomial-time TM2 reverses the unary-field order inside every
marked row and restores forward stream order. -/
noncomputable def unaryFrameMarkedRowFieldReverse_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime encodeUnaryFrameValueRowFamily id
      unaryFrameMarkedRowFieldReverseStream := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      unaryFrameMarkedRowFieldReverseRev_computableInPolyTime
      (reverse_computableInPolyTime (Γ := UnaryFrameSym))
  simpa [Function.comp_def] using Classical.choice composed

end CLRS.Chapter34.Turing.PolyBuilder


