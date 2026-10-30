-- Prove2me | Definitions.Def_OAIQ081S125
-- name    : OAIQ081S125
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T22:37:28.03447+00:00
-- url     : https://prove2.me/theorems/c5f9c1da-c567-498b-b9f5-d54de3dd2c85
-- title:
--   Definitions bundle OAIQ081S125 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 105 declarations of OpenAI's Lean: 92 definitions, 1 inductive type or structure and 12 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.nativeIndices`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceWitness.Generated`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.FromCounts.state`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.buildState`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.cacheCellState`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.Code`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.ExecutesIn`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.RelRowSpec`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.RelSourceSpec`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.RowSpec`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.appendSource`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.clear`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.copy`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.emitRow`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.evaluateRow`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.execute`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.executeModel`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.fiberBody`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.findOwner`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.finishRows`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.frameRow`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.initializeSource`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.ownerResult`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.push`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.readIndex`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.resetExecutor`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.rowBody`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.rowLoop`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.rowPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.rowsCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.stageScalarWork`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.transfer`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.unstageScalarWork`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.zeroRow`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.zeroRows`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.zeroSource`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceValuesProgram.CallbackRelation`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceValuesProgram.body`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceValuesProgram.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceValuesProgram.loop` and 53 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLog_LayoutProgramScalarCacheCell`, `SubexponentialSAT_SqrtLog_LayoutProgramScalarFromCountsPrimitives`, `SubexponentialSAT_SqrtLog_LayoutProgramSourceBankFrameInput`, `SubexponentialSAT_SqrtLog_LayoutProgramSourceWitness`, `SubexponentialSAT_SqrtLog_LayoutSourceRowsProgram`, `SubexponentialSAT_SqrtLog_LayoutSourceRowsProgramCore`, `SubexponentialSAT_SqrtLog_LayoutSourceRowsProgramInitializeLift`, `SubexponentialSAT_SqrtLog_LayoutSourceRowsProgramModel`, `SubexponentialSAT_SqrtLog_LayoutSourceRowsProgramStaging`, `SubexponentialSAT_SqrtLog_LayoutSourceRowsProgramZero`, `SubexponentialSAT_SqrtLog_LayoutSourceValuesProgramLoop`, `SubexponentialSAT_SqrtLog_LayoutSourceValuesProgramRelation`, `SubexponentialSAT_SqrtLog_LeafBranchProgram`, `SubexponentialSAT_SqrtLog_LeafHeadFactorsProgram`, `SubexponentialSAT_SqrtLog_LeafHeadFactorsProgramLoop`, `SubexponentialSAT_SqrtLog_LeafHeadFactorsProgramRun`, `SubexponentialSAT_SqrtLog_LeafHeadFactorsProgramTest`, `SubexponentialSAT_SqrtLog_LeafHeadSetupProgramAddress`, `SubexponentialSAT_SqrtLog_LeafHeadSetupProgramBoot`, `SubexponentialSAT_SqrtLog_LeafHeadSetupProgramBootRun`, `SubexponentialSAT_SqrtLog_LeafHeadSetupProgramMatrixRun`, `SubexponentialSAT_SqrtLog_LeafHeadSetupProgramNativeInputs`, `SubexponentialSAT_SqrtLog_LeafHeadSetupProgramSelection`, `SubexponentialSAT_SqrtLog_LeafHighContextProgramBase`, `SubexponentialSAT_SqrtLog_LeafPackingFiberBounds`, `SubexponentialSAT_SqrtLog_LeafParametersProgramNative`, `SubexponentialSAT_SqrtLog_LeafProgramHashParameters`, `SubexponentialSAT_SqrtLog_LeafRingSetupProgramNative`, `SubexponentialSAT_SqrtLog_LeafStatisticsSemanticsTransport`, `SubexponentialSAT_SqrtLog_MomentsReadoutProgramState`, `SubexponentialSAT_SqrtLog_PolynomialExecutorProgram`, `SubexponentialSAT_SqrtLog_PolynomialExecutorProgramBasic`, `SubexponentialSAT_SqrtLog_PolynomialExecutorProgramFlat`, `SubexponentialSAT_SqrtLog_PolynomialExecutorProgramServices`, `SubexponentialSAT_SqrtLog_ProducedQueryRankMagnitude`, `SubexponentialSAT_Subexp_BasisTransposePlanProgram`, `SubexponentialSAT_Subexp_PackingLeftoverEmitter`, `SubexponentialSAT_Subexp_PackingLeftovers`, `SubexponentialSAT_Subexp_UniversalRowDataProgram`, `SubexponentialSAT_Subexp_UniversalRowEmitCall`, `SubexponentialSAT_Subexp_UniversalRowExecution`, `SubexponentialSAT_Subexp_UniversalRowSourceProgram`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S100`, `OAIQ081S101`, `OAIQ081S102`, `OAIQ081S106`, `OAIQ081S107`, `OAIQ081S108` and `OAIQ081S109` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S144`, `OAIQ081S145`, `OAIQ081S146`, `OAIQ081S148` and `OAIQ081S151`; the statements `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.FromCounts.numerator_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.cacheBuildLoop_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceExpression.literal_length_le_sourceLengthBound`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceExpression.typed_row_contract`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.findOwner_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.initializeSource_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.zeroRows_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.matrixBase_fiberReady`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHighContextProgram.Local.mask_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.evaluate_correct`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.evaluate_full` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.flat_run`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.FromCounts.numerator_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.cacheBuildLoop_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceExpression.typed_row_contract`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.findOwner_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.initializeSource_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.zeroRows_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.matrixBase_fiberReady`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHighContextProgram.Local.mask_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.evaluate_correct`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.evaluate_full` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.flat_run`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S100
import Definitions.Def_OAIQ081S101
import Definitions.Def_OAIQ081S102
import Definitions.Def_OAIQ081S106
import Definitions.Def_OAIQ081S107
import Definitions.Def_OAIQ081S108
import Definitions.Def_OAIQ081S109

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramScalarCacheCell
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The unsigned cache recurrence is executed by a one-bit shift followed by
the original finite little-endian adder. Its representation growth is linear
in the number of cells; no canonical-word assumption is used. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgramScalar

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.BinaryArithmetic
open SubexponentialSAT.SqrtLog.RowSelectionProgram

def cacheCellState (regs : Fin 8 → Bool) (prior old : List Bool) : State 8 3 :=
  ⟨regs,BinaryPrograms.Add.stackState prior old []⟩

end SubexponentialSAT.SqrtLog.LayoutProgramScalar

/-! One complete cache-row transform, including record parsing and preserving
emission of every newly computed value. -/

/-! Complete reusable cache pass: read one encoded row, compute and emit its
new row, append the end marker, reverse the output, and clear the carry. -/

/-! The number of coefficient-cache rows is runtime unary data. This fixed
loop invokes the complete paid row pass and preserves the current encoded row.
-/

/-! The physical unsigned cache computes the original coefficient recurrence's
natural magnitudes, in ascending degree order. -/

/-! A fixed loop builds the initial all-one cache row from a runtime unary
length. The constant program contains one record, independent of that length. -/

/-! One fixed program builds the complete unsigned H cache from the unary
runtime parameters A and R. No coefficient or initial cache is free input. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgramScalar

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SqrtLog.RowSelectionProgram

def buildState (regs : Fin 8 → Bool) (a r queue : List Bool) : BuildData :=
  ⟨regs,fun j => if j = 15 then queue else if j = 17 then a else if j = 18 then r else []⟩

end SubexponentialSAT.SqrtLog.LayoutProgramScalar

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramScalarFromCountsPrimitives
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutProgramScalar.FromCounts

attribute [local simp] Fin.coe_ofNat_eq_mod

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls RowSelectionProgram

def state (c : Saved) (regs : Fin 9 → Bool)
    (unchanged h n rc ac bp bn : List Bool) (result : WordPair) : Data :=
  ⟨regs,![c.hp,c.hn,c.width,c.power.1,c.power.2,c.r,c.a,unchanged,h,n,rc,ac,bp,bn,
    [],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],result.1,result.2,[]]⟩

end SubexponentialSAT.SqrtLog.LayoutProgramScalar.FromCounts

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_BasisTransposePlanProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Physical transpose read-plan generation

Two unary countdowns visit columns and rows in decreasing order. Each visit
constructs the unary physical index by repeated copying and emits one actual
framed record. Prepending these visits produces the increasing transpose
read order directly. All counters are runtime stacks and the code is fixed.
-/

namespace SubexponentialSAT.Subexp.BasisTransposePlanProgram

open BitProgram StructuredCalls

def ports (counter : Fin 7) : UnaryForPrograms.Ports 3 7 := ⟨counter, 0, 1⟩

end SubexponentialSAT.Subexp.BasisTransposePlanProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingLeftoverEmitter
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual emission and covered-key lookup for the leftover packing pass. -/
namespace SubexponentialSAT.Subexp.PackingLeftoverEmitter

open BitProgram StructuredCalls MatrixProgramSupport

theorem command_eval_exact (vertex rank address storage metadata addresses : List Bool)
    (regs : Fin 8 → Bool) :
    ∃ rf, Eval command (commandCost vertex rank address)
      (state regs vertex rank address storage metadata addresses)
      (state rf [] (true::rank) (true::address) (storageOutput vertex storage)
        (metadataOutput vertex rank metadata) (addressOutput vertex address addresses)) := by
  let a0 := workState regs vertex rank address storage metadata addresses [] [] []
  obtain ⟨d1,h1,s1⟩ := copy_eval (0 : Fin 9) 7 6 (by decide) (by decide) (by decide) a0 rfl
  let a1 := workState d1.regs
    vertex rank address storage metadata addresses [] vertex []
  have e1 : d1 = a1 := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    rw [s1]
    funext j
    fin_cases j <;> simp [a0,workState,StackRoutines.copyStacks]
  rw [e1] at h1
  obtain ⟨d2,h2,s2⟩ := emitFrame_eval (7 : Fin 9) 8 6 (by decide) (by decide) (by decide) a1 rfl
  let a2 := workState d2.regs
    vertex rank address storage metadata addresses [] [] (Encoding.frame vertex)
  have e2 : d2 = a2 := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    rw [s2]
    funext j
    fin_cases j <;> simp [a1,workState]
  rw [e2] at h2
  have h3 := TupleProgram.pushConst_eval (8 : Fin 9) (0 : Fin 8) true a2
  let a3 := workState (Function.update a2.regs 0 true)
    vertex rank address storage metadata addresses [] [] (true :: (Encoding.frame vertex))
  have e3 : TupleProgram.pushedState 8 0 true a2 = a3 := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext j
    fin_cases j <;> simp [a2,workState]
  rw [e3] at h3
  obtain ⟨d4,h4,s4⟩ := transfer_eval (8 : Fin 9) 3 (by decide) a3
  let a4 := workState d4.regs
    vertex rank address ((true :: (Encoding.frame vertex)).reverse ++ storage) metadata addresses [] [] []
  have e4 : d4 = a4 := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    rw [s4]
    funext j
    fin_cases j <;> simp [a3,workState,StackRoutines.transferStacks]
  rw [e4] at h4
  obtain ⟨d5,h5,s5⟩ := copy_eval (1 : Fin 9) 7 6 (by decide) (by decide) (by decide) a4 rfl
  let a5 := workState d5.regs
    vertex rank address ((true :: (Encoding.frame vertex)).reverse ++ storage) metadata addresses [] rank []
  have e5 : d5 = a5 := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    rw [s5]
    funext j
    fin_cases j <;> simp [a4,workState,StackRoutines.copyStacks]
  rw [e5] at h5
  obtain ⟨d6,h6,s6⟩ := emitFrame_eval (7 : Fin 9) 8 6 (by decide) (by decide) (by decide) a5 rfl
  let a6 := workState d6.regs
    vertex rank address ((true :: (Encoding.frame vertex)).reverse ++ storage) metadata addresses [] [] (Encoding.frame rank)
  have e6 : d6 = a6 := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    rw [s6]
    funext j
    fin_cases j <;> simp [a5,workState]
  rw [e6] at h6
  have h7 := TupleProgram.pushConst_eval (8 : Fin 9) (0 : Fin 8) false a6
  let a7 := workState (Function.update a6.regs 0 false)
    vertex rank address ((true :: (Encoding.frame vertex)).reverse ++ storage) metadata addresses [] [] (false :: (Encoding.frame rank))
  have e7 : TupleProgram.pushedState 8 0 false a6 = a7 := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext j
    fin_cases j <;> simp [a6,workState]
  rw [e7] at h7
  obtain ⟨d8,h8,s8⟩ := emitFrame_eval (8 : Fin 9) 4 6 (by decide) (by decide) (by decide) a7 rfl
  let a8 := workState d8.regs
    vertex rank address ((true :: (Encoding.frame vertex)).reverse ++ storage) (Encoding.frame (false :: (Encoding.frame rank)) ++ metadata) addresses [] [] []
  have e8 : d8 = a8 := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    rw [s8]
    funext j
    fin_cases j <;> simp [a7,workState]
  rw [e8] at h8
  obtain ⟨d9,h9,s9⟩ := copy_eval (0 : Fin 9) 7 6 (by decide) (by decide) (by decide) a8 rfl
  let a9 := workState d9.regs
    vertex rank address ((true :: (Encoding.frame vertex)).reverse ++ storage) (Encoding.frame (false :: (Encoding.frame rank)) ++ metadata) addresses [] vertex []
  have e9 : d9 = a9 := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    rw [s9]
    funext j
    fin_cases j <;> simp [a8,workState,StackRoutines.copyStacks]
  rw [e9] at h9
  obtain ⟨d10,h10,s10⟩ := emitFrame_eval (7 : Fin 9) 4 6 (by decide) (by decide) (by decide) a9 rfl
  let a10 := workState d10.regs
    vertex rank address ((true :: (Encoding.frame vertex)).reverse ++ storage) (Encoding.frame vertex ++ (Encoding.frame (false :: (Encoding.frame rank)) ++ metadata)) addresses [] [] []
  have e10 : d10 = a10 := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    rw [s10]
    funext j
    fin_cases j <;> simp [a9,workState]
  rw [e10] at h10
  obtain ⟨d11,h11,s11⟩ := copy_eval (2 : Fin 9) 7 6 (by decide) (by decide) (by decide) a10 rfl
  let a11 := workState d11.regs
    vertex rank address ((true :: (Encoding.frame vertex)).reverse ++ storage) (Encoding.frame vertex ++ (Encoding.frame (false :: (Encoding.frame rank)) ++ metadata)) addresses [] address []
  have e11 : d11 = a11 := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    rw [s11]
    funext j
    fin_cases j <;> simp [a10,workState,StackRoutines.copyStacks]
  rw [e11] at h11
  obtain ⟨d12,h12,s12⟩ := emitFrame_eval (7 : Fin 9) 5 6 (by decide) (by decide) (by decide) a11 rfl
  let a12 := workState d12.regs
    vertex rank address ((true :: (Encoding.frame vertex)).reverse ++ storage) (Encoding.frame vertex ++ (Encoding.frame (false :: (Encoding.frame rank)) ++ metadata)) (Encoding.frame address ++ addresses) [] [] []
  have e12 : d12 = a12 := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    rw [s12]
    funext j
    fin_cases j <;> simp [a11,workState]
  rw [e12] at h12
  obtain ⟨d13,h13,s13⟩ := emitFrame_eval (0 : Fin 9) 5 6 (by decide) (by decide) (by decide) a12 rfl
  let a13 := workState d13.regs
    [] rank address ((true :: (Encoding.frame vertex)).reverse ++ storage) (Encoding.frame vertex ++ (Encoding.frame (false :: (Encoding.frame rank)) ++ metadata)) (Encoding.frame vertex ++ (Encoding.frame address ++ addresses)) [] [] []
  have e13 : d13 = a13 := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    rw [s13]
    funext j
    fin_cases j <;> simp [a12,workState]
  rw [e13] at h13
  have h14 := TupleProgram.pushConst_eval (1 : Fin 9) (0 : Fin 8) true a13
  let a14 := workState (Function.update a13.regs 0 true)
    [] (true :: rank) address ((true :: (Encoding.frame vertex)).reverse ++ storage) (Encoding.frame vertex ++ (Encoding.frame (false :: (Encoding.frame rank)) ++ metadata)) (Encoding.frame vertex ++ (Encoding.frame address ++ addresses)) [] [] []
  have e14 : TupleProgram.pushedState 1 0 true a13 = a14 := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext j
    fin_cases j <;> simp [a13,workState]
  rw [e14] at h14
  have h15 := TupleProgram.pushConst_eval (2 : Fin 9) (0 : Fin 8) true a14
  let a15 := workState (Function.update a14.regs 0 true)
    [] (true :: rank) (true :: address) ((true :: (Encoding.frame vertex)).reverse ++ storage) (Encoding.frame vertex ++ (Encoding.frame (false :: (Encoding.frame rank)) ++ metadata)) (Encoding.frame vertex ++ (Encoding.frame address ++ addresses)) [] [] []
  have e15 : TupleProgram.pushedState 2 0 true a14 = a15 := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext j
    fin_cases j <;> simp [a14,workState]
  rw [e15] at h15
  have hrun := h1.seq (h2.seq (h3.seq (h4.seq (h5.seq (h6.seq (h7.seq (h8.seq (h9.seq (h10.seq (h11.seq (h12.seq (h13.seq (h14.seq (h15.seq ((.base (.skip a15)))))))))))))))))
  have hcost : (7*(a0.stacks 0).length+5)+((8*(a1.stacks 7).length+8)+(2+((3*(a3.stacks 8).length+3)+((7*(a4.stacks 1).length+5)+((8*(a5.stacks 7).length+8)+(2+((8*(a7.stacks 8).length+8)+((7*(a8.stacks 0).length+5)+((8*(a9.stacks 7).length+8)+((7*(a10.stacks 2).length+5)+((8*(a11.stacks 7).length+8)+((8*(a12.stacks 0).length+8)+(2+(2+(0))))))))))))))) = commandCost vertex rank address := by
    simp [a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,workState,commandCost,Encoding.length_frame]
    ring
  rw [hcost] at hrun
  exact ⟨a15.regs,hrun⟩

theorem program_trace (vertex rank address storage metadata addresses : List Bool)
    (regs : Fin 8 → Bool) :
    ∃ rf, Trace program (commandCost vertex rank address+1)
      ((state regs vertex rank address storage metadata addresses).withPC (some program.entry))
      ((state rf [] (true::rank) (true::address) (storageOutput vertex storage)
        (metadataOutput vertex rank metadata) (addressOutput vertex address addresses)).withPC none) := by
  obtain ⟨rf,h⟩ := command_eval_exact vertex rank address storage metadata addresses regs
  exact ⟨rf,compiled_halt_trace h 0 3⟩

end SubexponentialSAT.Subexp.PackingLeftoverEmitter


end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingLeftovers
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Actual leftover packing pass

The immutable covered table is searched for every original vertex. A found
vertex is skipped. A missing vertex is appended to reversed storage and both
lookup tables, with actual unary rank/address increments.
-/
namespace SubexponentialSAT.Subexp.PackingLeftovers

open BitProgram StructuredCalls MatrixProgramSupport

theorem emit_eval (regs : Fin 8 → Bool)
    (covered source rank address storage metadata addresses vertex : List Bool) :
    ∃ rf, Eval emitCall (PackingLeftoverEmitter.commandCost vertex rank address+1)
      (data regs [] [] covered source [] rank address storage metadata addresses vertex)
      (data rf [] [] covered source [] (true::rank) (true::address)
        (PackingLeftoverEmitter.storageOutput vertex storage)
        (PackingLeftoverEmitter.metadataOutput vertex rank metadata)
        (PackingLeftoverEmitter.addressOutput vertex address addresses) []) := by
  let a := data regs [] [] covered source [] rank address storage metadata addresses vertex
  obtain ⟨rf,ht⟩ := PackingLeftoverEmitter.program_trace vertex rank address storage metadata addresses regs
  let b := data rf [] [] covered source [] (true::rank) (true::address)
    (PackingLeftoverEmitter.storageOutput vertex storage)
    (PackingLeftoverEmitter.metadataOutput vertex rank metadata)
    (PackingLeftoverEmitter.addressOutput vertex address addresses) []
  have ha : embedState id emitterStacks a
      (PackingLeftoverEmitter.state regs vertex rank address storage metadata addresses) = a := by
    apply SelectorMapProgram.embed_eq _ _ Function.injective_id emitterStacks_injective
    · intros; rfl
    · intro i
      fin_cases i <;> rfl
    · intros; rfl
    · intros; rfl
  have hb : embedState id emitterStacks a
      (PackingLeftoverEmitter.state rf [] (true::rank) (true::address)
        (PackingLeftoverEmitter.storageOutput vertex storage)
        (PackingLeftoverEmitter.metadataOutput vertex rank metadata)
        (PackingLeftoverEmitter.addressOutput vertex address addresses)) = b := by
    apply SelectorMapProgram.embed_eq _ _ Function.injective_id emitterStacks_injective
    · intros; rfl
    · intro i
      fin_cases i <;> rfl
    · intro i hi
      exact (hi ⟨i,rfl⟩).elim
    · intro i hi
      have h15 : i ≠ 15 := fun h => hi ⟨0,h.symm⟩
      have h10 : i ≠ 10 := fun h => hi ⟨1,h.symm⟩
      have h11 : i ≠ 11 := fun h => hi ⟨2,h.symm⟩
      have h12 : i ≠ 12 := fun h => hi ⟨3,h.symm⟩
      have h13 : i ≠ 13 := fun h => hi ⟨4,h.symm⟩
      have h14 : i ≠ 14 := fun h => hi ⟨5,h.symm⟩
      simp only [a,b,data_stacks,ite_eq_right h15,ite_eq_right h10,ite_eq_right h11,ite_eq_right h12,ite_eq_right h13,ite_eq_right h14]
  have he := eval_call_lifted PackingLeftoverEmitter.program id emitterStacks a
    Function.injective_id emitterStacks_injective ht
  rw [ha,hb] at he
  exact ⟨rf,he⟩

set_option maxHeartbeats 1600000 in
theorem callback_eval (records : Records) (v : ℕ) (s : Snapshot)
    (regs : Fin 8 → Bool) (source : List Bool) :
    ∃ (n : ℕ) (rf : Fin 8 → Bool), n ≤ callbackCost records v s ∧
      Eval callback n (configured regs records source (unary v) s [])
        (configured rf records source [] (advance records s v) []) ∧
      rf 5 = false ∧ rf 6 = true ∧ rf 7 = false := by
  let a0 := configured regs records source (unary v) s []
  obtain ⟨r1,h1,hs1⟩ := transfer_eval (8 : Fin 18) 15 (by decide) a0
  let a1 := configured r1.regs records source [] s (unary v)
  have he1 : r1=a1 := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    rw [hs1]
    funext i
    fin_cases i <;> simp [a0,configured,data,StackRoutines.transferStacks]
  rw [he1] at h1
  obtain ⟨r2,h2,hs2⟩ := copy_eval (6 : Fin 18) 0 9 (by decide) (by decide) (by decide) a1 rfl
  let a2 := data r2.regs (SelectorProgram.rawRecords records) []
    (SelectorProgram.rawRecords records) source [] (unary s.rank) (unary s.address)
    s.storage s.metadata s.addresses (unary v)
  have he2 : r2=a2 := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    rw [hs2]
    funext i
    fin_cases i <;> simp [a1,configured,data,StackRoutines.copyStacks]
  rw [he2] at h2
  obtain ⟨r3,h3,hs3⟩ := copy_eval (15 : Fin 18) 2 9 (by decide) (by decide) (by decide) a2 rfl
  let a3 := data r3.regs (SelectorProgram.rawRecords records) (unary v)
    (SelectorProgram.rawRecords records) source [] (unary s.rank) (unary s.address)
    s.storage s.metadata s.addresses (unary v)
  have he3 : r3=a3 := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    rw [hs3]
    funext i
    fin_cases i <;> simp [a2,data,StackRoutines.copyStacks]
  rw [he3] at h3
  obtain ⟨nq,hnq,rq,hq,hflag⟩ := query_eval records (unary v) r3.regs source []
    (unary s.rank) (unary s.address) s.storage s.metadata s.addresses (unary v)
  simp only [List.reverse_replicate] at hq
  let a4 := configured rq records source [] s (unary v)
  have hbranch : ∃ nb rb, nb ≤ 44*v+31*s.rank+15*s.address+103 ∧
      Eval (.ite 4 clearVertex emitCall) nb a4
        (configured rb records source [] (advance records s v) []) := by
    cases hc : covered records v with
    | true =>
        have hf : rq 4 = true := hflag.trans hc
        have he := clearVertex_eval rq (SelectorProgram.rawRecords records) source
          (unary s.rank) (unary s.address) s.storage s.metadata s.addresses (unary v)
        refine ⟨2*v+4,readRegs rq 0 1 none,by omega,?_⟩
        simpa [a4,configured,advance,hc] using Eval.ite_true hf he
    | false =>
        have hf : rq 4 = false := hflag.trans hc
        obtain ⟨rf,he⟩ := emit_eval rq (SelectorProgram.rawRecords records) source
          (unary s.rank) (unary s.address) s.storage s.metadata s.addresses (unary v)
        refine ⟨44*v+31*s.rank+15*s.address+103,rf,le_rfl,?_⟩
        simpa [a4,configured,advance,hc,appendVertex,PackingLeftoverEmitter.commandCost,
          List.replicate_succ,Nat.add_assoc] using Eval.ite_false hf he
  obtain ⟨nb,rb,hnb,hb⟩ := hbranch
  have hr := resetParser_eval (configured rb records source [] (advance records s v) [])
  have hrun := h1.seq (h2.seq (h3.seq (hq.seq (hb.seq hr))))
  refine ⟨_,parserRegs rb false true false,?_,hrun,?_,?_,?_⟩
  · change (3*(unary v).length+3)+((7*(SelectorProgram.rawRecords records).length+5)+
      ((7*(unary v).length+5)+(nq+(nb+3)))) ≤ callbackCost records v s
    simp only [List.length_replicate]
    dsimp [PackingCoveredQuery.budget] at hnq
    simp only [List.length_replicate] at hnq
    dsimp [callbackCost]
    omega
  · simp [parserRegs]
  · simp [parserRegs]
  · simp [parserRegs]

theorem loop_eval (records : Records) (vertices : List ℕ) (s : Snapshot)
    (regs : Fin 8 → Bool) (suffix : List Bool) :
    ∃ (n : ℕ) (rf : Fin 8 → Bool), n ≤ 1+iterationCost records vertices s ∧
      Eval (RecordPrograms.loop ports callback) n
        (RecordPrograms.afterTag ports (configured regs records [] [] s [])
          (vertices.map unary) suffix)
        (RecordPrograms.state ports
          (configured rf records [] [] (vertices.foldl (advance records) s) [])
          false true false suffix []) := by
  induction vertices generalizing s regs with
  | nil =>
      refine ⟨1,regs,by simp [iterationCost],?_⟩
      simpa only [List.map_nil,RecordPrograms.afterTag,List.foldl_nil] using
        (Eval.while_false (body := RecordPrograms.body ports callback)
          (a := RecordPrograms.state ports (configured regs records [] [] s [])
            false true false suffix []) (by simp))
  | cons v vertices ih =>
      let a := configured regs records [] [] s []
      let tail := Encoding.encodeList id (vertices.map unary) ++ suffix
      have hreader : Eval (RecordPrograms.reader ports) (6*v+4)
          (RecordPrograms.afterTag ports a ((v::vertices).map unary) suffix)
          (RecordPrograms.state ports a false true false tail (unary v)) := by
        simpa only [List.map_cons,RecordPrograms.afterTag,List.append_nil,
          List.length_replicate,List.reverse_replicate] using
          RecordPrograms.reader_eval ports a (unary v) tail [] true true false
      obtain ⟨nc,rc,hnc,hc,h5,h6,h7⟩ := callback_eval records v s
        (parserRegs regs false true false) tail
      let b := configured rc records [] [] (advance records s v) []
      have hcb : Eval callback nc
          (RecordPrograms.state ports a false true false tail (unary v))
          (RecordPrograms.state ports b false true false tail []) := by
        simpa only [a,b,parser_state,parserRegs_self rc false true false h5 h6 h7] using hc
      have hbranch : Eval
          (.ite ports.found (RecordPrograms.atom (.set ports.tag false))
            (RecordPrograms.atom (.pop ports.source ports.tag ports.present))) 2
          (RecordPrograms.state ports b false true false tail [])
          (RecordPrograms.afterTag ports b (vertices.map unary) suffix) := by
        apply Eval.ite_false (by simp)
        exact RecordPrograms.pop_list_eval ports b (vertices.map unary) suffix false true
      obtain ⟨nr,rf,hnr,hr⟩ := ih (advance records s v) rc
      have hrun := Eval.while_true
        (show (RecordPrograms.afterTag ports a ((v::vertices).map unary) suffix).regs ports.tag=true by
          simp [RecordPrograms.afterTag]) (hreader.seq (hcb.seq hbranch)) hr
      refine ⟨6*v+4+(nc+2)+nr+1,rf,?_,?_⟩
      · simp only [iterationCost]
        omega
      · simpa only [RecordPrograms.loop,RecordPrograms.body,a,b,List.foldl_cons] using hrun

/-- Complete scan of actual original-vertex records. The saved covered table
is unchanged, and all work ports are cleared. -/
theorem command_eval (records : Records) (vertices : List ℕ) (s : Snapshot)
    (regs : Fin 8 → Bool) (suffix : List Bool) :
    ∃ (n : ℕ) (rf : Fin 8 → Bool), n+1 ≤ traceCost records vertices s ∧
      Eval command n
        (state regs (SelectorProgram.rawRecords records)
          (ProgramEncoding.encodeRecords (vertices.map unary) ++ suffix)
          (unary s.rank) (unary s.address) s.storage s.metadata s.addresses)
        (state rf (SelectorProgram.rawRecords records) suffix
          (unary (vertices.foldl (advance records) s).rank)
          (unary (vertices.foldl (advance records) s).address)
          (vertices.foldl (advance records) s).storage
          (vertices.foldl (advance records) s).metadata
          (vertices.foldl (advance records) s).addresses) := by
  let a := configured regs records [] [] s []
  obtain ⟨n,rf,hn,he⟩ := loop_eval records vertices s regs suffix
  have hset := RecordPrograms.set_found_eval ports a (regs 5) (regs 6) (regs 7) false
    (ProgramEncoding.encodeRecords (vertices.map unary) ++ suffix) []
  have hpop := RecordPrograms.pop_list_eval ports a (vertices.map unary) suffix (regs 5) (regs 6)
  have hrun := hset.seq (hpop.seq he)
  rw [parser_state, parser_state] at hrun
  refine ⟨1+(1+n),parserRegs rf false true false,by dsimp [traceCost]; omega,?_⟩
  simpa only [command,RecordPrograms.iterate,a,configured,data,state,
    parserRegs_self regs (regs 5) (regs 6) (regs 7) rfl rfl rfl] using hrun

theorem program_trace (records : Records) (vertices : List ℕ) (s : Snapshot)
    (regs : Fin 8 → Bool) (suffix : List Bool) :
    ∃ (n : ℕ) (rf : Fin 8 → Bool), n ≤ traceCost records vertices s ∧
      Trace program n
        ((state regs (SelectorProgram.rawRecords records)
          (ProgramEncoding.encodeRecords (vertices.map unary) ++ suffix)
          (unary s.rank) (unary s.address) s.storage s.metadata s.addresses).withPC (some program.entry))
        ((state rf (SelectorProgram.rawRecords records) suffix
          (unary (vertices.foldl (advance records) s).rank)
          (unary (vertices.foldl (advance records) s).address)
          (vertices.foldl (advance records) s).storage
          (vertices.foldl (advance records) s).metadata
          (vertices.foldl (advance records) s).addresses).withPC none) := by
  obtain ⟨n,rf,hn,he⟩ := command_eval records vertices s regs suffix
  exact ⟨n+1,rf,hn,compiled_halt_trace he 7 12⟩

end SubexponentialSAT.Subexp.PackingLeftovers

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_UniversalRowDataProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Assemble a complete raw row from runtime scalar/cache tables. -/

namespace SubexponentialSAT.Subexp.UniversalRowDataProgram

open BitProgram StructuredCalls StackRoutines
open UniversalRowGather (Data Word)
open UniversalRowLoop (Tables Valid ready)
open UniversalRowFactorLoop (indexWord)

abbrev active : Cmd 8 32 :=
  .seq (.call (copyProgram 28 17 15 (0 : Fin 8) 1)) UniversalRowLoop.loop

abbrev command : Cmd 8 32 :=
  .seq UniversalRowGuard.command
    (.seq (TupleProgram.pushConst 31 0 false)
      (.seq (.ite 7 active (.base .skip)) UniversalRowTermFraming.row))

end SubexponentialSAT.Subexp.UniversalRowDataProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_UniversalRowExecution
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed nested source emitter and its actual byte-level execution bound. -/
namespace SubexponentialSAT.Subexp.UniversalRowProgram

open BitProgram StructuredCalls
open SubexpKernelControl (Word Accumulator pushWord operator operators counterPort popTag unframe emitFramedLiteral emitLiteral
  emitOperator countOne drain scan )

local infixr:60 " ;; " => Cmd.seq

abbrev rowBody : Cmd 3 8 :=
  emitFramedLiteral ;; scan termBody ;; emitLiteral 1 ;; drain 7 false ;; emitOperator false

abbrev command : Cmd 3 8 :=
  .base (.atom (.set 2 true)) ;; prepareX ;; rowBody ;; clearX ;;
    SubexpKernelControl.transferOutput ;; .base (.atom (.set 2 false))

abbrev program : Program 3 8 (size command + 1) := compiled command 0 0

end SubexponentialSAT.Subexp.UniversalRowProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_UniversalRowEmitCall
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A framed call to the actual row source emitter inside the row workspace. -/

namespace SubexponentialSAT.Subexp.UniversalRowEmitCall

open BitProgram StructuredCalls
open UniversalRowProgram (Row)
open SubexpKernelControl (Word)

abbrev emit : Cmd 8 32 :=
  .call (ProgramLinking.liftProgram UniversalRowProgram.program regs stackMap)

abbrev command : Cmd 8 32 := .seq reset emit

end SubexponentialSAT.Subexp.UniversalRowEmitCall

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_UniversalRowSourceProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! One fixed producer from packed scalar/cache tables to row postfix bytes. -/

namespace SubexponentialSAT.Subexp.UniversalRowSourceProgram

open BitProgram StructuredCalls
open UniversalRowGather (Data Word)
open UniversalRowLoop (Tables Valid ready)

abbrev command : Cmd 8 32 :=
  .seq UniversalRowDataProgram.command UniversalRowEmitCall.command

abbrev program : Program 8 32 (size command + 1) := compiled command 31 31

end SubexponentialSAT.Subexp.UniversalRowSourceProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourceValuesProgramLoop
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed control that constructs an ordered scalar table. The callback is an
actual finite command with a measured execution contract. Runtime unary node
indices and counters do not change the command. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceValuesProgram

open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open _root_.OAI.Algorithms.SubexponentialSAT.SubexpPolynomialServiceControl (transfer transfer_run)

attribute [local simp] Fin.coe_ofNat_eq_mod

def ports : UnaryForPrograms.Ports 16 256 := ⟨64,14,15⟩

def body (callback : Code) : Code :=
  .seq callback (.seq (transfer 255 65) advance)
def loop (callback : Code) : Code := UnaryForPrograms.forCmd ports (body callback)

def command (callback : Code) : Code :=
  .seq (copy 22 64) (.seq (loop callback) (.seq (clear 37) (transfer 65 67)))
def program (callback : Code) := compiled (command callback) 22 67

end SubexponentialSAT.SqrtLog.LayoutSourceValuesProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourceValuesProgramRelation
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Relational refinement of the same table builder. Each scalar may have any
correct byte representation; all table entries are obtained from executions. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceValuesProgram

open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open _root_.OAI.Algorithms.SubexponentialSAT.SubexpPolynomialServiceControl (transfer transfer_run)
attribute [local simp] Fin.coe_ofNat_eq_mod

/-- Every observed callback result is a measured scalar computation. -/
def CallbackRelation (callback : Code) (base : Store)
    (valid : ℕ → List Bool → Prop) (Q K W : ℕ) : Prop :=
  ∀ j, j < Q → ∀ remaining acc regs, ∃ n rf word,
    n ≤ K ∧ word.length = W ∧ valid j word ∧
    Eval callback n (⟨regs,loopState base j remaining acc⟩ : Data)
      (⟨rf,Function.update (loopState base j remaining acc) 255 word⟩ : Data)

end SubexponentialSAT.SqrtLog.LayoutSourceValuesProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramSourceBankFrameInput
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The actual scalar producer's numerator input already contains precisely
all low type-extractor inputs. No second pre-expanded input is assumed. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank
attribute [local simp] Fin.coe_ofNat_eq_mod
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes

def nativeIndices {r Q : ℕ} (u y : UniversalType r Q 1) : List Bool :=
  ProgramEncoding.encodeRecords (MismatchPlanProgram.indexRecords (nativePositions u y).reverse)

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PolynomialExecutorProgramBasic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Executable coefficient-array meaning of the row postfix interpreter.
Literal padding and all arithmetic operate on stored coefficient words. -/
namespace SubexponentialSAT.SqrtLog.PolynomialExecutorProgram
open SubexponentialSAT.SubexpSymbolicCost

abbrev Coeff (B d : ℕ) := DensePolynomialProgram.Coeff B d

noncomputable def meaning {C R : Type*} [CommRing R] (ops : RepresentedRing C R)
    (P : List C) : Polynomial R := SubexponentialSAT.PolynomialAlgorithm.denote (P.map ops.decode)

end SubexponentialSAT.SqrtLog.PolynomialExecutorProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramSourceWitness
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A complete typed witness for one actual universal source word: compiler
bytes, full polynomial meaning, degree, and physical byte length. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.SourceWitness
open SubexponentialSAT.Subexp SubexponentialSAT.SubexpSymbolicCost SubexponentialSAT.MulticolorTypes
open SubexponentialSAT.SubexpRepresentedRows SubexponentialSAT.SubexpRowInterpolation
open PolynomialExecutorProgram

variable {B d r Q : ℕ} {O : Type*} [CommRing O]

def Generated (ops : RepresentedRing (Coeff B d) O) (R L : ℕ)
    (value : Polynomial O) (bytes : List Bool) : Prop :=
  ∃ e : Algorithm.Expr (List (Coeff B d)),
    bytes=SubexpPostfixControl.serializeCode DensePolynomialProgram.encode e.compile ∧
    (e.map (meaning ops)).eval=value ∧
    ((e.map (meaning ops)).eval).natDegree ≤ R ∧ bytes.length ≤ L

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceWitness

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourceRowsProgramCore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native framing and postfix accumulation for complete source rows. The
local bank is relocated as a whole by the leaf controller. No polynomial
value is an instruction or an input to these controllers. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT BitProgram StructuredCalls

abbrev Code := Cmd 16 340

def ExecutesIn (c : Code) (K : ℕ) (s t : Store) : Prop :=
  ∀ regs, ∃ n rf, n ≤ K ∧ Eval c n (⟨regs,s⟩ : Data) (⟨rf,t⟩ : Data)

def transfer (src dst : Fin 340) : Code := .call (StackRoutines.transferProgram src dst 0 1)
def clear (src : Fin 340) : Code := .call (StackRoutines.clearProgram src 0 1)
def copy (src dst : Fin 340) : Code := .call (StackRoutines.copyProgram src dst 339 0 1)
def push (dst : Fin 340) (b : Bool) : Code := Subexp.TupleProgram.pushConst dst 0 b

/-- 329 is the remaining fiber, 305 the current incidence column. -/
def readIndex : Code := .call (RowSelectionProgramTupleCheck.Read.program 329 305 0 1)

/-- The reverse accumulator333 receives a genuine source followed by add. -/
def appendSource : Code := .seq (transfer 287 333) (.seq (push 333 true) (push 333 false))

def zeroSource : Code := .seq (push 333 false) (push 333 false)

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourceRowsProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Complete finite controllers for source fiber sums and ambient source-row
serialization. Parameters are actual finite programs with paid contracts. -/

/-! A runtime owner-fiber fold of actual serialized polynomial sources. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT BitProgram StructuredCalls

attribute [local simp] Fin.coe_ofNat_eq_mod

def fiberBody (source : Code) : Code :=
  .seq readIndex (.seq source (.seq appendSource (clear 305)))

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT BitProgram StructuredCalls

def findOwner : Code := .call (ProgramLinking.liftProgram
  LayoutOwnerFiberProgram.program ownerRegisters ownerStacks)

def ownerResult (a : Data) (regs : Fin 16 → Bool) (is : List ℕ) : Data :=
  ⟨regs,Function.update (Function.update a.stacks 328 (LayoutOwnerFiberProgram.unary is.length)) 329 (LayoutOwnerFiberProgram.encodeIndices is)⟩

def frameRow : Code := .call (ProgramLinking.liftProgram
  Squarefree.Program.frameEmitProgram frameRegisters frameStacks)

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT BitProgram StructuredCalls
attribute [local simp] Fin.coe_ofNat_eq_mod

def emitRow : Code := .seq (transfer 240 330)
  (.seq frameRow (.seq (push 334 true) (transfer 334 332)))

def finishRows : Code := .seq (push 332 false) (transfer 332 205)

def rowPorts : UnaryForPrograms.Ports 16 340 := ⟨331,14,15⟩
def rowBody (callback : Code) : Code := .seq callback (.seq emitRow (push 320 true))
def rowLoop (callback : Code) : Code := UnaryForPrograms.forCmd rowPorts (rowBody callback)
def rowsCommand (callback : Code) : Code :=
  .seq (copy 212 331) (.seq (rowLoop callback) (.seq (clear 320) finishRows))

def RowSpec (callback : Code) (base : Store) (value : ℕ → List Bool) (N K : ℕ) : Prop :=
  ∀ j, j < N → ∀ remaining acc,
    ExecutesIn callback K (rowState base j remaining acc)
      (Function.update (rowState base j remaining acc) 240 (value j))

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT BitProgram StructuredCalls
attribute [local simp] Fin.coe_ofNat_eq_mod

variable {Witness : Type*}

/-- Witnesses may be selected by the concrete run. Every result carries its
semantic relation, exact serialization, and a byte bound. -/
def RelSourceSpec (source : Code) (base : Store) (encode : Witness → List Bool)
    (R : ℕ → Witness → Prop) (I K L : ℕ) : Prop :=
  ∀ i, i ≤ I → ∀ ids acc regs, ∃ w n rf,
    R i w ∧ (encode w).length ≤ L ∧ n ≤ K ∧
    Eval source n (⟨regs,Function.update (fiberState base ids acc) 305
      (List.replicate i true)⟩ : Data)
      (⟨rf,Function.update (Function.update (fiberState base ids acc) 305
        (List.replicate i true)) 287 (encode w)⟩ : Data)

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

/-! Paid bank relocation and register reset for the native polynomial source
executor. The parameter is a finite BitProgram; the integration selects the
checked polynomial executor, never a polynomial-value instruction. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT BitProgram StructuredCalls

def resetExecutor : Code := liftCommand SubexpDenseLiteralPadding.reset 26 26 id executorPorts

abbrev execute {l : ℕ} (p : Program 16 256 l) : Code :=
  .seq resetExecutor (.call (ProgramLinking.liftProgram p id executorPorts))

/-- Controls21/26 are temporarily parked while source333 is interpreted. -/
abbrev evaluateRow {l : ℕ} (p : Program 16 256 l) : Code :=
  .seq (transfer 21 335) (.seq (transfer 26 336) (.seq (transfer 333 26)
    (.seq (execute p) (.seq (transfer 335 21) (transfer 336 26)))))

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT BitProgram StructuredCalls
attribute [local simp] Fin.coe_ofNat_eq_mod
variable {Witness : Type*}

def RelRowSpec (callback : Code) (base : Store) (encode : Witness → List Bool)
    (R : ℕ → Witness → Prop) (N K W : ℕ) : Prop :=
  ∀ j, j < N → ∀ remaining acc regs, ∃ w n rf,
    R j w ∧ (encode w).length=W ∧ n ≤ K ∧
    Eval callback n (⟨regs,rowState base j remaining acc⟩ : Data)
      (⟨rf,Function.update (rowState base j remaining acc) 240 (encode w)⟩ : Data)

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

/-! The bytes produced by the runtime fold are the compiler output of the
same finite sum expression, including the empty-owner zero polynomial. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourceRowsProgramInitializeLift
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT BitProgram StructuredCalls

def initializeSource : Code := liftCommand LayoutSourceRowsProgramInitialize.command
  210 192 id initializationPorts

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PolynomialExecutorProgramServices
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete native add, truncated multiply and padding services for the
source-row postfix interpreter on arbitrary-degree coefficient arrays. -/
namespace SubexponentialSAT.SqrtLog.PolynomialExecutorProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open SubexponentialSAT.SubexpRowPostfixInterpreter (physicalCfg ImplementsOnGlobal LoadImplementsGlobal)
open SubexponentialSAT.SubexpRowPostfixContext (operandStore preparedStore )

def addProgram := SubexpRowPostfixServices.program DensePolynomialProgram.AddService.command
def mulProgram := SubexpRowPostfixServices.program DensePolynomialProgram.Fixed.mulCommand


end SubexponentialSAT.SqrtLog.PolynomialExecutorProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PolynomialExecutorProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! One fixed native interpreter for raw row-polynomial postfix source.
All literal padding and coefficient-array arithmetic are included. -/
namespace SubexponentialSAT.SqrtLog.PolynomialExecutorProgram
open SubexponentialSAT BitProgram StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open SubexponentialSAT.SubexpRowPostfixInterpreter (physicalCfg)

def program := SubexponentialSAT.SubexpRowPostfixInterpreter.globalProgram addProgram mulProgram
  SubexpDenseLiteralPadding.program

end SubexponentialSAT.SqrtLog.PolynomialExecutorProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PolynomialExecutorProgramFlat
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The complete native source interpreter returns an ordinary flat
coefficient array on240, ready for the perturbation producer. -/
namespace SubexponentialSAT.SqrtLog.PolynomialExecutorProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open SubexponentialSAT.SubexpRowPostfixInterpreter (physicalCfg )
open SubexponentialSAT.SubexpRowPostfixContext (operandStore )

def flatProgram := flattenProgram program

end SubexponentialSAT.SqrtLog.PolynomialExecutorProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourceRowsProgramModel
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT BitProgram StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open SubexponentialSAT.SubexpRowPostfixInterpreter (physicalCfg )
open SubexponentialSAT.SubexpRowPostfixContext (operandStore )

def executeModel : Code := execute PolynomialExecutorProgram.flatProgram

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourceRowsProgramStaging
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The source numerator uses empty scalar work tapes5/10. The polynomial
executor retains its modulus/width there. Two reversible transfers isolate
these phases without touching the native high arithmetic cache. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT BitProgram StructuredCalls
attribute [local simp] Fin.coe_ofNat_eq_mod

def stageScalarWork : Code := .seq (transfer 5 335) (transfer 10 336)
def unstageScalarWork : Code := .seq (transfer 335 5) (transfer 336 10)

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourceRowsProgramZero
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Absent factor incidences have zero source polynomials. This branch copies
the initialized zero array once per ambient coordinate and emits every row. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT BitProgram StructuredCalls

def zeroRow : Code := copy 192 240
def zeroRows : Code := rowsCommand zeroRow

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafBranchProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The branch callback is a real residual-count program followed by the native
binary adder. Semantic branch counts occur only in its verification contract. -/
namespace SubexponentialSAT.SqrtLog.LeafBranchProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.ExecCNFTupleEnumeration

variable {R S : ℕ}

def read (p : Ports R S) (a : State R S) := a.stacks (p.mass.stack 0)

abbrev body (p : Ports R S) (query : Cmd R S) :=
  Cmd.seq query (LeafProgram.Mass.invoke p.mass)

end SubexponentialSAT.SqrtLog.LeafBranchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadFactorsProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Factor head selection uses the full original table and a paid ambient offset. -/
namespace SubexponentialSAT.SqrtLog.LeafHeadFactorsProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

abbrev Data := State 16 64
abbrev Code := Cmd 16 64

def selected (d : Data) (word : List Bool) : Data :=
  ⟨readRegs d.regs 0 1 none,Function.update d.stacks 36 word⟩


end SubexponentialSAT.SqrtLog.LeafHeadFactorsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadFactorsProgramTest
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafHeadFactorsProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

def Clean (d : Data) : Prop :=
  ∀ i ∈ ([12,16,17,18,19,20,21,34,36,40,42] : List (Fin 64)), d.stacks i = []

def addressed (d : Data) : Data := afterCopy (afterCopy d 31 40 0 1) 39 40 0 1

def cleared (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, Function.update d.stacks 40 []⟩
def clearAddress : Code := .call (StackRoutines.clearProgram 40 0 1)

def tested (d : Data) (answer : Bool) : Data :=
  ⟨Function.update (readRegs d.regs 0 1 none) 4 answer, d.stacks⟩

end SubexponentialSAT.SqrtLog.LeafHeadFactorsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadFactorsProgramLoop
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafHeadFactorsProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

def loopPorts : UnaryForPrograms.Ports 16 64 := ⟨39,14,15⟩

end SubexponentialSAT.SqrtLog.LeafHeadFactorsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadFactorsProgramRun
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafHeadFactorsProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

def input (regs : Fin 16 → Bool) (rows : List (List Bool)) (A N W z : ℕ) : Data :=
  ⟨regs,baseStacks rows A N W z⟩

def result (rows : List (List Bool)) (A N W z : ℕ) : Data :=
  ⟨fun _ => false,
    Function.update (Function.update (baseStacks rows A N W z) 0
      (ProgramEncoding.encodeRecords ((chosenIds (predicate rows A z) N).map Encoding.encodeNat)))
      1 (zeros (count (predicate rows A z) N))⟩

end SubexponentialSAT.SqrtLog.LeafHeadFactorsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadSetupProgramAddress
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The node index and palette size are runtime inputs. This fixed program
initializes the head countdown and computes the first physical color address
by real unary multiplication. Subsequent heads increment that address. -/
namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Address
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.Subexp.BasisTransposePlanProgram

def input (regs : Fin 3 → Bool) (r t : ℕ) : _root_.OAI.Algorithms.SubexponentialSAT.Subexp.BasisTransposePlanProgram.Data :=
  ⟨regs,![_root_.OAI.Algorithms.SubexponentialSAT.Subexp.BasisTransposePlanProgram.unary r,[],_root_.OAI.Algorithms.SubexponentialSAT.Subexp.BasisTransposePlanProgram.unary t,[],[],[],[]]⟩
def result (regs : Fin 3 → Bool) (r t : ℕ) : _root_.OAI.Algorithms.SubexponentialSAT.Subexp.BasisTransposePlanProgram.Data :=
  ⟨regs,![_root_.OAI.Algorithms.SubexponentialSAT.Subexp.BasisTransposePlanProgram.unary r,[],_root_.OAI.Algorithms.SubexponentialSAT.Subexp.BasisTransposePlanProgram.unary t,_root_.OAI.Algorithms.SubexponentialSAT.Subexp.BasisTransposePlanProgram.unary r,_root_.OAI.Algorithms.SubexponentialSAT.Subexp.BasisTransposePlanProgram.unary (t*r),[],[]]⟩

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Address

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadSetupProgramBoot
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Per-node paid bootstrap: address multiplication, actual plan-record
counting, and construction of the integer interpolation coefficient cache. -/
noncomputable section

namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def rowCountProgram := compiled SubexponentialSAT.SubexpScopeCountSetup.countCommand 1 2
def countRows : Code := stage rowCountProgram rowCountRegs (by decide) rowCountInputs rowCountOutputs

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadSetupProgramBootRun
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact state and cost of the paid per-node bootstrap. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog
namespace LeafHeadSetupProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def addressState (a : Data) (regs : Fin 3 → Bool) (r t : ℕ) : Data :=
  returned addressRegs (by decide) addressInputs addressOutputs a (Address.result regs r t)

end LeafHeadSetupProgram

end SqrtLog

end SubexponentialSAT

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadSetupProgramSelection
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual original/factor ID selection from the common full word table.
The input masters are copied into an isolated lookup program, and its output
records are copied back before the entire lookup workspace is cleared. -/
noncomputable section

namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def factorResult (a : Data) (A N : ℕ) (rows : List (List Bool)) (W z : ℕ) : Data :=
  returned id (by decide) factorInputs factorOutputs a
    (LeafHeadFactorsProgram.result rows A N W z)
def factorCost (a : Data) (A N : ℕ) (rows : List (List Bool)) (W z : ℕ) :=
  stageCost id (by decide) factorInputs factorOutputs a
    (LeafHeadFactorsProgram.result rows A N W z)
    (LeafHeadFactorsProgram.budget A N rows.length W z)

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadSetupProgramMatrixRun
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The all-row entry cache is physically copied into the complete matrix
bank, and the actual controller table is copied out as the next head alphabet. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def matrixBase (a : Data) : Fin 288 → List Bool := fun i =>
  if i=0 then a.stacks 141 else if i=17 then a.stacks 650 else if i=18 then a.stacks 128 else
  if i=23 then a.stacks 651 else if i=225 then a.stacks 135 else if i=226 then a.stacks 136 else
  if i=227 then a.stacks 640 else if i=228 then a.stacks 641 else if i=229 then a.stacks 140 else
  if i=230 then a.stacks 642 else if i=231 then a.stacks 138 else if i=232 then a.stacks 139 else
  if i=233 then a.stacks 130 else if i=234 then a.stacks 131 else if i=235 then a.stacks 307 else
  if i=236 then a.stacks 132 else []

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram

end
end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadSetupProgramNativeInputs
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Runtime source facts for the closed head setup. No cache output, matrix,
entry evaluator, or running-time witness is supplied in this interface. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open SubexponentialSAT.Subexp.ConstructivePacking RowSelectionProgram

structure Ready (s : Inputs) (a : LeafHeadSetupProgram.Data) : Prop where
  ambient : a.stacks 128=unary s.n
  factors : a.stacks 129=unary s.N
  colors : a.stacks 130=unary s.r
  nodes : a.stacks 131=unary s.Q
  wordWidth : a.stacks 132=unary (s.Q*s.r)
  words : a.stacks 133=s.rows.flatten
  low : a.stacks 134=s.low
  metadata : a.stacks 135=s.metadata
  plans : a.stacks 136=LayoutOwnerFiberProgram.stream s.plans
  order : a.stacks 138=unary s.R
  height : a.stacks 139=s.height
  width : a.stacks 140=s.width
  offset : BinaryArithmetic.toNat (a.stacks 141)=s.offset
  node : a.stacks 307=unary s.node.val
  tuples : a.stacks 660=[]
  marker : a.stacks 665=[]

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHighContextProgramBase
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A paid parser pipeline stages the current physical high assignment. -/
namespace SubexponentialSAT.SqrtLog.LeafHighContextProgram.Local
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.Subexp.BlockSearchPreparation

abbrev Code := Cmd 4 10

def maskStep : Code := .call (ProgramLinking.liftProgram HighIncidenceProgram.Mask.program maskRegs maskStacks)
def copyCounter : Code := .call (StackRoutines.copyProgram 0 4 8 0 1)
def flattenStep : Code := .call (ProgramLinking.liftProgram SubexponentialSAT.Subexp.AssignmentRecordViews.flattenProgram flatRegs flatStacks)
def copyMask : Code := .call (StackRoutines.copyProgram 1 7 8 0 1)


end SubexponentialSAT.SqrtLog.LeafHighContextProgram.Local

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafStatisticsSemanticsTransport
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Scope transport for the actual native factor IDs. -/
namespace SubexponentialSAT.SqrtLog.LeafStatisticsSemantics

open PackingIncidenceInput HighIncidence

/-- The concrete rank-based bijection transports every native scope exactly to
the residual original factor or the singleton of its numbered uncovered owner. -/
theorem nativeScope_transport (scopes : List (List ℕ)) (mask : List Bool)
    (e : Fin scopes.length ⊕ uncovered (residualScope scopes mask)) :
    nativeScope scopes mask (factorCodeEquiv scopes mask e) = completedScope scopes mask e := by
  cases e with
  | inl e => exact nativeScope_original scopes mask e
  | inr v => exact nativeScope_neutral scopes mask v

theorem nativeScope_degree (scopes : List (List ℕ)) (mask : List Bool) (v : Free mask) :
    Incidence.degree (nativeScope scopes mask) v =
      max 1 (LeafStatisticsProgram.degree scopes v.val.val) := by
  calc
    _ = Incidence.degree (completedScope scopes mask) v := by
      rw [Incidence.degree_eq_sum, Incidence.degree_eq_sum]
      symm
      apply Fintype.sum_equiv (factorCodeEquiv scopes mask)
      intro e
      rw [nativeScope_transport]
    _ = _ := completed_degree scopes mask v

end SubexponentialSAT.SqrtLog.LeafStatisticsSemantics

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafPackingFiberBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Raw native incidence records have no repeated owner-factor pair. Hence their
index fibers are bounded by the statistics of the actual completed scopes. -/
namespace SubexponentialSAT.SqrtLog.LeafPackingFiberBounds
open PackingIncidenceInput LeafStatisticsSemantics LeafStatisticsProgram

 theorem owner_fiber_le (scopes : List (List ℕ)) (mask : List Bool) (n : ℕ)
    (hm : mask.length ≤ n) (v : Fin n) :
    (Finset.univ.filter fun i : Semantics.Incidences scopes mask =>
      Semantics.owner scopes n mask hm i=v).card ≤ (measured scopes mask).occurrence := by
  classical
  let s := Finset.univ.filter fun i : Semantics.Incidences scopes mask =>
    Semantics.owner scopes n mask hm i=v
  change s.card ≤ _
  by_cases hs : s.Nonempty
  · obtain ⟨j,hj⟩ := hs
    let w := freeOwner scopes mask j
    have hjv : Semantics.owner scopes n mask hm j=v := (Finset.mem_filter.mp hj).2
    have hsame (i) (hi : i ∈ s) : freeOwner scopes mask i=w := by
      apply Subtype.ext
      apply Fin.ext
      change ((Semantics.nativeEntries scopes mask).get i).1 =
        ((Semantics.nativeEntries scopes mask).get j).1
      exact congrArg Fin.val ((Finset.mem_filter.mp hi).2.trans hjv.symm)
    have hcard : s.card ≤ Incidence.degree (nativeScope scopes mask) w := by
      apply Finset.card_le_card_of_injOn (Semantics.factor scopes n mask hm)
      · intro i hi
        change _ ∈ Finset.univ.filter (fun e => w ∈ nativeScope scopes mask e)
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        rw [← hsame i hi]
        exact freeOwner_mem scopes mask n hm i
      · intro i hi j hj he
        exact free_pair_injective scopes mask n hm i j ((hsame i hi).trans (hsame j hj).symm) he
    have hbound := (totals_occurrence_le_iff scopes 0 mask zero
      (measured scopes mask).occurrence).mp (le_refl (measured scopes mask).occurrence)
    rw [nativeScope_degree] at hcard
    exact hcard.trans (by simpa only [Nat.zero_add] using hbound.2 w.val (free_bit mask w))
  · simp [Finset.not_nonempty_iff_eq_empty.mp hs]

end SubexponentialSAT.SqrtLog.LeafPackingFiberBounds

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParametersProgramNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native runtime leaf parameter production, integer guards, and paid setup.
The former composition modules are import-only compatibility shims. -/


/- Component: SubexponentialSAT.SqrtLog.LeafParametersProgramBankRoots -/

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Bank

open BitProgram StructuredCalls BinaryArithmetic

theorem copy_eval (r : Regs) (w : Words) (a o : Fin 64) (hoa : o ≠ a) (ho : w o = []) :
    ∃ rf, Eval (copyCmd a o) (7*(w a).length+5) (state r w)
        (state rf (Function.update w o (w a))) := by
  have hh := ArithmeticCalls.copyAt_eval (port a) (port o) (work 1 (by decide) 0) (state r w)
    (by intro h; exact hoa ((Fin.castAdd_injective 64 13) h.symm))
    (work_ne_port 1 (by decide) 0 a).symm
    (work_ne_port 1 (by decide) 0 o)
    (by simpa using ho) (state_work r w _ (by simp [work]))
  refine ⟨(ArithmeticCalls.afterCopy (port a) (port o) (state r w)).regs,?_⟩
  simp only [ArithmeticCalls.afterCopy] at hh
  rw [state_update] at hh
  simpa only [copyCmd, ArithmeticCalls.afterCopy, state_port] using hh

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Bank


/- Component: SubexponentialSAT.SqrtLog.LeafParametersProgramDispatch -/

/-! A fixed ten-comparison bit guard. All operands are runtime binary words.
This module states their data relation separately from parameter production. -/

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.BitGuard

open BitProgram StructuredCalls StructuredProgram BinaryArithmetic

def cost (j : Fin 10) (d : Data) : ℕ :=
  10 * max (d.stacks (pair j 0)).length (d.stacks (pair j 1)).length + 8

def pass (j : Fin 10) (d : Data) : Bool :=
  decide (BinaryArithmetic.toNat (d.stacks (pair j 1))  ≤  BinaryArithmetic.toNat (d.stacks (pair j 0)))

def checksCost (js : List (Fin 10)) (d : Data) : ℕ := (js.map (fun j => cost j d)).sum
def checksPass (js : List (Fin 10)) (d : Data) : Bool := js.all (fun j => pass j d)

def Encodes (x : Input) (a : Data) : Prop :=
  ∀ j, BinaryArithmetic.toNat (a.stacks (pair j 0)) = upper x j ∧
    BinaryArithmetic.toNat (a.stacks (pair j 1)) = lower x j

end SubexponentialSAT.SqrtLog.LeafParametersProgram.BitGuard


/- Component: SubexponentialSAT.SqrtLog.LeafParametersProgramCircuit -/


end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramHashParameters
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete placement of the selector's numerical preparation in the full
leaf bank. Formula784 and answer787 are outside this routine;782 contains the
actual binary clause count produced by ClauseCount.caller. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.HashParameters

open SubexponentialSAT BitProgram StructuredCalls

abbrev command : Cmd 40 896 := Execution.HashParameters.command ports

end SubexponentialSAT.SqrtLog.LeafProgram.HashParameters

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafRingSetupProgramNative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


/-! The fixed executable preparation pipeline.  Its input is the actual
numerical bank emitted by `LeafParametersProgram`; no field polynomial,
modulus, multiplication table, nodes, or idempotent coefficients are inputs.
The stage-by-stage execution theorem is separate from this code definition.
-/


/-! Arithmetic consumers use the same bytes generated by the preceding
stages.  These are structural handoff lemmas; the complete production
trace must establish `NativeBytes` before invoking them. -/

namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram
open BitProgram StructuredCalls

def unaryPlan : List (Fin 640 × Fin 640) → Cmd 32 640
  | [] => .base .skip
  | p::ps => .seq (unary p.1 p.2) (unaryPlan ps)

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsReadoutProgramState
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed forty-stack workspace for the two runtime readout counters. -/


/-! Actual stack construction of the sparse key (u,z,empty support), followed
by the paid query cleanup and unary-index increment. -/


/-! One concrete (u,z) coefficient fetch, addition, and index advance. -/


/-! The U loop is driven by a real unary stack. Every visit invokes the
concrete key builder and dictionary scan; no callback is left abstract. -/
namespace SubexponentialSAT.SqrtLog.MomentsReadoutProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

def innerPorts : UnaryForPrograms.Ports 8 40 := ⟨32,0,1⟩

end SubexponentialSAT.SqrtLog.MomentsReadoutProgram


/-! Seed one Z accumulator from the cached zero vector and append the
completed coefficient to the output, paying for every copy and reversal. -/


/-! Runtime Z enumeration. Completed fixed-width coefficients are prepended
in reverse and are restored once by the final output transfer. -/


/-! Build the all-false support mask from the actual ambient shape stack.
The loop length is the ambient number of variables, including unused ones. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ProducedQueryRankMagnitude
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The actual raw owner-fiber length controls separately stored signed
components, so the executed shift is bounded without canonical signs. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.ProducedQueryRank
open scoped BigOperators
open PackingCallerProgram LeafParametersProgram BucketProgram.ProducedRank

 theorem actual_fiber_length (p : Problem) (v : Fin p.n) :
    (LayoutOwnerFiberProgram.fiberIndices v.val 0
      (PackingIncidenceInput.Semantics.nativeEntries p.scopes p.mask)).length=
      (Finset.univ.filter fun i => owner p i=v).card := by
  conv_lhs => rw [← addressPairs_eq p,fiber_length_ofFn]
  rw [Finset.card_filter]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [addressPair_owner,Fin.val_inj]

end SubexponentialSAT.SqrtLog.ProducedQueryRank

end

end OAI.Algorithms
end


