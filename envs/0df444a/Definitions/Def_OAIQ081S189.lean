-- Prove2me | Definitions.Def_OAIQ081S189
-- name    : OAIQ081S189
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T23:45:55.052378+00:00
-- url     : https://prove2.me/theorems/75db3cd1-b3d1-40b6-add0-c4ed166db798
-- title:
--   Definitions bundle OAIQ081S189 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 24 declarations of OpenAI's Lean: 20 definitions and 4 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback.callbackBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback.uniformCallbackBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCorrect.assignmentBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentProgram.callback`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentProgram.choose`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentProgram.hashFactor`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentProgram.loop`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentProgram.markedFactor`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentProgram.prepareIncidence`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram.caller`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram.literalIteration`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram.literalPayload`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram.lowPayload`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram.prepareFactor`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram.program`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader.commandFrom`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader.localCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader.localProgram`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader.lowCall`.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: [`SubexponentialSAT_SqrtLogSpace_FactorAssignmentCallbackNative`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/FactorAssignmentCallbackNative.lean), [`SubexponentialSAT_SqrtLogSpace_FactorAssignmentCorrect`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/FactorAssignmentCorrect.lean), [`SubexponentialSAT_SqrtLogSpace_FactorAssignmentProgram`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/FactorAssignmentProgram.lean), [`SubexponentialSAT_SqrtLogSpace_FactorTableProgram`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/FactorTableProgram.lean), [`SubexponentialSAT_SqrtLogSpace_SignatureHeadLoaderCore`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/SignatureHeadLoaderCore.lean), [`SubexponentialSAT_SqrtLog_LeafProgramQueryArithmetic`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafProgramQueryArithmetic.lean), [`SubexponentialSAT_SqrtLog_LeafProgramQueryDegreeRing`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafProgramQueryDegreeRing.lean), [`SubexponentialSAT_SqrtLog_LeafProgramQueryRing`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafProgramQueryRing.lean), [`SubexponentialSAT_SqrtLog_LeafRingSetupProgramLowFrameWide`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafRingSetupProgramLowFrameWide.lean).
--
--   **Imports.** It imports the bundles `OAIQ081S186`, `OAIQ081S187` and `OAIQ081S188` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S191` and `OAIQ081S192`; the statements `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentBranches.hashFactor_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentBranches.markedFactor_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentBranches.prepareIncidence_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback.callbackBudget_le`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback.callback_eval_correct`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback.neutral_callback_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative.command_native_resources`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative.lowPayload_native_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative.native_literal`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram.literalPayload_rel` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableSpace.command_resources`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentBranches.hashFactor_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentBranches.markedFactor_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentBranches.prepareIncidence_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback.callbackBudget_le`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback.callback_eval_correct`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback.neutral_callback_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative.command_native_resources`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative.lowPayload_native_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative.native_literal`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram.literalPayload_rel` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableSpace.command_resources`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ081S186
import Definitions.Def_OAIQ081S187
import Definitions.Def_OAIQ081S188

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorTableProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual selected-factor table runs over ambient variable IDs. Each low
payload is specialized immediately before its framed table entry is retained.
The source scratch embedding excludes persistent layout masters. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI BitProgram StructuredCalls SubexpConvolutionControl SubexpScanPrimitives
open SubexpPolynomialConstructor PerturbationAssembly OAI.Algorithms.SubexponentialSAT.SubexpLiftRing

attribute [local simp] Fin.coe_ofNat_eq_mod

def lowPayload : OuterCode := .seq (liftBase LeafProgram.Source.command) specializeCall

def literalPayload : OuterCode :=
  .seq (liftInner (readFlag 234)) (.ite 15 (liftInner highConstant) lowPayload)

def literalIteration : OuterCode :=
  .seq (liftInner makeLiteralKey) (.seq literalPayload (liftInner finishLiteral))

def prepareFactor : OuterCode :=
  .seq (liftInner (copy 212 233))
    (.seq (UnaryForPrograms.forCmd literalPorts literalIteration)
      (liftInner (move 229 221)))

/-- Exact closed table command, with the old paid staging and export programs
relocated away from all persistent layout masters. -/
def command : OuterCode :=
  .seq initializeWorker (.seq (liftBase LeafProgram.Incidence.stage)
    (.seq prepareFactor (liftBase LeafProgram.Incidence.exportResult)))

def program := compiled command 556 62

def caller : Cmd 40 896 := .call (ProgramLinking.liftProgram program callerRegisters id)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorAssignmentProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The accepted-assignment factor product uses the original finite-ring
indicator and clause programs after the concrete specialized table producer.
Every cache is rebuilt from persistent source words by paid native copies;
neutral factor IDs leave the running multiplicative identity unchanged. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentProgram

open OAI BitProgram StructuredCalls SubexpSetupStorage
open SqrtLog SqrtLog.LeafProgram
noncomputable section

def prepareIncidence : Code :=
  .seq (liftLow FactorID.command 149 556) FactorTableProgram.caller

def hashFactor : Code := .seq prepareIncidence
  (liftLow (.seq Expansion.forwardCommand FactorEvaluationSpace.hashArithmetic) 154 151)

def markedFactor : Code := .seq prepareIncidence
  (liftLow (.seq (Factor.move 154 63) FactorEvaluationSpace.markedArithmetic) 154 151)

def choose : Code := .ite 5 hashFactor (.ite 6 markedFactor (.base .skip))

def callback : Code := .seq clearCallback
  (.seq (liftLow FactorDispatch.command 149 154)
    (.seq choose (.seq (clear 149) returnToRecords)))

def loop : Code := RecordPrograms.iterate ports callback

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorAssignmentCallbackNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete physical inputs for the streamed factor callback. The source
context is the actual q.ctx, and the dispatcher determines every selected row
and clause. These predicates contain stored words and finite size bounds only.
Their construction from the actual loader/cache run remains an integration step. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback
open OAI BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open SqrtLog SqrtLog.LeafProgram HashCircuitProgram HashCircuitProgram.Native
open IdempotentApplyProgram.Steps MomentsProgram NativeSemantics
open FactorAssignmentProgram
open Subexp.ConstructivePacking MulticolorTypes LayoutProgram DensePolynomialProgram

noncomputable section

variable {r Q n d A S : ℕ} {q : Factor.Spec r Q n d}
  {one seed : FactorAssignmentLoop.Raw n (baseWidth 3 q.p.t) d}
  {a : FactorAssignmentProgram.Data} {f : ℕ}

/-- The explicit cost keeps every dispatcher scan and every native branch.
It is a proof-side numerical envelope, never a traversal over possible states. -/
def callbackBudget (q : Factor.Spec r Q n d) (A S width : ℕ)
    (a : FactorAssignmentProgram.Data) (f : ℕ) (rf : Fin 8 → Bool) : ℕ :=
  clearCallbackCost a + 9 * (a.stacks 149).length + 15 +
    LeafFactorDispatchProgram.budget q.rawRows q.clauses q.mark f +
    if hf : f < q.rows.length then hashBranchBudget q A S width a f hf rf
    else if q.marked && decide (f = q.rows.length) then markedBranchBudget q A S a f rf else 0

/-- The complete per-record bound is fixed before the record scan. Z bounds
only explicit source dimensions, serialized inputs and retained arithmetic
capacity; no evaluator or run is assumed. -/
def uniformCallbackBudget (q : Factor.Spec r Q n d) (A S Z : ℕ) : ℕ :=
  callbackScratch.length * (2*A+3) + 128*A+200 + tableBudget q A S +
    2000*Z^3 + 14000000*Z^9

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorAssignmentCorrect
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual initializer, source-context cache, dispatcher, specialized
incidence producer and factor arithmetic instantiate the stored-ID fold.
The output is the entire specialized coefficient-ring product on stack854.
Every resource assertion below concerns this same fixed command. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCorrect

open OAI BitProgram StructuredCalls SubexpSetupStorage
open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram MomentsProgram
open OAI.Algorithms.SubexponentialSAT.SubexpLiftRing OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing
open FactorAssignmentProgram FactorAssignmentBoundary FactorAssignmentLoop

noncomputable section
attribute [local simp] Fin.coe_ofNat_eq_mod

variable {r Q n d P M S : ℕ} {q : Factor.Spec r Q n d}

def assignmentBudget (q : Factor.Spec r Q n d) (P S Z : ℕ) : ℕ :=
  entryScratch.length * (2 * P + 3) + 1100 * (P + 1) + 2 +
    uniformProductBudget n (baseWidth 3 q.p.t) d q.u q.J P
      (FactorAssignmentCallback.uniformCallbackBudget q P S Z)

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCorrect
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureHeadLoaderCore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The fixed head-loader table uses the actual integer entry program. Its
physical matrix view follows LeafHeadSetupProgramHead/MatrixRun exactly, while
its controller emits one matrix and never constructs assignment tables. -/
noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader
open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
open OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage

/-- The low bank computes a single actual head; output668 is the full shifted
matrix. Raw669 is cleared before returning to the signature iterator. -/
def localCommand : Code :=
  .seq prepareHead (.seq rawCommand (.seq shiftCommand (clearCmd 669)))
def localProgram := compiled localCommand 649 668

def lowCall : Cmd 16 896 :=
  .call (ProgramLinking.liftProgram localProgram id lowStacks)

def commandFrom (src : Fin 896) : Cmd 16 896 :=
  .seq (importAddressFrom src) (.seq lowCall exportMatrix)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader
end
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafRingSetupProgramLowFrameWide
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Low-workspace preservation for the actual wide producer call.  The
numeric premises are exactly those already used to execute that call. -/
namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram.LowFrame
open BitProgram StructuredCalls LeafParametersProgram

theorem producerWideCall_empty
    (base out : StructuredProgram.State 40 768) (n : ℕ)
    (he : Eval producerWideCall n base out)
    (m : Circuit.Model) (w : Bank.Words) (r : Bank.Regs)
    (hs : Circuit.Shape m w)
    (ha : projectState (registers 8 (by decide)) parameters
      (projectState wideRegisters wideStacks base)=Bank.state r w)
    (W V L : ℕ) (hinit : ∀ i,(base.stacks i).length ≤ W)
    (hv : ∀ i,(Circuit.result Serialization.code m).val i ≤ V)
    (hw : ∀ i,(Circuit.result Serialization.code m).len i ≤ L)
    (ht : 0 < m.val 33) (hd : 0 < m.val 34)
    (i : Fin 768) (hi : i.val < 190) (hz : base.stacks i=[]) :
    out.stacks i=[] := by
  let a := projectState wideRegisters wideStacks base
  obtain ⟨nc,hnc,e,M,cache,u,hec,hp,hcollector⟩ :=
    producerCommand_eval a m w r hs ha W V L
      (fun j => hinit (wideStacks j)) hv hw ht hd
  have hrun := compiled_halt_trace hec (parameters 0) 300
  have hwide : Eval producerWideCall (nc+1) base
      (embedState wideRegisters wideStacks base e) :=
    eval_call_from_state producerProgram wideRegisters wideStacks base
      wideRegisters_injective wideStacks_injective hrun
  have heq := SubexpPrimeProgram.eval_result_unique he hwide 0 0
  rw [heq]
  let j : Fin 640 := ⟨i.val,by omega⟩
  have hj : wideStacks j=i := Fin.ext rfl
  rw [←hj,embedState_stack _ _ _ _ wideStacks_injective]
  apply (producerCommand_preservesEmpty j (by exact hi)).run hec
  change base.stacks (wideStacks j)=[]
  rw [hj]
  exact hz

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram.LowFrame

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramQueryRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Ring and interpolation setup are performed once per marked query. All
arithmetic objects in the conclusion are generated by the two native programs. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Query.Ring
open SubexponentialSAT BitProgram StructuredCalls LeafParametersProgram
open LeafRingSetupProgram

theorem command_eval (base : Query.Data) (m : Circuit.Model)
    (w : Bank.Words) (r : Bank.Regs) (hs : Circuit.Shape m w)
    (ha : projectState (registers 8 (by decide)) parameters
      (projectState wideRegisters wideStacks base)=Bank.state r w)
    (W V L : ℕ) (hinit : ∀i,(base.stacks i).length ≤ W)
    (hv : ∀i,(Circuit.result Serialization.code m).val i ≤ V)
    (hw : ∀i,(Circuit.result Serialization.code m).len i ≤ L)
    (ht : 0 < m.val 33) (hd : 0 < m.val 34)
    (hexp : (Circuit.result Serialization.code m).val 44=3^(m.val 34)-2) :
    ∃ n ≤ budget m W V L, ∃ e : LeafRingSetupProgram.Data,
      ∃ (M : SubexpPreparedQuartic.Modulus 3 (m.val 33))
        (cache : RingProgram.ScalarCache 3 (m.val 33))
        (u : RingProgram.ScalarCode 3 (m.val 33)), ∃ out : Query.Data,
      Eval command n base out ∧ Produced m hd M cache u e ∧
      (∀i : Fin 640,i.val < 340 → out.stacks (wideStacks i)=e.stacks i) ∧
      out.stacks 713=InterpolationCacheProgram.inverseBytes (m.val 33) (IrreducibleSearch.data hd)
        M cache (LeafProgram.Constants.constantCode (m.val 34) cache.minusOne cache.zero)
        (nodeWords (m.val 33) (m.val 34) (m.val 21)) ∧
      out.stacks 714=InterpolationCacheProgram.negativeBytes (m.val 33) (IrreducibleSearch.data hd)
        M cache (LeafProgram.Constants.constantCode (m.val 34) cache.minusOne cache.zero)
        (nodeWords (m.val 33) (m.val 34) (m.val 21)) ∧
      out.stacks 715=InterpolationCacheProgram.differenceBytes (m.val 33) (IrreducibleSearch.data hd)
        M cache (LeafProgram.Constants.constantCode (m.val 34) cache.minusOne cache.zero)
        (nodeWords (m.val 33) (m.val 34) (m.val 21)) ∧
      out.stacks 716=List.replicate (m.val 21*(m.val 34*SubexpLiftRing.baseWidth 3 (m.val 33))) true ∧
      out.stacks 717=List.replicate (m.val 34*SubexpLiftRing.baseWidth 3 (m.val 33)) true ∧
      (∀i : Fin 768,340 ≤ i.val → i.val < 660 → out.stacks i=[]) ∧
      (∀i : Fin 768,660 ≤ i.val → i≠699 → i∉([713,714,715,716,717] : List (Fin 768)) →
        out.stacks i=base.stacks i) ∧
      (∀i : Fin 768,320 ≤ i.val → i.val < 340 → out.stacks i=base.stacks i) ∧
      (∀i : Fin 40,16 ≤ i.val → i.val < 24 → out.regs i=base.regs i) ∧
      (∀i : Fin 768,i.val < 190 → base.stacks i=[] → out.stacks i=[]) := by
  obtain ⟨nr,hnr,e,M,cache,u,her,hp,hregs,hhigh,hlow⟩ :=
    producerProgram_lifted base (projectState wideRegisters wideStacks base) rfl m w r hs ha
      W V L (fun i => hinit (wideStacks i)) hv hw ht hd
  let b := embedState wideRegisters wideStacks base e
  have hb (i : Fin 640) : b.stacks (wideStacks i)=e.stacks i :=
    embedState_stack _ _ _ _ wideStacks_injective i
  have hi := Interpolation.inputs_of_produced b e m hd M cache u hp hb hexp
  have hflat : b.stacks 256=(nodeWords (m.val 33) (m.val 34) (m.val 21)).flatMap RingProgram.flat := by
    rw [show b.stacks 256=e.stacks 256 from hb 256,hp.flatNodes]
    rw [List.flatMap_def]
  have hwidth : ∀i,(b.stacks i).length ≤ W+(producerBudget m W V L+1)+1 := by
    intro i
    have hh := Interpolation.eval_width her hinit i
    dsimp only [b]
    omega
  have hpos : 0 < m.val 34*SubexpLiftRing.baseWidth 3 (m.val 33) := by
    apply Nat.mul_pos hd
    unfold SubexpLiftRing.baseWidth
    exact Nat.mul_pos ht (Nat.succ_pos _)
  obtain ⟨ni,hni,out,hei,h713,h714,h715,h716,h717,hprivate,hframe,hiregs⟩ :=
    Interpolation.command_eval b (m.val 33) (IrreducibleSearch.data hd) M cache hp.caches.canonical
      (LeafProgram.Constants.constantCode (m.val 34) cache.minusOne cache.zero) hpos
      (nodeWords (m.val 33) (m.val 34) (m.val 21)) hi hflat
      (W+(producerBudget m W V L+1)+1) hwidth
  have outside (i : Fin 768) (hi : i.val < 340 ∨ 660 ≤ i.val) : i∉Interpolation.privatePorts := by
    simp only [Interpolation.privatePorts,List.mem_map,List.mem_finRange,true_and,not_exists]
    intro j hj
    have hh := congrArg Fin.val hj
    dsimp [Interpolation.localPorts] at hh
    omega
  refine ⟨nr+ni,?_,e,M,cache,u,out,her.seq hei,hp,?_,h713,h714,h715,?_,h717,?_,?_,?_,?_,?_⟩
  · simp only [nodeWords_length] at hni
    dsimp only [budget]
    omega
  · intro i hi
    exact (hframe (wideStacks i) (outside _ (Or.inl hi))
      (by intro h; have := congrArg Fin.val h; dsimp [wideStacks] at this; omega)
      (by simp only [List.mem_cons,List.not_mem_nil,or_false];
          intro h; rcases h with h|h|h|h|h <;>
            have hh := congrArg Fin.val h <;> dsimp [wideStacks] at hh <;> omega)).trans (hb i)
  · simpa only [nodeWords_length] using h716
  · intro i hlo hhi
    let j : Fin 320 := ⟨i.val-340,by omega⟩
    have hj : Interpolation.localPorts j=i := by
      apply Fin.ext
      dsimp [Interpolation.localPorts,j]
      omega
    rw [← hj]
    exact hprivate _ (Interpolation.privatePorts_mem j)
  · intro i hi h699 ho
    exact (hframe i (outside i (Or.inr hi)) h699 ho).trans (hhigh i (by omega))
  · intro i hlo hhi
    let j : Fin 640 := ⟨i.val,by omega⟩
    have hj : wideStacks j=i := Fin.ext rfl
    have hf := hframe i (outside i (Or.inl hhi))
      (by intro h; have hh : i.val=699 := congrArg Fin.val h; omega)
      (by
        intro h
        have hlarge : 340 ≤ i.val := by
          simp only [List.mem_cons,List.not_mem_nil,or_false] at h
          rcases h with rfl|rfl|rfl|rfl|rfl <;> decide
        omega)
    exact hf.trans (by simpa only [hj] using hlow j hlo hhi)
  · intro i hlo hhi
    exact (hiregs i hlo (by omega)).trans (hregs i hlo hhi)

  · intro i hi hz
    have hbz := LowFrame.producerWideCall_empty base b nr her m w r hs ha W V L
      hinit hv hw ht hd i hi hz
    apply Eq.trans (hframe i (outside i (Or.inl (by omega))) ?_ ?_) hbz
    · intro h
      have hh : i.val=699 := congrArg Fin.val h
      omega
    · intro h
      have hh : 190 ≤ i.val := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at h
        rcases h with rfl|rfl|rfl|rfl|rfl <;> decide
      omega

end SubexponentialSAT.SqrtLog.LeafProgram.Query.Ring

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramQueryArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! One actual arithmetic preparation per query: ring caches, interpolation
caches, then the inverse layout denominator. All three run before branching. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Query
open SubexponentialSAT BitProgram StructuredCalls LeafParametersProgram

 theorem arithmetic_eval (base : Data) (m : Circuit.Model)
    (w : Bank.Words) (r : Bank.Regs) (hs : Circuit.Shape m w)
    (ha : projectState (LeafRingSetupProgram.registers 8 (by decide)) LeafRingSetupProgram.parameters
      (projectState LeafRingSetupProgram.wideRegisters LeafRingSetupProgram.wideStacks base)=Bank.state r w)
    (W V L : ℕ) (hinit : ∀i,(base.stacks i).length ≤ W)
    (hv : ∀i,(Circuit.result Serialization.code m).val i ≤ V)
    (hw : ∀i,(Circuit.result Serialization.code m).len i ≤ L)
    (ht : 0 < m.val 33) (hd : 0 < m.val 34)
    (hexp : (Circuit.result Serialization.code m).val 44=3^(m.val 34)-2)
    (h728 : base.stacks 728=[]) :
    ∃ n ≤ arithmeticBudget m W V L (base.stacks 740).length,
      ∃ (e : LeafRingSetupProgram.Data)
        (M : SubexpPreparedQuartic.Modulus 3 (m.val 33))
        (cache : RingProgram.ScalarCache 3 (m.val 33))
        (u : RingProgram.ScalarCode 3 (m.val 33)) (out : Data),
      Eval arithmetic n base out ∧ ArithmeticOutput base out m hd M cache u e ∧
      (RingProgram.modelRing (m.val 33) ht hd (IrreducibleSearch.data hd) M cache).decode
        (LayoutDenominatorProgramQuery.value (m.val 33) (IrreducibleSearch.data hd)
          M cache u (base.stacks 740).length) *
        (2 : (IrreducibleSearch.data hd).O (m.val 33)) ^ ((base.stacks 740).length-1)=1 := by
  obtain ⟨nr,hnr,e,M,cache,u,b,hr,hp,hlow,h713,h714,h715,h716,h717,hprivate,hhigh,hcollector,hregs,hlowBlank⟩ :=
    Ring.command_eval base m w r hs ha W V L hinit hv hw ht hd hexp
  have hf728 : b.stacks 728=base.stacks 728 := hhigh _ (by decide) (by decide) (by decide)
  have hf740 : b.stacks 740=base.stacks 740 := hhigh _ (by decide) (by decide) (by decide)
  have hbwidth : ∀i,(b.stacks i).length ≤ W+Ring.budget m W V L+1 := by
    intro i
    have hi := LeafRingSetupProgram.Interpolation.eval_width hr hinit i
    omega
  obtain ⟨nd,hnd,out,he,hout,hinv,hdregs⟩ :=
    LayoutDenominatorProgramQuery.produced_command_eval b m ht hd M cache u e hp hlow
      (fun i hi hj => hprivate i hi (by omega)) (hf728.trans h728) _ hbwidth
  have frame (i : Fin 768) (hi : i≠728) : out.stacks i=b.stacks i := by
    rw [hout,Function.update_of_ne hi]
  have hv728 : out.stacks 728=RingProgram.flat (LayoutDenominatorProgramQuery.value
      (m.val 33) (IrreducibleSearch.data hd) M cache u (base.stacks 740).length) := by
    simp only [hout,Function.update_same,hf740]
  refine ⟨nr+nd,?_,e,M,cache,u,out,hr.seq he,?_,?_⟩
  · rw [hf740] at hnd
    unfold arithmeticBudget
    omega
  · refine ⟨hp,?_,(frame _ (by decide)).trans h713,(frame _ (by decide)).trans h714,
      (frame _ (by decide)).trans h715,(frame _ (by decide)).trans h716,
      (frame _ (by decide)).trans h717,hv728,?_,?_,?_,?_,?_⟩
    · intro i hi
      apply Eq.trans (frame _ ?_) (hlow i hi)
      intro h
      have hh := congrArg Fin.val h
      dsimp [LeafRingSetupProgram.wideStacks] at hh
      omega
    · intro i hi hj
      apply Eq.trans (frame i ?_) (hprivate i hi hj)
      intro h
      have hh : i.val=728 := congrArg Fin.val h
      omega
    · intro i hi h699 ho
      have h728' : i≠728 := by intro h; subst i; simp at ho
      rw [frame i h728']
      apply hhigh i hi h699
      intro hh
      apply ho
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hh ⊢
      rcases hh with hh|hh|hh|hh|hh
      · exact Or.inl hh
      · exact Or.inr (Or.inl hh)
      · exact Or.inr (Or.inr (Or.inl hh))
      · exact Or.inr (Or.inr (Or.inr (Or.inl hh)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))
    · intro i hi hj
      apply Eq.trans (frame i ?_) (hcollector i hi hj)
      intro h
      have hh : i.val=728 := congrArg Fin.val h
      omega
    · intro i hi hj
      exact (hdregs i hi).trans (hregs i hi hj)
    · intro i hi hz
      apply Eq.trans (frame i ?_) (hlowBlank i hi hz)
      intro h
      have hh : i.val=728 := congrArg Fin.val h
      omega
  · simpa only [hf740] using hinv

end SubexponentialSAT.SqrtLog.LeafProgram.Query

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramQueryDegreeRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Extra exact-byte certificate for the unchanged ring/interpolation command. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Query.Ring
open SubexponentialSAT BitProgram StructuredCalls LeafParametersProgram LeafRingSetupProgram

theorem command_eval_degree (base : Query.Data) (m : Circuit.Model)
    (w : Bank.Words) (r : Bank.Regs) (hs : Circuit.Shape m w)
    (ha : projectState (registers 8 (by decide)) parameters
      (projectState wideRegisters wideStacks base)=Bank.state r w)
    (W V L : ℕ) (hinit : ∀i,(base.stacks i).length ≤ W)
    (hv : ∀i,(Circuit.result Serialization.code m).val i ≤ V)
    (hw : ∀i,(Circuit.result Serialization.code m).len i ≤ L)
    (ht : 0 < m.val 33) (hd : 0 < m.val 34)
    (hexp : (Circuit.result Serialization.code m).val 44=3^(m.val 34)-2) :
    ∃ n ≤ budget m W V L, ∃ e : LeafRingSetupProgram.Data,
      ∃ (M : SubexpPreparedQuartic.Modulus 3 (m.val 33))
        (cache : RingProgram.ScalarCache 3 (m.val 33))
        (u : RingProgram.ScalarCode 3 (m.val 33)), ∃ out : Query.Data,
      Eval command n base out ∧ Produced m hd M cache u e ∧
      (∀i : Fin 640,i.val < 340 → out.stacks (wideStacks i)=e.stacks i) ∧
      out.stacks 713=InterpolationCacheProgram.inverseBytes (m.val 33) (IrreducibleSearch.data hd)
        M cache (LeafProgram.Constants.constantCode (m.val 34) cache.minusOne cache.zero)
        (nodeWords (m.val 33) (m.val 34) (m.val 21)) ∧
      out.stacks 714=InterpolationCacheProgram.negativeBytes (m.val 33) (IrreducibleSearch.data hd)
        M cache (LeafProgram.Constants.constantCode (m.val 34) cache.minusOne cache.zero)
        (nodeWords (m.val 33) (m.val 34) (m.val 21)) ∧
      out.stacks 715=InterpolationCacheProgram.differenceBytes (m.val 33) (IrreducibleSearch.data hd)
        M cache (LeafProgram.Constants.constantCode (m.val 34) cache.minusOne cache.zero)
        (nodeWords (m.val 33) (m.val 34) (m.val 21)) ∧
      out.stacks 716=List.replicate (m.val 21*(m.val 34*SubexpLiftRing.baseWidth 3 (m.val 33))) true ∧
      out.stacks 717=List.replicate (m.val 34*SubexpLiftRing.baseWidth 3 (m.val 33)) true ∧
      (∀i : Fin 768,340 ≤ i.val → i.val < 660 → out.stacks i=[]) ∧
      (∀i : Fin 768,660 ≤ i.val → i≠699 → i∉([713,714,715,716,717] : List (Fin 768)) →
        out.stacks i=base.stacks i) ∧
      (∀i : Fin 768,320 ≤ i.val → i.val < 340 → out.stacks i=base.stacks i) ∧
      (∀i : Fin 40,16 ≤ i.val → i.val < 24 → out.regs i=base.regs i) ∧
      (∀i : Fin 768,i.val < 190 → base.stacks i=[] → out.stacks i=[]) ∧
      out.stacks 204=List.replicate (m.val 34) true := by
  obtain ⟨nr,hnr,e,M,cache,u,her,hp,hregs,hhigh,hlow⟩ :=
    producerProgram_lifted base (projectState wideRegisters wideStacks base) rfl m w r hs ha
      W V L (fun i => hinit (wideStacks i)) hv hw ht hd
  let b := embedState wideRegisters wideStacks base e
  have hb (i : Fin 640) : b.stacks (wideStacks i)=e.stacks i :=
    embedState_stack _ _ _ _ wideStacks_injective i
  have hi := Interpolation.inputs_of_produced b e m hd M cache u hp hb hexp
  have hflat : b.stacks 256=(nodeWords (m.val 33) (m.val 34) (m.val 21)).flatMap RingProgram.flat := by
    rw [show b.stacks 256=e.stacks 256 from hb 256,hp.flatNodes]
    rw [List.flatMap_def]
  have hwidth : ∀i,(b.stacks i).length ≤ W+(producerBudget m W V L+1)+1 := by
    intro i
    have hh := Interpolation.eval_width her hinit i
    dsimp only [b]
    omega
  have hpos : 0 < m.val 34*SubexpLiftRing.baseWidth 3 (m.val 33) := by
    apply Nat.mul_pos hd
    unfold SubexpLiftRing.baseWidth
    exact Nat.mul_pos ht (Nat.succ_pos _)
  obtain ⟨ni,hni,out,hei,h713,h714,h715,h716,h717,hprivate,hframe,hiregs⟩ :=
    Interpolation.command_eval b (m.val 33) (IrreducibleSearch.data hd) M cache hp.caches.canonical
      (LeafProgram.Constants.constantCode (m.val 34) cache.minusOne cache.zero) hpos
      (nodeWords (m.val 33) (m.val 34) (m.val 21)) hi hflat
      (W+(producerBudget m W V L+1)+1) hwidth
  have outside (i : Fin 768) (hi : i.val < 340 ∨ 660 ≤ i.val) : i∉Interpolation.privatePorts := by
    simp only [Interpolation.privatePorts,List.mem_map,List.mem_finRange,true_and,not_exists]
    intro j hj
    have hh := congrArg Fin.val hj
    dsimp [Interpolation.localPorts] at hh
    omega
  refine ⟨nr+ni,?_,e,M,cache,u,out,her.seq hei,hp,?_,h713,h714,h715,?_,h717,?_,?_,?_,?_,?_,?_⟩
  · simp only [nodeWords_length] at hni
    dsimp only [budget]
    omega
  · intro i hi
    exact (hframe (wideStacks i) (outside _ (Or.inl hi))
      (by intro h; have := congrArg Fin.val h; dsimp [wideStacks] at this; omega)
      (by simp only [List.mem_cons,List.not_mem_nil,or_false];
          intro h; rcases h with h|h|h|h|h <;>
            have hh := congrArg Fin.val h <;> dsimp [wideStacks] at hh <;> omega)).trans (hb i)
  · simpa only [nodeWords_length] using h716
  · intro i hlo hhi
    let j : Fin 320 := ⟨i.val-340,by omega⟩
    have hj : Interpolation.localPorts j=i := by
      apply Fin.ext
      dsimp [Interpolation.localPorts,j]
      omega
    rw [← hj]
    exact hprivate _ (Interpolation.privatePorts_mem j)
  · intro i hi h699 ho
    exact (hframe i (outside i (Or.inr hi)) h699 ho).trans (hhigh i (by omega))
  · intro i hlo hhi
    let j : Fin 640 := ⟨i.val,by omega⟩
    have hj : wideStacks j=i := Fin.ext rfl
    have hf := hframe i (outside i (Or.inl hhi))
      (by intro h; have hh : i.val=699 := congrArg Fin.val h; omega)
      (by
        intro h
        have hlarge : 340 ≤ i.val := by
          simp only [List.mem_cons,List.not_mem_nil,or_false] at h
          rcases h with rfl|rfl|rfl|rfl|rfl <;> decide
        omega)
    exact hf.trans (by simpa only [hj] using hlow j hlo hhi)
  · intro i hlo hhi
    exact (hiregs i hlo (by omega)).trans (hregs i hlo hhi)

  · intro i hi hz
    have hbz := LowFrame.producerWideCall_empty base b nr her m w r hs ha W V L
      hinit hv hw ht hd i hi hz
    apply Eq.trans (hframe i (outside i (Or.inl (by omega))) ?_ ?_) hbz
    · intro h
      have hh : i.val=699 := congrArg Fin.val h
      omega
    · intro h
      have hh : 190 ≤ i.val := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at h
        rcases h with rfl|rfl|rfl|rfl|rfl <;> decide
      omega

  · have hdg := producerWideCall_degree base b nr her m w r hs ha W V L hinit hv hw ht hd
    exact (hframe 204 (outside _ (Or.inl (by decide))) (by decide) (by decide)).trans hdg

end SubexponentialSAT.SqrtLog.LeafProgram.Query.Ring

end OAI.Algorithms
end


