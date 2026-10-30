-- Prove2me | Definitions.Def_OAIQ081S173
-- name    : OAIQ081S173
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T23:21:05.114079+00:00
-- url     : https://prove2.me/theorems/068d55b7-b887-494e-9e64-4b33303ccb46
-- title:
--   Definitions bundle OAIQ081S173 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 21 declarations of OpenAI's Lean: 10 definitions and 11 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutDenominatorProgramQuery.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutDenominatorProgramQuery.localCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutDenominatorProgramQuery.localProgram`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Execute.bitBound`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Execute.runtimeBound`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports.clearModelBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports.exportFieldBound`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Layout.guardedBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.Data`, `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowProgram.encodeFactor`.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: [`SubexponentialSAT_SqrtLogSpace_HighQuerySetup`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HighQuerySetup.lean), [`SubexponentialSAT_SqrtLog_IdempotentPreparationProgram`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/IdempotentPreparationProgram.lean), [`SubexponentialSAT_SqrtLog_IdempotentProgramComplete`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/IdempotentProgramComplete.lean), [`SubexponentialSAT_SqrtLog_IdempotentProgramFinal`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/IdempotentProgramFinal.lean), [`SubexponentialSAT_SqrtLog_InterpolationCacheProgramPairs`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/InterpolationCacheProgramPairs.lean), [`SubexponentialSAT_SqrtLog_InterpolationCacheProgramPass`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/InterpolationCacheProgramPass.lean), [`SubexponentialSAT_SqrtLog_InterpolationCacheProgramRows`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/InterpolationCacheProgramRows.lean), [`SubexponentialSAT_SqrtLog_LayoutDenominatorProgramQueryCode`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutDenominatorProgramQueryCode.lean), [`SubexponentialSAT_SqrtLog_LeafParametersProgramExports`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafParametersProgramExports.lean), [`SubexponentialSAT_SqrtLog_LeafParametersProgramNative`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafParametersProgramNative.lean), [`SubexponentialSAT_SubexpKernelControl`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SubexpKernelControl.lean), [`SubexponentialSAT_Subexp_UniversalRowProgram`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/Subexp/UniversalRowProgram.lean).
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S166`, `OAIQ081S167`, `OAIQ081S168` and `OAIQ081S169` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S180`, `OAIQ081S181`, `OAIQ081S182`, `OAIQ081S183` and `OAIQ081S185`; the statements `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.parameterCall_eval` and `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowFactorLoop.loop_indices_eval`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.accepted`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.marked`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCount.run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.accepted_replay`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.marked_replay`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.literal_cleanup_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.uncovered_cleanup`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceExpression.literal_length_le_sourceLengthBound` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.parameterCall_eval`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S166
import Definitions.Def_OAIQ081S167
import Definitions.Def_OAIQ081S168
import Definitions.Def_OAIQ081S169

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

/-! A fixed ten-comparison bit guard. All operands are runtime binary words.
This module states their data relation separately from parameter production. -/


namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Layout

open Circuit Bank BinaryArithmetic Asymptotic

def guardedBudget (x : Input) (l : Fin 8 → ℕ) :=
  Circuit.budget guardedCode (initialModel x l)

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Layout


/- Component: SubexponentialSAT.SqrtLog.LeafParametersProgramDispatchCost -/

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Execute

open BitProgram StructuredCalls BinaryArithmetic Bank Circuit

def bitBound (x : Input) (l : Fin 8 → ℕ) : ℕ :=
  iterMajorant Layout.guardedCode.length (Layout.setupScale x l)

def runtimeBound (x : Input) (l : Fin 8 → ℕ) : ℕ :=
  Prepared.runtimeBound x l+100*bitBound x l+83

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Execute


/- Component: SubexponentialSAT.SqrtLog.LeafParametersProgramPublic -/


end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParametersProgramExports
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native cache preparation, persistent metadata export, and bank restoration.
The guard register is framed. Unary cache tapes are cleared after copying so
ring setup again receives the ordinary binary parameter model. -/
namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports
open BitProgram StructuredCalls BinaryArithmetic Bank Circuit
noncomputable section
attribute [local simp] Fin.coe_ofNat_eq_mod

def exportFieldBound (m : Model) (i : Fin 16) : ℕ :=
  if i.val < 5 then Cache.unaryBound (m.val (localSource i)) (m.len (localSource i))
  else 7*cacheLength m (localSource i)+5

def clearModelBudget (m : Model) : ℕ :=
  2*((List.finRange 18).map (fun i => cacheLength m ⟨46+i.val,by omega⟩)).sum+57

end
end SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutDenominatorProgramQueryCode
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The per-query denominator is computed in a disjoint 256-stack bank. The
only persistent output is stack 728; the runtime exponent is read from 740. -/
namespace SubexponentialSAT.SqrtLog.LayoutDenominatorProgramQuery
open SubexponentialSAT BitProgram StructuredCalls SubexpSetupStorage

abbrev localCommand : Cmd 16 768 := .seq (copyMany 460 pairs)
  (.seq nativeCall (.seq (copyCmd 592 728 460) (clearMany bank)))

def localProgram := compiled localCommand 740 728
abbrev command : Cmd 40 768 := .call (ProgramLinking.liftProgram localProgram registers id)

end SubexponentialSAT.SqrtLog.LayoutDenominatorProgramQuery

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentPreparationProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! One fixed native preparation command accepts only the runtime binary
precision. It constructs its modulus, scalar cache, table, arrays and counters
with charged bit instructions, ready for the fixed Newton program. -/
namespace SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

open BitProgram StructuredCalls SubexpQuarticRing

theorem preparation_eval (bits : List Bool) (t : ℕ)
    (hv : CounterPrograms.value bits=t) (ht : 0 < t) :
    ∃ n e, ∃ (M : SubexpPreparedQuartic.Modulus 3 t),
      ∃ (cache : RingProgram.ScalarCache 3 t) (u : RingProgram.ScalarCode 3 t),
      Eval preparation n (inputData bits) e ∧ Ready t bits.length M cache u e ∧
        n ≤ preparationBudget t bits.length := by
  obtain ⟨M,logword,nb,rb,hlog,hlen,hnb,heb⟩ := boot_eval bits t hv ht
  let a : Data := ⟨rb,bootStacks t bits M.bits logword⟩
  let W := 2*t+bits.length
  have hshape : (List.replicate (2*t) true).length=SubexpLiftRing.baseWidth 3 t := by
    simp [RingProgram.ternary_baseWidth]
  have hrest : Scalar.Rest a M.bits := by
    constructor
    · intro i; fin_cases i <;> simp [a,Scalar.low,bootStacks]
    · simp [a,bootStacks]
  have hslots : ∀ i, (a.stacks (Scalar.port i)).length ≤ W := by
    intro i
    fin_cases i <;> simp [a,Scalar.port,bootStacks,W]
  obtain ⟨ns,b,cache,u,hes,hp,hframe,hns⟩ := Scalar.command_prepares t ht M
    (List.replicate (2*t) true) hshape a W hrest
    (by simp [a,bootStacks]) (by simp [W]) hslots
    (by simp [a,bootStacks]) (by simp [a,bootStacks])
  have frame : ∀ j, (∀ i, Scalar.port i≠j) → b.stacks j=bootStacks t bits M.bits logword j :=
    hframe
  have h12 : b.stacks 12=List.replicate (2*t) true := by
    rw [frame 12 (by intro i; fin_cases i <;> decide)]
    simp [bootStacks]
  have h37 : b.stacks 37=List.replicate (3*t) true := by
    rw [frame 37 (by intro i; fin_cases i <;> decide)]
    simp [bootStacks]
  have h39 : b.stacks 39=logword := by
    rw [frame 39 (by intro i; fin_cases i <;> decide)]
    simp [bootStacks]
  have empty : ∀ p ∈ ([22,26,32,33,34,35,36] : List (Fin 41)), b.stacks p=[] := by
    intro p hmem
    have hf : ∀ i, Scalar.port i≠p := by
      intro i he
      rw [←he] at hmem
      fin_cases i <;> simp [Scalar.port] at hmem
    rw [frame p hf]
    fin_cases p <;> simp_all [bootStacks]
  have hW : ∀ p ∈ preparationDiscard, (b.stacks p).length ≤ W := by
    intro p hmem
    by_cases hport : ∃ i, Scalar.port i=p
    · obtain ⟨i,rfl⟩ := hport
      have hb := prepared_pool_length t M cache u b hp i
      rw [RingProgram.ternary_baseWidth] at hb
      dsimp [W]; omega
    · rw [frame p (by intro i he; exact hport ⟨i,he⟩)]
      by_cases h31 : p = 31
      · subst p
        simp [bootStacks, W]
      by_cases h29 : p = 29
      · subst p
        simp [bootStacks, W] ; omega
      have h5 : p ≠ 5 := by
        intro h
        subst p
        simp [preparationDiscard] at hmem
      have h12 : p ≠ 12 := by
        intro h
        subst p
        simp [preparationDiscard] at hmem
      have h37 : p ≠ 37 := by
        intro h
        subst p
        simp [preparationDiscard] at hmem
      have h39 : p ≠ 39 := by
        intro h
        subst p
        simp [preparationDiscard] at hmem
      simp [bootStacks, h31, h29, h5, h12, h37, h39]
  obtain ⟨nf,e,hnf,hef,hfinished⟩ := finishCommand_eval t ht M cache u b hp W h37
    (empty 26 (by simp)) (empty 22 (by simp)) (empty 32 (by simp))
    (empty 33 (by simp)) (empty 34 (by simp)) (empty 35 (by simp)) (empty 36 (by simp)) hW
  have enc := finished_encoded t ht M cache u b e hp h12 h37 hfinished
  have hcounter := finished_counter t b e _ hfinished
  refine ⟨nb+(ns+nf),e,M,cache,u,heb.seq (hes.seq hef),?_,?_⟩
  · refine ⟨enc,hp.zeroCanonical,hp.inverse,?_,?_,hcounter.2⟩
    · simpa [hcounter.1,h39] using hlog
    · simpa [hcounter.1,h39] using hlen
  · have hs := Scalar.budget_polynomial t W
    dsimp [preparationBudget,W] at *
    omega

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentProgramFinal
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete native Newton lift and the exact degree-three coefficient output.
The input-state contract includes prepared scalar constants and the cached
H-adic table; native preparation is a separate remaining construction. -/
namespace SubexponentialSAT.SqrtLog.IdempotentProgram

open scoped BigOperators
open BitProgram StructuredCalls SubexpSymbolicCost
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

attribute [local instance] OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentProgram.ternaryPrimeFinal
/-- An actual fixed finite bit program computes every Newton iteration and all
array arithmetic from the supplied prepared state. -/
theorem nativeLiftWords_run (t : ℕ) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t)
    (hz : BinaryArithmetic.toNat cache.zero.val < 3^t)
    (u : RingProgram.ScalarCode 3 t)
    (degree width : List Bool) (hd : degree.length = 3*t) (hw : width.length = baseWidth 3 t)
    (regs : Registers (RingProgram.Code (RingProgram.ScalarCode 3 t) (3*t)))
    (state : RegisterData)
    (encoded : RegistersEncoded M.bits width cache.zero.val
      (RingTriple.tableEncoding (tableCode (t:=t) (RingProgram.scalarProgram 3 t M cache))) degree
      (minusOneRun (RingProgram.scalarProgram 3 t M cache) t).1 regs state)
    (hinitial : regs 0 = (initialRun (RingProgram.scalarProgram 3 t M cache) t u).1)
    (hcounter : CounterPrograms.value (state.stacks 39) = Nat.clog 2 t)
    (hs : state.stacks 40 = []) :
    ∃ next : RegisterData, RunsIn newtonProgram (nativeLiftBudget t (state.stacks 39).length)
      (state.withPC (some newtonProgram.entry)) (next.withPC none) ∧
      next.stacks 32 = RingProgram.flat (binaryLiftWords t M cache u) := by
  obtain ⟨n,next,he,henc,hn⟩ := newtonMachine_exact 3 t M cache hz
    (tableCode (t:=t) (RingProgram.scalarProgram 3 t M cache))
    (zeroCode (RingProgram.scalarProgram 3 t M cache) t)
    (oneCode (RingProgram.scalarProgram 3 t M cache) t)
    (minusOneRun (RingProgram.scalarProgram 3 t M cache) t).1
    degree width hd hw regs state encoded hs
  refine ⟨next, ⟨n+1, ?_, compiled_halt_trace he 32 32⟩, ?_⟩
  · simpa only [nativeLiftBudget, hcounter] using Nat.add_le_add_right hn 1
  · have ho := henc.values 0
    rw [liftCode_result, hcounter, hinitial] at ho
    exact ho

end SubexponentialSAT.SqrtLog.IdempotentProgram


end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentProgramComplete
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed finite bit program constructs the ternary H-adic lift from its
binary precision alone. Preparation, array arithmetic, iteration and output
serialization are all covered by actual bit-instruction traces. -/
namespace SubexponentialSAT.SqrtLog.IdempotentProgram

open scoped BigOperators
open BitProgram StructuredCalls SubexpQuarticRing

/-- The input has only the binary precision in stack 31. No arithmetic table,
constants, counter, advice or other prepared data is supplied to the machine. -/
theorem completeProgram_runs (bits : List Bool) (t : ℕ)
    (hv : CounterPrograms.value bits=t) (ht : 0 < t) :
    ∃ next : RegisterData, ∃ (M : SubexpPreparedQuartic.Modulus 3 t),
      ∃ (cache : RingProgram.ScalarCache 3 t) (u : RingProgram.ScalarCode 3 t),
      RunsIn completeProgram (completeBudget t bits.length)
        ((IdempotentPreparationProgram.inputData bits).withPC (some completeProgram.entry))
        (next.withPC none) ∧
      next.stacks 32=RingProgram.flat (binaryLiftWords t M cache u) ∧
      (2 : ZMod (3^t))*wordValue 3 t u=1 := by
  obtain ⟨np,prepared,M,cache,u,hp,ready,hnp⟩ :=
    IdempotentPreparationProgram.preparation_eval bits t hv ht
  obtain ⟨next,⟨nl,hnl,hl⟩,hout⟩ := nativeLiftWords_run t M cache ready.zeroCanonical u
    (List.replicate (3*t) true) (List.replicate (2*t) true)
    (by simp) (by simp [RingProgram.ternary_baseWidth])
    (IdempotentPreparationProgram.initialRegisters t M cache u) prepared
    ready.encoded rfl ready.counter ready.loopScratch
  have hbound := nativeLiftBudget_mono t ready.counterLength
  refine ⟨next,M,cache,u,⟨np+nl+1,?_,?_⟩,hout,ready.inverse⟩
  · unfold completeBudget
    omega
  · exact compiled_halt_trace (hp.seq (Eval.call newtonProgram hl)) 31 32

end SubexponentialSAT.SqrtLog.IdempotentProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_InterpolationCacheProgramPass
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Packed scans starting from a preserved node master. -/
namespace SubexponentialSAT.SqrtLog.InterpolationCacheProgram
open SubexponentialSAT BitProgram StructuredCalls

theorem mapScan_run {C : Type*} (encode : C → List Bool) (f : C → C) (W K : ℕ)
    (hW : 0 < W) (hwidth : ∀x,(encode x).length=W)
    (src dst arg : Fin 320) (hp : MapPorts src dst arg)
    (service : Code) (P : Store → Prop)
    (stable : ∀s i v,P s → i∈([src,dst,arg,208] : List (Fin 320)) → P (Function.update s i v))
    (hspec : ∀s x,P s → s arg=encode x → s 208=[] →
      Runs service K s (Function.update s 208 (encode (f x))))
    (s : Store) (xs : List C) (hP : P s) (hsrc : s src=xs.flatMap encode)
    (harg : s arg=[]) (hresult : s 208=[])
    (h104 : (s 104).length=W) (h270 : s 270=[]) (h271 : s 271=[]) :
    Runs (mapScan src dst arg service) (xs.length*(K+19*W+19)+2) s
      (Function.update (Function.update s src []) dst
        ((xs.flatMap fun x => encode (f x)).reverse++s dst)) := by
  intro r
  obtain ⟨n,rf,hn,he⟩ := mapLoop_run encode f W K hW hwidth src dst arg hp service P stable
    hspec s xs hP hsrc harg hresult h104 h270 h271 r
  exact ⟨1+n,rf,by omega,(peek_eval s r src).seq he⟩

theorem scanMaster_run {C : Type*} (encode : C → List Bool) (f : C → C) (W K : ℕ)
    (hW : 0 < W) (hwidth : ∀x,(encode x).length=W)
    (src dst arg : Fin 320) (hp : MapPorts src dst arg) (h256 : (256:Fin 320)≠src)
    (service : Code) (P : Store → Prop)
    (stable : ∀s i v,P s → i∈([src,dst,arg,208] : List (Fin 320)) → P (Function.update s i v))
    (hspec : ∀s x,P s → s arg=encode x → s 208=[] →
      Runs service K s (Function.update s 208 (encode (f x))))
    (s : Store) (xs : List C) (hP : P s) (hmaster : s 256=xs.flatMap encode)
    (hsrc : s src=[]) (harg : s arg=[]) (hresult : s 208=[])
    (h104 : (s 104).length=W) (h270 : s 270=[]) (h271 : s 271=[]) :
    Runs (scanMaster src dst arg service) (xs.length*(K+26*W+19)+7) s
      (Function.update s dst ((xs.flatMap fun x => encode (f x)).reverse++s dst)) := by
  have hs270 : (270:Fin 320)≠src := hp.ne (by decide : (1:Fin 7)≠3)
  let mid := Function.update s src (xs.flatMap encode)
  have h1 : Runs (copy 256 src) (7*(xs.length*W)+5) s mid := by
    simpa only [mid,hmaster,hsrc,List.append_nil,flatMap_length encode W hwidth] using
      copy_run s 256 src h256 (by decide) hs270 h270
  have h2 := mapScan_run encode f W K hW hwidth src dst arg hp service P stable hspec mid xs
    (stable _ src _ hP (by simp)) (by simp [mid])
    (by simp [mid,(show arg≠src from hp.ne (by decide : (5:Fin 7)≠3)),harg])
    (by simp [mid,(show (208:Fin 320)≠src from hp.ne (by decide : (6:Fin 7)≠3)),hresult])
    (by simpa only [mid,Function.update_of_ne ((show (104:Fin 320)≠src from hp.ne (by decide : (0:Fin 7)≠3)))] using h104)
    (by simpa only [mid,Function.update_of_ne hs270] using h270)
    (by simpa only [mid,Function.update_of_ne ((show (271:Fin 320)≠src from hp.ne (by decide : (2:Fin 7)≠3)))] using h271)
  have hend : Function.update (Function.update mid src []) dst
      ((xs.flatMap fun x => encode (f x)).reverse++mid dst) =
      Function.update s dst ((xs.flatMap fun x => encode (f x)).reverse++s dst) := by
    simp only [mid,Function.update_idem,Function.update_of_ne (show dst≠src from hp.ne (by decide : (4:Fin 7)≠3))]
    rw [←hsrc,Function.update_eq_self]
  rw [hend] at h2
  exact (h1.seq h2).mono (by nlinarith)

end SubexponentialSAT.SqrtLog.InterpolationCacheProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_InterpolationCacheProgramRows
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native scans for inverse nodes, negative nodes, and a complete row of
pairwise difference inverses. -/
namespace SubexponentialSAT.SqrtLog.InterpolationCacheProgram
open SubexponentialSAT BitProgram StructuredCalls
open SubexpLiftRing

theorem inverseScan_run (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (hz : BinaryArithmetic.toNat cache.zero.val < 3^t) (minusOne : Coeff t d)
    (hW : 0 < d*baseWidth 3 t) (s : Store) (xs : List (Coeff t d))
    (hready : Ready t a M cache minusOne s) (hm : s 256=xs.flatMap RingProgram.flat)
    (hsrc : s 257=[]) (harg : s 213=[]) (hresult : s 208=[])
    (hother : s 218=RingProgram.flat (RingProgram.modelProgram t a M cache).zeroRun.1) :
    Runs inverseScan (nodeScanBudget (inverseBudget t d) (d*baseWidth 3 t) xs.length) s
      (Function.update s 259 ((xs.flatMap fun x => RingProgram.flat (inverseValue t a M cache minusOne x)).reverse++s 259)) := by
  apply scanMaster_run RingProgram.flat (inverseValue t a M cache minusOne) _ _ hW
    RingProgram.flat_length 257 259 213 (by unfold MapPorts; decide) (by decide) inverseCommand
    (fun s => Ready t a M cache minusOne s ∧ s 218=RingProgram.flat (RingProgram.modelProgram t a M cache).zeroRun.1)
    ?_ ?_ s xs ⟨hready,hother⟩ hm hsrc harg hresult hready.width
    (hready.scratch 270 (by decide)) (hready.scratch 271 (by decide))
  · intro s i v h hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl
    all_goals exact ⟨h.1.update_controller _ v (by decide),by simpa using h.2⟩
  · intro s x h hx hr
    exact h.1.inverse_run hz x _ hx h.2 hr

theorem rowScan_run (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (hz : BinaryArithmetic.toNat cache.zero.val < 3^t) (minusOne x : Coeff t d)
    (hW : 0 < d*baseWidth 3 t) (s : Store) (xs : List (Coeff t d))
    (hready : Ready t a M cache minusOne s) (hm : s 256=xs.flatMap RingProgram.flat)
    (hsrc : s 258=[]) (harg : s 218=[]) (hresult : s 208=[])
    (htheta : s 213=RingProgram.flat x) :
    Runs rowScan (nodeScanBudget (inverseBudget t d) (d*baseWidth 3 t) xs.length) s
      (Function.update s 261 ((xs.flatMap fun y => RingProgram.flat (differenceValue t a M cache minusOne x y)).reverse++s 261)) := by
  apply scanMaster_run RingProgram.flat (differenceValue t a M cache minusOne x) _ _ hW
    RingProgram.flat_length 258 261 218 (by unfold MapPorts; decide) (by decide) inverseCommand
    (fun s => Ready t a M cache minusOne s ∧ s 213=RingProgram.flat x)
    ?_ ?_ s xs ⟨hready,htheta⟩ hm hsrc harg hresult hready.width
    (hready.scratch 270 (by decide)) (hready.scratch 271 (by decide))
  · intro s i v h hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl
    all_goals exact ⟨h.1.update_controller _ v (by decide),by simpa using h.2⟩
  · intro s y h hy hr
    exact h.1.inverse_run hz x y h.2 hy hr

end SubexponentialSAT.SqrtLog.InterpolationCacheProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_InterpolationCacheProgramPairs
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Nested native scans producing the full row-major difference-inverse
array. Every diagonal cell is computed by the same total inverse routine. -/
namespace SubexponentialSAT.SqrtLog.InterpolationCacheProgram
open SubexponentialSAT BitProgram StructuredCalls StackRoutines
open SubexpLiftRing

theorem pairStep_run (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (hz : BinaryArithmetic.toNat cache.zero.val < 3^t) (minusOne x : Coeff t d)
    (hW : 0 < d*baseWidth 3 t) (s : Store) (xs : List (Coeff t d)) (rest : List Bool)
    (hr : Ready t a M cache minusOne s) (hm : s 256=xs.flatMap RingProgram.flat)
    (hsrc : s 257=RingProgram.flat x++rest)
    (hclean : ∀i∈([208,213,218,258] : List (Fin 320)),s i=[]) :
    Runs pairStep (nodeScanBudget (inverseBudget t d) (d*baseWidth 3 t) xs.length+16*(d*baseWidth 3 t)+14) s
      (Function.update (Function.update s 257 rest) 261 ((rowBytes t a M cache minusOne xs x).reverse++s 261)) := by
  let s1 := Function.update (Function.update s 257 rest) 213 (RingProgram.flat x)
  let s2 := Function.update s1 261 ((rowBytes t a M cache minusOne xs x).reverse++s 261)
  have h1 : Runs (take 257 213) (14*(d*baseWidth 3 t)+11) s s1 := by
    simpa only [s1,hclean 213 (by simp),List.append_nil,RingProgram.flat_length] using
      take_run s 257 213 (by decide) (RingProgram.flat x) rest hsrc
        (hr.width.trans (RingProgram.flat_length x).symm)
        (hr.scratch 270 (by decide)) (hr.scratch 271 (by decide))
  have hr1 : Ready t a M cache minusOne s1 :=
    (hr.update_controller 257 rest (by decide)).update_controller 213 _ (by decide)
  have h2 : Runs rowScan (nodeScanBudget (inverseBudget t d) (d*baseWidth 3 t) xs.length) s1 s2 := by
    have hs1 : s1 261 = s 261 := by simp [s1]
    simpa only [s2, rowBytes, hs1] using
      rowScan_run t a M cache hz minusOne x hW s1 xs hr1
        (by simpa [s1] using hm) (by simpa [s1] using hclean 258 (by simp))
        (by simpa [s1] using hclean 218 (by simp))
        (by simpa [s1] using hclean 208 (by simp)) (by simp [s1])
  have h3 : Runs (clear 213) (2*(d*baseWidth 3 t)+3) s2 (Function.update s2 213 []) := by
    simpa [s2,s1,RingProgram.flat_length] using clear_run s2 213
  have he : Function.update s2 213 []=
      Function.update (Function.update s 257 rest) 261 ((rowBytes t a M cache minusOne xs x).reverse++s 261) := by
    funext i
    by_cases hi : i=213
    · subst i; simp [s2,s1,hclean 213 (by simp)]
    · simp [s2,s1,Function.update_apply,hi]
  rw [he] at h3
  exact (h1.seq (h2.seq h3)).mono (by omega)

end SubexponentialSAT.SqrtLog.InterpolationCacheProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpKernelControl
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# A fixed controller constructing the separated postfix source

The input contains literal payloads and the three nested lists of blocks,
color groups, and terms.  The controller only parses frames, copies bits,
and emits postfix tags.  It has no arithmetic callback and never builds a
Cartesian product of the inner lists.  Three unary stacks hold the pending
right-fold operators, so the emitted source has exactly the association of
`SubexpAlgorithm.momentExpression`.
-/

namespace SubexponentialSAT.SubexpKernelControl

open BitProgram StructuredCalls

/-! ## Fixed source-constructor control -/

/-! ## Concrete machine states and elementary traces -/

@[simp] theorem setCounter_emit (i : Fin 3) (word code : Word) (a : Accumulator) :
    setCounter i word (emit code a) = emit code (setCounter i word a) := by
  fin_cases i <;> rfl

/-! The following induction rule accounts for actual executions of the fixed
payload body. Its premises will be proved for `termBody`, `groupBody`, and
`blockBody`; the exported whole-controller statement has no callback argument. -/

@[simp] theorem counterWord_emit (i : Fin 3) (code : Word) (a : Accumulator) :
    counterWord i (emit code a) = counterWord i a := by
  fin_cases i <;> simp [counterWord, emit]

/-! ## Forward-output service boundary -/

@[simp] theorem pushWord_length (x : Word) : (pushWord x).length = 2 * x.length + 2 := by
  simp [pushWord]

end SubexponentialSAT.SubexpKernelControl

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_UniversalRowProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Physical source construction for universal interpolation rows

The input holds raw coefficient payloads, node inverses, and negative nodes.
It does not contain polynomial instructions. Fixed nested scans emit the
Lagrange products and correction sum as postfix source in canonical list order.
The surrounding row-data producer supplies the selected mismatch positions;
its matrix, cache, and type-mask construction is tracked separately.
-/

namespace SubexponentialSAT.Subexp.UniversalRowProgram

open BitProgram StructuredCalls
open SubexpKernelControl (Word Accumulator pushWord operator operators emit state counterWord setCounter counterPort popTag unframe emitFramedLiteral emitLiteral
  emitOperator countOne drain scan )

def encodeFactor (f : Factor Word) : Word :=
  Encoding.frame f.inverseDifference ++ Encoding.frame f.negativeNode

end SubexponentialSAT.Subexp.UniversalRowProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighQuerySetup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete preparation and fresh high-counter initialization for the fixed
marked and accepted queries. The witness below is produced by the actual
programs; no implementation or evaluator is supplied as a hypothesis. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup

open OAI BitProgram StructuredCalls SqrtLog LeafParametersProgram
open LeafProgram.Query HashGreedyProgram.NativeRound
open HighMarkedFrontend

abbrev Data := State 40 896

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup
end


