-- Prove2me | Definitions.Def_OAIQ081S093
-- name    : OAIQ081S093
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T22:14:04.717882+00:00
-- url     : https://prove2.me/theorems/bb2ed5fc-74e6-451f-9199-47d598f4adb3
-- title:
--   Definitions bundle OAIQ081S093 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 87 declarations of OpenAI's Lean: 57 definitions and 30 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.ClauseCount.small`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Expansion.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Expansion.reverseInput`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Expansion.reversedInput`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.FactorDispatch.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.FactorDispatch.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.FactorDispatch.copied`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.FactorDispatch.dispatch`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.LayoutMasters.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.LayoutMasters.LocalData`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.LayoutMasters.load`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.LayoutMasters.loadCost`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.LayoutMasters.loadLocal`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.LayoutMasters.loaded`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.LayoutMasters.parkCost`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.LayoutMasters.parkLocal`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.LayoutMasters.parked`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.SourceControls.cutoff`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.copied`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.emptyRange`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.regsState`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.scopeReset`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgram.clear`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgram.clearPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgram.clearPortsCost`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgram.clearResult`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgram.clearedPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgram.copy`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgram.counterCost`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgram.overwrite`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Arity.Code`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingLoaderProgram.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingLoaderProgram.framed`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCoefficientLiftProgram.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingNodeProgram.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingNodeProgram.loop`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingNodeProgram.ports`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingNodeProgram.preparedCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingNodeProgram.preparedProgram` and 17 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLogSpace_HighQueryAdapter`, `SubexponentialSAT_SqrtLog_LeafProgramClauseCount`, `SubexponentialSAT_SqrtLog_LeafProgramExpansion`, `SubexponentialSAT_SqrtLog_LeafProgramExpansionForward`, `SubexponentialSAT_SqrtLog_LeafProgramFactorDispatch`, `SubexponentialSAT_SqrtLog_LeafProgramLayoutMasters`, `SubexponentialSAT_SqrtLog_LeafProgramNodeFrames`, `SubexponentialSAT_SqrtLog_LeafProgramSourceControls`, `SubexponentialSAT_SqrtLog_LeafQueryFrontendConstants`, `SubexponentialSAT_SqrtLog_LeafQueryFrontendOps`, `SubexponentialSAT_SqrtLog_LeafQueryFrontendPorts`, `SubexponentialSAT_SqrtLog_LeafQueryFrontendState`, `SubexponentialSAT_SqrtLog_LeafRingSetupProgramNative`, `SubexponentialSAT_SqrtLog_LeafRingSetupProgramWords`, `SubexponentialSAT_SqrtLog_LeafStatisticsProgramArity`, `SubexponentialSAT_SqrtLog_PackingIncidenceInputPackingTransport`, `SubexponentialSAT_SqrtLog_PackingLoaderProgramFrame`, `SubexponentialSAT_SqrtLog_RingCoefficientLiftProgram`, `SubexponentialSAT_SqrtLog_RingNodeProgram`, `SubexponentialSAT_SqrtLog_RingNodeProgramPrepare`, `SubexponentialSAT_SqrtLog_RingProgramTableLoop`, `SubexponentialSAT_SqrtLog_RingProgramTableMachine`, `SubexponentialSAT_SqrtLog_RingProgramTablePowers`, `SubexponentialSAT_SqrtLog_RingProgramTableRound`, `SubexponentialSAT_SqrtLog_RingProgramTableSetup`, `SubexponentialSAT_SqrtLog_RingProgramTableStep`, `SubexponentialSAT_SqrtLog_RingTableLayoutProgram`, `SubexponentialSAT_SqrtLog_RingTableLayoutProgramBlock`, `SubexponentialSAT_SubexpArgumentProgram`, `SubexponentialSAT_SubexpEnumerationProgram`, `SubexponentialSAT_SubexpTaylorFrames`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S066`, `OAIQ081S067`, `OAIQ081S068`, `OAIQ081S069`, `OAIQ081S070`, `OAIQ081S071`, `OAIQ081S073`, `OAIQ081S075` and `OAIQ081S076` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S109`, `OAIQ081S110`, `OAIQ081S111`, `OAIQ081S112`, `OAIQ081S114` and `OAIQ081S123`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.accepted`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.marked`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCount.run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.accepted_replay`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.marked_replay` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram.clauseCount_eval`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S066
import Definitions.Def_OAIQ081S067
import Definitions.Def_OAIQ081S068
import Definitions.Def_OAIQ081S069
import Definitions.Def_OAIQ081S070
import Definitions.Def_OAIQ081S071
import Definitions.Def_OAIQ081S073
import Definitions.Def_OAIQ081S075
import Definitions.Def_OAIQ081S076

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighQueryAdapter
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete per-high-assignment setup and compressed head overlays.
The routines read physical counter/mask words and preserve ambient coordinates. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter

open OAI BitProgram StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram

abbrev Data := State 40 896

open OAI.Algorithms.SubexponentialSAT.StackRoutines


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramClauseCount
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Count the clauses in the actual emitted leaf. Both the preserving record
scan and unary-to-binary conversion are fixed native programs. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.ClauseCount

open SubexponentialSAT BitProgram StructuredCalls

def small (regs : Fin 8 → Bool) (formula unary : List Bool) : State 8 15 :=
  ⟨regs,![[],formula,unary,[],[],[],[],[],[],[],[],[],[],[],[]]⟩

end SubexponentialSAT.SqrtLog.LeafProgram.ClauseCount

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramExpansion
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native expansion of one selected raw hash row.  The row is read from the
dispatcher result; every original clause lookup and coefficient lift is paid
by the fixed assembler.  The original formula and dynamic width words are
read in place, so they remain available for the next factor. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Expansion

open SubexponentialSAT BitProgram StructuredCalls

abbrev Data := State 40 768

end SubexponentialSAT.SqrtLog.LeafProgram.Expansion

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramExpansionForward
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The preserved source lookup returns forward frame contents. Reverse this
actual tape before invoking the raw-tuple assembler. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Expansion
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

abbrev reverseInput : Cmd 40 768 :=
  .call (StackRoutines.reverseProgram 154 358 359 0 1)

def reversedInput (a : Data) : Data := afterReverse a 154 0 1

end SubexponentialSAT.SqrtLog.LeafProgram.Expansion

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramFactorDispatch
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The factor dispatcher in the native leaf's actual bank.  The parsed ID
is retained for incidence preparation.  The mark flag is read from a tape,
not inserted as a program parameter. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.FactorDispatch

open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

abbrev Data := State 40 768
abbrev dispatch : Cmd 40 768 :=
  .call (ProgramLinking.liftProgram LeafFactorDispatchProgram.program register stackMap)
abbrev command : Cmd 40 768 := .seq (.seq copyID readFlag) dispatch

def copied (a : Data) : Data := afterCopy a 149 152 0 1

end SubexponentialSAT.SqrtLog.LeafProgram.FactorDispatch

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpEnumerationProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Encoded interval enumeration by fixed finite control

A current label and a remaining count live on little-endian Boolean stacks.
The program invokes an actual body command once per label and advances using
verified finite-table increment/decrement routines.  Mathematical state
embeddings below occur only in execution proofs; no instruction evaluates an
arbitrary semantic function.
-/

namespace SubexponentialSAT.SubexpEnumerationProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredProgram
open SubexponentialSAT.CounterPrograms

variable {R S : ℕ}

/-- Actual complete carry/borrow trace, preserving the caller's flag bit. -/
theorem ripple_local_trace (c b present flag : Bool) (xs : List Bool) :
    Trace (rippleProgram c) (rippleCost c xs + 1)
      ((localData b present flag xs []).withPC (some (rippleProgram c).entry))
      ((localData false false flag (ripple c xs) []).withPC none) := by
  have h : Trace (rippleProgram c) (rippleCost c xs)
      (counterCfg 0 b present flag xs [])
      (counterCfg 10 false false flag (ripple c xs) []) := by
    simpa using ripple_trace c b present flag xs []
  exact h.trans (.cons (by simp [step, counterCfg, execInstr,
    localData, State.withPC]) (.refl _))

/-- Actual scan/restore trace, including the final halt instruction. -/
theorem zero_local_trace (b present flag : Bool) (xs : List Bool) :
    Trace zeroProgram (8 * xs.length + 6)
      ((localData b present flag xs []).withPC (some zeroProgram.entry))
      ((localData false false (isZero xs) xs []).withPC none) := by
  have h : Trace zeroProgram (8 * xs.length + 5)
      (counterCfg 0 b present flag xs [])
      (counterCfg 9 false false (isZero xs) xs []) := by
    simpa [Nat.add_assoc] using
      SubexponentialSAT.Computation.Trace.cons (zero_step0 b present flag xs [])
        (zero_scan_trace b present true xs [])
  exact h.trans (.cons (by simp [step, counterCfg, execInstr,
    localData, State.withPC]) (.refl _))

abbrev rippleCmd (p : Ports R S) (q c : Bool) : StructuredCalls.Cmd R S :=
  .call (ProgramLinking.liftProgram (rippleProgram c) p.register (stackPorts p q))

abbrev zeroCmd (p : Ports R S) : StructuredCalls.Cmd R S :=
  .call (ProgramLinking.liftProgram zeroProgram p.register (stackPorts p false))

theorem ripple_eval (p : Ports R S) (q c : Bool) (d : Data R S)
    (hs : d.stacks p.scratch = []) :
    StructuredCalls.Eval (rippleCmd p q c) (rippleCost c (d.stacks (target p q)) + 1)
      d (rippleResult p q c d) := by
  have h := StructuredCalls.eval_call_lifted (rippleProgram c) p.register (stackPorts p q) d
    p.register.injective (stackPorts p q).injective
    (ripple_local_trace c (d.regs (p.register 0)) (d.regs (p.register 1))
      (d.regs (p.register 2)) (d.stacks (target p q)))
  change StructuredCalls.Eval (rippleCmd p q c) _
    (install p q d _ _ _ _ []) (rippleResult p q c d) at h
  rw [← hs, install_self] at h
  exact h

theorem zero_eval (p : Ports R S) (d : Data R S) (hs : d.stacks p.scratch = []) :
    StructuredCalls.Eval (zeroCmd p) (8 * (d.stacks p.remaining).length + 6)
      d (zeroResult p d) := by
  have h := StructuredCalls.eval_call_lifted zeroProgram p.register (stackPorts p false) d
    p.register.injective (stackPorts p false).injective
    (zero_local_trace (d.regs (p.register 0)) (d.regs (p.register 1))
      (d.regs (p.register 2)) (d.stacks p.remaining))
  change StructuredCalls.Eval (zeroCmd p) _
    (install p false d _ _ _ _ []) (zeroResult p d) at h
  have hd : install p false d (d.regs (p.register 0)) (d.regs (p.register 1))
      (d.regs (p.register 2)) (d.stacks p.remaining) [] = d := by
    simpa [target, hs] using install_self p false d
  rw [hd] at h
  exact h

abbrev testCmd (p : Ports R S) : StructuredCalls.Cmd R S :=
  .seq (zeroCmd p) (.base (.atom (.bnot (p.register 2) (p.register 2))))

theorem test_eval (p : Ports R S) (d : Data R S) (hs : d.stacks p.scratch = []) :
    StructuredCalls.Eval (testCmd p) (8 * (d.stacks p.remaining).length + 7)
      d (testResult p d) := by
  have h := StructuredCalls.Eval.seq (zero_eval p d hs)
    (StructuredCalls.Eval.base (StructuredProgram.Eval.atom
      (.bnot (p.register 2) (p.register 2)) (zeroResult p d)))
  simpa only [testCmd, testResult, Nat.add_assoc] using h

end SubexponentialSAT.SubexpEnumerationProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramLayoutMasters
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Layout/source metadata are parked outside the native arithmetic bank.
CRT and scalar arithmetic use several ports128..141 as scratch; these values
are therefore physically reloaded for each node and cleared before CRT. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.LayoutMasters
open SubexponentialSAT BitProgram StructuredCalls SubexpSetupStorage

abbrev LocalData := State 16 768
abbrev Data := State 40 768

abbrev parkLocal : Cmd 16 768 := .seq (copyMany 684 parkPairs) (clearMany lowPorts)
abbrev loadLocal : Cmd 16 768 := copyMany 684 loadPairs
def parked (a : LocalData) := clearManyState lowPorts (copyManyState parkPairs a)
def loaded (a : LocalData) := copyManyState loadPairs a
def parkCost (a : LocalData) := copyManyCost parkPairs a+
  clearManyCost lowPorts (copyManyState parkPairs a)
def loadCost (a : LocalData) := copyManyCost loadPairs a

abbrev load : Cmd 40 768 := .call (ProgramLinking.liftProgram (compiled loadLocal 730 128) registers id)

end SubexponentialSAT.SqrtLog.LeafProgram.LayoutMasters

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpArgumentProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Finite-control serialization of marked-incidence arguments

The raw-list ABI is `Encoding.encodeList id` of record bodies
`frame key ++ frame coefficient`. Coefficient payloads are opaque bit strings.
The term writer consumes one coefficient frame and a reversed key, restoring
its scratch stacks. All loops below execute fixed Boolean/stack instructions.
-/

namespace SubexponentialSAT.SubexpArgumentProgram

open BitProgram StructuredCalls
open SubexpRecordScan

theorem writer_eval (outer : Bool) (d : Data) (bits : List Bool)
    (hkey : d.stacks 1 = bits.reverse) :
    Eval (.call (writer outer)) (5 * bits.length + 7) d (afterWriter outer d bits) := by
  let a := SubexpNormalizeProgram.filterState (d.regs 0) (d.regs 1) (d.regs 2)
    (d.stacks 0) (d.stacks 2) (d.stacks (destination outer)) bits.reverse
  let b := SubexpNormalizeProgram.filterState true false (d.regs 2)
    (d.stacks 0) (d.stacks 2)
    (true :: (Encoding.frame bits ++ d.stacks (destination outer))) []
  have ha : embedState writerRegs (writerStacks outer) d a = d := by
    apply embedState_eq _ _ writerRegs_injective (writerStacks_injective outer)
    · intro i; fin_cases i <;> rfl
    · intro i; fin_cases i <;> simp [a, writerStacks, SubexpNormalizeProgram.filterState,
        SubexpPostfixControl.quadruple, hkey]
    · intros; rfl
    · intros; rfl
  have hb : embedState writerRegs (writerStacks outer) d b = afterWriter outer d bits := by
    apply embedState_eq _ _ writerRegs_injective (writerStacks_injective outer)
    · intro i; fin_cases i <;>
        simp [ finishedRegs, writerRegs, b, SubexpNormalizeProgram.filterState,
          SubexpPostfixControl.triple]
    · intro i; cases outer <;> fin_cases i <;>
        simp [ writerStacks, destination, b, SubexpNormalizeProgram.filterState,
          SubexpPostfixControl.quadruple]
    · intro i hi
      have h0 : i ≠ 0 := fun h => hi ⟨0, h.symm⟩
      have h1 : i ≠ 1 := fun h => hi ⟨1, h.symm⟩
      simp [ finishedRegs, h0, h1]
    · intro i hi
      have h1 : i ≠ 1 := fun h => hi ⟨3, h.symm⟩
      have hd : i ≠ destination outer := fun h => hi ⟨2, h.symm⟩
      simp [ h1, hd]
  have ht : Trace SubexpNormalizeProgram.emitRecordProgram (5 * bits.length + 7)
      (a.withPC (some SubexpNormalizeProgram.emitRecordProgram.entry)) (b.withPC none) :=
    SubexpNormalizeProgram.emitRecord_trace bits (d.stacks 0) (d.stacks 2)
      (d.stacks (destination outer)) (d.regs 0) (d.regs 1) (d.regs 2)
  have h := eval_call_lifted SubexpNormalizeProgram.emitRecordProgram writerRegs
    (writerStacks outer) d writerRegs_injective (writerStacks_injective outer) ht
  simpa only [writer, ha, hb] using h

end SubexponentialSAT.SubexpArgumentProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpTaylorFrames
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed-control conversion of a flat coefficient stream into an ordered
list of framed coefficients. Runtime counters determine the coefficient
width and requested count. Missing high coefficients are actually read as
zero by the existing padded-reader program. -/

namespace SubexponentialSAT.SubexpTaylorFrames

open BitProgram StructuredCalls SubexpScanPrimitives
open SubexpExponentProgram

theorem paddedRead_eval (B : ℕ) (regs : Fin 5 → Bool) (w : Words)
    (hc : w.counter.length = B) :
    ∃ regs', Eval paddedRead (4 * B + 3) (state regs w)
      (state regs' {w with
        input := w.input.drop B
        counter := []
        payload := (padTake B w.input).reverse ++ w.payload}) := by
  obtain ⟨rr, hr⟩ := pad_counter_trace w.counter (regs ∘ padRegs) w.input w.payload
  rw [hc] at hr
  let regs' : Fin 5 → Bool := fun i => if i = 0 then rr 0 else if i = 1 then rr 1 else regs i
  let a : State 2 3 := ⟨regs ∘ padRegs,
    SubexpKeyPadProgram.storage w.input w.counter w.payload⟩
  let b : State 2 3 := ⟨rr,
    SubexpKeyPadProgram.storage (w.input.drop B) [] ((padTake B w.input).reverse ++ w.payload)⟩
  have ha : embedState padRegs padStacks (state regs w) a = state regs w := by
    apply embedState_eq _ _ padRegs_injective padStacks_injective
    · intro i; rfl
    · intro i; fin_cases i <;> simp [a, state, store, padStacks, SubexpKeyPadProgram.storage ]
    · intros; rfl
    · intros; rfl
  have hb : embedState padRegs padStacks (state regs w) b =
      state regs' {w with
        input := w.input.drop B
        counter := []
        payload := (padTake B w.input).reverse ++ w.payload} := by
    apply embedState_eq _ _ padRegs_injective padStacks_injective
    · intro i; fin_cases i <;> simp [regs', state, b, padRegs]
    · intro i; fin_cases i <;> simp [state, store, b, padStacks, SubexpKeyPadProgram.storage]
    · intro i hi
      have h0 : i ≠ 0 := fun h => hi ⟨0, h.symm⟩
      have h1 : i ≠ 1 := fun h => hi ⟨1, h.symm⟩
      simp [state, regs', h0, h1]
    · intro i hi
      have h0 : i ≠ 0 := fun h => hi ⟨0, h.symm⟩
      have h2 : i ≠ 2 := fun h => hi ⟨1, h.symm⟩
      have h4 : i ≠ 4 := fun h => hi ⟨2, h.symm⟩
      fin_cases i <;> simp_all [state, store]
  have he := eval_call_lifted SubexpKeyPadProgram.program padRegs padStacks (state regs w)
    padRegs_injective padStacks_injective (a := a) (b := b) hr
  exact ⟨regs', by simpa only [paddedRead, ha, hb] using he⟩

theorem writeRecord_eval (regs : Fin 5 → Bool) (w : Words) (bits : List Bool)
    (hp : w.payload = bits.reverse) :
    Eval writeRecord (5 * bits.length + 7) (state regs w)
      (state (SubexpArgumentProgram.finishedRegs regs)
        {w with payload := [], record := recordBytes bits ++ w.record}) := by
  let a : State 5 6 := ⟨regs, fun i => store w (writerStacks i)⟩
  have hr := SubexpArgumentProgram.writer_eval true a bits (by simpa [a, store, writerStacks] using hp)
  have ha : embedState id writerStacks (state regs w) a = state regs w := by
    apply embedState_eq _ _ Function.injective_id writerStacks_injective
    · intros; rfl
    · intros; rfl
    · intros; rfl
    · intros; rfl
  have hb : embedState id writerStacks (state regs w)
      (SubexpArgumentProgram.afterWriter true a bits) =
      state (SubexpArgumentProgram.finishedRegs regs)
        {w with payload := [], record := recordBytes bits ++ w.record} := by
    apply embedState_eq _ _ Function.injective_id writerStacks_injective
    · intro i; rfl
    · intro i; fin_cases i <;> simp [a,
        SubexpArgumentProgram.destination, state, store, writerStacks, recordBytes]
    · intro i hi; exact False.elim (hi ⟨i, rfl⟩)
    · intro i hi
      have h4 : i ≠ 4 := fun h => hi ⟨1, h.symm⟩
      have h5 : i ≠ 5 := fun h => hi ⟨3, h.symm⟩
      fin_cases i <;> simp_all [state, store]
  cases hr with
  | call _ ht =>
      have he := eval_call_lifted (SubexpArgumentProgram.writer true) id writerStacks
        (state regs w) Function.injective_id writerStacks_injective ht
      simpa only [writeRecord, ha, hb] using he

theorem one_eval (B : ℕ) (regs : Fin 5 → Bool) (w : Words)
    (hw : w.width.length = B) (hc : w.counter = [])
    (hp : w.payload = []) (hr : w.record = []) (hs : w.scratch = []) :
    ∃ regs', Eval one (22 * B + 24) (state regs w)
      (state regs' {w with
        input := w.input.drop B
        packed := (recordBytes (padTake B w.input)).reverse ++ w.packed}) := by
  let w1 := {w with counter := w.width}
  let w2 := {w1 with
    input := w.input.drop B
    counter := []
    payload := (padTake B w.input).reverse}
  let w3 := {w2 with payload := [], record := recordBytes (padTake B w.input)}
  have h1 := copy_eval (state regs w) 1 2 7 0 1
    (by decide) (by decide) (by decide) (by decide) (by simpa [state, store] using hs)
  have e1 : afterCopy (state regs w) 1 2 0 1 = state (readRegs regs 0 1 none) w1 := by
    apply state_ext
    · rfl
    · funext i; fin_cases i <;> simp [afterCopy, StackRoutines.copyStacks, state, store, w1, hc]
  rw [e1] at h1
  obtain ⟨r2, h2⟩ := paddedRead_eval B (readRegs regs 0 1 none) w1 hw
  have h2' : Eval paddedRead (4 * B + 3) (state (readRegs regs 0 1 none) w1)
      (state r2 w2) := by
    simpa only [w2, w1, hp, List.append_nil] using h2
  have h3 := writeRecord_eval r2 w2 (padTake B w.input) rfl
  have h3' : Eval writeRecord (5 * (padTake B w.input).length + 7)
      (state r2 w2) (state (SubexpArgumentProgram.finishedRegs r2) w3) := by
    simpa only [w3, w2, w1, hr, List.append_nil] using h3
  have h4 := transfer_eval (state (SubexpArgumentProgram.finishedRegs r2) w3) 5 6 0 1
    (by decide) (by decide)
  have e4 : afterTransfer (state (SubexpArgumentProgram.finishedRegs r2) w3) 5 6 0 1 =
      state (readRegs (SubexpArgumentProgram.finishedRegs r2) 0 1 none)
        {w with
          input := w.input.drop B
          packed := (recordBytes (padTake B w.input)).reverse ++ w.packed} := by
    apply state_ext
    · rfl
    · funext i; fin_cases i <;> simp [afterTransfer, StackRoutines.transferStacks,
        state, store, w3, w2, w1, hc, hp, hr]
  rw [e4] at h4
  refine ⟨readRegs (SubexpArgumentProgram.finishedRegs r2) 0 1 none, ?_⟩
  have he := h1.seq (h2'.seq (h3'.seq h4))
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  simp [ state, store, w1, w2, w3, hp, hr, hw, recordBytes,
    Encoding.length_frame, padTake_length, Nat.mul_add, Nat.add_assoc]
  omega

theorem loop_eval (width : List Bool) (n : ℕ) (input packed : List Bool) (regs : Fin 5 → Bool) :
    ∃ regs', Eval loop (n * (22 * width.length + 27) + 1)
      (state (readRegs regs 0 1 (List.replicate n true).head?) (data width n input packed))
      (state regs' (data width 0 (input.drop (n * width.length))
        ((framedBytes width.length n input).reverse ++ packed))) := by
  induction n generalizing input packed regs with
  | zero =>
      refine ⟨readRegs regs 0 1 none, ?_⟩
      simpa [loop, data, framedBytes, chunks] using
        (Eval.while_false (body := .seq popCount (.seq one guard))
          (a := state (readRegs regs 0 1 none) (data width 0 input packed))
          (by simp [state, readRegs]))
  | succ n ih =>
      let rs := readRegs regs 0 1 (some true)
      have hp := popCount_eval rs (data width (n + 1) input packed) true
        (List.replicate n true) rfl
      obtain ⟨r1, h1⟩ := one_eval width.length (readRegs rs 0 1 (some true))
        (data width n input packed) rfl rfl rfl rfl rfl
      have hg := guard_eval r1 (data width n (input.drop width.length)
        ((recordBytes (padTake width.length input)).reverse ++ packed))
      obtain ⟨rr, hr⟩ := ih (input.drop width.length)
        ((recordBytes (padTake width.length input)).reverse ++ packed) r1
      have ht : (state rs (data width (n + 1) input packed)).regs 1 = true := by
        simp [state, rs, readRegs]
      have hbody := hp.seq (h1.seq hg)
      have he := Eval.while_true ht hbody hr
      refine ⟨rr, ?_⟩
      convert he using 1 <;>
        simp [ data, rs, framedBytes, chunks, List.drop_drop,
          List.reverse_append, List.append_assoc, Nat.add_mul, Nat.add_comm,
          Nat.add_left_comm, Nat.add_assoc]
      all_goals first | rfl | omega

theorem command_eval (width : List Bool) (n : ℕ) (input : List Bool) (regs : Fin 5 → Bool) :
    ∃ regs', Eval command (n * (28 * width.length + 33) + 10)
      (state regs (data width n input []))
      (state regs' {data width 0 (input.drop (n * width.length)) [] with
        output := Encoding.encodeList id (chunks width.length n input)}) := by
  have hg := guard_eval regs (data width n input [])
  obtain ⟨rr, hl⟩ := loop_eval width n input [] regs
  have hf := finish_eval rr (data width 0 (input.drop (n * width.length))
    ((framedBytes width.length n input).reverse ++ [])) rfl
  refine ⟨readRegs (Function.update rr 0 false) 0 1 none, ?_⟩
  have he := hg.seq (hl.seq hf)
  convert he using 1
  · simp [data, framedBytes_length]
    ring
  · simp [data, encode_chunks]

theorem program_trace (width : List Bool) (n : ℕ) (input : List Bool) (regs : Fin 5 → Bool) :
    ∃ regs', Trace program (n * (28 * width.length + 33) + 11)
      ((state regs (data width n input [])).withPC (some program.entry))
      ((state regs' {data width 0 (input.drop (n * width.length)) [] with
        output := Encoding.encodeList id (chunks width.length n input)}).withPC none) := by
  obtain ⟨rr, hr⟩ := command_eval width n input regs
  exact ⟨rr, by simpa [Nat.add_assoc] using compiled_halt_trace hr 0 8⟩

end SubexponentialSAT.SubexpTaylorFrames

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramNodeFrames
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid conversion of flat fixed-width node words to framed node records.
Both the width and the number of nodes are read from runtime unary tapes. -/

namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeFrames

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpTaylorFrames
open SubexponentialSAT.SubexpExponentProgram

/-- Every output delimiter is written by the audited frame-producing loop. -/
theorem trace (width : List Bool) (words : List (List Bool))
    (hw : ∀ word ∈ words, word.length = width.length) (regs : Fin 5 → Bool) :
    ∃ finalRegs, Trace program (words.length * (28 * width.length + 33) + 11)
      ((state regs (data width words.length words.flatten [])).withPC (some program.entry))
      ((state finalRegs {data width 0 [] [] with
        output := Encoding.encodeList id words}).withPC none) := by
  obtain ⟨rf, he⟩ := program_trace width words.length words.flatten regs
  rw [chunks_flatten _ _ hw] at he
  have hdrop : words.flatten.drop (words.length * width.length) = [] := by
    rw [← flatten_length _ _ hw]
    simp
  exact ⟨rf, by simpa only [hdrop] using he⟩

end SubexponentialSAT.SqrtLog.LeafProgram.NodeFrames

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramSourceControls
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid source-control copies into the isolated 340-stack worker. All inputs
come from runtime layout/ring masters; no source polynomial is supplied. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.SourceControls
open SubexponentialSAT BitProgram StructuredCalls SubexpSetupStorage

/-- The source length is R+1, independently of the target Z-jet order. -/
abbrev cutoff : Cmd 16 768 := .seq (copyCmd 138 550 684)
  (.seq (.base (.atom (.set 0 true))) (.base (.atom (.push 550 0))))

end SubexponentialSAT.SqrtLog.LeafProgram.SourceControls

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafQueryFrontendPorts
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed disjoint work areas for the per-query native frontend. -/
namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
abbrev Data := State 40 768

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafQueryFrontendOps
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid copies and fixed constants used between frontend stages. -/
namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls

def copied (a : Data) (src dst : Fin 768) := SubexpScanPrimitives.afterCopy a src dst 0 1

@[simp] theorem copied_stack (a : Data) (src dst i : Fin 768) :
    (copied a src dst).stacks i = if i=dst then a.stacks src ++ a.stacks dst else a.stacks i := by
  simp [copied,SubexpScanPrimitives.afterCopy,StackRoutines.copyStacks,Function.update_apply]

def regsState (xs : List (StructuredProgram.Atom 40 768)) (a : Data) := SubexpParameterProgram.runAtoms xs a

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafStatisticsProgramArity
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Runtime outer record fold computing the maximum masked scope length and
factor count, including empty scope records. -/
namespace SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Arity
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
abbrev Code := Cmd 10 12

end SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Arity

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafQueryFrontendState
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Ordinary finite-window facts for the concrete frontend port maps. -/
namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls

def emptyRange (a : Data) (lo hi : ℕ) : Prop :=
  ∀ i : Fin 768, lo ≤ i.val → i.val < hi → a.stacks i=[]

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafQueryFrontendConstants
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls

def scopeReset (a : Data) : Data := regsState scopeResetAtoms a

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingProgramTableStep
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingProgramTable

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

abbrev nativeTriple : Cmd 8 27 := .call (ProgramLinking.liftProgram
  (compiled RingScan.tripleStep 8 0) id triplePorts)

/-- Assemble a triple from saved tail, next polynomial coefficient, and -1;
perform the native multiply-add; retain the last output and advance a's shift. -/
abbrev coefficientStep : Cmd 8 27 :=
  .seq (copy 17 9) (.seq (load 16 9) (.seq (copy 18 9)
    (.seq nativeTriple (.seq (clear 19) (.seq (copy 0 19)
      (.seq (transfer 0 20) (load 15 0)))))))


end SubexponentialSAT.SqrtLog.RingProgramTable

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingProgramTableLoop
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingProgramTable

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

abbrev coefficientLoop : Cmd 8 27 := .while 3 (.seq coefficientStep popCount)
abbrev coefficientScan : Cmd 8 27 := .seq popCount coefficientLoop

end SubexponentialSAT.SqrtLog.RingProgramTable

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafRingSetupProgramWords
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid word movement and binary-to-unary conversion used by ring setup.
The helpers update actual tapes; a state equality is never used as a free
copy, clear, or counter conversion. -/
namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram

open BitProgram StructuredCalls StackRoutines

abbrev clear (dst : Fin 640) : Cmd 32 640 :=
  .call (clearProgram dst 30 31)

abbrev copy (src dst : Fin 640) : Cmd 32 640 :=
  .call (copyProgram src dst 639 30 31)

theorem clear_eval (dst : Fin 640) (a : Data) :
    Eval (clear dst) (2*(a.stacks dst).length+3) a
      ⟨readRegs a.regs 30 31 none, Function.update a.stacks dst []⟩ :=
  Subexp.TupleProgram.clear_eval dst 30 31 a

theorem copy_eval (src dst : Fin 640) (a : Data)
    (hsd : src ≠ dst) (hs : src ≠ 639) (hd : (639 : Fin 640) ≠ dst)
    (hw : a.stacks 639 = []) :
    Eval (copy src dst) (7*(a.stacks src).length+5) a
      ⟨readRegs a.regs 30 31 none,
        Function.update a.stacks dst (a.stacks src ++ a.stacks dst)⟩ :=
  Subexp.TupleProgram.copy_eval src dst 639 30 31 hsd hs hd (by decide) a hw

abbrev overwrite (src dst : Fin 640) : Cmd 32 640 :=
  .seq (clear dst) (copy src dst)

/-- Clear the destination before copying.  This supports reuse of physical
scratch without requiring its previous value to vanish for free. -/
theorem overwrite_eval (src dst : Fin 640) (a : Data)
    (hsd : src ≠ dst) (hs : src ≠ 639) (hd : (639 : Fin 640) ≠ dst)
    (hw : a.stacks 639 = []) :
    Eval (overwrite src dst) (2*(a.stacks dst).length+7*(a.stacks src).length+8) a
      ⟨readRegs a.regs 30 31 none, Function.update a.stacks dst (a.stacks src)⟩ := by
  let b : Data := ⟨readRegs a.regs 30 31 none, Function.update a.stacks dst []⟩
  have hc := clear_eval dst a
  have hp := copy_eval src dst b hsd hs hd (by simpa [b, hd] using hw)
  convert hc.seq hp using 1 <;>
    simp [ b, hsd, readRegs_reset] ; omega

def clearPorts : List (Fin 640) → Cmd 32 640
  | [] => .base .skip
  | p :: ps => .seq (clear p) (clearPorts ps)

def clearResult (a : Data) (p : Fin 640) : Data :=
  ⟨readRegs a.regs 30 31 none, Function.update a.stacks p []⟩

def clearedPorts : List (Fin 640) → Data → Data
  | [], a => a
  | p :: ps, a => clearedPorts ps (clearResult a p)

def clearPortsCost : List (Fin 640) → Data → ℕ
  | [], _ => 0
  | p :: ps, a => 2*(a.stacks p).length+3+clearPortsCost ps (clearResult a p)

theorem clearPorts_eval (ps : List (Fin 640)) (a : Data) :
    Eval (clearPorts ps) (clearPortsCost ps a) a (clearedPorts ps a) := by
  induction ps generalizing a with
  | nil => exact .base (.skip _)
  | cons p ps ih => exact (clear_eval p a).seq (ih _)

theorem clearedPorts_stacks (ps : List (Fin 640)) (a : Data) (i : Fin 640) :
    (clearedPorts ps a).stacks i = if i ∈ ps then [] else a.stacks i := by
  induction ps generalizing a with
  | nil => simp [clearedPorts]
  | cons p ps ih =>
    simp only [clearedPorts, ih, List.mem_cons, clearResult]
    by_cases hi : i=p
    · subst i
      simp
    · by_cases hm : i ∈ ps <;> simp [hi,hm]

theorem clearPortsCost_bound (ps : List (Fin 640)) (a : Data) (W : ℕ)
    (hw : ∀ p ∈ ps, (a.stacks p).length ≤ W) :
    clearPortsCost ps a ≤ ps.length*(2*W+3) := by
  induction ps generalizing a with
  | nil => simp [clearPortsCost]
  | cons p ps ih =>
    have hp := hw p (by simp)
    have htail : ∀ q ∈ ps, ((clearResult a p).stacks q).length ≤ W := by
      intro q hq
      by_cases h : q=p
      · simp [clearResult,h]
      · simpa [clearResult,h] using hw q (by simp [hq])
    have ht := ih (clearResult a p) htail
    simp only [clearPortsCost, List.length_cons]
    nlinarith

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingCoefficientLiftProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


/-! A fixed scanner widens consecutive two-bit coefficients using a runtime
width tape. The original width is preserved, and all bit movement is paid. -/
namespace SubexponentialSAT.SqrtLog.RingCoefficientLiftProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.ModularPrograms
open SubexponentialSAT.Subexp.MatrixProgramSupport

abbrev Data := State 8 7

end SubexponentialSAT.SqrtLog.RingCoefficientLiftProgram


/-! Exact byte bridge from canonical F3 coefficients to the supplied-polynomial
ring model. The program itself has no degree or width parameter. -/


/-! Search-to-table ABI. The search has 22 registers and 28 stacks. In particular,
stack24 may contain unread candidates and is outside this adapter's ports. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingNodeProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed physical program generating all nonzero radix nodes up to a runtime
bound. The bound counts down, so prepending each row gives ascending order. -/
namespace SubexponentialSAT.SqrtLog.RingNodeProgram

open SubexponentialSAT BitProgram StructuredCalls CounterPrograms
open SubexpFieldRowPreparation SubexpBasePUnranking SubexpEnumerationProgram
open BinaryArithmetic SubexpLiftRing

/-- Only the remaining counter and its scratch are used by this controller. -/
def ports : Ports 8 15 where
  register := ⟨fun i => i.castLE (by decide), by intro i j h; exact Fin.ext (congrArg (fun x : Fin 8 => x.val) h)⟩
  current := 6
  remaining := 13
  scratch := 10
  current_ne_remaining := by decide
  current_ne_scratch := by decide
  remaining_ne_scratch := by decide

abbrev step : Cmd 8 15 := .seq SubexpFieldRowPreparation.command
  (.seq (rippleCmd ports false false) (testCmd ports))
abbrev loop : Cmd 8 15 := .while (ports.register 2) step
abbrev command : Cmd 8 15 := .seq (testCmd ports) loop

end SubexponentialSAT.SqrtLog.RingNodeProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingNodeProgramPrepare
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Constant-control preparation of the padded radix and the final node stream.
The only supplied words are zero padding, binary Q, and unary d. -/
namespace SubexponentialSAT.SqrtLog.RingNodeProgram

open SubexponentialSAT BitProgram StructuredCalls CounterPrograms
open SubexpFieldRowPreparation BinaryArithmetic SubexpLiftRing

abbrev preparedCommand : Cmd 8 15 := .seq prepareRadix command

def preparedProgram := compiled preparedCommand 13 12

end SubexponentialSAT.SqrtLog.RingNodeProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingProgramTableRound
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingProgramTable

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

abbrev round : Cmd 8 27 := .seq prepareRound (.seq coefficientScan finishVector)

end SubexponentialSAT.SqrtLog.RingProgramTable

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingProgramTablePowers
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingProgramTable

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

abbrev powerLoop : Cmd 8 27 := .while 3 (.seq round popRound)
abbrev powerScan : Cmd 8 27 := .seq popRound powerLoop

end SubexponentialSAT.SqrtLog.RingProgramTable

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingProgramTableSetup
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingProgramTable

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

abbrev preparePowers : Cmd 8 27 :=
  .seq initializeVector (.seq prepareRounds (.seq powerScan finishPowers))


def program := compiled preparePowers 8 0

end SubexponentialSAT.SqrtLog.RingProgramTable

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingTableLayoutProgramBlock
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingTableLayout

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

theorem finishBlock_eval (s : Store) (regs : Fin 2 → Bool) :
    Eval finishBlock (2*s.ii.length+4) (state regs s)
      (state (readRegs regs 0 1 none) {s with ii := [], ki := false :: s.ki}) := by
  let a := afterClear (state regs s) 15
  have h1 := clear_eval (state regs s) 15
  have h2 : Eval (.base (.atom (.push 14 0))) 1 a
      (state (readRegs regs 0 1 none) {s with ii := [], ki := false :: s.ki}) := by
    have h := StructuredProgram.Eval.atom (StructuredProgram.Atom.push (r := 2) (s := 18) 14 0) a
    apply Eval.base
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      fin_cases i <;> simp [a, afterClear, clearStacks, state, tapes, StructuredProgram.Atom.instr, execInstr, readRegs]
  convert h1.seq h2 using 1 ; simp [state, tapes]

end SubexponentialSAT.SqrtLog.RingTableLayout

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingTableLayoutProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A uniform finite program transforming power-major scalar records into the
k-major multiplication table. No dimension changes its finite control. -/
namespace SubexponentialSAT.SqrtLog.RingTableLayout

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

theorem finish_eval (s : Store) (regs : Fin 2 → Bool) :
    ∃ rf, Eval finish (2*s.ki.length + 3*s.rev.length + 6)
      (state regs s)
      (state rf {s with ki := [], rev := [], out := s.rev.reverse ++ s.out}) := by
  let d := state regs s
  let a := afterClear d 14
  have h1 := clear_eval d 14
  have h2 := transfer_eval a 17 3 (by decide)
  have hf : afterTransfer a 17 3 =
      state (afterTransfer a 17 3).regs {s with ki := [], rev := [], out := s.rev.reverse ++ s.out} := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      fin_cases i <;> simp [a, d, afterClear, clearStacks, transferStacks, state, tapes]
  refine ⟨(afterTransfer a 17 3).regs, ?_⟩
  rw [← hf]
  convert h1.seq h2 using 1
  all_goals try with_reducible_and_instances rfl
  simp [a, d, afterClear, clearStacks, state, tapes]
  omega

end SubexponentialSAT.SqrtLog.RingTableLayout

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingProgramTableMachine
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingProgramTable.Machine

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

abbrev prep : Cmd 8 42 := .call (ProgramLinking.liftProgram RingProgramTable.program id prepPorts)
abbrev command : Cmd 8 42 := .seq prep layout

def program := compiled command 27 0

end SubexponentialSAT.SqrtLog.RingProgramTable.Machine

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

def counterCost : List (Fin 640 × Fin 640) → (Fin 640 → List Bool) → ℕ
  | [],_ => 0
  | p::ps,s => LeafParametersProgram.Serialization.unaryCopyBound (s p.1)+1+
      counterCost ps (counterStack s p)

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingIncidenceInputPackingTransport
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Changing only the displayed incidence-list length transports the same
packing; numeric positions, labels, metadata bytes, and matrix values agree. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput
open SubexponentialSAT.Subexp SubexponentialSAT.Subexp.ConstructivePacking SubexponentialSAT.MulticolorTypes

variable {D E : ℕ} {U : Type*}

@[simp] theorem reindexPacking_metadataRecords [DecidableEq U] (h : D = E)
    (P : PackingData (Fin D) U) (encodeType : U → List Bool) :
    PackingMetadata.records (reindexPacking h P) (fun v => List.replicate v.val true) encodeType =
      PackingMetadata.records P (fun v => List.replicate v.val true) encodeType := by
  cases h
  rfl

@[simp] theorem reindexPacking_metadataBytes [DecidableEq U] (h : D = E)
    (P : PackingData (Fin D) U) (encodeType : U → List Bool) :
    SelectorProgram.rawRecords (PackingMetadata.records (reindexPacking h P)
      (fun v => List.replicate v.val true) encodeType) =
    SelectorProgram.rawRecords (PackingMetadata.records P
      (fun v => List.replicate v.val true) encodeType) := by
  rw [reindexPacking_metadataRecords]

variable {r Q : ℕ}

@[simp] theorem reindexPacking_localEntry (h : D = E)
    (P : PackingData (Fin D) (UniversalType r Q 1)) (A R : ℕ) (t : Fin Q) (i j : Fin E) :
    LayoutProgram.localEntry (reindexPacking h P) A R t i j =
      LayoutProgram.localEntry P A R t (Fin.cast h.symm i) (Fin.cast h.symm j) := by
  cases h
  rfl

@[simp] theorem reindexPacking_entryNat (h : D = E)
    (P : PackingData (Fin D) (UniversalType r Q 1)) (A R : ℕ) (t : Fin Q) (i j : ℕ) :
    BucketProgram.ProducedRank.entryNat (reindexPacking h P) A R t i j =
      BucketProgram.ProducedRank.entryNat P A R t i j := by
  cases h
  rfl

end SubexponentialSAT.SqrtLog.PackingIncidenceInput

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingLoaderProgramFrame
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Framing and paid parameter serialization for the packing loader. -/
namespace SubexponentialSAT.SqrtLog.PackingLoaderProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
abbrev Data := State 16 64

noncomputable def framed (outside : Store) (d : State 16 48) : Data :=
  embedState id lowPorts (⟨d.regs,outside⟩ : Data) d

@[simp] theorem framed_regs (outside : Store) (d : State 16 48) :
    (framed outside d).regs=d.regs := by
  funext i
  exact embedState_register id lowPorts (⟨d.regs,outside⟩ : Data) d Function.injective_id i

@[simp] theorem framed_low (outside : Store) (d : State 16 48) (i : Fin 48) :
    (framed outside d).stacks (lowPorts i)=d.stacks i :=
  embedState_stack id lowPorts (⟨d.regs,outside⟩ : Data) d lowPorts.injective i

theorem framed_outside (outside : Store) (d : State 16 48) (i : Fin 64)
    (hi : ¬ ∃ j, lowPorts j=i) : (framed outside d).stacks i=outside i :=
  embedState_stack_frame id lowPorts (⟨d.regs,outside⟩ : Data) d i hi

@[simp] theorem embed_framed (outside : Store) (a b : State 16 48) :
    embedState id lowPorts (framed outside a) b=framed outside b := by
  apply embedState_eq_of_ports id lowPorts _ _ b Function.injective_id lowPorts.injective
  · intro i; simp
  · intro i hi; exact (hi ⟨i,rfl⟩).elim
  · intro i; exact framed_low outside b i
  · intro i hi
    rw [framed_outside outside b i hi,framed_outside outside a i hi]

end SubexponentialSAT.SqrtLog.PackingLoaderProgram

end OAI.Algorithms
end


