-- Prove2me | Definitions.Def_OAIQ081S106
-- name    : OAIQ081S106
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T22:23:47.267964+00:00
-- url     : https://prove2.me/theorems/9598ae3f-de26-4774-aa13-ccb7951234c0
-- title:
--   Definitions bundle OAIQ081S106 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 64 declarations of OpenAI's Lean: 30 definitions and 34 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchPairAdapter.input`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchPairAdapter.output`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgram.ArithmeticReady`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgram.EntryAt`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgram.Ready`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgram.bank`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgram.data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgram.moved`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgram.ownerResult`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgram.parked`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutMatrixProgram.parsed`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOffsetProgram.bank`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOffsetProgram.clearMany`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOffsetProgram.clearOne`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOffsetProgram.filled`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOffsetProgram.initial`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOffsetProgram.input`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOffsetProgram.loaded`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOffsetProgram.result`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Circuit.Shape`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.state`, `OAI.Algorithms.SubexponentialSAT.Subexp.PackingOutputSemantics.finish`, `OAI.Algorithms.SubexponentialSAT.Subexp.PackingOutputSemantics.packedSnapshot`, `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowFactorLoop.callback`, `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowFactorLoop.loop`, `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowLoop.loop`, `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowProgram.termBody`, `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowTermProgram.command`, `OAI.Algorithms.SubexponentialSAT.SubexpBlockParameterProgram.inputWords`, `OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage.WordBound`.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLog_IrreducibleSearchPairAdapter`, `SubexponentialSAT_SqrtLog_LayoutFiberSumProgram`, `SubexponentialSAT_SqrtLog_LayoutFiberSumProgramBasic`, `SubexponentialSAT_SqrtLog_LayoutFiberSumProgramLoop`, `SubexponentialSAT_SqrtLog_LayoutFiberSumProgramMove`, `SubexponentialSAT_SqrtLog_LayoutMatrixProgramPrimitives`, `SubexponentialSAT_SqrtLog_LayoutOffsetProgram`, `SubexponentialSAT_SqrtLog_LayoutOffsetProgramRun`, `SubexponentialSAT_SqrtLog_LayoutProgramPackLabels`, `SubexponentialSAT_SqrtLog_LeafParametersProgramNative`, `SubexponentialSAT_SqrtLog_MomentsProgramProduct`, `SubexponentialSAT_SubexpBlockParameterProgram`, `SubexponentialSAT_SubexpSetupStorageCost`, `SubexponentialSAT_Subexp_BlockSearchProgram`, `SubexponentialSAT_Subexp_BucketProgram`, `SubexponentialSAT_Subexp_CandidateScoreProgram`, `SubexponentialSAT_Subexp_MatrixProgramSupport`, `SubexponentialSAT_Subexp_PackingAddressSemantics`, `SubexponentialSAT_Subexp_PackingBucketCalls`, `SubexponentialSAT_Subexp_PackingMetadata`, `SubexponentialSAT_Subexp_PackingOutputSemantics`, `SubexponentialSAT_Subexp_PackingVertexLabels`, `SubexponentialSAT_Subexp_SelectorMapProgram`, `SubexponentialSAT_Subexp_TupleProgram`, `SubexponentialSAT_Subexp_UniversalRowExecution`, `SubexponentialSAT_Subexp_UniversalRowFactorLoop`, `SubexponentialSAT_Subexp_UniversalRowLoop`, `SubexponentialSAT_Subexp_UniversalRowTermProgram`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S083`, `OAIQ081S084`, `OAIQ081S085`, `OAIQ081S087`, `OAIQ081S088`, `OAIQ081S089`, `OAIQ081S090` and `OAIQ081S091` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S122`, `OAIQ081S123`, `OAIQ081S124`, `OAIQ081S125`, `OAIQ081S126`, `OAIQ081S127`, `OAIQ081S130`, `OAIQ081S132` and `OAIQ081S134`; the statements `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader.shift_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Execution.HashParameters.command_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.WeightedCore.command_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgram.addEntry_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgram.command_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgram.query_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.stageCost_linear`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram.stage_bounded_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.keyPhase_eval` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.scalePhase_eval`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram.Rescan.body_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram.Rescan.prepareKey_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.HeadGate.keyCall_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureKeyNative.run`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram.preMatrixProgram_runsIn`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram.preScan_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.WeightedCallbacks.accumulate_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.WeightedCallbacks.complement_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgram.addEntry_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgram.command_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgram.query_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup.Native.command_eval_found`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram.stage_bounded_eval` and `OAI.Algorithms.SubexponentialSAT.Subexp.MatrixVectorProgram.matrix_trace`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S083
import Definitions.Def_OAIQ081S084
import Definitions.Def_OAIQ081S085
import Definitions.Def_OAIQ081S087
import Definitions.Def_OAIQ081S088
import Definitions.Def_OAIQ081S089
import Definitions.Def_OAIQ081S090
import Definitions.Def_OAIQ081S091

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_TupleProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed-control Cartesian tuple generation

Alphabet words, tuple payloads, and iteration depths are stack data.  The
instruction tables below do not depend on any of their lengths.
-/

namespace SubexponentialSAT.Subexp.TupleProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

/-! The fixed ABI uses ten Boolean registers and nine Boolean stacks:
0 prior tuples, 1 saved alphabet, 2 current reversed tuple, 3 alphabet cursor,
4 reversed word, 5 output, 6 copied tuple, 7 copy scratch, 8 unary depth.
Registers 0--2 and 3--5 belong to the two framed iterators, 6--7 are scratch,
and 8--9 belong to the eventual depth loop. -/

theorem expandStep_eval (alphabet rows : Records) (depth : List Bool) (guard : Bool)
    (a : State 10 9) (ha : Ready alphabet rows depth guard a) :
    ∃ n next, n ≤ stepCost rows alphabet ∧
      Ready alphabet (cartesianOutput rows alphabet) depth guard next ∧
      Eval expandStep n a next := by
  obtain ⟨n, b, hn, hb, hb0, hb2, hb5, ht⟩ :=
    cartesian_eval rows alphabet [] depth guard a ha.1 ha.2.1 ha.2.2.1 ha.2.2.2
  simp only [List.append_nil] at hb5
  let c : State 10 9 :=
    ⟨readRegs b.regs 6 7 none, StackRoutines.transferStacks 5 6 b.stacks⟩
  let d : State 10 9 :=
    ⟨readRegs c.regs 6 7 none, StackRoutines.transferStacks 6 0 c.stacks⟩
  let e := pushedState 5 6 false d
  have h1 := transfer_eval 5 6 6 7 (by decide) (by decide) b
  have h2 := transfer_eval 6 0 6 7 (by decide) (by decide) c
  have h3 := pushConst_eval 5 6 false d
  refine ⟨n + ((3 * (b.stacks 5).length + 3) + (3 * (c.stacks 6).length + 3 + 2)),
    e, ?_, ?_, ht.seq (h1.seq (h2.seq h3))⟩
  · have hc6 : (c.stacks 6).length = (b.stacks 5).length := by
      simp [c, StackRoutines.transferStacks, hb.2.2.2.1]
    rw [hc6, hb5]
    dsimp [stepCost]
    omega
  · rcases hb with ⟨hba, hb3, hb4, hb6, hb7, hb8, hb9⟩
    simp [Ready, outerInvariant, e, d, c, StackRoutines.transferStacks,
      readRegs, hba, hb3, hb4, hb6, hb7, hb8, hb9, hb0, hb2, hb5]

theorem powerCmd_eval (alphabet rows : Records) (depth : List Bool) (guard : Bool)
    (a : State 10 9) (ha : Ready alphabet rows depth guard a) :
    ∃ n next, n ≤ powerCost alphabet depth.length rows ∧
      Ready alphabet (powerRows alphabet depth.length rows) [] false next ∧
      Eval powerCmd n a next := by
  induction depth generalizing rows guard a with
  | nil =>
      let b := readDepthState a
      have hb : Ready alphabet rows [] false b := by
        rcases ha with ⟨⟨h1,h3,h4,h6,h7,h8,h9⟩,h0,h2,h5⟩
        simp [Ready, outerInvariant, b, readRegs,
          h1,h3,h4,h6,h7,h8,h0,h2,h5]
      refine ⟨2, b, le_rfl, hb, ?_⟩
      exact (readDepth_eval a).seq (Eval.while_false hb.1.2.2.2.2.2.2)
  | cons bit depth ih =>
      let b := readDepthState a
      have hb : Ready alphabet rows depth true b := by
        rcases ha with ⟨⟨h1,h3,h4,h6,h7,h8,h9⟩,h0,h2,h5⟩
        simp [Ready, outerInvariant, b, readRegs,
          h1,h3,h4,h6,h7,h8,h0,h2,h5]
      obtain ⟨n, c, hn, hc, ht⟩ := expandStep_eval alphabet rows depth true b hb
      obtain ⟨m, d, hm, hd, hr⟩ := ih (cartesianOutput rows alphabet) true c hc
      cases hr with
      | @seq first second k l x y z hp hl =>
          refine ⟨1 + (n + k + l + 1), d, ?_, hd, ?_⟩
          · simp only [List.length_cons, powerCost]
            omega
          · exact (readDepth_eval a).seq
              (Eval.while_true hb.1.2.2.2.2.2.2 (ht.seq hp) hl)

theorem generateProgram_runsIn (alphabet : Records) (depth : List Bool) (guard : Bool)
    (a : State 10 9) (ha : outerInvariant alphabet depth guard a)
    (h0 : a.stacks 0 = []) (h2 : a.stacks 2 = []) (h5 : a.stacks 5 = []) :
    ∃ next, Ready alphabet (powerRows alphabet depth.length [[]]) [] false next ∧
      RunsIn generateProgram (powerCost alphabet depth.length [[]] + 9)
        (a.withPC (some generateProgram.entry)) (next.withPC none) := by
  obtain ⟨b,hb,hi⟩ := initCmd_eval alphabet depth guard a ha h0 h2 h5
  obtain ⟨n,next,hn,hs,he⟩ := powerCmd_eval alphabet [[]] depth guard b hb
  refine ⟨next,hs,8+n+1,by omega,?_⟩
  exact StructuredCalls.compiled_halt_trace (hi.seq he) 1 0

end SubexponentialSAT.Subexp.TupleProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IrreducibleSearchPairAdapter
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed physical split of a concatenated pair of coefficient arrays. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchPairAdapter

open BitProgram StructuredCalls SubexpSetupStorage IrreducibleSearchProgram

def input (as bs : List IrreducibleSearch.F) (count : List Bool)
    (regs : Fin 16 → Bool) : State 16 6 :=
  ⟨regs, ![coefficientArray (as ++ bs), count, [], [], [], []]⟩
def output (as bs : List IrreducibleSearch.F) (count : List Bool)
    (regs : Fin 16 → Bool) : State 16 6 :=
  ⟨regs, ![coefficientArray bs, count, [], [], coefficientArray as, []]⟩

end SubexponentialSAT.SqrtLog.IrreducibleSearchPairAdapter

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutFiberSumProgramBasic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native owner-fiber summation helpers. The remaining fiber is a stream of
actual unary index fields, never an array of precomputed matrix entries. -/
namespace SubexponentialSAT.SqrtLog.LayoutFiberSumProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open RowSelectionProgram

/-- Only the arithmetic scratch bank must be empty. The entry callback may
require the stronger condition that all stacks below 200 are empty. -/
def ArithmeticReady (base : Data) : Prop :=
  ∀ i : Fin 256, i.val < 11 → base.stacks i = []

def bank (base : Data) (queue column : List Bool) (acc next : WordPair) :
    Fin 256 → List Bool := fun i =>
  if i=212 then acc.1 else if i=213 then acc.2 else if i=214 then queue else
  if i=253 then column else if i=254 then next.1 else if i=255 then next.2 else base.stacks i

def data (base : Data) (regs : Fin 16 → Bool) (queue column : List Bool)
    (acc next : WordPair) : Data := ⟨regs,bank base queue column acc next⟩

end SubexponentialSAT.SqrtLog.LayoutFiberSumProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutFiberSumProgramLoop
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutFiberSumProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls RowSelectionProgram

/-- A concrete entry command, with explicit execution and frame obligations.
No list of entries is an input to the fiber machine. -/
def EntryAt (entry : Code) (base : Data) (value : ℕ → ℤ) (T B M i : ℕ) : Prop :=
  ∀ (regs : Fin 16 → Bool) (queue : List Bool) (acc : WordPair),
    ∃ n ≤ T, ∃ rf result,
      Eval entry n (data base regs queue (unary i) acc ([],[]))
        (data base rf queue (unary i) acc result) ∧
      pairValue result=value i ∧ pairLength result ≤ B ∧ pairTotal result.1 result.2 ≤ M

end SubexponentialSAT.SqrtLog.LayoutFiberSumProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_BucketProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# A fixed bit program for one packing bucket

The input is a framed query followed by framed `(type key, vertex payload)`
records. The routine compares actual bit strings. It consumes all records,
keeps the query on port 2, and prepends matching framed payloads on port 5.
Supplying records in reverse vertex order produces the original bucket order.
-/

namespace SubexponentialSAT.Subexp.BucketProgram

open BitProgram StructuredProgram StructuredCalls SubexpRecordScan

/-- An actual structured execution of the EOF-controlled loop. -/
theorem scanLoop_eval (regs : Fin 5 → Bool) (rs : List Record) (query output : List Bool) :
    ∃ n ≤ loopBudget rs query, ∃ regs',
      StructuredCalls.Eval scanLoop n (ready regs rs query output)
        (recordState regs' [] [] query.reverse [] [] (scanOutput rs query output)) := by
  induction rs generalizing regs output with
  | nil =>
    refine ⟨1, le_rfl, (ready regs [] query output).regs, ?_⟩
    simpa [scanLoop, ready, encodeRecords, scanOutput, selected, frames] using
      (StructuredCalls.Eval.while_false (test := (1 : Fin 5)) (body := loopBody)
        (ready_guard_nil regs query output))
  | cons row rs ih =>
    rcases row with ⟨key, payload⟩
    let rr := (ready regs ((key, payload) :: rs) query output).regs
    let out := if key = query then Encoding.frame payload ++ output else output
    obtain ⟨nr, hnr, regs₁, he⟩ :=
      oneRecord_eval rr key query payload (encodeRecords rs) output
    have hrecord : StructuredCalls.Eval oneRecord nr
        (ready regs ((key, payload) :: rs) query output)
        (recordState regs₁ (encodeRecords rs) [] query.reverse [] [] out) := by
      simpa only [ready, encodeRecords, rr, out] using he.1
    have hpeek := peekInput_eval regs₁ rs query out
    obtain ⟨nt, hnt, regs₂, ht⟩ := ih regs₁ out
    have hbody : StructuredCalls.Eval loopBody (nr + 1)
        (ready regs ((key, payload) :: rs) query output) (ready regs₁ rs query out) :=
      StructuredCalls.Eval.seq hrecord hpeek
    have hw := StructuredCalls.Eval.while_true
      (ready_guard_cons regs key payload rs query output) hbody ht
    refine ⟨(nr + 1) + nt + 1, ?_, regs₂, ?_⟩
    · simp only [loopBudget]
      omega
    · simpa only [scanLoop, scanOutput_cons, out] using hw

theorem scan_eval (regs : Fin 5 → Bool) (rs : List Record) (query output : List Bool) :
    ∃ n ≤ 1 + loopBudget rs query, ∃ regs',
      StructuredCalls.Eval scan n
        (recordState regs (encodeRecords rs) [] query.reverse [] [] output)
        (recordState regs' [] [] query.reverse [] [] (scanOutput rs query output)) := by
  obtain ⟨n, hn, regs', he⟩ := scanLoop_eval regs rs query output
  exact ⟨1 + n, Nat.add_le_add_left hn 1, regs',
    StructuredCalls.Eval.seq (peekInput_eval regs rs query output) he⟩

end SubexponentialSAT.Subexp.BucketProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixProgramSupport
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed stack and frame-reading routines used by the encoded matrix checker. -/

namespace SubexponentialSAT.Subexp.MatrixProgramSupport

open BitProgram StructuredCalls

variable {s : ℕ}

/-- Consume a raw word and prepend its complete frame, with every encoding
step performed by fixed instructions. -/
theorem emitFrame_eval (src dst tmp : Fin s) (hsd : src ≠ dst) (hst : src ≠ tmp)
    (htd : tmp ≠ dst) (d : Data s) (ht : d.stacks tmp = []) :
    ∃ e, Eval (emitFrame src dst tmp htd) (8 * (d.stacks src).length + 8) d e ∧
      e.stacks = Function.update (Function.update d.stacks src []) dst
        (Encoding.frame (d.stacks src) ++ d.stacks dst) := by
  obtain ⟨a, ha, hsa⟩ := transfer_eval src tmp hst d
  let b := TupleProgram.pushedState dst 0 false a
  let e := TupleProgram.escapedState (fieldPorts tmp dst htd) b
  have hb := TupleProgram.pushConst_eval dst (0 : Fin 8) false a
  have he := TupleProgram.escape_eval_state (fieldPorts tmp dst htd) b
  have ht' : b.stacks tmp = (d.stacks src).reverse := by
    simp only [b, Function.update_apply, hsa]
    simp [ ht, htd]
  have htlen : (b.stacks (fieldPorts tmp dst htd).source).length =
      (d.stacks src).length := by
    simpa only [fieldPorts, List.length_reverse] using congrArg List.length ht'
  refine ⟨e, ?_, ?_⟩
  · have hh := Eval.seq ha (Eval.seq hb he)
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    omega
  · simp only [e, b, fieldPorts, hsa]
    funext j
    by_cases hjd : j = dst
    · subst j
      simp [StackRoutines.transferStacks, ht, Ne.symm hsd,
        htd, Ne.symm htd, TupleProgram.frame_eq_escaped,
        List.append_assoc]
    · by_cases hjs : j = src
      · subst j
        simp [StackRoutines.transferStacks, ht, hsd, hst, htd, Ne.symm htd]
      · by_cases hjt : j = tmp
        · subst j
          simp [StackRoutines.transferStacks, ht, Ne.symm hst,
            htd, Ne.symm htd]
        · simp [StackRoutines.transferStacks, hjd, hjs, hjt]

end SubexponentialSAT.Subexp.MatrixProgramSupport

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_SelectorMapProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# A fixed loop applying the selected-index map to query records

The selector uses ports 0--5.  Port 6 is the framed query cursor, port 7
preserves the raw key/payload table, and port 8 accumulates framed answers.
Answers are prepended, so the returned record list reverses query order.
-/

namespace SubexponentialSAT.Subexp.SelectorMapProgram

open BitProgram StructuredCalls

theorem selector_eval (records : List (List Bool × List Bool)) (query : List Bool)
    (regs : Fin 8 → Bool) (cursor table acc : List Bool) :
    ∃ n ≤ SelectorProgram.budget query records, ∃ localRegs tail,
      tail.length ≤ (SelectorProgram.rawRecords records).length + n ∧
      Eval (.call selector) n
        (state regs (SelectorProgram.rawRecords records) [] query.reverse [] [] [] cursor table acc)
        (state (mergeRegs regs localRegs) tail (selected records query).reverse query.reverse
          [] [] [] cursor table acc) := by
  obtain ⟨n, hn, localRegs, tail, ht⟩ :=
    SelectorProgram.program_trace query records (fun i => regs (lowRegs i))
  have htail := trace_stack_bound SelectorProgram.program ht 0
  let a := state regs (SelectorProgram.rawRecords records) [] query.reverse [] [] [] cursor table acc
  let b := state (mergeRegs regs localRegs) tail (selected records query).reverse query.reverse
    [] [] [] cursor table acc
  have ha : embedState lowRegs lowStacks a
      (SubexpRecordScan.recordState (fun i => regs (lowRegs i))
        (SelectorProgram.rawRecords records) [] query.reverse [] [] []) = a := by
    apply embed_eq _ _ lowRegs_injective lowStacks_injective
    · intro i; fin_cases i <;> rfl
    · intro i; fin_cases i <;> rfl
    · intros; rfl
    · intros; rfl
  have hb : embedState lowRegs lowStacks a
      (SubexpRecordScan.recordState localRegs tail (selected records query).reverse query.reverse [] [] []) = b := by
    apply embed_eq _ _ lowRegs_injective lowStacks_injective
    · intro i; fin_cases i <;> rfl
    · intro i; fin_cases i <;> rfl
    · intro j hj
      fin_cases j <;> simp_all [lowRegs, mergeRegs, state, a, b, Fin.exists_fin_succ]
    · intro j hj
      fin_cases j <;> simp_all [lowStacks, state, a, b, Fin.exists_fin_succ]
  refine ⟨n, hn, localRegs, tail, ?_, ?_⟩
  · simpa [SubexpRecordScan.recordState, StructuredProgram.State.withPC] using htail
  · have h := eval_call_lifted SelectorProgram.program lowRegs lowStacks a
      lowRegs_injective lowStacks_injective ht
    change Eval (.call selector) n _
      (embedState lowRegs lowStacks a
        (SubexpRecordScan.recordState localRegs tail (selected records query).reverse
          query.reverse [] [] [])) at h
    rw [ha, hb] at h
    exact h

end SubexponentialSAT.Subexp.SelectorMapProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingVertexLabels
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Gathering the actual assignment type at every vertex before packing. -/

namespace SubexponentialSAT.Subexp.PackingVertexLabels

open BitProgram StructuredCalls MatrixProgramSupport

/-- Each callback consumes the actual framed plan, performs the persistent
array reads, and prepends one raw `(type, vertex)` record. -/
theorem callback_eval (rows : List (List Bool)) (width : List Bool) (plan : List ℕ)
    (regs : Fin 8 → Bool) (source records : List Bool) (index : ℕ)
    (hrows : ∀ row ∈ rows, row.length = width.length)
    (hplan : ∀ i ∈ plan, i < rows.length) :
    ∃ (n : ℕ) (rf : Fin 8 → Bool),
      Eval callback n
        (state regs rows.flatten [] width [] source (planPayload plan).reverse
          (List.replicate index true) records [])
        (state rf rows.flatten [] width [] source [] (List.replicate (index+1) true)
          (Encoding.frame (GatherProgram.gathered rows plan) ++
            (Encoding.frame (List.replicate index true) ++ records)) []) ∧
      rf 5 = false ∧ rf 6 = true ∧ rf 7 = false ∧
      n ≤ callbackCost width.length (planBytes plan).length index := by
  let a := state regs rows.flatten [] width [] source (planPayload plan).reverse
    (List.replicate index true) records []
  obtain ⟨b, hab, hb⟩ := transfer_eval (11 : Fin 15) 14 (by decide) a
  have hbe : b = state b.regs rows.flatten [] width [] source []
      (List.replicate index true) records (planPayload plan) := by
    apply state_of_stacks b regs
    rw [hb]
    funext i
    fin_cases i <;> simp [a, state, StackRoutines.transferStacks]
  rw [hbe] at hab
  let b' := state b.regs rows.flatten [] width [] source []
    (List.replicate index true) records (planPayload plan)
  obtain ⟨c, hbc, hc⟩ := readWord_eval (14 : Fin 15) 8 2
    (by decide) (by decide) (by decide) b' (planBytes plan) []
    (by simp [b',state,planPayload,planBytes]) rfl rfl
  have hce : c = state c.regs rows.flatten [] width (planBytes plan) source []
      (List.replicate index true) records [] := by
    apply state_of_stacks c regs
    rw [hc]
    funext i
    fin_cases i <;> simp [b', state]
  rw [hce] at hbc
  let c' := state c.regs rows.flatten [] width (planBytes plan) source []
    (List.replicate index true) records []
  let c0 := setData 0 false c'
  let c1 := setData 1 false c0
  let c2 := setData 2 false c1
  have hr0 := set_eval 0 false c'
  have hr1 := set_eval 1 false c0
  have hr2 := set_eval 2 false c1
  obtain ⟨ng, hng, hg⟩ := gatherCall_eval rows width plan c2.regs source
    (List.replicate index true) records (by simp [c2,c1,c0,setData])
    (by simp [c2,c1,c0,setData]) (by simp [c2,c1,c0,setData]) hrows hplan
  let d := state c2.regs rows.flatten (GatherProgram.gathered rows plan) width [] source []
    (List.replicate index true) records []
  obtain ⟨e, hde, he⟩ := copy_eval (12 : Fin 15) 14 2
    (by decide) (by decide) (by decide) d rfl
  have hee : e = state e.regs rows.flatten (GatherProgram.gathered rows plan) width [] source []
      (List.replicate index true) records (List.replicate index true) := by
    apply state_of_stacks e regs
    rw [he]
    funext i
    fin_cases i <;> simp [d, state, StackRoutines.copyStacks]
  rw [hee] at hde
  let e' := state e.regs rows.flatten (GatherProgram.gathered rows plan) width [] source []
    (List.replicate index true) records (List.replicate index true)
  obtain ⟨f, hef, hf⟩ := emitFrame_eval (14 : Fin 15) 13 2
    (by decide) (by decide) (by decide) e' rfl
  have hfe : f = state f.regs rows.flatten (GatherProgram.gathered rows plan) width [] source []
      (List.replicate index true) (Encoding.frame (List.replicate index true) ++ records) [] := by
    apply state_of_stacks f regs
    rw [hf]
    funext i
    fin_cases i <;> simp [e', state]
  rw [hfe] at hef
  let f' := state f.regs rows.flatten (GatherProgram.gathered rows plan) width [] source []
    (List.replicate index true) (Encoding.frame (List.replicate index true) ++ records) []
  obtain ⟨g, hfg, hgst⟩ := emitFrame_eval (1 : Fin 15) 13 2
    (by decide) (by decide) (by decide) f' rfl
  have hge : g = state g.regs rows.flatten [] width [] source []
      (List.replicate index true) (Encoding.frame (GatherProgram.gathered rows plan) ++
        (Encoding.frame (List.replicate index true) ++ records)) [] := by
    apply state_of_stacks g regs
    rw [hgst]
    funext i
    fin_cases i <;> simp [f', state]
  rw [hge] at hfg
  let g' := state g.regs rows.flatten [] width [] source []
    (List.replicate index true) (Encoding.frame (GatherProgram.gathered rows plan) ++
      (Encoding.frame (List.replicate index true) ++ records)) []
  let p := TupleProgram.pushedState 12 0 true g'
  let p5 := setData 5 false p
  let p6 := setData 6 true p5
  let p7 := setData 7 false p6
  have hp := TupleProgram.pushConst_eval (12 : Fin 15) (0 : Fin 8) true g'
  have hp5 := set_eval 5 false p
  have hp6 := set_eval 6 true p5
  have hp7 := set_eval 7 false p6
  have hpout : p7 = state p7.regs rows.flatten [] width [] source []
      (List.replicate (index+1) true) (Encoding.frame (GatherProgram.gathered rows plan) ++
        (Encoding.frame (List.replicate index true) ++ records)) [] := by
    apply state_of_stacks p7 regs
    funext i
    fin_cases i <;> simp [p7,p6,p5,p,g',setData,state,List.replicate_succ]
  have hrun := hab.seq (hbc.seq (hr0.seq (hr1.seq (hr2.seq
    (hg.seq (hde.seq (hef.seq (hfg.seq (hp.seq (hp5.seq (hp6.seq
      (hp7.seq (.base (.skip p7))))))))))))))
  have hcost : (3*(a.stacks 11).length+3) + ((9*(planBytes plan).length+7) +
      (1+(1+(1+(ng+((7*(d.stacks 12).length+5)+((8*(e'.stacks 14).length+8)+
      ((8*(f'.stacks 1).length+8)+(2+(1+(1+(1+0)))))))))))) =
      ng + 15*(planBytes plan).length + 15*index +
        8*(GatherProgram.gathered rows plan).length + 42 := by
    simp [a,d,e',f',state,planPayload,planBytes,Encoding.length_frame]
    ring
  rw [hcost, hpout] at hrun
  refine ⟨_,p7.regs,hrun,?_,?_,?_,?_⟩
  · simp [p7,p6,p5,setData]
  · simp [p7,p6,p5,setData]
  · simp [p7,setData]
  · let t := width.length + (planBytes plan).length + index + 1
    have ht : 1 ≤ t := by dsimp [t]; omega
    have hw : width.length ≤ t := by dsimp [t]; omega
    have hb : (planBytes plan).length ≤ t := by dsimp [t]; omega
    have hi : index ≤ t := by dsimp [t]; omega
    have hplen : plan.length ≤ (planBytes plan).length := by
      rw [planBytes, GatherProgram.encoded_plan_length]
      omega
    have hlen : (GatherProgram.gathered rows plan).length ≤ t*t := by
      rw [GatherProgram.gathered_length rows plan width.length hrows hplan]
      exact Nat.mul_le_mul (hplen.trans hb) hw
    have hgc : ng ≤ 100*t^2 := by
      apply hng.trans ((GatherProgram.traceCost_le_serialized rows width.length plan hrows hplan).trans ?_)
      change 100*(width.length+(planBytes plan).length+1)^2 ≤ 100*t^2
      gcongr
      dsimp [t]
      omega
    have ht2 : t ≤ t^2 := by nlinarith
    change ng + 15*(planBytes plan).length + 15*index +
      8*(GatherProgram.gathered rows plan).length + 42 ≤ 200*t^2
    nlinarith

theorem loop_eval (rows : List (List Bool)) (width : List Bool)
    (plans : List (List ℕ)) (regs : Fin 8 → Bool) (start : ℕ)
    (records suffix : List Bool)
    (hrows : ∀ row ∈ rows, row.length = width.length)
    (hplans : ∀ plan ∈ plans, ∀ i ∈ plan, i < rows.length) :
    ∃ (n : ℕ) (rf : Fin 8 → Bool), n ≤ 1+iterationCost width.length plans start ∧
      Eval (RecordPrograms.loop ports callback) n
        (RecordPrograms.afterTag ports (base rows width regs start records)
          (plans.map planPayload) suffix)
        (RecordPrograms.state ports
          (base rows width rf (start+plans.length)
            (BucketProgram.encodeRecords (labelRecords rows plans start).reverse ++ records))
          false true false suffix []) := by
  induction plans generalizing regs start records with
  | nil =>
      refine ⟨1,regs,by simp [iterationCost],?_⟩
      simpa only [List.map_nil, RecordPrograms.afterTag, List.length_nil, Nat.add_zero,
        labelRecords_nil, List.reverse_nil, BucketProgram.encodeRecords, List.nil_append] using
        (Eval.while_false (body := RecordPrograms.body ports callback)
          (a := RecordPrograms.state ports (base rows width regs start records)
            false true false suffix []) (by simp))
  | cons plan plans ih =>
      let a := base rows width regs start records
      let tail := Encoding.encodeList id (plans.map planPayload) ++ suffix
      have hreader : Eval (RecordPrograms.reader ports) (6*(planPayload plan).length+4)
          (RecordPrograms.afterTag ports a ((plan::plans).map planPayload) suffix)
          (RecordPrograms.state ports a false true false tail (planPayload plan).reverse) := by
        simpa only [List.map_cons, RecordPrograms.afterTag, List.append_nil] using
          RecordPrograms.reader_eval ports a (planPayload plan) tail [] true true false
      obtain ⟨nc,rc,hc,hr5,hr6,hr7,hnc⟩ := callback_eval rows width plan
        (parserRegs regs false true false) tail records start hrows
        (hplans plan (by simp))
      let out := Encoding.frame (GatherProgram.gathered rows plan) ++
        (Encoding.frame (List.replicate start true) ++ records)
      let b := base rows width rc (start+1) out
      have hcb : Eval callback nc
          (RecordPrograms.state ports a false true false tail (planPayload plan).reverse)
          (RecordPrograms.state ports b false true false tail []) := by
        simpa only [a,b,base,parser_state,
          parserRegs_self rc false true false hr5 hr6 hr7] using hc
      have hbranch : Eval
          (.ite ports.found (RecordPrograms.atom (.set ports.tag false))
            (RecordPrograms.atom (.pop ports.source ports.tag ports.present))) 2
          (RecordPrograms.state ports b false true false tail [])
          (RecordPrograms.afterTag ports b (plans.map planPayload) suffix) := by
        apply Eval.ite_false (by simp)
        exact RecordPrograms.pop_list_eval ports b (plans.map planPayload) suffix false true
      obtain ⟨nr,rf,hnr,hr⟩ := ih rc (start+1) out
        (fun q hq => hplans q (by simp [hq]))
      have hbody := hreader.seq (hcb.seq hbranch)
      have hrun := Eval.while_true
        (show (RecordPrograms.afterTag ports a ((plan::plans).map planPayload) suffix).regs
          ports.tag = true by simp [RecordPrograms.afterTag]) hbody hr
      refine ⟨6*(planPayload plan).length+4+(nc+2)+nr+1,rf,?_,?_⟩
      · simp only [iterationCost]
        omega
      · have hindex : start+1+plans.length = start+(plan::plans).length := by simp; omega
        simpa only [RecordPrograms.loop, RecordPrograms.body, a, b, out, hindex,
          reversed_output_cons] using hrun

/-- Execute every supplied forward plan in order. The packed assignment and
row width are preserved; the raw bucket records are prepended in reverse order. -/
theorem command_eval (rows : List (List Bool)) (width : List Bool)
    (plans : List (List ℕ)) (regs : Fin 8 → Bool) (start : ℕ)
    (records suffix : List Bool)
    (hrows : ∀ row ∈ rows, row.length = width.length)
    (hplans : ∀ plan ∈ plans, ∀ i ∈ plan, i < rows.length) :
    ∃ (n : ℕ) (rf : Fin 8 → Bool), n+1 ≤ traceCost width.length plans start ∧
      Eval command n
        (state regs rows.flatten [] width []
          (ProgramEncoding.encodeRecords (plans.map planPayload) ++ suffix) []
          (List.replicate start true) records [])
        (state rf rows.flatten [] width [] suffix []
          (List.replicate (start+plans.length) true)
          (BucketProgram.encodeRecords (labelRecords rows plans start).reverse ++ records) []) := by
  let a := base rows width regs start records
  obtain ⟨n,rf,hn,he⟩ := loop_eval rows width plans regs start records suffix hrows hplans
  have hset := RecordPrograms.set_found_eval ports a (regs 5) (regs 6) (regs 7) false
    (ProgramEncoding.encodeRecords (plans.map planPayload) ++ suffix) []
  have hpop := RecordPrograms.pop_list_eval ports a (plans.map planPayload) suffix (regs 5) (regs 6)
  have hrun := hset.seq (hpop.seq he)
  refine ⟨1+(1+n),parserRegs rf false true false,by dsimp [traceCost]; omega,?_⟩
  simpa only [command,RecordPrograms.iterate,a,base,parser_state,
    parserRegs_self regs (regs 5) (regs 6) (regs 7) rfl rfl rfl] using hrun

theorem program_trace (rows : List (List Bool)) (width : List Bool)
    (plans : List (List ℕ)) (regs : Fin 8 → Bool) (start : ℕ)
    (records suffix : List Bool)
    (hrows : ∀ row ∈ rows, row.length = width.length)
    (hplans : ∀ plan ∈ plans, ∀ i ∈ plan, i < rows.length) :
    ∃ (n : ℕ) (rf : Fin 8 → Bool), n ≤ traceCost width.length plans start ∧
      Trace program n
        ((state regs rows.flatten [] width []
          (ProgramEncoding.encodeRecords (plans.map planPayload) ++ suffix) []
          (List.replicate start true) records []).withPC (some program.entry))
        ((state rf rows.flatten [] width [] suffix []
          (List.replicate (start+plans.length) true)
          (BucketProgram.encodeRecords (labelRecords rows plans start).reverse ++ records) []).withPC none) := by
  obtain ⟨n,rf,hn,he⟩ := command_eval rows width plans regs start records suffix hrows hplans
  exact ⟨n+1,rf,hn,compiled_halt_trace he 10 13⟩

end SubexponentialSAT.Subexp.PackingVertexLabels

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutFiberSumProgramMove
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutFiberSumProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def moved (src dst : Fin 256) (a : Data) : Data :=
  ⟨readRegs a.regs 0 1 none,
    Function.update (Function.update a.stacks src []) dst (a.stacks src)⟩

def ownerResult (a : Data) (regs : Fin 16 → Bool) (is : List ℕ) : Data :=
  ⟨regs,Function.update (Function.update a.stacks 215 (unary is.length)) 214 (encodeIndices is)⟩

end SubexponentialSAT.SqrtLog.LayoutFiberSumProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutFiberSumProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutFiberSumProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls RowSelectionProgram

def Ready (base : Data) : Prop :=
  (∀ i : Fin 256, i.val < 200 → base.stacks i=[]) ∧
  (∀ i : Fin 256, 212 ≤ i.val → i.val < 252 → base.stacks i=[])

def parked (base : Data) (query : ℕ) : Data :=
  ⟨base.regs,Function.update base.stacks 216 (unary query)⟩

end SubexponentialSAT.SqrtLog.LayoutFiberSumProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutMatrixProgramPrimitives
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed stack and framing adapters for direct construction of all incidence
rows. The adapters expose native instruction counts and exact stack effects. -/
namespace SubexponentialSAT.SqrtLog.LayoutMatrixProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev parsed {s : ℕ} (src dst : Fin s) (d : Data s) (rf : Fin 16 → Bool)
    (tail bits : List Bool) : Data s :=
  ⟨rf,Function.update (Function.update d.stacks src tail) dst bits⟩

end SubexponentialSAT.SqrtLog.LayoutMatrixProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpBlockParameterProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Actual block-size and block-threshold arithmetic

The three input words contain `s`, `delta`, and `Q`.  The width `k` is part
of the fixed code.  Seven high stacks are a reusable empty work bank; the
fifteen low stacks retain inputs, constants, and computed intermediate words.
Every arithmetic operation below invokes a proved finite Boolean program.
-/

namespace SubexponentialSAT.SubexpBlockParameterProgram

open BitProgram StructuredCalls BinaryArithmetic

def inputWords (s delta Q : List Bool) : Words :=
  ![s, delta, Q, [], [], [], [], [], [], [], [], [], [], [], []]

end SubexponentialSAT.SubexpBlockParameterProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutOffsetProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed native producer of the signed-bucket offset 2*B*(8*Q)^(2*R).
All arithmetic acts on runtime binary words. This offset is unrelated to
the unary scalar-row width 1+2*A*R+Q. -/
namespace SubexponentialSAT.SqrtLog.LayoutOffsetProgram
open SubexponentialSAT BitProgram StructuredCalls BinaryArithmetic
open SubexpBlockParameterProgram

abbrev bank := SubexpBlockParameterProgram.state

def initial (B Q R : List Bool) : Words := SubexpBlockParameterProgram.inputWords B Q R

def loaded (B Q R : List Bool) : Words :=
  Function.update (Function.update (initial B Q R) 3 two) 4 eight

def filled (B Q R a e p b out : List Bool) : Words :=
  Function.update (Function.update (Function.update (Function.update
    (Function.update (loaded B Q R) 5 a) 6 e) 7 p) 8 b) 9 out

end SubexponentialSAT.SqrtLog.LayoutOffsetProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutOffsetProgramRun
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutOffsetProgram
open SubexponentialSAT BitProgram StructuredCalls BinaryArithmetic SubexpBlockParameterProgram

abbrev clearOne (i : Fin 15) : Cmd 8 22 := ArithmeticExpressionSupport.clearCmd (port i)

abbrev clearMany : List (Fin 15) → Cmd 8 22
  | [] => .base .skip
  | i::is => .seq (clearOne i) (clearMany is)

abbrev input (regs : Regs) (B Q R : List Bool) : Data := bank regs (initial B Q R)
abbrev result (B Q R out : List Bool) : Data := bank (fun _ => false) (Function.update (initial B Q R) 9 out)

end SubexponentialSAT.SqrtLog.LayoutOffsetProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingMetadata
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact lookup semantics for the storage-ordered packing metadata table.
The physical extraction proof identifies its emitted records with this table. -/

namespace SubexponentialSAT.Subexp.PackingMetadata

open ConstructivePacking
open GlobalBasisMetadata (Metadata)

variable {V U : Type*} [DecidableEq V] [DecidableEq U]

theorem records_eq_leftovers_append (P : PackingData V U)
    (encodeVertex : V → List Bool) (encodeType : U → List Bool) :
    records P encodeVertex encodeType =
      P.leftovers.reverse.map (row P encodeVertex encodeType) ++
        coveredRecords P encodeVertex encodeType := by
  simp [records, coveredRecords, PackingReorder.storageVertices, List.reverse_append]

theorem covered_lookup_none_iff (P : PackingData V U)
    (encodeVertex : V → List Bool) (encodeType : U → List Bool)
    (hvertex : Function.Injective encodeVertex) (v : V) :
    (coveredRecords P encodeVertex encodeType).lookup (encodeVertex v) = none ↔
      P.lookup v = none := by
  unfold coveredRecords row
  rw [lookup_graph_encoded_none _ _ _ hvertex, List.mem_reverse, mem_packedVertices_iff]
  cases hv : P.lookup v <;> simp []

/-- The physical missing-key filter selects exactly the typed leftovers. -/
theorem covered_filter_eq_leftovers (P : PackingData V U)
    (encodeVertex : V → List Bool) (encodeType : U → List Bool)
    (hvertex : Function.Injective encodeVertex) :
    P.vertices.values.filter (fun v => decide
      ((coveredRecords P encodeVertex encodeType).lookup (encodeVertex v) = none)) = P.leftovers := by
  unfold PackingData.leftovers
  apply List.filter_congr
  intro v _
  simp only [covered_lookup_none_iff P encodeVertex encodeType hvertex]

end SubexponentialSAT.Subexp.PackingMetadata

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingAddressSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The emitted storage-address table is the graph of the actual packed
coordinate order. Its lookups produce the existing reordering read plan. -/

namespace SubexponentialSAT.Subexp.PackingAddressSemantics

open ConstructivePacking

variable {V U : Type*} [DecidableEq V] [DecidableEq U]

theorem selected_storageAddresses (P : PackingData V U) (encodeVertex : V → List Bool)
    (he : Function.Injective encodeVertex) (v : V) :
    SelectorMapProgram.selected (storageAddresses P encodeVertex) (encodeVertex v) =
      List.replicate ((PackingReorder.storageVertices P).idxOf v) true := by
  unfold SelectorMapProgram.selected
  rw [lookup_storageAddresses P encodeVertex he v]
  rfl

theorem selected_queries_eq_readPlan (P : PackingData V U) (encodeVertex : V → List Bool)
    (he : Function.Injective encodeVertex) :
    (P.vertices.values.map encodeVertex).map
      (SelectorMapProgram.selected (storageAddresses P encodeVertex)) =
      (PackingReorder.readPlan P).map (fun i => List.replicate i true) := by
  simp only [PackingReorder.readPlan, List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro v _
  exact selected_storageAddresses P encodeVertex he v

/-- Reverse queries compensate for the selector's prepending accumulator,
so its actual output is the read plan in original vertex order. -/
theorem mappedRecords_eq_readPlan (P : PackingData V U) (encodeVertex : V → List Bool)
    (he : Function.Injective encodeVertex) :
    SelectorMapProgram.mappedRecords (storageAddresses P encodeVertex)
      (P.vertices.values.reverse.map encodeVertex) =
      (PackingReorder.readPlan P).map (fun i => List.replicate i true) := by
  unfold SelectorMapProgram.mappedRecords
  rw [List.map_reverse, List.map_reverse, List.reverse_reverse]
  exact selected_queries_eq_readPlan P encodeVertex he

end SubexponentialSAT.Subexp.PackingAddressSemantics

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_CandidateScoreProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed-control candidate scoring

Score records are accumulated as reversed serialized bytes and reversed once
at the end, so output score order agrees with the input candidate order.
-/

namespace SubexponentialSAT.Subexp.CandidateScoreProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem resetList_eval {r s : ℕ} (indices : List (Fin r)) (d : State r s) :
    StructuredProgram.Eval (resetList indices) indices.length d
      ⟨resetValues indices d.regs,d.stacks⟩ := by
  induction indices generalizing d with
  | nil => exact .skip d
  | cons i rest ih =>
      have h := (StructuredProgram.Eval.atom (.set i false) d).seq
        (ih ((StructuredProgram.Atom.set i false).eval d))
      simpa [resetList,resetValues,StructuredProgram.Atom.eval,
        StructuredProgram.Atom.instr,StructuredProgram.State.ofCfg,
        StructuredProgram.State.withPC,execInstr,Nat.add_comm] using h

end SubexponentialSAT.Subexp.CandidateScoreProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingBucketCalls
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Physical subroutine calls for the all-type packing fold. -/

namespace SubexponentialSAT.Subexp.PackingBucketCalls

open BitProgram StructuredCalls MatrixProgramSupport

/-- One real scan consumes a copied reversed label table, retaining the query
and producing the bucket in original vertex order. -/
theorem bucketCall_eval (records : List BucketProgram.Record) (query : List Bool)
    (regs : Fin 8 → Bool) (saved keys scan minimum table count result : List Bool) :
    ∃ n ≤ 2 + BucketProgram.loopBudget records.reverse query, ∃ regs',
      Eval bucketCall n
        (state regs (BucketProgram.encodeRecords records.reverse) query.reverse []
          saved keys scan minimum table count result)
        (state regs' [] query.reverse (words (BucketProgram.selected records query))
          saved keys scan minimum table count result) := by
  let localRegs : Fin 5 → Bool := fun i => regs (bucketRegs i)
  obtain ⟨n, hn, rf, ht⟩ := BucketProgram.scan_eval localRegs records.reverse query []
  have hh := compiled_halt_trace ht 0 5
  have he := eval_call_lifted scanProgram bucketRegs bucketPorts
    (state regs (BucketProgram.encodeRecords records.reverse) query.reverse []
      saved keys scan minimum table count result)
    bucketRegs_injective bucketPorts_injective hh
  rw [embed_bucket, embed_bucket, merged_restrict] at he
  refine ⟨n + 1, by omega, merged regs rf, ?_⟩
  simpa only [BucketProgram.scanOutput_reverse, frames_eq_words, List.append_nil] using he

end SubexponentialSAT.Subexp.PackingBucketCalls

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingOutputSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The actual leftover scan completes the metadata, storage order, and
address table produced by complete-block extraction. -/

namespace SubexponentialSAT.Subexp.PackingOutputSemantics

open ConstructivePacking

variable {V U : Type*} [DecidableEq V] [DecidableEq U]

theorem leftovers_eq (P : PackingData V U) (code : V → ℕ)
    (encodeType : U → List Bool) (hc : Function.Injective code) :
    PackingLeftovers.leftovers
        (PackingMetadata.coveredRecords P (vertexBytes code) encodeType)
        (P.vertices.values.map code) = P.leftovers.map code := by
  unfold PackingLeftovers.leftovers
  rw [List.filter_map]
  apply congrArg (List.map code)
  rw [← PackingMetadata.covered_filter_eq_leftovers P (vertexBytes code) encodeType
    (vertexBytes_injective code hc)]
  apply List.filter_congr
  intro v _
  simp only [Function.comp_def]
  unfold PackingLeftovers.covered
  change Bool.not ((PackingMetadata.coveredRecords P (vertexBytes code) encodeType).lookup
      (vertexBytes code v)).isSome =
    decide ((PackingMetadata.coveredRecords P (vertexBytes code) encodeType).lookup
      (vertexBytes code v) = none)
  cases (PackingMetadata.coveredRecords P (vertexBytes code) encodeType).lookup
    (vertexBytes code v) <;> rfl

/-- Exact state after complete-block extraction from empty accumulators. -/
def packedSnapshot (P : PackingData V U) (code : V → ℕ)
    (encodeType : U → List Bool) : PackingLeftovers.Snapshot :=
  { rank := 0
    address := (PackingReorder.packedVertices P).length
    storage := (PackingExtraction.vertexPrefix
      ((PackingReorder.packedVertices P).map (vertexBytes code))).reverse
    metadata := SelectorProgram.rawRecords
      (PackingMetadata.coveredRecords P (vertexBytes code) encodeType)
    addresses := SelectorProgram.rawRecords
      (PackingAddressSemantics.addressRows
        ((PackingReorder.packedVertices P).map (vertexBytes code)) 0).reverse }

theorem snapshotOf_extraction (P : PackingData V U) (code : V → ℕ)
    (encodeType : U → List Bool) (c : PackingExtraction.Context)
    (hb : c.block = []) (ha : c.address = []) (hs : c.storage = [])
    (hm : c.metadata = []) (ht : c.addresses = []) :
    snapshotOf (PackingExtraction.advanceMany
      (PackingExtraction.typedEntries P (vertexBytes code) encodeType) P.blockCount 0 c) =
      packedSnapshot P code encodeType := by
  have hu : c.address = PackingMetadata.unary 0 := ha
  have hn := PackingExtraction.advanceMany_address_unary
    (PackingExtraction.typedEntries P (vertexBytes code) encodeType) P.blockCount 0 c 0 hu
  have hlen : (PackingExtraction.advanceMany
      (PackingExtraction.typedEntries P (vertexBytes code) encodeType)
      P.blockCount 0 c).address.length = (PackingReorder.packedVertices P).length := by
    rw [hn, PackingReorder.packedVertices_length]
    simp [PackingMetadata.unary, PackingExtraction.typedEntries]
  unfold snapshotOf
  rw [hlen, PackingExtraction.typed_extraction_storage,
    PackingExtraction.typed_extraction_metadata _ _ _ _ hb,
    PackingExtraction.typed_extraction_addresses _ _ _ _ 0 hu]
  simp only [hs, hm, ht, List.append_nil] ; rfl

def finish (P : PackingData V U) (code : V → ℕ) (encodeType : U → List Bool)
    (s : PackingLeftovers.Snapshot) : PackingLeftovers.Snapshot :=
  (P.vertices.values.map code).foldl
    (PackingLeftovers.advance (PackingMetadata.coveredRecords P (vertexBytes code) encodeType)) s

theorem finish_metadata (P : PackingData V U) (code : V → ℕ)
    (encodeType : U → List Bool) (hc : Function.Injective code) :
    (finish P code encodeType (packedSnapshot P code encodeType)).metadata =
      SelectorProgram.rawRecords (PackingMetadata.records P (vertexBytes code) encodeType) := by
  unfold finish
  rw [PackingLeftovers.final_metadata, leftovers_eq P code encodeType hc]
  change SelectorProgram.rawRecords
      (PackingLeftovers.metadataRecords 0 (P.leftovers.map code)).reverse ++
      SelectorProgram.rawRecords
        (PackingMetadata.coveredRecords P (vertexBytes code) encodeType) = _
  rw [metadataRecords_leftovers, ← List.map_reverse, ← PackingLeftovers.rawRecords_append,
    ← PackingMetadata.records_eq_leftovers_append]

theorem finish_storage (P : PackingData V U) (code : V → ℕ)
    (encodeType : U → List Bool) (hc : Function.Injective code) :
    (finish P code encodeType (packedSnapshot P code encodeType)).storage =
      (PackingExtraction.vertexPrefix
        ((PackingReorder.storageVertices P).map (vertexBytes code))).reverse := by
  unfold finish
  rw [PackingLeftovers.final_storage, leftovers_eq P code encodeType hc]
  simp [packedSnapshot, PackingLeftovers.storageRecords, PackingReorder.storageVertices,
    PackingExtraction.vertexPrefix, vertexBytes, PackingMetadata.unary,
    List.flatMap_map, List.flatMap_append, List.reverse_append]

theorem finish_addresses (P : PackingData V U) (code : V → ℕ)
    (encodeType : U → List Bool) (hc : Function.Injective code) :
    (finish P code encodeType (packedSnapshot P code encodeType)).addresses =
      SelectorProgram.rawRecords (PackingAddressSemantics.storageAddresses P (vertexBytes code)) := by
  unfold finish
  rw [PackingLeftovers.final_addresses, leftovers_eq P code encodeType hc,
    addressRecords_eq_addressRows]
  simp only [packedSnapshot, PackingAddressSemantics.storageAddresses,
    PackingReorder.storageVertices, List.map_append,
    PackingAddressSemantics.addressRows_append, List.length_map, Nat.zero_add,
    List.reverse_append, PackingLeftovers.rawRecords_append, List.map_map] ; rfl

theorem finish_counters (P : PackingData V U) (code : V → ℕ)
    (encodeType : U → List Bool) (hc : Function.Injective code) :
    (finish P code encodeType (packedSnapshot P code encodeType)).rank = P.leftovers.length ∧
    (finish P code encodeType (packedSnapshot P code encodeType)).address =
      (PackingReorder.storageVertices P).length := by
  have h := PackingLeftovers.final_counters
    (PackingMetadata.coveredRecords P (vertexBytes code) encodeType)
    (P.vertices.values.map code) (packedSnapshot P code encodeType)
  rw [leftovers_eq P code encodeType hc] at h
  simpa only [finish, packedSnapshot, List.length_map, Nat.zero_add,
    PackingReorder.storageVertices, List.length_append] using h

/-- All physical accumulators after extraction and the actual leftover scan. -/
theorem finish_extraction_outputs (P : PackingData V U) (code : V → ℕ)
    (encodeType : U → List Bool) (hc : Function.Injective code)
    (c : PackingExtraction.Context) (hb : c.block = []) (ha : c.address = [])
    (hs : c.storage = []) (hm : c.metadata = []) (ht : c.addresses = []) :
    let s := finish P code encodeType (snapshotOf (PackingExtraction.advanceMany
      (PackingExtraction.typedEntries P (vertexBytes code) encodeType) P.blockCount 0 c))
    s.metadata = SelectorProgram.rawRecords
        (PackingMetadata.records P (vertexBytes code) encodeType) ∧
    s.storage = (PackingExtraction.vertexPrefix
        ((PackingReorder.storageVertices P).map (vertexBytes code))).reverse ∧
    s.addresses = SelectorProgram.rawRecords
        (PackingAddressSemantics.storageAddresses P (vertexBytes code)) ∧
    s.rank = P.leftovers.length ∧ s.address = (PackingReorder.storageVertices P).length := by
  dsimp only
  rw [snapshotOf_extraction P code encodeType c hb ha hs hm ht]
  exact ⟨finish_metadata P code encodeType hc, finish_storage P code encodeType hc,
    finish_addresses P code encodeType hc, finish_counters P code encodeType hc⟩

end SubexponentialSAT.Subexp.PackingOutputSemantics

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramPackLabels
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Packing from physically produced label records. This route accepts the
incidence pair-gatherer's type labels directly, avoiding reconstruction of a
factor-to-incidence scope table. The fixed program computes blocks, uncovered
coordinates, metadata, storage order, and inverse addresses. It does not
assume any of those outputs. Label and universal-type byte production remain
explicit upstream obligations. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.PackLabels

open SubexponentialSAT.Subexp SubexponentialSAT.Subexp.ConstructivePacking
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

variable {U : Type*} [DecidableEq U]

theorem minimum_eq (s : Spec U) :
    PackingBucketTable.minimum (records s) (keys s) s.params.D = s.packing.blockCount := by
  have h := PackingBucketTable.minimum_eq_blockCount s.packing s.encodeType s.encodeVertex
    s.encodeType_injective
  simpa only [records, keys, Spec.packing, List.length_finRange] using h

theorem table_eq (s : Spec U) :
    PackingBucketTable.table (records s) (keys s) = (entries s).map PackingExtraction.entryWord := by
  change PackingBucketTable.table
    (BucketProgram.vertexRecords s.packing.vertices.values s.packing.label s.encodeType s.encodeVertex)
    (s.packing.types.values.map s.encodeType) = _
  rw [PackingBucketTable.table_eq_typed s.packing s.encodeType s.encodeVertex s.encodeType_injective]
  simp only [entries, PackingExtraction.typedEntries, List.map_map,
    PackingExtraction.entryWord, PackingExtraction.bucketWord, Function.comp_def]

theorem inverse_rows (s : Spec U) :
    PackingProgram.inverseRows (addressRecords s) s.params.D =
      (PackingReorder.readPlan s.packing).map PackingMetadata.unary := by
  have h := PackingAddressSemantics.mappedRecords_eq_readPlan s.packing s.encodeVertex
    s.encodeVertex_injective
  have hq : PackingProgram.inverseQueries s.params.D =
      s.packing.vertices.values.reverse.map s.encodeVertex := by
    simp only [PackingProgram.inverseQueries, Spec.packing,
      ← List.range_eq_range', ← List.map_coe_finRange, List.map_reverse, List.map_map,
      Function.comp_def, PackingMetadata.unary] ; rfl
  rw [PackingProgram.inverseRows, addressRecords, hq, h]
  simp [PackingMetadata.unary]


end SubexponentialSAT.SqrtLog.LayoutProgram.PackLabels

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

/-! A fixed ten-comparison bit guard. All operands are runtime binary words.
This module states their data relation separately from parameter production. -/

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Circuit

open BitProgram StructuredCalls BinaryArithmetic Bank

def Shape (m : Model) (w : Words) : Prop :=
  (∀ a, BinaryArithmetic.toNat (w a)=m.val a) ∧ (∀ a, (w a).length ≤ m.len a)

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Circuit


/- Component: SubexponentialSAT.SqrtLog.LeafParametersProgramLayout -/


end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsProgramProduct
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


/-! A fixed sparse-product instruction table. Its three subservices perform
coefficient scaling, key join/clipping, and additive normalization, respectively.
All outer source lengths and ring dimensions live on tape. -/


namespace SubexponentialSAT.SqrtLog.MomentsProgram.Product
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

def state (regs : Fin 8 → Bool) (s : Store) : Data := ⟨regs,tapes s⟩

end SubexponentialSAT.SqrtLog.MomentsProgram.Product


end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpSetupStorageCost
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Cost of the concrete setup storage instructions

Copying and cleanup are charged by the lengths of the words physically read.
The final stage bound is linear in a common word bound; its coefficients depend
only on the statically allocated ports and copy lists.
-/

namespace SubexponentialSAT.SubexpSetupStorage

open BitProgram StructuredCalls

def WordBound {r s : ℕ} (B : ℕ) (a : State r s) : Prop :=
  ∀ i, (a.stacks i).length ≤ B

theorem clearState_wordBound {S : ℕ} (p : Fin S) (a : Data S) (B : ℕ)
    (ha : WordBound B a) : WordBound B (clearState p a) := by
  intro i
  by_cases hi : i = p
  · subst i
    simp [clearState]
  · simpa [clearState, hi] using ha i

theorem clearManyCost_le {S : ℕ} (ps : List (Fin S)) (a : Data S) (B : ℕ)
    (ha : WordBound B a) : clearManyCost ps a ≤ ps.length * (2 * B + 3) := by
  induction ps generalizing a with
  | nil => simp [clearManyCost]
  | cons p ps ih =>
    have hc := ih (clearState p a) (clearState_wordBound p a B ha)
    have hp : 2 * (a.stacks p).length + 3 ≤ 2 * B + 3 := by
      have := ha p
      omega
    calc
      clearManyCost (p :: ps) a =
          (2 * (a.stacks p).length + 3) + clearManyCost ps (clearState p a) := rfl
      _ ≤ (2 * B + 3) + ps.length * (2 * B + 3) := Nat.add_le_add hp hc
      _ = (p :: ps).length * (2 * B + 3) := by simp only [List.length_cons]; ring

theorem copyManyCost_le {S : ℕ} (ps : List (Fin S × Fin S)) (a : Data S) (B : ℕ)
    (hsep : ∀ p ∈ ps, ∀ q ∈ ps, p.1 ≠ q.2)
    (ha : ∀ p ∈ ps, (a.stacks p.1).length ≤ B) :
    copyManyCost ps a ≤ ps.length * (7 * B + 5) := by
  induction ps generalizing a with
  | nil => simp [copyManyCost]
  | cons p ps ih =>
    have hs : ∀ q ∈ ps, ∀ z ∈ ps, q.1 ≠ z.2 := by
      intro q hq z hz
      exact hsep q (List.mem_cons_of_mem _ hq) z (List.mem_cons_of_mem _ hz)
    have hb : ∀ q ∈ ps, ((copyState p.1 p.2 a).stacks q.1).length ≤ B := by
      intro q hq
      rw [copyState_frame _ _ _ _
        (hsep q (List.mem_cons_of_mem _ hq) p (List.mem_cons_self))]
      exact ha q (List.mem_cons_of_mem _ hq)
    have hc := ih (copyState p.1 p.2 a) hs hb
    have hp : 7 * (a.stacks p.1).length + 5 ≤ 7 * B + 5 := by
      have := ha p List.mem_cons_self
      omega
    calc
      copyManyCost (p :: ps) a =
          (7 * (a.stacks p.1).length + 5) + copyManyCost ps (copyState p.1 p.2 a) := rfl
      _ ≤ (7 * B + 5) + ps.length * (7 * B + 5) := Nat.add_le_add hp hc
      _ = (p :: ps).length * (7 * B + 5) := by simp only [List.length_cons]; ring

theorem copyMany_wordBound {S : ℕ} (ps : List (Fin S × Fin S)) (a : Data S) (B : ℕ)
    (hd : (ps.map Prod.snd).Nodup)
    (hz : ∀ p ∈ ps, a.stacks p.2 = [])
    (hsep : ∀ p ∈ ps, ∀ q ∈ ps, p.1 ≠ q.2)
    (ha : WordBound B a) : WordBound B (copyManyState ps a) := by
  intro i
  by_cases hm : ∃ p ∈ ps, p.2 = i
  · obtain ⟨p, hp, rfl⟩ := hm
    rw [copyMany_value ps a hd hz hsep p hp]
    exact ha p.1
  · have hi : ∀ p ∈ ps, i ≠ p.2 := by
      intro p hp he
      exact hm ⟨p, hp, he.symm⟩
    rw [copyMany_frame ps a i hi]
    exact ha i

end SubexponentialSAT.SubexpSetupStorage

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_BlockSearchProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed control for the universal-block finite search

The commands in this file scan runtime framed lists. Their finite control
depends on the supplied finite predicate program and fixed ports, never on
the block dimension, field size, or list lengths. Predicate specifications
are measured `StructuredCalls.Eval` contracts for actual finite code.
-/

namespace SubexponentialSAT.Subexp.BlockSearchProgram

open BitProgram StructuredCalls

/-- Repeated universal scans preserve the saved enumeration and consume their
working source even when a failed predicate stops the scan early. -/
theorem savedAllCommand_eval {r s : ℕ} (p : SavedPorts r s)
    (predicate : Cmd r s) (test : List Bool → Bool) (cost : List Bool → ℕ)
    (invariant : State r s → Prop) (valid : List Bool → Prop)
    (contract : RecordPrograms.CallbackContractOn p.toPorts predicate test cost invariant valid)
    (records : List (List Bool)) (base : State r s)
    (hrecords : ∀ bits ∈ records, valid bits) (hbase : invariant base)
    (hs : base.stacks p.saved = ProgramEncoding.encodeRecords records)
    (ht : base.stacks p.temporary = []) (v pr found : Bool) :
    ∃ n next,
      n ≤ 9 * (ProgramEncoding.encodeRecords records).length +
        RecordPrograms.budget (fun bits => cost bits + 2) records + 14 ∧
      invariant next ∧ Eval (savedAllCommand p predicate) n
        (RecordPrograms.state p.toPorts base v pr found [] [])
        (RecordPrograms.state p.toPorts next false true (records.all test) [] []) := by
  have hcopy := copy_saved_eval p base (ProgramEncoding.encodeRecords records) hs ht v pr found
  obtain ⟨n, next, hn, hnext, hall⟩ := allCommand_eval p.toPorts predicate test cost
    invariant valid contract records [] base hrecords hbase false false found
  simp only [List.append_nil] at hall
  have hclear := clear_source_eval p.toPorts next
    (RecordPrograms.unread (fun bits => !(test bits)) records []) false true (records.all test)
  have hset := set_present_eval p.toPorts next false false (records.all test) true [] []
  refine ⟨_, next, ?_, hnext, hcopy.seq (hall.seq (hclear.seq hset))⟩
  have hl := unread_length_le (fun bits => !(test bits)) records
  omega

/-! A full-dimensional candidate needs only universal scalar tests. -/

open scoped BigOperators
open SubexponentialSAT.QuarticSearch

end SubexponentialSAT.Subexp.BlockSearchProgram

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
open SubexpKernelControl (Word Accumulator pushWord operator operators popTag unframe emitFramedLiteral emitLiteral
  emitOperator countOne drain scan )

local infixr:60 " ;; " => Cmd.seq

abbrev termBody : Cmd 3 8 :=
  emitFramedLiteral ;; emitFramedLiteral ;; emitX ;; emitOperator true ;;
    productBody ;; emitOperator true ;; emitOperator true ;; countOne 7

end SubexponentialSAT.Subexp.UniversalRowProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_UniversalRowFactorLoop
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual diagonal exclusion and factor-record production for a row. -/

namespace SubexponentialSAT.Subexp.UniversalRowFactorLoop

open BitProgram StructuredCalls StackRoutines
open UniversalRowGather (Word)

abbrev callback : Cmd 8 32 :=
  .seq compareIndex
    (.seq (.ite 4 (.base .skip) selected)
      (.seq (.call (clearProgram 9 (0 : Fin 8) 1)) resetFlags))

abbrev loop : Cmd 8 32 := RecordPrograms.iterate ports callback

end SubexponentialSAT.Subexp.UniversalRowFactorLoop

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_UniversalRowTermProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! One actual correction-term iteration, from packed tables to a row record. -/

namespace SubexponentialSAT.Subexp.UniversalRowTermProgram

open BitProgram StructuredCalls StackRoutines
open UniversalRowGather (Word)
open UniversalRowFactorLoop (indexWord)

abbrev command : Cmd 8 32 :=
  .seq UniversalRowGather.termFields
    (.seq (.call (copyProgram 28 8 15 (0 : Fin 8) 1))
      (.seq (TupleProgram.pushConst 21 0 false)
        (.seq UniversalRowFactorLoop.loop
          (.seq UniversalRowTermFraming.term
            (.seq (.call (clearProgram 0 (0 : Fin 8) 1))
              (.seq (.call (clearProgram 16 (0 : Fin 8) 1))
                UniversalRowFactorLoop.resetFlags))))))

end SubexponentialSAT.Subexp.UniversalRowTermProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_UniversalRowLoop
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The actual outer loop assembling correction terms in selected-index order. -/

namespace SubexponentialSAT.Subexp.UniversalRowLoop

open BitProgram StructuredCalls
open UniversalRowGather (Word)
open UniversalRowFactorLoop (indexWord)

abbrev loop : Cmd 8 32 := RecordPrograms.iterate ports UniversalRowTermProgram.command

end SubexponentialSAT.Subexp.UniversalRowLoop

end OAI.Algorithms
end


