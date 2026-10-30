-- Prove2me | Definitions.Def_OAIQ081S105
-- name    : OAIQ081S105
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T22:23:13.843828+00:00
-- url     : https://prove2.me/theorems/7061a8ea-f713-4d77-b15c-c7e3c5352693
-- title:
--   Definitions bundle OAIQ081S105 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 54 declarations of OpenAI's Lean: 24 definitions and 30 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchBootstrap.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchBootstrap.generateAt`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchBootstrap.searchCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchCandidateControl.wide`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchEnumeration.generateCmd`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchEnumeration.powerCmd`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchEnumeration.powerLoop`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchEnumeration.program`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchProgram.afterOne`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchProgram.afterThree`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchProgram.afterTwo`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchProgram.atomsResult`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchProgram.coefficientState`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchProgram.dotGuardState`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchProgram.dotInput`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchProgram.dotState`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchProgram.productGuardState`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchProgram.productOutput`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchProgram.productState`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchProgram.transferState`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchProgram.writtenPair`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.ScaleProgram.Data`, `OAI.Algorithms.SubexponentialSAT.SubexpKernelControl.emit`, `OAI.Algorithms.SubexponentialSAT.SubexpOrderedTupleStep.step`.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLog_IdempotentProgramService`, `SubexponentialSAT_SqrtLog_IrreducibleSearchBootstrap`, `SubexponentialSAT_SqrtLog_IrreducibleSearchBootstrapPreparation`, `SubexponentialSAT_SqrtLog_IrreducibleSearchEnumeration`, `SubexponentialSAT_SqrtLog_IrreducibleSearchNativeScan`, `SubexponentialSAT_SqrtLog_IrreducibleSearchProgram`, `SubexponentialSAT_SqrtLog_IrreducibleSearchProgramDot`, `SubexponentialSAT_SqrtLog_IrreducibleSearchProgramDotRun`, `SubexponentialSAT_SqrtLog_IrreducibleSearchProgramLift`, `SubexponentialSAT_SqrtLog_IrreducibleSearchProgramScalar`, `SubexponentialSAT_SqrtLog_SquarefreeScaleProgram`, `SubexponentialSAT_SubexpKernelControl`, `SubexponentialSAT_SubexpOrderedTupleStep`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S084`, `OAIQ081S085`, `OAIQ081S086`, `OAIQ081S087` and `OAIQ081S088` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S121`, `OAIQ081S122`, `OAIQ081S135` and `OAIQ081S136`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S084
import Definitions.Def_OAIQ081S085
import Definitions.Def_OAIQ081S086
import Definitions.Def_OAIQ081S087
import Definitions.Def_OAIQ081S088

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentProgramService
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Lift the common 32-stack arithmetic ABI into the Newton machine and prove
that the source-preserving register wrapper has the exact specified effect. -/
namespace SubexponentialSAT.SqrtLog.IdempotentProgram

open BitProgram StructuredCalls

theorem callService_eval (command : Cmd 8 32) (a b : State 8 32)
    (d : RegisterData) (result : Fin 41 → List Bool) (n : ℕ)
    (hr : a.regs = d.regs)
    (ha : ∀ i, d.stacks (servicePorts i) = a.stacks i)
    (hb : ∀ i, result (servicePorts i) = b.stacks i)
    (hout : ∀ j, (¬∃ i, servicePorts i = j) → result j = d.stacks j)
    (run : Eval command n a b) :
    ∃ e, Eval (callService command) (n+1) d e ∧ e.stacks = result := by
  have he := eval_call_lifted (compiled command 8 0) id servicePorts d
    Function.injective_id servicePorts_injective (compiled_halt_trace run 8 0)
  have hin : embedState id servicePorts d a = d := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id servicePorts_injective
    · intro i; exact (congrFun hr i).symm
    · intro i hi; exact False.elim (hi ⟨i,rfl⟩)
    · exact ha
    · intro i hi; rfl
  rw [hin] at he
  refine ⟨embedState id servicePorts d b, he, ?_⟩
  funext j
  by_cases hj : ∃ i, servicePorts i = j
  · obtain ⟨i,rfl⟩ := hj
    rw [embedState_stack _ _ _ _ servicePorts_injective]
    exact (hb i).symm
  · rw [embedState_stack_frame _ _ _ _ j hj]
    exact (hout j hj).symm

end SubexponentialSAT.SqrtLog.IdempotentProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpOrderedTupleStep
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! # A fixed Cartesian expansion in exact enumeration order -/

namespace SubexponentialSAT.SubexpOrderedTupleStep

open BitProgram StructuredCalls Subexp.TupleProgram SubexpOrderedTupleData
open Subexp.BlockSearchPreparation (restrictState lifted_call)

theorem reverseRecords_eval (records : Records) (a : State 10 9)
    (h0 : a.stacks 0 = [false]) (h2 : a.stacks 2 = [])
    (h5 : a.stacks 5 = ProgramEncoding.encodeRecords records) :
    ∃ n next, n ≤ 10 * (ProgramEncoding.encodeRecords records).length ∧
      next.stacks 0 = ProgramEncoding.encodeRecords records.reverse ∧
      next.stacks 2 = [] ∧ next.stacks 5 = [] ∧
      (∀ i, i ≠ 0 → i ≠ 2 → i ≠ 5 → next.stacks i = a.stacks i) ∧
      next.regs 9 = a.regs 9 ∧ Eval reverseRecords n a next := by
  let small := SubexpNormalizeProgram.filterState false true false [] (a.stacks 1)
    (ProgramEncoding.encodeRecords records.reverse) []
  have hstart : restrictState reverseRegisters reverseStacks a =
      SubexpNormalizeProgram.filterState (a.regs 0) (a.regs 1) (a.regs 2)
        (ProgramEncoding.encodeRecords records) (a.stacks 1) [false] [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i
      fin_cases i <;> simp [reverseRegisters,SubexpPostfixControl.triple]
    · funext i
      fin_cases i <;> simp [reverseStacks,SubexpPostfixControl.quadruple,h0,h2,h5]
  have hr := SubexpNormalizeProgram.reverseRecords_runsIn records [] [] (a.stacks 1)
    (a.regs 0) (a.regs 1) (a.regs 2)
  obtain ⟨n,hn,he⟩ := lifted_call SubexpNormalizeProgram.reverseRecordsProgram
    reverseRegisters reverseStacks reverseRegisters_injective reverseStacks_injective
    a small (10 * (ProgramEncoding.encodeRecords records).length)
    (by simpa [hstart,small,ProgramEncoding.encodeRecords,Encoding.encodeList] using hr)
  refine ⟨n,embedState reverseRegisters reverseStacks a small,hn,?_,?_,?_,?_,?_,he⟩
  · simpa [reverseStacks,small,SubexpNormalizeProgram.filterState,
      SubexpPostfixControl.quadruple] using
      embedState_stack reverseRegisters reverseStacks a small reverseStacks_injective 2
  · simpa [reverseStacks,small,SubexpNormalizeProgram.filterState,
      SubexpPostfixControl.quadruple] using
      embedState_stack reverseRegisters reverseStacks a small reverseStacks_injective 3
  · simpa [reverseStacks,small,SubexpNormalizeProgram.filterState,
      SubexpPostfixControl.quadruple] using
      embedState_stack reverseRegisters reverseStacks a small reverseStacks_injective 0
  · intro i hi0 hi2 hi5
    by_cases hi1 : i = 1
    · subst i
      simpa [reverseStacks,small,SubexpNormalizeProgram.filterState,
        SubexpPostfixControl.quadruple] using
        embedState_stack reverseRegisters reverseStacks a small reverseStacks_injective 1
    · apply embedState_stack_frame
      rintro ⟨j,hj⟩
      fin_cases j <;> simp_all [reverseStacks]
  · apply embedState_register_frame
    rintro ⟨j,hj⟩
    fin_cases j <;> simp [reverseRegisters] at hj

/-- Expand all tuples, reverse the record order, and restore the empty
accumulator. Every loop is in the two fixed called programs. -/
abbrev step : Cmd 10 9 :=
  .seq cartesianCmd (.seq (pushConst 0 6 false)
    (.seq reverseRecords (pushConst 5 6 false)))

theorem step_eval (alphabet rows : Records) (depth : List Bool) (guard : Bool)
    (a : State 10 9) (ha : Ready alphabet rows depth guard a) :
    ∃ n next, n ≤ stepCost rows alphabet ∧
      Ready alphabet (orderedCartesian rows alphabet) depth guard next ∧
      Eval step n a next := by
  obtain ⟨n,b,hn,hb,hb0,hb2,hb5,ht⟩ :=
    cartesian_eval rows alphabet [] depth guard a ha.1 ha.2.1 ha.2.2.1 ha.2.2.2
  simp only [List.append_nil] at hb5
  let c := pushedState 0 6 false b
  have hc0 : c.stacks 0 = [false] := by simp [c,hb0]
  have hc2 : c.stacks 2 = [] := by simp [c,hb2]
  have hc5 : c.stacks 5 = ProgramEncoding.encodeRecords (cartesianOutput rows alphabet) := by
    simp [c,hb5]
  obtain ⟨m,d,hm,hd0,hd2,hd5,hframe,hreg,hr⟩ :=
    reverseRecords_eval (cartesianOutput rows alphabet) c hc0 hc2 hc5
  let e := pushedState 5 6 false d
  have h1 := pushConst_eval 0 6 false b
  have h2 := pushConst_eval 5 6 false d
  refine ⟨n + (2 + (m + 2)),e,?_,?_,ht.seq (h1.seq (hr.seq h2))⟩
  · dsimp [stepCost]
    omega
  · rcases hb with ⟨hb1,hb3,hb4,hb6,hb7,hb8,hb9⟩
    have hd1 := hframe 1 (by decide) (by decide) (by decide)
    have hd3 := hframe 3 (by decide) (by decide) (by decide)
    have hd4 := hframe 4 (by decide) (by decide) (by decide)
    have hd6 := hframe 6 (by decide) (by decide) (by decide)
    have hd7 := hframe 7 (by decide) (by decide) (by decide)
    have hd8 := hframe 8 (by decide) (by decide) (by decide)
    simp [Ready,outerInvariant,e,hd0,hd2,hd5,hd1,hd3,hd4,hd6,hd7,hd8,
      hreg,c,hb1,hb3,hb4,hb6,hb7,hb8,hb9,orderedCartesian_eq_reverse]

end SubexponentialSAT.SubexpOrderedTupleStep

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IrreducibleSearchEnumeration
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed finite-control generation in the exact irreducible-search order. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchEnumeration

open BitProgram StructuredCalls Subexp.TupleProgram SubexpOrderedTupleData

/-- The depth is stack data; the ordered Cartesian body is fixed. -/
abbrev powerLoop : Cmd 10 9 :=
  .while 9 (.seq SubexpOrderedTupleStep.step readDepth)
abbrev powerCmd : Cmd 10 9 := .seq readDepth powerLoop

theorem powerCmd_eval (alphabet rows : Records) (depth : List Bool) (guard : Bool)
    (a : State 10 9) (ha : Ready alphabet rows depth guard a) :
    ∃ n next, n ≤ powerCost alphabet depth.length rows ∧
      Ready alphabet (orderedRows alphabet depth.length rows) [] false next ∧
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
      obtain ⟨n, c, hn, hc, ht⟩ := SubexpOrderedTupleStep.step_eval alphabet rows depth true b hb
      obtain ⟨m, d, hm, hd, hr⟩ := ih (orderedCartesian rows alphabet) true c hc
      cases hr with
      | @seq first second k l x y z hp hl =>
          refine ⟨1 + (n + k + l + 1), d, ?_, hd, ?_⟩
          · simp only [List.length_cons, powerCost]
            omega
          · exact (readDepth_eval a).seq
              (Eval.while_true hb.1.2.2.2.2.2.2 (ht.seq hp) hl)


abbrev generateCmd : Cmd 10 9 := .seq initCmd powerCmd
def program := StructuredCalls.compiled generateCmd 1 0

theorem program_runsIn (alphabet : Records) (depth : List Bool) (guard : Bool)
    (a : State 10 9) (ha : outerInvariant alphabet depth guard a)
    (h0 : a.stacks 0 = []) (h2 : a.stacks 2 = []) (h5 : a.stacks 5 = []) :
    ∃ next, Ready alphabet (orderedRows alphabet depth.length [[]]) [] false next ∧
      RunsIn program (powerCost alphabet depth.length [[]] + 9)
        (a.withPC (some program.entry)) (next.withPC none) := by
  obtain ⟨b,hb,hi⟩ := initCmd_eval alphabet depth guard a ha h0 h2 h5
  obtain ⟨n,next,hn,hs,he⟩ := powerCmd_eval alphabet [[]] depth guard b hb
  refine ⟨next,hs,8+n+1,by omega,?_⟩
  exact StructuredCalls.compiled_halt_trace (hi.seq he) 1 0

open SubexpEnumerationPayload SubexpTupleRefinement

end SubexponentialSAT.SqrtLog.IrreducibleSearchEnumeration

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IrreducibleSearchBootstrapPreparation
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


/-! A fixed framed call generates an ordered table from a runtime unary depth.
Only its output and depth ports change; the generator's sentinel is paid for
and cleared before returning. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchBootstrap

open BitProgram StructuredCalls
open Subexp.TupleProgram SubexpOrderedTupleData
open SubexpEnumerationPayload SubexpTupleRefinement

abbrev generateAt (candidate : Bool) : Cmd 22 28 :=
  .seq (.call (ProgramLinking.liftProgram IrreducibleSearchEnumeration.program
    generatorRegs (generatorMap candidate))) (clearCmd 3)

end SubexponentialSAT.SqrtLog.IrreducibleSearchBootstrap


/-! Paid construction of both search tables from a single unary depth word. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchBootstrap

open BitProgram StructuredCalls


abbrev command : Cmd 22 28 :=
  .seq (copyCmd 14 22)
  (.seq (Subexp.TupleProgram.pushConst 22 0 false)
  (.seq (pushWord 10 alphabetWord)
  (.seq (copyCmd 14 6)
  (.seq (generateAt true)
  (.seq (copyCmd 22 6)
  (.seq (copyCmd 22 6)
  (.seq (generateAt false)
  (.seq (clearCmd 10) RegisterResetProgram.all))))))))

end SubexponentialSAT.SqrtLog.IrreducibleSearchBootstrap

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IrreducibleSearchProgramScalar
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed truth-table arithmetic for the irreducible search over F₃

The six input bits select one of 64 *static* leaves. No parameter of the
polynomial search occurs in this instruction table. The two output bits
encode the multiply-add `s + a*b` in the same two-bit scalar format as the
audited tuple generator.
-/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredProgram

def writtenPair {R S : ℕ} (lo hi : Fin R) (bits : Bool × Bool)
    (d : State R S) : State R S :=
  (Atom.set hi bits.2).eval ((Atom.set lo bits.1).eval d)

theorem writePair_eval {R S : ℕ} (lo hi : Fin R) (bits : Bool × Bool)
    (d : State R S) : Eval (writePair lo hi bits) 2 d (writtenPair lo hi bits d) :=
  (Eval.atom _ _).seq (Eval.atom _ _)

theorem truthTable_eval {R S : ℕ} (lo hi : Fin R)
    (inputs : List (Fin R)) (f : List Bool → Bool × Bool) (d : State R S) :
    Eval (truthTable lo hi inputs f) (inputs.length + 2) d
      (writtenPair lo hi (f (inputs.map d.regs)) d) := by
  induction inputs generalizing f with
  | nil => exact writePair_eval lo hi (f []) d
  | cons i is ih =>
      cases h : d.regs i with
      | false =>
          have he := Eval.ite_false (yes := truthTable lo hi is (fun bs => f (true :: bs)))
            h (ih (fun bs => f (false :: bs)))
          simpa [truthTable, h, Nat.add_assoc] using he
      | true =>
          have he := Eval.ite_true (no := truthTable lo hi is (fun bs => f (false :: bs)))
            h (ih (fun bs => f (true :: bs)))
          simpa [truthTable, h, Nat.add_assoc] using he

end SubexponentialSAT.SqrtLog.IrreducibleSearchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IrreducibleSearchProgramDot
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldE
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed bit program for the dynamically long F₃ dot product. Every
coefficient is physically read and every multiply-add uses the static
64-entry bit table. The source arrays are consumed. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredProgram

def atomsResult {R S : ℕ} (as : List (Atom R S)) (d : State R S) : State R S :=
  as.foldl (fun s a => a.eval s) d

theorem atoms_eval {R S : ℕ} (as : List (Atom R S)) (d : State R S) :
    Eval (atomsCommand as) as.length d (atomsResult as d) := by
  induction as generalizing d with
  | nil => exact .skip d
  | cons a as ih =>
      simpa [atomsCommand, atomsResult, Nat.add_comm] using
        (Eval.atom a d).seq (ih (a.eval d))

def dotState (as bs : List IrreducibleSearch.F) (s : IrreducibleSearch.F)
    (regs : Fin 8 → Bool) (output : List Bool) : State 8 3 :=
  ⟨Function.update (Function.update regs 4 (scalarBits s).1) 5 (scalarBits s).2,
    ![coefficientArray as, coefficientArray bs, output]⟩

def dotGuardState (as bs : List IrreducibleSearch.F) (s : IrreducibleSearch.F)
    (regs : Fin 8 → Bool) (output : List Bool) : State 8 3 :=
  (Atom.pop 0 0 6).eval (dotState as bs s regs output)

theorem dotBody_eval (a b s : IrreducibleSearch.F)
    (as bs : List IrreducibleSearch.F) (regs : Fin 8 → Bool) (output : List Bool) :
    ∃ nextRegs, Eval dotBody 14
      (dotGuardState (a :: as) (b :: bs) s regs output)
      (dotGuardState as bs (s + a * b) nextRegs output) := by
  let d0 := dotGuardState (a :: as) (b :: bs) s regs output
  let d1 := atomsResult dotReadAtoms d0
  let d2 := writtenPair (S := 3) 6 7 (scalarBits (s + a * b)) d1
  let d3 := atomsResult dotCopyAtoms d2
  have hcalc : Eval dotScalar 8 d1 d2 := by
    have he := truthTable_eval (S := 3) (6 : Fin 8) 7 [0, 1, 2, 3, 4, 5]
      multiplyAddBits d1
    simpa [dotScalar, d1, d0, atomsResult, dotReadAtoms, dotGuardState, dotState,
      Atom.eval, Atom.instr, State.ofCfg, State.withPC, execInstr,
      readRegs, coefficientArray_cons, coefficientWord_eq, multiplyAddBits,
      scalarValue_bits, d2] using he
  have hstate : d3 = dotState as bs (s + a * b) d3.regs output := by
    change State.mk d3.regs d3.stacks = State.mk _ _
    congr 1
    · funext i
      fin_cases i <;>
        simp [d3, d2, d1, d0, atomsResult, dotCopyAtoms, dotReadAtoms,
          writtenPair, dotGuardState, dotState, Atom.eval, Atom.instr,
          State.ofCfg, execInstr, readRegs]
    · funext i
      fin_cases i <;>
        simp [d3, d2, d1, d0, atomsResult, dotCopyAtoms, dotReadAtoms,
          writtenPair, dotGuardState, dotState, Atom.eval, Atom.instr,
          State.ofCfg, execInstr, readRegs,
          coefficientArray_cons, coefficientWord_eq]
  refine ⟨d3.regs, ?_⟩
  have he := (atoms_eval dotReadAtoms d0).seq
    (hcalc.seq ((atoms_eval dotCopyAtoms d2).seq (Eval.atom (.pop 0 0 6) d3)))
  rw [hstate] at he
  simpa only [d0, dotBody, dotReadAtoms, dotCopyAtoms, List.length_cons,
    List.length_nil, Nat.reduceAdd, dotGuardState] using he

end SubexponentialSAT.SqrtLog.IrreducibleSearchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IrreducibleSearchProgramDotRun
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldE
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Complete execution of the fixed F₃ dot product, including initialization,
serialization of its output, the final halt, and primitive simulation. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredProgram

def dotInput (as bs : List IrreducibleSearch.F) (regs : Fin 8 → Bool)
    (output : List Bool) : State 8 3 :=
  ⟨regs, ![coefficientArray as, coefficientArray bs, output]⟩

theorem dotInitial_result (as bs : List IrreducibleSearch.F)
    (regs : Fin 8 → Bool) (output : List Bool) :
    atomsResult dotInitialAtoms (dotInput as bs regs output) =
      dotGuardState as bs 0 regs output := by
  have hz : scalarBits (0 : IrreducibleSearch.F) = (false, false) := by decide
  simp [atomsResult, dotInitialAtoms, dotInput, dotGuardState, dotState,
    Atom.eval, Atom.instr, State.ofCfg, execInstr, hz]

theorem dotFinal_result (s : IrreducibleSearch.F)
    (regs : Fin 8 → Bool) (output : List Bool) :
    atomsResult dotFinalAtoms (dotGuardState [] [] s regs output) =
      ⟨(dotGuardState [] [] s regs output).regs,
        ![[], [], coefficientWord s ++ output]⟩ := by
  simp [atomsResult, dotFinalAtoms, dotGuardState, dotState,
    Atom.eval, Atom.instr, State.ofCfg, execInstr,
    readRegs, coefficientWord_eq]
  all_goals (funext i; fin_cases i <;> simp)

end SubexponentialSAT.SqrtLog.IrreducibleSearchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IrreducibleSearchProgramLift
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Framed invocation of the fixed three-stack prefix and dot programs. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

noncomputable def afterThree {r R S : ℕ} (regs : Fin r ↪ Fin R) (ports : Fin 3 ↪ Fin S)
    (rf : Fin r → Bool) (a b c : List Bool) (d : State R S) : State R S :=
  ⟨Function.extend regs rf d.regs, replaceThree ports a b c d.stacks⟩

theorem three_embed {r R S : ℕ} (regs : Fin r ↪ Fin R) (ports : Fin 3 ↪ Fin S)
    (rf : Fin r → Bool) (a b c : List Bool) (d : State R S) :
    embedState regs ports d ⟨rf, ![a, b, c]⟩ = afterThree regs ports rf a b c d := by
  apply embedState_eq_of_ports regs ports d _ _ regs.injective ports.injective
  · intro i
    exact regs.injective.extend_apply _ _ _
  · intro i hi
    exact Function.extend_apply' _ _ _ hi
  · intro i
    exact replaceThree_at ports a b c d.stacks i
  · intro i hi
    exact replaceThree_frame ports a b c d.stacks i hi

theorem three_initial {r R S : ℕ} (regs : Fin r ↪ Fin R) (ports : Fin 3 ↪ Fin S)
    (a b c : List Bool) (d : State R S)
    (ha : d.stacks (ports 0) = a) (hb : d.stacks (ports 1) = b)
    (hc : d.stacks (ports 2) = c) :
    embedState regs ports d ⟨fun i => d.regs (regs i), ![a, b, c]⟩ = d := by
  apply embedState_eq_of_ports regs ports d _ _ regs.injective ports.injective
  · intro i; rfl
  · intros; rfl
  · intro i
    fin_cases i <;> assumption
  · intros; rfl

theorem prefixCall_eval {R S : ℕ} (regs : Fin 6 ↪ Fin R) (ports : Fin 3 ↪ Fin S)
    (as : List IrreducibleSearch.F) (count output : List Bool) (d : State R S)
    (ha : d.stacks (ports 0) = coefficientArray as)
    (hb : d.stacks (ports 1) = count) (hc : d.stacks (ports 2) = output) :
    ∃ rf, Eval (prefixCall regs ports) (7 * count.length + 3) d
      (afterThree regs ports rf (coefficientArray (as.drop count.length)) []
        (coefficientArray (paddedPrefix count.length as).reverse ++ output) d) := by
  obtain ⟨rf, he⟩ := prefixReverse_trace as count output (fun i => d.regs (regs i))
  have ht := eval_call_lifted prefixReverseProgram regs ports d regs.injective ports.injective
    (a := ⟨fun i => d.regs (regs i), ![coefficientArray as, count, output]⟩)
    (b := ⟨rf, ![coefficientArray (as.drop count.length), [],
      coefficientArray (paddedPrefix count.length as).reverse ++ output]⟩) he
  rw [three_initial regs ports _ _ _ d ha hb hc, three_embed] at ht
  exact ⟨rf, ht⟩

end SubexponentialSAT.SqrtLog.IrreducibleSearchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IrreducibleSearchProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldE
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Closed fixed-bit F₃ factor checker. The complete command is independent
of the degree. All coefficient addresses and loop bounds are runtime unary
words; source vectors are preserved and scratch stacks are discharged. -/


/-! Coefficient -/

/-! A fixed coefficient kernel: two preserved source arrays, a preserved
unary coefficient address plus one, and an output stack. Every copy, padded
prefix, coefficient reversal, multiply-add and cleanup is an actual call. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage

def coefficientState (as bs : List IrreducibleSearch.F) (count output : List Bool)
    (regs : Fin 16 → Bool) : State 16 11 :=
  ⟨regs, ![coefficientArray as, coefficientArray bs, count,
    [], [], [], [], [], [], output, []]⟩

end SubexponentialSAT.SqrtLog.IrreducibleSearchProgram


/-! CoefficientRun -/

/-! The closed, fixed-program boundary for one arbitrary convolution
coefficient. Its sources and runtime unary address are preserved and all
work stacks are empty again. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem coefficientValue_convolution {d : ℕ}
    (a b : Fin d → IrreducibleSearch.F) (j : ℕ) :
    coefficientValue (List.ofFn a) (List.ofFn b) (j + 1) =
      IrreducibleSearch.convolution a b j := by
  unfold coefficientValue
  rw [paddedPrefix_convolutionLeft, paddedPrefix_convolutionRight, convolution_dot]

end SubexponentialSAT.SqrtLog.IrreducibleSearchProgram


/-! ProductLift -/

/-! A framed invocation of the source-preserving coefficient kernel. The
extra stack stores the remaining runtime product length. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def productState (as bs : List IrreducibleSearch.F) (count remaining output : List Bool)
    (regs : Fin 16 → Bool) : State 16 12 :=
  ⟨regs, ![coefficientArray as, coefficientArray bs, count,
    [], [], [], [], [], [], output, [], remaining]⟩

theorem product_embed (as bs : List IrreducibleSearch.F)
    (count remaining output newOutput : List Bool) (regs finalRegs : Fin 16 → Bool) :
    embedState id coefficientStackPorts (productState as bs count remaining output regs)
      (coefficientState as bs count newOutput finalRegs) =
      productState as bs count remaining newOutput finalRegs := by
  apply embedState_eq_of_ports id coefficientStackPorts _ _ _
    Function.injective_id coefficientStackPorts.injective
  · intro i; rfl
  · intro i hi; exact (hi ⟨i, rfl⟩).elim
  · intro i
    fin_cases i <;> rfl
  · intro i hi
    have h : i = 11 := by
      apply Fin.ext
      by_contra hn
      have hv : i.val < 11 := by omega
      exact hi ⟨⟨i.val, hv⟩, rfl⟩
    subst i
    simp [productState]

end SubexponentialSAT.SqrtLog.IrreducibleSearchProgram


/-! Product -/

/-! A fixed outer loop runs the coefficient kernel at successively longer
unary addresses. Source arrays are preserved; all output coefficients are
physically written in decreasing degree order. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.StructuredProgram (Atom)

def productGuardState (as bs : List IrreducibleSearch.F)
    (count remaining output : List Bool) (regs : Fin 16 → Bool) : State 16 12 :=
  (Atom.pop 11 14 15).eval (productState as bs count remaining output regs)

def productOutput (as bs : List IrreducibleSearch.F) : ℕ → ℕ → List Bool → List Bool
  | _, 0, output => output
  | start, n + 1, output => productOutput as bs (start + 1) n
      (coefficientWord (coefficientValue as bs start) ++ output)

end SubexponentialSAT.SqrtLog.IrreducibleSearchProgram


/-! ProductRun -/

namespace SubexponentialSAT.SqrtLog.IrreducibleSearchProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.StructuredProgram (Atom)

theorem productOutput_value (as bs : List IrreducibleSearch.F) (start n : ℕ)
    (output : List Bool) :
    productOutput as bs start n output =
      coefficientArray (((List.range' start n).map (coefficientValue as bs)).reverse) ++ output := by
  induction n generalizing start output with
  | zero => simp [productOutput]
  | succ n ih =>
      simp [productOutput, ih, List.range'_succ, List.reverse_cons,
        coefficientArray_append, coefficientArray_cons, List.append_assoc]

theorem productOutput_convolution {d : ℕ} (a b : Fin d → IrreducibleSearch.F)
    (n : ℕ) (output : List Bool) :
    productOutput (List.ofFn a) (List.ofFn b) 1 n output =
      coefficientArray (((List.range n).map (IrreducibleSearch.convolution a b)).reverse) ++ output := by
  rw [productOutput_value]
  congr 3
  apply List.ext_getElem (by simp)
  intro i hi hi'
  simp only [List.getElem_map, List.getElem_range', List.getElem_range, Nat.one_mul]
  simpa only [Nat.add_comm, Nat.one_mul, Nat.mul_one] using coefficientValue_convolution a b i

end SubexponentialSAT.SqrtLog.IrreducibleSearchProgram


/-! Monic -/

/-! Appending the implicit monic coefficient uses two physical transfers.
No input-dependent instruction table or uncharged array append is used. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.StructuredProgram (Atom)

def transferState {S : ℕ} (src dst : Fin S) (d : State 16 S) : State 16 S :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.transferStacks src dst d.stacks⟩

theorem transferCommand_eval {S : ℕ} (src dst : Fin S) (hne : src ≠ dst)
    (d : State 16 S) :
    Eval (transferCommand src dst) (3 * (d.stacks src).length + 3) d
      (transferState src dst d) := by
  exact Eval.call _ (ListRegisterProgram.transfer_run src dst (0 : Fin 16) 1
    hne (by decide) d.regs d.stacks)

theorem appendOneCommand_eval {S : ℕ} (src tmp : Fin S) (hne : src ≠ tmp)
    (cs : List IrreducibleSearch.F) (d : State 16 S)
    (hsrc : d.stacks src = coefficientArray cs) (htmp : d.stacks tmp = []) :
    ∃ rf, Eval (appendOneCommand src tmp) (12 * cs.length + 10) d
      ⟨rf, Function.update d.stacks src (coefficientArray (cs ++ [1]))⟩ := by
  let d1 := transferState src tmp d
  let d2 := atomsResult (monicAtoms src) d1
  let d3 := transferState tmp src d2
  have he := (transferCommand_eval src tmp hne d).seq
    ((Eval.base (atoms_eval (monicAtoms src) d1)).seq
      (transferCommand_eval tmp src hne.symm d2))
  have hl : (d2.stacks tmp).length = 2 * cs.length := by
    simp [d2, d1, atomsResult, monicAtoms, transferState, StackRoutines.transferStacks,
      Atom.eval, Atom.instr, StructuredProgram.State.ofCfg,
      execInstr, hne, hne.symm, hsrc, htmp, coefficientArray_length]
  have hs : d3.stacks = Function.update d.stacks src (coefficientArray (cs ++ [1])) := by
    funext i
    by_cases hi : i = src
    · subst i
      simp [d3, d2, d1, transferState, StackRoutines.transferStacks, atomsResult,
        monicAtoms, Atom.eval, Atom.instr, StructuredProgram.State.ofCfg, execInstr, hne, hne.symm, hsrc, htmp,
        coefficientArray_append, coefficientArray_cons, coefficientWord_eq, scalarBits] ; decide
    · by_cases hit : i = tmp
      · subst i
        simp [d3, d2, d1, transferState, StackRoutines.transferStacks, atomsResult,
          monicAtoms, Atom.eval, Atom.instr, StructuredProgram.State.ofCfg, execInstr, hne, hne.symm, htmp]
      · simp [d3, d2, d1, transferState, StackRoutines.transferStacks, atomsResult,
          monicAtoms, Atom.eval, Atom.instr, StructuredProgram.State.ofCfg, execInstr, hi, hit]
  refine ⟨d3.regs, ?_⟩
  have hd : d3 = ⟨d3.regs, Function.update d.stacks src (coefficientArray (cs ++ [1]))⟩ := by
    exact SubexpScanPrimitives.state_ext rfl hs
  change Eval (appendOneCommand src tmp) _ d d3 at he
  rw [hd] at he
  simpa only [hl, hsrc, coefficientArray_length, monicAtoms, List.length_cons,
    List.length_nil, Nat.reduceAdd, show 3 * (2 * cs.length) + 3 +
      (4 + (3 * (2 * cs.length) + 3)) = 12 * cs.length + 10 by omega] using he

end SubexponentialSAT.SqrtLog.IrreducibleSearchProgram


/-! MonicAlgebra -/

namespace SubexponentialSAT.SqrtLog.IrreducibleSearchProgram

open SubexponentialSAT.BitProgram

theorem productComparison_eq {d : ℕ} (c : Fin d → IrreducibleSearch.F)
    (a b : Fin (d + 1) → IrreducibleSearch.F) :
    decide (coefficientArray (((List.range (2 * d + 1)).map
        (IrreducibleSearch.convolution a b)).reverse) =
      coefficientArray (paddedPrefix (2 * d + 1) (List.ofFn c ++ [1])).reverse) =
      IrreducibleSearch.productEq c a b := by
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, coefficientArray_injective.eq_iff, List.reverse_inj,
    monicArray_padded, IrreducibleSearch.productEq, List.all_eq_true,
    List.mem_range, decide_eq_true_eq]
  constructor
  · intro h j hj
    have he := congrArg (fun xs => xs[j]?) h
    rw [List.getElem?_map, List.getElem?_range hj, Option.map_some,
      List.getElem?_ofFn, dite_eq_left hj] at he
    exact Option.some.inj he
  · intro h
    apply List.ext_getElem (by simp)
    intro j hj hj'
    simpa only [List.getElem_map, List.getElem_range, List.getElem_ofFn] using
      h j (by simpa only [List.length_map, List.length_range] using hj)

end SubexponentialSAT.SqrtLog.IrreducibleSearchProgram


/-! CheckLift -/

/-! Framed calls to the physical Boolean predicates. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

noncomputable def afterTwo {r R S : ℕ} (regs : Fin r ↪ Fin R) (ports : Fin 2 ↪ Fin S)
    (rf : Fin r → Bool) (a b : List Bool) (d : State R S) : State R S :=
  ⟨Function.extend regs rf d.regs, replaceTwo ports a b d.stacks⟩

theorem two_embed {r R S : ℕ} (regs : Fin r ↪ Fin R) (ports : Fin 2 ↪ Fin S)
    (rf : Fin r → Bool) (a b : List Bool) (d : State R S) :
    embedState regs ports d ⟨rf, ![a, b]⟩ = afterTwo regs ports rf a b d := by
  apply embedState_eq_of_ports regs ports d _ _ regs.injective ports.injective
  · intro i; exact regs.injective.extend_apply _ _ _
  · intro i hi; exact Function.extend_apply' _ _ _ hi
  · intro i; fin_cases i <;> simp [afterTwo, replaceTwo, ports.injective.eq_iff]
  · intro i hi
    have h0 : i ≠ ports 0 := fun h => hi ⟨0, h.symm⟩
    have h1 : i ≠ ports 1 := fun h => hi ⟨1, h.symm⟩
    simp [afterTwo, replaceTwo, h0, h1]

theorem two_initial {r R S : ℕ} (regs : Fin r ↪ Fin R) (ports : Fin 2 ↪ Fin S)
    (a b : List Bool) (d : State R S)
    (ha : d.stacks (ports 0) = a) (hb : d.stacks (ports 1) = b) :
    embedState regs ports d ⟨fun i => d.regs (regs i), ![a, b]⟩ = d := by
  apply embedState_eq_of_ports regs ports d _ _ regs.injective ports.injective
  · intro i; rfl
  · intros; rfl
  · intro i; fin_cases i <;> assumption
  · intros; rfl

theorem compareCall_eval {S : ℕ} (ports : Fin 2 ↪ Fin S)
    (a b : List Bool) (hlen : a.length = b.length) (d : State 16 S)
    (ha : d.stacks (ports 0) = a) (hb : d.stacks (ports 1) = b) :
    ∃ rf, Eval (compareCall ports) (6 * a.length + 4) d
        (afterTwo fourRegisters ports rf [] [] d) ∧
      (afterTwo fourRegisters ports rf [] [] d).regs 3 = decide (a = b) := by
  obtain ⟨rf, he, hv⟩ := compare_run a b hlen (fun i => d.regs (fourRegisters i))
  have ht := eval_call_lifted compareProgram fourRegisters ports d
    fourRegisters.injective ports.injective
    (a := ⟨fun i => d.regs (fourRegisters i), ![a, b]⟩)
    (b := ⟨rf, ![[], []]⟩) he
  change Eval (compareCall ports) _
    (embedState fourRegisters ports d ⟨fun i => d.regs (fourRegisters i), ![a, b]⟩)
    (embedState fourRegisters ports d ⟨rf, ![[], []]⟩) at ht
  rw [two_initial _ _ _ _ _ ha hb, two_embed] at ht
  refine ⟨rf, ht, ?_⟩
  change Function.extend fourRegisters rf d.regs (fourRegisters 3) = _
  rw [fourRegisters.injective.extend_apply]
  exact hv

noncomputable def afterOne {r R S : ℕ} (regs : Fin r ↪ Fin R) (port : Fin S)
    (rf : Fin r → Bool) (a : List Bool) (d : State R S) : State R S :=
  ⟨Function.extend regs rf d.regs, Function.update d.stacks port a⟩

theorem one_embed {r R S : ℕ} (regs : Fin r ↪ Fin R) (port : Fin S)
    (rf : Fin r → Bool) (a : List Bool) (d : State R S) :
    embedState regs (onePort port) d ⟨rf, fun _ => a⟩ = afterOne regs port rf a d := by
  apply embedState_eq_of_ports regs (onePort port) d _ _ regs.injective (onePort port).injective
  · intro i; exact regs.injective.extend_apply _ _ _
  · intro i hi; exact Function.extend_apply' _ _ _ hi
  · intro i
    fin_cases i
    change Function.update d.stacks port a port = a
    simp
  · intro i hi
    have h : i ≠ port := fun h => hi ⟨0, h.symm⟩
    simp [afterOne, h]

theorem one_initial {r R S : ℕ} (regs : Fin r ↪ Fin R) (port : Fin S)
    (a : List Bool) (d : State R S) (ha : d.stacks port = a) :
    embedState regs (onePort port) d ⟨fun i => d.regs (regs i), fun _ => a⟩ = d := by
  apply embedState_eq_of_ports regs (onePort port) d _ _ regs.injective (onePort port).injective
  · intro i; rfl
  · intros; rfl
  · intro i; exact ha
  · intros; rfl

theorem nonconstantCall_eval {S d : ℕ} (port : Fin S)
    (a : Fin (d + 1) → IrreducibleSearch.F) (s : State 16 S)
    (ha : s.stacks port = coefficientArray (List.ofFn a)) :
    ∃ rf, Eval (nonconstantCall port) (5 * d + 6) s
        (afterOne fourRegisters port rf [] s) ∧
      (afterOne fourRegisters port rf [] s).regs 3 = IrreducibleSearch.nonconstant a := by
  obtain ⟨rf, he, hv⟩ := nonconstant_vector_run a (fun i => s.regs (fourRegisters i))
  have hf (x : List Bool) : (![x] : Fin 1 → List Bool) = (fun _ => x) := by
    funext i; fin_cases i; rfl
  simp only [nonconstantCfg, hf] at he
  have ht := eval_call_lifted nonconstantProgram fourRegisters (onePort port) s
    fourRegisters.injective (onePort port).injective
    (a := ⟨fun i => s.regs (fourRegisters i), fun _ => coefficientArray (List.ofFn a)⟩)
    (b := ⟨rf, fun _ => []⟩) he
  change Eval (nonconstantCall port) _
    (embedState fourRegisters (onePort port) s
      ⟨fun i => s.regs (fourRegisters i), fun _ => coefficientArray (List.ofFn a)⟩)
    (embedState fourRegisters (onePort port) s ⟨rf, fun _ => []⟩) at ht
  rw [one_initial _ _ _ _ ha, one_embed] at ht
  refine ⟨rf, ht, ?_⟩
  change Function.extend fourRegisters rf s.regs (fourRegisters 3) = _
  rw [fourRegisters.injective.extend_apply]
  exact hv

end SubexponentialSAT.SqrtLog.IrreducibleSearchProgram


/-! PairProduct -/


/-! Candidate -/


/-! ProductCheck -/


/-! Pair -/

/-! Closed primitive pair test. All three source vectors and the runtime
unary degree are preserved. The return bit is exactly the scalar pairPass. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IrreducibleSearchNativeScan
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed native irreducible-polynomial search: concrete factor callbacks,
saved universal scans, exact ordered candidate selection, and measured cost. -/

/-! A fixed factor-pair callback and universal scan. All checker arithmetic,
record extraction, array splitting, and cleanup use explicit bit programs. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchFactorControl

open BitProgram StructuredCalls IrreducibleSearchProgram
open Subexp.BlockSearchPreparation (restrictState lifted_call)
attribute [local simp] Fin.addCases Fin.coe_ofNat_eq_mod

theorem factorTest_encode {d : ℕ} (c : Fin d → IrreducibleSearch.F)
    (ab : (Fin (d + 1) → IrreducibleSearch.F) × (Fin (d + 1) → IrreducibleSearch.F)) :
    factorTest c (pairEncode ab) = IrreducibleSearch.pairPass c ab :=
  (pairEncode_injective d).extend_apply _ _ _

end SubexponentialSAT.SqrtLog.IrreducibleSearchFactorControl

/-! Fixed first-success scan using the concrete saved factor checker. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchCandidateControl

open BitProgram StructuredCalls IrreducibleSearchProgram
open Subexp.BlockSearchPreparation (restrictState lifted_call)
open SubexpEnumerationPayload SubexpTupleRefinement
attribute [local simp] Fin.addCases Fin.coe_ofNat_eq_mod

def wide (low : State 19 24) (tag present found : Bool)
    (source payload extra : List Bool) : Data :=
  ⟨Fin.addCases (m := 19) (n := 3) (motive := fun _ => Bool) low.regs ![tag,present,found],
    Fin.addCases (m := 24) (n := 4) (motive := fun _ => List Bool)
      low.stacks ![source,payload,[],extra]⟩

theorem embed_wide (before after : State 19 24) (tag present found : Bool)
    (source payload extra : List Bool) :
    embedState lowRegs lowStacks (wide before tag present found source payload extra) after =
      wide after tag present found source payload extra := by
  apply SubexpScanPrimitives.embedState_eq lowRegs lowStacks lowRegs_injective lowStacks_injective
  · intro i; simp [wide, lowRegs]
  · intro i; simp [wide, lowStacks]
  · intro j hj
    revert hj
    refine Fin.addCases (m := 19) (n := 3) (fun i => ?_) (fun i => ?_) j
    · intro hi; exact (hi ⟨i,rfl⟩).elim
    · intro _; simp [wide]
  · intro j hj
    revert hj
    refine Fin.addCases (m := 24) (n := 4) (fun i => ?_) (fun i => ?_) j
    · intro hi; exact (hi ⟨i,rfl⟩).elim
    · intro _; simp [wide]


theorem record_state_wide (low : State 19 24) (tag present found v pr f : Bool)
    (source payload extra newSource newPayload : List Bool) :
    RecordPrograms.state ports (wide low tag present found source payload extra)
      v pr f newSource newPayload = wide low v pr f newSource newPayload extra := by
  apply SubexpScanPrimitives.state_ext
  · funext i; fin_cases i <;> simp [RecordPrograms.state, ports, wide]
  · funext i; fin_cases i <;> simp [RecordPrograms.state, ports, wide]

end SubexponentialSAT.SqrtLog.IrreducibleSearchCandidateControl

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IrreducibleSearchBootstrap
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


namespace SubexponentialSAT.SqrtLog.IrreducibleSearchBootstrap

open BitProgram StructuredCalls
open SubexpEnumerationPayload SubexpTupleRefinement IrreducibleSearchProgram
attribute [local simp] Fin.addCases Fin.coe_ofNat_eq_mod

/-- All table preparation and the first-success scan share one fixed program. -/
abbrev searchCommand : Cmd 22 28 :=
  .seq command (.call IrreducibleSearchCandidateControl.program)


end SubexponentialSAT.SqrtLog.IrreducibleSearchBootstrap

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeScaleProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Base stage. -/
/-! Fixed physical ABI for scaling all coefficients in a sparse dictionary.
The low 32 stacks are the common coefficient-ring service. The eight high
stacks hold source, reversed output, scalar, key, coefficient staging, frame
staging, final output, and a preserved copy of the unary degree. -/

namespace SubexponentialSAT.SqrtLog.Squarefree.ScaleProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

abbrev Data := State 8 40

end SubexponentialSAT.SqrtLog.Squarefree.ScaleProgram

/-! Moves stage. -/

/-! Emit stage. -/

/-! Native stage. -/

/-! Loop stage. -/

/-! Cost stage. -/

/-! Semantics stage. -/

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

def emit (code : Word) (a : Accumulator) : Accumulator :=
  { a with output := code.reverse ++ a.output }

/-! The following induction rule accounts for actual executions of the fixed
payload body. Its premises will be proved for `termBody`, `groupBody`, and
`blockBody`; the exported whole-controller statement has no callback argument. -/

/-! ## Forward-output service boundary -/

end SubexponentialSAT.SubexpKernelControl

end OAI.Algorithms
end


