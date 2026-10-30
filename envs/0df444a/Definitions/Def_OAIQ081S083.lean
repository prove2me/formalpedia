-- Prove2me | Definitions.Def_OAIQ081S083
-- name    : OAIQ081S083
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T22:05:00.522257+00:00
-- url     : https://prove2.me/theorems/d046bd08-2674-4edd-b38c-dc91f1d55cf7
-- title:
--   Definitions bundle OAIQ081S083 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 31 declarations of OpenAI's Lean: 13 definitions and 18 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeParametersProgram.minComparePorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Bank.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Bank.copyCmd`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Bank.state`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Circuit.Ready`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Circuit.lengths`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Circuit.values`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Execute.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Execute.state`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter.HeadSelect.Data`, `OAI.Algorithms.SubexponentialSAT.Subexp.BasisTransposePlanProgram.Data`, `OAI.Algorithms.SubexponentialSAT.SubexpBlockParameterProgram.state`, `OAI.Algorithms.SubexponentialSAT.UnaryForPrograms.popCmd`.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_ProgramStateFrames`, `SubexponentialSAT_SqrtLogSpace_HighQueryAdapter`, `SubexponentialSAT_SqrtLog_CodeParametersProgramUnary`, `SubexponentialSAT_SqrtLog_LeafParametersProgramBank`, `SubexponentialSAT_SqrtLog_LeafParametersProgramNative`, `SubexponentialSAT_SqrtLog_RingScanAdd`, `SubexponentialSAT_SqrtLog_RingScanAddLoop`, `SubexponentialSAT_SqrtLog_RingScanService`, `SubexponentialSAT_SqrtLog_RingTripleBasic`, `SubexponentialSAT_SqrtLog_RingTripleMatrix`, `SubexponentialSAT_SqrtLog_RingTripleRowStep`, `SubexponentialSAT_SqrtLog_RingTripleRows`, `SubexponentialSAT_SubexpBlockParameterProgram`, `SubexponentialSAT_Subexp_BasisTransposePlanProgram`, `SubexponentialSAT_UnaryForPrograms`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S066`, `OAIQ081S067` and `OAIQ081S068` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S100`, `OAIQ081S101`, `OAIQ081S102`, `OAIQ081S103`, `OAIQ081S104`, `OAIQ081S106`, `OAIQ081S108`, `OAIQ081S109`, `OAIQ081S110`, `OAIQ081S114` and `OAIQ081S115`; the statement `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Interval.at_eval`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafExecution.call_export_execution`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeTerminal.power_bounded`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram.rowCommand_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgram.Loop.frameRecord_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgram.Loop.frameWeight_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgram.Loop.lookup_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadScatterProgram.program_runsIn`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.MassPreserve.command_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Prepare.cutoff_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.ReadScalar.emit_eval` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.prepareProgram_factored_runsIn`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S066
import Definitions.Def_OAIQ081S067
import Definitions.Def_OAIQ081S068

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ProgramStateFrames
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Reusable data projection and framing for genuine finite subroutine calls.
The projection/embedding functions specify states; executable code uses only
the fixed instruction-port relocation already proved by ProgramLinking. -/

namespace SubexponentialSAT.StructuredCalls

open SubexponentialSAT.BitProgram

/-- A complete local run can be called directly from an arbitrary caller state. -/
theorem eval_call_from_state {r s l R S : ℕ} (p : Program r s l)
    (register : Fin r → Fin R) (stack : Fin s → Fin S) (d : State R S)
    (hr : Function.Injective register) (hs : Function.Injective stack)
    {n : ℕ} {b : State r s}
    (h : Trace p n ((projectState register stack d).withPC (some p.entry)) (b.withPC none)) :
    Eval (.call (ProgramLinking.liftProgram p register stack)) n
      d (embedState register stack d b) := by
  simpa only [embedState_project register stack d hr hs] using
    eval_call_lifted p register stack d hr hs h

end SubexponentialSAT.StructuredCalls

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_UnaryForPrograms
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed-control unary-counted callbacks

The counter is a Boolean stack whose length is the iteration count. Its bits
are ignored. The controller pops before each callback and tests the presence
flag; callbacks preserve the remaining counter tail and may clobber all
registers. Every observation contains an actual callback evaluation.
-/

namespace SubexponentialSAT.UnaryForPrograms

open BitProgram StructuredProgram
open CounterForPrograms (budgetSum)

variable {R S : ℕ}

abbrev popCmd (p : Ports R S) : StructuredCalls.Cmd R S :=
  .base (.atom (.pop p.counter p.bit p.flag))

end SubexponentialSAT.UnaryForPrograms

end OAI.Algorithms
end

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

namespace HeadSelect
open OAI.Algorithms.SubexponentialSAT.StackRoutines

abbrev Data := State 4 5

end HeadSelect

open OAI.Algorithms.SubexponentialSAT.StackRoutines


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter
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

def state (r : Regs) (w : Words) : Data :=
  ⟨r, fun i => if h : i.val < 15 then w ⟨i.val, h⟩ else []⟩

@[simp] theorem state_regs (r : Regs) (w : Words) : (state r w).regs = r := rfl

@[simp] theorem state_port (r : Regs) (w : Words) (i : Fin 15) :
    (state r w).stacks (port i) = w i := by simp [state, port]

end SubexponentialSAT.SubexpBlockParameterProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParametersProgramBank
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Bank

open BitProgram StructuredCalls BinaryArithmetic

abbrev Data := StructuredProgram.State 8 77

def state (r : Regs) (w : Words) : Data :=
  ⟨r, fun i => if h : i.val < 64 then w ⟨i.val, h⟩ else []⟩

@[simp] theorem state_port (r : Regs) (w : Words) (i : Fin 64) :
    (state r w).stacks (port i) = w i := by simp [state, port]


end SubexponentialSAT.SqrtLog.LeafParametersProgram.Bank

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

abbrev copyCmd (a o : Fin 64) : Cmd 8 77 :=
  ArithmeticCalls.copyAt (port a) (port o) (work 1 (by decide) 0)

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Bank


/- Component: SubexponentialSAT.SqrtLog.LeafParametersProgramDispatch -/

/-! A fixed ten-comparison bit guard. All operands are runtime binary words.
This module states their data relation separately from parameter production. -/

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Circuit

open BitProgram StructuredCalls BinaryArithmetic Bank

def Ready (w : Words) : Instr → Prop
  | .clear _ => True
  | .load o _ | .copy _ o _ | .add _ _ o _ _ | .mul _ _ o _ _
  | .pow _ _ o _ _ | .sqrt _ o _ => w o=[]
  | .quot _ b o _ _ => w o=[] ∧ 0 < BinaryArithmetic.toNat (w b)
  | .logSucc _ | .addConst _ _ | .pred _ | .maxTwo _ => True

def values (w : Words) (a : Fin 64) := BinaryArithmetic.toNat (w a)
def lengths (w : Words) (a : Fin 64) := (w a).length

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Circuit


/- Component: SubexponentialSAT.SqrtLog.LeafParametersProgramCircuitRun -/

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Execute

open BitProgram StructuredCalls BinaryArithmetic Bank Circuit

abbrev Data := StructuredProgram.State 9 77

def state (r : Fin 9 → Bool) (w : Words) : Data :=
  ⟨r,(Bank.state (fun _ => false) w).stacks⟩

@[simp] theorem state_port (r : Fin 9 → Bool) (w : Words) (a : Fin 64) :
    (state r w).stacks (Bank.port a)=w a :=
  Bank.state_port (fun _ => false) w a

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Execute


/- Component: SubexponentialSAT.SqrtLog.LeafParametersProgramCircuitBudget -/


end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeParametersProgramUnary
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Production sparse-code parameter program. Fixed arithmetic, minimum,
metadata identities and unary materialization are checked in one unit. -/

/-! Arithmetic identities used by the physical sparse-code parameter program. -/


/-! A concrete minimum operation used between two straight-line arithmetic
stages. The comparison consumes only two explicitly copied temporary words. -/
namespace SubexponentialSAT.SqrtLog.CodeParametersProgram

open BitProgram StructuredCalls BinaryArithmetic LeafParametersProgram.Bank

def minComparePorts : Fin 2 → Fin 77 := ![port 62,port 63]

end SubexponentialSAT.SqrtLog.CodeParametersProgram


/-! Fixed finite arithmetic instructions for all sparse-code search metadata.
Ports 0 and 1 contain m and B. Outputs: q=5, D=9, t=11, tD=12,
local distance=15, r=18, rD=19, N=21. Unary conversion is a separate,
explicitly paid stage. -/


/-! Explicit paid binary-to-unary copies for code-search metadata. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingScanAdd
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native scalar addition inside a flat, runtime-sized coefficient scan. -/
namespace SubexponentialSAT.SqrtLog.RingScan

open BitProgram StructuredCalls StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

theorem scalarAdd_eval (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (regs : Fin 8 → Bool) (x y : Word (baseWidth p t))
    (xs ys out count width : List Bool) :
    ∃ n ≤ 6000 * (baseWidth p t + 1)^2, ∃ finalRegs,
      Eval scalarAdd n
        (addState regs M.bits x.val y.val xs ys out count width)
        (addState finalRegs M.bits (SubexpPreparedQuartic.wordAdd p t M x y).1.val []
          xs ys out count width) := by
  obtain ⟨rf, n, hn, ht⟩ := SubexpScalarMachine.wordAdd_run p t M regs x y
  have he := eval_call_lifted ModularRingPrograms.wordAddProgram id scalarStacks
    (addState regs M.bits x.val y.val xs ys out count width)
    Function.injective_id scalarStacks_injective
    (a := ⟨regs, ModularRingPrograms.extendSeven
      (ModularRingPrograms.scalarInput x.val y.val M.bits) []⟩)
    (b := ⟨rf, ModularRingPrograms.extendSeven
      (ModularRingPrograms.scalarInput (SubexpPreparedQuartic.wordAdd p t M x y).1.val [] M.bits) []⟩) ht
  refine ⟨n, hn, rf, ?_⟩
  simpa only [embed_scalar] using he

/-- One real coefficient step, including both dynamic-width loads and output
movement. All input suffixes and unary controls are preserved exactly. -/
theorem addStep_eval (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (regs : Fin 8 → Bool) (x y : Word (baseWidth p t))
    (xs ys out count width : List Bool) (hwidth : width.length = baseWidth p t) :
    ∃ n ≤ 6000 * (baseWidth p t + 1)^2 + 31 * baseWidth p t + 27,
      ∃ finalRegs, Eval addStep n
        (addState regs M.bits [] [] (x.val ++ xs) (y.val ++ ys) out count width)
        (addState finalRegs M.bits [] [] xs ys
          ((SubexpPreparedQuartic.wordAdd p t M x y).1.val.reverse ++ out) count width) := by
  have hx := loadX_eval regs M.bits x.val xs [] (y.val ++ ys) out count width
    (hwidth.trans x.property.symm)
  have hy := loadY_eval (readRegs regs 1 3 none) M.bits x.val y.val ys xs out count width
    (hwidth.trans y.property.symm)
  obtain ⟨n, hn, rf, ha⟩ := scalarAdd_eval p t M (readRegs regs 1 3 none) x y xs ys out count width
  have he := emitReverse_eval rf M.bits (SubexpPreparedQuartic.wordAdd p t M x y).1.val
    xs ys out count width
  have hy' := hy
  simp only [readRegs_reset] at hy'
  have total := hx.seq (hy'.seq (ha.seq he))
  refine ⟨_, ?_, readRegs rf 1 3 none, total⟩
  simp only [x.property, y.property, (SubexpPreparedQuartic.wordAdd p t M x y).1.property]
  omega

end SubexponentialSAT.SqrtLog.RingScan

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingScanAddLoop
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The vector length is a unary input, never a generated list of instructions. -/
namespace SubexponentialSAT.SqrtLog.RingScan

open BitProgram StructuredCalls StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

theorem loop_eval (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (pairs : List (Word (baseWidth p t) × Word (baseWidth p t)))
    (regs : Fin 8 → Bool) (out count width : List Bool)
    (hcount : count.length = pairs.length) (hwidth : width.length = baseWidth p t) :
    ∃ n ≤ pairs.length * (6000 * (baseWidth p t + 1)^2 + 31 * baseWidth p t + 29) + 1,
      ∃ finalRegs, Eval addLoop n
        (addState (readRegs regs 1 3 count.head?) M.bits [] []
          (leftBits pairs) (rightBits pairs) out count.tail width)
        (addState finalRegs M.bits [] [] [] [] ((sumBits p t M pairs).reverse ++ out) [] width) := by
  induction pairs generalizing regs out count with
  | nil =>
      have hc : count = [] := List.length_eq_zero_iff.mp (by simpa using hcount)
      subst count
      refine ⟨1, by simp, readRegs regs 1 3 none, ?_⟩
      apply Eval.while_false
      simp [addState, readRegs_present]
  | cons pair pairs ih =>
      cases count with
      | nil => simp at hcount
      | cons bit count =>
          have hc : count.length = pairs.length := by simpa using hcount
          obtain ⟨n, hn, rf, hs⟩ := addStep_eval p t M (readRegs regs 1 3 (some bit))
            pair.1 pair.2 (leftBits pairs) (rightBits pairs) out count width hwidth
          have hp := popCount_eval rf M.bits [] [] (leftBits pairs) (rightBits pairs)
            ((SubexpPreparedQuartic.wordAdd p t M pair.1 pair.2).1.val.reverse ++ out) count width
          obtain ⟨m, hm, rg, hl⟩ := ih rf
            ((SubexpPreparedQuartic.wordAdd p t M pair.1 pair.2).1.val.reverse ++ out)
            count hc
          have he := Eval.while_true
            (show (addState (readRegs regs 1 3 (some bit)) M.bits [] []
              (leftBits (pair :: pairs)) (rightBits (pair :: pairs)) out count width).regs 3 = true by
                simp [addState, readRegs_present])
            (hs.seq hp) hl
          refine ⟨n + 1 + m + 1, ?_, rg, ?_⟩
          · simp only [List.length_cons]
            nlinarith
          · simpa only [addLoop, leftBits, rightBits, sumBits, List.head?_cons, List.tail_cons,
              List.reverse_append, List.append_assoc] using he

/-- Full vector addition scan. The input counter has one arbitrary bit per
coefficient. Both flat vector suffixes are currently empty; the lower-level
step already permits arbitrary suffixes for embedding in record interpreters. -/
theorem addScan_eval (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (pairs : List (Word (baseWidth p t) × Word (baseWidth p t)))
    (regs : Fin 8 → Bool) (out count width : List Bool)
    (hcount : count.length = pairs.length) (hwidth : width.length = baseWidth p t) :
    ∃ n ≤ pairs.length * (6000 * (baseWidth p t + 1)^2 + 31 * baseWidth p t + 29) + 2,
      ∃ finalRegs, Eval addScan n
        (addState regs M.bits [] [] (leftBits pairs) (rightBits pairs) out count width)
        (addState finalRegs M.bits [] [] [] [] ((sumBits p t M pairs).reverse ++ out) [] width) := by
  have hp := popCount_eval regs M.bits [] [] (leftBits pairs) (rightBits pairs) out count width
  obtain ⟨n, hn, rf, hl⟩ := loop_eval p t M pairs regs out count width hcount hwidth
  exact ⟨1+n, by omega, rf, hp.seq hl⟩


/-- A complete native flat-vector addition, with forward-order output on
stack zero and empty input/counter/scratch stacks. The width and modulus remain. -/
theorem addVector_eval (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (pairs : List (Word (baseWidth p t) × Word (baseWidth p t)))
    (regs : Fin 8 → Bool) (count width : List Bool)
    (hcount : count.length = pairs.length) (hwidth : width.length = baseWidth p t) :
    ∃ n ≤ pairs.length * (6000 * (baseWidth p t + 1)^2 + 34 * baseWidth p t + 29) + 5,
      ∃ finalRegs, Eval addVector n
        (addState regs M.bits [] [] (leftBits pairs) (rightBits pairs) [] count width)
        (addState finalRegs M.bits (sumBits p t M pairs) [] [] [] [] [] width) := by
  obtain ⟨n, hn, rf, hs⟩ := addScan_eval p t M pairs regs [] count width hcount hwidth
  simp only [List.append_nil] at hs
  have hf := finishAdd_eval rf M.bits (sumBits p t M pairs).reverse width
  simp only [List.reverse_reverse, List.length_reverse, sumBits_length] at hf
  refine ⟨_, ?_, readRegs rf 1 3 none, hs.seq hf⟩
  nlinarith

theorem addVectorProgram_run (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (pairs : List (Word (baseWidth p t) × Word (baseWidth p t)))
    (regs : Fin 8 → Bool) (count width : List Bool)
    (hcount : count.length = pairs.length) (hwidth : width.length = baseWidth p t) :
    ∃ finalRegs, RunsIn addVectorProgram
      (pairs.length * (6000 * (baseWidth p t + 1)^2 + 34 * baseWidth p t + 29) + 6)
      ((addState regs M.bits [] [] (leftBits pairs) (rightBits pairs) [] count width).withPC
        (some addVectorProgram.entry))
      ((addState finalRegs M.bits (sumBits p t M pairs) [] [] [] [] [] width).withPC none) := by
  obtain ⟨n, hn, rf, he⟩ := addVector_eval p t M pairs regs count width hcount hwidth
  exact ⟨rf, n + 1, by omega, compiled_halt_trace he 8 0⟩

end SubexponentialSAT.SqrtLog.RingScan

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingTripleBasic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed-port primitives for dynamic Cartesian triple expansion. All loop
bounds and coefficient widths are words on stacks, not generated code. -/
namespace SubexponentialSAT.SqrtLog.RingTriple

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpQuarticRing

theorem emitTriple_eval (B : ℕ) (s : Store) (regs : Fin 2 → Bool)
    (y c yt ct : List Bool) (hx : s.held.length = B)
    (hy : y.length = B) (hc : c.length = B) (hw : s.width.length = B) :
    ∃ regs', Eval emitTriple (44 * B + 38)
      (state regs {s with ys := y ++ yt, table := c ++ ct})
      (state regs' {s with ys := yt, table := ct, out := (s.held ++ y ++ c).reverse ++ s.out}) := by
  let d := state regs {s with ys := y ++ yt, table := c ++ ct}
  let a := afterCopy d 6 8
  let b := afterTransfer a 8 3
  let e := afterLoad b 0 y yt
  let f := afterTransfer e 7 3
  let g := afterLoad f 1 c ct
  have h1 := copy_eval d 6 8 (by decide) (by decide) (by decide) (by rfl)
  have h2 := transfer_eval a 8 3 (by decide)
  have h3 := load_eval b 0 y yt (by rfl) (by rfl) (by rfl) (by simpa [b, a, d,
    afterTransfer, afterCopy, transferStacks, copyStacks, state, tapes] using (hw.trans hy.symm))
  have h4 := transfer_eval e 7 3 (by decide)
  have h5 := load_eval f 1 c ct (by rfl) (by rfl) (by rfl) (by simpa [f, e, b, a, d,
    afterTransfer, afterLoad, afterCopy, transferStacks, copyStacks, loadPorts, state, tapes]
    using (hw.trans hc.symm))
  have h6 := transfer_eval g 8 3 (by decide)
  have heq : afterTransfer g 8 3 =
      state (afterTransfer g 8 3).regs {s with ys := yt, table := ct, out := (s.held ++ y ++ c).reverse ++ s.out} := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      fin_cases i <;> simp [g, f, e, b, a, d, afterTransfer, afterLoad, afterCopy,
        transferStacks, copyStacks, loadPorts, state, tapes, List.reverse_append, List.append_assoc]
  refine ⟨(afterTransfer g 8 3).regs, ?_⟩
  rw [← heq]
  convert h1.seq (h2.seq (h3.seq (h4.seq (h5.seq h6)))) using 1
  all_goals try with_reducible_and_instances rfl
  simp [g, f, e, b, a, d, afterTransfer, afterLoad, afterCopy,
    transferStacks, copyStacks, loadPorts, state, tapes, hx, hy, hc]
  omega

end SubexponentialSAT.SqrtLog.RingTriple

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingTripleRows
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingTriple

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpQuarticRing

theorem jLoop_eval (B : ℕ) (s : Store) (pairs : List (Word B × Word B))
    (tail count : List Bool) (regs : Fin 2 → Bool)
    (hc : count.length = pairs.length) (hx : s.held.length = B) (hw : s.width.length = B) :
    ∃ n ≤ pairs.length * (44 * B + 40) + 1, ∃ regs',
      Eval jLoop n
        (state (readRegs regs 0 1 count.head?) {s with ys := leftBits pairs, table := rightBits pairs ++ tail, jc := count.tail})
        (state regs' {s with ys := [], table := tail, out := (rowBits s.held pairs).reverse ++ s.out, jc := []}) := by
  induction pairs generalizing s count regs with
  | nil =>
    have hcount : count = [] := List.length_eq_zero_iff.mp (by simpa using hc)
    subst count
    refine ⟨1, by simp, readRegs regs 0 1 none, ?_⟩
    simpa [leftBits, rightBits, rowBits] using
      (Eval.while_false (test := (1 : Fin 2)) (body := .seq emitTriple popJ)
        (a := state (readRegs regs 0 1 none)
          {s with ys := [], table := tail, jc := []}) (by simp [state, readRegs_present]))
  | cons p pairs ih =>
    cases count with
    | nil => simp at hc
    | cons bit count =>
      have hc' : count.length = pairs.length := by simpa using hc
      obtain ⟨r₁, hemit⟩ := emitTriple_eval B {s with jc := count}
        (readRegs regs 0 1 (some bit)) p.1.val p.2.val (leftBits pairs)
        (rightBits pairs ++ tail) hx p.1.property p.2.property hw
      let m := {s with ys := leftBits pairs, table := rightBits pairs ++ tail, out := (s.held ++ p.1.val ++ p.2.val).reverse ++ s.out, jc := count}
      have hp := popJ_eval r₁ m
      obtain ⟨n, hn, r₂, hloop⟩ := ih m count r₁ hc' hx hw
      have hbody : Eval (.seq emitTriple popJ) (44 * B + 38 + 1)
          (state (readRegs regs 0 1 (some bit))
            {s with ys := leftBits (p :: pairs), table := rightBits (p :: pairs) ++ tail, jc := count})
          (state (readRegs r₁ 0 1 count.head?) {m with jc := count.tail}) := by
        simpa [m, leftBits, rightBits, List.append_assoc] using hemit.seq hp
      refine ⟨(44 * B + 38) + 1 + n + 1, ?_, r₂, ?_⟩
      · simp only [List.length_cons]; nlinarith
      · have he := Eval.while_true
          (test := (1 : Fin 2))
          (show (state (readRegs regs 0 1 (some bit))
            {s with ys := leftBits (p :: pairs), table := rightBits (p :: pairs) ++ tail, jc := count}).regs 1 = true by simp [state, readRegs_present])
          hbody hloop
        simpa [jLoop, m, leftBits, rightBits, rowBits,
          List.reverse_append, List.append_assoc] using he

theorem jScan_eval (B : ℕ) (s : Store) (pairs : List (Word B × Word B))
    (tail count : List Bool) (regs : Fin 2 → Bool)
    (hc : count.length = pairs.length) (hx : s.held.length = B) (hw : s.width.length = B) :
    ∃ n ≤ pairs.length * (44 * B + 40) + 2, ∃ regs',
      Eval jScan n
        (state regs {s with ys := leftBits pairs, table := rightBits pairs ++ tail, jc := count})
        (state regs' {s with ys := [], table := tail, out := (rowBits s.held pairs).reverse ++ s.out, jc := []}) := by
  have hp := popJ_eval regs {s with ys := leftBits pairs, table := rightBits pairs ++ tail, jc := count}
  obtain ⟨n, hn, regs', ht⟩ := jLoop_eval B s pairs tail count regs hc hx hw
  exact ⟨1 + n, by omega, regs', hp.seq ht⟩

end SubexponentialSAT.SqrtLog.RingTriple

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingTripleRowStep
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingTriple

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpQuarticRing

theorem startRow_eval (B : ℕ) (s : Store) (regs : Fin 2 → Bool)
    (x xt : List Bool) (hx : x.length = B) (hw : s.width.length = B) :
    ∃ regs', Eval startRow (14 * B + 7 * s.y.length + 7 * s.degree.length + 22)
      (state regs {s with xs := x ++ xt, held := [], ys := [], jc := []})
      (state regs' {s with xs := xt, held := x, ys := s.y, jc := s.degree}) := by
  let d := state regs {s with xs := x ++ xt, held := [], ys := [], jc := []}
  let a := afterLoad d 2 x xt
  let b := afterCopy a 1 5
  have h1 := load_eval d 2 x xt (by rfl) (by rfl) (by rfl)
    (by simpa [d, state, tapes] using (hw.trans hx.symm))
  have h2 := copy_eval a 1 5 (by decide) (by decide) (by decide) (by rfl)
  have h3 := copy_eval b 9 12 (by decide) (by decide) (by decide) (by rfl)
  have hf : afterCopy b 9 12 =
      state (afterCopy b 9 12).regs {s with xs := xt, held := x, ys := s.y, jc := s.degree} := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      fin_cases i <;> simp [b, a, d, afterCopy, afterLoad, copyStacks, loadPorts, state, tapes]
  refine ⟨(afterCopy b 9 12).regs, ?_⟩
  rw [← hf]
  convert h1.seq (h2.seq h3) using 1
  all_goals try with_reducible_and_instances rfl
  simp [b, a, d, afterCopy, afterLoad, copyStacks, loadPorts, state, tapes, hx]
  omega

theorem rowStep_eval (B : ℕ) (s : Store) (regs : Fin 2 → Bool)
    (x : Word B) (pairs : List (Word B × Word B)) (xt ct : List Bool)
    (hy : leftBits pairs = s.y) (hd : s.degree.length = pairs.length)
    (hw : s.width.length = B) :
    ∃ n ≤ 100 * (s.degree.length + 1) * (B + 1), ∃ regs',
      Eval rowStep n
        (state regs {s with xs := x.val ++ xt, table := rightBits pairs ++ ct, held := [], ys := [], jc := []})
        (state regs' {s with xs := xt, table := ct, held := [], ys := [], jc := [], out := (rowBits x.val pairs).reverse ++ s.out}) := by
  obtain ⟨r₁, hstart⟩ := startRow_eval B {s with table := rightBits pairs ++ ct}
    regs x.val xt x.property hw
  let a := {s with xs := xt, held := x.val}
  obtain ⟨n, hn, r₂, hscan⟩ := jScan_eval B a pairs ct s.degree r₁ hd x.property hw
  have hscan' : Eval jScan n
      (state r₁ {s with table := rightBits pairs ++ ct, xs := xt, held := x.val, ys := s.y, jc := s.degree})
      (state r₂ {s with xs := xt, table := ct, held := x.val, ys := [], jc := [], out := (rowBits x.val pairs).reverse ++ s.out}) := by
    simpa [a, hy] using hscan
  have hclear := clearHeld_eval
    {s with xs := xt, table := ct, held := x.val, ys := [], jc := [], out := (rowBits x.val pairs).reverse ++ s.out} r₂
  refine ⟨(14 * B + 7 * s.y.length + 7 * s.degree.length + 22) + (n + (2 * B + 3)),
    ?_, readRegs r₂ 0 1 none, ?_⟩
  · have hyl : s.y.length = pairs.length * B := by rw [← hy, leftBits_length]
    rw [← hd] at hyl hn
    nlinarith
  · simpa only [x.property] using hstart.seq (hscan'.seq hclear)

end SubexponentialSAT.SqrtLog.RingTriple

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingTripleMatrix
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingTriple

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpQuarticRing

theorem iLoop_eval (B : ℕ) (s : Store) (rows : List (Row B))
    (tail count : List Bool) (regs : Fin 2 → Bool)
    (hc : count.length = rows.length) (hfit : RowsFit s rows) (hw : s.width.length = B) :
    ∃ n ≤ rows.length * (100 * (s.degree.length + 1) * (B + 1) + 2) + 1, ∃ regs',
      Eval iLoop n
        (state (readRegs regs 0 1 count.head?)
          {s with xs := xBits rows, ys := [], held := [], table := tableBits rows ++ tail, ic := count.tail, jc := []})
        (state regs' {s with xs := [], ys := [], held := [], table := tail, ic := [], jc := [], out := (matrixBits rows).reverse ++ s.out}) := by
  induction rows generalizing s count regs with
  | nil =>
    have hcount : count = [] := List.length_eq_zero_iff.mp (by simpa using hc)
    subst count
    refine ⟨1, by simp, readRegs regs 0 1 none, ?_⟩
    simpa [xBits, tableBits, matrixBits] using
      (Eval.while_false (test := (1 : Fin 2)) (body := .seq rowStep popI)
        (a := state (readRegs regs 0 1 none)
          {s with xs := [], ys := [], held := [], table := tail, ic := [], jc := []})
        (by simp [state, readRegs_present]))
  | cons r rows ih =>
    cases count with
    | nil => simp at hc
    | cons bit count =>
      have hc' : count.length = rows.length := by simpa using hc
      have hrow := hfit r (by simp)
      obtain ⟨u, hu, r₁, hrowstep⟩ := rowStep_eval B {s with ic := count}
        (readRegs regs 0 1 (some bit)) r.1 r.2 (xBits rows) (tableBits rows ++ tail)
        hrow.1 hrow.2 hw
      let m := {s with xs := xBits rows, ys := [], held := [], table := tableBits rows ++ tail, ic := count, jc := [], out := (rowBits r.1.val r.2).reverse ++ s.out}
      have hp := popI_eval r₁ m
      have hfit' : RowsFit m rows := by
        intro a ha
        exact hfit a (by simp [ha])
      obtain ⟨n, hn, r₂, hloop⟩ := ih m count r₁ hc' hfit' hw
      have hbody : Eval (.seq rowStep popI) (u + 1)
          (state (readRegs regs 0 1 (some bit))
            {s with xs := xBits (r :: rows), ys := [], held := [], table := tableBits (r :: rows) ++ tail, ic := count, jc := []})
          (state (readRegs r₁ 0 1 count.head?) {m with ic := count.tail}) := by
        simpa [m, xBits, tableBits, List.append_assoc] using hrowstep.seq hp
      refine ⟨u + 1 + n + 1, ?_, r₂, ?_⟩
      · change n ≤ rows.length * (100 * (s.degree.length + 1) * (B + 1) + 2) + 1 at hn
        change u ≤ 100 * (s.degree.length + 1) * (B + 1) at hu
        simp only [List.length_cons]
        nlinarith
      · have he := Eval.while_true (test := (1 : Fin 2))
          (show (state (readRegs regs 0 1 (some bit))
            {s with xs := xBits (r :: rows), ys := [], held := [], table := tableBits (r :: rows) ++ tail, ic := count, jc := []}).regs 1 = true by
              simp [state, readRegs_present]) hbody hloop
        simpa [iLoop, m, matrixBits, List.reverse_append, List.append_assoc] using he

end SubexponentialSAT.SqrtLog.RingTriple

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingScanService
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! One fixed native service for arbitrary-degree coefficient-ring products. -/
namespace SubexponentialSAT.SqrtLog.RingScan
open BitProgram StructuredCalls StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

theorem serviceFinish_eval (regs : Fin 8 → Bool) (s : ServiceStore) :
    Eval serviceFinish (2*s.inner.length+3)
      (serviceWorkState regs s)
      (serviceWorkState (readRegs regs 1 3 none) {s with inner := []}) := by
  have he := serviceClear_eval (serviceWorkState regs s) 16
  convert he using 1
  · simp [serviceWorkState, serviceTapes]
  · apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i; fin_cases i <;> simp [ serviceWorkState, serviceTapes, clearStacks]

end SubexponentialSAT.SqrtLog.RingScan

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

abbrev Data := State 3 7

end SubexponentialSAT.Subexp.BasisTransposePlanProgram

end OAI.Algorithms
end


