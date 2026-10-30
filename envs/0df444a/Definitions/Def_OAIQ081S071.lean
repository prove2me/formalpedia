-- Prove2me | Definitions.Def_OAIQ081S071
-- name    : OAIQ081S071
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T21:54:20.06484+00:00
-- url     : https://prove2.me/theorems/66baea50-7720-4c68-ad31-a383740fa546
-- title:
--   Definitions bundle OAIQ081S071 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 64 declarations of OpenAI's Lean: 38 definitions and 26 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchBootstrap.pushWord`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchCandidateControl.callback`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchCandidateControl.checkCandidate`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchCandidateControl.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchCandidateControl.program`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchFactorControl.callback`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchFactorControl.checkPair`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchFactorControl.savedAll`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchFactorControl.savedProgram`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchProgram.coefficientCall`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchProgram.coefficientCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchProgram.coefficientProgram`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchProgram.dotBody`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchProgram.dotCall`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchProgram.dotCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchProgram.dotLoop`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchProgram.dotProgram`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchProgram.dotScalar`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchProgram.multiplyAddBits`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchProgram.pairCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchProgram.pairProductCall`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchProgram.pairProductCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchProgram.pairProgram`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchProgram.productBody`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchProgram.productCheckCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchProgram.productCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchProgram.productLoop`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchProgram.productProgram`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutBlocks.data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutDenominatorProgram.budget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutDenominatorProgramQuery.budget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.state`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram.Selector.scanVolume`, `OAI.Algorithms.SubexponentialSAT.Subexp.PackingVertexLabels.Data`, `OAI.Algorithms.SubexponentialSAT.Subexp.PackingVertexLabels.planBytes`, `OAI.Algorithms.SubexponentialSAT.SubexpNormalizeProgram.filterState`, `OAI.Algorithms.SubexponentialSAT.SubexpPostfixControl.cfg4`, `OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage.clearManyCost`.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparsePriorityProgram`, `SubexponentialSAT_SqrtLog_IrreducibleSearch`, `SubexponentialSAT_SqrtLog_IrreducibleSearchBasic`, `SubexponentialSAT_SqrtLog_IrreducibleSearchBootstrapPrimitives`, `SubexponentialSAT_SqrtLog_IrreducibleSearchControl`, `SubexponentialSAT_SqrtLog_IrreducibleSearchFactorEnumeration`, `SubexponentialSAT_SqrtLog_IrreducibleSearchNativeScan`, `SubexponentialSAT_SqrtLog_IrreducibleSearchProgram`, `SubexponentialSAT_SqrtLog_IrreducibleSearchProgramDot`, `SubexponentialSAT_SqrtLog_IrreducibleSearchProgramDotRun`, `SubexponentialSAT_SqrtLog_IrreducibleSearchProgramLift`, `SubexponentialSAT_SqrtLog_IrreducibleSearchProgramScalar`, `SubexponentialSAT_SqrtLog_IrreducibleSearchProgramStorage`, `SubexponentialSAT_SqrtLog_LayoutBlocks`, `SubexponentialSAT_SqrtLog_LayoutDenominatorProgramModel`, `SubexponentialSAT_SqrtLog_LayoutDenominatorProgramQueryCode`, `SubexponentialSAT_SqrtLog_LayoutProgramScalar`, `SubexponentialSAT_SqrtLog_ProgramTapeReplayMacros`, `SubexponentialSAT_StructuredProgram`, `SubexponentialSAT_SubexpNormalizeProgram`, `SubexponentialSAT_SubexpPostfixControl`, `SubexponentialSAT_SubexpSetupFrames`, `SubexponentialSAT_SubexpSetupStorage`, `SubexponentialSAT_Subexp_BlockSearchPreparation`, `SubexponentialSAT_Subexp_BlockSearchProgram`, `SubexponentialSAT_Subexp_PackingVertexLabels`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S045`, `OAIQ081S046`, `OAIQ081S047`, `OAIQ081S050`, `OAIQ081S051`, `OAIQ081S053` and `OAIQ081S054` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S087`, `OAIQ081S088`, `OAIQ081S089`, `OAIQ081S091`, `OAIQ081S092`, `OAIQ081S093`, `OAIQ081S095`, `OAIQ081S096`, `OAIQ081S097`, `OAIQ081S098` and `OAIQ081S099`; the statements `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.accumulate_eval_total`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.multiply_eval_total`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.scalarProgram_runsIn_total` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutRank.blocks_data_total_rank_le`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgram.Loop.frameRecord_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgram.Loop.frameWeight_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.Marked.fetch_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.accumulate_eval_total`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.multiply_eval_total`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.scalarProgram_runsIn_total`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutRank.blocks_data_total_rank_le`, `OAI.Algorithms.SubexponentialSAT.SubexpDenseLiteralPadding.program_runsIn` and `OAI.Algorithms.SubexponentialSAT.SubexpRowPostfixServices.program_runsIn`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S045
import Definitions.Def_OAIQ081S046
import Definitions.Def_OAIQ081S047
import Definitions.Def_OAIQ081S050
import Definitions.Def_OAIQ081S051
import Definitions.Def_OAIQ081S053
import Definitions.Def_OAIQ081S054

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_StructuredProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Structured programs compiled to finite bit instruction tables

The syntax has no unbounded natural-number registers or semantic-function
instructions. All data operations are the concrete Boolean-register and stack
instructions of BitProgram. Loops inspect a Boolean register, and changing data
never changes the finite generated instruction table.
-/

namespace SubexponentialSAT.StructuredProgram

open SubexponentialSAT.BitProgram

/-- Whole-program correctness: n structured steps become n actual bit-program
steps to the exit address, with no unresolved compiler-certificate premise. -/
theorem compiled_trace {r s : ℕ} {c : Cmd r s} {n : ℕ} {a b : State r s}
    (h : Eval c n a b) (inputStack outputStack : Fin s) :
    Trace (compiled c inputStack outputStack) n
      (a.withPC (some (compiled c inputStack outputStack).entry))
      (b.withPC (some (exitAddress c))) :=
  eval_trace h _ _ _ (compiled_site c inputStack outputStack)

/-- Executing the generated final halt costs one additional instruction. -/
theorem compiled_halt_trace {r s : ℕ} {c : Cmd r s} {n : ℕ} {a b : State r s}
    (h : Eval c n a b) (inputStack outputStack : Fin s) :
    Trace (compiled c inputStack outputStack) (n + 1)
      (a.withPC (some (compiled c inputStack outputStack).entry)) (b.withPC none) := by
  apply (compiled_trace h inputStack outputStack).trans
  refine .cons ?_ (.refl _)
  rw [step]
  simp only [State.withPC, Option.map_some]
  rw [compiled_exit]
  rfl

end SubexponentialSAT.StructuredProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparsePriorityProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete components of the sharp clause/core search from Appendix A.
The guard counts actual framed literals and executes the preserving subset tester.
The complete search and its polynomial resource bound are developed separately below. -/


namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram

open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls

namespace Selector

def scanVolume (F : Formula) (mask width size threshold : List Bool) : ℕ :=
  2 * (Filter.formulaCode F).length + mask.length + width.length + size.length + threshold.length + 1

end Selector

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IrreducibleSearchBasic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Finite coefficient tests for arbitrary-degree irreducible search

Only vectors, finite lists, and scalar arithmetic are executed. `ofFn` and
the polynomial interpretation occur solely in the correctness proofs.
-/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearch

open Polynomial
open scoped BigOperators

theorem productEq_iff {d : ℕ} (c : Fin d → F) (a b : Fin (d + 1) → F) :
    productEq c a b = true ↔
      Polynomial.ofFn (d + 1) a * Polynomial.ofFn (d + 1) b = QuarticSearch.poly c := by
  simp only [productEq, List.all_eq_true, List.mem_range, decide_eq_true_eq,
    convolution_eq_coeff, candidateEntry_eq_coeff]
  constructor
  · intro h
    apply Polynomial.ext
    intro j
    by_cases hj : j < 2 * d + 1
    · exact h j hj
    · have ha : (Polynomial.ofFn (d + 1) a).natDegree ≤ d :=
        Nat.lt_succ_iff.mp (Polynomial.ofFn_natDegree_lt (Nat.succ_pos d) a)
      have hb : (Polynomial.ofFn (d + 1) b).natDegree ≤ d :=
        Nat.lt_succ_iff.mp (Polynomial.ofFn_natDegree_lt (Nat.succ_pos d) b)
      have hm : (Polynomial.ofFn (d + 1) a * Polynomial.ofFn (d + 1) b).natDegree ≤
          (Polynomial.ofFn (d + 1) a).natDegree + (Polynomial.ofFn (d + 1) b).natDegree :=
        Polynomial.natDegree_mul_le
      rw [coeff_eq_zero_of_natDegree_lt (by omega),
        coeff_eq_zero_of_natDegree_lt (by rw [QuarticSearch.poly_natDegree]; omega)]
  · intro h j _
    exact congrArg (fun p : F[X] => p.coeff j) h

end SubexponentialSAT.SqrtLog.IrreducibleSearch

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IrreducibleSearch
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Executable arbitrary-degree irreducible search over F₃

Search all monic degree-`d` coefficient vectors and reject each candidate
which is the product of two nonconstant arrays of degree at most `d`.
The test uses explicit convolution. Mathematical finite-field existence
proves that the executable search succeeds for every positive `d`.
-/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearch

open Polynomial

theorem pairPass_iff {d : ℕ} (c : Fin d → F) (a b : Fin (d + 1) → F) :
    pairPass c (a, b) = true ↔
      ¬(0 < (Polynomial.ofFn (d + 1) a).natDegree ∧
        0 < (Polynomial.ofFn (d + 1) b).natDegree ∧
        Polynomial.ofFn (d + 1) a * Polynomial.ofFn (d + 1) b = QuarticSearch.poly c) := by
  rw [← nonconstant_iff (Nat.succ_pos d), ← nonconstant_iff (Nat.succ_pos d),
    ← productEq_iff]
  unfold pairPass
  cases nonconstant a <;> cases nonconstant b <;> cases productEq c a b <;> decide

end SubexponentialSAT.SqrtLog.IrreducibleSearch

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_BlockSearchPreparation
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed preparation of candidate tables, split dimensions, and coefficient
tuples for the universal block search. All three dimensions are runtime data. -/

namespace SubexponentialSAT.Subexp.BlockSearchPreparation

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem embed_restrict_eq {r s R S : ℕ} (ρ : Fin r → Fin R) (σ : Fin s → Fin S)
    (a : State R S) (hρ : Function.Injective ρ) (hσ : Function.Injective σ) :
    embedState ρ σ a (restrictState ρ σ a) = a := by
  apply congrArg₂ StructuredProgram.State.mk
  · funext i
    by_cases h : ∃ j, ρ j = i
    · obtain ⟨j,rfl⟩ := h
      exact embedState_register ρ σ a (restrictState ρ σ a) hρ j
    · exact embedState_register_frame ρ σ a (restrictState ρ σ a) i h
  · funext i
    by_cases h : ∃ j, σ j = i
    · obtain ⟨j,rfl⟩ := h
      exact embedState_stack ρ σ a (restrictState ρ σ a) hσ j
    · exact embedState_stack_frame ρ σ a (restrictState ρ σ a) i h

theorem lifted_call {r s R S l : ℕ} (p : Program r s l)
    (ρ : Fin r → Fin R) (σ : Fin s → Fin S) (hρ : Function.Injective ρ)
    (hσ : Function.Injective σ) (a : State R S) (b : State r s) (bound : ℕ)
    (h : RunsIn p bound ((restrictState ρ σ a).withPC (some p.entry)) (b.withPC none)) :
    ∃ n, n ≤ bound ∧ Eval (.call (ProgramLinking.liftProgram p ρ σ)) n
      a (embedState ρ σ a b) := by
  obtain ⟨n,hn,ht⟩ := h
  refine ⟨n,hn,?_⟩
  have he := eval_call_lifted p ρ σ a hρ hσ ht
  simpa only [embed_restrict_eq ρ σ a hρ hσ] using he

end SubexponentialSAT.Subexp.BlockSearchPreparation

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpPostfixControl
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Concrete postfix instruction dispatch and literal push

The fixed prefix tags are push `0`, add `10`, and multiply `11`.
A push tag is followed by an `Encoding.frame` coefficient payload. End of
the code stack ends the instruction stream. The base dispatcher exposes
explicit service exits. The linked program implements literal push through
the actual frame parser and a Boolean-stack encoding loop; scalar arithmetic
remains at explicit service boundaries.

Registers: 0 last bit, 1 successful-pop flag, 2 binary-operation flag.
Stacks: 0 serialized code, 1 unary operand depth, 2 framed operand data.
The operand data stack is preserved throughout dispatch. On a successful
dispatch the depth stack has already been adjusted for the pending service.
The linked literal service uses stack 3 as initially empty scratch and returns
to dispatch with that scratch empty and the framed operand list updated.
-/

namespace SubexponentialSAT.SubexpPostfixControl

open BitProgram

/-! ## Serialization of the existing postfix instruction type -/

/-! ## Literal-push service with the framed-list operand ABI -/

abbrev cfg4 {l : ℕ} (pc : Option (Fin l)) (value present operation : Bool)
    (code depth operands scratch : List Bool) : Cfg 3 4 l :=
  ⟨pc, triple value present operation, quadruple code depth operands scratch⟩

theorem literalService_encode_cycle (b v p op : Bool) (code depth operands scratch : List Bool) :
    Trace literalService 5
      (cfg4 (some 9) v p op code depth operands (b :: scratch))
      (cfg4 (some 9) true true op code depth (true :: b :: operands) scratch) := by
  refine .cons (b := cfg4 (some 10) b true op code depth operands scratch) ?_ ?_
  · simp [step, execInstr, cfg4, triple, quadruple, readRegs]
  refine .cons (b := cfg4 (some 11) b true op code depth operands scratch) ?_ ?_
  · simp [step, execInstr, cfg4, triple, quadruple]
  refine .cons (b := cfg4 (some 12) b true op code depth (b :: operands) scratch) ?_ ?_
  · simp [step, execInstr, cfg4, triple, quadruple]
  refine .cons (b := cfg4 (some 13) true true op code depth (b :: operands) scratch) ?_ ?_
  · simp [step, execInstr, cfg4, triple, quadruple]
  refine .cons ?_ (.refl _)
  simp [step, execInstr, cfg4, triple, quadruple]

theorem literalService_encode_loop (scratch code depth operands : List Bool) (v p op : Bool) :
    Trace literalService (5 * scratch.length + 2)
      (cfg4 (some 9) v p op code depth operands scratch)
      (cfg4 (some 14) false false op code depth (escapeBits scratch.reverse ++ operands) []) := by
  induction scratch generalizing operands v p with
  | nil =>
      refine .cons (b := cfg4 (some 10) false false op code depth operands []) ?_ ?_
      · simp [step, execInstr, cfg4, triple, quadruple, readRegs]
      · refine .cons ?_ (.refl _)
        simp [step, execInstr, cfg4, triple, quadruple, escapeBits]
  | cons b bs ih =>
      have h := (literalService_encode_cycle b v p op code depth operands bs).trans
        (ih (true :: b :: operands) true true)
      have hn : 5 + (5 * bs.length + 2) = 5 * (b :: bs).length + 2 := by
        simp only [List.length_cons]
        omega
      simpa only [hn, List.reverse_cons, escapeBits_append, escapeBits,
        List.append_assoc, List.cons_append, List.nil_append] using h

theorem literalService_encode_trace (bits code depth operands : List Bool) (v p op : Bool) :
    Trace literalService (5 * bits.length + 7)
      (cfg4 (some 7) v p op code depth operands bits.reverse)
      (cfg4 none true false op code depth (true :: (Encoding.frame bits ++ operands)) []) := by
  have init : Trace literalService 2
      (cfg4 (some 7) v p op code depth operands bits.reverse)
      (cfg4 (some 9) false p op code depth (false :: operands) bits.reverse) := by
    refine .cons (b := cfg4 (some 8) false p op code depth operands bits.reverse) ?_ ?_
    · simp [step, execInstr, cfg4, triple, quadruple]
    · refine .cons ?_ (.refl _)
      simp [step, execInstr, cfg4, triple, quadruple]
  have loop := literalService_encode_loop bits.reverse code depth (false :: operands) false p op
  have finish : Trace literalService 3
      (cfg4 (some 14) false false op code depth (Encoding.frame bits ++ operands) [])
      (cfg4 none true false op code depth (true :: (Encoding.frame bits ++ operands)) []) := by
    refine .cons (b := cfg4 (some 15) true false op code depth (Encoding.frame bits ++ operands) []) ?_ ?_
    · simp [step, execInstr, cfg4, triple, quadruple]
    refine .cons (b := cfg4 (some 16) true false op code depth (true :: (Encoding.frame bits ++ operands)) []) ?_ ?_
    · simp [step, execInstr, cfg4, triple, quadruple]
    refine .cons ?_ (.refl _)
    simp [step, execInstr, cfg4, triple, quadruple]
  have loop' : Trace literalService (5 * bits.length + 2)
      (cfg4 (some 9) false p op code depth (false :: operands) bits.reverse)
      (cfg4 (some 14) false false op code depth (Encoding.frame bits ++ operands) []) := by
    simpa [List.length_reverse, List.reverse_reverse, frame_eq_escape,
      List.append_assoc] using loop
  have h := (init.trans loop').trans finish
  have hn : 2 + (5 * bits.length + 2) + 3 = 5 * bits.length + 7 := by omega
  simpa only [hn] using h

end SubexponentialSAT.SubexpPostfixControl

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpNormalizeProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Concrete syntax routines for CNF normalization

This module begins the machine implementation of normalization with the
complement-query operation used in tautology testing. `negateProgram` is one
fixed finite instruction table. It scans a unary literal code in pairs and
emits the code with its polarity flipped. Unbounded data stays on the stacks.

The theorems count actual `BitProgram.step` transitions. Full formula
deduplication, tautology filtering, and absorption are separate obligations;
this routine is not presented as the completed normalization algorithm.
-/

namespace SubexponentialSAT.SubexpNormalizeProgram

open BitProgram
open ParserProgram (cfg)

/-! ## Actual record-filter output step

The predicate's result occupies register 2. The following fixed callback
consumes the reversed record on stack 3, prepends its framed representation to
stack 2 exactly when selected, and resets the iterator's flags. Its two other
stacks are preserved. Computing the selection bit is a separate operation.
-/

def filterState (value present selected : Bool)
    (source work output payload : List Bool) : StructuredProgram.State 3 4 :=
  ⟨SubexpPostfixControl.triple value present selected,
    SubexpPostfixControl.quadruple source work output payload⟩

theorem emitRecord_trace (bits source work output : List Bool) (v p selected : Bool) :
    Trace emitRecordProgram (5 * bits.length + 7)
      ((filterState v p selected source work output bits.reverse).withPC
        (some emitRecordProgram.entry))
      ((filterState true false selected source work
        (true :: (Encoding.frame bits ++ output)) []).withPC none) := by
  have hstep : step emitRecordProgram = step SubexpPostfixControl.literalService := by
    funext c
    rfl
  change SubexponentialSAT.Computation.Trace (step emitRecordProgram) _ _ _
  rw [hstep]
  simpa only [emitRecordProgram, step, filterState, StructuredProgram.State.withPC,
    SubexpPostfixControl.cfg4] using
      SubexpPostfixControl.literalService_encode_trace bits source work output v p selected

theorem discardRecord_trace (bits source work output : List Bool) (v p selected : Bool) :
    Trace discardRecordProgram (2 * bits.length + 3)
      ((filterState v p selected source work output bits.reverse).withPC
        (some discardRecordProgram.entry))
      ((filterState false false selected source work output []).withPC none) := by
  have h := StackRoutines.clearProgram_trace (r := 3) (s := 4) 3 0 1
    (SubexpPostfixControl.triple v p selected)
    (SubexpPostfixControl.quadruple source work output bits.reverse)
  have hh := StackRoutines.halt_after_trace (StackRoutines.clearProgram (3 : Fin 4)
    (0 : Fin 3) 1) h 2 rfl rfl
  simpa [discardRecordProgram, StackRoutines.clearProgram, StackRoutines.clearResult,
    StackRoutines.clearStacks, filterState, StructuredProgram.State.withPC,
    readRegs, Nat.add_assoc] using hh

theorem resetFilterFlags_eval (v p selected : Bool)
    (source work output payload : List Bool) :
    StructuredProgram.Eval resetFilterFlags 3
      (filterState v p selected source work output payload)
      (filterState false true false source work output payload) := by
  have h0 : StructuredProgram.Eval (.atom (.set 0 false)) 1
      (filterState v p selected source work output payload)
      (filterState false p selected source work output payload) := by
    simpa [StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.withPC, StructuredProgram.State.ofCfg, execInstr,
      filterState] using StructuredProgram.Eval.atom (.set 0 false)
        (filterState v p selected source work output payload)
  have h1 : StructuredProgram.Eval (.atom (.set 1 true)) 1
      (filterState false p selected source work output payload)
      (filterState false true selected source work output payload) := by
    simpa [StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.withPC, StructuredProgram.State.ofCfg, execInstr,
      filterState] using StructuredProgram.Eval.atom (.set 1 true)
        (filterState false p selected source work output payload)
  have h2 : StructuredProgram.Eval (.atom (.set 2 false)) 1
      (filterState false true selected source work output payload)
      (filterState false true false source work output payload) := by
    simpa [StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.withPC, StructuredProgram.State.ofCfg, execInstr,
      filterState] using StructuredProgram.Eval.atom (.set 2 false)
        (filterState false true selected source work output payload)
  exact .seq h0 (.seq h1 h2)

/-! ## A complete record-order reversal pass

Prepending accepted records reverses their order. This second, unconditional
pass restores the order required by `List.filter` and the executable
sparsifier. It reverses the records, never the bits within a record.
-/

theorem recordState_eq (base : StructuredProgram.State 3 4)
    (v p f : Bool) (source payload : List Bool) :
    RecordPrograms.state filterPorts base v p f source payload =
      filterState v p f source (base.stacks 1) (base.stacks 2) payload := by
  apply congrArg₂ StructuredProgram.State.mk
  · funext i
    fin_cases i <;> simp [ filterPorts,
      SubexpPostfixControl.triple]
  · funext i
    fin_cases i <;> simp [ filterPorts,
      SubexpPostfixControl.quadruple]

theorem prependVisits_result {records : List (List Bool)}
    {before after : StructuredProgram.State 3 4}
    (h : RecordPrograms.Visits (fun _ => false) PrependEffect records before after)
    (acc : List (List Bool)) (hacc : before.stacks 2 = Encoding.encodeList id acc) :
    after.stacks 2 = Encoding.encodeList id (records.reverse ++ acc) ∧
      after.stacks 1 = before.stacks 1 := by
  induction h generalizing acc with
  | nil base => simpa using And.intro hacc (Eq.refl (base.stacks 1))
  | hit ht _ => cases ht
  | @miss bits records before middle after _ he _ ih =>
      have hm : middle.stacks 2 = Encoding.encodeList id (bits :: acc) := by
        rw [he.2, hacc]
        rfl
      obtain ⟨hout, hwork⟩ := ih (bits :: acc) hm
      refine ⟨?_, hwork.trans he.1⟩
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using hout

/-! ## Exact-order contract for the full normalization filter

The selection callback in the following theorem is a fixed structured
program with measured executions. No procedure is manufactured from the
mathematical predicate. Once that callback is supplied, the theorem tracks
the output of the actual generic record iterator, including record order.
-/

end SubexponentialSAT.SubexpNormalizeProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IrreducibleSearchBootstrapPrimitives
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed word loading and framed stack routines for the search bootstrap. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchBootstrap

open BitProgram StructuredCalls

/-- The bits here are part of the finite command, never runtime advice. -/
def pushWord (dst : Fin 28) : List Bool → Cmd 22 28
  | [] => .base .skip
  | b :: bs => .seq (pushWord dst bs) (Subexp.TupleProgram.pushConst dst 0 b)

end SubexponentialSAT.SqrtLog.IrreducibleSearchBootstrap

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

theorem negateResult_eval {r s : ℕ} (p : RecordPrograms.Ports r s) (base : State r s)
    (v pr result : Bool) (src out : List Bool) :
    Eval (negateResult p) 2 (RecordPrograms.state p base v pr result src out)
      (RecordPrograms.state p base v pr (!result) src out) := by
  cases result with
  | false =>
      apply Eval.ite_false (by simp)
      exact RecordPrograms.set_found_eval p base v pr false true src out
  | true =>
      apply Eval.ite_true (by simp)
      exact RecordPrograms.set_found_eval p base v pr true false src out

theorem negated_contract {r s : ℕ} (p : RecordPrograms.Ports r s)
    (predicate : Cmd r s) (test : List Bool → Bool) (cost : List Bool → ℕ)
    (invariant : State r s → Prop) (valid : List Bool → Prop)
    (h : RecordPrograms.CallbackContractOn p predicate test cost invariant valid) :
    RecordPrograms.CallbackContractOn p (.seq predicate (negateResult p))
      (fun bits => !(test bits)) (fun bits => cost bits + 2) invariant valid := by
  intro bits tail base hv hi
  obtain ⟨n, next, hn, hnext, run⟩ := h bits tail base hv hi
  exact ⟨n + 2, next, by dsimp; omega, hnext,
    run.seq (negateResult_eval p next false true (test bits) tail [])⟩

theorem copy_saved_eval {r s : ℕ} (p : SavedPorts r s) (base : State r s)
    (bits : List Bool) (hs : base.stacks p.saved = bits) (ht : base.stacks p.temporary = [])
    (v pr found : Bool) :
    Eval (.call (StackRoutines.copyProgram p.saved p.source p.temporary p.tag p.present))
      (7 * bits.length + 5)
      (RecordPrograms.state p.toPorts base v pr found [] [])
      (RecordPrograms.state p.toPorts base false false found bits []) := by
  have h := TupleProgram.copy_eval p.saved p.source p.temporary p.tag p.present
    p.saved_ne_source p.saved_ne_temporary p.temporary_ne_source p.tag_ne_present
    (RecordPrograms.state p.toPorts base v pr found [] [])
    (by simpa [RecordPrograms.state, p.temporary_ne_source, p.temporary_ne_payload] using ht)
  have he : (⟨readRegs (RecordPrograms.state p.toPorts base v pr found [] []).regs
      p.tag p.present none,
      StackRoutines.copyStacks p.saved p.source
        (RecordPrograms.state p.toPorts base v pr found [] []).stacks⟩ : State r s) =
      RecordPrograms.state p.toPorts base false false found bits [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i
      by_cases hv : i = p.tag <;> by_cases hp : i = p.present <;> by_cases hf : i = p.found <;>
        simp_all [readRegs, RecordPrograms.state, Function.update_apply,
          p.tag_ne_present, p.found_ne_tag, p.found_ne_present]
    · funext i
      by_cases hi : i = p.source <;> by_cases hp : i = p.payload <;>
        simp_all [StackRoutines.copyStacks, RecordPrograms.state, Function.update_apply,
          p.source_ne_payload, Ne.symm p.source_ne_payload,
          p.saved_ne_source, p.saved_ne_payload]
  rw [he] at h
  simpa [RecordPrograms.state, p.saved_ne_source, p.saved_ne_payload, hs] using h

/-! A full-dimensional candidate needs only universal scalar tests. -/

open scoped BigOperators
open SubexponentialSAT.QuarticSearch

end SubexponentialSAT.Subexp.BlockSearchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IrreducibleSearchControl
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact output of the fixed first-success record iterator. The measured
callback contract is discharged by the concrete coefficient checker. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearch

open BitProgram StructuredCalls SubexpEnumerationPayload SubexpTupleRefinement

/-- The visiting semantics stores the first successful record, including order. -/
theorem selected_of_visits_find {r s : ℕ} (output : Fin s)
    (test : List Bool → Bool) {records : List (List Bool)} {base next : State r s}
    (h : RecordPrograms.Visits test (fun bits _ b => b.stacks output = bits) records base next)
    {bits : List Bool} (hf : records.find? test = some bits) :
    next.stacks output = bits := by
  induction h with
  | nil base => simp at hf
  | @hit word rest base next ht he =>
      have hb : word = bits := by simpa [ht] using hf
      simpa only [hb] using he
  | @miss word rest base middle next ht he history ih =>
      exact ih (by simpa [ht] using hf)

end SubexponentialSAT.SqrtLog.IrreducibleSearch

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IrreducibleSearchFactorEnumeration
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! One fixed tuple-generation call produces all concatenated factor pairs. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearch

open SubexpOrderedTupleData SubexpTupleRefinement SubexpEnumerationPayload

theorem encoded_candidates_add (d e : ℕ) :
    (candidates (d + e)).map (encodeTuple (scalarCode 3)) =
      (candidates d).flatMap (fun a =>
        (candidates e).map (fun b => encodeTuple (scalarCode 3) a ++
          encodeTuple (scalarCode 3) b)) := by
  change (QuarticSearch.vectors (QuarticSearch.elements 3) (d + e)).map _ = _
  rw [← orderedRows_encoded, orderedRows_add, orderedRows_from_rows]
  rw [orderedRows_encoded, orderedRows_encoded]
  simp only [List.flatMap_map, List.map_map, Function.comp_def, candidates]

theorem encoded_factorPairs (d : ℕ) :
    (candidates ((d + 1) + (d + 1))).map (encodeTuple (scalarCode 3)) =
      (factorPairs d).map (fun ab => encodeTuple (scalarCode 3) ab.1 ++
        encodeTuple (scalarCode 3) ab.2) := by
  rw [encoded_candidates_add]
  simp only [factorPairs, List.map_flatMap, List.map_map, Function.comp_def]

end SubexponentialSAT.SqrtLog.IrreducibleSearch

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

def multiplyAddBits (bits : List Bool) : Bool × Bool :=
  scalarBits
    (scalarValue (bits[4]?.getD false) (bits[5]?.getD false) +
      scalarValue (bits[0]?.getD false) (bits[1]?.getD false) *
      scalarValue (bits[2]?.getD false) (bits[3]?.getD false))

end SubexponentialSAT.SqrtLog.IrreducibleSearchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IrreducibleSearchProgramStorage
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid preserving access to the search's coefficient arrays. The address
is a unary input stack, never a program parameter; every access uses the
same 38-label program. The source and scalar width are restored. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredProgram

theorem coefficientArray_flatten (as : List IrreducibleSearch.F) :
    coefficientArray as = (as.map coefficientWord).flatten := by
  induction as with
  | nil => rfl
  | cons a as ih => simp only [coefficientArray_cons, List.map_cons, List.flatten_cons, ih]

end SubexponentialSAT.SqrtLog.IrreducibleSearchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IrreducibleSearchProgramDot
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
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

abbrev dotScalar : Cmd 8 3 := truthTable 6 7 [0, 1, 2, 3, 4, 5] multiplyAddBits
abbrev dotBody : Cmd 8 3 :=
  .seq (atomsCommand dotReadAtoms)
    (.seq dotScalar (.seq (atomsCommand dotCopyAtoms) (.atom (.pop 0 0 6))))
abbrev dotLoop : Cmd 8 3 := .while 6 dotBody

end SubexponentialSAT.SqrtLog.IrreducibleSearchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IrreducibleSearchProgramDotRun
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Complete execution of the fixed F₃ dot product, including initialization,
serialization of its output, the final halt, and primitive simulation. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredProgram

abbrev dotCommand : Cmd 8 3 :=
  .seq (atomsCommand dotInitialAtoms) (.seq dotLoop (atomsCommand dotFinalAtoms))
abbrev dotProgram : Program 8 3 (size dotCommand + 1) := compiled dotCommand 0 2

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

abbrev dotCall {R S : ℕ} (regs : Fin 8 ↪ Fin R) (ports : Fin 3 ↪ Fin S) : Cmd R S :=
  .call (ProgramLinking.liftProgram dotProgram regs ports)

end SubexponentialSAT.SqrtLog.IrreducibleSearchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpSetupStorage
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Physical storage operations for the closed parameter setup

All copies, clears, and register resets are fixed instruction sequences or
calls to proved bit programs. Their state transformations below are assertion
notation only. The setup program uses them to isolate dirty arithmetic
subroutines from the persistent parameter words.
-/

namespace SubexponentialSAT.SubexpSetupStorage

open BitProgram StructuredCalls

theorem clear_eval {S : ℕ} (port : Fin S) (a : Data S) :
    Eval (clearCmd port) (2 * (a.stacks port).length + 3) a (clearState port a) := by
  apply Eval.call
  exact ListRegisterProgram.clear_run port (0 : Fin 16) 1 a.regs a.stacks

def clearManyCost {S : ℕ} : List (Fin S) → Data S → ℕ
  | [], _ => 0
  | p :: ps, a => 2 * (a.stacks p).length + 3 + clearManyCost ps (clearState p a)

end SubexponentialSAT.SubexpSetupStorage

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IrreducibleSearchProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
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

abbrev coefficientCommand : Cmd 16 11 :=
  .seq (copyCmd 0 3 10) <| .seq (copyCmd 2 5 10) <|
  .seq (prefixCall sixRegisters coefficientLeftPorts) <| .seq (copyCmd 2 5 10) <|
  .seq (prefixCall sixRegisters coefficientReversePorts) <| .seq (copyCmd 1 4 10) <|
  .seq (copyCmd 2 5 10) <| .seq (prefixCall sixRegisters coefficientRightPorts) <|
  .seq (dotCall eightRegisters coefficientDotPorts) <| .seq (clearCmd 3) (clearCmd 4)

end SubexponentialSAT.SqrtLog.IrreducibleSearchProgram


/-! CoefficientRun -/

/-! The closed, fixed-program boundary for one arbitrary convolution
coefficient. Its sources and runtime unary address are preserved and all
work stacks are empty again. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev coefficientProgram : Program 16 11 (size coefficientCommand + 1) :=
  compiled coefficientCommand 0 9

end SubexponentialSAT.SqrtLog.IrreducibleSearchProgram


/-! ProductLift -/

/-! A framed invocation of the source-preserving coefficient kernel. The
extra stack stores the remaining runtime product length. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev coefficientCall : Cmd 16 12 :=
  .call (ProgramLinking.liftProgram coefficientProgram id coefficientStackPorts)

end SubexponentialSAT.SqrtLog.IrreducibleSearchProgram


/-! Product -/

/-! A fixed outer loop runs the coefficient kernel at successively longer
unary addresses. Source arrays are preserved; all output coefficients are
physically written in decreasing degree order. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.StructuredProgram (Atom)

abbrev productBody : Cmd 16 12 := .seq coefficientCall <|
  .seq (.base (atomsCommand productIncrement)) (.base (.atom (.pop 11 14 15)))
abbrev productLoop : Cmd 16 12 := .while 15 productBody

end SubexponentialSAT.SqrtLog.IrreducibleSearchProgram


/-! ProductRun -/

namespace SubexponentialSAT.SqrtLog.IrreducibleSearchProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.StructuredProgram (Atom)

abbrev productCommand : Cmd 16 12 :=
  .seq (.base (.atom (.pop 11 14 15))) productLoop

abbrev productProgram : Program 16 12 (size productCommand + 1) :=
  compiled productCommand 0 9

end SubexponentialSAT.SqrtLog.IrreducibleSearchProgram


/-! Monic -/

/-! Appending the implicit monic coefficient uses two physical transfers.
No input-dependent instruction table or uncharged array append is used. -/


/-! MonicAlgebra -/


/-! CheckLift -/

/-! Framed calls to the physical Boolean predicates. -/


/-! PairProduct -/

namespace SubexponentialSAT.SqrtLog.IrreducibleSearchProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.StructuredProgram (Atom)
open SubexponentialSAT.SubexpSetupStorage

abbrev pairProductCall : Cmd 16 18 :=
  .call (ProgramLinking.liftProgram productProgram id pairProductPorts)

abbrev pairProductCommand : Cmd 16 18 :=
  .seq (copyCmd 14 11 17) <| .seq (copyCmd 14 11 17) <|
  .seq (.base (atomsCommand pairProductSetupAtoms)) <|
  .seq pairProductCall (clearCmd 2)

end SubexponentialSAT.SqrtLog.IrreducibleSearchProgram


/-! Candidate -/


/-! ProductCheck -/

namespace SubexponentialSAT.SqrtLog.IrreducibleSearchProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev productCheckCommand : Cmd 16 18 :=
  .seq pairProductCommand (.seq candidateCommand (compareCall productComparePorts))

end SubexponentialSAT.SqrtLog.IrreducibleSearchProgram


/-! Pair -/

/-! Closed primitive pair test. All three source vectors and the runtime
unary degree are preserved. The return bit is exactly the scalar pairPass. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage
open SubexponentialSAT.StructuredProgram (Atom)

abbrev pairCommand : Cmd 16 18 := .seq productCheckCommand pairTailCommand

abbrev pairProgram : Program 16 18 (size pairCommand + 1) := compiled pairCommand 13 13

end SubexponentialSAT.SqrtLog.IrreducibleSearchProgram

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

abbrev checkPair : Cmd 19 24 := .call (ProgramLinking.liftProgram pairProgram lowRegs lowStacks)
abbrev callback : Cmd 19 24 :=
  .seq unpack (.seq split (.seq checkPair
    (.seq saveResult (.seq (clear 0) (.seq (clear 1) presentTrue)))))

abbrev savedAll : Cmd 19 24 := Subexp.BlockSearchProgram.savedAllCommand savedPorts callback
def savedProgram := compiled savedAll 20 13

end SubexponentialSAT.SqrtLog.IrreducibleSearchFactorControl

/-! Fixed first-success scan using the concrete saved factor checker. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchCandidateControl

open BitProgram StructuredCalls IrreducibleSearchProgram
open Subexp.BlockSearchPreparation (restrictState lifted_call)
open SubexpEnumerationPayload SubexpTupleRefinement
attribute [local simp] Fin.addCases Fin.coe_ofNat_eq_mod

abbrev checkCandidate : Cmd 22 28 := .call (ProgramLinking.liftProgram
  IrreducibleSearchFactorControl.savedProgram lowRegs lowStacks)
abbrev callback : Cmd 22 28 :=
  .seq (.seq clearCandidate unpack) (.seq checkCandidate (.seq saveResult presentTrue))
abbrev command : Cmd 22 28 := RecordPrograms.iterate ports callback
def program := compiled command 24 13

end SubexponentialSAT.SqrtLog.IrreducibleSearchCandidateControl

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutBlocks
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Assemble complete copies of an actual universal block, with singleton
constraints on uncovered incidences. The scalar ring is arbitrary. -/
namespace SubexponentialSAT.SqrtLog.LayoutBlocks

open scoped BigOperators
open LayoutPullback LayoutExactBuckets

variable {U I F G O : Type*}
variable [Fintype U] [DecidableEq U] [Fintype I] [DecidableEq I]
variable [Fintype G] [DecidableEq G] [CommRing O]
variable {Q R b : ℕ} {label : I → U}

noncomputable def data
    (C : Layout.Data (O := O) (G := G) (id : U → U) (id : U → U) Q R)
    (P : SubexponentialSAT.BlockPacking.CompleteBlocks label b) (factor : I → F)
    (color : F → Fin Q → G)
    (hcolor : ∀ i t, C.color (label i) t = color (factor i) t) :
    Layout.Data (O := O) (G := G) (id : I → I) factor Q R := by
  classical
  let head := copyHead C label
  let J := RowIndex C P
  let embedHead := embedHead C P
  let constraints := constraints C P
  refine Layout.ofIndexed C.node C.units head color (assembledRow P C.row) ?_ ?_
    J constraints ?_
  · intro i v
    by_cases hi : i ∈ Set.range P.embed
    · obtain ⟨⟨j,u⟩, rfl⟩ := hi
      rw [assembledRow_apply]
      apply row_origin (P.blockEmbedding j) (C.row u) u
      intro w
      simpa [Pi.single_apply, eq_comm] using C.row_origin u w
    · by_cases hv : v = i <;> simp [assembledRow_outside P C.row i hi, hv]
  · intro i v
    by_cases hi : i ∈ Set.range P.embed
    · obtain ⟨⟨j,u⟩, rfl⟩ := hi
      rw [assembledRow_apply]
      exact row_degree _ _ R (C.row_degree u) v
    · by_cases hv : v = i <;> simp [assembledRow_outside P C.row i hi, hv]
  · intro t i g hg z hz
    by_cases hi : i ∈ Set.range P.embed
    · obtain ⟨⟨j,u⟩, rfl⟩ := hi
      have htype : label (P.embed (j,u)) = u := P.type_eq j u
      have hgc : g ≠ C.color u t := by
        intro heq
        apply hg
        rw [← hcolor (P.embed (j,u)) t, htype]
        exact heq
      have hc : ∀ a, signature (C.constraints t g)
          (duplicate (embedHead t g j) z) a = 0 := by
        intro a
        have hh := hz (Sum.inl (j,a))
        change value (row (embedHead t g j) (C.constraints t g a)) z = 0 at hh
        rw [value_pullback] at hh
        exact hh
      have hh := C.locality t u g hgc (duplicate (embedHead t g j) z) hc
      change value (fun v : {i : I // head t i = g} =>
        (assembledRow P C.row (P.embed (j,u)) v.val).eval (C.node t)) z = 0
      rw [assembledRow_apply]
      simp_rw [row_eval]
      have he (a : U) : C.head t a = head t (P.blockEmbedding j a) := by
        change C.head t a = C.head t (label (P.embed (j, a)))
        rw [P.type_eq]
      have hr (v : {i : I // head t i = g}) :
          row (P.blockEmbedding j) (fun a => (C.row u a).eval (C.node t)) v.val =
            row (embedHead t g j)
              (fun a : {a : U // C.head t a = g} => (C.row u a.val).eval (C.node t)) v := by
        exact LayoutHeadPullback.row_restrict (P.blockEmbedding j)
          (C.head t) (head t) he g _ v
      simp_rw [hr]
      rw [value_pullback]
      exact hh
    · change (∑ v : {i : I // head t i = g},
        (assembledRow P C.row i v.val).eval (C.node t) * (z v : O)) = 0
      rw [assembledRow_outside P C.row i hi]
      by_cases hig : head t i = g
      · let v : {i : I // head t i = g} := ⟨i,hig⟩
        have hzv : z v = 0 := by
          have hh := hz (Sum.inr ⟨v,hi⟩)
          simpa [constraints, LayoutBlocks.constraints, signature, Pi.single_apply] using hh
        have hs : (∑ a : {i : I // head t i = g},
            (if a.val = i then (1 : O) else 0) * (z a : O)) = (z v : O) := by
          have he (a : {i : I // head t i = g}) : (a.val = i) ↔ a = v := by
            exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
          simp_rw [he]
          simp
        simp only [Polynomial.eval_C, hs, hzv, Int.cast_zero]
      · apply Finset.sum_eq_zero
        intro v _
        have hv : v.val ≠ i := by
          intro h
          exact hig (h ▸ v.property)
        simp [hv]

end SubexponentialSAT.SqrtLog.LayoutBlocks

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutDenominatorProgramModel
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The concrete extension-ring denominator program. It first lifts the actual
scalar-half word, then runs the paid native multiplication loop. -/
namespace SubexponentialSAT.SqrtLog.LayoutDenominatorProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open SubexpLiftRing SubexpQuarticRing
open IntegerRingLiftProgram

def budget (R t d : ℕ) : ℕ :=
  modelSignedBudget (baseWidth 3 t) t d +
    powerBudget R (HornerProgram.Services.mulBudget (baseWidth 3 t) d) (d*baseWidth 3 t)

end SubexponentialSAT.SqrtLog.LayoutDenominatorProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpSetupFrames
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Frame and value rules for the actual setup copy/cleanup routines. -/

namespace SubexponentialSAT.SubexpSetupStorage

open BitProgram StructuredCalls

/-- Distinct empty destinations receive the original source words. The source
locations are disjoint from every destination, so earlier copies preserve them. -/
theorem copyMany_value {S : ℕ} (ps : List (Fin S × Fin S)) (a : Data S)
    (hdup : (ps.map Prod.snd).Nodup)
    (hclear : ∀ p ∈ ps, a.stacks p.2 = [])
    (hsep : ∀ p ∈ ps, ∀ q ∈ ps, p.1 ≠ q.2)
    (p : Fin S × Fin S) (hp : p ∈ ps) :
    (copyManyState ps a).stacks p.2 = a.stacks p.1 := by
  induction ps generalizing a p with
  | nil => simp at hp
  | cons q qs ih =>
    have hd : q.2 ∉ qs.map Prod.snd ∧ (qs.map Prod.snd).Nodup := by
      simpa only [List.map_cons, List.nodup_cons] using hdup
    have hne : ∀ z ∈ qs, z.2 ≠ q.2 := by
      intro z hz he
      exact hd.1 (List.mem_map.mpr ⟨z, hz, he⟩)
    rcases List.mem_cons.mp hp with he | hp
    · subst p
      have hf := copyMany_frame qs (copyState q.1 q.2 a) q.2
        (fun z hz => (hne z hz).symm)
      change (copyManyState qs (copyState q.1 q.2 a)).stacks q.2 = _
      rw [hf]
      simp [copyState, StackRoutines.copyStacks, hclear q (by simp)]
    · have hc : ∀ z ∈ qs, (copyState q.1 q.2 a).stacks z.2 = [] := by
        intro z hz
        exact (copyState_frame q.1 q.2 z.2 a (hne z hz)).trans
          (hclear z (by simp [hz]))
      have hs : ∀ z ∈ qs, ∀ w ∈ qs, z.1 ≠ w.2 := by
        intro z hz w hw
        exact hsep z (by simp [hz]) w (by simp [hw])
      exact (ih (copyState q.1 q.2 a) hd.2 hc hs p hp).trans
        (copyState_frame q.1 q.2 p.1 a (hsep p (by simp [hp]) q (by simp)))

end SubexponentialSAT.SubexpSetupStorage

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

def budget (R t d W : ℕ) : ℕ := LayoutDenominatorProgram.budget R t d + 600*(W+2)

end SubexponentialSAT.SqrtLog.LayoutDenominatorProgramQuery

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramScalar
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete arithmetic adapters for the cached layout scalar loop.
The working signed pair occupies 0/1, the next operand 2/3, the record queue
15, and the saved sum 16/17. All arithmetic is an actual compiled bit program.
-/
namespace SubexponentialSAT.SqrtLog.LayoutProgramScalar

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SqrtLog.RowSelectionProgram

def state (regs : Fin 8 → Bool) (acc work next : WordPair)
    (queue : List Bool) : Data :=
  ⟨regs, fun j => if j=0 then work.1 else if j=1 then work.2 else
    if j=2 then next.1 else if j=3 then next.2 else if j=15 then queue else
    if j=16 then acc.1 else if j=17 then acc.2 else []⟩

end SubexponentialSAT.SqrtLog.LayoutProgramScalar

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ProgramTapeReplayMacros
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Footprints of the fixed storage and scan controllers used by the leaf. -/
namespace SubexponentialSAT.SqrtLog.ProgramTapeReplay
open SubexponentialSAT BitProgram StructuredCalls
variable {r s : ℕ}

theorem avoids_clearCmd (H : Fin s → Prop) (src : Fin s) (hs : ¬ H src) :
    AvoidsCmd H (SubexpSetupStorage.clearCmd src) :=
  avoids_clearProgram H src 0 1 hs

theorem avoids_copyMany (H : Fin s → Prop) (tmp : Fin s)
    (ps : List (Fin s × Fin s)) (ht : ¬ H tmp)
    (hp : ∀ p ∈ ps, ¬ H p.1 ∧ ¬ H p.2) :
    AvoidsCmd H (SubexpSetupStorage.copyMany tmp ps) := by
  induction ps with
  | nil => trivial
  | cons p ps ih =>
    exact ⟨avoids_copyCmd H p.1 p.2 tmp (hp p (by simp)).1 (hp p (by simp)).2 ht,
      ih (fun q hq => hp q (by simp [hq]))⟩

theorem avoids_clearMany (H : Fin s → Prop) (ps : List (Fin s))
    (hp : ∀ p ∈ ps, ¬ H p) : AvoidsCmd H (SubexpSetupStorage.clearMany ps) := by
  induction ps with
  | nil => trivial
  | cons p ps ih =>
    exact ⟨avoids_clearCmd H p (hp p (by simp)), ih (fun q hq => hp q (by simp [hq]))⟩

end SubexponentialSAT.SqrtLog.ProgramTapeReplay

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

abbrev Data := StructuredProgram.State 8 15

def planBytes (plan : List ℕ) : List Bool :=
  ProgramEncoding.encodeRecords (GatherProgram.indexRecords plan)

end SubexponentialSAT.Subexp.PackingVertexLabels

end OAI.Algorithms
end


