-- Prove2me | Definitions.Def_OAIQ081S094
-- name    : OAIQ081S094
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T22:13:41.700905+00:00
-- url     : https://prove2.me/theorems/84c9b4d5-af7c-43a2-81db-0e21b6db53b0
-- title:
--   Definitions bundle OAIQ081S094 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 13 declarations of OpenAI's Lean: 1 definition and 12 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram.Mask.Data`.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: [`SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparsePriorityProgram`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/DisjointReuse/SparsePriorityProgram.lean), [`SubexponentialSAT_SqrtLog_RingNodeProgram`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/RingNodeProgram.lean), [`SubexponentialSAT_SqrtLog_RingProgramTableBasic`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/RingProgramTableBasic.lean), [`SubexponentialSAT_SqrtLog_RingTableLayoutProgramMatrix`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/RingTableLayoutProgramMatrix.lean), [`SubexponentialSAT_SqrtLog_RingTableLayoutProgramRowStep`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/RingTableLayoutProgramRowStep.lean), [`SubexponentialSAT_SqrtLog_RingTableLayoutProgramRows`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/RingTableLayoutProgramRows.lean), [`SubexponentialSAT_SqrtLog_RingTableLayoutProgramStep`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/RingTableLayoutProgramStep.lean), [`SubexponentialSAT_SubexpBasePUnranking`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SubexpBasePUnranking.lean).
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S067`, `OAIQ081S068`, `OAIQ081S076` and `OAIQ081S077` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S109` and `OAIQ081S113`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S067
import Definitions.Def_OAIQ081S068
import Definitions.Def_OAIQ081S076
import Definitions.Def_OAIQ081S077

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

namespace Mask

abbrev Data := State 8 4

end Mask

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpBasePUnranking
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Actual base-p digit extraction

A digit is obtained by the checked binary long-division program. Its remainder
is copied to the fixed width of the modulus, while the padded high bits are
removed. Repeated extraction uses the quotient as the next rank. The modulus,
arity, and all widths are data; the instruction table is fixed.
-/

namespace SubexponentialSAT.SubexpBasePUnranking

open BitProgram StructuredCalls StackRoutines
open BinaryArithmetic ModularQuotientArithmetic

/-- One complete division/extraction step, including actual fixed-width copying
and restoration of the quotient as the next working rank. -/
theorem extractionStep_eval (regs : Fin 8 → Bool)
    (modulus rank arity rev output : List Bool) :
    ∃ n ≤ stepBudget modulus rank, ∃ finalRegs : Fin 8 → Bool,
      Eval extractionStep n (state regs modulus rank arity rev output)
        (state finalRegs modulus (nextRank modulus rank) arity
          ((digit modulus rank).reverse ++ rev) output) := by
  obtain ⟨n, hn, rf, hd⟩ := ModularQuotientLift.programAt_eval divisionPorts modulus rank regs
    (tapes [] modulus rank [] arity [] [] rev output)
    rfl rfl rfl rfl rfl rfl rfl rfl
  change Eval (.call (ModularQuotientLift.programAt divisionPorts)) n
    (state regs modulus rank arity rev output)
    ⟨rf, Function.update (Function.update (Function.update
      (tapes [] modulus rank [] arity [] [] rev output) 0 (divide modulus rank).2)
      6 []) 7 (divide modulus rank).1⟩ at hd
  simp only [tapes_update_0, tapes_update_6, tapes_update_7] at hd
  have hc := collectDigit_eval rf (digit modulus rank)
    ((divide modulus rank).2.drop modulus.length) modulus (nextRank modulus rank)
    arity rev output (digit_length _ _)
  have hsplit : digit modulus rank ++ (divide modulus rank).2.drop modulus.length =
      (divide modulus rank).2 := List.take_append_drop _ _
  rw [hsplit] at hc
  have hhigh : ((divide modulus rank).2.drop modulus.length).length = rank.length := by
    simp only [List.length_drop, divide_remainder_length]
    omega
  have h := hd.seq hc
  refine ⟨_, ?_, readRegs rf 1 3 none, h⟩
  simp only [hhigh, nextRank_length]
  dsimp [stepBudget] at *
  omega

/-- The runtime unary arity controls a fixed while loop. Division changes the
rank value but preserves its padded bit width, so each iteration has one common
explicit bound. -/
theorem loop_eval (regs : Fin 8 → Bool) (modulus rank arity rev output : List Bool) :
    ∃ n ≤ arity.length * (stepBudget modulus rank + 2) + 1, ∃ finalRegs : Fin 8 → Bool,
      Eval loop n (afterRead regs modulus rank arity rev output)
        (state finalRegs modulus (remainingRank modulus arity.length rank) []
          ((digitWords modulus arity.length rank).flatten.reverse ++ rev) output) := by
  induction arity generalizing regs rank rev with
  | nil =>
      refine ⟨1, by simp, readRegs regs 1 3 none, ?_⟩
      have h : (afterRead regs modulus rank [] rev output).regs 3 = false := by
        simp [afterRead, state, readRegs]
      simpa [loop, afterRead, state, remainingRank, digitWords] using
        (Eval.while_false (test := (3 : Fin 8)) (body := .seq extractionStep popArity) h)
  | cons b arity ih =>
      let r₁ := readRegs regs 1 3 (some b)
      obtain ⟨ns, hns, r₂, hs⟩ := extractionStep_eval r₁ modulus rank arity rev output
      have hp := popArity_eval r₂ modulus (nextRank modulus rank) arity
        ((digit modulus rank).reverse ++ rev) output
      obtain ⟨nt, hnt, rf, ht⟩ := ih r₂ (nextRank modulus rank)
        ((digit modulus rank).reverse ++ rev)
      have hb : (afterRead regs modulus rank (b :: arity) rev output).regs 3 = true := by
        simp [afterRead, state, readRegs]
      have hloop := Eval.while_true (test := (3 : Fin 8)) hb (hs.seq hp) ht
      refine ⟨ns + 1 + nt + 1, ?_, rf, ?_⟩
      · have hbudget : stepBudget modulus (nextRank modulus rank) = stepBudget modulus rank := by
          simp [stepBudget]
        rw [hbudget] at hnt
        simp only [List.length_cons, Nat.succ_mul]
        omega
      · simpa [loop, afterRead, r₁, state, List.length_cons, remainingRank, digitWords,
          List.reverse_append, List.append_assoc] using hloop

end SubexponentialSAT.SubexpBasePUnranking

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

theorem unrank_eq_digits (m rank : List Bool) (hm : 0 < BinaryArithmetic.toNat m) (k : ℕ) :
    (digitWords m k rank).flatten = digits m.length (BinaryArithmetic.toNat m) k (BinaryArithmetic.toNat rank) := by
  induction k generalizing rank with
  | zero => rfl
  | succ k ih =>
    have hd : digit m rank = fixedBits m.length (BinaryArithmetic.toNat rank % BinaryArithmetic.toNat m) := by
      apply SubexpModulusConstruction.bits_eq_of_length_of_value
      · simp [digit_length]
      · rw [digit_value m rank hm, toNat_fixedBits_of_lt]
        exact (Nat.mod_lt _ hm).trans (SubexpFactorProgram.toNat_lt_pow_length m)
    simp only [digitWords, List.flatten_cons, digits, hd]
    rw [ih, nextRank_value m rank hm]

end SubexponentialSAT.SqrtLog.RingNodeProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingProgramTableBasic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native primitives used by the companion-table preparation machine. -/
namespace SubexponentialSAT.SqrtLog.RingProgramTable

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

theorem load_eval (d : Data) (src dst : Fin 27)
    (hinj : Function.Injective (loadPorts src dst)) (word tail : List Bool)
    (hsrc : d.stacks src = word ++ tail) (h13 : d.stacks 13 = []) (h14 : d.stacks 14 = [])
    (hwidth : (d.stacks 12).length = word.length) :
    Eval (load src dst) (14 * word.length + 12) d (afterLoad d src dst word tail) := by
  let a := RingScan.loadState ![d.regs 1, d.regs 3] (word ++ tail)
    (d.stacks dst) (d.stacks 12) [] []
  let b := RingScan.loadState ![false, false] tail
    (word ++ d.stacks dst) (d.stacks 12) [] []
  have ha : embedState loadRegisters (loadPorts src dst) d a = d := by
    apply embedState_eq_of_ports _ _ _ _ _ loadRegisters_injective hinj
    · intro i; fin_cases i <;> rfl
    · intro i hi; rfl
    · intro i; fin_cases i <;> first | exact hsrc | exact h13 | exact h14 | rfl
    · intro i hi; rfl
  have hsd : src ≠ dst := by
    intro h
    have : (0 : Fin 5) = 1 := hinj h
    exact (by decide : (0 : Fin 5) ≠ 1) this
  have hds : dst ≠ src := Ne.symm hsd
  have hsp (k : Fin 5) (hk : k ≠ 0) : loadPorts src dst k ≠ src := by
    intro h
    exact hk (hinj h)
  have hdp (k : Fin 5) (hk : k ≠ 1) : loadPorts src dst k ≠ dst := by
    intro h
    exact hk (hinj h)
  have hs12 : (12 : Fin 27) ≠ src := hsp 2 (by decide)
  have hd12 : (12 : Fin 27) ≠ dst := hdp 2 (by decide)
  have hs13 : (13 : Fin 27) ≠ src := hsp 3 (by decide)
  have hd13 : (13 : Fin 27) ≠ dst := hdp 3 (by decide)
  have hs14 : (14 : Fin 27) ≠ src := hsp 4 (by decide)
  have hd14 : (14 : Fin 27) ≠ dst := hdp 4 (by decide)
  have hb : embedState loadRegisters (loadPorts src dst) d b = afterLoad d src dst word tail := by
    apply embedState_eq_of_ports _ _ _ _ _ loadRegisters_injective hinj
    · intro i; fin_cases i <;> simp [b, RingScan.loadState, afterLoad, loadRegisters, readRegs]
    · intro i hi
      have h1 : i ≠ 1 := fun h => hi ⟨0, h.symm⟩
      have h3 : i ≠ 3 := fun h => hi ⟨1, h.symm⟩
      simp [afterLoad, readRegs, h1, h3]
    · intro i
      fin_cases i
      · simp [b, RingScan.loadState, RingScan.loadTapes, afterLoad, loadPorts, hsd]
      · simp [b, RingScan.loadState, RingScan.loadTapes, afterLoad, loadPorts]
      · simp [b, RingScan.loadState, RingScan.loadTapes, afterLoad, loadPorts, hs12, hd12]
      · simp [b, RingScan.loadState, RingScan.loadTapes, afterLoad, loadPorts, h13, hs13, hd13]
      · simp [b, RingScan.loadState, RingScan.loadTapes, afterLoad, loadPorts, h14, hs14, hd14]
    · intro i hi
      have hs : i ≠ src := fun h => hi ⟨0, h.symm⟩
      have hd : i ≠ dst := fun h => hi ⟨1, h.symm⟩
      simp [afterLoad, hs, hd]
  have ht := RingScan.loadWordProgram_trace ![d.regs 1, d.regs 3] word tail
    (d.stacks dst) (d.stacks 12) hwidth
  have hr : readRegs (![d.regs 1, d.regs 3] : Fin 2 → Bool) 0 1 none = ![false,false] := by
    first | done | (first | done | (funext i; fin_cases i <;> rfl))
  rw [hr] at ht
  have he := eval_call_lifted RingScan.loadWordProgram loadRegisters (loadPorts src dst) d
    loadRegisters_injective hinj (a := a) (b := b) ht
  simpa only [ha, hb, load] using he


theorem load_store_eval (s t : Store) (regs : Fin 8 → Bool) (src dst : Fin 27)
    (hinj : Function.Injective (loadPorts src dst)) (word tail : List Bool)
    (hsrc : tapes s src = word ++ tail)
    (hwidth : s.width.length = word.length)
    (heq : Function.update (Function.update (tapes s) src tail) dst
      (word ++ tapes s dst) = tapes t) :
    Eval (load src dst) (14 * word.length + 12) (state regs s)
      (state (readRegs regs 1 3 none) t) := by
  have h := load_eval (state regs s) src dst hinj word tail hsrc (by rfl) (by rfl) hwidth
  simpa only [afterLoad, state, heq] using h

end SubexponentialSAT.SqrtLog.RingProgramTable

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingTableLayoutProgramStep
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingTableLayout

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

theorem emit_eval (s : Store) (regs : Fin 2 → Bool) (rows : List (List Bool))
    (hp : s.powers = rows.flatten)
    (hw : ∀ row ∈ rows, row.length = s.width.length)
    (hb : s.ji.length < rows.length) (hword : s.word = []) (hindex : s.index = []) :
    ∃ rf, Eval emit
      (s.ji.length * (14 * s.width.length + 17) +
        18 * s.width.length + 7 * s.degree.length + 29)
      (state regs s)
      (state rf {s with
        ji := s.degree ++ s.ji
        rev := (wordAt rows s.ji.length).reverse ++ s.rev}) := by
  let d := state regs s
  let a := afterCopy d 16 5
  let b := afterRead a (wordAt rows s.ji.length)
  let c := afterTransfer b 4 17
  have h1 := copy_eval d 16 5 (by decide) (by decide) (by decide) (by rfl)
  have h2 := readAt_eval a rows s.ji.length
    (by simpa [a, d, afterCopy, copyStacks, state, tapes] using hp)
    (by simp [a, d, afterCopy, copyStacks, state, tapes, hindex]) hb
    (by simpa [a, d, afterCopy, copyStacks, state, tapes] using hw)
    (by rfl) (by rfl) (by rfl) (by rfl)
  have h3 := transfer_eval b 4 17 (by decide)
  have h4 := copy_eval c 1 16 (by decide) (by decide) (by decide) (by rfl)
  have hf : afterCopy c 1 16 =
      state (afterCopy c 1 16).regs {s with
        ji := s.degree ++ s.ji
        rev := (wordAt rows s.ji.length).reverse ++ s.rev} := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      fin_cases i <;>
        simp [c, b, a, d, afterCopy, afterRead, afterTransfer,
          copyStacks, transferStacks, state, tapes, hword, hindex]
  refine ⟨(afterCopy c 1 16).regs, ?_⟩
  rw [← hf]
  have hwl := wordAt_length rows s.ji.length s.width.length hb hw
  convert h1.seq (h2.seq (h3.seq h4)) using 1
  all_goals try with_reducible_and_instances rfl
  simp [c, b, a, d, afterCopy, afterRead, afterTransfer,
    copyStacks, transferStacks, state, tapes, hword, hindex, hwl]
  ring

end SubexponentialSAT.SqrtLog.RingTableLayout

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingTableLayoutProgramRows
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingTableLayout

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

theorem jLoop_eval (rows : List (List Bool)) (s : Store) (regs : Fin 2 → Bool)
    (count : List Bool) (C : ℕ)
    (hp : s.powers = rows.flatten)
    (hw : ∀ row ∈ rows, row.length = s.width.length)
    (hword : s.word = []) (hindex : s.index = [])
    (hcap : s.ji.length + count.length * s.degree.length ≤ C)
    (hv : ∀ j < count.length, s.ji.length + j*s.degree.length < rows.length) :
    ∃ n ≤ count.length * (emitBudget s.width.length s.degree.length C + 2) + 1,
      ∃ rf idx, idx.length = s.ji.length + count.length*s.degree.length ∧
      Eval jLoop n
        (state (readRegs regs 0 1 count.head?) {s with jc := count.tail})
        (state rf {s with
          jc := []
          ji := idx
          rev := (rowBits rows s.degree.length s.ji.length count.length).reverse ++ s.rev}) := by
  induction count generalizing s regs with
  | nil =>
      refine ⟨1, by simp, readRegs regs 0 1 none, s.ji, by simp, ?_⟩
      simpa [rowBits, jLoop] using
        (Eval.while_false (body := .seq emit (pop 13))
          (a := state (readRegs regs 0 1 none) {s with jc := []})
          (by simp [state, readRegs_present]))
  | cons bit count ih =>
      let s1 : Store := {s with
        jc := count
        ji := s.degree ++ s.ji
        rev := (wordAt rows s.ji.length).reverse ++ s.rev}
      have hb : s.ji.length < rows.length := by simpa using hv 0 (by simp)
      obtain ⟨r1, he⟩ := emit_eval {s with jc := count}
        (readRegs regs 0 1 (some bit)) rows hp hw hb hword hindex
      have he' : Eval emit
          (s.ji.length * (14*s.width.length+17) + 18*s.width.length + 7*s.degree.length + 29)
          (state (readRegs regs 0 1 (some bit)) {s with jc := count})
          (state r1 s1) := he
      have hr := jPop_eval s1 r1
      have hcap1 : s1.ji.length + count.length*s1.degree.length ≤ C := by
        simp only [s1, List.length_append, List.length_cons] at hcap ⊢
        nlinarith
      have hv1 : ∀ j < count.length,
          s1.ji.length + j*s1.degree.length < rows.length := by
        intro j hj
        have hh := hv (j+1) (by simpa using Nat.succ_lt_succ hj)
        simp only [s1, List.length_append] at ⊢
        nlinarith
      obtain ⟨n, hn, rf, idx, hidx, hl⟩ := ih s1 r1 hp hw hword hindex hcap1 hv1
      have ht := Eval.while_true
        (show (state (readRegs regs 0 1 (some bit)) {s with jc := count}).regs 1 = true by
          simp [state, readRegs_present]) (he'.seq hr) hl
      refine ⟨(s.ji.length * (14*s.width.length+17) + 18*s.width.length +
        7*s.degree.length + 29 + 1) + n + 1, ?_, rf, idx, ?_, ?_⟩
      · have hstart : s.ji.length ≤ C := by omega
        simp only [s1, List.length_cons] at hn ⊢
        dsimp [emitBudget] at hn ⊢
        nlinarith
      · simp only [s1, List.length_append, List.length_cons] at hidx ⊢
        nlinarith
      · simpa only [jLoop, s1, List.head?_cons, List.tail_cons, List.length_cons,
          List.length_append, rowBits, Nat.add_comm, List.reverse_append, List.append_assoc]
          using ht

theorem jScan_eval (rows : List (List Bool)) (s : Store) (regs : Fin 2 → Bool) (C : ℕ)
    (hp : s.powers = rows.flatten)
    (hw : ∀ row ∈ rows, row.length = s.width.length)
    (hword : s.word = []) (hindex : s.index = [])
    (hcap : s.ji.length + s.jc.length*s.degree.length ≤ C)
    (hv : ∀ j < s.jc.length, s.ji.length + j*s.degree.length < rows.length) :
    ∃ n ≤ s.jc.length * (emitBudget s.width.length s.degree.length C + 2) + 2,
      ∃ rf idx, idx.length = s.ji.length + s.jc.length*s.degree.length ∧
      Eval jScan n (state regs s)
        (state rf {s with
          jc := []
          ji := idx
          rev := (rowBits rows s.degree.length s.ji.length s.jc.length).reverse ++ s.rev}) := by
  obtain ⟨n, hn, rf, idx, hidx, he⟩ := jLoop_eval rows s regs s.jc C hp hw hword hindex hcap hv
  exact ⟨1+n, by omega, rf, idx, hidx, (jPop_eval s regs).seq he⟩

end SubexponentialSAT.SqrtLog.RingTableLayout

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingTableLayoutProgramRowStep
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingTableLayout

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

theorem finishRow_eval (s : Store) (regs : Fin 2 → Bool) :
    ∃ rf, Eval finishRow (2*s.ji.length + 7*s.degree.length + 8)
      (state regs s) (state rf {s with ji := [], ii := s.degree ++ s.ii}) := by
  let d := state regs s
  let a := afterClear d 16
  have h1 := clear_eval d 16
  have h2 := copy_eval a 1 15 (by decide) (by decide) (by decide) (by rfl)
  have hf : afterCopy a 1 15 =
      state (afterCopy a 1 15).regs {s with ji := [], ii := s.degree ++ s.ii} := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      fin_cases i <;> simp [a, d, afterClear, copyStacks, clearStacks, state, tapes]
  refine ⟨(afterCopy a 1 15).regs, ?_⟩
  rw [← hf]
  convert h1.seq h2 using 1
  all_goals try with_reducible_and_instances rfl
  simp [a, d, afterClear, clearStacks, state, tapes]
  omega

theorem rowStep_eval (rows : List (List Bool)) (s : Store) (regs : Fin 2 → Bool) (C : ℕ)
    (hp : s.powers = rows.flatten)
    (hw : ∀ row ∈ rows, row.length = s.width.length)
    (hword : s.word = []) (hindex : s.index = []) (hj : s.ji = []) (hc : s.jc = [])
    (hcap : s.ii.length + s.degree.length*s.degree.length ≤ C)
    (hv : ∀ j < s.degree.length, s.ii.length+j*s.degree.length < rows.length) :
    ∃ n ≤ rowBudget s.width.length s.degree.length C, ∃ rf,
      Eval rowStep n (state regs s)
        (state rf {s with
          ii := s.degree ++ s.ii
          rev := (rowBits rows s.degree.length s.ii.length s.degree.length).reverse ++ s.rev}) := by
  obtain ⟨r1, h1⟩ := startRow_eval s regs hj hc
  let a : Store := {s with ji := s.ii, jc := s.degree}
  obtain ⟨n, hn, r2, idx, hidx, h2⟩ := jScan_eval rows a r1 C hp hw hword hindex hcap hv
  let b : Store := {s with
    jc := []
    ji := idx
    rev := (rowBits rows s.degree.length s.ii.length s.degree.length).reverse ++ s.rev}
  have h2' : Eval jScan n (state r1 a) (state r2 b) := h2
  obtain ⟨r3, h3⟩ := finishRow_eval b r2
  refine ⟨(7*s.ii.length + 7*s.degree.length + 10) +
    (n + (2*idx.length + 7*s.degree.length + 8)), ?_, r3, ?_⟩
  · dsimp [a] at hn hidx
    dsimp [rowBudget, b]
    nlinarith
  · simpa only [rowStep, a, b, hj, hc] using h1.seq (h2'.seq h3)

end SubexponentialSAT.SqrtLog.RingTableLayout

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingTableLayoutProgramMatrix
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingTableLayout

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

theorem iLoop_eval (rows : List (List Bool)) (s : Store) (regs : Fin 2 → Bool)
    (count : List Bool) (C : ℕ)
    (hp : s.powers = rows.flatten)
    (hw : ∀ row ∈ rows, row.length = s.width.length)
    (hword : s.word = []) (hindex : s.index = []) (hj : s.ji = []) (hc : s.jc = [])
    (hcap : s.ii.length + count.length*s.degree.length + s.degree.length*s.degree.length ≤ C)
    (hv : ∀ i < count.length, ∀ j < s.degree.length,
      s.ii.length + i*s.degree.length + j*s.degree.length < rows.length) :
    ∃ n ≤ count.length * (rowBudget s.width.length s.degree.length C + 2) + 1,
      ∃ rf idx, idx.length = s.ii.length + count.length*s.degree.length ∧
      Eval iLoop n
        (state (readRegs regs 0 1 count.head?) {s with ic := count.tail})
        (state rf {s with
          ic := []
          ii := idx
          rev := (matrixBits rows s.degree.length s.ii.length count.length).reverse ++ s.rev}) := by
  induction count generalizing s regs with
  | nil =>
      refine ⟨1, by simp, readRegs regs 0 1 none, s.ii, by simp, ?_⟩
      simpa [matrixBits] using
        (Eval.while_false (body := .seq rowStep (pop 12))
          (a := state (readRegs regs 0 1 none) {s with ic := []})
          (by simp [state, readRegs_present]))
  | cons bit count ih =>
      let s1 : Store := {s with
        ic := count
        ii := s.degree ++ s.ii
        rev := (rowBits rows s.degree.length s.ii.length s.degree.length).reverse ++ s.rev}
      have hcap0 : s.ii.length + s.degree.length*s.degree.length ≤ C := by omega
      have hv0 : ∀ j < s.degree.length, s.ii.length+j*s.degree.length < rows.length := by
        intro j hj
        simpa using hv 0 (by simp) j hj
      obtain ⟨m, hm, r1, he⟩ := rowStep_eval rows {s with ic := count}
        (readRegs regs 0 1 (some bit)) C hp hw hword hindex hj hc hcap0 hv0
      have he' : Eval rowStep m
          (state (readRegs regs 0 1 (some bit)) {s with ic := count}) (state r1 s1) := he
      have hr := iPop_eval s1 r1
      have hcap1 : s1.ii.length + count.length*s1.degree.length +
          s1.degree.length*s1.degree.length ≤ C := by
        simp only [s1, List.length_append, List.length_cons] at hcap ⊢
        nlinarith
      have hv1 : ∀ i < count.length, ∀ j < s1.degree.length,
          s1.ii.length+i*s1.degree.length+j*s1.degree.length < rows.length := by
        intro i hi j hj
        have hh := hv (i+1) (by simpa using Nat.succ_lt_succ hi) j hj
        simp only [s1, List.length_append] at ⊢
        nlinarith
      obtain ⟨n, hn, rf, idx, hidx, hl⟩ := ih s1 r1 hp hw hword hindex hj hc hcap1 hv1
      have ht := Eval.while_true
        (show (state (readRegs regs 0 1 (some bit)) {s with ic := count}).regs 1 = true by
          simp [state, readRegs_present]) (he'.seq hr) hl
      refine ⟨(m+1)+n+1, ?_, rf, idx, ?_, ?_⟩
      · simp only [s1, List.length_cons] at hm hn ⊢
        nlinarith
      · simp only [s1, List.length_append, List.length_cons] at hidx ⊢
        nlinarith
      · simpa only [iLoop, s1, List.head?_cons, List.tail_cons, List.length_cons,
          List.length_append, matrixBits, Nat.add_comm, List.reverse_append, List.append_assoc]
          using ht

theorem iScan_eval (rows : List (List Bool)) (s : Store) (regs : Fin 2 → Bool) (C : ℕ)
    (hp : s.powers = rows.flatten)
    (hw : ∀ row ∈ rows, row.length = s.width.length)
    (hword : s.word = []) (hindex : s.index = []) (hj : s.ji = []) (hc : s.jc = [])
    (hcap : s.ii.length + s.ic.length*s.degree.length + s.degree.length*s.degree.length ≤ C)
    (hv : ∀ i < s.ic.length, ∀ j < s.degree.length,
      s.ii.length+i*s.degree.length+j*s.degree.length < rows.length) :
    ∃ n ≤ s.ic.length * (rowBudget s.width.length s.degree.length C + 2) + 2,
      ∃ rf idx, idx.length = s.ii.length + s.ic.length*s.degree.length ∧
      Eval iScan n (state regs s)
        (state rf {s with
          ic := []
          ii := idx
          rev := (matrixBits rows s.degree.length s.ii.length s.ic.length).reverse ++ s.rev}) := by
  obtain ⟨n, hn, rf, idx, hidx, he⟩ :=
    iLoop_eval rows s regs s.ic C hp hw hword hindex hj hc hcap hv
  exact ⟨1+n, by omega, rf, idx, hidx, (iPop_eval s regs).seq he⟩

end SubexponentialSAT.SqrtLog.RingTableLayout

end OAI.Algorithms
end


