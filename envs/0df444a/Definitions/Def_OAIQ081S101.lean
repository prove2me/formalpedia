-- Prove2me | Definitions.Def_OAIQ081S101
-- name    : OAIQ081S101
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T22:21:38.925203+00:00
-- url     : https://prove2.me/theorems/8fd6ed8a-1a5f-4038-9f42-d706b3122992
-- title:
--   Definitions bundle OAIQ081S101 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 28 declarations of OpenAI's Lean: 6 definitions and 22 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.BitGuard.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Circuit.Admissible`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.accumulateTriplesRun`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.dotTriplesRun`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingTriple.rowTriples`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingTriple.tableEncoding`.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: [`SubexponentialSAT_SqrtLog_LeafParametersProgramNative`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafParametersProgramNative.lean), [`SubexponentialSAT_SqrtLog_RingProgramFold`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/RingProgramFold.lean), [`SubexponentialSAT_SqrtLog_RingProgramSerialization`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/RingProgramSerialization.lean), [`SubexponentialSAT_SqrtLog_RingScanBridge`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/RingScanBridge.lean), [`SubexponentialSAT_SqrtLog_RingScanContract`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/RingScanContract.lean), [`SubexponentialSAT_SqrtLog_RingScanContractLoop`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/RingScanContractLoop.lean), [`SubexponentialSAT_SqrtLog_RingScanTriple`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/RingScanTriple.lean), [`SubexponentialSAT_SqrtLog_RingScanTripleLoop`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/RingScanTripleLoop.lean), [`SubexponentialSAT_SqrtLog_RingTripleBridge`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/RingTripleBridge.lean), [`SubexponentialSAT_SqrtLog_RingTripleMatrix`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/RingTripleMatrix.lean), [`SubexponentialSAT_SubexpScalarMachine`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SubexpScalarMachine.lean).
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S082` and `OAIQ081S083` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S116`, `OAIQ081S117`, `OAIQ081S118`, `OAIQ081S119`, `OAIQ081S120`, `OAIQ081S121`, `OAIQ081S125`, `OAIQ081S126`, `OAIQ081S128`, `OAIQ081S129` and `OAIQ081S136`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S082
import Definitions.Def_OAIQ081S083

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

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.BitGuard

open BitProgram StructuredCalls StructuredProgram BinaryArithmetic
abbrev Data := StructuredProgram.State 9 20

end SubexponentialSAT.SqrtLog.LeafParametersProgram.BitGuard


/- Component: SubexponentialSAT.SqrtLog.LeafParametersProgramCircuit -/

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Circuit

open BitProgram StructuredCalls BinaryArithmetic Bank

def Admissible (m : Model) : Instr → Prop
  | .clear _ => True
  | .load o _ | .copy _ o _ | .add _ _ o _ _ | .mul _ _ o _ _
  | .pow _ _ o _ _ | .sqrt _ o _ => m.len o=0
  | .quot _ b o _ _ => m.len o = 0 ∧ 0 < m.val b
  | .logSucc _ | .addConst _ _ | .pred _ | .maxTwo _ => True

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Circuit


/- Component: SubexponentialSAT.SqrtLog.LeafParametersProgramLayout -/


end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpScalarMachine
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Exact machine refinement of the prepared scalar callbacks

The program output agrees as a Boolean list with the callback output, not
only modulo the coefficient modulus. Fixed width and binary-value uniqueness
give the final identification. The program tables are independent of p and mu.
-/

namespace SubexponentialSAT.SubexpScalarMachine

open SubexponentialSAT.BinaryArithmetic SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open SubexponentialSAT.BitProgram SubexponentialSAT.ModularRingPrograms SubexponentialSAT.ModularDivisionPrograms

variable (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)

theorem wordMul_run (regs : Fin 8 → Bool) (x y : Word (baseWidth p μ)) :
    ∃ finalRegs,
      RunsIn wordMulProgram (6000 * (baseWidth p μ + 1)^2)
        ⟨some wordMulProgram.entry, regs, extendSeven (scalarInput x.val y.val M.bits) []⟩
        ⟨none, finalRegs,
          extendSeven (resting (SubexpPreparedQuartic.wordMul p μ M x y).1.val M.bits []) []⟩ := by
  obtain ⟨rf, output, hr, hlen, hv⟩ := wordMul_value regs x.val y.val M.bits
    (baseWidth p μ) x.property y.property M.length_le
    (modulus_pos p μ M) (modulus_capacity p μ M)
  have hvalue : BinaryArithmetic.toNat (SubexpPreparedQuartic.wordMul p μ M x y).1.val =
      (BinaryArithmetic.toNat x.val * BinaryArithmetic.toNat y.val) % BinaryArithmetic.toNat M.bits :=
    mulBaseRun_value _ _ _ _ (modulus_pos p μ M) (modulus_capacity p μ M)
  have heq : output = (SubexpPreparedQuartic.wordMul p μ M x y).1.val :=
    SubexpModulusConstruction.bits_eq_of_length_of_value _ _
      (hlen.trans (SubexpPreparedQuartic.wordMul p μ M x y).1.property.symm)
      (hv.trans hvalue.symm)
  exact ⟨rf, heq ▸ hr⟩

end SubexponentialSAT.SubexpScalarMachine

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingProgramSerialization
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingProgram

open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing SubexponentialSAT.BinaryArithmetic

variable (p t : ℕ) [Fact p.Prime]

omit [Fact (Nat.Prime p)] in
/-- Semantic equality of canonical base words is exact byte equality. -/
theorem word_eq_of_value (x y : ScalarCode p t)
    (hx : BinaryArithmetic.toNat x.val < p^t) (hy : BinaryArithmetic.toNat y.val < p^t)
    (h : wordValue p t x = wordValue p t y) : x = y := by
  apply Subtype.ext
  apply SubexponentialSAT.SubexpModulusConstruction.bits_eq_of_length_of_value _ _
    (x.property.trans y.property.symm)
  have hv := congrArg ZMod.val h
  simpa only [wordValue, ZMod.val_natCast, Nat.mod_eq_of_lt hx,
    Nat.mod_eq_of_lt hy] using hv

/-- Every nonempty scalar sum is canonical even if its cached zero was not. -/
theorem sumRun_canonical (M : SubexponentialSAT.SubexpPreparedQuartic.Modulus p t)
    (cache : ScalarCache p t) (x : ScalarCode p t × ℕ)
    (xs : List (ScalarCode p t × ℕ)) :
    BinaryArithmetic.toNat (sumRun (scalarProgram p t M cache) (x :: xs)).1.val < p^t :=
  SubexponentialSAT.SubexpPreparedQuartic.wordAdd_canonical p t M _ _

end SubexponentialSAT.SqrtLog.RingProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingProgramFold
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingProgram

open scoped BigOperators
open SubexponentialSAT.SubexpSymbolicCost

variable {C A : Type*} [CommRing A]

def dotTriplesRun (ops : RingProgram C) (xs : List (Triple C)) : C × ℕ :=
  sumRun ops (xs.map fun x => tripleRun ops x.1 x.2.1 x.2.2)

def accumulateTriplesRun (ops : RingProgram C) : List (Triple C) → C → C × ℕ
  | [], z => (z, 0)
  | x :: xs, z =>
    let term := tripleRun ops x.1 x.2.1 x.2.2
    let s := ops.addRun z term.1
    let out := accumulateTriplesRun ops xs s.1
    (out.1, term.2 + s.2 + out.2 + 1)

theorem dotTriplesRun_correct (ops : RepresentedRing C A) (xs : List (Triple C)) :
    ops.decode (dotTriplesRun ops.program xs).1 = (xs.map (tripleValue ops)).sum := by
  rw [dotTriplesRun, sumRun_correct]
  simp only [List.map_map, Function.comp_def, tripleRun_correct ]
  rfl

theorem accumulateTriplesRun_correct (ops : RepresentedRing C A)
    (xs : List (Triple C)) (z : C) :
    ops.decode (accumulateTriplesRun ops.program xs z).1 =
      ops.decode z + (xs.map (tripleValue ops)).sum := by
  induction xs generalizing z with
  | nil => simp [accumulateTriplesRun]
  | cons x xs ih =>
    change ops.decode (accumulateTriplesRun ops.program xs
      (ops.addRun z (tripleRun ops.program x.1 x.2.1 x.2.2).1).1).1 = _
    rw [ih, ops.add_correct, tripleRun_correct]
    simp only [List.map_cons, List.sum_cons, tripleValue]
    ring

end SubexponentialSAT.SqrtLog.RingProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingScanTriple
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A native three-scalar product and accumulator step. Triples are serialized
as consecutive fixed-width words; both width and triple count remain data. -/
namespace SubexponentialSAT.SqrtLog.RingScan

open BitProgram StructuredCalls StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

theorem scalarMul_eval (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (regs : Fin 8 → Bool) (x y : Word (baseWidth p t))
    (xs ys out count width : List Bool) :
    ∃ n ≤ 6000 * (baseWidth p t + 1)^2, ∃ finalRegs,
      Eval scalarMul n
        (addState regs M.bits x.val y.val xs ys out count width)
        (addState finalRegs M.bits (SubexpPreparedQuartic.wordMul p t M x y).1.val []
          xs ys out count width) := by
  obtain ⟨rf, n, hn, ht⟩ := SubexpScalarMachine.wordMul_run p t M regs x y
  have he := eval_call_lifted ModularRingPrograms.wordMulProgram id scalarStacks
    (addState regs M.bits x.val y.val xs ys out count width)
    Function.injective_id scalarStacks_injective
    (a := ⟨regs, ModularRingPrograms.extendSeven
      (ModularRingPrograms.scalarInput x.val y.val M.bits) []⟩)
    (b := ⟨rf, ModularRingPrograms.extendSeven
      (ModularRingPrograms.scalarInput (SubexpPreparedQuartic.wordMul p t M x y).1.val [] M.bits) []⟩) ht
  refine ⟨n, hn, rf, ?_⟩
  simpa only [embed_scalar] using he

theorem tripleStep_eval (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (regs : Fin 8 → Bool) (a b c seed : Word (baseWidth p t))
    (tail count width : List Bool) (hwidth : width.length = baseWidth p t) :
    ∃ n ≤ 18000 * (baseWidth p t + 1)^2 + 48 * baseWidth p t + 42,
      ∃ finalRegs, Eval tripleStep n
        (addState regs M.bits seed.val [] [] (a.val ++ (b.val ++ (c.val ++ tail))) [] count width)
        (addState finalRegs M.bits
          (SubexpPreparedQuartic.wordAdd p t M (tripleProduct p t M a b c) seed).1.val
          [] [] tail [] count width) := by
  let ab := (SubexpPreparedQuartic.wordMul p t M a b).1
  let abc := tripleProduct p t M a b c
  have hs := emitReverse_eval regs M.bits seed.val []
    (a.val ++ (b.val ++ (c.val ++ tail))) [] count width
  simp only [List.append_nil] at hs
  have hl := loadHead_eval (readRegs regs 1 3 none) M.bits a.val
    (b.val ++ (c.val ++ tail)) [] [] seed.val.reverse count width (hwidth.trans a.property.symm)
  have hr := loadY_eval (readRegs regs 1 3 none) M.bits a.val b.val
    (c.val ++ tail) [] seed.val.reverse count width (hwidth.trans b.property.symm)
  obtain ⟨n₁, hn₁, r₁, hm₁⟩ := scalarMul_eval p t M (readRegs regs 1 3 none)
    a b [] (c.val ++ tail) seed.val.reverse count width
  have hc := loadY_eval r₁ M.bits ab.val c.val tail [] seed.val.reverse count width
    (hwidth.trans c.property.symm)
  obtain ⟨n₂, hn₂, r₂, hm₂⟩ := scalarMul_eval p t M (readRegs r₁ 1 3 none)
    ab c [] tail seed.val.reverse count width
  have hrestore := restoreAccumulator_eval r₂ M.bits abc.val [] tail seed.val.reverse count width
  simp only [List.length_reverse, List.reverse_reverse] at hrestore
  obtain ⟨n₃, hn₃, r₃, ha⟩ := scalarAdd_eval p t M (readRegs r₂ 1 3 none)
    abc seed [] tail [] count width
  simp only [readRegs_reset] at hl hr
  have total := hs.seq (hl.seq (hr.seq (hm₁.seq (hc.seq (hm₂.seq (hrestore.seq ha))))))
  refine ⟨_, ?_, r₃, total⟩
  simp only [a.property, b.property, c.property, seed.property]
  omega

end SubexponentialSAT.SqrtLog.RingScan

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingScanTripleLoop
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed-control streaming contraction of arbitrary many scalar triples. -/
namespace SubexponentialSAT.SqrtLog.RingScan

open BitProgram StructuredCalls StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

theorem tripleLoop_eval (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (triples : List (WordTriple (baseWidth p t))) (seed : Word (baseWidth p t))
    (regs : Fin 8 → Bool) (count width suffix : List Bool)
    (hcount : count.length = triples.length) (hwidth : width.length = baseWidth p t) :
    ∃ n ≤ triples.length * (18000 * (baseWidth p t + 1)^2 + 48 * baseWidth p t + 44) + 1,
      ∃ finalRegs, Eval tripleLoop n
        (addState (readRegs regs 1 3 count.head?) M.bits seed.val [] []
          (tripleBits triples ++ suffix) [] count.tail width)
        (addState finalRegs M.bits (foldTriples p t M seed triples).val [] [] suffix [] [] width) := by
  induction triples generalizing seed regs count with
  | nil =>
      have hc : count = [] := List.length_eq_zero_iff.mp (by simpa using hcount)
      subst count
      refine ⟨1, by simp, readRegs regs 1 3 none, ?_⟩
      apply Eval.while_false
      simp [addState, readRegs_present]
  | cons x triples ih =>
      cases count with
      | nil => simp at hcount
      | cons bit count =>
          have hc : count.length = triples.length := by simpa using hcount
          obtain ⟨n, hn, rf, hs⟩ := tripleStep_eval p t M (readRegs regs 1 3 (some bit))
            x.1 x.2.1 x.2.2 seed (tripleBits triples ++ suffix) count width hwidth
          have hp := popCount_eval rf M.bits
            (SubexpPreparedQuartic.wordAdd p t M (tripleProduct p t M x.1 x.2.1 x.2.2) seed).1.val
            [] [] (tripleBits triples ++ suffix) [] count width
          obtain ⟨m, hm, rg, hl⟩ := ih
            (SubexpPreparedQuartic.wordAdd p t M (tripleProduct p t M x.1 x.2.1 x.2.2) seed).1
            rf count hc
          have he := Eval.while_true
            (show (addState (readRegs regs 1 3 (some bit)) M.bits seed.val [] []
              (x.1.val ++ (x.2.1.val ++ (x.2.2.val ++ (tripleBits triples ++ suffix)))) [] count width).regs 3 = true by
                simp [addState, readRegs_present])
            (hs.seq hp) hl
          refine ⟨n + 1 + m + 1, ?_, rg, ?_⟩
          · simp only [List.length_cons]
            nlinarith
          · simpa only [tripleLoop, tripleBits, foldTriples, List.head?_cons, List.tail_cons, List.append_assoc] using he

/-- The streaming controller is fixed. Its input stream and unary count may
have any finite size. Every scalar multiplication/addition and each scan is
included in the bound. -/
theorem tripleScan_eval_suffix (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (triples : List (WordTriple (baseWidth p t))) (seed : Word (baseWidth p t))
    (regs : Fin 8 → Bool) (count width suffix : List Bool)
    (hcount : count.length = triples.length) (hwidth : width.length = baseWidth p t) :
    ∃ n ≤ triples.length * (18000 * (baseWidth p t + 1)^2 + 48 * baseWidth p t + 44) + 2,
      ∃ finalRegs, Eval tripleScan n
        (addState regs M.bits seed.val [] [] (tripleBits triples ++ suffix) [] count width)
        (addState finalRegs M.bits (foldTriples p t M seed triples).val [] [] suffix [] [] width) := by
  have hp := popCount_eval regs M.bits seed.val [] [] (tripleBits triples ++ suffix) [] count width
  obtain ⟨n, hn, rf, hl⟩ := tripleLoop_eval p t M triples seed regs count width suffix hcount hwidth
  exact ⟨1+n, by omega, rf, hp.seq hl⟩

theorem tripleScanProgram_run_suffix (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (triples : List (WordTriple (baseWidth p t))) (seed : Word (baseWidth p t))
    (regs : Fin 8 → Bool) (count width suffix : List Bool)
    (hcount : count.length = triples.length) (hwidth : width.length = baseWidth p t) :
    ∃ finalRegs, RunsIn tripleScanProgram
      (triples.length * (18000 * (baseWidth p t + 1)^2 + 48 * baseWidth p t + 44) + 3)
      ((addState regs M.bits seed.val [] [] (tripleBits triples ++ suffix) [] count width).withPC
        (some tripleScanProgram.entry))
      ((addState finalRegs M.bits (foldTriples p t M seed triples).val [] [] suffix [] [] width).withPC none) := by
  obtain ⟨n, hn, rf, he⟩ := tripleScan_eval_suffix p t M triples seed regs count width suffix hcount hwidth
  exact ⟨rf, n+1, by omega, compiled_halt_trace he 9 0⟩

end SubexponentialSAT.SqrtLog.RingScan

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingScanBridge
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact byte interfaces between the semantic ring callbacks and fixed native
flat-stack scanners. Materializing the input vectors/triples is a separate,
explicitly charged caller operation. -/
namespace SubexponentialSAT.SqrtLog.RingScan

open BitProgram StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

theorem leftBits_map {B : ℕ} (pairs : List (Word B × Word B)) :
    leftBits pairs = (pairs.map fun x => x.1.val).flatten := by
  induction pairs with
  | nil => rfl
  | cons x xs ih => simp only [leftBits, List.map_cons, List.flatten_cons, ih]

theorem rightBits_map {B : ℕ} (pairs : List (Word B × Word B)) :
    rightBits pairs = (pairs.map fun x => x.2.val).flatten := by
  induction pairs with
  | nil => rfl
  | cons x xs ih => simp only [rightBits, List.map_cons, List.flatten_cons, ih]

theorem sumBits_map (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (pairs : List (Word (baseWidth p t) × Word (baseWidth p t))) :
    sumBits p t M pairs =
      (pairs.map fun x => (SubexpPreparedQuartic.wordAdd p t M x.1 x.2).1.val).flatten := by
  induction pairs with
  | nil => rfl
  | cons x xs ih => simp only [sumBits, List.map_cons, List.flatten_cons, ih]

theorem prepared_wordAdd_comm (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (a b : Word (baseWidth p t)) :
    (SubexpPreparedQuartic.wordAdd p t M a b).1 =
      (SubexpPreparedQuartic.wordAdd p t M b a).1 := by
  apply RingProgram.word_eq_of_value p t
  · exact SubexpPreparedQuartic.wordAdd_canonical p t M a b
  · exact SubexpPreparedQuartic.wordAdd_canonical p t M b a
  · simp only [SubexpPreparedQuartic.wordAdd_correct, add_comm]

theorem foldTriples_eq_accumulate (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    (triples : List (WordTriple (baseWidth p t))) (seed : Word (baseWidth p t)) :
    foldTriples p t M seed triples =
      (RingProgram.accumulateTriplesRun (RingProgram.scalarProgram p t M cache) triples seed).1 := by
  induction triples generalizing seed with
  | nil => rfl
  | cons x xs ih =>
      change foldTriples p t M
        (SubexpPreparedQuartic.wordAdd p t M (tripleProduct p t M x.1 x.2.1 x.2.2) seed).1 xs =
        (RingProgram.accumulateTriplesRun (RingProgram.scalarProgram p t M cache) xs
          (SubexpPreparedQuartic.wordAdd p t M seed (tripleProduct p t M x.1 x.2.1 x.2.2)).1).1
      rw [prepared_wordAdd_comm p t M]
      exact ih _

end SubexponentialSAT.SqrtLog.RingScan

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingScanContract
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed outer loop contracts a runtime-sized sequence of triple blocks. -/
namespace SubexponentialSAT.SqrtLog.RingScan
open BitProgram StructuredCalls StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

theorem contractCoordinate_eval (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t)
    (triples : List (WordTriple (baseWidth p t))) (seed : Word (baseWidth p t))
    (regs : Fin 8 → Bool) (count width suffix outer inner zero out : List Bool)
    (hc : count.length = triples.length) (hw : width.length = baseWidth p t) :
    ∃ n ≤ triples.length * (18000 * (baseWidth p t + 1)^2 + 48 * baseWidth p t + 44) + 3,
      ∃ rf, Eval contractCoordinate n
      (contractState regs M.bits seed.val (tripleBits triples ++ suffix) count width outer inner zero out)
      (contractState rf M.bits (foldTriples p t M seed triples).val suffix [] width outer inner zero out) := by
  obtain ⟨rf, n, hn, ht⟩ := tripleScanProgram_run_suffix p t M triples seed regs count width suffix hc hw
  have he := eval_call_lifted tripleScanProgram id contractLower
    (contractState regs M.bits seed.val (tripleBits triples ++ suffix) count width outer inner zero out)
    Function.injective_id contractLower_injective ht
  exact ⟨n, hn, rf, by simpa only [embed_contract] using he⟩

theorem contractStep_eval (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t)
    (triples : List (WordTriple (baseWidth p t))) (seed : Word (baseWidth p t))
    (regs : Fin 8 → Bool) (width suffix outer inner out : List Bool)
    (hc : inner.length = triples.length) (hw : width.length = baseWidth p t) :
    ∃ n ≤ inner.length * (18000 * (baseWidth p t + 1)^2 + 48 * baseWidth p t + 51)
        + 10 * baseWidth p t + 16,
      ∃ rf, Eval contractStep n
      (contractState regs M.bits [] (tripleBits triples ++ suffix) [] width outer inner seed.val out)
      (contractState rf M.bits [] suffix [] width outer inner seed.val
        ((foldTriples p t M seed triples).val.reverse ++ out)) := by
  have h1 := contractCopyCount_eval regs M.bits (tripleBits triples ++ suffix) width outer inner seed.val out
  have h2 := contractCopyZero_eval (readRegs regs 1 3 none) M.bits
    (tripleBits triples ++ suffix) inner width outer inner seed.val out
  simp only [readRegs_reset] at h2
  obtain ⟨n, hn, rf, h3⟩ := contractCoordinate_eval p t M triples seed
    (readRegs regs 1 3 none) inner width suffix outer inner seed.val out hc hw
  have h4 := contractEmit_eval rf M.bits (foldTriples p t M seed triples).val suffix width outer inner seed.val out
  refine ⟨_, ?_, readRegs rf 1 3 none, h1.seq (h2.seq (h3.seq h4))⟩
  simp only [seed.property, (foldTriples p t M seed triples).property]
  rw [← hc] at hn
  nlinarith

end SubexponentialSAT.SqrtLog.RingScan

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingScanContractLoop
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native whole-vector contraction, with both dimensions held on data tapes. -/
namespace SubexponentialSAT.SqrtLog.RingScan
open BitProgram StructuredCalls StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

theorem contractLoop_eval (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t)
    (blocks : List (List (WordTriple (baseWidth p t)))) (seed : Word (baseWidth p t))
    (regs : Fin 8 → Bool) (width suffix outer inner out : List Bool)
    (ho : outer.length = blocks.length)
    (hi : ∀ b ∈ blocks, inner.length = b.length) (hw : width.length = baseWidth p t) :
    ∃ n ≤ blocks.length * (inner.length * (18000 * (baseWidth p t + 1)^2 + 48 * baseWidth p t + 51)
        + 10 * baseWidth p t + 18) + 1,
      ∃ rf, Eval contractLoop n
      (contractState (readRegs regs 1 3 outer.head?) M.bits []
        (blockBits blocks ++ suffix) [] width outer.tail inner seed.val out)
      (contractState rf M.bits [] suffix [] width [] inner seed.val
        ((contractBits p t M seed blocks).reverse ++ out)) := by
  induction blocks generalizing regs outer out with
  | nil =>
      have he : outer = [] := List.length_eq_zero_iff.mp (by simpa using ho)
      subst outer
      refine ⟨1, by simp, readRegs regs 1 3 none, ?_⟩
      apply Eval.while_false
      simp [contractState, readRegs_present]
  | cons b bs ih =>
      cases outer with
      | nil => simp at ho
      | cons bit outer =>
          have ho' : outer.length = bs.length := by simpa using ho
          obtain ⟨n, hn, rf, hs⟩ := contractStep_eval p t M b seed (readRegs regs 1 3 (some bit))
            width (blockBits bs ++ suffix) outer inner out (hi b (by simp)) hw
          have hp := contractPop_eval rf M.bits [] (blockBits bs ++ suffix) [] width outer inner seed.val
            ((foldTriples p t M seed b).val.reverse ++ out)
          obtain ⟨m, hm, rg, hl⟩ := ih rf outer ((foldTriples p t M seed b).val.reverse ++ out)
            ho' (fun c hc => hi c (by simp [hc]))
          have he := Eval.while_true
            (show (contractState (readRegs regs 1 3 (some bit)) M.bits []
              (tripleBits b ++ (blockBits bs ++ suffix)) [] width outer inner seed.val out).regs 3 = true by
                simp [contractState, readRegs_present]) (hs.seq hp) hl
          refine ⟨n + 1 + m + 1, ?_, rg, ?_⟩
          · simp only [List.length_cons]; nlinarith
          · simpa only [contractLoop, blockBits, contractBits, List.head?_cons, List.tail_cons,
              List.reverse_append, List.append_assoc] using he

theorem contractScan_eval (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t)
    (blocks : List (List (WordTriple (baseWidth p t)))) (seed : Word (baseWidth p t))
    (regs : Fin 8 → Bool) (width suffix outer inner out : List Bool)
    (ho : outer.length = blocks.length)
    (hi : ∀ b ∈ blocks, inner.length = b.length) (hw : width.length = baseWidth p t) :
    ∃ n ≤ blocks.length * (inner.length * (18000 * (baseWidth p t + 1)^2 + 48 * baseWidth p t + 51)
        + 10 * baseWidth p t + 18) + 2,
      ∃ rf, Eval contractScan n
      (contractState regs M.bits [] (blockBits blocks ++ suffix) [] width outer inner seed.val out)
      (contractState rf M.bits [] suffix [] width [] inner seed.val
        ((contractBits p t M seed blocks).reverse ++ out)) := by
  have hp := contractPop_eval regs M.bits [] (blockBits blocks ++ suffix) [] width outer inner seed.val out
  obtain ⟨n, hn, rf, hl⟩ := contractLoop_eval p t M blocks seed regs width suffix outer inner out ho hi hw
  exact ⟨1+n, by omega, rf, hp.seq hl⟩

theorem contractVector_eval (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t)
    (blocks : List (List (WordTriple (baseWidth p t)))) (seed : Word (baseWidth p t))
    (regs : Fin 8 → Bool) (width suffix outer inner : List Bool)
    (ho : outer.length = blocks.length)
    (hi : ∀ b ∈ blocks, inner.length = b.length) (hw : width.length = baseWidth p t) :
    ∃ n ≤ blocks.length * (inner.length * (18000 * (baseWidth p t + 1)^2 + 48 * baseWidth p t + 51)
        + 13 * baseWidth p t + 18) + 5,
      ∃ rf, Eval contractVector n
      (contractState regs M.bits [] (blockBits blocks ++ suffix) [] width outer inner seed.val [])
      (contractState rf M.bits (contractBits p t M seed blocks) suffix [] width [] inner seed.val []) := by
  obtain ⟨n, hn, rf, hs⟩ := contractScan_eval p t M blocks seed regs width suffix outer inner [] ho hi hw
  simp only [List.append_nil] at hs
  have hf := contractFinish_eval rf M.bits suffix width inner seed.val (contractBits p t M seed blocks).reverse
  simp only [List.reverse_reverse, List.length_reverse, contractBits_length] at hf
  refine ⟨_, ?_, readRegs rf 1 3 none, hs.seq hf⟩
  nlinarith

theorem contractVectorProgram_run (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t)
    (blocks : List (List (WordTriple (baseWidth p t)))) (seed : Word (baseWidth p t))
    (regs : Fin 8 → Bool) (width suffix outer inner : List Bool)
    (ho : outer.length = blocks.length)
    (hi : ∀ b ∈ blocks, inner.length = b.length) (hw : width.length = baseWidth p t) :
    ∃ rf, RunsIn contractVectorProgram
      (blocks.length * (inner.length * (18000 * (baseWidth p t + 1)^2 + 48 * baseWidth p t + 51)
        + 13 * baseWidth p t + 18) + 6)
      ((contractState regs M.bits [] (blockBits blocks ++ suffix) [] width outer inner seed.val []).withPC
        (some contractVectorProgram.entry))
      ((contractState rf M.bits (contractBits p t M seed blocks) suffix [] width [] inner seed.val []).withPC none) := by
  obtain ⟨n, hn, rf, he⟩ := contractVector_eval p t M blocks seed regs width suffix outer inner ho hi hw
  exact ⟨rf, n+1, by omega, compiled_halt_trace he 9 0⟩

end SubexponentialSAT.SqrtLog.RingScan

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

theorem iScan_eval (B : ℕ) (s : Store) (rows : List (Row B))
    (tail count : List Bool) (regs : Fin 2 → Bool)
    (hc : count.length = rows.length) (hfit : RowsFit s rows) (hw : s.width.length = B) :
    ∃ n ≤ rows.length * (100 * (s.degree.length + 1) * (B + 1) + 2) + 2, ∃ regs',
      Eval iScan n
        (state regs {s with xs := xBits rows, ys := [], held := [], table := tableBits rows ++ tail, ic := count, jc := []})
        (state regs' {s with xs := [], ys := [], held := [], table := tail, ic := [], jc := [], out := (matrixBits rows).reverse ++ s.out}) := by
  have hp := popI_eval regs {s with xs := xBits rows, ys := [], held := [], table := tableBits rows ++ tail, ic := count, jc := []}
  obtain ⟨n, hn, regs', ht⟩ := iLoop_eval B s rows tail count regs hc hfit hw
  exact ⟨1 + n, by omega, regs', hp.seq ht⟩

end SubexponentialSAT.SqrtLog.RingTriple

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingTripleBridge
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The input/output of the dynamic expander is exactly the k-major table and
triple stream used by the native ring contraction. `List.ofFn` below describes
the serialized input and theorem; the fixed program builds the repeated stream
by actual counted loops and paid source copies. -/
namespace SubexponentialSAT.SqrtLog.RingTriple

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpQuarticRing

def tableEncoding {B d : ℕ} (table : Fin d → Fin d → Fin d → Word B) : List Bool :=
  (List.ofFn fun k : Fin d => (List.ofFn fun i : Fin d =>
    (List.ofFn fun j : Fin d => (table i j k).val).flatten).flatten).flatten

def rowTriples {B : ℕ} (r : Row B) : List (RingScan.WordTriple B) :=
  r.2.map fun p => (r.1, p.1, p.2)

end SubexponentialSAT.SqrtLog.RingTriple

end OAI.Algorithms
end


