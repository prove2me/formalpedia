-- Prove2me | Definitions.Def_OAIQ081S129
-- name    : OAIQ081S129
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T22:39:06.839024+00:00
-- url     : https://prove2.me/theorems/7e41998c-87e8-401a-9a04-2d0e0f152636
-- title:
--   Definitions bundle OAIQ081S129 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 24 declarations of OpenAI's Lean: 4 definitions and 20 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgramTable.lastPrevious`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgramTable.lastProduced`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgramTable.outputBits`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgramTable.ready`.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: [`SubexponentialSAT_SqrtLog_LeafRingSetupProgramNative`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafRingSetupProgramNative.lean), [`SubexponentialSAT_SqrtLog_RingProgramTableCanonical`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/RingProgramTableCanonical.lean), [`SubexponentialSAT_SqrtLog_RingProgramTableData`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/RingProgramTableData.lean), [`SubexponentialSAT_SqrtLog_RingProgramTableInitial`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/RingProgramTableInitial.lean), [`SubexponentialSAT_SqrtLog_RingProgramTableLoop`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/RingProgramTableLoop.lean), [`SubexponentialSAT_SqrtLog_RingProgramTableRound`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/RingProgramTableRound.lean), [`SubexponentialSAT_SqrtLog_RingProgramTableSemantics`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/RingProgramTableSemantics.lean), [`SubexponentialSAT_SqrtLog_RingProgramTableStep`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/RingProgramTableStep.lean), [`SubexponentialSAT_SubexpBasePUnranking`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SubexpBasePUnranking.lean), [`SubexponentialSAT_SubexpFieldRowPreparation`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SubexpFieldRowPreparation.lean).
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S095`, `OAIQ081S100`, `OAIQ081S101`, `OAIQ081S102` and `OAIQ081S109` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S145` and `OAIQ081S146`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S095
import Definitions.Def_OAIQ081S100
import Definitions.Def_OAIQ081S101
import Definitions.Def_OAIQ081S102
import Definitions.Def_OAIQ081S109

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingProgramTableStep
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingProgramTable

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

theorem nativeTriple_eval (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (s : Store) (regs : Fin 8 → Bool)
    (tail c minusOne previous : Word (baseWidth p t)) (suffix : List Bool)
    (hmod : s.modulus = M.bits) (hw : s.width.length = baseWidth p t) :
    ∃ n ≤ 18000*(baseWidth p t+1)^2+48*baseWidth p t+43, ∃ rf,
      Eval nativeTriple n
        (state regs {s with left := previous.val, source := tail.val ++ (c.val ++ (minusOne.val ++ suffix)), saved := []})
        (state rf {s with left := (coefficient p t M tail c minusOne previous).val, source := suffix, saved := []}) := by
  obtain ⟨n, hn, rf, he⟩ := RingScan.tripleStep_eval p t M regs tail c minusOne previous
    suffix s.count s.width hw
  have ht := compiled_halt_trace he 8 0
  let initial := {s with left := previous.val, source := tail.val ++ (c.val ++ (minusOne.val ++ suffix)), saved := []}
  have h := eval_call_lifted (compiled RingScan.tripleStep 8 0) id triplePorts
    (state regs initial) Function.injective_id triplePorts_injective ht
  refine ⟨n+1, by omega, rf, ?_⟩
  simpa only [nativeTriple, ← hmod, embed_triple, initial, coefficient] using h


theorem coefficientStep_eval (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (s : Store) (regs : Fin 8 → Bool)
    (tail c minusOne previous current : Word (baseWidth p t)) (ct avtail : List Bool)
    (hmod : s.modulus = M.bits) (hw : s.width.length = baseWidth p t)
    (hnew : s.newTail.length ≤ baseWidth p t) :
    ∃ n ≤ 18000*(baseWidth p t+1)^2+102*baseWidth p t+88, ∃ rf,
      Eval coefficientStep n
        (state regs {s with left := previous.val, source := [], saved := [], vector := current.val ++ avtail, coefficients := c.val ++ ct, tail := tail.val, minusOne := minusOne.val})
        (state rf {s with left := current.val, source := [], saved := [], vector := avtail, coefficients := ct, tail := tail.val, minusOne := minusOne.val, newTail := (coefficient p t M tail c minusOne previous).val, output := (coefficient p t M tail c minusOne previous).val.reverse ++ s.output}) := by
  let z := coefficient p t M tail c minusOne previous
  let s0 := {s with left := previous.val, source := [], saved := [], vector := current.val ++ avtail, coefficients := c.val ++ ct, tail := tail.val, minusOne := minusOne.val}
  let s1 := {s0 with source := minusOne.val}
  let s2 := {s1 with source := c.val ++ minusOne.val, coefficients := ct}
  let s3 := {s2 with source := tail.val ++ (c.val ++ minusOne.val)}
  let s4 := {s3 with left := z.val, source := []}
  let s5 := {s4 with newTail := []}
  let s6 := {s5 with newTail := z.val}
  let s7 := {s6 with left := [], output := z.val.reverse ++ s.output}
  let s8 := {s7 with left := current.val, vector := avtail}
  let rr := readRegs regs 1 3 none
  have h1 := copy_store_eval s0 s1 regs 17 9 (by decide) (by decide) (by decide) (by
    funext i; fin_cases i <;> simp [copyStacks, tapes, s0, s1])
  have h2 := load_store_eval s1 s2 rr 16 9 (by decide) c.val ct (by rfl)
    (hw.trans c.property.symm) (by
      funext i; fin_cases i <;> simp [tapes, s2, s1, s0])
  have h3 := copy_store_eval s2 s3 rr 18 9 (by decide) (by decide) (by decide) (by
    funext i; fin_cases i <;> simp [copyStacks, tapes, s3, s2, s1, s0])
  obtain ⟨n, hn, rf, h4⟩ := nativeTriple_eval p t M s3 rr tail c minusOne previous [] hmod hw
  have hh4 : Eval nativeTriple n (state rr s3) (state rf s4) := by
    simpa only [s4, s3, s2, s1, s0, z, List.append_nil] using h4
  have h5 := clear_store_eval s4 s5 rf 19 (by
    funext i; fin_cases i <;> simp [clearStacks, tapes, s5, s4])
  let rg := readRegs rf 1 3 none
  have h6 := copy_store_eval s5 s6 rg 0 19 (by decide) (by decide) (by decide) (by
    funext i; fin_cases i <;> simp [copyStacks, tapes, s6, s5, s4])
  have h7 := transfer_store_eval s6 s7 rg 0 20 (by decide) (by
    funext i; fin_cases i <;> simp [transferStacks, tapes, s7, s6, s5, s4, s3, s2, s1, s0])
  have h8 := load_store_eval s7 s8 rg 15 0 (by decide) current.val avtail (by rfl)
    (hw.trans current.property.symm) (by
      funext i; fin_cases i <;> simp [tapes, s8, s7])
  simp only [rr, rg, readRegs_reset] at h2 h3 h6 h7 h8
  have he := h1.seq (h2.seq (h3.seq (hh4.seq (h5.seq (h6.seq (h7.seq h8))))))
  refine ⟨_, ?_, rg, he⟩
  simp [s0, s1, s2, s3, s4, s5, s6, tapes]
  omega

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

abbrev outputBits (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (tail minusOne : Word (baseWidth p t)) : Pairs (baseWidth p t) → Word (baseWidth p t) → List Bool
  | [], _ => []
  | (c,a) :: pairs, previous =>
    (coefficient p t M tail c minusOne previous).val ++ outputBits p t M tail minusOne pairs a

abbrev lastPrevious {B : ℕ} : Pairs B → Word B → Word B
  | [], previous => previous
  | (_,a) :: pairs, _ => lastPrevious pairs a

abbrev lastProduced (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (tail minusOne : Word (baseWidth p t)) : Pairs (baseWidth p t) → Word (baseWidth p t) → List Bool → List Bool
  | [], _, initial => initial
  | (c,a) :: pairs, previous, _ =>
    lastProduced p t M tail minusOne pairs a (coefficient p t M tail c minusOne previous).val

theorem loop_eval (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (tail minusOne : Word (baseWidth p t))
    (pairs : Pairs (baseWidth p t)) (previous : Word (baseWidth p t))
    (s : Store) (regs : Fin 8 → Bool) (count : List Bool)
    (hcount : count.length = pairs.length) (hmod : s.modulus = M.bits)
    (hw : s.width.length = baseWidth p t) (hnew : s.newTail.length ≤ baseWidth p t) :
    ∃ n ≤ pairs.length * (18000*(baseWidth p t+1)^2+102*baseWidth p t+90)+1, ∃ rf,
      Eval coefficientLoop n
        (state (readRegs regs 1 3 count.head?) {s with left := previous.val, source := [], saved := [], vector := RingScan.rightBits pairs, coefficients := RingScan.leftBits pairs, tail := tail.val, minusOne := minusOne.val, count := count.tail})
        (state rf {s with left := (lastPrevious pairs previous).val, source := [], saved := [], vector := [], coefficients := [], tail := tail.val, minusOne := minusOne.val, count := [], newTail := lastProduced p t M tail minusOne pairs previous s.newTail, output := (outputBits p t M tail minusOne pairs previous).reverse ++ s.output}) := by
  induction pairs generalizing previous s regs count with
  | nil =>
    have hc : count = [] := List.length_eq_zero_iff.mp (by simpa using hcount)
    subst count
    refine ⟨1, by simp, readRegs regs 1 3 none, ?_⟩
    simpa [coefficientLoop, lastPrevious, lastProduced, outputBits,
      RingScan.rightBits, RingScan.leftBits] using
      (Eval.while_false (body := .seq coefficientStep popCount)
        (show (state (readRegs regs 1 3 none)
            { s with
              left := previous.val
              source := []
              saved := []
              vector := (List.nil : List Bool)
              coefficients := (List.nil : List Bool)
              tail := tail.val
              minusOne := minusOne.val
              count := [] }).regs 3 = false by
          simp [ readRegs_present]))
  | cons pair pairs ih =>
    cases count with
    | nil => simp at hcount
    | cons bit count =>
      have hc : count.length = pairs.length := by simpa using hcount
      let z := coefficient p t M tail pair.1 minusOne previous
      let s' := {s with newTail := z.val, output := z.val.reverse ++ s.output}
      obtain ⟨n, hn, rf, hs⟩ := coefficientStep_eval p t M {s with count := count}
        (readRegs regs 1 3 (some bit)) tail pair.1 minusOne previous pair.2
        (RingScan.leftBits pairs) (RingScan.rightBits pairs) hmod hw hnew
      have hp := popCount_eval
        {s' with left := pair.2.val, source := [], saved := [], vector := RingScan.rightBits pairs, coefficients := RingScan.leftBits pairs, tail := tail.val, minusOne := minusOne.val, count := count} rf
      obtain ⟨m, hm, rg, hl⟩ := ih pair.2 s' rf count hc hmod hw
        (by simpa [s'] using z.property.le)
      have he := Eval.while_true
        (show (state (readRegs regs 1 3 (some bit)) {s with left := previous.val, source := [], saved := [], vector := RingScan.rightBits (pair::pairs), coefficients := RingScan.leftBits (pair::pairs), tail := tail.val, minusOne := minusOne.val, count := count}).regs 3 = true by
          simp [ readRegs_present])
        (hs.seq hp) hl
      refine ⟨n+1+m+1, ?_, rg, ?_⟩
      · simp only [List.length_cons]
        nlinarith
      · simpa only [coefficientLoop, outputBits, lastPrevious, lastProduced, RingScan.leftBits,
          RingScan.rightBits, List.head?_cons, List.tail_cons, List.reverse_append,
          List.append_assoc, s', z] using he

theorem coefficientScan_eval (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (tail minusOne : Word (baseWidth p t))
    (pairs : Pairs (baseWidth p t)) (previous : Word (baseWidth p t))
    (s : Store) (regs : Fin 8 → Bool) (count : List Bool)
    (hcount : count.length = pairs.length) (hmod : s.modulus = M.bits)
    (hw : s.width.length = baseWidth p t) (hnew : s.newTail.length ≤ baseWidth p t) :
    ∃ n ≤ pairs.length * (18000*(baseWidth p t+1)^2+102*baseWidth p t+90)+2, ∃ rf,
      Eval coefficientScan n
        (state regs {s with left := previous.val, source := [], saved := [], vector := RingScan.rightBits pairs, coefficients := RingScan.leftBits pairs, tail := tail.val, minusOne := minusOne.val, count := count})
        (state rf {s with left := (lastPrevious pairs previous).val, source := [], saved := [], vector := [], coefficients := [], tail := tail.val, minusOne := minusOne.val, count := [], newTail := lastProduced p t M tail minusOne pairs previous s.newTail, output := (outputBits p t M tail minusOne pairs previous).reverse ++ s.output}) := by
  have hp := popCount_eval {s with left := previous.val, source := [], saved := [], vector := RingScan.rightBits pairs, coefficients := RingScan.leftBits pairs, tail := tail.val, minusOne := minusOne.val, count := count} regs
  obtain ⟨n, hn, rf, hl⟩ := loop_eval p t M tail minusOne pairs previous s regs count hcount hmod hw hnew
  exact ⟨1+n, by omega, rf, hp.seq hl⟩

end SubexponentialSAT.SqrtLog.RingProgramTable

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingProgramTableData
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingProgramTable

open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

theorem outputWords_bits (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (tail minusOne : Word (baseWidth p t))
    (pairs : Pairs (baseWidth p t)) (previous : Word (baseWidth p t)) :
    wordBits (outputWords p t M tail minusOne pairs previous) =
      outputBits p t M tail minusOne pairs previous := by
  induction pairs generalizing previous with
  | nil => rfl
  | cons pair pairs ih => simp [wordBits, outputWords, outputBits, ← ih pair.2]

theorem lastProduced_word (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (tail minusOne : Word (baseWidth p t))
    (pairs : Pairs (baseWidth p t)) (previous old : Word (baseWidth p t)) :
    lastProduced p t M tail minusOne pairs previous old.val =
      (lastOutputWord p t M tail minusOne pairs previous old).val := by
  induction pairs generalizing previous old with
  | nil => rfl
  | cons pair pairs ih => exact ih pair.2 _

theorem lastProduced_independent (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (tail minusOne : Word (baseWidth p t))
    (pairs : Pairs (baseWidth p t)) (previous : Word (baseWidth p t))
    (hn : pairs ≠ []) (x y : List Bool) :
    lastProduced p t M tail minusOne pairs previous x =
      lastProduced p t M tail minusOne pairs previous y := by
  cases pairs with
  | nil => exact False.elim (hn rfl)
  | cons pair pairs => rfl

end SubexponentialSAT.SqrtLog.RingProgramTable

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingProgramTableInitial
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingProgramTable

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpQuarticRing

theorem literalWords_bits {B : ℕ} (n : ℕ) (seed zeroWord : Word B) :
    wordBits (literalWords n seed zeroWord) = literalBits n seed zeroWord := by
  induction n generalizing seed with
  | zero => rfl
  | succ n ih => simpa [wordBits, literalWords, literalBits] using congrArg (seed.val ++ ·) (ih zeroWord)

end SubexponentialSAT.SqrtLog.RingProgramTable

end OAI.Algorithms
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

/-- The checked fixed program implements runtime-arity base-p unranking. -/
theorem program_runsIn (regs : Fin 8 → Bool) (modulus rank arity output : List Bool) :
    ∃ finalRegs : Fin 8 → Bool,
      RunsIn program (budget modulus rank arity)
        ((state regs modulus rank arity [] output).withPC (some program.entry))
        ((state finalRegs modulus (remainingRank modulus arity.length rank) [] []
          ((digitWords modulus arity.length rank).flatten ++ output)).withPC none) := by
  obtain ⟨n, hn, rf, he⟩ := command_eval regs modulus rank arity output
  exact ⟨rf, n + 1, hn, compiled_halt_trace he 6 12⟩

end SubexponentialSAT.SubexpBasePUnranking

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpFieldRowPreparation
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Preserving preparation of a local field-label row

Copy the enumerator's rank and the factor's unary arity into the checked
unranking routine, produce the fixed-width digit stream, and clear the padded
final quotient. The modulus, rank master, and arity master are preserved.
-/

namespace SubexponentialSAT.SubexpFieldRowPreparation

open BitProgram StructuredCalls StackRoutines

theorem unrank_eval (regs : Fin 8 → Bool) (m rm am rank arity output : List Bool) :
    ∃ n ≤ SubexpBasePUnranking.budget m rank arity, ∃ finalRegs,
      Eval unrank n (data regs m rm am rank arity output)
        (data finalRegs m rm am
          (SubexpBasePUnranking.remainingRank m arity.length rank) []
          ((SubexpBasePUnranking.digitWords m arity.length rank).flatten ++ output)) := by
  obtain ⟨rf, n, hn, ht⟩ := SubexpBasePUnranking.program_runsIn regs m rank arity output
  have he := eval_call_lifted SubexpBasePUnranking.program id stackPort
    (data regs m rm am rank arity output) Function.injective_id stackPort_injective ht
  rw [embed_unrank, embed_unrank] at he
  exact ⟨n, hn, rf, he⟩

/-- The local row label stream is built without changing either enumeration
master. The padded final quotient is actually cleared, even when its value is zero. -/
theorem command_eval (regs : Fin 8 → Bool) (modulus rank arity output : List Bool) :
    ∃ n ≤ budget modulus rank arity, ∃ finalRegs,
      Eval command n (data regs modulus rank arity [] [] output)
        (data finalRegs modulus rank arity [] []
          ((SubexpBasePUnranking.digitWords modulus arity.length rank).flatten ++ output)) := by
  have h₁ := copy_eval 13 6 (by decide) (by decide) (by decide) regs
    (tapes modulus rank arity [] [] output) rfl
  simp only [copyStacks, tapes_13, tapes_6, List.append_nil, tapes_update_6] at h₁
  have h₂ := copy_eval 14 8 (by decide) (by decide) (by decide) (readRegs regs 1 3 none)
    (tapes modulus rank arity rank [] output) rfl
  simp only [copyStacks, tapes_14, tapes_8, List.append_nil, tapes_update_8, readRegs_reset] at h₂
  obtain ⟨nu, hnu, rf, hu⟩ := unrank_eval (readRegs regs 1 3 none)
    modulus rank arity rank arity output
  have h₃ := clear_eval rf
    (tapes modulus rank arity (SubexpBasePUnranking.remainingRank modulus arity.length rank) []
      ((SubexpBasePUnranking.digitWords modulus arity.length rank).flatten ++ output))
  simp only [clearStacks, tapes_6, tapes_update_6, SubexpBasePUnranking.remainingRank_length] at h₃
  have h := h₁.seq (h₂.seq (hu.seq h₃))
  refine ⟨_, ?_, readRegs rf 1 3 none, h⟩
  dsimp [budget]
  omega

end SubexponentialSAT.SubexpFieldRowPreparation

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

def ready {B d : ℕ} (s : Store) (c : List.Vector (Word B) d) (v : VectorData B d)
    (zeroWord minusOne : Word B) : Store :=
  {s with left := [], source := [], saved := [], count := [], vector := wordBits v.coefficients.val, coefficients := [], minusOne := minusOne.val, tail := v.last.val, newTail := [], output := [], polynomial := wordBits c.val, zero := zeroWord.val}

theorem round_eval (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) {d : ℕ} (hd : 0 < d)
    (zeroWord minusOne : Word (baseWidth p t))
    (c : List.Vector (Word (baseWidth p t)) d) (v : VectorData (baseWidth p t) d)
    (s : Store) (regs : Fin 8 → Bool) (hmod : s.modulus = M.bits)
    (hw : s.width.length = baseWidth p t) (hdegree : s.degree.length = d) :
    ∃ n ≤ roundBudget (baseWidth p t) d, ∃ rf, Eval round n
      (state regs (ready s c v zeroWord minusOne))
      (state rf (ready {s with powers := (wordBits (advance p t M zeroWord minusOne c v).coefficients.val).reverse ++ s.powers}
        c (advance p t M zeroWord minusOne c v) zeroWord minusOne)) := by
  let pairs := c.val.zip v.coefficients.val
  let next := advance p t M zeroWord minusOne c v
  let a := ready s c v zeroWord minusOne
  have hp := prepareRound_eval a regs rfl rfl rfl
  obtain ⟨n, hn, rf, hs⟩ := coefficientScan_eval p t M v.last minusOne pairs zeroWord
    a (readRegs regs 1 3 none) s.degree (by simpa [pairs] using hdegree) hmod hw (by simp [a, ready])
  have hbits : outputBits p t M v.last minusOne pairs zeroWord = wordBits next.coefficients.val := by
    exact (outputWords_bits p t M v.last minusOne pairs zeroWord).symm
  have hlast : lastProduced p t M v.last minusOne pairs zeroWord [] = next.last.val := by
    rw [lastProduced_independent p t M v.last minusOne pairs zeroWord (by
      intro he
      have hlen : pairs.length = d := by simp [pairs]
      rw [he] at hlen
      simp at hlen
      omega) [] zeroWord.val]
    exact lastProduced_word p t M v.last minusOne pairs zeroWord zeroWord
  let b := {a with left := (lastPrevious pairs zeroWord).val, source := [], saved := [], vector := [], coefficients := [], tail := v.last.val, minusOne := minusOne.val, count := [], newTail := next.last.val, output := (wordBits next.coefficients.val).reverse}
  have hs' : Eval coefficientScan n
      (state (readRegs regs 1 3 none) {a with left := a.zero, coefficients := a.polynomial, count := a.degree})
      (state rf b) := by
    simpa only [a, ready, b, pairs, leftBits_zip, rightBits_zip, hbits, hlast, List.append_nil] using hs
  have hf := finishVector_eval b rf rfl rfl
  refine ⟨(7*a.polynomial.length+7*a.degree.length+7*a.zero.length+15) +
    (n + (2*b.left.length+13*b.output.length+2*b.tail.length+9*b.newTail.length+25)),
    ?_, readRegs rf 1 3 none, ?_⟩
  · have hlen : (wordBits next.coefficients.val).length = d*baseWidth p t := by simp
    have hprev : ((lastPrevious pairs zeroWord).val).length = baseWidth p t :=
      (lastPrevious pairs zeroWord).property
    have hvlast : v.last.val.length = baseWidth p t := v.last.property
    have hnlast : next.last.val.length = baseWidth p t := next.last.property
    have hz : zeroWord.val.length = baseWidth p t := zeroWord.property
    simp [a, ready, b, hdegree, hlen, roundBudget, hprev, hvlast, hnlast, hz,
      pairs] at hn ⊢
    apply roundBudget_covers (baseWidth p t) d n hd
    simpa [pairs] using hn
  · simpa only [round, a, b, ready, List.reverse_reverse, List.append_nil] using hp.seq (hs'.seq hf)

end SubexponentialSAT.SqrtLog.RingProgramTable

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingProgramTableSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingProgramTable

open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

theorem outputWords_correct (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (tail minusOne : Word (baseWidth p t))
    (hminus : wordValue p t minusOne = -1) (pairs : Pairs (baseWidth p t))
    (previous : Word (baseWidth p t)) :
    (outputWords p t M tail minusOne pairs previous).map (wordValue p t) =
      IrreducibleSearch.companionScan (wordValue p t tail) (wordValue p t previous)
        (pairs.map fun x => (wordValue p t x.1, wordValue p t x.2)) := by
  induction pairs generalizing previous with
  | nil => rfl
  | cons pair pairs ih =>
    simp only [outputWords, List.map_cons, IrreducibleSearch.companionScan, ih]
    congr 1
    unfold coefficient RingScan.tripleProduct
    rw [SubexpPreparedQuartic.wordAdd_correct, SubexpPreparedQuartic.wordMul_correct,
      SubexpPreparedQuartic.wordMul_correct, hminus]
    ring

theorem outputWords_last (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (tail minusOne : Word (baseWidth p t))
    (pairs : Pairs (baseWidth p t)) (hn : pairs ≠ [])
    (previous old : Word (baseWidth p t)) :
    (outputWords p t M tail minusOne pairs previous).getLast? =
      some (lastOutputWord p t M tail minusOne pairs previous old) := by
  induction pairs generalizing previous old with
  | nil => exact False.elim (hn rfl)
  | cons pair pairs ih =>
    cases pairs with
    | nil => rfl
    | cons pair' pairs =>
      simpa only [outputWords, lastOutputWord, List.getLast?_cons_cons] using
        ih (by simp) pair.2 (coefficient p t M tail pair.1 minusOne previous)


theorem iterData_succ (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) {d : ℕ}
    (zeroWord minusOne : Word (baseWidth p t)) (c : List.Vector (Word (baseWidth p t)) d)
    (n : ℕ) (v : VectorData (baseWidth p t) d) :
    iterData p t M zeroWord minusOne c (n+1) v =
      advance p t M zeroWord minusOne c (iterData p t M zeroWord minusOne c n v) := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih => exact ih (advance p t M zeroWord minusOne c v)

open SubexponentialSAT.BinaryArithmetic in
theorem outputWords_canonical (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (tail minusOne : Word (baseWidth p t))
    (pairs : Pairs (baseWidth p t)) (previous : Word (baseWidth p t)) :
    ∀ x ∈ outputWords p t M tail minusOne pairs previous, BinaryArithmetic.toNat x.val < p^t := by
  induction pairs generalizing previous with
  | nil => simp [outputWords]
  | cons pair pairs ih =>
    intro x hx
    rcases List.mem_cons.mp hx with heq | hx
    · subst x
      exact SubexpPreparedQuartic.wordAdd_canonical p t M _ _
    · exact ih pair.2 x hx

open SubexponentialSAT.BinaryArithmetic in
theorem advance_canonical (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) {d : ℕ}
    (zeroWord minusOne : Word (baseWidth p t)) (c : List.Vector (Word (baseWidth p t)) d)
    (v : VectorData (baseWidth p t) d) (i : Fin d) :
    BinaryArithmetic.toNat ((advance p t M zeroWord minusOne c v).coefficients.get i).val < p^t := by
  have hm : (advance p t M zeroWord minusOne c v).coefficients.get i ∈
      (advance p t M zeroWord minusOne c v).coefficients.val := by
    rw [← listOfFn_get]
    exact List.mem_ofFn.mpr ⟨i, rfl⟩
  exact outputWords_canonical p t M v.last minusOne _ zeroWord _ hm

end SubexponentialSAT.SqrtLog.RingProgramTable

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingProgramTableCanonical
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingProgramTable

open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing SubexponentialSAT.BinaryArithmetic

variable (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
variable (cache : RingProgram.ScalarCache p t)

theorem callbackPower_canonical {d : ℕ} (c : Fin d → Word (baseWidth p t))
    (hz : BinaryArithmetic.toNat cache.zero.val < p^t) (ho : BinaryArithmetic.toNat cache.one.val < p^t)
    (n : ℕ) (i : Fin d) :
    BinaryArithmetic.toNat ((RingProgram.powerVectorRun (RingProgram.scalarProgram p t M cache) c n).1 i).val < p^t := by
  cases n with
  | zero =>
    simp only [RingProgram.powerVectorRun, RingProgram.oneVectorRun, RingProgram.tabulateRun_eq]
    split <;> assumption
  | succ n =>
    simp only [RingProgram.powerVectorRun, RingProgram.mulXRun, RingProgram.tabulateRun_eq]
    exact SubexpPreparedQuartic.wordAdd_canonical p t M _ _

end SubexponentialSAT.SqrtLog.RingProgramTable

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

theorem clearedPorts_register_frame (ps : List (Fin 640)) (a : Data)
    (i : Fin 32) (h30 : i≠30) (h31 : i≠31) :
    (clearedPorts ps a).regs i=a.regs i := by
  induction ps generalizing a with
  | nil => rfl
  | cons p ps ih =>
    rw [clearedPorts,ih]
    simp [clearResult,readRegs,h30,h31]

/-- The first paid cleanup preserves the complete generated numeric bank. -/
theorem initial_clear_parameter_projection (a : Data) :
    projectState (registers 8 (by decide)) parameters
      (clearedPorts (workPorts++outputPorts) a) =
    projectState (registers 8 (by decide)) parameters a := by
  apply congrArg₂ StructuredProgram.State.mk
  · funext i
    apply clearedPorts_register_frame
    · intro h; have hh:=congrArg Fin.val h; simp only [registers] at hh; omega
    · intro h; have hh:=congrArg Fin.val h; simp only [registers] at hh; omega
  · funext i
    exact (clearedPorts_stacks _ _ _).trans
      (ite_eq_right (initial_clear_preserves_parameter i))

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram



end OAI.Algorithms
end


