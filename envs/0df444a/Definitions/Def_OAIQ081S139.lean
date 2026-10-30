-- Prove2me | Definitions.Def_OAIQ081S139
-- name    : OAIQ081S139
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T22:46:08.104194+00:00
-- url     : https://prove2.me/theorems/d4bde748-e4bf-422b-a315-f950434eb0d1
-- title:
--   Definitions bundle OAIQ081S139 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 91 declarations of OpenAI's Lean: 80 definitions, 2 inductive types or structures and 9 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Clause.cost`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Clause.step`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.LiteralCallback.budget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.LiteralCallback.negateBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.LiteralCallback.negative`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.LiteralCallback.result`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.LiteralCallback.value`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Row.WeightedClause`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Row.clauseValue`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Row.cost`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Row.literalList`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Row.payload`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Row.value`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgram.Expansion.coefficient`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgram.Expansion.weightedClause`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgram.Expansion.weightedRow`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Branches.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Branches.loop`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Branches.pop`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Branches.program`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Branches.push`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Branches.record`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Bounds.Bounded`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Bounds.Good`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Bounds.Valid`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Multiplier.arithmeticCost`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Multiplier.byteEntries`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Multiplier.complementCost`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Multiplier.complemented`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Multiplier.cubic`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Multiplier.prepareCost`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Multiplier.prepared`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Multiplier.shiftForward`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Multiplier.shifted`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps.Context`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps.Raw`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps.accumulatorCost`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps.addCost`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps.applyLoopCost`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps.constant` and 42 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLog_HashCircuitProgramInterpreter`, `SubexponentialSAT_SqrtLog_HashCircuitProgramMeaning`, `SubexponentialSAT_SqrtLog_HashInputProgramExpansion`, `SubexponentialSAT_SqrtLog_HighIncidenceProgramBranches`, `SubexponentialSAT_SqrtLog_HornerProgramServices`, `SubexponentialSAT_SqrtLog_IdempotentApplyProgramBounds`, `SubexponentialSAT_SqrtLog_IdempotentApplyProgramBoundsCapacity`, `SubexponentialSAT_SqrtLog_IdempotentApplyProgramExecution`, `SubexponentialSAT_SqrtLog_IdempotentApplyProgramFinal`, `SubexponentialSAT_SqrtLog_IdempotentApplyProgramMultiplierKernel`, `SubexponentialSAT_SqrtLog_IdempotentApplyProgramServices`, `SubexponentialSAT_SqrtLog_IdempotentApplyProgramStored`, `SubexponentialSAT_SqrtLog_IdempotentPreparationProgramScalarMachine`, `SubexponentialSAT_SqrtLog_IdempotentPreparationProgramScalarRun`, `SubexponentialSAT_SqrtLog_InterpolationCacheProgramScan`, `SubexponentialSAT_SqrtLog_LeafParametersProgramNative`, `SubexponentialSAT_SqrtLog_MomentsProgramNormalize`, `SubexponentialSAT_SqrtLog_MomentsProgramProduct`, `SubexponentialSAT_SqrtLog_RingScanService`, `SubexponentialSAT_SqrtLog_RingTripleExpand`, `SubexponentialSAT_SqrtLog_RingTripleProgram`, `SubexponentialSAT_UnaryForPrograms`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S116`, `OAIQ081S117`, `OAIQ081S118` and `OAIQ081S119` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S153`, `OAIQ081S154`, `OAIQ081S155`, `OAIQ081S157`, `OAIQ081S158` and `OAIQ081S165`; the statements `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorProductSpace.accumulate_run_space`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TruncatedRingProgram.product_dense`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TruncatedRingProgram.product_work_le`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Cost.clause_le`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Cost.literal_le`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Cost.negative_le`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Cost.product_le`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Cost.row_le`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Clause.callback_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Row.program_runs`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.WeightedCallbacks.accumulate_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.WeightedCallbacks.complement_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.WeightedCore.command_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgram.Expansion.forward_original_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Bounds.loopCost_le`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Bounds.mulCost_le`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Bounds.prepareCost_le`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Bounds.totalCost_le`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Multiplier.arithmetic_runs`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Multiplier.prepared_denote`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps.accumulator_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps.add_constant_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps.applyLoop_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps.loop_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps.mul_hash_clean`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.add_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.descendingStored_denote`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.accumulate_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NativeSemantics.clause_denote_scoped`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Normalize.program_run` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.step_eval`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorProductSpace.accumulate_run_space`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TruncatedRingProgram.product_dense`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TruncatedRingProgram.product_work_le`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.checkLoop_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.program_runsIn`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.rowStep_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Cost.clause_le`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Cost.literal_le`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Cost.negative_le`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Cost.product_le`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Cost.row_le`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Clause.callback_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Row.program_runs`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.WeightedCallbacks.accumulate_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.WeightedCallbacks.complement_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.WeightedCore.command_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgram.Expansion.forward_original_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Bounds.loopCost_le`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Bounds.mulCost_le`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Bounds.prepareCost_le`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Bounds.totalCost_le`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Multiplier.arithmetic_runs`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Multiplier.prepared_denote`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps.accumulator_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps.add_constant_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps.applyLoop_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps.loop_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps.mul_hash_clean`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.add_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.descendingStored_denote`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.accumulate_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NativeSemantics.clause_denote_scoped`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Normalize.program_run` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.step_eval`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S116
import Definitions.Def_OAIQ081S117
import Definitions.Def_OAIQ081S118
import Definitions.Def_OAIQ081S119

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsProgramNormalize
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms



namespace SubexponentialSAT.SqrtLog.MomentsProgram.Normalize
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

variable {K : Type*} [DecidableEq K]

def work (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {d : ℕ} (key : K → List Bool) :
    List (K × RingProgram.Code (Word (baseWidth p t)) d) →
    List (K × RingProgram.Code (Word (baseWidth p t)) d) → ℕ
  | [], _ => 1
  | a::source, seed => stepBudget p t M cache key seed a.1 a.2 + 2 +
      work p t M cache key source (Dictionary.insertCode p t M cache a.1 a.2 seed)

end SubexponentialSAT.SqrtLog.MomentsProgram.Normalize


end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingTripleExpand
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingTriple

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpQuarticRing

theorem kLoop_eval (B : ℕ) (s : Store) (matrices : List (List (Row B)))
    (tail count : List Bool) (regs : Fin 2 → Bool)
    (hc : count.length = matrices.length)
    (hfit : ∀ a ∈ matrices, MatrixFits s a) (hw : s.width.length = B) :
    ∃ n ≤ matrices.length * (200 * (s.degree.length + 1)^2 * (B + 1) + 2) + 1, ∃ regs',
      Eval kLoop n
        (state (readRegs regs 0 1 count.head?)
          {s with xs := [], ys := [], held := [], table := allTableBits matrices ++ tail, kc := count.tail, ic := [], jc := []})
        (state regs' {s with xs := [], ys := [], held := [], table := tail, kc := [], ic := [], jc := [], out := (allTripleBits matrices).reverse ++ s.out}) := by
  induction matrices generalizing s count regs with
  | nil =>
    have hcount : count = [] := List.length_eq_zero_iff.mp (by simpa using hc)
    subst count
    refine ⟨1, by simp, readRegs regs 0 1 none, ?_⟩
    simpa [allTableBits, allTripleBits] using
      (Eval.while_false (test := (1 : Fin 2)) (body := .seq matrixStep popK)
        (a := state (readRegs regs 0 1 none)
          {s with xs := [], ys := [], held := [], table := tail, kc := [], ic := [], jc := []})
        (by simp [state, readRegs_present]))
  | cons a matrices ih =>
    cases count with
    | nil => simp at hc
    | cons bit count =>
      have hc' : count.length = matrices.length := by simpa using hc
      have ha := hfit a (by simp)
      obtain ⟨u, hu, r₁, hstep⟩ := matrixStep_eval B {s with kc := count} a
        (allTableBits matrices ++ tail) (readRegs regs 0 1 (some bit)) ha hw
      let m := {s with xs := [], ys := [], held := [], table := allTableBits matrices ++ tail, kc := count, ic := [], jc := [], out := (matrixBits a).reverse ++ s.out}
      have hp := popK_eval r₁ m
      have hfit' : ∀ a ∈ matrices, MatrixFits m a := by
        intro a ha
        exact hfit a (by simp [ha])
      obtain ⟨n, hn, r₂, hloop⟩ := ih m count r₁ hc' hfit' hw
      have hbody : Eval (.seq matrixStep popK) (u + 1)
          (state (readRegs regs 0 1 (some bit))
            {s with xs := [], ys := [], held := [], table := allTableBits (a :: matrices) ++ tail, kc := count, ic := [], jc := []})
          (state (readRegs r₁ 0 1 count.head?) {m with kc := count.tail}) := by
        simpa [m, allTableBits, List.append_assoc] using hstep.seq hp
      refine ⟨u + 1 + n + 1, ?_, r₂, ?_⟩
      · change n ≤ matrices.length * (200 * (s.degree.length + 1)^2 * (B + 1) + 2) + 1 at hn
        change u ≤ 200 * (s.degree.length + 1)^2 * (B + 1) at hu
        simp only [List.length_cons]
        nlinarith
      · have he := Eval.while_true (test := (1 : Fin 2))
          (show (state (readRegs regs 0 1 (some bit))
            {s with xs := [], ys := [], held := [], table := allTableBits (a :: matrices) ++ tail, kc := count, ic := [], jc := []}).regs 1 = true by
              simp [state, readRegs_present]) hbody hloop
        simpa [kLoop, m, allTripleBits, List.reverse_append, List.append_assoc] using he

theorem kScan_eval (B : ℕ) (s : Store) (matrices : List (List (Row B)))
    (tail count : List Bool) (regs : Fin 2 → Bool)
    (hc : count.length = matrices.length)
    (hfit : ∀ a ∈ matrices, MatrixFits s a) (hw : s.width.length = B) :
    ∃ n ≤ matrices.length * (200 * (s.degree.length + 1)^2 * (B + 1) + 2) + 2, ∃ regs',
      Eval kScan n
        (state regs {s with xs := [], ys := [], held := [], table := allTableBits matrices ++ tail, kc := count, ic := [], jc := []})
        (state regs' {s with xs := [], ys := [], held := [], table := tail, kc := [], ic := [], jc := [], out := (allTripleBits matrices).reverse ++ s.out}) := by
  have hp := popK_eval regs {s with xs := [], ys := [], held := [], table := allTableBits matrices ++ tail, kc := count, ic := [], jc := []}
  obtain ⟨n, hn, regs', ht⟩ := kLoop_eval B s matrices tail count regs hc hfit hw
  exact ⟨1 + n, by omega, regs', hp.seq ht⟩

end SubexponentialSAT.SqrtLog.RingTriple

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingTripleProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingTriple

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpQuarticRing

theorem expand_eval (B : ℕ) (s : Store) (matrices : List (List (Row B)))
    (regs : Fin 2 → Bool) (hd : s.degree.length = matrices.length)
    (hfit : ∀ a ∈ matrices, MatrixFits s a) (hw : s.width.length = B) :
    ∃ n ≤ expandBudget B s.degree.length, ∃ regs',
      Eval expand n
        (state regs {s with table := allTableBits matrices, out := [], xs := [], ys := [], held := [], kc := [], ic := [], jc := []})
        (state regs' {s with table := [], out := [], xs := allTripleBits matrices, ys := [], held := [], kc := [], ic := [], jc := []}) := by
  let a := {s with table := allTableBits matrices, out := [], xs := [], ys := [], held := [], ic := [], jc := []}
  have hcopy := copyK_eval a regs
  obtain ⟨n, hn, r₁, hscan⟩ := kScan_eval B {s with out := []} matrices [] s.degree
    (readRegs regs 0 1 none) hd hfit hw
  simp only [List.append_nil] at hscan
  let b := {s with table := [], out := (allTripleBits matrices).reverse, xs := [], ys := [], held := [], kc := [], ic := [], jc := []}
  have hfinish := finish_eval b r₁
  dsimp only [b] at hfinish
  simp only [List.length_reverse, List.reverse_reverse] at hfinish
  have hlen : (allTripleBits matrices).length = 3 * B * s.degree.length^3 := by
    rw [allTripleBits_length s matrices hfit, ← hd]
    ring
  refine ⟨(7 * s.degree.length + 5) + (n + (3 * (allTripleBits matrices).length + 3)),
    ?_, readRegs r₁ 0 1 none, ?_⟩
  · rw [← hd] at hn
    rw [hlen]
    unfold expandBudget
    nlinarith
  · simpa [a, b, List.length_reverse, List.reverse_reverse, List.append_nil] using
      hcopy.seq (hscan.seq hfinish)

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

theorem multiplicationBits_length {B d : ℕ}
    (table : Fin d → Fin d → Fin d → Word B) (x y : RingProgram.Code (Word B) d) :
    (blockBits (multiplicationBlocks table x y)).length = 3*B*d^3 := by
  rw [blockBits_length_uniform _ (multiplicationBlocks_uniform table x y), multiplicationBlocks_length]
  ring

end SubexponentialSAT.SqrtLog.RingScan

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
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

def keptJoin {n B d : ℕ} (left : Squarefree.Index (Fin n)) (u J : ℕ) : List (Entry n B d) → List (Entry n B d)
  | [] => []
  | (b,c)::rest => if (left.join b).Kept u J then (left.join b,c)::keptJoin left u J rest
      else keptJoin left u J rest

def block (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {n d : ℕ}
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t)) (u J : ℕ)
    (a : Entry n (baseWidth p t) d) (right : List (Entry n (baseWidth p t) d)) :=
  (keptJoin a.1 u J (Squarefree.ScaleProgram.scaled p t M cache table a.2 right)).reverse

end SubexponentialSAT.SqrtLog.MomentsProgram.Product


namespace SubexponentialSAT.SqrtLog.MomentsProgram.Product
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

def stepBudget (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {n d : ℕ}
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t)) (u J : ℕ)
    (a : Entry n (baseWidth p t) d) (right seed : List (Entry n (baseWidth p t) d)) : ℕ :=
  let scaled := Squarefree.ScaleProgram.scaled p t M cache table a.2 right
  let source := block p t M cache table u J a right
  (6*(Squarefree.encodeIndex a.1).length+9*(RingProgram.flat a.2).length+11) +
  (7*(bytes right).length+11*(RingProgram.flat a.2).length+
    Squarefree.ScaleProgram.budget Squarefree.encodeIndex right+17) +
  (9*(bytes scaled).length+5*(Squarefree.encodeIndex a.1).length+9*u+9*J+
    Squarefree.KeyMapProgram.budget a.1 u J (coefficientBytes scaled)+32) +
  (9*(bytes source).length+9*d+Normalize.work p t M cache Squarefree.encodeIndex source seed+18)

end SubexponentialSAT.SqrtLog.MomentsProgram.Product


namespace SubexponentialSAT.SqrtLog.MomentsProgram.Product
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

def run (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {n d : ℕ}
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t)) (u J : ℕ) :
    List (Entry n (baseWidth p t) d) → List (Entry n (baseWidth p t) d) →
      List (Entry n (baseWidth p t) d) → List (Entry n (baseWidth p t) d)
  | [], _, seed => seed
  | a::left, right, seed => run p t M cache table u J left right
      (Normalize.run p t M cache (block p t M cache table u J a right) seed)

def work (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {n d : ℕ}
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t)) (u J : ℕ) :
    List (Entry n (baseWidth p t) d) → List (Entry n (baseWidth p t) d) →
      List (Entry n (baseWidth p t) d) → ℕ
  | [], _, _ => 1
  | a::left, right, seed => stepBudget p t M cache table u J a right seed + 2 +
      work p t M cache table u J left right
        (Normalize.run p t M cache (block p t M cache table u J a right) seed)

end SubexponentialSAT.SqrtLog.MomentsProgram.Product

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashCircuitProgramMeaning
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact pure result functions of the fixed native hash interpreter. The
execution proofs live in HashCircuitProgramInterpreter; no alternate evaluator
or operation oracle is introduced here. -/
namespace SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.LiteralCallback
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open MomentsProgram

variable (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
variable (cache : RingProgram.ScalarCache p t) {n d : ℕ}
variable (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
variable (minusOne : RingProgram.Code (Word (baseWidth p t)) d)
variable (one payload left : List (Product.Entry n (baseWidth p t) d))

def negative : List (Product.Entry n (baseWidth p t) d) :=
  Normalize.run p t M cache
    (Squarefree.ScaleProgram.scaled p t M cache table minusOne payload) one

def value (positive : Bool) : List (Product.Entry n (baseWidth p t) d) :=
  if positive then negative p t M cache table minusOne one payload else payload

def result (u J : ℕ) (positive : Bool) : List (Product.Entry n (baseWidth p t) d) :=
  Product.run p t M cache table u J left (value p t M cache table minusOne one payload positive) []

end SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.LiteralCallback

namespace SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Clause
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open MomentsProgram

variable (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
variable (cache : RingProgram.ScalarCache p t) {n d : ℕ}
variable (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
variable (minusOne : RingProgram.Code (Word (baseWidth p t)) d)
variable (one : List (Product.Entry n (baseWidth p t) d))
variable (incidence : Fin n → List (Product.Entry n (baseWidth p t) d))
variable (u J : ℕ)

def step (l : SAT.Literal (Fin n)) (acc : List (Product.Entry n (baseWidth p t) d)) :=
  LiteralCallback.result p t M cache table minusOne one (incidence l.variable) acc u J l.positive

end SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Clause

namespace SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Row
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open MomentsProgram

variable (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
variable (cache : RingProgram.ScalarCache p t) {n d : ℕ}
variable (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
variable (minusOne : RingProgram.Code (Word (baseWidth p t)) d)
structure WeightedClause (n B d : ℕ) where
  scalar : RingProgram.Code (Word B) d
  literals : List (SAT.Literal (Fin n))

def literalList {n B d : ℕ} (w : WeightedClause n B d) : List Bool :=
  Encoding.encodeList id (w.literals.map Clause.literalBits)
def payload {n B d : ℕ} (w : WeightedClause n B d) : List Bool :=
  Encoding.frame (RingProgram.flat w.scalar) ++ literalList w

variable (one : List (Product.Entry n (baseWidth p t) d))
variable (incidence : Fin n → List (Product.Entry n (baseWidth p t) d))
variable (u J : ℕ)

def clauseValue (w : WeightedClause n (baseWidth p t) d) :=
  DynamicFold.value (Clause.step p t M cache table minusOne one incidence u J) w.literals one

def value (w : WeightedClause n (baseWidth p t) d) (acc : List (Product.Entry n (baseWidth p t) d)) :=
  Normalize.run p t M cache (Squarefree.ScaleProgram.scaled p t M cache table w.scalar
    (clauseValue p t M cache table minusOne one incidence u J w)) acc

end SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Row

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashCircuitProgramInterpreter
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

attribute [local simp] Fin.addCases Fin.coe_ofNat_eq_mod Fin.ext_iff


/-! Component: HashCircuitProgramLiteralCallback. All public namespaces and APIs are retained. -/


/-! Literal callback with actual lookup, polarity, sparse product, and return.
The represented minus-one and one values are explicit cached inputs. All work
is performed by the fixed native commands wired into the row interpreter. -/
namespace SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.LiteralCallback
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open MomentsProgram

variable (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
variable (cache : RingProgram.ScalarCache p t) {n d : ℕ}
variable (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
variable (minusOne : RingProgram.Code (Word (baseWidth p t)) d)
variable (one payload left : List (Product.Entry n (baseWidth p t) d))

def negateBudget (degree : List Bool) : ℕ :=
  36*(Product.bytes payload).length + 18*(RingProgram.flat minusOne).length +
  7*(Product.bytes one).length + 9*(Product.bytes (negative p t M cache table minusOne one payload)).length +
  9*degree.length + Squarefree.ScaleProgram.budget Squarefree.encodeIndex payload +
  Normalize.work p t M cache Squarefree.encodeIndex
    (Squarefree.ScaleProgram.scaled p t M cache table minusOne payload) one + 73

def budget (degree : List Bool) (u J v : ℕ) (positive : Bool)
    (entries : List (List Bool × List Bool)) : ℕ :=
  8*v+16+literalFetchBudget (Encoding.encodeNat v) entries+9*(Product.bytes payload).length+10 +
  (if positive then negateBudget p t M cache table minusOne one payload degree else 0) + 1 +
  9*(Product.bytes left).length+
  11*(Product.bytes (value p t M cache table minusOne one payload positive)).length+
  9*(Product.bytes (result p t M cache table minusOne one payload left u J positive)).length+
  Product.work p t M cache table u J left (value p t M cache table minusOne one payload positive) []+29+3

end SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.LiteralCallback

/-! Component: HashCircuitProgramClause. All public namespaces and APIs are retained. -/


/-! Typed clause traversal using the fixed native literal callback. Input is
still the original unary literal encoding; the type is used only to specify
which dictionary entry the native decoder and lookup retrieve. -/
namespace SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Clause
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open MomentsProgram

variable (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
variable (cache : RingProgram.ScalarCache p t) {n d : ℕ}
variable (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
variable (minusOne : RingProgram.Code (Word (baseWidth p t)) d)
variable (one : List (Product.Entry n (baseWidth p t) d))
variable (incidence : Fin n → List (Product.Entry n (baseWidth p t) d))
variable (degree : List Bool) (u J : ℕ) (entries : List (List Bool × List Bool))

def cost (l : SAT.Literal (Fin n)) (acc : List (Product.Entry n (baseWidth p t) d)) :=
  LiteralCallback.budget p t M cache table minusOne one (incidence l.variable) acc degree
    u J l.variable.val l.positive entries

end SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Clause

/-! Component: HashCircuitProgramRow. All public namespaces and APIs are retained. -/


/-! The actual nested hash-row interpreter. The only inputs below are serialized
literal clauses, flat represented scalars, the selected incidence dictionary,
and the ring/cache words used by the native services. -/
namespace SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Row
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open MomentsProgram

variable (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
variable (cache : RingProgram.ScalarCache p t) {n d : ℕ}
variable (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
variable (minusOne : RingProgram.Code (Word (baseWidth p t)) d)
variable (one : List (Product.Entry n (baseWidth p t) d))
variable (incidence : Fin n → List (Product.Entry n (baseWidth p t) d))
variable (degree : List Bool) (u J : ℕ) (entries : List (List Bool × List Bool))

def cost (w : WeightedClause n (baseWidth p t) d) (acc : List (Product.Entry n (baseWidth p t) d)) : ℕ :=
  let clause := clauseValue p t M cache table minusOne one incidence u J w
  3*(payload w).length+6*(RingProgram.flat w.scalar).length+8 +
  (7*(Product.bytes one).length+5) +
  (3+DynamicFold.work Clause.literalBits (Clause.step p t M cache table minusOne one incidence u J)
    (Clause.cost p t M cache table minusOne one incidence degree u J entries) w.literals one) +
  (36*(Product.bytes clause).length+14*(RingProgram.flat w.scalar).length+9*(Product.bytes acc).length+
    9*(Product.bytes (value p t M cache table minusOne one incidence u J w acc)).length+9*degree.length+
    Squarefree.ScaleProgram.budget Squarefree.encodeIndex clause+
    Normalize.work p t M cache Squarefree.encodeIndex (Squarefree.ScaleProgram.scaled p t M cache table w.scalar clause) acc+74)+3

end SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Row

/-! Component: HashCircuitProgramRun. All public namespaces and APIs are retained. -/


/-! Compiled fixed-program trace for one serialized sparse hash row. The
initial accumulator is physically cleared, and the final halt is charged. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashInputProgramExpansion
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact bytes and coefficient meaning at the raw-row/interpreter boundary.
The full extension dimension is D; the assembler parameter is D-1. -/
namespace SubexponentialSAT.SqrtLog.HashInputProgram.Expansion
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open HashCircuitProgram.Native
attribute [local simp] Fin.coe_ofNat_eq_mod

def coefficient (t : ℕ) : (D : ℕ) → ZMod 3 → RingProgram.Code (RingProgram.ScalarCode 3 t) D
  | 0, _ => Fin.elim0
  | d+1, c => constantVector t d c

def weightedClause {n : ℕ} (t D : ℕ) (source : List (List (SAT.Literal (Fin n))))
    (term : Fin (encodedClauses source).length × ZMod 3) :
    Row.WeightedClause n (SubexpLiftRing.baseWidth 3 t) D :=
  ⟨coefficient t D term.2,originalClause source term.1⟩

def weightedRow {n : ℕ} (t D : ℕ) (source : List (List (SAT.Literal (Fin n))))
    (terms : List (Fin (encodedClauses source).length × ZMod 3)) :
    List (Row.WeightedClause n (SubexpLiftRing.baseWidth 3 t) D) :=
  terms.map (weightedClause t D source)

@[simp] theorem weightedRow_length {n : ℕ} (t D : ℕ)
    (source : List (List (SAT.Literal (Fin n))))
    (terms : List (Fin (encodedClauses source).length × ZMod 3)) :
    (weightedRow t D source terms).length=terms.length := by simp [weightedRow]

end SubexponentialSAT.SqrtLog.HashInputProgram.Expansion

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

/-- Exact callback count and exact controller overhead, including the final
empty pop and false guard. -/
theorem Visits.bounds {p : Ports R S} {body : StructuredCalls.Cmd R S}
    {costs : List ℕ} {n : ℕ} {d e : Data R S} (h : Visits p body costs n d e) :
    costs.length = (d.stacks p.counter).length ∧ e.stacks p.counter = [] ∧
      n = costs.sum + 2 * costs.length + 2 := by
  induction h with
  | done d he => simp [he]
  | @step d e f nb nt costs hne hb hc ht ih =>
      rcases ih with ⟨hlen, hempty, htime⟩
      have hw : (e.stacks p.counter).length + 1 = (d.stacks p.counter).length := by
        rw [hc, popped_counter]
        cases hword : d.stacks p.counter with
        | nil => exact False.elim (hne hword)
        | cons b bs => simp
      refine ⟨?_, hempty, ?_⟩
      · simp only [List.length_cons, hlen]
        exact hw
      · simp only [List.sum_cons, List.length_cons]
        omega

end SubexponentialSAT.UnaryForPrograms

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HighIncidenceProgramBranches
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Runtime Boolean branch initialization and exhaustive odometer traces.
The only parameter in the enumeration command is its fixed real callback.
The high dimension is data, not finite control. -/
namespace SubexponentialSAT.SqrtLog.HighIncidenceProgram.Branches
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def push (b : Bool) : Code := .seq (.base (.atom (.set 0 b))) (.base (.atom (.push 1 0)))

def record : Code := .seq (push false) (.seq (push false) (.seq (push true) (push true)))

def pop : Code := .base (.atom (.pop 0 0 1))

def loop : Code := .while 1 (.seq (.ite 0 record (.base .skip)) pop)
def command : Code := .seq (push false) (.seq pop loop)

def program := compiled command 0 1

end SubexponentialSAT.SqrtLog.HighIncidenceProgram.Branches

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HornerProgramServices
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fully discharged native binary services for arbitrary coefficient-vector
length. Shared by Horner, local CRT and dense polynomial services. -/
namespace SubexponentialSAT.SqrtLog.HornerProgram.Services

open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open CRTLocalProgram (ServiceSpec)

/-- Updating the caller's two polynomial caches does not affect scalar service
readiness; all remaining low ports are retained. -/
theorem NativeReady.frame_except_low_caches {p t : ℕ} [Fact p.Prime]
    {M : SubexpPreparedQuartic.Modulus p t} {cache : RingProgram.ScalarCache p t}
    {d : ℕ} {table : Fin d → Fin d → Fin d → Word (baseWidth p t)}
    {base s : Store} (h : NativeReady p t M cache table base)
    (hf : ∀ i : Fin 256, i.val < 205 → i ≠ 192 → i ≠ 193 → s i = base i) :
    NativeReady p t M cache table s := by
  have h194 := hf 194 (by decide) (by decide) (by decide)
  have h201 := hf 201 (by decide) (by decide) (by decide)
  have h202 := hf 202 (by decide) (by decide) (by decide)
  have h203 := hf 203 (by decide) (by decide) (by decide)
  have h204 := hf 204 (by decide) (by decide) (by decide)
  refine ⟨?_, h194.trans h.modulus, ?_, h203.trans h.zero, h201.trans h.table, ?_⟩
  · refine ⟨(hf 120 (by decide) (by decide) (by decide)).trans h.workspace.1, ?_⟩
    intro i
    have h192 : ReconstructionProgram.RingAdapter.ports i ≠ 192 := by
      fin_cases i <;> decide
    have h193 : ReconstructionProgram.RingAdapter.ports i ≠ 193 := by
      fin_cases i <;> decide
    rw [hf _ (ReconstructionProgram.RingAdapter.ports_low i) h192 h193]
    simpa only [ReconstructionProgram.RingAdapter.finalNative, h194, h201, h202, h203]
      using h.workspace.2 i
  · simpa only [h202] using h.width
  · simpa only [h204] using h.degree

/-- Readiness transports across the standard persistent low-frame relation. -/
theorem NativeReady.frame {p t : ℕ} [Fact p.Prime]
    {M : SubexpPreparedQuartic.Modulus p t} {cache : RingProgram.ScalarCache p t}
    {d : ℕ} {table : Fin d → Fin d → Fin d → Word (baseWidth p t)}
    {base s : Store} (h : NativeReady p t M cache table base)
    (hf : CRTLocalProgram.LowFrame base s) : NativeReady p t M cache table s :=
  h.frame_except_low_caches fun i hi _ _ => hf i hi

end SubexponentialSAT.SqrtLog.HornerProgram.Services

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentApplyProgramStored
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact stored-list specification of the native Horner application. The
operations here are the functional results of the concrete normalized-add
and sparse-product machines, rather than operations on noncomputable jets. -/
namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram

open scoped BigOperators
open SubexpLiftRing SubexpQuarticRing
open MomentsProgram

variable (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {n d : ℕ}

abbrev Stored := List (Product.Entry n (baseWidth p t) d)

def constantStored (word : RingProgram.ScalarCode p t) : Stored p t (n:=n) (d:=d) :=
  [(Squarefree.Index.origin,scalarVector cache.zero word)]

def addStored (a b : Stored p t (n:=n) (d:=d)) : Stored p t (n:=n) (d:=d) :=
  Normalize.run p t M cache a b

def mulStored (table : Fin d → Fin d → Fin d → Word (baseWidth p t)) (uCap J : ℕ)
    (a b : Stored p t (n:=n) (d:=d)) : Stored p t (n:=n) (d:=d) :=
  Product.run p t M cache table uCap J a b []

def tripleStored (table : Fin d → Fin d → Fin d → Word (baseWidth p t)) (uCap J : ℕ)
    (h : Stored p t (n:=n) (d:=d)) (v : Triple (RingProgram.ScalarCode p t)) : Stored p t (n:=n) (d:=d) :=
  addStored p t M cache
    (mulStored p t M cache table uCap J
      (addStored p t M cache
        (mulStored p t M cache table uCap J (constantStored p t cache v.c) h)
        (constantStored p t cache v.b)) h)
    (constantStored p t cache v.a)

def descendingStored (table : Fin d → Fin d → Fin d → Word (baseWidth p t)) (uCap J : ℕ)
    (h g : Stored p t (n:=n) (d:=d)) (vs : List (Triple (RingProgram.ScalarCode p t)))
    (acc : Stored p t (n:=n) (d:=d)) : Stored p t (n:=n) (d:=d) :=
  vs.foldl (fun current v => addStored p t M cache
    (mulStored p t M cache table uCap J current g)
    (tripleStored p t M cache table uCap J h v)) acc

variable {R : Type*} [CommRing R] (φ : ZMod (p^t) →+* R) (basis : Fin d → R)

noncomputable def storedDenote (a : Stored p t (n:=n) (d:=d)) : Squarefree.Jet (Fin n) R :=
  Squarefree.Sparse.denote (MomentsProgram.Dictionary.denoteTable
    (RingProgram.denote (RingProgram.scalarRing p t M cache) φ basis) a)

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentApplyProgramBoundsCapacity
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Finite record capacity for the actual normalized stored lists. The finite
universe is used for counting only; the program never enumerates it. -/
namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Bounds

open SubexpLiftRing SubexpQuarticRing
open MomentsProgram

def Valid {n B d : ℕ} (vars : Finset (Fin n)) (u J : ℕ)
    (entries : List (Product.Entry n B d)) : Prop :=
  ∀ a ∈ entries, Product.ValidKey vars u J a.1

def Good {n B d : ℕ} (vars : Finset (Fin n)) (u J : ℕ)
    (entries : List (Product.Entry n B d)) : Prop :=
  Valid vars u J entries ∧ (Squarefree.Sparse.keys entries).Nodup

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Bounds

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentApplyProgramServices
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native sparse arithmetic services shared by multiplier construction and Horner evaluation. -/
namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps

open BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open HashCircuitProgram.Native
open MomentsProgram

structure Context (p t n d : ℕ) where
  modulus : SubexpPreparedQuartic.Modulus p t
  cache : RingProgram.ScalarCache p t
  zeroBound : BinaryArithmetic.toNat cache.zero.val < p^t
  table : Fin d → Fin d → Fin d → Word (baseWidth p t)
  u : ℕ
  J : ℕ
  width : List Bool
  widthLength : width.length=baseWidth p t

variable {p t n d : ℕ} [Fact p.Prime]

abbrev Raw := List (Product.Entry n (baseWidth p t) d)

def low (c : Context p t n d) : Fin 56 → List Bool :=
  Product.tapes (Product.idle c.modulus.bits c.width c.cache.zero.val
    (RingTriple.tableEncoding c.table) (List.replicate d true)
    (List.replicate c.u true) (List.replicate c.J true))

def constant (c : Context p t n d) (w : RingProgram.ScalarCode p t) : Raw (p:=p) (t:=t) (n:=n) (d:=d) :=
  constantStored p t c.cache w

def mul (c : Context p t n d) (a b : Raw (p:=p) (t:=t) (n:=n) (d:=d)) : Raw (p:=p) (t:=t) (n:=n) (d:=d) :=
  mulStored p t c.modulus c.cache c.table c.u c.J a b

def plus (c : Context p t n d) (a b : Raw (p:=p) (t:=t) (n:=n) (d:=d)) : Raw (p:=p) (t:=t) (n:=n) (d:=d) :=
  addStored p t c.modulus c.cache a b

def mulCost (c : Context p t n d) (a b : Raw (p:=p) (t:=t) (n:=n) (d:=d)) : ℕ :=
  9*(Product.bytes a).length+11*(Product.bytes b).length+
    9*(Product.bytes (mul c a b)).length+
    Product.work p t c.modulus c.cache c.table c.u c.J a b []+29

def addCost (c : Context p t n d) (a b : Raw (p:=p) (t:=t) (n:=n) (d:=d)) : ℕ :=
  18*(Product.bytes a).length+9*(Product.bytes b).length+
    9*(Product.bytes (plus c a b)).length+9*d+
    Normalize.work p t c.modulus c.cache Squarefree.encodeIndex a b+43


end SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentApplyProgramExecution
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


/-! Native high-register services for the quadratic and Horner steps. -/


/-! Complete native evaluation of one degree-two coefficient digit. -/
namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps

open BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open HashCircuitProgram.Native
open MomentsProgram

variable {p t n d : ℕ} [Fact p.Prime]

def quadraticCost (ctx : Context p t n d) (h : Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (v : Triple (RingProgram.ScalarCode p t)) : ℕ :=
  let ch:=mul ctx (constant ctx v.c) h
  let chb:=plus ctx ch (constant ctx v.b)
  let chbh:=mul ctx chb h
  3*ReadScalar.wordCost (baseWidth p t) d n +
    2*(7*(Product.bytes h).length+5)+
    mulCost ctx (constant ctx v.c) h+addCost ctx ch (constant ctx v.b)+
    mulCost ctx chb h+addCost ctx chbh (constant ctx v.a)

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps


/-! The native Horner accumulator update, including every move and cleanup. -/
namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps

open BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open HashCircuitProgram.Native
open MomentsProgram

variable {p t n d : ℕ} [Fact p.Prime]

def accumulatorCost (ctx : Context p t n d)
    (e a g : Raw (p:=p) (t:=t) (n:=n) (d:=d)) : ℕ :=
  let ag:=mul ctx a g
  let out:=plus ctx ag e
  18*(Product.bytes e).length+9*(Product.bytes a).length+
    7*(Product.bytes g).length+9*(Product.bytes out).length+37+
      mulCost ctx a g+addCost ctx ag e

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps


/-! Measured descending Horner loop over the actual computed coefficient tape. -/
namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps

open BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open HashCircuitProgram.Native
open MomentsProgram

variable {p t n d : ℕ} [Fact p.Prime]

def loopResult (ctx : Context p t n d) (h g : Raw (p:=p) (t:=t) (n:=n) (d:=d)) :
    List (Triple (RingProgram.ScalarCode p t)) → Raw (p:=p) (t:=t) (n:=n) (d:=d) → Raw (p:=p) (t:=t) (n:=n) (d:=d)
  | [],a => a
  | v::vs,a => loopResult ctx h g vs
      (plus ctx (mul ctx a g) (tripleStored p t ctx.modulus ctx.cache ctx.table ctx.u ctx.J h v))

def loopCost (ctx : Context p t n d) (h g : Raw (p:=p) (t:=t) (n:=n) (d:=d)) :
    List (Triple (RingProgram.ScalarCode p t)) → Raw (p:=p) (t:=t) (n:=n) (d:=d) → ℕ
  | [],_ => 1
  | v::vs,a =>
      let e:=tripleStored p t ctx.modulus ctx.cache ctx.table ctx.u ctx.J h v
      quadraticCost ctx h v+accumulatorCost ctx e a g+2+
        loopCost ctx h g vs (plus ctx (mul ctx a g) e)

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps

namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps

open BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open HashCircuitProgram.Native
open MomentsProgram

variable {p t n d : ℕ} [Fact p.Prime]

def applyLoopCost (ctx : Context p t n d) (h g : Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (vs : List (Triple (RingProgram.ScalarCode p t))) (key : List Bool) : ℕ :=
  10*(triplesTape vs).length+
    9*(Product.bytes (loopResult ctx h g vs.reverse [])).length+
    2*(Product.bytes g).length+2*key.length+23+loopCost ctx h g vs.reverse []

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentApplyProgramBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed polynomial envelopes for the concrete degree-two coefficient and
Horner machines. Every byte copy, dictionary scan, product and tape reversal
in the native cost definitions is charged. -/
namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Bounds

open SubexpLiftRing SubexpQuarticRing
open MomentsProgram
open Steps

variable {p t n d : ℕ} [Fact p.Prime]

def Bounded (ctx : Context p t n d) (vars : Finset (Fin n))
    (a : Stored p t (n:=n) (d:=d)) : Prop :=
  Valid vars ctx.u ctx.J a ∧ a.length ≤ capacity vars ctx.u ctx.J

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Bounds

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentApplyProgramMultiplierKernel
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Source component: IdempotentApplyProgramMultiplierArithmetic. -/

/-! Native construction of the cubic multiplier before its U shift. -/
namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Multiplier
open BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open HashCircuitProgram.Native
open MomentsProgram
open Steps

variable {p t n d : ℕ} [Fact p.Prime]

def complemented (c : Context p t n d) (minus : RingProgram.Code (Word (baseWidth p t)) d)
    (h one : Raw (p:=p) (t:=t) (n:=n) (d:=d)) : Raw (p:=p) (t:=t) (n:=n) (d:=d) :=
  Normalize.run p t c.modulus c.cache
    (Squarefree.ScaleProgram.scaled p t c.modulus c.cache c.table minus h) one

def complementCost (c : Context p t n d) (minus : RingProgram.Code (Word (baseWidth p t)) d)
    (h one : Raw (p:=p) (t:=t) (n:=n) (d:=d)) : ℕ :=
  36*(Product.bytes h).length+18*(RingProgram.flat minus).length+
    7*(Product.bytes one).length+9*(Product.bytes (complemented c minus h one)).length+9*d+
    Squarefree.ScaleProgram.budget Squarefree.encodeIndex h+
    Normalize.work p t c.modulus c.cache Squarefree.encodeIndex
      (Squarefree.ScaleProgram.scaled p t c.modulus c.cache c.table minus h) one+73

def cubic (c : Context p t n d) (minus : RingProgram.Code (Word (baseWidth p t)) d)
    (h one : Raw (p:=p) (t:=t) (n:=n) (d:=d)) : Raw (p:=p) (t:=t) (n:=n) (d:=d) :=
  let a:=complemented c minus h one
  mul c (mul c (plus c a one) a) h

def arithmeticCost (c : Context p t n d) (minus : RingProgram.Code (Word (baseWidth p t)) d)
    (h one : Raw (p:=p) (t:=t) (n:=n) (d:=d)) : ℕ :=
  let a:=complemented c minus h one
  let b:=plus c a one
  let q:=mul c b a
  (7*(Product.bytes h).length+5)+complementCost c minus h one+
  (7*(Product.bytes a).length+5)+(7*(Product.bytes a).length+5)+
  (2*(Product.bytes a).length+3)+(7*(Product.bytes one).length+5)+addCost c a one+
  (7*(Product.bytes a).length+5)+mulCost c b a+(2*(Product.bytes a).length+3)+
  (7*(Product.bytes h).length+5)+mulCost c q h

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Multiplier

/-! Source component: IdempotentApplyProgramMultiplier. -/

/-! Concrete preparation of the stored multiplier used by native Horner evaluation. -/
namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Multiplier
open BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open HashCircuitProgram.Native
open MomentsProgram
open Steps

variable {p t n d : ℕ} [Fact p.Prime]

def byteEntries (xs : Raw (p:=p) (t:=t) (n:=n) (d:=d)) :
    List (Squarefree.KeyMapProgram.Entry n) := xs.map fun e => (e.1,RingProgram.flat e.2)

def shiftForward (a : Squarefree.Index (Fin n)) (u J : ℕ) :
    Raw (p:=p) (t:=t) (n:=n) (d:=d) → Raw (p:=p) (t:=t) (n:=n) (d:=d)
  | [] => []
  | (b,c)::rest => if (a.join b).Kept u J then (a.join b,c)::shiftForward a u J rest
      else shiftForward a u J rest

def shifted (c : Context p t n d) (xs : Raw (p:=p) (t:=t) (n:=n) (d:=d)) : Raw (p:=p) (t:=t) (n:=n) (d:=d) :=
  (shiftForward (uKey n) c.u c.J xs).reverse

def prepared (c : Context p t n d) (minus : RingProgram.Code (Word (baseWidth p t)) d)
    (h one : Raw (p:=p) (t:=t) (n:=n) (d:=d)) : Raw (p:=p) (t:=t) (n:=n) (d:=d) := shifted c (cubic c minus h one)

def prepareCost (c : Context p t n d) (minus : RingProgram.Code (Word (baseWidth p t)) d)
    (h one : Raw (p:=p) (t:=t) (n:=n) (d:=d)) : ℕ :=
  arithmeticCost c minus h one+20*n+50+
    Squarefree.KeyMapProgram.budget (uKey n) c.u c.J (byteEntries (cubic c minus h one))+2

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Multiplier

/-! Source component: IdempotentApplyProgramMultiplierSemantics. -/

/-! The multiplier produced by the native preparation is U H(H-1)(H-2). -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentApplyProgramFinal
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Full native application of a computed idempotent coefficient array.
The multiplier is built from H and ordinary cached constants; the indicator
is then computed by the measured Horner loop. -/
namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram

open scoped BigOperators
open BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open HashCircuitProgram.Native
open MomentsProgram
open Steps

variable {p t n d : ℕ} [Fact p.Prime]

def applied (ctx : Context p t n d) (minus : RingProgram.Code (Word (baseWidth p t)) d)
    (h one : Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (vs : List (Triple (RingProgram.ScalarCode p t))) : Raw (p:=p) (t:=t) (n:=n) (d:=d) :=
  loopResult ctx h (Multiplier.prepared ctx minus h one) vs.reverse []

def applicationBudget (ctx : Context p t n d)
    (minus : RingProgram.Code (Word (baseWidth p t)) d)
    (h one : Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (vs : List (Triple (RingProgram.ScalarCode p t))) : ℕ :=
  Multiplier.prepareCost ctx minus h one+
    applyLoopCost ctx h (Multiplier.prepared ctx minus h one) vs
      (Squarefree.encodeIndex (Multiplier.uKey n))+1

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentPreparationProgramScalarMachine
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed register language for the twelve scalar cache/temporary words.
Its interpreter is actual finite code, not a unit-cost arithmetic oracle. -/
namespace SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar
open BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing ModularRingPrograms

variable (p t : ℕ) [Fact p.Prime]

theorem sequence_eval (M : SubexpPreparedQuartic.Modulus p t) (ops : List Op)
    (v : Values p t) (d : Data) (h : Encoded p t M v d) :
    ∃ n e, Eval (sequence ops) n d e ∧ Encoded p t M (run p t M ops v) e ∧
      Frame d e ∧ n ≤ ops.length * stepBudget p t := by
  induction ops generalizing v d with
  | nil => exact ⟨0,d,.base (.skip _),h,fun _ _=>rfl,by simp⟩
  | cons a as ih =>
      obtain ⟨na,da,ha,hva,hfa,hna⟩:=a.command_eval p t M v d h
      obtain ⟨nb,db,hb,hvb,hfb,hnb⟩:=ih _ da hva
      refine ⟨na+nb,db,ha.seq hb,hvb,?_,?_⟩
      · intro j hj; exact (hfb j hj).trans (hfa j hj)
      · simp only [List.length_cons]; nlinarith

def iterateForward (M : SubexpPreparedQuartic.Modulus p t) (v : Values p t) : ℕ → Values p t
  | 0 => v
  | n+1 => run p t M halfStep (iterateForward M v n)

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentPreparationProgramScalarRun
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar
open BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing

/-- Every operation and loop bound is read from the runtime stacks. -/
abbrev arithmeticCommand : Cmd 8 41 :=
  .seq (sequence constants) <|
  .seq (ArithmeticCalls.copyAt 29 40 38) <|
  .seq halfLoop <|
  .seq (sequence finalCoefficients) <|
  .seq (IdempotentProgram.registerClear 24) (IdempotentProgram.registerClear 25)

def finalValues (t:ℕ) (M:SubexpPreparedQuartic.Modulus 3 t) (v:Values 3 t) : Values 3 t :=
  run 3 t M finalCoefficients (iterateForward 3 t M (run 3 t M constants v) t)

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_InterpolationCacheProgramScan
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed-width physical map scan. The service is an ordinary finite
subprogram, and its output is transferred into the actual packed table. -/
namespace SubexponentialSAT.SqrtLog.InterpolationCacheProgram
open SubexponentialSAT BitProgram StructuredCalls StackRoutines

def seq_p2 (a b : Code) : Code := .seq a b

end SubexponentialSAT.SqrtLog.InterpolationCacheProgram

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

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Layout

open BitProgram StructuredCalls BinaryArithmetic Bank Circuit

/-- Low eight slots hold ambient n, residual n, original clause count, actual
occurrence bound, maximum arity, full factor count (hash+marked+neutral),
formula width, and total incidences.
The remaining finite table is straight-line syntax, not an input oracle. -/
abbrev earlyCode : List Instr := [
  .load 8 [false,true],
  .load 9 [true,true],
  .load 10 [false,false,false,false,false,true],
  .load 11 [false,false,false,false,false,false,true],
  .load 12 [false,false,false,false,false,false,false,true],
  .copy 1 13 (by decide), .addConst 13 16, .logSucc 13,
  .copy 13 14 (by decide), .logSucc 14,
  .mul 14 14 15 (by decide) (by decide),
  .sqrt 13 16 (by decide),
  .quot 16 15 17 (by decide) (by decide),
  .copy 17 18 (by decide), .maxTwo 18]

abbrev quotientCode : List Instr := [
  .copy 18 19 (by decide), .logSucc 19,
  .mul 11 19 20 (by decide) (by decide),
  .quot 13 20 21 (by decide) (by decide)]

abbrev prefixCode : List Instr := earlyCode ++ quotientCode

abbrev heavyCode : List Instr := [
  .mul 13 13 22 (by decide) (by decide),
  .mul 3 18 23 (by decide) (by decide),
  .mul 23 22 24 (by decide) (by decide),
  .mul 10 24 25 (by decide) (by decide),
  .mul 11 24 26 (by decide) (by decide), .logSucc 26,
  .mul 12 21 27 (by decide) (by decide),
  .mul 27 26 28 (by decide) (by decide),
  .sqrt 28 29 (by decide), .addConst 29 4]

abbrev finishCode : List Instr := heavyCode ++ powerCode

def coreCode : List Instr := prefixCode ++ finishCode

def tailCode : List Instr := [
  .copy 2 32 (by decide), .logSucc 32, .addConst 32 1,
  .add 0 32 33 (by decide) (by decide),
  .copy 21 34 (by decide), .logSucc 34, .addConst 34 1,
  .pow 9 34 35 (by decide) (by decide),
  .copy 33 36 (by decide), .pred 36,
  .mul 9 36 37 (by decide) (by decide),
  .mul 8 5 38 (by decide) (by decide),
  .add 38 37 39 (by decide) (by decide), .addConst 39 1,
  .mul 6 29 40 (by decide) (by decide),
  .mul 40 39 41 (by decide) (by decide),
  .copy 21 43 (by decide), .pred 43, .addConst 43 1,
  .quot 41 43 42 (by decide) (by decide), .addConst 42 1]

def code : List Instr := coreCode ++ tailCode

def initialModel (x : Input) (inputLengths : Fin 8 → ℕ) : Model where
  val := initialValues x
  len i := if h : i.val < 8 then inputLengths ⟨i.val,h⟩ else 0

def model (x : Input) (inputLengths : Fin 8 → ℕ) : Model :=
  Circuit.result code (initialModel x inputLengths)

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Layout


/- Component: SubexponentialSAT.SqrtLog.LeafParametersProgramLayoutReady -/


namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.GuardSetup

open BitProgram StructuredCalls BinaryArithmetic Bank Circuit

/-- Materialize the twenty comparison operands. Public parameter slots and
all eight original metadata words are preserved. Reused private slots are
cleared by real stack programs before each new arithmetic result. -/
def preparation : List Instr := [
  .clear 8,
  .load 8 [true],
  .clear 9,
  .load 9 [false,true],
  .clear 10,
  .load 10 [false,false,true],
  .clear 11,
  .load 11 [false,false,false,false,true],
  .clear 12,
  .mul 31 31 12 (by decide) (by decide),
  .clear 15,
  .mul 25 25 15 (by decide) (by decide),
  .clear 16,
  .add 3 4 16 (by decide) (by decide),
  .clear 19,
  .mul 10 16 19 (by decide) (by decide),
  .clear 20,
  .mul 19 12 20 (by decide) (by decide),
  .clear 22,
  .mul 20 15 22 (by decide) (by decide),
  .clear 23,
  .mul 18 18 23 (by decide) (by decide),
  .clear 24,
  .mul 21 23 24 (by decide) (by decide),
  .clear 26,
  .mul 11 24 26 (by decide) (by decide),
  .clear 27,
  .mul 10 29 27 (by decide) (by decide)]

def emissions : List Instr := [
  .clear 44,
  .copy 1 44 (by decide),
  .clear 45,
  .copy 8 45 (by decide),
  .clear 46,
  .copy 0 46 (by decide),
  .clear 47,
  .copy 1 47 (by decide),
  .clear 48,
  .copy 2 48 (by decide),
  .clear 49,
  .copy 8 49 (by decide),
  .clear 50,
  .copy 3 50 (by decide),
  .clear 51,
  .copy 8 51 (by decide),
  .clear 52,
  .copy 4 52 (by decide),
  .clear 53,
  .copy 8 53 (by decide),
  .clear 54,
  .copy 7 54 (by decide),
  .clear 55,
  .copy 1 55 (by decide),
  .clear 56,
  .copy 21 56 (by decide),
  .clear 57,
  .copy 9 57 (by decide),
  .clear 58,
  .copy 21 58 (by decide),
  .clear 59,
  .copy 27 59 (by decide),
  .clear 60,
  .copy 7 60 (by decide),
  .clear 61,
  .copy 22 61 (by decide),
  .clear 62,
  .copy 1 62 (by decide),
  .clear 63,
  .copy 26 63 (by decide)]

def code : List Instr := preparation ++ emissions

end SubexponentialSAT.SqrtLog.LeafParametersProgram.GuardSetup


/- Component: SubexponentialSAT.SqrtLog.LeafParametersProgramPrepared -/

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Prepared

open BitProgram StructuredCalls BinaryArithmetic Bank Circuit

def code := Layout.code++GuardSetup.code

abbrev command : Cmd 8 77 := Circuit.program code

def finalModel (x : Input) (l : Fin 8 → ℕ) :=
  Circuit.result GuardSetup.code (Layout.model x l)

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Prepared


/- Component: SubexponentialSAT.SqrtLog.LeafParametersProgramExecute -/


end OAI.Algorithms
end


