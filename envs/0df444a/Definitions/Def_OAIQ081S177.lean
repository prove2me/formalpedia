-- Prove2me | Definitions.Def_OAIQ081S177
-- name    : OAIQ081S177
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T23:24:26.762165+00:00
-- url     : https://prove2.me/theorems/6c01f83e-7bfb-4434-800c-6820f2ce8d44
-- title:
--   Definitions bundle OAIQ081S177 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 15 declarations of OpenAI's Lean: 5 definitions and 10 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.sourceRowProperty`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryRank.queryLabelRows`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback.fetched`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamCorrect.finishBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamCorrect.nodeSpace`.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: [`SubexponentialSAT_SqrtLogSpace_FactorAssignmentCallbackNative`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/FactorAssignmentCallbackNative.lean), [`SubexponentialSAT_SqrtLogSpace_QueryStreamCorrect`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryStreamCorrect.lean), [`SubexponentialSAT_SqrtLog_PackingIncidenceInputLoose`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/PackingIncidenceInputLoose.lean), [`SubexponentialSAT_SqrtLog_PackingLoaderProgramCore`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/PackingLoaderProgramCore.lean), [`SubexponentialSAT_SqrtLog_PackingPrefixProgramLift`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/PackingPrefixProgramLift.lean), [`SubexponentialSAT_SqrtLog_PackingPrefixProgramRun`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/PackingPrefixProgramRun.lean), [`SubexponentialSAT_SqrtLog_PackingProgramAssemblyHeadSetup`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/PackingProgramAssemblyHeadSetup.lean), [`SubexponentialSAT_SqrtLog_PackingProgramAssemblyHeads`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/PackingProgramAssemblyHeads.lean), [`SubexponentialSAT_SqrtLog_PerturbationAssemblySource`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/PerturbationAssemblySource.lean), [`SubexponentialSAT_SqrtLog_ProducedQueryRankSchedule`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/ProducedQueryRankSchedule.lean), [`SubexponentialSAT_Subexp_AssignmentInputProgram`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/Subexp/AssignmentInputProgram.lean).
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S168`, `OAIQ081S169`, `OAIQ081S171` and `OAIQ081S172` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S183`, `OAIQ081S184` and `OAIQ081S185`; the statements `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback.Input.payload_correct` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback.Input.staged_factorJet`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback.Input.staged_factorJet` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryResources.rank_budget`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S168
import Definitions.Def_OAIQ081S169
import Definitions.Def_OAIQ081S171
import Definitions.Def_OAIQ081S172

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationAssemblySource
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Closed source-to-incidence preparation. All source rows are produced by
the actual finite source program; its contract is derived from physical
metadata and arithmetic input conditions, never a supplied polynomial table. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT BitProgram StructuredCalls DensePolynomialProgram SubexpLiftRing
open SubexponentialSAT.Subexp.ConstructivePacking SubexponentialSAT.MulticolorTypes LayoutProgram
open LayoutSourceRowsProgram

/-- The full coefficient polynomial of the actual selected factor/literal,
including the zero source for a missing incidence. -/
def sourceRowProperty {r Q d : ℕ} (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (n f j : ℕ) (rows : List (Fixed.Array (baseWidth 3 p.t) d (p.R+1))) : Prop :=
  RowProperty Fixed.encode
    (fun v out => PolynomialExecutorProgram.meaning p.ops out.val =
      sourceRowFamily ps n f j (totalPackedSource p P) v)
    ((p.R+1)*(d*baseWidth 3 p.t)) 0 rows

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorAssignmentCallbackNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete physical inputs for the streamed factor callback. The source
context is the actual q.ctx, and the dispatcher determines every selected row
and clause. These predicates contain stored words and finite size bounds only.
Their construction from the actual loader/cache run remains an integration step. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback
open OAI BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open SqrtLog SqrtLog.LeafProgram HashCircuitProgram HashCircuitProgram.Native
open IdempotentApplyProgram.Steps MomentsProgram NativeSemantics
open FactorAssignmentProgram
open Subexp.ConstructivePacking MulticolorTypes LayoutProgram DensePolynomialProgram

noncomputable section

/-- Exact selected-payload state produced by the concrete dispatcher. -/
def fetched {r Q n d : ℕ} (q : Factor.Spec r Q n d)
    (a : FactorAssignmentProgram.Data) (f : ℕ) (rf : Fin 8 → Bool) :
    FactorAssignmentProgram.Data := dispatched a rf q.rawRows q.clauses q.marked q.mark f

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_AssignmentInputProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Physical input construction for sequential type assignment

All parameters are unary stack data. The fixed program constructs the one-hot
word alphabet, reads its actual first word, derives its packed view, and builds
the exact seed range and dimensions expected by `AssignmentInitProgram`.
-/

namespace SubexponentialSAT.Subexp.AssignmentInputProgram

open BitProgram StructuredCalls SubexpSetupStorage AssignmentInputCall

/-- The complete fixed producer, including concrete record extraction and
range generation. The only semantic witness chooses names for the actual
emitted word bytes; it is not supplied to the executable program. -/
theorem command_eval_measured (regs : Fin 16 → Bool) (r Q delta D E B : ℕ)
    (pairs : List Bool) (hr : 0 < r) (hB : 1 ≤ B)
    (ha : Within (inputState regs r Q delta D E pairs) B)
    (hcolor : (ProgramEncoding.encodeRecords (OneHotAlphabetProgram.rows 0 r)).length ≤ B)
    (hwords : (ProgramEncoding.encodeRecords (AssignmentAlphabetSemantics.wordBytes r Q)).length ≤ B)
    (hfirst : ((AssignmentAlphabetSemantics.wordBytes r Q).headD []).length ≤ B)
    (hflat : (AssignmentAlphabetSemantics.wordBytes r Q).flatten.length ≤ B)
    (hwidth : Q * r ≤ B) (hdelta : delta + 1 ≤ B) (hdepth : 2 * (delta + 1) ≤ B)
    (hseed : seedCount delta D E ≤ B)
    (hseeds : (AssignmentSeedRange.seedRecords (seedCount delta D E)).length ≤ B) :
    ∃ ticks, ticks ≤ sourceBudget r Q delta D E B ∧
      Eval command ticks (inputState regs r Q delta D E pairs)
      (outputState r Q delta D E pairs) := by
  let a := inputState regs r Q delta D E pairs
  obtain ⟨t1, a1, he1, hs1, hc1, ht1⟩ := colorAlphabet_eval a r (input_clean regs r Q delta D E pairs) rfl
  have hb1 := within_of_update a a1 7 _ B ha hcolor hs1
  have hn1 := ht1 B ha hcolor hB
  obtain ⟨t2, a2, he2, hs2, hc2, ht2⟩ := wordAlphabet_eval a1 r Q hc1
    (by simp [hs1]) (by simp [hs1, a, inputState])
  have hb2 := within_of_update a1 a2 30 _ B hb1 hwords hs2
  have hn2 := ht2 B hb1 hwords hB
  obtain ⟨w, tail, hw, _, _⟩ := AssignmentAlphabetSemantics.wordBytes_order hr Q
  have hbytes : AssignmentAlphabetSemantics.wordBytes r Q =
      ReadPlan.encodeWord w :: tail.map ReadPlan.encodeWord := hw.symm
  have hhead : (AssignmentAlphabetSemantics.wordBytes r Q).headD [] = ReadPlan.encodeWord w := by
    simp [hbytes]
  have hwlen : (ReadPlan.encodeWord w).length ≤ B := by simpa [hbytes] using hfirst
  obtain ⟨t3, a3, he3, hs3, hc3, ht3⟩ := firstWord_eval a2 (ReadPlan.encodeWord w)
    (tail.map ReadPlan.encodeWord) hc2 (by simp [hs2, hbytes])
  have hb3 := within_of_update a2 a3 0 _ B hb2 hwlen hs3
  have hn3 := ht3 B hb2 hwlen hB
  obtain ⟨t4, a4, he4, hs4, hc4, ht4⟩ := packedAlphabet_eval a3
    (AssignmentAlphabetSemantics.wordBytes r Q) hc3 (by simp [hs3, hs2])
  have hb4 := within_of_update a3 a4 9 _ B hb3 hflat hs4
  have hn4 := ht4 B hb3 hflat hB
  have hwlen' : (unary (Q * r)).length ≤ B := by simpa using hwidth
  obtain ⟨t5, a5, he5, hs5, hc5, ht5⟩ := repeat_eval a4 1 2 10 r Q hc4
    (by simp [hs4, hs3, hs2, hs1, a, inputState])
    (by simp [hs4, hs3, hs2, hs1, a, inputState])
    (by decide) (by decide) (by simp) (by decide)
  have hb5 := within_of_update a4 a5 10 _ B hb4 hwlen' hs5
  have hn5 := ht5 B hb4 hwlen' hB
  have hdlen : (unary (delta + 1)).length ≤ B := by simpa using hdelta
  obtain ⟨t6, a6, he6, hs6, hc6, ht6⟩ := deltaPlusOne_eval a5 delta hc5
    (by simp [hs5, hs4, hs3, hs2, hs1, a, inputState])
    (by simp [hs5, hs4, hs3, hs2, hs1, a, inputState])
  have hb6 := within_of_update a5 a6 6 _ B hb5 hdlen hs6
  have hn6 := ht6 B hb5 hdlen hB
  have hdepthlen : (unary (2 * (delta + 1))).length ≤ B := by simpa using hdepth
  obtain ⟨t7, a7, he7, hs7, hc7, ht7⟩ := depth_eval a6 (delta + 1) hc6
    (by simp [hs6]) (by simp [hs6, hs5, hs4, hs3, hs2, hs1, a, inputState])
  have hb7 := within_of_update a6 a7 34 _ B hb6 hdepthlen hs7
  have hn7 := ht7 B hb6 hdepthlen hB
  have hseedlen : (unary (seedCount delta D E)).length ≤ B := by simpa using hseed
  obtain ⟨t8, a8, he8, hs8, hc8, ht8⟩ := seedSize_eval a7 delta D E hc7
    (by simp [hs7, hs6, hs5, hs4, hs3, hs2, hs1, a, inputState])
    (by simp [hs7, hs6])
    (by simp [hs7, hs6, hs5, hs4, hs3, hs2, hs1, a, inputState])
  have hb8 := within_of_update a7 a8 47 _ B hb7 hseedlen hs8
  have hn8 := ht8 B hb7 hseedlen hB
  obtain ⟨t9, a9, he9, hs9, _, ht9⟩ := seedRange_eval a8 (seedCount delta D E) hc8 (by simp [hs8])
  have hb9 := within_of_update a8 a9 46 _ B hb8 hseeds hs9
  have hn9 := ht9 B hb8 hseeds hB
  let ac := clearManyState [1, 2, 3, 4, 5, 6, 7] a9
  let af := resetManyState (List.finRange 16) ac
  have he10 := (clearMany_eval [1, 2, 3, 4, 5, 6, 7] a9).seq
    (resetMany_eval (List.finRange 16) ac)
  have haf : af = outputState r Q delta D E pairs := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext j
      change (resetManyState (List.finRange 16) ac).regs j = false
      rw [resetMany_regs]
      simp
    · funext j
      change (resetManyState (List.finRange 16) ac).stacks j = _
      rw [resetMany_stacks]
      change (clearManyState [1, 2, 3, 4, 5, 6, 7] a9).stacks j = _
      rw [clearMany_stacks]
      fin_cases j <;> simp [hs9, hs8, hs7, hs6, hs5, hs4, hs3, hs2, hs1, a,
        inputState,
        context, hbytes, AssignmentInitProgram.unary]
  change Eval cleanup _ a9 af at he10
  rw [haf] at he10
  refine ⟨_, ?_, he1.seq (he2.seq (he3.seq (he4.seq (he5.seq (he6.seq (he7.seq
    (he8.seq (he9.seq he10))))))))⟩
  have hcleanup := (clearMany_bound [1, 2, 3, 4, 5, 6, 7] a9 B hb9).2
  simp only [List.length_cons, List.length_nil, List.length_finRange] at hcleanup ⊢
  simp only [sourceBudget, sourceCharge, hhead]
  omega

theorem command_eval (regs : Fin 16 → Bool) (r Q delta D E : ℕ)
    (pairs : List Bool) (hr : 0 < r) :
    ∃ ticks, ticks ≤ budget r Q delta D E pairs ∧
      Eval command ticks (inputState regs r Q delta D E pairs)
        (outputState r Q delta D E pairs) := by
  apply command_eval_measured regs r Q delta D E (extent r Q delta D E pairs) pairs hr
  · dsimp only [extent]
    omega
  · intro j
    dsimp only [inputState]
    split_ifs <;> (try simp only [List.length_replicate, List.length_nil]) <;>
      dsimp only [extent] <;> omega
  all_goals dsimp only [extent]; omega

theorem program_runsIn (regs : Fin 16 → Bool) (r Q delta D E : ℕ)
    (pairs : List Bool) (hr : 0 < r) :
    RunsIn program (budget r Q delta D E pairs + 1)
      ((inputState regs r Q delta D E pairs).withPC (some program.entry))
      ((outputState r Q delta D E pairs).withPC none) := by
  obtain ⟨ticks, hbound, ht⟩ := command_eval regs r Q delta D E pairs hr
  exact ⟨ticks + 1, Nat.add_le_add_right hbound 1, compiled_halt_trace ht 1 30⟩

end SubexponentialSAT.Subexp.AssignmentInputProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingLoaderProgramCore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native alphabet/seed construction followed by actual assignment copying.
The old producer is used at delta=0 so the seed count is exactly ambient+factors;
the new scorer's four-word depth is installed separately. -/
namespace SubexponentialSAT.SqrtLog.PackingLoaderProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

/-- Actual generation from numeric parameters and the installed raw pair
bytes. No alphabet, seed list, or initialized assignment is an input. -/
theorem core_eval (outside : Store) (regs : Fin 16 → Bool)
    (r Q n f : ℕ) (pairs : List Bool) (hr : 0 < r) :
    ∃ t ≤ coreBudget r Q n f pairs, Eval core t
      (framed outside (AssignmentInputProgram.inputState regs r Q 0 n f pairs))
      (framed outside (AssignmentInitProgram.outputState (context r Q n f pairs))) := by
  obtain ⟨t,ht,he⟩ := AssignmentInputProgram.program_runsIn regs r Q 0 n f pairs hr
  have h1 := framed_call AssignmentInputProgram.program outside he
  have h2 := framed_call AssignmentInitProgram.program outside
    (AssignmentInitProgram.program_trace (context r Q n f pairs) (fun _ => false))
  exact ⟨t+AssignmentInitProgram.sourceCost (context r Q n f pairs),
    Nat.add_le_add_right ht _, h1.seq h2⟩

end SubexponentialSAT.SqrtLog.PackingLoaderProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingPrefixProgramRun
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PackingPrefixProgram

open SubexponentialSAT BitProgram StructuredCalls
open SubexponentialSAT.Subexp

theorem command_eval (regs : Fin 3 → Bool) (table count width : List Bool)
    (henough : count.length * width.length ≤ table.length) :
    ∃ n ≤ budget count.length width.length, ∃ regs',
      Eval command n (input regs table count width) (output regs' table count width) := by
  let a := input regs table count width
  let a1 := copied 1 5 a
  let a2 := afterNormalize 4 a1
  let a3 := copied 2 5 a2
  let a4 := afterNormalize 8 a3
  let a5 := copied 4 5 a4
  have h1 : Eval (copy 1 5) (7 * count.length + 5) a a1 :=
    copy_eval 1 5 a (by decide) (by decide) (by decide) rfl
  have hc1 : a1.stacks 5 = count := by simp [a1, a, copied, input, StackRoutines.copyStacks]
  have h2 := normalize_eval 4 (by decide) a1
  rw [hc1] at h2
  have ht2 : a2.stacks 7 = [] := by
    simp [a2, a1, a, afterNormalize, copied, input, StackRoutines.copyStacks]
  have hw2 : a2.stacks 2 = width := by
    simp [a2, a1, a, afterNormalize, copied, input, StackRoutines.copyStacks]
  have h3 := copy_eval 2 5 a2 (by decide) (by decide) (by decide) ht2
  rw [hw2] at h3
  have hw3 : a3.stacks 5 = width := by
    simp [a3, a2, a1, a, afterNormalize, copied, input, StackRoutines.copyStacks]
  have h4 := normalize_eval 8 (by decide) a3
  rw [hw3] at h4
  have ht4 : a4.stacks 7 = [] := by
    simp [a4, a3, a2, a1, a, afterNormalize, copied, input, StackRoutines.copyStacks]
  have hh4 : a4.stacks 4 = unary count.length := by
    simp [a4, a3, a2, a1, a, afterNormalize, copied, input, StackRoutines.copyStacks, unary]
  have h5 := copy_eval 4 5 a4 (by decide) (by decide) (by decide) ht4
  rw [hh4, List.length_replicate] at h5
  have hmW : a5.stacks 8 = unary width.length := by
    simp [a5, a4, a3, a2, a1, a, afterNormalize, copied, input, StackRoutines.copyStacks, unary]
  have hmh : a5.stacks 5 = unary count.length := by
    simp [a5, a4, a3, a2, a1, a, afterNormalize, copied, input, StackRoutines.copyStacks, unary]
  have hmt : a5.stacks 7 = [] := by
    simp [a5, a4, a3, a2, a1, a, afterNormalize, copied, input, StackRoutines.copyStacks]
  obtain ⟨n, hn, r6, h6⟩ := multiply_eval a5 width.length count.length hmW hmh hmt
  let a6 : Data := ⟨r6, Function.update (Function.update a5.stacks 5 []) 6
    (unary (count.length * width.length) ++ a5.stacks 6)⟩
  let a7 := cleared 8 a6
  have hw6 : a6.stacks 8 = unary width.length := by simpa [a6] using hmW
  have h7 := clear_eval 8 a6
  rw [hw6, List.length_replicate] at h7
  have hm6 : a7.stacks 6 = unary (count.length * width.length) := by
    simp [a7, a6, a5, a4, a3, a2, a1, a, cleared, afterNormalize, copied, input,
      StackRoutines.clearStacks, StackRoutines.copyStacks]
  have htable : a7.stacks 0 = table := by
    simp [a7, a6, a5, a4, a3, a2, a1, a, cleared, afterNormalize, copied, input,
      StackRoutines.clearStacks, StackRoutines.copyStacks]
  have empty7 : a7.stacks 5 = [] ∧ a7.stacks 7 = [] ∧ a7.stacks 8 = [] ∧
      a7.stacks 9 = [] ∧ a7.stacks 10 = [] := by
    simp [a7, a6, a5, a4, a3, a2, a1, a, cleared, afterNormalize, copied, input,
      StackRoutines.clearStacks, StackRoutines.copyStacks]
  have h8 := readPrefix_eval a7 (count.length * width.length) hm6
    (by simpa [htable] using henough) empty7.1 empty7.2.1 empty7.2.2.1
      empty7.2.2.2.1 empty7.2.2.2.2
  let a8 : Data := ⟨readRegs a7.regs 0 1 none, Function.update a7.stacks 3
    ((a7.stacks 0).take (count.length * width.length) ++ a7.stacks 3)⟩
  let a9 := cleared 6 a8
  have hp8 : a8.stacks 6 = unary (count.length * width.length) := by simpa [a8] using hm6
  have h9 := clear_eval 6 a8
  rw [hp8, List.length_replicate] at h9
  have ht := h1.seq (h2.seq (h3.seq (h4.seq (h5.seq (h6.seq (h7.seq (h8.seq h9)))))))
  have heq : a9 = output a9.regs table count width := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      fin_cases i <;>
        simp [ a8, a7, a6, a5, a4, a3, a2, a1, a, cleared,
          afterNormalize, copied, input, StackRoutines.clearStacks, StackRoutines.copyStacks, unary]
  change Eval command _ a a9 at ht
  rw [heq] at ht
  refine ⟨_, ?_, a9.regs, ht⟩
  unfold budget
  nlinarith

theorem program_trace (regs : Fin 3 → Bool) (table count width : List Bool)
    (henough : count.length * width.length ≤ table.length) :
    ∃ n ≤ budget count.length width.length + 1, ∃ regs',
      Trace program n ((input regs table count width).withPC (some program.entry))
        ((output regs' table count width).withPC none) := by
  obtain ⟨n, hn, regs', ht⟩ := command_eval regs table count width henough
  exact ⟨n + 1, by omega, regs', compiled_halt_trace ht 0 3⟩

end SubexponentialSAT.SqrtLog.PackingPrefixProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingPrefixProgramLift
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PackingPrefixProgram

open SubexponentialSAT BitProgram StructuredCalls

/-- Framed prefix preparation, preserving the persistent table, raw h and W
counters, every outside bank, and any stored incidence score outside ports. -/
theorem prepare_eval {r s : ℕ} (p : Ports r s) (a : State r s)
    (hempty : ∀ i : Fin 11, 3 ≤ i.val → a.stacks (p.stack i) = [])
    (henough : (a.stacks (p.stack 1)).length * (a.stacks (p.stack 2)).length ≤
      (a.stacks (p.stack 0)).length) :
    ∃ n ≤ budget (a.stacks (p.stack 1)).length (a.stacks (p.stack 2)).length + 1,
      ∃ b, Ready p a b ∧ Eval (prepare p) n a b := by
  let regs := a.regs ∘ p.register
  let table := a.stacks (p.stack 0)
  let count := a.stacks (p.stack 1)
  let width := a.stacks (p.stack 2)
  obtain ⟨n, hn, regs', ht⟩ := program_trace regs table count width henough
  have hin : input regs table count width = projectState p.register p.stack a := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      fin_cases i <;> simp [ table, count, width, hempty]
  rw [hin] at ht
  let b := embedState p.register p.stack a (output regs' table count width)
  have he := eval_call_from_state program p.register p.stack a p.register_injective p.stack_injective ht
  have hs : ∀ i, b.stacks (p.stack i) = (output regs' table count width).stacks i :=
    embedState_stack p.register p.stack a (output regs' table count width) p.stack_injective
  refine ⟨n, hn, b, ?_, he⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    rw [hs]
    fin_cases i <;> rfl
  · exact hs 3
  · exact hs 4
  · intro i hi
    rw [hs]
    fin_cases i <;> simp_all [output]
  · intro i hi
    exact embedState_stack_frame p.register p.stack a (output regs' table count width) i (by rintro ⟨j, hj⟩; exact hi j hj)
  · intro i hi
    exact embedState_register_frame p.register p.stack a (output regs' table count width) i (by rintro ⟨j, hj⟩; exact hi j hj)

end SubexponentialSAT.SqrtLog.PackingPrefixProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingProgramAssemblyHeadSetup
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The native head-stage gate and paid extraction of its prior-word prefix. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram.Assembly
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes

theorem headSetup_eval {r Q : ℕ} (d : Data) (heads : ℕ) (fixed : List (Word r Q))
    (padding : List Bool) (hr : SetupReady d)
    (hhead : SubexponentialSAT.CounterPrograms.value (d.stacks 20)=heads)
    (hp : (d.stacks 19).length=fixed.length)
    (hw : (d.stacks 10).length=ReadPlan.wordWidth r Q)
    (ha : d.stacks 8=(fixed.reverse.map ReadPlan.encodeWord).flatten++padding) :
    ∃ t ≤ PackingWeightProgram.Gate.budget (projectState gateRegisters gatePorts d)+1+
      PackingPrefixProgram.budget (headCount heads fixed) (ReadPlan.wordWidth r Q)+1,
      ∃ e : Data, Eval headSetup t d e ∧
      e.stacks 1=(headRows heads fixed).flatten ∧
      e.stacks 2=List.replicate (headCount heads fixed) true ∧
      (e.stacks 18).length=headCount heads fixed ∧
      (∀ j,j≠1→j≠2→j≠18→e.stacks j=d.stacks j) := by
  obtain ⟨tg,htg,b,hg,ho,hf⟩ := gate_eval d hr
  have hcount : (b.stacks 18).length=headCount heads fixed := by
    rw [ho,hhead,hp]
    simp only [headCount]
    split <;> simp [hp]
  have hb8 : b.stacks 8=d.stacks 8 := hf _ (by decide)
  have hb10 : (b.stacks 10).length=ReadPlan.wordWidth r Q := by rw [hf _ (by decide),hw]
  have hcapacity : (b.stacks 18).length*(b.stacks 10).length ≤ (b.stacks 8).length := by
    rw [hcount,hb10,hb8,ha,List.length_append,encodedWords_length,List.length_reverse]
    exact (Nat.mul_le_mul_right _ (headCount_le heads fixed)).trans (Nat.le_add_right _ _)
  obtain ⟨tp,htp,e,hep,he⟩ := PackingPrefixProgram.prepare_eval prefixABI b (by
    intro i hi
    fin_cases i <;> try (norm_num at hi)
    all_goals simpa [prefixABI,prefixPorts,hf] using hr _ (by simp)) hcapacity
  have ho1 : e.stacks 1=(headRows heads fixed).flatten := by
    have hh := hep.2.1
    change e.stacks 1=(b.stacks 8).take ((b.stacks 18).length*(b.stacks 10).length) at hh
    rw [hh,hcount,hb10,hb8,ha]
    exact take_headRows heads fixed padding
  have ho2 : e.stacks 2=List.replicate (headCount heads fixed) true := by
    have hh := hep.2.2.1
    simpa [prefixABI,prefixPorts,PackingPrefixProgram.unary,hcount] using hh
  have ho18 : (e.stacks 18).length=headCount heads fixed := by
    have hh := hep.1 1
    have hh' : e.stacks 18=b.stacks 18 := by simpa [prefixABI,prefixPorts] using hh
    exact (congrArg List.length hh').trans hcount
  refine ⟨tg+tp,?_,e,hg.seq he,ho1,ho2,ho18,?_⟩
  · change tp ≤ PackingPrefixProgram.budget (b.stacks 18).length (b.stacks 10).length+1 at htp
    rw [hcount,hb10] at htp
    omega
  · intro j hj1 hj2 hj18
    by_cases hm : ∃ i,prefixPorts i=j
    · obtain ⟨i,rfl⟩ := hm
      fin_cases i <;> first
        | exact False.elim (hj1 rfl)
        | exact False.elim (hj2 rfl)
        | exact False.elim (hj18 rfl)
        | exact (hep.1 0).trans (hf _ (by decide))
        | exact (hep.1 2).trans (hf _ (by decide))
        | exact (hep.2.2.2.1 (5 : Fin 11) (by decide)).trans (hr _ (by simp [prefixPorts])).symm
        | exact (hep.2.2.2.1 (6 : Fin 11) (by decide)).trans (hr _ (by simp [prefixPorts])).symm
        | exact (hep.2.2.2.1 (7 : Fin 11) (by decide)).trans (hr _ (by simp [prefixPorts])).symm
        | exact (hep.2.2.2.1 (8 : Fin 11) (by decide)).trans (hr _ (by simp [prefixPorts])).symm
        | exact (hep.2.2.2.1 (9 : Fin 11) (by decide)).trans (hr _ (by simp [prefixPorts])).symm
        | exact (hep.2.2.2.1 (10 : Fin 11) (by decide)).trans (hr _ (by simp [prefixPorts])).symm
    · exact (hep.2.2.2.2.1 j (by intro i hi; exact hm ⟨i,hi⟩)).trans (hf j hj18)

end SubexponentialSAT.SqrtLog.PackingProgram.Assembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingProgramAssemblyHeads
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual head-score production from the controller table and alphabet. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram.Assembly
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes

theorem heads_eval {r Q : ℕ} (d : Data) (headCount : ℕ) (fixed alphabet : List (Word r Q))
    (padding : List Bool) (hr : HeadReady d)
    (hhead : SubexponentialSAT.CounterPrograms.value (d.stacks 20)=headCount)
    (hp : (d.stacks 19).length=fixed.length)
    (hw : (d.stacks 10).length=ReadPlan.wordWidth r Q)
    (ha : d.stacks 8=(fixed.reverse.map ReadPlan.encodeWord).flatten++padding)
    (halphabet : d.stacks 30=ProgramEncoding.encodeRecords (alphabet.map ReadPlan.encodeWord)) :
    ∃ t ≤ headsBudget d headCount fixed alphabet, ∃ e : Data,
      Eval heads t d e ∧
      e.stacks 12=ProgramEncoding.encodeRecords
        (alphabet.map (fun candidate => UnaryCompare.encode (overlap headCount fixed candidate))) ∧
      (∀ j,j≠12→e.stacks j=d.stacks j) := by
  have hready : SetupReady d := by
    intro j hj
    exact hr j ((show ({1,2,3,4,5,6,7,13,18} : Finset (Fin 48)) ⊆
      {1,2,3,4,5,6,7,12,13,14,15,16,17,18} by decide) hj)
  obtain ⟨ts,hts,b,hs,hb1,hb2,hb18,hbf⟩ := headSetup_eval d headCount fixed padding hready hhead hp hw ha
  have hb14 : b.stacks 14=[] := (hbf _ (by decide) (by decide) (by decide)).trans (hr _ (by simp))
  have hb17 : b.stacks 17=[] := (hbf _ (by decide) (by decide) (by decide)).trans (hr _ (by simp))
  have hb30 : b.stacks 30=d.stacks 30 := hbf _ (by decide) (by decide) (by decide)
  let a := SubexponentialSAT.SubexpScanPrimitives.afterCopy b 30 14 0 1
  have hcopy : Eval copyAlphabet (7*(b.stacks 30).length+5) b a :=
    SubexponentialSAT.SubexpScanPrimitives.copy_eval b 30 14 17 0 1 (by decide) (by decide) (by decide) (by decide) hb17
  have hstack : a.stacks=Function.update b.stacks 14 (b.stacks 30) := by
    funext j
    simp [a,SubexponentialSAT.SubexpScanPrimitives.afterCopy,SubexponentialSAT.StackRoutines.copyStacks,hb14]
  let z := SequentialProgram.resetState (List.finRange 16) a
  have hreset : Eval resetHead 16 a z := SequentialProgram.resetList_eval _ _
  have hzstack : z.stacks=Function.update b.stacks 14 (b.stacks 30) := hstack
  have hzregs : ∀ i,z.regs (headRegisters i)=false := by
    intro i
    simp [z]
  have hz1 : z.stacks (headPorts 1)=(headRows headCount fixed).flatten := by
    simpa [hzstack,headPorts] using hb1
  have hz5 : z.stacks (headPorts 5)=List.replicate (headRows headCount fixed).length true := by
    simpa [hzstack,headPorts,headRows_length] using hb2
  have hz8 : z.stacks (headPorts 8)=ProgramEncoding.encodeRecords (alphabet.map ReadPlan.encodeWord) := by
    simp [hzstack,headPorts,hb30,halphabet]
  have hzero : ∀ i : Fin 12,i≠1→i≠5→i≠8→z.stacks (headPorts i)=[] := by
    intro i hi1 hi5 hi8
    fin_cases i <;> first
      | exact False.elim (hi1 rfl)
      | exact False.elim (hi5 rfl)
      | exact False.elim (hi8 rfl)
      | simpa [hzstack,headPorts,hbf] using hr _ (by simp)
  have hvalid : ∀ candidate ∈ alphabet.map ReadPlan.encodeWord,
      PackingHeadProgramCandidates.validPayload (headRows headCount fixed) candidate := by
    intro candidate hc row hrow
    obtain ⟨word,_,rfl⟩ := List.mem_map.mp hc
    simpa using headRows_width headCount fixed row hrow
  obtain ⟨tc,htc,c,hc,hcs,_,_⟩ := PackingHeadProgramCandidates.command_lifted
    headRegisters headPorts headRegisters_injective headPorts_injective z
    (headRows headCount fixed) (alphabet.map ReadPlan.encodeWord)
    hzregs hz1 hz5 hz8 hzero hvalid
  have hc1 : c.stacks 1=(headRows headCount fixed).flatten := by simpa [hcs,headPorts,hzstack] using hb1
  have hc2 : c.stacks 2=List.replicate (Assembly.headCount headCount fixed) true := by
    simpa [hcs,headPorts,hzstack] using hb2
  have hc18 : (c.stacks 18).length=Assembly.headCount headCount fixed := by
    simpa [hcs,headPorts,hzstack] using hb18
  have hlength : ∀ j ∈ ([1,2,18] : List (Fin 48)),
      (c.stacks j).length ≤ Assembly.headCount headCount fixed*ReadPlan.wordWidth r Q+Assembly.headCount headCount fixed := by
    intro j hj
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl|rfl|rfl
    · rw [hc1,headRows_flatten_length]; omega
    · rw [hc2,List.length_replicate]; omega
    · rw [hc18]; omega
  obtain ⟨tl,htl,e,hl,hes⟩ := SequentialProgram.clearList_eval [1,2,18] c _ hlength
  refine ⟨ts+((7*(b.stacks 30).length+5)+(16+(tc+tl))),?_,e,
    hs.seq (hcopy.seq (hreset.seq (hc.seq hl))),?_,?_⟩
  · simp only [List.length_cons,List.length_nil] at htl
    rw [hb30]
    unfold headsBudget
    omega
  · rw [hes]
    simp [hcs,headPorts,headScoreRecords_eq]
  · intro j hj12
    rw [hes]
    by_cases hj1 : j=1
    · subst j; simp [hr 1 (by simp)]
    by_cases hj2 : j=2
    · subst j; simp [hr 2 (by simp)]
    by_cases hj18 : j=18
    · subst j; simp [hr 18 (by simp)]
    by_cases hj14 : j=14
    · subst j; simp [hcs,headPorts,hr 14 (by simp)]
    · simp only [List.mem_cons,List.not_mem_nil,hj1,hj2,hj18,or_self,ite_false]
      simpa [hcs,headPorts,hzstack,hj12,hj14] using hbf j hj1 hj2 hj18

end SubexponentialSAT.SqrtLog.PackingProgram.Assembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingIncidenceInputLoose
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The incidence scorer does not touch controller storage on ports 12--18. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput
open SubexponentialSAT.BitProgram SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp
open SubexponentialSAT.SqrtLog.PackingIncidenceProgram

section Semantics
variable {I V E : Type*} [Fintype I] [Fintype V] [Fintype E]
  [DecidableEq I] [DecidableEq V] [DecidableEq E]
  (ivar : I → V) (factor : I → E) {r Q : ℕ}

omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] in
theorem run_from_memory_loose (a : Word r Q) (tail fixed : List (Word r Q))
    (pairs : List (I × I)) (indices : List (V ⊕ E)) (hi : ∀ x, x ∈ indices)
    (n : ℕ) (raw : List PlanPair) (d : ScoreBuilderProgram.Data)
    (hraw : raw.Perm (pairs.map (incidencePair ivar factor indices)))
    (hm : LooseMemory a fixed n d)
    (hh : SequentialProgram.HighState
      (ScoreBuilderRawInput.environment 1 (a::tail) indices.length raw) d.stacks)
    (hsize : n+1+fixed.length = indices.length) :
    ∃ t ≤ runtimeBound indices.length raw.length (a::tail).length (ReadPlan.wordWidth r Q),
      ∃ e : ScoreBuilderProgram.Data,
      SubexponentialSAT.StructuredCalls.Eval command t d e ∧
      e.stacks 0 = ProgramEncoding.encodeRecords ((a::tail).map (fun candidate =>
        UnaryCompare.encode (incidenceNumerator ivar factor (a::tail) pairs indices a
          n (candidate::fixed)))) ∧
      (∀ j, j ≠ 0 → e.stacks j = d.stacks j) := by
  have hp : ∀ pair ∈ raw, ValidRawPair indices.length pair := by
    intro pair hpair
    obtain ⟨p, _, rfl⟩ := List.mem_map.mp (hraw.mem_iff.mp hpair)
    exact incidencePair_valid ivar factor indices hi p
  obtain ⟨t, ht, regs, he⟩ := command_eval_loose a tail fixed n indices.length raw d hm hh hsize hp
  refine ⟨t, ht, _, he, ?_, output_frame d regs _⟩
  have hout := scoreBytes_eq ivar factor a tail fixed pairs indices hi n raw
    (cleaned a tail d) hraw (cleaned_memory a tail fixed n d hm) hsize
  rw [cleaned_context] at hout
  simpa [ScoreBuilderProgram.resultState] using hout
end Semantics
end SubexponentialSAT.SqrtLog.PackingIncidenceInput

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ProducedQueryRankSchedule
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Scheduled rank of the literal native packing. The intermediate scan
premises are discharged for produced queries in the final certificate. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.ProducedQueryRank
open scoped BigOperators
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp.ConstructivePacking
open PackingCallerProgram LeafParametersProgram
open BucketProgram.ProducedRank

/-- The actual query parameters fix the rank function; no rank field is input. -/
def queryLabelRows (q : LeafQueryFrontend.Query) (k : ℕ) (hg : Guard (q.input k))
    (a : Word (LeafProgram.Query.packingProblem q k hg).r (LeafProgram.Query.packingProblem q k hg).Q)
    (tail : List (Word (LeafProgram.Query.packingProblem q k hg).r
      (LeafProgram.Query.packingProblem q k hg).Q)) : ℕ :=
  labelRows (LeafProgram.Query.packingProblem q k hg) a tail (produce (q.input k)).R (queryLow q)

end SubexponentialSAT.SqrtLog.ProducedQueryRank

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryStreamCorrect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Physical boundaries of the fixed conditioned query. The node invariant
retains the actual prepared words and the exact length of the emitted stream;
it contains no execution or evaluator fields. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamCorrect

open OAI BitProgram StructuredCalls SqrtLog SubexpLiftRing SubexpQuarticRing
open SubexpSetupStorage

def finishBudget (n t d J A : ℕ) : ℕ :=
  QueryNodeFinish.budget n (baseWidth 3 t) d t J (QueryHeadBudgets.compact A)

def nodeSpace (n t d J A : ℕ) : ℕ :=
  max (StreamedQueryMeasuredCost.pairSpaceEnvelope A)
    (896*QueryHeadBudgets.compact A+prepareBudget A+finishBudget n t d J A+1)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamCorrect
end


