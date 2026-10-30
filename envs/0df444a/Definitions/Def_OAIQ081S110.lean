-- Prove2me | Definitions.Def_OAIQ081S110
-- name    : OAIQ081S110
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T22:26:58.179836+00:00
-- url     : https://prove2.me/theorems/9e222661-3d93-4def-af87-29d7d36a1fed
-- title:
--   Definitions bundle OAIQ081S110 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 68 declarations of OpenAI's Lean: 33 definitions and 35 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.SourceReady.localStore`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.SourceReady.sourceBase`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.CopiesReady`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.CopyReady`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Query.scopeCopyBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.copiesCost`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.copiesState`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafScopeInputBounds.capacity`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Arity.maxCall`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Arity.prepare`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Arity.scopeCall`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Arity.transfer`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary.cleared`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary.copied`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary.machine`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary.transferred`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.afterClear`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.afterCopy`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.afterTransfer`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProjectionProgram.afterFrame`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsReadoutProgram.accumulate`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsReadoutProgram.accumulateProgram`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsReadoutProgram.fetchAdd`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.incidenceScorerContext`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.incidenceScorerPlan`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceProgram.PlanPair`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceProgram.incidencePair`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram.Code`, `OAI.Algorithms.SubexponentialSAT.Subexp.CollisionGenerateProgram.command`, `OAI.Algorithms.SubexponentialSAT.Subexp.CollisionGenerateProgram.generator`, `OAI.Algorithms.SubexponentialSAT.Subexp.CollisionGenerateProgram.program`, `OAI.Algorithms.SubexponentialSAT.Subexp.PairScoreProgram.pairCount`.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLogSpace_AttainedSignatureProgram`, `SubexponentialSAT_SqrtLog_LeafProgramQueryBank`, `SubexponentialSAT_SqrtLog_LeafProgramSourceReadyCore`, `SubexponentialSAT_SqrtLog_LeafProgramSourceReadyInput`, `SubexponentialSAT_SqrtLog_LeafQueryFrontendInputBudget`, `SubexponentialSAT_SqrtLog_LeafQueryFrontendOps`, `SubexponentialSAT_SqrtLog_LeafRingSetupProgramNative`, `SubexponentialSAT_SqrtLog_LeafRingSetupProgramReplay`, `SubexponentialSAT_SqrtLog_LeafScopeInputBoundsQuery`, `SubexponentialSAT_SqrtLog_LeafStatisticsProgramArity`, `SubexponentialSAT_SqrtLog_MomentsProgramDictionaryBase`, `SubexponentialSAT_SqrtLog_MomentsProgramDictionaryState`, `SubexponentialSAT_SqrtLog_MomentsProgramProduct`, `SubexponentialSAT_SqrtLog_MomentsProjectionProgramBase`, `SubexponentialSAT_SqrtLog_MomentsReadoutProgramAccumulate`, `SubexponentialSAT_SqrtLog_MomentsReadoutProgramFetch`, `SubexponentialSAT_SqrtLog_NativePackingBounds`, `SubexponentialSAT_SqrtLog_NativePackingBoundsTail`, `SubexponentialSAT_SqrtLog_PackingCallerProgramBoundsBasic`, `SubexponentialSAT_SqrtLog_PackingCompletion`, `SubexponentialSAT_SqrtLog_PackingCompletionGenerated`, `SubexponentialSAT_SqrtLog_PackingCompletionScore`, `SubexponentialSAT_SqrtLog_PackingIncidenceProgram`, `SubexponentialSAT_SqrtLog_PackingIncidenceProgramInputs`, `SubexponentialSAT_SqrtLog_RingNodeProgram`, `SubexponentialSAT_Subexp_CandidateContextRefinement`, `SubexponentialSAT_Subexp_CollisionGenerateProgram`, `SubexponentialSAT_Subexp_PackingCanonicalData`, `SubexponentialSAT_Subexp_PackingVertexLabels`, `SubexponentialSAT_Subexp_PairScoreProgram`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S082`, `OAIQ081S083`, `OAIQ081S084`, `OAIQ081S085`, `OAIQ081S089`, `OAIQ081S092`, `OAIQ081S093`, `OAIQ081S095` and `OAIQ081S096` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S128`, `OAIQ081S130`, `OAIQ081S131`, `OAIQ081S134`, `OAIQ081S135` and `OAIQ081S136`; the statements `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Arity.scopeCall_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary.finish_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary.insert_code_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary.insert_hit_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary.onHit_eval` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsReadoutProgram.fetchAdd_miss`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Arity.scopeCall_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary.insert_hit_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary.onHit_eval` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsReadoutProgram.fetchAdd_miss`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S082
import Definitions.Def_OAIQ081S083
import Definitions.Def_OAIQ081S084
import Definitions.Def_OAIQ081S085
import Definitions.Def_OAIQ081S089
import Definitions.Def_OAIQ081S092
import Definitions.Def_OAIQ081S093
import Definitions.Def_OAIQ081S095
import Definitions.Def_OAIQ081S096

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_AttainedSignatureProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Native full-key computation for the resumable attained-signature scan

One invocation preserves the assignment and all raw integer constraint rows.
Its local polynomial-time bound controls every scratch stack at every source
prefix. The generator retains candidate and predecessor cursors separately.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram

open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport
open OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram

abbrev Code := Cmd 8 16

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramQueryBank
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The packed layout is constructed beside the live parameter bank. These
equalities bridge the frontend's physical bank to the ring producer after
packing has changed its own registers and private scratch. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Query
open SubexponentialSAT BitProgram StructuredCalls LeafParametersProgram

theorem ring_bank_of_frame (a b : Data) (w : Bank.Words) (r : Bank.Regs)
    (ha : projectState Exports.bankRegs Exports.bank a=Bank.state r w)
    (hf : ∀i : Fin 768,340 ≤ i.val → i.val < 417 → b.stacks i=a.stacks i) :
    projectState (LeafRingSetupProgram.registers 8 (by decide)) LeafRingSetupProgram.parameters
      (projectState LeafRingSetupProgram.wideRegisters LeafRingSetupProgram.wideStacks b)=
      Bank.state (b.regs ∘ Exports.bankRegs) w := by
  apply congrArg₂ StructuredProgram.State.mk
  · funext i
    fin_cases i <;> rfl
  · funext i
    change b.stacks (Exports.bank i)=(Bank.state (b.regs ∘ Exports.bankRegs) w).stacks i
    rw [hf (Exports.bank i) (by simp [Exports.bank])
      (by have := i.isLt; simp [Exports.bank]; omega)]
    exact congrFun (congrArg StructuredProgram.State.stacks ha) i

end SubexponentialSAT.SqrtLog.LeafProgram.Query

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramSourceReadyCore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Byte-level value and frame rules for source preparation. These rules
concern the actual paid copy/clear state transformer, not assumed source
execution or a supplied readiness certificate. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.SourceReady
open SubexponentialSAT BitProgram StructuredCalls SubexpSetupStorage
def localStore (a : Data) : Fin 340 → List Bool := (prepared a).stacks ∘ localPort

end SubexponentialSAT.SqrtLog.LeafProgram.SourceReady

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

theorem iterationCost_le (width : ℕ) (plans : List (List ℕ)) (start P K : ℕ)
    (hplan : ∀ plan ∈ plans, (planBytes plan).length ≤ P)
    (hindex : start+plans.length ≤ K) :
    iterationCost width plans start ≤
      plans.length * (12*P+13+200*(width+P+K+1)^2) := by
  induction plans generalizing start with
  | nil => simp [iterationCost]
  | cons plan plans ih =>
      have hp := hplan plan (by simp)
      have hs : start ≤ K := by
        simp only [List.length_cons] at hindex
        omega
      have ht := ih (start+1) (fun p hm => hplan p (by simp [hm])) (by
        simp only [List.length_cons] at hindex
        omega)
      have hc : callbackCost width (planBytes plan).length start ≤
          200*(width+P+K+1)^2 := by
        dsimp [callbackCost]
        gcongr
      have he : (planPayload plan).length ≤ 2*P+1 := by
        change (Encoding.frame (planBytes plan)).length ≤ _
        rw [Encoding.length_frame]
        omega
      simp only [iterationCost, List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

/-- A polynomial in the number of plans, maximum serialized plan size,
row width, and initial unary index. It also covers zero-width arrays. -/
theorem traceCost_le (width : ℕ) (plans : List (List ℕ)) (start P : ℕ)
    (hp : ∀ plan ∈ plans, (planBytes plan).length ≤ P) :
    traceCost width plans start ≤
      4 + plans.length*(12*P+13+200*(width+P+start+plans.length+1)^2) := by
  have h := iterationCost_le width plans start P (start+plans.length) hp le_rfl
  dsimp [traceCost]
  simpa only [Nat.add_assoc] using Nat.add_le_add_left h 4

end SubexponentialSAT.Subexp.PackingVertexLabels

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_CollisionGenerateProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Generating and evaluating collision tuples with fixed control

The alphabet and unary tuple depth are input data. The generator and collision
stream are linked through actual stack ports. The current word table and the
two selected read plans remain runtime inputs and are preserved.
-/

namespace SubexponentialSAT.Subexp.CollisionGenerateProgram

open BitProgram StackRoutines StructuredCalls

abbrev generator : Cmd 10 20 :=
  .call (ProgramLinking.liftProgram TupleProgram.generateProgram id generatorPorts)

abbrev command : Cmd 10 20 :=
  .seq generator (.seq clearWork (.seq resetCommand streamCommand))

abbrev program : Program 10 20 (StructuredCalls.size command + 1) :=
  StructuredCalls.compiled command 19 11

end SubexponentialSAT.Subexp.CollisionGenerateProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PairScoreProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Aggregating the actual collision streams of all vertex pairs

The fixed program consumes framed pairs of already selected read plans.
Producing those selected plans from original plans and the remaining-index
table is a separate preparation step.  Every pair invokes the actual tuple
generator and collision machine; a final fixed unary tally produces the score.
-/

namespace SubexponentialSAT.Subexp.PairScoreProgram

open BitProgram StackRoutines StructuredCalls

def pairCount (ctx : Context) (pair : PlanPair) : ℕ :=
  PaddedCompletion.trueCount (pairStream ctx pair [])

theorem pairStream_trueCount (ctx : Context) (pair : PlanPair) (stream : List Bool) :
    PaddedCompletion.trueCount (pairStream ctx pair stream) =
      pairCount ctx pair + PaddedCompletion.trueCount stream := by
  unfold pairCount pairStream
  rw [CollisionTupleProgram.streamed_trueCount, CollisionTupleProgram.streamed_trueCount]
  simp [PaddedCompletion.trueCount, PaddedCompletion.successful]

theorem streamedPairs_trueCount (ctx : Context) (pairs : List PlanPair) (stream : List Bool) :
    PaddedCompletion.trueCount (streamedPairs ctx pairs stream) =
      (pairs.map (pairCount ctx)).sum + PaddedCompletion.trueCount stream := by
  induction pairs generalizing stream with
  | nil => simp [streamedPairs]
  | cons pair pairs ih =>
    change PaddedCompletion.trueCount (streamedPairs ctx pairs (pairStream ctx pair stream)) = _
    rw [ih, pairStream_trueCount]
    simp only [List.map_cons, List.sum_cons]
    omega

theorem score_eq_sum (ctx : Context) (pairs : List PlanPair) :
    score ctx pairs = (pairs.map (pairCount ctx)).sum := by
  rw [score, streamedPairs_trueCount]
  simp [PaddedCompletion.trueCount, PaddedCompletion.successful]

end SubexponentialSAT.Subexp.PairScoreProgram

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

theorem test_data (r : Fin 8 → Bool) (m rank arity out : List Bool) :
    testResult ports (data r m rank arity [] [] out) =
      data (testResult ports (data r m rank arity [] [] out)).regs m rank arity [] [] out := by
  apply SubexpEnumerationProgram.data_ext
  · rfl
  · exact testResult_stacks ports _ rfl

theorem ripple_data (r : Fin 8 → Bool) (m rank arity out : List Bool) :
    rippleResult ports false false (data r m rank arity [] [] out) =
      data (rippleResult ports false false (data r m rank arity [] [] out)).regs
        m (ripple false rank) arity [] [] out := by
  apply SubexpEnumerationProgram.data_ext
  · rfl
  · funext i
    by_cases h13 : i = 13
    · subst i
      exact rippleResult_target ports false false _
    by_cases h10 : i = 10
    · subst i
      exact rippleResult_scratch ports false false _
    rw [rippleResult_other ports false false _ i h13 h10]
    fin_cases i <;> simp_all [data, SubexpFieldRowPreparation.tapes]

end SubexponentialSAT.SqrtLog.RingNodeProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramSourceReadyInput
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A physical caller contract. All hypotheses are bytes in retained masters,
blank work tapes, or explicit length bounds. In particular no native source
readiness or execution is assumed. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.SourceReady
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl DensePolynomialProgram
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open SubexponentialSAT.Subexp SubexponentialSAT.Subexp.ConstructivePacking SubexponentialSAT.MulticolorTypes LayoutProgram
open LayoutSourceRowsProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

variable {r Q d : ℕ}
  {ps : List (ℕ × ℕ)}
  {P : PackingData (Fin ps.length) (UniversalType r Q 1)}
  {a : Data}
  {v N f S : ℕ}

def sourceBase (a : Data) (D W : ℕ) (ps : List (ℕ × ℕ)) (v N f : ℕ) :=
  preparedSourceStore (localStore a) D W ps v N f

end SubexponentialSAT.SqrtLog.LeafProgram.SourceReady

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

def CopyReady (a : Data) (src dst : Fin 768) : Prop :=
  src ≠ dst ∧ src ≠ 679 ∧ (679 : Fin 768) ≠ dst ∧ a.stacks 679 = []

def copiesState : List (Fin 768 × Fin 768) → Data → Data
  | [],a => a
  | (s,d)::xs,a => copiesState xs (copied a s d)
def copiesCost : List (Fin 768 × Fin 768) → Data → ℕ
  | [],_ => 0
  | (s,d)::xs,a => 7*(a.stacks s).length+5+copiesCost xs (copied a s d)
def CopiesReady : List (Fin 768 × Fin 768) → Data → Prop
  | [],_ => True
  | (s,d)::xs,a => CopyReady a s d ∧ CopiesReady xs (copied a s d)

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
def scopeCall : Code := .call (ProgramLinking.liftProgram Scope.program scopeRegs scopeStacks)
def prepare : Code := .base (SubexpParameterProgram.atoms [.set 4 false,.set 5 true,.set 6 false])

def maxCall : Code := .call (ProgramLinking.liftProgram Max.program maxRegs maxStacks)

def transfer : Code := .call (StackRoutines.transferProgram 8 5 0 1)

end SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Arity

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafQueryFrontendInputBudget
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls
attribute [local simp] Fin.coe_ofNat_eq_mod

def Query.scopeCopyBudget (q : Query) : ℕ :=
  7*(Encoding.encodeList id q.clauses).length+5+
  (7*(HashScopeProgram.RawTable.inputBits q.width.length q.rows).length+5+
  (7*q.index.length+5+(7+5+(7*q.modulus.length+5+(7*q.width.length+5)))))

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

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
open LeafParametersProgram

/-- For the fixed five-counter plan, no destination overlaps a source. -/
theorem numericPlan_cost_le (s : Fin 640 → List Bool) (V W : ℕ)
    (hv : ∀ p∈numericPlan, BinaryArithmetic.toNat (s p.1) ≤ V)
    (hw : ∀ p∈numericPlan, (s p.1).length ≤ W) :
    counterCost numericPlan s ≤ 5*(7*W+6+32*(V+1)*(W+1)) := by
  have h1 := unaryCopyBound_le (s 374) V W (hv (374,204) (by simp [numericPlan])) (hw (374,204) (by simp [numericPlan]))
  have h2 := unaryCopyBound_le (s 384) V W (hv (384,209) (by simp [numericPlan])) (hw (384,209) (by simp [numericPlan]))
  have h3 := unaryCopyBound_le (s 382) V W (hv (382,243) (by simp [numericPlan])) (hw (382,243) (by simp [numericPlan]))
  have h4 := unaryCopyBound_le (s 340) V W (hv (340,191) (by simp [numericPlan])) (hw (340,191) (by simp [numericPlan]))
  have h5 := unaryCopyBound_le (s 361) V W (hv (361,296) (by simp [numericPlan])) (hw (361,296) (by simp [numericPlan]))
  simp only [numericPlan,counterCost,counterStack,Function.update_of_ne (by decide : (384 : Fin 640)≠204),
    Function.update_of_ne (by decide : (382 : Fin 640)≠209),
    Function.update_of_ne (by decide : (382 : Fin 640)≠204),
    Function.update_of_ne (by decide : (340 : Fin 640)≠243),
    Function.update_of_ne (by decide : (340 : Fin 640)≠209),
    Function.update_of_ne (by decide : (340 : Fin 640)≠204),
    Function.update_of_ne (by decide : (361 : Fin 640)≠191),
    Function.update_of_ne (by decide : (361 : Fin 640)≠243),
    Function.update_of_ne (by decide : (361 : Fin 640)≠209),
    Function.update_of_ne (by decide : (361 : Fin 640)≠204)]
  omega

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafRingSetupProgramReplay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


/-! Syntactic no-read/no-write certificate for the existing native ring
producer.  Hidden collector tapes do not affect its exact execution time. -/
namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram.Replay
open BitProgram StructuredCalls ProgramTapeReplay

theorem clear (i : Fin 640) (h : ¬hidden i) :
    AvoidsCmd hidden (LeafRingSetupProgram.clear i) :=
  avoids_clearProgram hidden i 30 31 h

theorem copy (src dst : Fin 640) (hs : ¬hidden src) (hd : ¬hidden dst) :
    AvoidsCmd hidden (LeafRingSetupProgram.copy src dst) :=
  avoids_copyProgram hidden src dst 639 30 31 hs hd (by decide)

theorem overwrite (src dst : Fin 640) (hs : ¬hidden src) (hd : ¬hidden dst) :
    AvoidsCmd hidden (LeafRingSetupProgram.overwrite src dst) :=
  ⟨clear dst hd,copy src dst hs hd⟩

theorem clearPorts (ps : List (Fin 640)) (hp : ∀i∈ps,¬hidden i) :
    AvoidsCmd hidden (LeafRingSetupProgram.clearPorts ps) := by
  induction ps with
  | nil => trivial
  | cons p ps ih => exact ⟨clear p (hp p (by simp)),ih (fun i hi => hp i (by simp [hi]))⟩

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram.Replay

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafScopeInputBoundsQuery
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Uniform physical-input capacity for the produced per-query frontend data. -/
namespace SubexponentialSAT.SqrtLog.LeafScopeInputBounds
open LeafQueryFrontend

def capacity (q : Query) (k : ℕ) : ℕ :=
  BinaryArithmetic.toNat q.ambient + (Encoding.encodeList id q.clauses).length +
    (HashScopeProgram.RawTable.inputBits q.width.length q.rows).length + q.index.length +
    q.modulus.length + q.width.length + q.ambient.length + k + 8

end SubexponentialSAT.SqrtLog.LeafScopeInputBounds

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsProgramDictionaryBase
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed physical dictionary-insertion program. All dictionary/key/vector
lengths are input data. The complete semantic composition is proved separately;
this file defines the finite table and its paid stack primitives. -/
namespace SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

abbrev Data := State 8 27

def copied (d : Data) (src dst : Fin 27) : Data :=
  ⟨readRegs d.regs 0 1 none, copyStacks src dst d.stacks⟩
def transferred (d : Data) (src dst : Fin 27) : Data :=
  ⟨readRegs d.regs 0 1 none, transferStacks src dst d.stacks⟩
def cleared (d : Data) (src : Fin 27) : Data :=
  ⟨readRegs d.regs 0 1 none, clearStacks src d.stacks⟩

end SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsProgramDictionaryState
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def machine (regs : Fin 8 → Bool) (a : Tape) : Data := ⟨regs,tapes a⟩

end SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary

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

def afterCopy (d : Data) (src dst : Fin 56) : Data :=
  ⟨readRegs d.regs 0 1 none,copyStacks src dst d.stacks⟩
def afterTransfer (d : Data) (src dst : Fin 56) : Data :=
  ⟨readRegs d.regs 0 1 none,transferStacks src dst d.stacks⟩
def afterClear (d : Data) (src : Fin 56) : Data :=
  ⟨readRegs d.regs 0 1 none,clearStacks src d.stacks⟩

end SubexponentialSAT.SqrtLog.MomentsProgram.Product


end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsProjectionProgramBase
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.MomentsProjectionProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def afterFrame (d : State 5 10) (src dst : Fin 10) (bits rest : List Bool) : State 5 10 :=
  ⟨readRegs d.regs 0 1 (some false), Function.update (Function.update d.stacks src rest) dst
    (bits.reverse ++ d.stacks dst)⟩

end SubexponentialSAT.SqrtLog.MomentsProjectionProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsReadoutProgramFetch
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A paid dictionary scan followed by native vector addition. A missing
coefficient contributes zero and leaves the accumulator unchanged. -/
namespace SubexponentialSAT.SqrtLog.MomentsReadoutProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open MomentsProgram.Dictionary

abbrev fetchAdd : Cmd 8 27 :=
  .seq (copy 15 18 23)
    (.seq lookup (.seq (.ite 4 onHit onMiss) (clear 18)))

end SubexponentialSAT.SqrtLog.MomentsReadoutProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsReadoutProgramAccumulate
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Commit the native sum as the next accumulator, reclaiming all temporary
strings. The dictionary and query are preserved for the runtime loop. -/
namespace SubexponentialSAT.SqrtLog.MomentsReadoutProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open MomentsProgram.Dictionary

abbrev accumulate : Cmd 8 27 := .seq fetchAdd commit

abbrev accumulateProgram : Program 8 27 (size accumulate+1) := compiled accumulate 15 17

end SubexponentialSAT.SqrtLog.MomentsReadoutProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingCanonicalData
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.compatibleDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.spectatorsAgreeDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.instDecidableAnchorValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# The actual assignment data used by canonical packing

The rows are the array emitted by the natural assignment program. Numeric
scope plans recover its actual type labels. The universal type enumeration
names the order of the physical tuple generator, without supplying a lookup
table or assuming the correctness of a packing result.
-/

namespace SubexponentialSAT.Subexp.PackingCanonicalSpec

open MulticolorTypes ConstructivePacking

variable {D r Q Δ : ℕ}

theorem types_length (hr : 0 < r) (hQ : 0 < Q) (Δ : ℕ) :
    (types hr hQ Δ).values.length = blockSize r Q Δ := by
  have h := congrArg List.length (types_bytes hr hQ Δ)
  simpa only [List.length_map, TypeEnumeration.universalBytes_length] using h

end SubexponentialSAT.Subexp.PackingCanonicalSpec

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_NativePackingBoundsTail
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Bounds for the actual packing tail

All sizes below come from the represented input and generated records.
There is no assumed runtime certificate: the cost estimates apply to the
same leftover and inverse budgets used by `PackingExecution.program_trace`.
-/

namespace SubexponentialSAT.SqrtLog.NativePackingBounds

open SubexponentialSAT.Subexp SubexponentialSAT.Subexp.ConstructivePacking LayoutProgram LayoutProgram.NativePacking

variable {U : Type*} [DecidableEq U]

@[simp] theorem suffix_D (s : Spec U) : s.suffix.params.D = s.params.D := rfl

theorem packed_vertices_length_le (s : Spec U) :
    (PackingReorder.packedVertices s.suffix.packing).length ≤ s.suffix.params.D := by
  simpa only [Fintype.card_fin] using
    (PackingAddressSemantics.packedVertices_nodup s.suffix.packing).length_le_card

theorem storage_vertices_length_le (s : Spec U) :
    (PackingReorder.storageVertices s.suffix.packing).length ≤ s.suffix.params.D := by
  simpa only [Fintype.card_fin] using
    (PackingAddressSemantics.storageVertices_nodup s.suffix.packing).length_le_card

theorem leftovers_length_le (s : Spec U) : s.suffix.packing.leftovers.length ≤ s.suffix.params.D := by
  simpa only [Fintype.card_fin] using s.suffix.packing.leftovers_nodup.length_le_card

theorem raw_length_le (rows : List (List Bool × List Bool)) (K B : ℕ)
    (hk : ∀ row ∈ rows, row.1.length ≤ K)
    (hb : ∀ row ∈ rows, row.2.length ≤ B) :
    (SelectorProgram.rawRecords rows).length ≤ rows.length * (2 * K + 2 * B + 2) := by
  induction rows with
  | nil => simp [SelectorProgram.rawRecords]
  | cons row rows ih =>
    have hkey := hk row (by simp)
    have hvalue := hb row (by simp)
    have htail := ih (fun x hx => hk x (List.mem_cons_of_mem _ hx))
      (fun x hx => hb x (List.mem_cons_of_mem _ hx))
    simp only [SelectorProgram.rawRecords, List.flatMap_cons, List.length_append,
      Encoding.length_frame, List.length_cons] at htail ⊢
    nlinarith

theorem address_list_length_le (s : Spec U) (vs : List (Fin s.suffix.params.D))
    (hnd : vs.Nodup) (hn : vs.length ≤ s.suffix.params.D) :
    (SelectorProgram.rawRecords (PackingAddressSemantics.addressRows
      (vs.map s.suffix.encodeVertex) 0).reverse).length ≤ addressBound s.suffix.params.D := by
  rw [PackingAddressSemantics.addressRows_map_graph vs s.suffix.encodeVertex hnd, ← List.map_reverse]
  have h := raw_length_le
    (vs.reverse.map (fun v => (s.suffix.encodeVertex v, List.replicate (vs.idxOf v) true)))
    s.suffix.params.D s.suffix.params.D
    (by
      intro row hr
      obtain ⟨v, _, rfl⟩ := List.mem_map.mp hr
      simpa only [PackLabels.Spec.encodeVertex, List.length_replicate] using Nat.le_of_lt v.isLt)
    (by
      intro row hr
      obtain ⟨v, _, rfl⟩ := List.mem_map.mp hr
      simpa only [List.length_replicate] using (List.idxOf_le_length (a := v) (l := vs)).trans hn)
  simp only [List.length_map, List.length_reverse] at h
  calc
    _ ≤ vs.length * (2 * s.suffix.params.D + 2 * s.suffix.params.D + 2) := h
    _ ≤ s.suffix.params.D * (2 * s.suffix.params.D + 2 * s.suffix.params.D + 2) := Nat.mul_le_mul_right _ hn
    _ = _ := by unfold addressBound; ring

theorem addresses_length_le (s : Spec U) : s.suffix.addresses.length ≤ addressBound s.suffix.params.D := by
  exact address_list_length_le s (PackingReorder.storageVertices s.suffix.packing)
    (PackingAddressSemantics.storageVertices_nodup s.suffix.packing) (storage_vertices_length_le s)

theorem address_records_length_le (s : Spec U) :
    (SelectorProgram.rawRecords (PackLabels.addressRecords s.suffix)).length ≤ addressBound s.suffix.params.D :=
  addresses_length_le s

end SubexponentialSAT.SqrtLog.NativePackingBounds

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_NativePackingBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Polynomial cost of the actual native address-plan suffix. -/
namespace SubexponentialSAT.SqrtLog.NativePackingBounds
open SubexponentialSAT.Subexp SubexponentialSAT.BitProgram LayoutProgram
variable {U : Type*} [DecidableEq U]

theorem input_labels (s : NativePacking.Spec U) :
    s.params.labelStream=BucketProgram.encodeRecords (PackLabels.records s.suffix).reverse := by
  rw [NativeFrontend.Params.labelStream,s.label_records]
  rfl

theorem keys_count (s : NativePacking.Spec U) : (PackLabels.keys s.suffix).length = s.types.values.length := by simp [PackLabels.keys,NativePacking.Spec.suffix]

theorem entries_count (s : NativePacking.Spec U) : (PackLabels.entries s.suffix).length = s.types.values.length := by
  simp [PackLabels.entries, PackingExtraction.typedEntries, PackLabels.Spec.packing, NativePacking.Spec.suffix]

end SubexponentialSAT.SqrtLog.NativePackingBounds

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_CandidateContextRefinement
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Candidate contexts and selected plans refine the natural score evaluator. -/

namespace SubexponentialSAT.Subexp.CandidateScoreRefinement

open SubexponentialSAT.MulticolorTypes SubexponentialSAT.SlotAssignment

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E]
variable {r Q Δ : ℕ}
  [NeZero r]
  (P : SubexponentialSAT.Factor.Pattern V E)

theorem score_context_congr (a b : PairScoreProgram.Context)
    (hc : a.current = b.current) (hw : a.width.length = b.width.length)
    (ha : a.alphabet = b.alphabet) (hd : a.depth.length = b.depth.length)
    (plans : List PairScoreProgram.PlanPair) :
    PairScoreProgram.score a plans = PairScoreProgram.score b plans := by
  have hcount : PairScoreProgram.pairCount a = PairScoreProgram.pairCount b := by
    funext pair
    simp only [PairScoreProgram.pairCount, PairScoreProgram.pairStream, hc, hw, ha, hd]
  simp only [PairScoreProgram.score_eq_sum, hcount]


end SubexponentialSAT.Subexp.CandidateScoreRefinement

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingIncidenceProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete incidence collision scoring from raw two-word read plans.
The fixed legacy program constructs its selection tables and all four-word
completion tuples at runtime. No precomputed collision table is an input. -/

namespace SubexponentialSAT.SqrtLog.PackingIncidenceProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp

abbrev PlanPair := PairScoreProgram.PlanPair

end SubexponentialSAT.SqrtLog.PackingIncidenceProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingIncidenceProgramInputs
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Raw incidence-address plans and the exact runtime active-support filter. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceProgram
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.LocalExpectation SubexponentialSAT.Subexp SubexponentialSAT.SqrtLog.Packing

section Plans
variable {I V E : Type*} [DecidableEq V] [DecidableEq E]
  (ivar : I → V) (factor : I → E)

def incidencePair (indices : List (V ⊕ E)) (pair : I × I) : PlanPair :=
  (incidencePlan ivar factor indices pair.1, incidencePlan ivar factor indices pair.2)

end Plans

section Support
variable {I V E : Type*} [Fintype I] [Fintype V] [Fintype E]
  [DecidableEq I] [DecidableEq V] [DecidableEq E]
  (ivar : I → V) (factor : I → E)

omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] in
theorem plan_support {Q : ℕ} (indices : List (V ⊕ E)) (pair : I × I) (j : ℕ) :
    j ∈ (incidencePair ivar factor indices pair).1.reverse ++
      (incidencePair ivar factor indices pair).2 ↔
    j ∈ numberedScoreSupport (Q := Q) ivar factor indices (.inl pair) := by
  rcases pair with ⟨i,l⟩
  simp [incidencePair, incidencePlan, numberedScoreSupport, scoreSupport,
 or_left_comm, or_comm]

end Support

end SubexponentialSAT.SqrtLog.PackingIncidenceProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingCompletion
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.compatibleDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.spectatorsAgreeDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.instDecidableAnchorValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Boolean local completion trees for the two exact packing score counters. -/
namespace SubexponentialSAT.SqrtLog.Packing
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.LocalExpectation SubexponentialSAT.Subexp.LocalExpectation
open SubexponentialSAT.Subexp.PaddedCompletion SubexponentialSAT.Subexp.ReadPlan

section Completion
variable {I V E : Type*} [Fintype I] [Fintype V] [Fintype E]
  [DecidableEq I] [DecidableEq V] [DecidableEq E]
variable (ivar : I → V) (factor : I → E) {r Q : ℕ}

omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] in
theorem numberedIncidenceTest_value (indices : List (V ⊕ E))
    (z : ScoreTerm I V Q) (η : ℕ → Word r Q) :
    boolValue (numberedIncidenceTest ivar factor indices z η) =
      PackingProgram.incidenceIndicator ivar factor z (fun a => η (indexCode indices a)) := by
  cases z with
  | inl p => rcases p with ⟨i,j⟩; simp [numberedIncidenceTest, incidenceWords_eq_iff,
      boolValue, PackingProgram.incidenceIndicator]
  | inr p => rfl

omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] in
theorem incidenceCompletionLeaves_count (alphabet : List (Word r Q))
    (indices : List (V ⊕ E)) (z : ScoreTerm I V Q) (remaining : List ℕ)
    (η : ℕ → Word r Q) :
    trueCount (incidenceCompletionLeaves ivar factor alphabet indices z remaining η) =
      scaledCount alphabet
        (fun ξ => PackingProgram.incidenceIndicator ivar factor z
          (fun a => ξ (indexCode indices a)))
        (numberedScoreSupport ivar factor indices z) 4 remaining η := by
  unfold incidenceCompletionLeaves
  rw [trueCount_paddedLeaves]
  simp only [numberedIncidenceTest_value]
  rfl

end Completion
end SubexponentialSAT.SqrtLog.Packing

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingCompletionGenerated
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.compatibleDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.spectatorsAgreeDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.instDecidableAnchorValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Runtime-generated incidence collision leaves, using actual two-word read plans. -/
namespace SubexponentialSAT.SqrtLog.Packing
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.LocalExpectation SubexponentialSAT.Subexp.LocalExpectation
open SubexponentialSAT.Subexp

section Plans
variable {I V E : Type*} [Fintype I] [Fintype V] [Fintype E]
  [DecidableEq I] [DecidableEq V] [DecidableEq E]
variable (ivar : I → V) (factor : I → E) {r Q : ℕ}

omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] in
theorem incidence_leafBit_eq (indices : List (V ⊕ E))
    (hi : ∀ a, a ∈ indices) (default : Word r Q) (current candidate : List (Word r Q))
    (remaining : List ℕ) (hc : indices.length ≤ current.length)
    (hr : remaining.length ≤ candidate.length) (i j : I) :
    CollisionTupleProgram.leafBit (CollisionTupleProgram.tupleBytes current)
      (ReadPlan.wordWidth r Q)
      (incidenceSelectedPlan ivar factor indices current.length remaining i)
      (incidenceSelectedPlan ivar factor indices current.length remaining j)
      (CollisionTupleProgram.tupleBytes candidate) =
      numberedIncidenceTest ivar factor indices (.inl (i,j))
        (ReadPlan.completedAt default current remaining candidate) := by
  have hrows : ∀ row ∈ current.map ReadPlan.encodeWord ++ candidate.map ReadPlan.encodeWord,
      row.length = ReadPlan.wordWidth r Q := by
    intro row hrow
    rcases List.mem_append.mp hrow with hrow | hrow <;>
      obtain ⟨word, _, rfl⟩ := List.mem_map.mp hrow <;> exact ReadPlan.encodeWord_length _
  rw [CollisionTupleProgram.tupleBytes, CollisionTupleProgram.tupleBytes,
    CollisionTupleProgram.leafBit_eq_collision _ _ _ hrows, ← List.map_append]
  unfold CollisionStreamProgram.collisionBit
  rw [gather_incidenceSelectedPlan ivar factor indices hi default current candidate remaining hc hr i,
      gather_incidenceSelectedPlan ivar factor indices hi default current candidate remaining hc hr j]
  simp only [CollisionProgram.encodeType_eq_iff, numberedIncidenceTest, incidenceWords_eq_iff]

omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] in
theorem generatedIncidenceLeaves_perm (alphabet : List (Word r Q))
    (indices : List (V ⊕ E)) (hi : ∀ a, a ∈ indices) (default : Word r Q)
    (current : List (Word r Q)) (remaining : List ℕ)
    (hc : indices.length ≤ current.length) (hr : remaining.length ≤ 4) (i j : I) :
    (generatedIncidenceLeaves ivar factor alphabet indices current remaining i j).Perm
      ((CoefficientSearch.tuples alphabet 4).map fun candidate =>
        numberedIncidenceTest ivar factor indices (.inl (i,j))
          (ReadPlan.completedAt default current remaining (List.ofFn candidate))) := by
  let test := CollisionTupleProgram.leafBit (CollisionTupleProgram.tupleBytes current)
    (ReadPlan.wordWidth r Q)
    (incidenceSelectedPlan ivar factor indices current.length remaining i)
    (incidenceSelectedPlan ivar factor indices current.length remaining j)
  have h := (CollisionGenerateRefinement.generated_word_perm alphabet 4).map test
  have heq : ((CoefficientSearch.tuples alphabet 4).map
      (fun candidate => CollisionTupleProgram.tupleBytes (List.ofFn candidate))).map test =
      (CoefficientSearch.tuples alphabet 4).map (fun candidate =>
        numberedIncidenceTest ivar factor indices (.inl (i,j))
          (ReadPlan.completedAt default current remaining (List.ofFn candidate))) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro candidate _
    exact incidence_leafBit_eq ivar factor indices hi default current _ remaining hc
      (by simpa using hr) i j
  rw [heq] at h
  have hrev := List.reverse_perm
    ((TupleProgram.powerRows (alphabet.map ReadPlan.encodeWord) 4 [[]]).map test)
  simpa only [generatedIncidenceLeaves, CollisionTupleProgram.streamed_eq_reverse_map,
    List.append_nil] using hrev.trans h

omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] in
theorem numberedIncidenceTest_currentArray (indices : List (V ⊕ E))
    (hi : ∀ a, a ∈ indices) (default : Word r Q) (fixed candidate : List (Word r Q))
    (remaining : List ℕ) (hn : remaining.Nodup) (hr : remaining.length ≤ candidate.length)
    (z : ScoreTerm I V Q) :
    numberedIncidenceTest ivar factor indices z
      (ReadPlan.completedAt default (ReadPlan.currentArray default indices.length fixed)
        remaining candidate) =
    numberedIncidenceTest ivar factor indices z
      (ReadPlan.applyChoices (decode default fixed)
        (PaddedCompletion.paddedIndices remaining 4) candidate) := by
  let _ : BEq (V ⊕ E) := instBEqOfDecidableEq
  have heq : (fun a : V ⊕ E => ReadPlan.completedAt default
        (ReadPlan.currentArray default indices.length fixed) remaining candidate
        (indexCode indices a)) =
      (fun a => ReadPlan.applyChoices (decode default fixed)
        (PaddedCompletion.paddedIndices remaining 4) candidate (indexCode indices a)) := by
    funext a
    unfold PaddedCompletion.paddedIndices
    rw [ReadPlan.applyChoices_padding, ReadPlan.applyChoices_real default _ _ _ hn hr]
    unfold ReadPlan.completedAt
    split_ifs
    · rfl
    · exact ReadPlan.currentArray_getD default indices.length fixed _
        (List.idxOf_lt_length_iff.mpr (hi _))
  cases z with
  | inl p => simp only [numberedIncidenceTest, heq]
  | inr p => rfl

omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] in
theorem generatedIncidencePair_perm (alphabet : List (Word r Q))
    (indices : List (V ⊕ E)) (hi : ∀ a, a ∈ indices) (default : Word r Q)
    (fixed : List (Word r Q)) (remaining : List ℕ) (hn : remaining.Nodup) (i j : I) :
    (generatedIncidenceLeaves ivar factor alphabet indices
      (ReadPlan.currentArray default indices.length fixed)
      (active (numberedScoreSupport (Q := Q) ivar factor indices (.inl (i,j))) remaining) i j).Perm
      (incidenceCompletionLeaves ivar factor alphabet indices (.inl (i,j)) remaining
        (decode default fixed)) := by
  let support := numberedScoreSupport (Q := Q) ivar factor indices (.inl (i,j))
  have hlen : (active support remaining).length ≤ 4 :=
    numberedActive_length_le ivar factor indices (.inl (i,j)) remaining hn
  have h := generatedIncidenceLeaves_perm ivar factor alphabet indices hi default
    (ReadPlan.currentArray default indices.length fixed) (active support remaining)
    (by simp) hlen i j
  have heq : ((CoefficientSearch.tuples alphabet 4).map fun candidate =>
      numberedIncidenceTest ivar factor indices (.inl (i,j))
        (ReadPlan.completedAt default (ReadPlan.currentArray default indices.length fixed)
          (active support remaining) (List.ofFn candidate))) =
      incidenceCompletionLeaves ivar factor alphabet indices (.inl (i,j)) remaining
        (decode default fixed) := by
    unfold incidenceCompletionLeaves PaddedCompletion.paddedLeaves
    rw [ReadPlan.leaves_eq_tuples, PaddedCompletion.paddedIndices_length _ _ hlen]
    apply congrArg (fun f => (CoefficientSearch.tuples alphabet 4).map f)
    funext candidate
    exact numberedIncidenceTest_currentArray ivar factor indices hi default fixed _ _
      (hn.filter _) (by simpa [active] using hlen) _
  rw [heq] at h
  exact h

omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] in
theorem generatedIncidencePair_count (alphabet : List (Word r Q))
    (indices : List (V ⊕ E)) (hi : ∀ a, a ∈ indices) (default : Word r Q)
    (fixed : List (Word r Q)) (remaining : List ℕ) (hn : remaining.Nodup) (i j : I) :
    PaddedCompletion.trueCount (generatedIncidenceLeaves ivar factor alphabet indices
      (ReadPlan.currentArray default indices.length fixed)
      (active (numberedScoreSupport (Q := Q) ivar factor indices (.inl (i,j))) remaining) i j) =
      scaledCount alphabet (fun η => PackingProgram.incidenceIndicator ivar factor
        (.inl (i,j)) (fun a => η (indexCode indices a)))
        (numberedScoreSupport (Q := Q) ivar factor indices (.inl (i,j))) 4 remaining
        (decode default fixed) := by
  rw [← incidenceCompletionLeaves_count]
  exact ((generatedIncidencePair_perm ivar factor alphabet indices hi default fixed
    remaining hn i j).filter id).length_eq

end Plans
end SubexponentialSAT.SqrtLog.Packing

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingCompletionScore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The primitive raw-plan candidate score equals the packing incidence counter. -/
namespace SubexponentialSAT.SqrtLog.Packing
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.LocalExpectation SubexponentialSAT.Subexp.LocalExpectation
open SubexponentialSAT.Subexp

section Scores
variable {I V E : Type*} [Fintype I] [Fintype V] [Fintype E]
  [DecidableEq I] [DecidableEq V] [DecidableEq E]
variable (ivar : I → V) (factor : I → E) {r Q : ℕ}

def incidenceScorerContext (alphabet : List (Word r Q)) (indices : List (V ⊕ E))
    (default : Word r Q) (fixed : List (Word r Q)) : PairScoreProgram.Context where
  current := (ReadPlan.currentArray default indices.length fixed).map ReadPlan.encodeWord
  width := List.replicate (ReadPlan.wordWidth r Q) true
  alphabet := alphabet.map ReadPlan.encodeWord
  depth := List.replicate 4 true

def incidenceScorerPlan (indices : List (V ⊕ E)) (remaining : List ℕ)
    (pair : I × I) : PairScoreProgram.PlanPair :=
  let activeIndices := active (numberedScoreSupport (Q := Q) ivar factor indices (.inl pair)) remaining
  (incidenceSelectedPlan ivar factor indices indices.length activeIndices pair.1,
   incidenceSelectedPlan ivar factor indices indices.length activeIndices pair.2)

end Scores
end SubexponentialSAT.SqrtLog.Packing

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingCallerProgramBoundsBasic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PackingCallerProgram.Bounds
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open PackingLoaderProgram PackingIncidenceInput

theorem words_bits (p : Problem) (a : Word p.r p.Q) (tail : List (Word p.r p.Q)) :
    ((p.words a tail).map ReadPlan.encodeWord).flatten.length=(p.n+p.factors)*(p.Q*p.r) := by
  rw [ScoreBuilderInputBounds.encodedWords_length,p.words_length]
  rfl

end SubexponentialSAT.SqrtLog.PackingCallerProgram.Bounds

end OAI.Algorithms
end


