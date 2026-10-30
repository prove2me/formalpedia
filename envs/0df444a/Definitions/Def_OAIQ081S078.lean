-- Prove2me | Definitions.Def_OAIQ081S078
-- name    : OAIQ081S078
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T22:06:31.631893+00:00
-- url     : https://prove2.me/theorems/51a80d3f-0612-4ac6-be20-64b3b784b5c5
-- title:
--   Definitions bundle OAIQ081S078 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 96 declarations of OpenAI's Lean: 49 definitions, 1 instance and 46 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.OuterQuery.Count.rawHashes`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.headEnergy`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingHeadIncremental.collision`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingHeadIncremental.pairCount`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInput.Emit.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInput.Emit.copied`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInput.Emit.data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInput.Emit.frame`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInput.Emit.framed`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInput.Emit.plan`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInput.Emit.recorded`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInput.Install.plans`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInput.Rows.prefixes`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInput.Rows.recordPrefix`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInput.Step.output`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingWeightProgram.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingWeightProgram.shift`, `OAI.Algorithms.SubexponentialSAT.Subexp.ActivePlanProgram.member`, `OAI.Algorithms.SubexponentialSAT.Subexp.ActivePlanProgram.membershipCall`, `OAI.Algorithms.SubexponentialSAT.Subexp.AssignmentRecordViews.first`, `OAI.Algorithms.SubexponentialSAT.Subexp.AssignmentRecordViews.firstProgram`, `OAI.Algorithms.SubexponentialSAT.Subexp.CandidateScoreProgram.emitScore`, `OAI.Algorithms.SubexponentialSAT.Subexp.CollisionGenerateProgram.Data`, `OAI.Algorithms.SubexponentialSAT.Subexp.CollisionStreamProgram.collisionBit`, `OAI.Algorithms.SubexponentialSAT.Subexp.MinimumProgram.Invariant`, `OAI.Algorithms.SubexponentialSAT.Subexp.MinimumProgram.afterCleanup`, `OAI.Algorithms.SubexponentialSAT.Subexp.MinimumProgram.afterClear`, `OAI.Algorithms.SubexponentialSAT.Subexp.MinimumProgram.afterCopy`, `OAI.Algorithms.SubexponentialSAT.Subexp.MinimumProgram.afterIncrement`, `OAI.Algorithms.SubexponentialSAT.Subexp.MinimumProgram.afterInitialize`, `OAI.Algorithms.SubexponentialSAT.Subexp.MinimumProgram.afterReplace`, `OAI.Algorithms.SubexponentialSAT.Subexp.MinimumProgram.best`, `OAI.Algorithms.SubexponentialSAT.Subexp.MinimumProgram.index`, `OAI.Algorithms.SubexponentialSAT.Subexp.MinimumProgram.inputState`, `OAI.Algorithms.SubexponentialSAT.Subexp.PairPreparationProgram.seedBytes`, `OAI.Algorithms.SubexponentialSAT.Subexp.PairScoreProgram.cleared`, `OAI.Algorithms.SubexponentialSAT.Subexp.SelectorPairProgram.buildPayload`, `OAI.Algorithms.SubexponentialSAT.Subexp.SelectorPairProgram.emitPayload`, `OAI.Algorithms.SubexponentialSAT.Subexp.SelectorPairProgram.framePair`, `OAI.Algorithms.SubexponentialSAT.Subexp.SequentialProgram.ScoreBuilderRefines` and 9 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLog_OuterQueryCountCore`, `SubexponentialSAT_SqrtLog_PackingHeadIncrementalPair`, `SubexponentialSAT_SqrtLog_PackingIncidenceInputEmit`, `SubexponentialSAT_SqrtLog_PackingIncidenceInputInstall`, `SubexponentialSAT_SqrtLog_PackingIncidenceInputNative`, `SubexponentialSAT_SqrtLog_PackingIncidenceInputSemantics`, `SubexponentialSAT_SqrtLog_PackingWeightProgramBasic`, `SubexponentialSAT_SqrtLog_PackingWordBalance`, `SubexponentialSAT_SqrtLog_PackingWords`, `SubexponentialSAT_SubexpIncidencePlanPrimitives`, `SubexponentialSAT_SubexpIncidencePlanScan`, `SubexponentialSAT_SubexpPlanAlphabetEmit`, `SubexponentialSAT_SubexpScopeMembershipProgram`, `SubexponentialSAT_Subexp_ActivePlanProgram`, `SubexponentialSAT_Subexp_AssignmentRecordViews`, `SubexponentialSAT_Subexp_CandidateScoreProgram`, `SubexponentialSAT_Subexp_CollisionGenerateProgram`, `SubexponentialSAT_Subexp_CollisionStreamProgram`, `SubexponentialSAT_Subexp_CollisionTupleProgram`, `SubexponentialSAT_Subexp_MinimumProgram`, `SubexponentialSAT_Subexp_PackingExtractionBounds`, `SubexponentialSAT_Subexp_PackingLeftovers`, `SubexponentialSAT_Subexp_PairPreparationProgram`, `SubexponentialSAT_Subexp_PairScoreBounds`, `SubexponentialSAT_Subexp_PairScoreProgram`, `SubexponentialSAT_Subexp_SelectorPairProgram`, `SubexponentialSAT_Subexp_SequentialProgram`, `SubexponentialSAT_Subexp_SequentialStep`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S045`, `OAIQ081S046`, `OAIQ081S047`, `OAIQ081S050`, `OAIQ081S051`, `OAIQ081S052`, `OAIQ081S053`, `OAIQ081S055`, `OAIQ081S056`, `OAIQ081S058`, `OAIQ081S060`, `OAIQ081S061` and `OAIQ081S062` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S095`, `OAIQ081S096`, `OAIQ081S097` and `OAIQ081S098`; the statements `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProducedHeads.problem_computed_energies`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProducedHeads.source_max_le_of_energy` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.incidence_mean_jointScore_le`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProducedHeads.problem_computed_energies`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProducedHeads.problem_head_max_bound`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProducedHeads.source_max_le_of_energy`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.incidence_mean_jointScore_le` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryRank.packing_coverage`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S045
import Definitions.Def_OAIQ081S046
import Definitions.Def_OAIQ081S047
import Definitions.Def_OAIQ081S050
import Definitions.Def_OAIQ081S051
import Definitions.Def_OAIQ081S052
import Definitions.Def_OAIQ081S053
import Definitions.Def_OAIQ081S055
import Definitions.Def_OAIQ081S056
import Definitions.Def_OAIQ081S058
import Definitions.Def_OAIQ081S060
import Definitions.Def_OAIQ081S061
import Definitions.Def_OAIQ081S062

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpIncidencePlanPrimitives
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed unary-counter and record-emission instructions for incidence plans. -/
namespace SubexponentialSAT.SubexpIncidencePlanPrimitives

open BitProgram StructuredCalls

theorem increment_eval (dst : Fin 10) (d : Data) :
    Eval (increment dst) 2 d (incremented dst d) := by
  have h := (Eval.base (StructuredProgram.Eval.atom (.set (0 : Fin 10) true) d)).seq
    (Eval.base (StructuredProgram.Eval.atom (.push dst (0 : Fin 10)) _))
  simpa [increment, incremented, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, StructuredProgram.State.withPC, execInstr] using h

def emitted (selected : Bool) (bits : List Bool) (d : Data) : Data :=
  ⟨Function.update (Function.update (Function.update d.regs 0 false) 1 true) 4 false,
    Function.update (Function.update d.stacks 1 []) 7
      (if selected then true :: (Encoding.frame bits ++ d.stacks 7) else d.stacks 7)⟩

end SubexponentialSAT.SubexpIncidencePlanPrimitives

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpScopeMembershipProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A concrete scope-membership subroutine for incidence-plan preparation.
The reversed scope record occupies stack 8 and the reversed query stack 2.
Stacks 0,1,3,4 are empty work ports; all remaining stacks are framed.
-/
namespace SubexponentialSAT.SubexpScopeMembershipProgram

open BitProgram StructuredCalls

theorem transfer_eval (d : Data) :
    Eval transfer (3 * (d.stacks 8).length + 3) d (transferred d) :=
  .call _ (ListRegisterProgram.transfer_run 8 0 0 1 (by decide) (by decide) d.regs d.stacks)

theorem clear_eval (i : Fin 10) (d : Data) :
    Eval (clear i) (2 * (d.stacks i).length + 3) d (cleared i d) :=
  .call _ (ListRegisterProgram.clear_run i 0 1 d.regs d.stacks)

end SubexponentialSAT.SubexpScopeMembershipProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpIncidencePlanScan
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed finite scan of encoded scopes. No slot map is supplied as input:
the local slot order is the encounter order of incident factors. -/
namespace SubexponentialSAT.SubexpIncidencePlanScan

open BitProgram StructuredCalls
open SubexpIncidencePlanPrimitives

theorem addDegree_eval (d : Data) (selected : Bool) (h : d.regs 4 = selected) :
    Eval addDegree (if selected then 3 else 1) d (addedDegree selected d) := by
  cases selected
  · exact .ite_false h (.base (.skip d))
  · exact .ite_true h (increment_eval 9 d)

theorem state_data (regs : Fin 10 → Bool) (v j degree : ℕ)
    (source out payload : List Bool) (t pr f : Bool) (src pay : List Bool) :
    RecordPrograms.state ports (data regs v j source out payload degree) t pr f src pay =
      data (Function.update (Function.update (Function.update regs 7 t) 8 pr) 9 f)
        v j src out pay degree := by
  apply congrArg (StructuredProgram.State.mk _)
  funext i
  fin_cases i <;> simp [ ports, data]

end SubexponentialSAT.SubexpIncidencePlanScan

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_CollisionStreamProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# A fixed collision callback with a persistent output stream

The runtime ABI reserves stack 0 for a packed row table, stack 3 for its unary
word width, stacks 8 and 10 for the two read plans, and stack 11 for the output
stream. Stacks 1 and 12 hold the two gathered type encodings. The remaining
stacks are gathering scratch. All sizes, plans, and encoded words are data.

The equality stage below uses the existing fixed equality program, clears its
possibly unconsumed input suffixes, and pushes one collision bit. In particular,
an early mismatch cannot leave stale type bytes in the next callback's scratch.
-/

namespace SubexponentialSAT.Subexp.CollisionStreamProgram

open BitProgram StackRoutines StructuredCalls

def collisionBit (rows : List (List Bool)) (left right : List ℕ) : Bool :=
  decide (GatherProgram.gathered rows left = GatherProgram.gathered rows right)

end SubexponentialSAT.Subexp.CollisionStreamProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_CollisionTupleProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Streaming collisions from framed runtime tuples

The current word array and selected read plans are preserved. Each parsed
tuple is appended to the current array by actual transfer/copy routines, then
the fixed collision callback gathers the two types and emits one bit.
-/

namespace SubexponentialSAT.Subexp.CollisionTupleProgram

open BitProgram StackRoutines StructuredCalls

theorem byteGather_flatten (rows : List (List Bool)) (width : ℕ)
    (hrows : ∀ row ∈ rows, row.length = width) (plan : List ℕ) :
    byteGather rows.flatten width plan = GatherProgram.gathered rows plan := by
  unfold byteGather GatherProgram.gathered
  apply congrArg (fun f : ℕ → List Bool => plan.flatMap f)
  funext i
  exact slice_flatten rows width hrows i

theorem leafBit_eq_collision (current candidate : List (List Bool)) (width : ℕ)
    (hrows : ∀ row ∈ current ++ candidate, row.length = width) (left right : List ℕ) :
    leafBit current.flatten width left right candidate.flatten =
      CollisionStreamProgram.collisionBit (current ++ candidate) left right := by
  unfold leafBit CollisionStreamProgram.collisionBit
  rw [← List.flatten_append, byteGather_flatten _ _ hrows, byteGather_flatten _ _ hrows]

end SubexponentialSAT.Subexp.CollisionTupleProgram

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

abbrev Data := StructuredProgram.State 10 20

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

def cleared (src : Fin 26) (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, clearStacks src d.stacks⟩

end SubexponentialSAT.Subexp.PairScoreProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PairScoreBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Closed bounds for the actual tuple generator and pair scorer

All costs below are the explicit bounds attached to proved executions of the
fixed programs.  The tuple recurrence is bounded from its actual list sizes;
no scalar-operation or callback-cost oracle is assumed.
-/

namespace SubexponentialSAT.Subexp.PairScoreBounds

open BitProgram

theorem tupleCost_eq (alphabet : List (List Bool)) (row : List Bool) :
    TupleProgram.tupleCost alphabet row =
      (12 * alphabet.length + 2) * row.length +
        25 * volume alphabet + 36 * alphabet.length + 18 := by
  have hb : RecordPrograms.budget (fun x => 5 * x.length + 12 * row.length + 15) alphabet =
      (5 + 6) * volume alphabet + (12 * row.length + 15 + 7) * alphabet.length := by
    simpa only [Nat.add_assoc] using budget_linear alphabet 5 (12 * row.length + 15)
  rw [TupleProgram.tupleCost, ProgramEncoding.encodeRecords_length, hb]
  dsimp only [volume]
  ring

theorem expansionCost_eq (rows alphabet : List (List Bool)) :
    TupleProgram.expansionCost rows alphabet =
      3 + (12 * alphabet.length + 8) * volume rows +
        (25 * volume alphabet + 36 * alphabet.length + 25) * rows.length := by
  unfold TupleProgram.expansionCost
  have hf : TupleProgram.tupleCost alphabet = fun row =>
      (12 * alphabet.length + 2) * row.length +
        (25 * volume alphabet + 36 * alphabet.length + 18) := by
    funext row
    simpa only [Nat.add_assoc] using tupleCost_eq alphabet row
  rw [hf, budget_linear]
  ring

end SubexponentialSAT.Subexp.PairScoreBounds

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_OuterQueryCountCore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Raw tuple rows and decoded selector rows have identical acceptance,
including repeated clause IDs and zero coefficients. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.OuterQuery.Count
open LeafProgram
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {n m : ℕ}

def rawHashes (source : Fin m → List (SAT.Literal (Fin n)))
    (rows : List (List (Fin m × ZMod 3))) : List (SparseRow (Fin n) (ZMod 3)) :=
  rows.map (fun row => row.map (fun term => (term.2,source term.1)))

end SubexponentialSAT.SqrtLog.OuterQuery.Count

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingWords
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.compatibleDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.spectatorsAgreeDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.instDecidableAnchorValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual shared-head/shared-factor words on an arbitrary finite incidence set. -/
namespace SubexponentialSAT.SqrtLog.Packing
open scoped BigOperators
open SubexponentialSAT.Variance SubexponentialSAT.MulticolorTypes

noncomputable section

section Incidences
variable {I V E : Type*} [Fintype I] [Fintype V] [Fintype E]
  [DecidableEq I] [DecidableEq V] [DecidableEq E]
variable (ivar : I → V) (factor : I → E) {r Q : ℕ}

omit [Fintype V] [Fintype E] [DecidableEq I] in
@[simp] theorem mem_dependencySet (i j : I) :
    j ∈ dependencySet ivar factor i ↔
      ivar j = ivar i ∨ factor j = factor i := by simp [dependencySet]

variable [NeZero r]

instance nonemptyUniversal : Nonempty (UniversalType r Q 1) :=
  ⟨⟨fun _ => 0, fun _ _ => 0⟩⟩

/-- Joint head energy at all interpolation nodes. -/
def headEnergy (ω : WordAssignment V E r Q) : ℚ :=
  ∑ t : Fin Q, energy (fun v : V => ω (.inl v) t)

end Incidences
end
end SubexponentialSAT.SqrtLog.Packing

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingHeadIncrementalPair
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact uniform-completion values of one head-collision term. -/
namespace SubexponentialSAT.SqrtLog.PackingHeadIncremental

open SubexponentialSAT.MulticolorTypes SubexponentialSAT.LocalExpectation SubexponentialSAT.Subexp.LocalExpectation
open scoped BigOperators

variable {r Q : ℕ}

def collision (t : Fin Q) (a b : ℕ) (ω : ℕ → Word r Q) : ℚ :=
  if ω a t = ω b t then 1 else 0

def pairCount (alphabet : List (Word r Q)) (remaining : List ℕ)
    (t : Fin Q) (a b : ℕ) (ω : ℕ → Word r Q) : ℕ :=
  scaledCount alphabet (fun η => if η a t = η b t then 1 else 0)
    {a, b} 4 remaining ω

end SubexponentialSAT.SqrtLog.PackingHeadIncremental

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpPlanAlphabetEmit
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Physical double framing for one vertex-plan alphabet entry. -/
namespace SubexponentialSAT.SubexpPlanAlphabetEmit

open BitProgram StructuredCalls Subexp.TupleProgram

theorem transfer_eval (d : Data) :
    Eval transfer (3*(d.stacks 0).length+3) d (transferred d) :=
  .call _ (ListRegisterProgram.transfer_run 0 1 0 1 (by decide) (by decide) d.regs d.stacks)

abbrev command : Cmd 3 3 := .seq transfer (.seq (pushConst 0 0 false)
  (.seq (escape innerPorts) (.seq transfer (.seq (pushConst 2 0 false)
    (.seq (escape outerPorts) (pushConst 2 0 true))))))

abbrev program : Program 3 3 (size command+1) := compiled command 0 2

end SubexponentialSAT.SubexpPlanAlphabetEmit

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingIncidenceInputEmit
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed writer for one double-framed two-address incidence plan. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput.Emit
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

def data (r : Fin 3 → Bool) (head factor tmp plan scratch out : List Bool) : Data :=
  ⟨r, ![head,factor,tmp,plan,scratch,out]⟩

def recorded (d : Data) (bits : List Bool) : Data :=
  ⟨![true,false,d.regs 2], Function.update (Function.update d.stacks 2 []) 3
    (true :: (Encoding.frame bits ++ d.stacks 3))⟩

def copied (src : Fin 6) (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.copyStacks src 2 d.stacks⟩
theorem copy_eval (src : Fin 6) (h2 : src ≠ 2) (h4 : src ≠ 4)
    (d : Data) (ht : d.stacks 4 = []) :
    Eval (copy src) (7*(d.stacks src).length+5) d (copied src d) :=
  TupleProgram.copy_eval src 2 4 0 1 h2 h4 (by decide) (by decide) d ht

abbrev frame : Cmd 3 6 := .call
  (ProgramLinking.liftProgram SubexpPlanAlphabetEmit.program id framePorts)
def framed (d : Data) (rf : Fin 3 → Bool) (bits : List Bool) : Data :=
  ⟨rf, Function.update (Function.update (Function.update d.stacks 3 []) 2 []) 5
    (true :: Encoding.frame (Encoding.frame bits) ++ d.stacks 5)⟩

abbrev command : Cmd 3 6 := .seq (TupleProgram.pushConst 3 0 false)
  (.seq (copy 1) (.seq record (.seq (copy 0) (.seq record frame))))
def plan (h f : ℕ) : List Bool := CollisionStreamProgram.planBytes [h,f]

end SubexponentialSAT.SqrtLog.PackingIncidenceInput.Emit

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

abbrev emitScore : Cmd 16 36 :=
  .seq (TupleProgram.pushConst 35 0 true)
    (.seq reverseWriter (TupleProgram.pushConst 35 0 false))

end SubexponentialSAT.Subexp.CandidateScoreProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_ActivePlanProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Computing the active completion positions

A fixed program filters a runtime list of unary seed positions. It retains a
position precisely when it is at least the runtime threshold and belongs to
the runtime pair read plan. The plan and threshold are preserved. Applying the
program to the complete ascending seed list gives a duplicate-free completion
plan in ascending order.
-/

namespace SubexponentialSAT.Subexp.ActivePlanProgram

open BitProgram StructuredCalls StackRoutines

abbrev membershipCall : Cmd 10 12 :=
  .call (ProgramLinking.liftProgram ExecCNFMembership.membershipProgram low7 low5)

abbrev member : Cmd 10 12 :=
  .seq (copy 6 0 4) (.seq membershipCall (.seq (clear 0) (clear 1)))

end SubexponentialSAT.Subexp.ActivePlanProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_SelectorPairProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!+# Selecting and framing both read plans of a vertex pair

The two selector-map calls share a persistent table. Stack 6 initially holds
the left query records and stack 9 the right query records. Stack 11 is an
existing record accumulator. The result prepends one record whose payload is
`frame leftPlanBytes ++ frame rightPlanBytes`.
-/

namespace SubexponentialSAT.Subexp.SelectorPairProgram

open BitProgram StructuredCalls

abbrev buildPayload : Cmd 8 12 :=
  .seq (.call (StackRoutines.transferProgram 8 9 (0 : Fin 8) 1))
    (.seq (TupleProgram.pushConst 8 0 false)
      (.seq (TupleProgram.escape rightPorts)
        (.seq (TupleProgram.pushConst 8 0 false)
          (TupleProgram.escape leftPorts))))

abbrev emitPayload : Cmd 8 12 :=
  .seq (.call (StackRoutines.transferProgram 8 10 (0 : Fin 8) 1))
    (.seq (TupleProgram.pushConst 11 0 false)
      (.seq (TupleProgram.escape outputPorts) (TupleProgram.pushConst 11 0 true)))

abbrev framePair : Cmd 8 12 := .seq buildPayload emitPayload

end SubexponentialSAT.Subexp.SelectorPairProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PairPreparationProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Preparing all selected pair plans once per assignment step

The fixed program preserves the full seed-index records, original pair
records, seed count, and processed counter. It computes the next cutoff,
builds each pair's actual selection table, and emits selected pair records.
The candidate value is not an input to this preparation phase.
-/

namespace SubexponentialSAT.Subexp.PairPreparationProgram

open BitProgram StructuredCalls StackRoutines

def seedBytes (M : ℕ) : List Bool :=
  ProgramEncoding.encodeRecords ((List.range M).map SelectionTableProgram.unary)

end SubexponentialSAT.Subexp.PairPreparationProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MinimumProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# A fixed program selecting the first minimum unary score

The input is a framed list of prepared unary scores. Scores are represented
by list lengths. The program returns the selected zero-based index in unary.
All control, registers, and stack ports are fixed independently of the input.
-/

namespace SubexponentialSAT.Subexp.MinimumProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.StackRoutines

def afterClear (d : Data) (dst : Fin 8) : Data :=
  ⟨readRegs d.regs 3 4 none, clearStacks dst d.stacks⟩

def afterCopy (d : Data) (src dst : Fin 8) : Data :=
  ⟨readRegs d.regs 3 4 none, copyStacks src dst d.stacks⟩

theorem clear_eval (d : Data) (dst : Fin 8) :
    Eval (clear dst) (2 * (d.stacks dst).length + 3) d (afterClear d dst) :=
  .call _ (ListRegisterProgram.clear_run dst 3 4 d.regs d.stacks)

theorem copy_eval (d : Data) (src dst : Fin 8)
    (hsd : src ≠ dst) (hs : src ≠ 5) (hd : (5 : Fin 8) ≠ dst)
    (htmp : d.stacks 5 = []) :
    Eval (copy src dst) (7 * (d.stacks src).length + 5) d (afterCopy d src dst) :=
  .call _ (ListRegisterProgram.copy_run src dst 5 3 4 hsd hs hd
    (by decide) d.regs d.stacks htmp)

theorem embed_restrict (d : Data) :
    embedState compareRegs compareStacks d
      ⟨fun i => d.regs (compareRegs i), fun i => d.stacks (compareStacks i)⟩ = d := by
  apply state_ext
  · funext j
    by_cases h : ∃ i, compareRegs i = j
    · obtain ⟨i, rfl⟩ := h
      exact embedState_register _ _ _ _ compareRegs_injective i
    · exact embedState_register_frame _ _ _ _ j h
  · funext j
    by_cases h : ∃ i, compareStacks i = j
    · obtain ⟨i, rfl⟩ := h
      exact embedState_stack _ _ _ _ compareStacks_injective i
    · exact embedState_stack_frame _ _ _ _ j h

/-- A genuine call to the destructive comparator, including all required
framing and bounds on the two residual scratch stacks. -/
theorem compare_eval (d : Data) :
    ∃ n ≤ 4 * min (d.stacks 3).length (d.stacks 4).length + 6, ∃ e : Data,
      Eval (.call comparator) n d e ∧
      e.regs 8 = decide ((d.stacks 3).length ≤ (d.stacks 4).length) ∧
      (∀ j : Fin 9, j.val < 5 → e.regs j = d.regs j) ∧
      (∀ j : Fin 8, j ≠ 3 → j ≠ 4 → e.stacks j = d.stacks j) ∧
      (e.stacks 3).length ≤ (d.stacks 3).length ∧
      (e.stacks 4).length ≤ (d.stacks 4).length := by
  obtain ⟨n, hn, c, ht, hp, hout⟩ :=
    UnaryCompare.runs (fun i => d.regs (compareRegs i)) (d.stacks 3) (d.stacks 4)
  let a : State 4 2 :=
    ⟨fun i => d.regs (compareRegs i), fun i => d.stacks (compareStacks i)⟩
  let b : State 4 2 := ⟨c.regs, c.stacks⟩
  let e := embedState compareRegs compareStacks d b
  have ha : embedState compareRegs compareStacks d a = d := embed_restrict d
  have ht' : Trace UnaryCompare.program n
      (a.withPC (some UnaryCompare.program.entry)) (b.withPC none) := by
    have hb : b.withPC none = c := by
      cases c
      simp_all [b, StructuredProgram.State.withPC]
    rw [hb]
    convert ht using 1
    all_goals try with_reducible_and_instances rfl
    apply congrArg (fun stk =>
      (⟨some 0, fun i => d.regs (compareRegs i), stk⟩ : Cfg 4 2 7))
    first | done | (funext i; fin_cases i <;> rfl)
  have he := eval_call_lifted UnaryCompare.program compareRegs compareStacks d
    compareRegs_injective compareStacks_injective ht'
  refine ⟨n, hn, e, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [ha, comparator] using he
  · change (embedState compareRegs compareStacks d b).regs (compareRegs 3) = _
    rw [embedState_register _ _ _ _ compareRegs_injective]
    exact hout
  · intro j hj
    apply embedState_register_frame
    rintro ⟨i, hi⟩
    have hv := congrArg Fin.val hi
    change 5 + i.val = j.val at hv
    omega
  · intro j h3 h4
    apply embedState_stack_frame
    rintro ⟨i, hi⟩
    fin_cases i <;> simp_all [compareStacks]
  · change ((embedState compareRegs compareStacks d b).stacks (compareStacks 0)).length ≤ _
    rw [embedState_stack _ _ _ _ compareStacks_injective]
    exact UnaryCompare.trace_length_le ht 0
  · change ((embedState compareRegs compareStacks d b).stacks (compareStacks 1)).length ≤ _
    rw [embedState_stack _ _ _ _ compareStacks_injective]
    exact UnaryCompare.trace_length_le ht 1

def afterIncrement (d : Data) : Data :=
  ⟨Function.update d.regs 3 false, Function.update d.stacks 6 (false :: d.stacks 6)⟩

theorem increment_eval (d : Data) : Eval increment 2 d (afterIncrement d) := by
  have h := Eval.seq (Eval.base (StructuredProgram.Eval.atom (.set 3 false) d))
    (Eval.base (StructuredProgram.Eval.atom (.push 6 3) _))
  simpa [increment, atom, afterIncrement, StructuredProgram.Atom.eval,
    StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg,
    StructuredProgram.State.withPC, execInstr] using h

def afterCleanup (d : Data) : Data :=
  afterIncrement (afterClear (afterClear (afterClear d 1) 3) 4)

theorem cleanup_eval (d : Data) :
    Eval cleanup
      (2 * (d.stacks 1).length + 2 * (d.stacks 3).length +
        2 * (d.stacks 4).length + 11) d (afterCleanup d) := by
  have h := Eval.seq (clear_eval d 1)
    (Eval.seq (clear_eval (afterClear d 1) 3)
      (Eval.seq (clear_eval (afterClear (afterClear d 1) 3) 4)
        (increment_eval (afterClear (afterClear (afterClear d 1) 3) 4))))
  convert h using 1 <;> simp [ afterCleanup, afterClear, clearStacks] ; omega

def afterReplace (d : Data) : Data :=
  afterCopy (afterClear (afterCopy (afterClear d 2) 1 2) 7) 6 7

theorem replaceBest_eval (d : Data) (htmp : d.stacks 5 = []) :
    Eval replaceBest
      (2 * (d.stacks 2).length + 7 * (d.stacks 1).length +
        2 * (d.stacks 7).length + 7 * (d.stacks 6).length + 16)
      d (afterReplace d) := by
  have h1 := clear_eval d 2
  have h2 := copy_eval (afterClear d 2) 1 2 (by decide) (by decide) (by decide)
    (by simpa [afterClear, clearStacks] using htmp)
  have h3 := clear_eval (afterCopy (afterClear d 2) 1 2) 7
  have h4 := copy_eval (afterClear (afterCopy (afterClear d 2) 1 2) 7) 6 7
    (by decide) (by decide) (by decide)
    (by simpa [afterClear, afterCopy, clearStacks, copyStacks] using htmp)
  convert Eval.seq h1 (Eval.seq h2 (Eval.seq h3 h4)) using 1 <;>
    simp [ afterReplace, afterClear, afterCopy, clearStacks, copyStacks] ; omega

/-- Invariants at record boundaries. The score bound is independent of how
many records remain, because the stored best score only decreases. -/
def Invariant (M : ℕ) (d : Data) : Prop :=
  d.stacks 3 = [] ∧ d.stacks 4 = [] ∧ d.stacks 5 = [] ∧
    (d.stacks 2).length ≤ M ∧ (d.stacks 7).length ≤ (d.stacks 6).length

def best (d : Data) : ℕ × ℕ := ((d.stacks 2).length, (d.stacks 7).length)
def index (d : Data) : ℕ := (d.stacks 6).length

theorem callback_eval_raw (M : ℕ) (d : Data) (hd : Invariant M d) :
    ∃ n ≤ 100 * (M + (d.stacks 1).length + index d + 1), ∃ e : Data,
      Eval callback n d e ∧ Invariant M e ∧
      index e = index d + 1 ∧
      best e = pick (best d) ((d.stacks 1).length, index d) ∧
      e.stacks 1 = [] ∧ e.stacks 0 = d.stacks 0 ∧
      (∀ j : Fin 9, j.val < 3 → e.regs j = d.regs j) := by
  obtain ⟨hd3, hd4, hd5, hM, hi⟩ := hd
  let a := afterCopy d 2 3
  let b := afterCopy a 1 4
  have hcopy1 := copy_eval d 2 3 (by decide) (by decide) (by decide) hd5
  have hcopy2 := copy_eval a 1 4 (by decide) (by decide) (by decide)
    (by simpa [a, afterCopy, copyStacks] using hd5)
  obtain ⟨n, hn, e, he, hout, hr, hs, h3, h4⟩ := compare_eval b
  have hb3 : b.stacks 3 = d.stacks 2 := by simp [b, a, afterCopy, copyStacks, hd3]
  have hb4 : b.stacks 4 = d.stacks 1 := by simp [b, a, afterCopy, copyStacks, hd4]
  simp only [hb3, hb4] at hn hout h3 h4
  have hef (j : Fin 8) (hj3 : j ≠ 3) (hj4 : j ≠ 4) : e.stacks j = d.stacks j := by
    rw [hs j hj3 hj4]
    simp [b, a, afterCopy, copyStacks, hj3, hj4]
  have her (j : Fin 9) (hj : j.val < 3) : e.regs j = d.regs j := by
    rw [hr j (by omega)]
    have hj3 : j ≠ 3 := by intro h; subst j; omega
    have hj4 : j ≠ 4 := by intro h; subst j; omega
    simp [b, a, afterCopy, readRegs, hj3, hj4]
  have he0 := hef 0 (by decide) (by decide)
  have he1 := hef 1 (by decide) (by decide)
  have he2 := hef 2 (by decide) (by decide)
  have he5 : e.stacks 5 = [] := by rw [hef 5 (by decide) (by decide), hd5]
  have he6 := hef 6 (by decide) (by decide)
  have he7 := hef 7 (by decide) (by decide)
  let k := if (d.stacks 2).length ≤ (d.stacks 1).length then e else afterReplace e
  have hbranch : ∃ m ≤ 2 * (d.stacks 2).length + 7 * (d.stacks 1).length +
      2 * (d.stacks 7).length + 7 * (d.stacks 6).length + 17,
      Eval (.ite 8 (.base .skip) replaceBest) m e k := by
    by_cases hle : (d.stacks 2).length ≤ (d.stacks 1).length
    · refine ⟨1, by omega, ?_⟩
      simpa [k, hle] using
        (Eval.ite_true (by simpa [hle] using hout) (Eval.base (.skip e)))
    · refine ⟨2 * (e.stacks 2).length + 7 * (e.stacks 1).length +
        2 * (e.stacks 7).length + 7 * (e.stacks 6).length + 16 + 1, ?_, ?_⟩
      · simp [he1, he2, he6, he7]
      · simpa [k, hle] using
          (Eval.ite_false (by simpa [hle] using hout) (replaceBest_eval e he5))
  obtain ⟨m, hm, hbranch⟩ := hbranch
  have hk0 : k.stacks 0 = d.stacks 0 := by
    by_cases hle : (d.stacks 2).length ≤ (d.stacks 1).length <;>
      simp [k, hle, afterReplace, afterClear, afterCopy, clearStacks, copyStacks, he0]
  have hk1 : k.stacks 1 = d.stacks 1 := by
    by_cases hle : (d.stacks 2).length ≤ (d.stacks 1).length <;>
      simp [k, hle, afterReplace, afterClear, afterCopy, clearStacks, copyStacks, he1]
  have hk3 : k.stacks 3 = e.stacks 3 := by
    by_cases hle : (d.stacks 2).length ≤ (d.stacks 1).length <;>
      simp [k, hle, afterReplace, afterClear, afterCopy, clearStacks, copyStacks]
  have hk4 : k.stacks 4 = e.stacks 4 := by
    by_cases hle : (d.stacks 2).length ≤ (d.stacks 1).length <;>
      simp [k, hle, afterReplace, afterClear, afterCopy, clearStacks, copyStacks]
  have hk5 : k.stacks 5 = [] := by
    by_cases hle : (d.stacks 2).length ≤ (d.stacks 1).length <;>
      simp [k, hle, afterReplace, afterClear, afterCopy, clearStacks, copyStacks, he5]
  have hk6 : k.stacks 6 = d.stacks 6 := by
    by_cases hle : (d.stacks 2).length ≤ (d.stacks 1).length <;>
      simp [k, hle, afterReplace, afterClear, afterCopy, clearStacks, copyStacks, he6]
  have hkM : (k.stacks 2).length ≤ M := by
    by_cases hle : (d.stacks 2).length ≤ (d.stacks 1).length
    · simpa [k, hle, he2] using hM
    · simp [k, hle, afterReplace, afterClear, afterCopy, clearStacks, copyStacks, he1]
      omega
  have hki : (k.stacks 7).length ≤ (d.stacks 6).length := by
    by_cases hle : (d.stacks 2).length ≤ (d.stacks 1).length
    · simpa [k, hle, he7] using hi
    · simp [k, hle, afterReplace, afterClear, afterCopy, clearStacks, copyStacks, he6]
  have hkb : best k = pick (best d) ((d.stacks 1).length, index d) := by
    by_cases hle : (d.stacks 2).length ≤ (d.stacks 1).length <;>
      simp [k, best, pick, index, hle, afterReplace, afterClear, afterCopy,
        clearStacks, copyStacks, he1, he2, he6, he7]
  have hkr (j : Fin 9) (hj : j.val < 3) : k.regs j = d.regs j := by
    have hj3 : j ≠ 3 := by intro h; subst j; omega
    have hj4 : j ≠ 4 := by intro h; subst j; omega
    by_cases hle : (d.stacks 2).length ≤ (d.stacks 1).length <;>
      simp [k, hle, afterReplace, afterClear, afterCopy, readRegs, hj3, hj4, her j hj]
  have hclean := cleanup_eval k
  let total := (7 * (d.stacks 2).length + 5) +
    ((7 * (a.stacks 1).length + 5) +
      (n + (m + (2 * (k.stacks 1).length + 2 * (k.stacks 3).length +
        2 * (k.stacks 4).length + 11))))
  refine ⟨total, ?_, afterCleanup k, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hn' : n ≤ 4 * (d.stacks 2).length + 6 :=
      hn.trans (by gcongr; exact min_le_left _ _)
    simp only [total, a, afterCopy, copyStacks, Function.update_of_ne (show (1 : Fin 8) ≠ 3 by decide),
      hk1, hk3, hk4, index]
    omega
  · exact Eval.seq hcopy1 (Eval.seq hcopy2 (Eval.seq he (Eval.seq hbranch hclean)))
  · simp [Invariant, afterCleanup, afterIncrement, afterClear, clearStacks, hk5, hk6, hkM]
    omega
  · simp [index, afterCleanup, afterIncrement, afterClear, clearStacks, hk6]
  · simpa [best, afterCleanup, afterIncrement, afterClear, clearStacks] using hkb
  · simp [afterCleanup, afterIncrement, afterClear, clearStacks]
  · simpa [afterCleanup, afterIncrement, afterClear, clearStacks] using hk0
  · intro j hj
    have hj3 : j ≠ 3 := by intro h; subst j; omega
    have hj4 : j ≠ 4 := by intro h; subst j; omega
    simpa [afterCleanup, afterIncrement, afterClear, readRegs, hj3, hj4] using hkr j hj

theorem callback_eval (M : ℕ) (base : Data) (hd : Invariant M base)
    (bits tail : List Bool) :
    ∃ n ≤ 100 * (M + bits.length + index base + 1), ∃ e : Data,
      Invariant M e ∧ index e = index base + 1 ∧
      best e = pick (best base) (bits.length, index base) ∧
      Eval callback n
        (RecordPrograms.state ports base false true false tail bits.reverse)
        (RecordPrograms.state ports e false true false tail []) := by
  let d := RecordPrograms.state ports base false true false tail bits.reverse
  have hi : Invariant M d := by
    simpa [d, Invariant, RecordPrograms.state, ports] using hd
  obtain ⟨n, hn, e, he, hIe, hie, hbe, hp, hs, hr⟩ := callback_eval_raw M d hi
  have heq : RecordPrograms.state ports e false true false tail [] = e := by
    apply RecordPrograms.state_eq_self
    · simpa [d, RecordPrograms.state, ports] using hr 0 (by decide)
    · simpa [d, RecordPrograms.state, ports] using hr 1 (by decide)
    · simpa [d, RecordPrograms.state, ports] using hr 2 (by decide)
    · simpa [d, RecordPrograms.state, ports] using hs
    · exact hp
  refine ⟨n, ?_, e, hIe, ?_, ?_, ?_⟩
  · simpa [d, index, RecordPrograms.state, ports] using hn
  · simpa [d, index, RecordPrograms.state, ports] using hie
  · simpa [d, best, index, RecordPrograms.state, ports] using hbe
  · rwa [heq]

/-- The fixed parser/callback loop visits every record in order. -/
theorem loop_eval (M : ℕ) (records : List (List Bool)) (suffix : List Bool)
    (base : Data) (hd : Invariant M base) :
    ∃ n ≤ scanBudget M (index base) records, ∃ e : Data,
      Invariant M e ∧ index e = index base + records.length ∧
      best e = scan (best base) (index base) records ∧
      Eval (RecordPrograms.loop ports callback) n
        (RecordPrograms.afterTag ports base records suffix)
        (RecordPrograms.state ports e false true false suffix []) := by
  induction records generalizing base with
  | nil =>
      refine ⟨1, by simp [scanBudget], base, hd, by simp, rfl, ?_⟩
      exact Eval.while_false (by simp [RecordPrograms.afterTag])
  | cons bits rest ih =>
      let tail := Encoding.encodeList id rest ++ suffix
      obtain ⟨n, hn, middle, hm, hi, hb, hc⟩ := callback_eval M base hd bits tail
      have hr : Eval (RecordPrograms.reader ports) (6 * bits.length + 4)
          (RecordPrograms.afterTag ports base (bits :: rest) suffix)
          (RecordPrograms.state ports base false true false tail bits.reverse) := by
        simpa [RecordPrograms.afterTag, tail] using
          RecordPrograms.reader_eval ports base bits tail [] true true false
      have hbranch : Eval
          (.ite ports.found (RecordPrograms.atom (.set ports.tag false))
            (RecordPrograms.atom (.pop ports.source ports.tag ports.present))) 2
          (RecordPrograms.state ports middle false true false tail [])
          (RecordPrograms.afterTag ports middle rest suffix) := by
        apply Eval.ite_false (by simp)
        exact RecordPrograms.pop_list_eval ports middle rest suffix false true
      obtain ⟨m, hmb, e, he, hei, heb, her⟩ := ih middle hm
      have hg : (RecordPrograms.afterTag ports base (bits :: rest) suffix).regs ports.tag = true := by
        simp [RecordPrograms.afterTag]
      refine ⟨(6 * bits.length + 4 + (n + 2)) + m + 1, ?_, e, he, ?_, ?_, ?_⟩
      · simp only [scanBudget]
        rw [hi] at hmb
        omega
      · rw [hei, hi, List.length_cons]
        omega
      · rw [heb, hb, hi]
        rfl
      · exact Eval.while_true hg (Eval.seq hr (Eval.seq hc hbranch)) her

theorem iterate_eval (M : ℕ) (records : List (List Bool)) (suffix : List Bool)
    (base : Data) (hd : Invariant M base) (v pr f : Bool) :
    ∃ n ≤ 2 + scanBudget M (index base) records, ∃ e : Data,
      Invariant M e ∧ index e = index base + records.length ∧
      best e = scan (best base) (index base) records ∧
      Eval (RecordPrograms.iterate ports callback) n
        (RecordPrograms.state ports base v pr f (Encoding.encodeList id records ++ suffix) [])
        (RecordPrograms.state ports e false true false suffix []) := by
  obtain ⟨n, hn, e, he, hi, hb, hr⟩ := loop_eval M records suffix base hd
  exact ⟨1 + (1 + n), by omega, e, he, hi, hb,
    Eval.seq (RecordPrograms.set_found_eval ports base v pr f false _ [])
      (Eval.seq (RecordPrograms.pop_list_eval ports base records suffix v pr) hr)⟩

def afterInitialize (d : Data) : Data :=
  afterIncrement (afterClear (afterCopy d 1 2) 1)

theorem initBest_eval (d : Data) (h5 : d.stacks 5 = []) :
    Eval initBest (9 * (d.stacks 1).length + 10) d (afterInitialize d) := by
  have h := Eval.seq (copy_eval d 1 2 (by decide) (by decide) (by decide) h5)
    (Eval.seq (clear_eval (afterCopy d 1 2) 1)
      (increment_eval (afterClear (afterCopy d 1 2) 1)))
  convert h using 1 <;>
    simp [ afterInitialize, afterCopy, copyStacks] ; omega

def inputState (records : List (List Bool)) : Data :=
  RecordPrograms.state ports emptyData false false false
    (ProgramEncoding.encodeRecords records) []

theorem command_eval (first : List Bool) (rest : List (List Bool)) :
    ∃ n ≤ 15 * first.length + 18 + scanBudget first.length 1 rest, ∃ e : Data,
      Eval command n (inputState (first :: rest)) e ∧
      (e.stacks 7).length = (firstMinimum first rest).2 := by
  let source := Encoding.encodeList id rest
  let d := RecordPrograms.state ports emptyData false true false source first.reverse
  let q := afterInitialize d
  have hq : Invariant first.length q := by
    simp [q, d, Invariant, afterInitialize, afterIncrement, afterClear, afterCopy,
      clearStacks, copyStacks, RecordPrograms.state, ports, emptyData]
  have hqi : index q = 1 := by
    simp [q, d, index, afterInitialize, afterIncrement, afterClear, afterCopy,
      clearStacks, copyStacks, RecordPrograms.state, ports, emptyData]
  have hqb : best q = (first.length, 0) := by
    simp [q, d, best, afterInitialize, afterIncrement, afterClear, afterCopy,
      clearStacks, copyStacks, RecordPrograms.state, ports, emptyData]
  have hqq : RecordPrograms.state ports q false true false source [] = q := by
    apply RecordPrograms.state_eq_self <;>
      simp [q, d, afterInitialize, afterIncrement, afterClear, afterCopy, readRegs,
        clearStacks, copyStacks, RecordPrograms.state, ports, emptyData]
  obtain ⟨m, hm, e, _, _, hb, hit⟩ :=
    iterate_eval first.length rest [] q hq false true false
  have hit' : Eval (RecordPrograms.iterate ports callback) m q
      (RecordPrograms.state ports e false true false [] []) := by
    simp only [List.append_nil] at hit
    change Eval _ m (RecordPrograms.state ports q false true false source []) _ at hit
    rwa [hqq] at hit
  have hinit : Eval initBest (9 * first.length + 10) d q := by
    simpa [q, d, RecordPrograms.state, ports] using initBest_eval d
      (by simp [d, RecordPrograms.state, ports, emptyData])
  have hreader : Eval (RecordPrograms.reader ports) (6 * first.length + 4)
      (RecordPrograms.afterTag ports emptyData (first :: rest) []) d := by
    simpa [RecordPrograms.afterTag, d, source] using
      RecordPrograms.reader_eval ports emptyData first source [] true true false
  have htotal := Eval.seq
    (RecordPrograms.set_found_eval ports emptyData false false false false
      (Encoding.encodeList id (first :: rest) ++ []) [])
    (Eval.seq (RecordPrograms.pop_list_eval ports emptyData (first :: rest) [] false false)
      (Eval.seq hreader (Eval.seq hinit hit')))
  refine ⟨1 + (1 + ((6 * first.length + 4) + ((9 * first.length + 10) + m))),
    ?_, RecordPrograms.state ports e false true false [] [], ?_, ?_⟩
  · rw [hqi] at hm
    omega
  · simpa [command, inputState, ProgramEncoding.encodeRecords] using htotal
  · rw [hqi, hqb] at hb
    have hp := congrArg Prod.snd hb
    simpa [best, firstMinimum, RecordPrograms.state, ports] using hp

/-- An actual halting trace, with polynomial cost in the prepared records. -/
theorem program_runsIn (first : List Bool) (rest : List (List Bool)) :
    ∃ e : Data,
      RunsIn program
        (500 * (first.length + (rest.map List.length).sum + rest.length + 1) ^ 2)
        ((inputState (first :: rest)).withPC (some program.entry))
        (e.withPC none) ∧
      (e.stacks 7).length = (firstMinimum first rest).2 := by
  obtain ⟨n, hn, e, he, hout⟩ := command_eval first rest
  refine ⟨e, ⟨n + 1, ?_, ?_⟩, hout⟩
  · exact (by omega : n + 1 ≤ 15 * first.length + 19 +
      scanBudget first.length 1 rest).trans (sourceBudget_le_quadratic first rest)
  · exact compiled_halt_trace he 0 7

/-- The unary program's output indexes the original candidate chosen by the
natural-number conditional-expectation algorithm. -/
theorem program_candidates {A : Type*} (score : A → ℕ) (a : A) (tail : List A) :
    ∃ e : Data, ∃ k < (a :: tail).length,
      RunsIn program
        (500 * (score a + (tail.map score).sum + tail.length + 1) ^ 2)
        ((inputState ((a :: tail).map (fun x => UnaryCompare.encode (score x)))).withPC
          (some program.entry)) (e.withPC none) ∧
      (e.stacks 7).length = k ∧
      (a :: tail)[k]? = some (NaturalAssignment.chooseMinNat score a tail) := by
  obtain ⟨e, he, hout⟩ := program_runsIn (UnaryCompare.encode (score a))
    (tail.map (fun x => UnaryCompare.encode (score x)))
  obtain ⟨k, hk, hi, hv⟩ := indexChoice_lookup score 0 a tail
  refine ⟨e, k, hk, ?_, ?_, ?_⟩
  · simpa [UnaryCompare.encode, List.map_map, Function.comp_def] using he
  · rw [firstMinimum_eq_chooseMin] at hout
    have hp := chooseTagged_indexChoice score 0 a tail
    simp only [UnaryCompare.encode_length] at hout
    change (e.stacks 7).length =
      (NaturalAssignment.chooseMinNat Prod.fst (score a, 0)
        (tagged (0 + 1) (tail.map (fun x => UnaryCompare.encode (score x))))).2 at hout
    rw [hp] at hout
    simpa [hi] using hout
  · simpa only [indexChoice_value] using hv

end SubexponentialSAT.Subexp.MinimumProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_SequentialProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed sequential assignment control

The loop counter, processed index, word width, alphabet, and assignment are
runtime stack data. A fixed score-building command is composed with the
verified minimum selector and preserving packed-array operations.
-/

namespace SubexponentialSAT.Subexp.SequentialProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

theorem embed_restrict (d : Data) :
    embedState minimumRegisters minimumStacks d
      ⟨fun i => d.regs (minimumRegisters i), fun i => d.stacks (minimumStacks i)⟩ = d := by
  apply congrArg₂ StructuredProgram.State.mk
  · funext j
    by_cases h : ∃ i, minimumRegisters i = j
    · obtain ⟨i, rfl⟩ := h
      exact embedState_register minimumRegisters minimumStacks d _ minimumRegisters_injective i
    · exact embedState_register_frame minimumRegisters minimumStacks d _ j h
  · funext j
    by_cases h : ∃ i, minimumStacks i = j
    · obtain ⟨i, rfl⟩ := h
      exact embedState_stack minimumRegisters minimumStacks d _ minimumStacks_injective i
    · exact embedState_stack_frame minimumRegisters minimumStacks d _ j h

abbrev resetState (rs : List (Fin 16)) (d : Data) : Data :=
  ⟨fun j => if j ∈ rs then false else d.regs j, d.stacks⟩

theorem resetList_eval (rs : List (Fin 16)) (d : Data) :
    Eval (resetList rs) rs.length d (resetState rs d) := by
  induction rs generalizing d with
  | nil =>
      simpa [resetList, resetState] using (Eval.base (StructuredProgram.Eval.skip d))
  | cons r rs ih =>
      let e : Data := ⟨Function.update d.regs r false, d.stacks⟩
      have ha : Eval (atom (.set r false)) 1 d e := .base (.atom _ _)
      have hh := ha.seq (ih e)
      have hs : resetState rs e = resetState (r :: rs) d := by
        apply congrArg₂ StructuredProgram.State.mk
        · funext j
          by_cases hj : j = r <;> by_cases hr : j ∈ rs <;>
            simp_all [resetState, e, Function.update_apply]
        · rfl
      simpa [resetList, hs, Nat.add_comm] using hh

theorem resetRegisters_eval (d : Data) :
    ∃ e : Data, Eval resetRegisters 9 d e ∧ e.stacks = d.stacks ∧
      (∀ i, e.regs (minimumRegisters i) = false) := by
  refine ⟨resetState [0, 1, 2, 3, 4, 5, 6, 7, 8] d,
    resetList_eval _ d, rfl, ?_⟩
  intro i
  fin_cases i <;> simp [ minimumRegisters]

theorem clearList_eval (rs : List (Fin 48)) (d : Data) (bound : ℕ)
    (hb : ∀ j ∈ rs, (d.stacks j).length ≤ bound) :
    ∃ n ≤ rs.length * (2 * bound + 3), ∃ e : Data,
      Eval (clearList rs) n d e ∧
      (∀ j, e.stacks j = if j ∈ rs then [] else d.stacks j) := by
  induction rs generalizing d with
  | nil =>
      exact ⟨0, by simp, d, .base (.skip d), by simp⟩
  | cons r rs ih =>
      let middle : Data := ⟨readRegs d.regs 9 8 none, clearStacks r d.stacks⟩
      have hm : ∀ j ∈ rs, (middle.stacks j).length ≤ bound := by
        intro j hj
        by_cases he : j = r
        · subst j
          simp [middle, clearStacks]
        · simpa [middle, clearStacks, he] using hb j (by simp [hj])
      obtain ⟨n, hn, e, he, hs⟩ := ih middle hm
      have ht : Eval (.call (clearProgram r (9 : Fin 16) 8))
          (2 * (d.stacks r).length + 3) d middle :=
        .call _ (ListRegisterProgram.clear_run r 9 8 d.regs d.stacks)
      refine ⟨(2 * (d.stacks r).length + 3) + n, ?_, e, ht.seq he, ?_⟩
      · have hr := hb r (by simp)
        simp only [List.length_cons]
        nlinarith
      · intro j
        rw [hs]
        by_cases hj : j = r <;> by_cases hr : j ∈ rs <;>
          simp_all [middle, clearStacks, Function.update_apply]

theorem cleanAuxiliary_eval (d : Data) (bound : ℕ)
    (hb : ∀ j ∈ ([0, 1, 2, 3, 4, 5, 6, 7, 12] : List (Fin 48)),
      (d.stacks j).length ≤ bound) :
    ∃ n ≤ 9 * (2 * bound + 3), ∃ e : Data,
      Eval cleanAuxiliary n d e ∧
      (∀ j, e.stacks j = if j ∈ ([0, 1, 2, 3, 4, 5, 6, 7, 12] : List (Fin 48))
        then [] else d.stacks j) :=
  clearList_eval _ d bound hb

abbrev afterWordUpdate (d : Data) (assigned : List (List Bool)) (new rest : List Bool) : Data :=
  ⟨readRegs d.regs 9 8 none,
    Function.update (Function.update (Function.update d.stacks 7 []) 12 new)
      8 (assigned.flatten ++ (new ++ rest))⟩

abbrev peeked (d : Data) : Data :=
  ⟨readRegs d.regs 9 10 (d.stacks 11).head?, d.stacks⟩

abbrev dropped (d : Data) : Data :=
  ⟨readRegs d.regs 9 10 (d.stacks 11).head?,
    Function.update d.stacks 11 (d.stacks 11).tail⟩

theorem peek_eval (d : Data) : Eval peekRemaining 1 d (peeked d) := by
  exact .base (.atom _ _)

theorem drop_eval (d : Data) : Eval dropRemaining 1 d (dropped d) := by
  exact .base (.atom _ _)

/-- A compositional contract for the displayed, fixed step code. Its
premise is an actual instruction execution, never an atomic score oracle. -/
abbrev StepRefines {A : Type*} (encode : A → List Bool) (a : A) (tail : List A)
    (evaluate : ℕ → List A → ℕ) (scoreBuilder : Cmd 16 48) (budget total : ℕ)
    (environment : Fin 48 → List Bool) : Prop :=
  ∀ (n : ℕ) (fixed : List A) (d : Data),
    n + 1 + fixed.length = total →
    Memory encode a tail (n + 1) fixed d.stacks →
    (d.stacks 11).length = n →
    HighState environment d.stacks →
    ∃ t ≤ budget, ∃ e : Data,
      Eval (step scoreBuilder) t d e ∧
      Memory encode a tail n
        (NaturalAssignment.chooseMinNat (fun x => evaluate n (x :: fixed)) a tail :: fixed)
        e.stacks ∧
      (e.stacks 11).length = n ∧ HighState environment e.stacks

theorem loop_eval {A : Type*} (encode : A → List Bool) (a : A) (tail : List A)
    (evaluate : ℕ → List A → ℕ) (scoreBuilder : Cmd 16 48) (budget total : ℕ)
    (environment : Fin 48 → List Bool)
    (hstep : StepRefines encode a tail evaluate scoreBuilder budget total environment)
    (n : ℕ) (fixed : List A) (d : Data)
    (hsize : n + fixed.length = total)
    (hm : Memory encode a tail n fixed d.stacks) (hc : (d.stacks 11).length = n)
    (hcontext : HighState environment d.stacks) :
    ∃ t ≤ n * (budget + 3) + 1, ∃ e : Data,
      Eval (loop scoreBuilder) t (peeked d) e ∧
      Memory encode a tail 0 (NaturalAssignment.assignNat a tail evaluate n fixed) e.stacks ∧
      e.stacks 11 = [] ∧ HighState environment e.stacks := by
  induction n generalizing fixed d with
  | zero =>
      have hz : d.stacks 11 = [] := List.length_eq_zero_iff.mp hc
      refine ⟨1, by simp, peeked d, ?_, hm, hz, hcontext⟩
      exact Eval.while_false (by simp [ hz, readRegs_present])
  | succ n ih =>
      have hnon : d.stacks 11 ≠ [] := by
        intro hz
        simp [hz] at hc
      have hg : (peeked d).regs 10 = true := by
        cases hs : d.stacks 11 with
        | nil => exact (hnon hs).elim
        | cons b bs => simp [ hs, readRegs_present]
      have hdmem : Memory encode a tail (n + 1) fixed (dropped (peeked d)).stacks :=
        memory_counter_update hm _
      have hdlen : ((dropped (peeked d)).stacks 11).length = n := by
        simp [ List.length_tail, hc]
      obtain ⟨k, hk, middle, ht, hmiddle, hmlen, hmcontext⟩ :=
        hstep n fixed (dropped (peeked d)) hsize hdmem hdlen (highState_counter_update hcontext _)
      obtain ⟨m, hmb, e, he, hem, hec, hecontext⟩ :=
        ih _ middle (by simpa [List.length_cons, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using hsize) hmiddle hmlen hmcontext
      refine ⟨(1 + (k + 1)) + m + 1, ?_, e, ?_, hem, hec, hecontext⟩
      · nlinarith
      · exact Eval.while_true hg
          (Eval.seq (drop_eval (peeked d)) (Eval.seq ht (peek_eval middle))) he

end SubexponentialSAT.Subexp.SequentialProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_SequentialStep
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete composition of score selection and packed assignment update. -/

namespace SubexponentialSAT.Subexp.SequentialProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

def afterProcessed (d : Data) : Data :=
  ⟨Function.update d.regs 9 false,
    Function.update d.stacks 19 (false :: d.stacks 19)⟩

theorem incrementProcessed_eval (d : Data) :
    Eval incrementProcessed 2 d (afterProcessed d) := by
  have h := Eval.seq (Eval.base (StructuredProgram.Eval.atom (.set 9 false) d))
    (Eval.base (StructuredProgram.Eval.atom (.push 19 9) _))
  simpa [incrementProcessed, atom, afterProcessed, StructuredProgram.Atom.eval,
    StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg,
    StructuredProgram.State.withPC, execInstr] using h

/-- The remaining integration boundary is a real execution of the supplied
fixed score-stream program. It preserves the assignment and controller ports
while writing one framed unary score per candidate to stack zero. -/
abbrev ScoreBuilderRefines {A : Type*} (encode : A → List Bool) (a : A) (tail : List A)
    (evaluate : ℕ → List A → ℕ) (builder : Cmd 16 48) (budget total : ℕ)
    (environment : Fin 48 → List Bool) : Prop :=
  ∀ (n : ℕ) (fixed : List A) (d : Data),
    n + 1 + fixed.length = total →
    Memory encode a tail (n + 1) fixed d.stacks →
    (d.stacks 11).length = n →
    HighState environment d.stacks →
    ∃ t ≤ budget, ∃ e : Data,
      Eval builder t d e ∧
      e.stacks 0 = ProgramEncoding.encodeRecords
        ((a :: tail).map (fun x => UnaryCompare.encode (evaluate n (x :: fixed)))) ∧
      (∀ j : Fin 48, j.val < 20 → j ≠ 0 → e.stacks j = d.stacks j) ∧
      HighState environment e.stacks

end SubexponentialSAT.Subexp.SequentialProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingIncidenceInputNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


/-! Convert a physically scanned factor-index stream to incidence plans. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput.Rows
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

def recordPrefix (h n j : ℕ) : List Bool :=
  true :: Encoding.frame (Encoding.frame (Emit.plan h (n+j)))
def prefixes (h n : ℕ) (js : List ℕ) : List Bool := js.flatMap (recordPrefix h n)

end SubexponentialSAT.SqrtLog.PackingIncidenceInput.Rows


/-! Native per-variable incident-factor scan from the original scope stream. -/


/-! Fixed cleanup for the native scope-address scanner. -/


/-! Calls to the fixed record mapper inside the native scope scan. -/


/-! One native low-variable step, including its uncovered neutral factor. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput.Step
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp
def output (scopes : List (List ℕ)) (n v z : ℕ) (out : List Bool) :=
  Rows.prefixes v n (factors scopes v z) ++ out
end SubexponentialSAT.SqrtLog.PackingIncidenceInput.Step


/-! Runtime high-mask loop for the original-address incidence stream. -/


/-! Count the physical scope stream before constructing native incidence plans. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingIncidenceInputInstall
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Raw scope bytes and a mask produce the actual installed incidence-pair table. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput.Install
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp
def plans (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool) :=
  Loop.plans scopes n 0 scopes.length mask
end SubexponentialSAT.SqrtLog.PackingIncidenceInput.Install

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingIncidenceInputSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Typed original-variable/factor semantics of the native address list. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput.Semantics
open SubexponentialSAT.Subexp

theorem plans_eq (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool) :
    ∀ v z, Loop.plans scopes n v z mask = (entries scopes v z mask).map (fun p => [p.1,n+p.2]) := by
  induction mask with
  | nil => intros; rfl
  | cons high mask ih =>
      intro v z
      cases high <;> simp [Loop.plans,entries,Loop.rowPlans,ih,List.map_map]

theorem incidencePlan_eq (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool) (hm : mask.length ≤ n)
    (i : Incidences scopes mask) :
    PackingIncidenceProgram.incidencePlan (owner scopes n mask hm) (factor scopes n mask hm)
      (seedIndices n (factorCount scopes mask)) i =
      [((nativeEntries scopes mask).get i).1,n+((nativeEntries scopes mask).get i).2] := by
  simp only [PackingIncidenceProgram.incidencePlan,seedIndices]
  rw [Packing.headsFirst_index_head _ _ _ (List.mem_finRange _),
    Packing.headsFirst_index_factor]
  simp only [List.length_finRange,SubexponentialSAT.LocalExpectation.indexCode,
    List.idxOf_finRange,owner,factor]

theorem incidencePlans_eq (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool) (hm : mask.length ≤ n) :
    PackingIncidenceProgram.incidencePlans (owner scopes n mask hm) (factor scopes n mask hm)
      (seedIndices n (factorCount scopes mask)) (List.finRange (nativeEntries scopes mask).length) =
      Loop.plans scopes n 0 scopes.length mask := by
  rw [plans_eq]
  simp only [PackingIncidenceProgram.incidencePlans]
  rw [show (List.finRange (nativeEntries scopes mask).length).map
      (PackingIncidenceProgram.incidencePlan (owner scopes n mask hm) (factor scopes n mask hm)
        (seedIndices n (factorCount scopes mask))) =
      List.ofFn (fun i : Incidences scopes mask =>
        [((nativeEntries scopes mask).get i).1,n+((nativeEntries scopes mask).get i).2]) by
      simp [List.ofFn_eq_map,incidencePlan_eq]]
  change List.ofFn ((fun p : ℕ × ℕ => [p.1,n+p.2]) ∘
    (nativeEntries scopes mask).get) = _
  rw [← List.map_ofFn,List.ofFn_get]
  rfl
end SubexponentialSAT.SqrtLog.PackingIncidenceInput.Semantics

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingWeightProgramBasic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed binary computation of the reciprocal-error packing coefficients.
Sources 0..3 hold n,s,M,r. Outputs 4,5 hold n²s² and 8M²r².
Ports 6,7 and 8..12 are temporary products and arithmetic scratch. -/
namespace SubexponentialSAT.SqrtLog.PackingWeightProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.ArithmeticCalls

abbrev shift : Cmd 8 13 := .seq (SubexponentialSAT.Subexp.TupleProgram.pushConst 5 0 false)
  (.seq (SubexponentialSAT.Subexp.TupleProgram.pushConst 5 0 false)
    (SubexponentialSAT.Subexp.TupleProgram.pushConst 5 0 false))

abbrev command : Cmd 8 13 := .seq (multiplyAt (ports 0))
  (.seq (multiplyAt (ports 1)) (.seq (multiplyAt (ports 2))
    (.seq (multiplyAt (ports 3)) (.seq shift (.seq (clear 6) (clear 7))))))

end SubexponentialSAT.SqrtLog.PackingWeightProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingWordBalance
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Natural color counts in an explicit uniform word alphabet. -/
namespace SubexponentialSAT.SqrtLog.Packing
open SubexponentialSAT.MulticolorTypes

variable {r Q : ℕ} [NeZero r]

theorem mean_word_color (alphabet : List (Word r Q)) (hn : alphabet.Nodup)
    (hf : ∀ w, w ∈ alphabet) (t : Fin Q) (c : Fin r) :
    SubexponentialSAT.ConditionalExpectation.mean alphabet
      (fun w => if w t = c then (1 : ℚ) else 0) = 1 / (r : ℚ) := by
  rw [SubexponentialSAT.TypeDistribution.list_mean_eq_uniform alphabet hn hf]
  simpa only [Fintype.card_fin] using
    (mean_eval t (fun a : Fin r => if a = c then (1 : ℚ) else 0)).trans
      (SubexponentialSAT.TypeDistribution.mean_indicator c)

end SubexponentialSAT.SqrtLog.Packing

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_AssignmentRecordViews
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed parser-based views of an actual framed word alphabet. -/

namespace SubexponentialSAT.Subexp.AssignmentRecordViews

open BitProgram StructuredCalls TupleProgram

/-- Read the actual first record. The remaining framed list is returned on 0. -/
abbrev first : Cmd 3 3 := .seq pop (.seq parse (.seq transfer setFlag))
def firstProgram := compiled first 0 2

end SubexponentialSAT.Subexp.AssignmentRecordViews

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingExtractionBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Polynomial bounds for the actual nested complete-block extraction. -/

namespace SubexponentialSAT.Subexp.PackingExtraction

theorem blockBudget_le (i : ℕ) (entries : List Entry) (c : Context) (B I A : ℕ)
    (hB : ∀ e ∈ entries, (entryWord e).length ≤ B)
    (hI : c.block.length ≤ I) (hA : c.address.length + entries.length ≤ A) :
    blockBudget i entries c ≤ entries.length * unitBudget B I A := by
  induction entries generalizing c with
  | nil => simp [blockBudget]
  | cons e es ih =>
    have he := hB e (by simp)
    have hc : c.address.length ≤ A := by simp only [List.length_cons] at hA; omega
    have hs : 6 * (entryWord e).length + callbackBudget (entryWord e) c.block c.address + 7 ≤
        unitBudget B I A := by
      dsimp [callbackBudget, unitBudget]
      omega
    have ht := ih (emitted c e.1 (entryVertex i e))
      (fun x hx => hB x (by simp [hx])) hI
      (by simpa [emitted, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hA)
    calc
      blockBudget i (e :: es) c ≤ unitBudget B I A + es.length * unitBudget B I A :=
        Nat.add_le_add hs ht
      _ = (e :: es).length * unitBudget B I A := by simp [Nat.add_mul, Nat.add_comm]

theorem loopBudget_le (entries : List Entry) (n i : ℕ) (c : Context) (B I A : ℕ)
    (hB : ∀ e ∈ entries, (entryWord e).length ≤ B)
    (hI : c.block.length + n ≤ I)
    (hA : c.address.length + n * entries.length ≤ A) :
    loopBudget entries n i c ≤
      1 + n * (7 * c.buckets.length + entries.length * unitBudget B I A + 13) := by
  induction n generalizing i c with
  | zero => simp [loopBudget]
  | succ n ih =>
    have hbc : c.block.length ≤ I := by omega
    have hac : c.address.length + entries.length ≤ A := by
      simp only [Nat.succ_mul] at hA
      omega
    have hb := blockBudget_le i entries c B I A hB hbc hac
    have hi : (advanced i entries c).block.length + n ≤ I := by
      rw [(advanced_static i entries c).1]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hI
    have ha : (advanced i entries c).address.length + n * entries.length ≤ A := by
      change (emitEntries i entries c).address.length + n * entries.length ≤ A
      rw [emitEntries_address_length]
      simpa [Nat.succ_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hA
    have hr := ih (i + 1) (advanced i entries c) hi ha
    rw [(advanced_static i entries c).2.1] at hr
    let K := 7 * c.buckets.length + entries.length * unitBudget B I A + 13
    have hk : bodyBudget i entries c + 1 ≤ K := by
      dsimp [bodyBudget, K]
      omega
    change loopBudget entries n (i + 1) (advanced i entries c) ≤ 1 + n * K at hr
    change bodyBudget i entries c + loopBudget entries n (i + 1) (advanced i entries c) + 1 ≤
      1 + (n + 1) * K
    calc
      _ ≤ K + (1 + n * K) := by omega
      _ = _ := by ring

end SubexponentialSAT.Subexp.PackingExtraction

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingLeftovers
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Actual leftover packing pass

The immutable covered table is searched for every original vertex. A found
vertex is skipped. A missing vertex is appended to reversed storage and both
lookup tables, with actual unary rank/address increments.
-/
namespace SubexponentialSAT.Subexp.PackingLeftovers

open BitProgram StructuredCalls MatrixProgramSupport

theorem callbackCost_le (records : Records) (v V R A : ℕ) (s : Snapshot)
    (hv : v ≤ V) (hr : s.rank ≤ R) (ha : s.address ≤ A) :
    callbackCost records v s ≤
      (45*V+109)*(SelectorProgram.rawRecords records).length+56*V+31*R+15*A+148 := by
  have hs := PackingCoveredQuery.scanBudget_le (unary v) records
  simp only [List.length_replicate] at hs
  calc
    callbackCost records v s ≤
        (45*v+109)*(SelectorProgram.rawRecords records).length+56*v+31*s.rank+15*s.address+148 := by
      dsimp [callbackCost]
      nlinarith
    _ ≤ _ := by gcongr

theorem iterationCost_le (records : Records) (vertices : List ℕ) (s : Snapshot) (V R A : ℕ)
    (hv : ∀ v ∈ vertices, v ≤ V)
    (hr : s.rank+vertices.length ≤ R) (ha : s.address+vertices.length ≤ A) :
    iterationCost records vertices s ≤ vertices.length *
      ((45*V+109)*(SelectorProgram.rawRecords records).length+62*V+31*R+15*A+155) := by
  induction vertices generalizing s with
  | nil => simp [iterationCost]
  | cons v vertices ih =>
      have hvv := hv v (by simp)
      have hcb := callbackCost_le records v V R A s hvv (by simp only [List.length_cons] at hr; omega)
        (by simp only [List.length_cons] at ha; omega)
      have hr' := advance_rank_le records s v
      have ha' := advance_address_le records s v
      have ht := ih (advance records s v) (fun x hx => hv x (by simp [hx]))
        (by simp only [List.length_cons] at hr; omega)
        (by simp only [List.length_cons] at ha; omega)
      let C := (45*V+109)*(SelectorProgram.rawRecords records).length+62*V+31*R+15*A+155
      have hhead : 6*v+callbackCost records v s+7 ≤ C := by
        dsimp [C]
        omega
      change 6*v+callbackCost records v s+7+
        iterationCost records vertices (advance records s v) ≤ (vertices.length+1)*C
      calc
        _ ≤ C+vertices.length*C := Nat.add_le_add hhead ht
        _ = _ := by ring

/-- Polynomial bound in serialized covered-table size, vertex count, largest
unary vertex, and the initial unary counters. -/
theorem traceCost_le (records : Records) (vertices : List ℕ) (s : Snapshot) (V : ℕ)
    (hv : ∀ v ∈ vertices, v ≤ V) :
    traceCost records vertices s ≤ 4+vertices.length *
      ((45*V+109)*(SelectorProgram.rawRecords records).length+62*V+
        31*(s.rank+vertices.length)+15*(s.address+vertices.length)+155) := by
  exact Nat.add_le_add_left (iterationCost_le records vertices s V
    (s.rank+vertices.length) (s.address+vertices.length) hv le_rfl le_rfl) 4

theorem range_traceCost_le (records : Records) (D : ℕ) (s : Snapshot) :
    traceCost records (List.range D) s ≤ 4+D *
      ((45*D+109)*(SelectorProgram.rawRecords records).length+62*D+
        31*(s.rank+D)+15*(s.address+D)+155) := by
  simpa only [List.length_range] using traceCost_le records (List.range D) s D
    (fun v hv => Nat.le_of_lt (List.mem_range.mp hv))

end SubexponentialSAT.Subexp.PackingLeftovers

end OAI.Algorithms
end


