-- Prove2me | Definitions.Def_OAIQ081S039
-- name    : OAIQ081S039
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T21:32:45.837384+00:00
-- url     : https://prove2.me/theorems/6fb80232-8aad-479c-a0a7-e98f8fad38f4
-- title:
--   Definitions bundle OAIQ081S039 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 128 declarations of OpenAI's Lean: 94 definitions, 1 inductive type or structure, 4 instances and 29 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.QueryReadback.Wide.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.QueryReadback.moveCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.SourceReady.bankBlank`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.markedCount`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.projectedAlgebra`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Code`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.copies`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.copy`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.numericMajorant`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.parameterSize`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgram.Replay.hidden`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafScopeInputBounds.StatisticsBound`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafScopeResourceBounds.forwardMask`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Binary.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Binary.state`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Finalize.Code`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Finalize.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Finalize.adjust`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Finalize.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Finalize.ensureOne`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Finalize.peek`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Finalize.peeked`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Finalize.program`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Finalize.pushOne`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Finalize.state`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Finalize.transfer`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Lookup.Code`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Lookup.body`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Lookup.copy`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Lookup.loop`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Lookup.popIndex`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Lookup.popScan`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Lookup.skip`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Max.Code`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Max.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Max.body`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Max.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Max.loop`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Max.popX`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Max.popped` and 55 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLog_LeafProgramMarked`, `SubexponentialSAT_SqrtLog_LeafProgramProjection`, `SubexponentialSAT_SqrtLog_LeafProgramQueryReadback`, `SubexponentialSAT_SqrtLog_LeafProgramQueryReadbackWide`, `SubexponentialSAT_SqrtLog_LeafProgramSourceReadyInput`, `SubexponentialSAT_SqrtLog_LeafQueryFrontendMajorants`, `SubexponentialSAT_SqrtLog_LeafQueryFrontendOps`, `SubexponentialSAT_SqrtLog_LeafQueryFrontendPorts`, `SubexponentialSAT_SqrtLog_LeafQueryFrontendScanBounds`, `SubexponentialSAT_SqrtLog_LeafRingSetupProgramInterpolationReplay`, `SubexponentialSAT_SqrtLog_LeafRingSetupProgramPorts`, `SubexponentialSAT_SqrtLog_LeafRingSetupProgramReplay`, `SubexponentialSAT_SqrtLog_LeafScopeInputBounds`, `SubexponentialSAT_SqrtLog_LeafScopeResourceBoundsStatistics`, `SubexponentialSAT_SqrtLog_LeafStatisticsProgramBinary`, `SubexponentialSAT_SqrtLog_LeafStatisticsProgramFinalize`, `SubexponentialSAT_SqrtLog_LeafStatisticsProgramLookup`, `SubexponentialSAT_SqrtLog_LeafStatisticsProgramMax`, `SubexponentialSAT_SqrtLog_LeafWeightProgram`, `SubexponentialSAT_SqrtLog_LeafWeightProgramNative`, `SubexponentialSAT_SqrtLog_LocalCodeExistence`, `SubexponentialSAT_SqrtLog_LocalCodeWeight`, `SubexponentialSAT_SqrtLog_MomentsBoolean`, `SubexponentialSAT_SqrtLog_MomentsBuckets`, `SubexponentialSAT_SqrtLog_MomentsProgramDictionaryInsert`, `SubexponentialSAT_SqrtLog_MomentsProgramDictionaryState`, `SubexponentialSAT_SqrtLog_MomentsProgramProduct`, `SubexponentialSAT_SqrtLog_MomentsProjectionProgramBase`, `SubexponentialSAT_SqrtLog_MomentsProjectionProgramBridge`, `SubexponentialSAT_SqrtLog_MomentsProjectionProgramMask`, `SubexponentialSAT_SqrtLog_MomentsProjectionProgramNative`, `SubexponentialSAT_SqrtLog_MomentsReadoutProgramBounds`, `SubexponentialSAT_SqrtLog_MomentsReadoutProgramState`, `SubexponentialSAT_SqrtLog_NativePackingBoundsTail`, `SubexponentialSAT_SqrtLog_PackingCompletionGenerated`, `SubexponentialSAT_SqrtLog_PackingIncidenceInputNative`, `SubexponentialSAT_SqrtLog_PackingIncidenceInputStats`, `SubexponentialSAT_SqrtLog_PackingIncidenceProgramInputs`, `SubexponentialSAT_SubexpEmptyClauseProgram`, `SubexponentialSAT_SubexpFlatCount`, `SubexponentialSAT_SubexpSunflowerProgram`, `SubexponentialSAT_Subexp_AssignmentInputProgram`, `SubexponentialSAT_Subexp_CollisionGenerateRefinement`, `SubexponentialSAT_Subexp_CollisionTupleProgram`, `SubexponentialSAT_Subexp_ConstructivePacking`, `SubexponentialSAT_Subexp_PackingBudgetArithmetic`, `SubexponentialSAT_Subexp_PairScoreBounds`, `SubexponentialSAT_Subexp_ReadPlan`, `SubexponentialSAT_Subexp_SelectorMapProgram`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S000`, `OAIQ081S001`, `OAIQ081S002`, `OAIQ081S003`, `OAIQ081S004`, `OAIQ081S005`, `OAIQ081S007`, `OAIQ081S008`, `OAIQ081S009`, `OAIQ081S011`, `OAIQ081S014`, `OAIQ081S016`, `OAIQ081S017` and `OAIQ081S018` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S060`, `OAIQ081S061`, `OAIQ081S062`, `OAIQ081S063` and `OAIQ081S064`; the statements `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafScopeInputBounds.statistics_bound` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafScopeResourceBounds.measured_polylog`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.eventually_raw_scope_guards`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafScopeInputBounds.statistics_bound` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafScopeResourceBounds.measured_polylog`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S000
import Definitions.Def_OAIQ081S001
import Definitions.Def_OAIQ081S002
import Definitions.Def_OAIQ081S003
import Definitions.Def_OAIQ081S004
import Definitions.Def_OAIQ081S005
import Definitions.Def_OAIQ081S007
import Definitions.Def_OAIQ081S008
import Definitions.Def_OAIQ081S009
import Definitions.Def_OAIQ081S011
import Definitions.Def_OAIQ081S014
import Definitions.Def_OAIQ081S016
import Definitions.Def_OAIQ081S017
import Definitions.Def_OAIQ081S018

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramMarked
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Weighted selector mass is the sum of ordinary marked-clause counts.
This identity justifies executing the same count pipeline once per supplied
clause; no weighted arithmetic is hidden in the local indicator evaluator. -/

namespace SubexponentialSAT.SqrtLog.LeafProgram

open scoped BigOperators

variable {X Row E : Type*} [Fintype X] [Fintype E]

def markedCount (rowAccept : Row → X → Bool) (rows : List Row)
    (bad : E → X → Bool) (e : E) : ℕ :=
  ∑ x, if HashSelect.accepts rowAccept rows x && bad e x then 1 else 0

end SubexponentialSAT.SqrtLog.LeafProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramProjection
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Sparse hash circuits commute with a canonical additive projection whose
product is stable. This is the bridge from truncated sparse operations to the
single untruncated source polynomial; no false ring-homomorphism claim about
canonical representatives is required. -/

namespace SubexponentialSAT.SqrtLog.LeafProgram

variable {V C R : Type*} [CommRing R]

def projectedAlgebra (project : R →+ R) : Algebra R where
  zero := 0
  one := project 1
  add := (· + ·)
  mul := fun x y => project (x * y)
  neg := Neg.neg

end SubexponentialSAT.SqrtLog.LeafProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpFlatCount
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Count decisions from the actual flat coefficient representation

Coefficients are stored constant-first, with four consecutive little-endian
words per coefficient. Width and modulus are runtime data. This adapter reads
the first word, discards the unused polynomial suffix, and executes the checked
remainder-and-positivity program. It does not serialize the array into records.
-/

namespace SubexponentialSAT.SubexpFlatCount

open BitProgram StructuredCalls ProgramLinking

abbrev peekCmd : Cmd 8 8 := .base (.atom (.peek 0 0 1))

end SubexponentialSAT.SubexpFlatCount

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramQueryReadback
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete readback/transfer adapter for the marked-query caller. The CRT
result is at261; the exact little-endian integer is delivered at323. The
unread marked-reference stream320 and mass accumulator322 are framed. -/

namespace SubexponentialSAT.SqrtLog.LeafProgram.QueryReadback

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpFlatCount

abbrev moveCommand : Cmd 19 330 :=
  .seq (.call (StackRoutines.transferProgram 261 324 0 1))
    (.call (StackRoutines.transferProgram 324 323 0 1))

end SubexponentialSAT.SqrtLog.LeafProgram.QueryReadback

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramQueryReadbackWide
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Relocation of the concrete reader into the shared marked/branch caller. -/

namespace SubexponentialSAT.SqrtLog.LeafProgram.QueryReadback.Wide

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpFlatCount

abbrev Data := State 40 768

end SubexponentialSAT.SqrtLog.LeafProgram.QueryReadback.Wide

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_ConstructivePacking
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Executable complete-block packing

All execution definitions use supplied finite lists, filtering, minimum scans,
indexed list access, and index lookup. No execution definition uses classical
choice or an abstract inverse. Mathematical cardinalities occur only in proofs.
-/

namespace SubexponentialSAT.Subexp.ConstructivePacking

open scoped BigOperators

namespace PackingData

variable {V U : Type*} [DecidableEq U]

theorem bucket_length_le (P : PackingData V U) (u : U) :
    (P.bucket u).length ≤ P.vertices.values.length := List.length_filter_le _ _

end PackingData

end SubexponentialSAT.Subexp.ConstructivePacking

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_ReadPlan
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Explicit local read plans

Read plans are lists of numeric positions in the explicit seed array. The
machine-facing data are fixed-width one-hot word records and unary indices.
Gathering them in head/slot order reproduces the actual type encoding.
-/

namespace SubexponentialSAT.Subexp.ReadPlan

open SubexponentialSAT.MulticolorTypes

section PartialAssignments

variable {W : Type*}

theorem selected_getD (default : W) (current : List W) (remaining : List ℕ)
    (candidate : List W) (n : ℕ) (hn : n < current.length) :
    (current ++ candidate).getD (selectPosition current.length remaining n) default =
      completedAt default current remaining candidate n := by
  by_cases hm : n ∈ remaining
  · simp only [selectPosition, completedAt, ite_eq_left hm]
    rw [List.getD_append_right _ _ _ _ (by omega)]
    simp
  · simp only [selectPosition, completedAt, ite_eq_right hm]
    exact List.getD_append _ _ _ _ hn

theorem selected_valid (currentSize candidateSize : ℕ) (remaining : List ℕ)
    (hlen : remaining.length ≤ candidateSize) (n : ℕ) (hn : n < currentSize) :
    selectPosition currentSize remaining n < currentSize + candidateSize := by
  by_cases hm : n ∈ remaining
  · have hi := List.idxOf_lt_length_iff.mpr hm
    simp only [selectPosition, ite_eq_left hm]
    omega
  · simp only [selectPosition, ite_eq_right hm]
    omega

end PartialAssignments

end SubexponentialSAT.Subexp.ReadPlan

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_SelectorMapProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# A fixed loop applying the selected-index map to query records

The selector uses ports 0--5.  Port 6 is the framed query cursor, port 7
preserves the raw key/payload table, and port 8 accumulates framed answers.
Answers are prepended, so the returned record list reverses query order.
-/

namespace SubexponentialSAT.Subexp.SelectorMapProgram

open BitProgram StructuredCalls

theorem oneRecord_bound (key query value : List Bool) :
    SubexpRecordScan.recordCost key query value + 4 ≤
      (9 * query.length + 40) * (2 * key.length + 2 * value.length + 2) := by
  calc
    _ ≤ 40 * (key.length + value.length) + (9 * query.length + 40) := by
      simp only [SubexpRecordScan.recordCost]
      omega
    _ ≤ (9 * query.length + 40) * (key.length + value.length) +
        (9 * query.length + 40) :=
      Nat.add_le_add_right (Nat.mul_le_mul_right _ (by omega)) _
    _ = (9 * query.length + 40) * (key.length + value.length + 1) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ (by omega)

end SubexponentialSAT.Subexp.SelectorMapProgram

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

theorem streamed_eq_reverse_map (current : List Bool) (width : ℕ) (left right : List ℕ)
    (tuples : List (List Bool)) (stream : List Bool) :
    streamed current width left right tuples stream =
      (tuples.map (leafBit current width left right)).reverse ++ stream := by
  induction tuples generalizing stream with
  | nil => rfl
  | cons bits tuples ih =>
    simp only [streamed, List.foldl_cons]
    change streamed current width left right tuples
      (leafBit current width left right bits :: stream) = _
    rw [ih]
    simp

end SubexponentialSAT.Subexp.CollisionTupleProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpSunflowerProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Actual finite programs used by sunflower candidate checking

Runtime clause counts and widths remain encoded stack data. The first
primitive counts framed records; it is an actual finite instruction table,
with a trace theorem, rather than a semantic list-length instruction.
-/
namespace SubexponentialSAT.SubexpSunflowerProgram

open BitProgram

namespace CountRecords

def steps (records : List (List Bool)) : ℕ := loopSteps records + 2

end CountRecords

end SubexponentialSAT.SubexpSunflowerProgram

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
  {v N f S : ℕ}

def bankBlank (i : Fin 320) : Prop := i=5 ∨ i=10 ∨
  (localBlank (sourcePorts i) ∧ i ∉ ([192,193,242,243,304] : List (Fin 320)))
instance instDecidableBankBlank (i : Fin 320) : Decidable (bankBlank i) := inferInstanceAs
  (Decidable (i=5 ∨ i=10 ∨
    (localBlank (sourcePorts i) ∧ i ∉ ([192,193,242,243,304] : List (Fin 320)))))

end SubexponentialSAT.SqrtLog.LeafProgram.SourceReady

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafQueryFrontendPorts
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed disjoint work areas for the per-query native frontend. -/
namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
abbrev Code := Cmd 40 768

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

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

def copy (src dst : Fin 768) : Code := .call (StackRoutines.copyProgram src dst 679 0 1)

def copies : List (Fin 768 × Fin 768) → Code
  | [] => .base .skip
  | (s,d)::xs => .seq (copy s d) (copies xs)

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafStatisticsProgramMax
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A native unary maximum. Consumes the new value and leaves the maximum
on the accumulator stack, using a linear number of physical bit operations. -/
namespace SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Max
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
abbrev Data := State 3 3
abbrev Code := Cmd 3 3

abbrev state (r : Fin 3 → Bool) (x y z : List Bool) : Data := ⟨r, ![x,y,z]⟩
abbrev popX : Code := .base (.atom (.pop 0 0 1))
abbrev takeY : Code := .base (.atom (.pop 1 0 2))
abbrev pushZ : Code := .seq (.base (.atom (.set 0 true))) (.base (.atom (.push 2 0)))
abbrev body : Code := .seq takeY (.seq pushZ popX)
abbrev loop : Code := .while 1 body

abbrev popped (r : Fin 3 → Bool) (x y z : List Bool) : Data :=
  state (readRegs r 0 1 x.head?) x.tail y z

abbrev transfer : Code := .call (StackRoutines.transferProgram 2 1 0 1)
abbrev command : Code := .seq popX (.seq loop transfer)

abbrev program := compiled command 0 1

end SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Max

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafStatisticsProgramLookup
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed native bit lookup at a unary index. The mask source is preserved. -/
namespace SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Lookup
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev Code := Cmd 4 5
abbrev popIndex : Code := .base (.atom (.pop 1 0 1))
abbrev popScan : Code := .base (.atom (.pop 2 2 3))
abbrev body : Code := .seq popScan popIndex
abbrev loop : Code := .while 1 body
abbrev skip : Code := .seq popIndex loop

abbrev copy : Code := .call (StackRoutines.copyProgram 0 2 3 0 1)

end SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Lookup

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafStatisticsProgramBinary
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native unary-to-binary conversion for each statistics output. -/
namespace SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Binary
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
abbrev Data := State 3 3

def state (r : Fin 3 → Bool) (input output : List Bool) : Data :=
  ⟨r,CounterPrograms.lengthStacks input output []⟩

end SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Binary

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafStatisticsProgramFinalize
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Add precisely the uncovered-variable neutral factors. Inputs are the
unary outputs of the physical scope and variable scans. -/
namespace SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Finalize
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
abbrev Data := State 3 3
abbrev Code := Cmd 3 3

abbrev state (r : Fin 3 → Bool) (q u a : ℕ) : Data := ⟨r, ![unary q,unary u,unary a]⟩
abbrev peek (i : Fin 3) : Code := .base (.atom (.peek i 0 1))
abbrev peeked (i : Fin 3) (d : Data) : Data := ⟨readRegs d.regs 0 1 (d.stacks i).head?,d.stacks⟩

abbrev pushOne : Code := .seq (.base (.atom (.set 0 true))) (.base (.atom (.push 2 0)))
abbrev ensureOne : Code := .seq (peek 2) (.ite 1 (.base .skip) pushOne)

abbrev adjust : Code := .seq (peek 1) (.ite 1 ensureOne (.base .skip))

abbrev transfer : Code := .call (StackRoutines.transferProgram 1 0 0 1)
abbrev command : Code := .seq adjust transfer
abbrev program := compiled command 0 1

end SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Finalize

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LocalCodeExistence
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact finite random-row counting, with no probabilistic hypothesis. -/

namespace SubexponentialSAT.SqrtLog.LocalCode

open scoped BigOperators
open SparseCode

section Evaluation

variable {R C : Type*} [Fintype R] [Fintype C] [DecidableEq R] [DecidableEq C]

def evaluationHom (v : C → F3) : CheckMatrix R C →+ (R → F3) where
  toFun Q := check Q v
  map_zero' := by ext r; simp [check]
  map_add' Q Q' := by ext r; simp [check, add_mul, Finset.sum_add_distrib]

noncomputable def killedMatrices (v : C → F3) : Finset (CheckMatrix R C) :=
  Finset.univ.filter fun Q => evaluationHom v Q = 0

end Evaluation

end SubexponentialSAT.SqrtLog.LocalCode

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LocalCodeWeight
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Elementary low-weight counting by successive single-coordinate updates. -/

namespace SubexponentialSAT.SqrtLog.LocalCode

open SparseCode

abbrev UpdateSymbol (D : ℕ) := Option (Fin D × F3)

def applySymbol {D : ℕ} : UpdateSymbol D → (Fin D → F3) → (Fin D → F3)
  | none, w => w
  | some (c, a), w => Function.update w c a

end SubexponentialSAT.SqrtLog.LocalCode

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafScopeResourceBoundsStatistics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Upper bounds for the actual measured statistics. The mask is the forward
reverse of the physical descending high-prefix stream. -/
namespace SubexponentialSAT.SqrtLog.LeafScopeResourceBounds
open LeafStatisticsProgram LeafStatisticsSemantics

abbrev forwardMask (scopes : List (List ℕ)) (cut n : ℕ) :=
  (HighIncidenceProgram.highPrefix scopes cut n).reverse

@[simp] theorem forwardMask_length (scopes : List (List ℕ)) (cut n : ℕ) :
    (forwardMask scopes cut n).length = n := by
  simp [forwardMask, HighIncidenceProgram.highPrefix_length]

end SubexponentialSAT.SqrtLog.LeafScopeResourceBounds

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafScopeInputBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Input-size bounds for explicit scopes. These bounds use actual duplicate-free
original-coordinate scope rows, with no value-only replacement for their bytes. -/
namespace SubexponentialSAT.SqrtLog.LeafScopeInputBounds
open LeafStatisticsProgram LeafStatisticsSemantics

structure StatisticsBound (scopes : List (List ℕ)) (mask : List Bool) (S : ℕ) : Prop where
  free : (measured scopes mask).free ≤ S
  occurrence : (measured scopes mask).occurrence ≤ S
  incidences : (measured scopes mask).incidences ≤ 2*S^2
  uncovered : (measured scopes mask).uncovered ≤ S
  arity : max (Arity.arity mask scopes 0)
    (if (measured scopes mask).uncovered=0 then 0 else 1) ≤ S
  factors : scopes.length+(measured scopes mask).uncovered ≤ 2*S

end SubexponentialSAT.SqrtLog.LeafScopeInputBounds

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafQueryFrontendScanBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls LeafScopeInputBounds
attribute [local simp] Fin.coe_ofNat_eq_mod

def numericMajorant (S : ℕ) : ℕ := 16*S+11+
  conversionCost S+conversionCost S+conversionCost S+conversionCost (2*S)+conversionCost (2*S^2)

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafQueryFrontendMajorants
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT

def parameterSize (S : ℕ) : ℕ := numericMajorant S+2*S^2+2*S+1

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

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

theorem volume_prefix (pref : List Bool) (rows : List (List Bool)) :
    volume (rows.map (fun row => pref ++ row)) = rows.length * pref.length + volume rows := by
  induction rows with
  | nil => simp
  | cons row rows ih => simp only [List.map_cons, volume_cons, List.length_append,
      List.length_cons, ih]; ring

theorem budget_linear (rows : List (List Bool)) (a b : ℕ) :
    RecordPrograms.budget (fun row => a * row.length + b) rows =
      (a + 6) * volume rows + (b + 7) * rows.length := by
  induction rows with
  | nil => simp [RecordPrograms.budget]
  | cons row rows ih =>
    simp only [RecordPrograms.budget, volume_cons, List.length_cons, ih]
    ring

theorem volume_cartesian (rows alphabet : List (List Bool)) :
    volume (TupleProgram.cartesianOutput rows alphabet) =
      alphabet.length * volume rows + rows.length * volume alphabet := by
  unfold TupleProgram.cartesianOutput
  rw [volume_reverse]
  induction rows with
  | nil => simp
  | cons row rows ih =>
    simp only [List.flatMap_cons, volume_append, volume_prefix,
      volume_cons, List.length_cons, ih]
    ring

end SubexponentialSAT.Subexp.PairScoreBounds

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafRingSetupProgramPorts
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed physical layout for native ring preparation.

The local setup has 32 registers and 640 stacks.  It can be lifted into the
40-register/768-stack leaf caller.  The collector's stacks 320--339 are never
used.  Arithmetic metadata is written directly to its native consumer port;
temporary search, scalar, table, and node data have disjoint workspaces.
-/
namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram

open BitProgram StructuredCalls

/-- These are preservation statements about physical ports, independent of
all runtime values and dimensions. -/
theorem search_avoids_collector (i : Fin 28) :
    (search i).val < 320 ∨ 340 ≤ (search i).val := by
  fin_cases i <;> decide

theorem scalar_avoids_collector (i : Fin 41) :
    (scalar i).val < 320 ∨ 340 ≤ (scalar i).val := by
  fin_cases i <;> decide

theorem table_avoids_collector (i : Fin 42) :
    (table i).val < 320 ∨ 340 ≤ (table i).val := by
  fin_cases i <;> decide

theorem nodes_avoids_collector (i : Fin 15) :
    (nodes i).val < 320 ∨ 340 ≤ (nodes i).val := by
  fin_cases i <;> decide

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafRingSetupProgramInterpolationReplay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact-time replay footprint of the existing interpolation producer. -/
namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram.Interpolation.Replay
open BitProgram StructuredCalls

theorem visible (i : Fin 768) (h : i.val < 320 ∨ 340 ≤ i.val) : ¬LeafProgram.OuterCarried.hidden i := by
  intro hh
  have hv : i.val=320 ∨ i.val=322 ∨ i.val=332 := by
    simpa [LeafProgram.OuterCarried.hidden,Fin.ext_iff] using hh
  omega

theorem private_visible : ∀i∈privatePorts,¬LeafProgram.OuterCarried.hidden i := by
  intro i hi
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp hi
  apply visible
  right
  change 340 ≤ 340+j.val
  omega

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram.Interpolation.Replay

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
open BitProgram StructuredCalls

def hidden : Fin 640 → Prop := LeafProgram.OuterCarried.hidden ∘ wideStacks
instance instDecidablePredFinOfNatNatHidden : DecidablePred hidden := fun i => inferInstanceAs
  (Decidable (LeafProgram.OuterCarried.hidden (wideStacks i)))

theorem hidden_bounds {i : Fin 640} (h : hidden i) : 320 ≤ i.val ∧ i.val < 340 := by
  have hv : i.val=320 ∨ i.val=322 ∨ i.val=332 := by
    simpa [hidden,Function.comp_def,LeafProgram.OuterCarried.hidden,wideStacks,
      Fin.ext_iff] using h
  omega

theorem visible (i : Fin 640) (h : i.val < 320 ∨ 340 ≤ i.val) : ¬hidden i := by
  intro hh
  have := hidden_bounds hh
  omega

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram.Replay

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafWeightProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The Boolean part of a local squarefree head weight, executed by a fixed
parallel scan of the assignment, support mask, and head mask. -/
namespace SubexponentialSAT.SqrtLog.LeafWeightProgram

open SubexponentialSAT BitProgram StructuredCalls

abbrev Data := StructuredProgram.State 8 3

abbrev data (r : Fin 8 → Bool) (a s h : List Bool) : Data := ⟨r,tapes a s h⟩

def ready (r : Fin 8 → Bool) (a s h : List Bool) : Data :=
  data (readRegs r 0 3 a.head?) a.tail s h

abbrev popAssignment : StructuredProgram.Cmd 8 3 := .atom (.pop 0 0 3)
abbrev body : StructuredProgram.Cmd 8 3 :=
  .seq (.atom (.pop 1 1 4)) <|
  .seq (.atom (.pop 2 2 5)) <|
  .seq (.atom (.band 7 1 2)) <|
  .seq (.atom (.bnot 7 7)) <|
  .seq (.atom (.bor 7 7 0)) <|
  .seq (.atom (.band 6 6 7)) popAssignment

abbrev loop : StructuredProgram.Cmd 8 3 := .while 3 body
abbrev command : Cmd 8 3 := .base <|
  .seq (.atom (.set 6 true)) (.seq popAssignment loop)

abbrev program := compiled command 0 0

end SubexponentialSAT.SqrtLog.LeafWeightProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafWeightProgramNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Preserving physical wrapper for the Boolean head-weight scan. The actual
ring zero and one are arbitrary runtime words, so the ring degree is dynamic. -/
namespace SubexponentialSAT.SqrtLog.LeafWeightProgram.Native

open SubexponentialSAT BitProgram StructuredCalls StackRoutines

abbrev scan : Cmd 8 10 :=
  .call (ProgramLinking.liftProgram LeafWeightProgram.program id stackMap)

end SubexponentialSAT.SqrtLog.LeafWeightProgram.Native

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsBoolean
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Boolean coordinate assembly and actual head weights. This avoids field
coordinates or residue representatives: head values are genuine Boolean bits. -/

namespace SubexponentialSAT.SqrtLog.Moments

open scoped BigOperators
open _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree

variable {V G R : Type*} [Fintype V] [Fintype G] [DecidableEq V] [DecidableEq G]

def assemble (head : V → G) (a : ∀ g, Head head g → Bool) : V → Bool :=
  fun v => a (head v) ⟨v, rfl⟩

def split (head : V → G) (a : V → Bool) : ∀ g, Head head g → Bool :=
  fun _ v => a v.val

/-- Every Boolean assignment is exactly one tuple of independent head values. -/
def headEquiv (head : V → G) : (V → Bool) ≃ (∀ g, Head head g → Bool) where
  toFun := split head
  invFun := assemble head
  left_inv a := rfl
  right_inv a := by
    funext g v
    rcases v with ⟨v, hv⟩
    cases hv
    rfl

end SubexponentialSAT.SqrtLog.Moments

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsBuckets
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual attained labels and their Boolean fibers. The label codomain need
not be finite: integer signature vectors are allowed. Enumeration is the
image of each finite head assignment set, followed by its actual fibers. -/

namespace SubexponentialSAT.SqrtLog.Moments

open scoped BigOperators

section BooleanFibers

variable {V G : Type*} [Fintype V] [Fintype G] [DecidableEq V] [DecidableEq G]
variable {L : G → Type*} [∀ g, DecidableEq (L g)]

instance headFintype (head : V → G) (g : G) : Fintype (Head head g) :=
  inferInstanceAs (Fintype {v : V // head v = g})

instance headDecidableEq (head : V → G) (g : G) : DecidableEq (Head head g) :=
  inferInstanceAs (DecidableEq {v : V // head v = g})

def booleanBucketEquiv (head : V → G)
    (label : ∀ g, (Head head g → Bool) → L g) :
    (V → Bool) ≃ Σ y : ∀ g, LabelValue label g, ∀ g, LabelBucket label g (y g) :=
  (headEquiv head).trans (actualBucketEquiv label)

end BooleanFibers

end SubexponentialSAT.SqrtLog.Moments

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

def tapes (a : Tape) : Fin 27 → List Bool := fun i =>
  if i = 0 then a.out else if i = 5 then a.modulus else
  if i = 8 then a.left else if i = 9 then a.right else
  if i = 11 then a.steps else if i = 12 then a.width else
  if i = 15 then a.dict else if i = 16 then a.query else
  if i = 17 then a.coeff else if i = 18 then a.remain else
  if i = 22 then a.found else if i = 24 then a.count else
  if i = 25 then a.result else if i = 26 then a.combined else []

noncomputable def overlay (regs : Fin 8 → Bool) (rr : Fin 5 → Bool) : Fin 8 → Bool :=
  Function.extend smallRegs rr regs

end SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsProgramDictionaryInsert
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

def outputTape (modulus width count dict coeff : List Bool) : Tape :=
  { modulus := modulus, width := width, count := count, dict := dict, coeff := coeff }

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
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

 def scaleEnvironment (a : Store) (scalar : List Bool) : Squarefree.ScaleProgram.Environment :=
  ⟨a.modulus,a.width,a.zero,a.table,scalar,a.degree⟩

end SubexponentialSAT.SqrtLog.MomentsProgram.Product


end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsProjectionProgramMask
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native scan used by exact-support projection: consume a mask while
copying its bits and an equally long zero mask to reversed accumulators. -/
namespace SubexponentialSAT.SqrtLog.MomentsProjectionProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredProgram

abbrev body : Cmd 3 3 :=
  .seq (.atom (.pop 0 0 1)) (.seq (.atom (.push 1 0))
    (.seq (.atom (.set 2 false)) (.seq (.atom (.push 2 2)) (.atom (.peek 0 0 1)))))
abbrev loop : Cmd 3 3 := .while 1 body
abbrev scan : Cmd 3 3 := .seq (.atom (.peek 0 0 1)) loop

end SubexponentialSAT.SqrtLog.MomentsProjectionProgram

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

def readPorts (src dst : Fin 10) : Fin 2 → Fin 10 := ParserProgram.pair src dst

abbrev transfer (src dst : Fin 10) : Cmd 5 10 :=
  .call (StackRoutines.transferProgram src dst (0:Fin 5) 1)

end SubexponentialSAT.SqrtLog.MomentsProjectionProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsProjectionProgramNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms



namespace SubexponentialSAT.SqrtLog.MomentsProjectionProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def keyBits (u z : ℕ) (mask : List Bool) : List Bool :=
  Encoding.encodeNat u++Encoding.encodeNat z++mask

def recordBits (u z : ℕ) (mask coeff : List Bool) : List Bool :=
  Encoding.frame (keyBits u z mask)++Encoding.frame coeff

@[simp] theorem keyBits_length (u z : ℕ) (mask : List Bool) :
    (keyBits u z mask).length = u+z+mask.length+2 := by
  simp [keyBits,Encoding.encodeNat]; omega
@[simp] theorem recordBits_length (u z : ℕ) (mask coeff : List Bool) :
    (recordBits u z mask coeff).length = 2*(u+z+mask.length+coeff.length)+6 := by
  simp [recordBits,keyBits_length]; omega

end SubexponentialSAT.SqrtLog.MomentsProjectionProgram


namespace SubexponentialSAT.SqrtLog.MomentsProjectionProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def Entry.bits (e : Entry) : List Bool := recordBits e.u e.z e.mask e.coeff
def raw : List Entry → List Bool
  | [] => []
  | e::es => e.bits++raw es

def loopBudget (query : List Bool) : List Entry → ℕ
  | [] => 1
  | e::es => 100*(e.bits.length+query.length+1)+2+loopBudget query es

@[simp] theorem raw_cons_ne (e : Entry) (es : List Entry) : raw (e::es) ≠ [] := by
  intro h
  have := congrArg List.length h
  simp [raw,Entry.bits,recordBits_length] at this

end SubexponentialSAT.SqrtLog.MomentsProjectionProgram


/-! A fixed finite program for exact-support projection of a raw sparse dictionary.
Coefficients are opaque framed payloads. No normalization or arithmetic is used. -/
namespace SubexponentialSAT.SqrtLog.MomentsProjectionProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

/-- Serialized target-mask and dictionary input. -/
def input (query : List Bool) (es : List Entry) := Encoding.frame query++raw es

end SubexponentialSAT.SqrtLog.MomentsProjectionProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsProjectionProgramBridge
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


namespace SubexponentialSAT.SqrtLog.MomentsProjectionProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree

@[simp] theorem encodeMask_empty (n : ℕ) :
    encodeMask (∅ : Finset (Fin n)) = List.replicate n false := by
  apply List.ext_getElem <;> simp [encodeMask]

end SubexponentialSAT.SqrtLog.MomentsProjectionProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsReadoutProgramState
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed forty-stack workspace for the two runtime readout counters. -/


/-! Actual stack construction of the sparse key (u,z,empty support), followed
by the paid query cleanup and unary-index increment. -/
namespace SubexponentialSAT.SqrtLog.MomentsReadoutProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

def queryBits (h : High) : List Bool := h.mask ++ false :: (h.z ++ false :: h.u)

end SubexponentialSAT.SqrtLog.MomentsReadoutProgram


/-! One concrete (u,z) coefficient fetch, addition, and index advance. -/


/-! The U loop is driven by a real unary stack. Every visit invokes the
concrete key builder and dictionary scan; no callback is left abstract. -/


/-! Seed one Z accumulator from the cached zero vector and append the
completed coefficient to the output, paying for every copy and reversal. -/


/-! Runtime Z enumeration. Completed fixed-width coefficients are prepended
in reverse and are restored once by the final output transfer. -/


/-! Build the all-false support mask from the actual ambient shape stack.
The loop length is the ambient number of variables, including unused ones. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsReadoutProgramBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Uniform polynomial accounting for all primitive readout loops. -/
namespace SubexponentialSAT.SqrtLog.MomentsReadoutProgram
open SubexponentialSAT.BitProgram
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

def uniformSlotBudget (B d n t J W N : ℕ) : ℕ :=
  100*(N+1)*(W+d*B+n+t+J+3)+MomentsProgram.Dictionary.codeBranchBudget B d+8*(d*B)+100

def uniformReadoutBudget (B d n t J W N : ℕ) : ℕ :=
  J*(t*(uniformSlotBudget B d n t J W N+2)+10*(d*B)+9*t+22)+
    3*(J*(d*B))+9*J+13*n+24

end SubexponentialSAT.SqrtLog.MomentsReadoutProgram

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

open SubexponentialSAT.Subexp SubexponentialSAT.Subexp.ConstructivePacking LayoutProgram

variable {U : Type*} [DecidableEq U]

def leftoversPolynomial (D T : ℕ) : ℕ :=
  36 + D * ((45 * D + 109) * metadataBound D T + 123 * D + 155) +
    10 * D + 8 * metadataBound D T + 6 * addressBound D + 3 * wordBound D

def inversePolynomial (D : ℕ) : ℕ :=
  6 * D ^ 2 + 19 * D + 33 + 12 * wordBound D + 9 * addressBound D +
    500 * (addressBound D + 1) * (wordBound D + 1)

end SubexponentialSAT.SqrtLog.NativePackingBounds

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_CollisionGenerateRefinement
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# The generated collision count is the padded pair count

The actual tuple generator may reverse record order. Its multiplicities,
the fixed-width word encoding, and the collision callback nevertheless give
exactly the successful-leaf count of the explicit padded completion tree.
-/

namespace SubexponentialSAT.Subexp.CollisionGenerateRefinement

open MulticolorTypes

theorem vectors_eq_tuples {A : Type*} (alphabet : List A) (n : ℕ) :
    QuarticSearch.vectors alphabet n = CoefficientSearch.tuples alphabet n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [QuarticSearch.vectors, CoefficientSearch.tuples, ih]

end SubexponentialSAT.Subexp.CollisionGenerateRefinement

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingCompletionGenerated
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Runtime-generated incidence collision leaves, using actual two-word read plans. -/
namespace SubexponentialSAT.SqrtLog.Packing
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.LocalExpectation
open SubexponentialSAT.Subexp

section Plans
variable {I V E : Type*} [Fintype I] [Fintype V] [Fintype E]
  [DecidableEq I] [DecidableEq V] [DecidableEq E]
variable (ivar : I → V) (factor : I → E) {r Q : ℕ}

def incidenceReadPlan (indices : List (V ⊕ E)) (i : I) : List ℕ :=
  [indexCode indices (.inl (ivar i)), indexCode indices (.inr (factor i))]

def incidenceSelectedPlan (indices : List (V ⊕ E)) (currentSize : ℕ)
    (remaining : List ℕ) (i : I) : List ℕ :=
  ReadPlan.completionPlan currentSize remaining (incidenceReadPlan ivar factor indices i)

end Plans
end SubexponentialSAT.SqrtLog.Packing

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

def incidencePlan (indices : List (V ⊕ E)) (i : I) : List ℕ :=
  [indexCode indices (.inl (ivar i)), indexCode indices (.inr (factor i))]

end Plans

end SubexponentialSAT.SqrtLog.PackingIncidenceProgram

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


/-! Native per-variable incident-factor scan from the original scope stream. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput.Scan
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

def scopeBits (scopes : List (List ℕ)) := Encoding.encodeList
  (Encoding.encodeList Encoding.encodeNat) scopes
end SubexponentialSAT.SqrtLog.PackingIncidenceInput.Scan


/-! Fixed cleanup for the native scope-address scanner. -/


/-! Calls to the fixed record mapper inside the native scope scan. -/


/-! One native low-variable step, including its uncovered neutral factor. -/


/-! Runtime high-mask loop for the original-address incidence stream. -/


/-! Count the physical scope stream before constructing native incidence plans. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput.Boot
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp
def records (scopes : List (List ℕ)) : List (List Bool) :=
  scopes.map (Encoding.encodeList Encoding.encodeNat)
end SubexponentialSAT.SqrtLog.PackingIncidenceInput.Boot

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingIncidenceInputStats
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The address stream and the native statistics use the same mask scan. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput.Stats
open SubexponentialSAT.Subexp
open LeafStatisticsProgram

def zero : Totals := ⟨0,0,0,0⟩
end SubexponentialSAT.SqrtLog.PackingIncidenceInput.Stats

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpEmptyClauseProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# A preserving empty-clause test on the actual encoded leaf

The fixed program searches for the one-bit encoding of an empty clause.
The leaf on stack 9 and every other caller word are preserved.  Only the
five empty membership work ports and one empty copy port are used.
-/

namespace SubexponentialSAT.SubexpEmptyClauseProgram

open BitProgram StructuredCalls

abbrev atom (a : StructuredProgram.Atom 10 10) : Cmd 10 10 := .base (.atom a)

abbrev copyLeaf : Cmd 10 10 := .call (StackRoutines.copyProgram 9 0 8 0 1)

abbrev loadQuery : Cmd 10 10 := .seq (atom (.set 0 false)) (atom (.push 2 0))

abbrev resetWork : Cmd 10 10 :=
  .seq (atom (.copy 0 4))
    (.seq (atom (.set 1 false))
      (.seq (atom (.set 2 false))
        (.seq (atom (.set 3 false))
          (.seq (atom (.set 4 false))
            (.seq (atom (.set 5 false)) (atom (.set 6 false)))))))

end SubexponentialSAT.SubexpEmptyClauseProgram

end OAI.Algorithms
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

open BitProgram StructuredCalls SubexpSetupStorage

/-- A closed bound containing only runtime parameter values and input size. -/
def sizeBound (r Q delta D E inputBits : ℕ) : ℕ :=
  let M := seedCount delta D E
  1 + r + Q + delta + D + E + (delta + 1) + 2 * (delta + 1) + Q * r +
    M + r ^ Q + (1 + (2 * r + 2) * r) +
    (1 + (2 * (Q * r) + 2) * r ^ Q) + Q * r + r ^ Q * (Q * r) +
    (1 + (2 * M + 2) * M) + inputBits

end SubexponentialSAT.Subexp.AssignmentInputProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingBudgetArithmetic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Numerical envelopes for the actual packing stages. Every argument below
is a size of an input or a bound established for a generated value. -/

namespace SubexponentialSAT.Subexp.PackingBudgetArithmetic

theorem type_cost_le (S n N W : ℕ) (hS : 1 ≤ S) (hn : n ≤ S)
    (hN : N ≤ S) (hW : W ≤ S) :
    800 * (n + 1) * (N + 1) * ((n + 1) * W + 1) + 12 ≤ 10012 * S ^ 4 := by
  have h2 : S ≤ S ^ 2 := le_power hS (by decide)
  have h4 : S ≤ S ^ 4 := le_power hS (by decide)
  have hn' : n + 1 ≤ 2 * S := by omega
  have hN' : N + 1 ≤ 2 * S := by omega
  have hh : (n + 1) * W + 1 ≤ 3 * S ^ 2 := by
    calc
      _ ≤ (2 * S) * S + 1 := by gcongr
      _ ≤ 3 * S ^ 2 := by ring_nf; omega
  calc
    _ ≤ 800 * (2 * S) * (2 * S) * (3 * S ^ 2) + 12 := by gcongr
    _ ≤ 10012 * S ^ 4 := by ring_nf; omega

theorem frontend_le (S B D Δ W F A P L C T : ℕ) (hS : 1 ≤ S)
    (hB : B ≤ S) (hD : D ≤ S) (hd : Δ ≤ S) (hW : W ≤ S) (hF : F ≤ S) (hA : A ≤ S)
    (hP : P ≤ 33 * S ^ 4) (hL : L ≤ 21000 * S ^ 7)
    (hC : C ≤ 10012 * S ^ 4) (hT : T ≤ 5 * S ^ 3) :
    (10100 * S ^ 4 + 9 * B + 11 * D + 9 * Δ + 6 * P + 34) +
    (21000 * S ^ 7 + 9 * F + 9 * W + 6 * P + 6 * L + 2 * D + 31) +
    (C + 9 * A + 7 * Δ + 6 * T + 24) ≤ 200000 * S ^ 7 := by
  have h7 : S ≤ S ^ 7 := le_power hS (by decide)
  have h37 : S ^ 3 ≤ S ^ 7 := Nat.pow_le_pow_right hS (by decide)
  have h47 : S ^ 4 ≤ S ^ 7 := Nat.pow_le_pow_right hS (by decide)
  calc
    _ ≤ (10100 * S ^ 4 + 9 * S + 11 * S + 9 * S + 6 * (33 * S ^ 4) + 34) +
        (21000 * S ^ 7 + 9 * S + 9 * S + 6 * (33 * S ^ 4) + 6 * (21000 * S ^ 7) + 2 * S + 31) +
        (10012 * S ^ 4 + 9 * S + 7 * S + 6 * (5 * S ^ 3) + 24) := by gcongr
    _ ≤ 200000 * S ^ 7 := by omega

theorem extraction_loop_le (S n N K B : ℕ) (hS : 1 ≤ S) (hn : n ≤ S) (hN : N ≤ S)
    (hK : K ≤ 43000 * S ^ 8) (hB : B ≤ 21003 * S ^ 7) :
    1 + n * (7 * K + N * (106 * B + 100 * S + 100 * S ^ 2 + 207) + 13) ≤
      2700000 * S ^ 9 := by
  have h7 : S ≤ S ^ 7 := le_power hS (by decide)
  have h9 : S ≤ S ^ 9 := le_power hS (by decide)
  have h27 : S ^ 2 ≤ S ^ 7 := Nat.pow_le_pow_right hS (by decide)
  have hu : 106 * B + 100 * S + 100 * S ^ 2 + 207 ≤ 2300000 * S ^ 7 := by omega
  calc
    _ ≤ 1 + S * (7 * (43000 * S ^ 8) + S * (2300000 * S ^ 7) + 13) := by gcongr
    _ ≤ 2700000 * S ^ 9 := by ring_nf; omega

theorem metadata_le (S D T : ℕ) (hS : 1 ≤ S) (hD : D ≤ S) (hT : T ≤ 5 * S ^ 3) :
    D * (6 * D + 4 * T + 8) ≤ 34 * S ^ 4 := by
  have h4 : S ≤ S ^ 4 := le_power hS (by decide)
  have h24 : S ^ 2 ≤ S ^ 4 := Nat.pow_le_pow_right hS (by decide)
  calc
    _ ≤ S * (6 * S + 4 * (5 * S ^ 3) + 8) := by gcongr
    _ ≤ 34 * S ^ 4 := by ring_nf; omega

theorem extraction_stage_le (S C n K M : ℕ) (hS : 1 ≤ S)
    (hC : C ≤ 2700000 * S ^ 9) (hn : n ≤ S)
    (hK : K ≤ 43000 * S ^ 8) (hM : M ≤ 34 * S ^ 4) :
    C + 6 * n + 2 * K + 7 * M + 16 ≤ 2800000 * S ^ 9 := by
  have h9 : S ≤ S ^ 9 := le_power hS (by decide)
  have h49 : S ^ 4 ≤ S ^ 9 := Nat.pow_le_pow_right hS (by decide)
  have h89 : S ^ 8 ≤ S ^ 9 := Nat.pow_le_pow_right hS (by decide)
  omega

theorem tail_le (S D T : ℕ) (hS : 1 ≤ S) (hD : D ≤ S) (hT : T ≤ 5 * S ^ 3) :
    30000 * (D + T + 1) ^ 4 ≤ 72030000 * S ^ 12 := by
  have h3 : S ≤ S ^ 3 := le_power hS (by decide)
  have hb : D + T + 1 ≤ 7 * S ^ 3 := by omega
  calc
    _ ≤ 30000 * (7 * S ^ 3) ^ 4 := by gcongr
    _ = _ := by ring

theorem final_le (S F B E V T : ℕ) (hS : 1 ≤ S)
    (hF : F ≤ 200000 * S ^ 7) (hB : B ≤ 5000000 * S ^ 10)
    (hE : E ≤ 2800000 * S ^ 9) (hV : V ≤ 400 * S ^ 2)
    (hT : T ≤ 72030000 * S ^ 12) :
    F + B + E + V + T + 1 ≤ 81000000 * S ^ 12 := by
  have h12 : S ≤ S ^ 12 := le_power hS (by decide)
  have h212 : S ^ 2 ≤ S ^ 12 := Nat.pow_le_pow_right hS (by decide)
  have h712 : S ^ 7 ≤ S ^ 12 := Nat.pow_le_pow_right hS (by decide)
  have h912 : S ^ 9 ≤ S ^ 12 := Nat.pow_le_pow_right hS (by decide)
  have h1012 : S ^ 10 ≤ S ^ 12 := Nat.pow_le_pow_right hS (by decide)
  omega

end SubexponentialSAT.Subexp.PackingBudgetArithmetic

end OAI.Algorithms
end


