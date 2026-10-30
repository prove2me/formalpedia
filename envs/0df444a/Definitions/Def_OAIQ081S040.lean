-- Prove2me | Definitions.Def_OAIQ081S040
-- name    : OAIQ081S040
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T21:33:06.970742+00:00
-- url     : https://prove2.me/theorems/327934b8-1198-4a64-ad38-db9a421bc34c
-- title:
--   Definitions bundle OAIQ081S040 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 122 declarations of OpenAI's Lean: 75 definitions, 1 inductive type or structure and 46 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.headScoreTerms`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgram.Wide.exportPairs`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgram.Wide.privatePorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgram.Wide.stagePairs`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgram.Workspace`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingHeadProgramAnd.program`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingHeadProgramPrefix.body`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingHeadProgramPrefix.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingHeadProgramPrefix.copy`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingHeadProgramPrefix.guard`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingHeadProgramPrefix.loop`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingHeadProgramPrefix.program`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingHeadProgramPrefix.zip`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingHeadProgramPreserve.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingHeadProgramPreserve.copyCount`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingHeadProgramPreserve.copyTable`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingHeadProgramPreserve.program`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingHeadProgramPreserve.scan`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInput.Emit.copy`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInput.Rows.budget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgram.Assembly.move`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgram.Assembly.moveMany`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgram.Assembly.park`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgram.Assembly.unpark`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingWeightProgram.ports`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram.Filter.flags`, `OAI.Algorithms.SubexponentialSAT.Subexp.ActivePlanProgram.copy`, `OAI.Algorithms.SubexponentialSAT.Subexp.AssignmentInitProgram.copyAlphabet`, `OAI.Algorithms.SubexponentialSAT.Subexp.AssignmentInitProgram.copyCounter`, `OAI.Algorithms.SubexponentialSAT.Subexp.AssignmentInitProgram.copyRemaining`, `OAI.Algorithms.SubexponentialSAT.Subexp.AssignmentInitProgram.reset`, `OAI.Algorithms.SubexponentialSAT.Subexp.AssignmentInitProgram.sourceCost`, `OAI.Algorithms.SubexponentialSAT.Subexp.AssignmentInputCall.Code`, `OAI.Algorithms.SubexponentialSAT.Subexp.AssignmentInputProgram.Code`, `OAI.Algorithms.SubexponentialSAT.Subexp.AssignmentPairFrontend.Code`, `OAI.Algorithms.SubexponentialSAT.Subexp.AssignmentPairFrontend.move`, `OAI.Algorithms.SubexponentialSAT.Subexp.AssignmentRecordViews.setFlag`, `OAI.Algorithms.SubexponentialSAT.Subexp.CandidateScoreProgram.copyCandidates`, `OAI.Algorithms.SubexponentialSAT.Subexp.CandidateScoreProgram.copyPairs`, `OAI.Algorithms.SubexponentialSAT.Subexp.CandidateScoreProgram.reverseEscapeProgram` and 36 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparsePriorityProgram`, `SubexponentialSAT_SqrtLog_PackingAlgorithm`, `SubexponentialSAT_SqrtLog_PackingCallerProgramBoundsPolynomial`, `SubexponentialSAT_SqrtLog_PackingCallerProgramCost`, `SubexponentialSAT_SqrtLog_PackingCallerProgramExport`, `SubexponentialSAT_SqrtLog_PackingCallerProgramExportCost`, `SubexponentialSAT_SqrtLog_PackingCallerProgramModel`, `SubexponentialSAT_SqrtLog_PackingCallerProgramReplay`, `SubexponentialSAT_SqrtLog_PackingCallerProgramStage`, `SubexponentialSAT_SqrtLog_PackingHeadProgramAnd`, `SubexponentialSAT_SqrtLog_PackingHeadProgramPrefix`, `SubexponentialSAT_SqrtLog_PackingHeadProgramPreserve`, `SubexponentialSAT_SqrtLog_PackingIncidenceInputCost`, `SubexponentialSAT_SqrtLog_PackingIncidenceInputEmit`, `SubexponentialSAT_SqrtLog_PackingIncidenceInputInstall`, `SubexponentialSAT_SqrtLog_PackingIncidenceInputNative`, `SubexponentialSAT_SqrtLog_PackingIncidenceInputSemantics`, `SubexponentialSAT_SqrtLog_PackingIncidenceProgramInstall`, `SubexponentialSAT_SqrtLog_PackingPrefix`, `SubexponentialSAT_SqrtLog_PackingPrefixScore`, `SubexponentialSAT_SqrtLog_PackingProgramAssemblyBasic`, `SubexponentialSAT_SqrtLog_PackingProgramAssemblyMetadata`, `SubexponentialSAT_SqrtLog_PackingWeightProgramBasic`, `SubexponentialSAT_SubexpIncidencePlanPrimitives`, `SubexponentialSAT_SubexpIncidencePlanScan`, `SubexponentialSAT_SubexpInputFrames`, `SubexponentialSAT_SubexpInputZip`, `SubexponentialSAT_SubexpNormalizeProgram`, `SubexponentialSAT_SubexpPlanAlphabetEmit`, `SubexponentialSAT_SubexpScopeMembershipProgram`, `SubexponentialSAT_SubexpSunflowerProgram`, `SubexponentialSAT_Subexp_ActivePlanProgram`, `SubexponentialSAT_Subexp_AssignmentEnumeration`, `SubexponentialSAT_Subexp_AssignmentInitProgram`, `SubexponentialSAT_Subexp_AssignmentInputCall`, `SubexponentialSAT_Subexp_AssignmentInputState`, `SubexponentialSAT_Subexp_AssignmentPairFrontend`, `SubexponentialSAT_Subexp_AssignmentRecordViews`, `SubexponentialSAT_Subexp_CandidateScoreProgram`, `SubexponentialSAT_Subexp_CollisionGenerateProgram`, `SubexponentialSAT_Subexp_MinimumProgram`, `SubexponentialSAT_Subexp_PaddedCompletion`, `SubexponentialSAT_Subexp_PairPlanPreparation`, `SubexponentialSAT_Subexp_PairPreparationProgram`, `SubexponentialSAT_Subexp_PairScoreProgram`, `SubexponentialSAT_Subexp_SequentialProgram`, `SubexponentialSAT_Subexp_UnaryTally`, `SubexponentialSAT_TypeDistribution`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S000`, `OAIQ081S001`, `OAIQ081S002`, `OAIQ081S003`, `OAIQ081S005`, `OAIQ081S006`, `OAIQ081S007`, `OAIQ081S009`, `OAIQ081S010`, `OAIQ081S011`, `OAIQ081S012`, `OAIQ081S015`, `OAIQ081S016`, `OAIQ081S017`, `OAIQ081S018` and `OAIQ081S019` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S057`, `OAIQ081S061`, `OAIQ081S062`, `OAIQ081S063` and `OAIQ081S064`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S000
import Definitions.Def_OAIQ081S001
import Definitions.Def_OAIQ081S002
import Definitions.Def_OAIQ081S003
import Definitions.Def_OAIQ081S005
import Definitions.Def_OAIQ081S006
import Definitions.Def_OAIQ081S007
import Definitions.Def_OAIQ081S009
import Definitions.Def_OAIQ081S010
import Definitions.Def_OAIQ081S011
import Definitions.Def_OAIQ081S012
import Definitions.Def_OAIQ081S015
import Definitions.Def_OAIQ081S016
import Definitions.Def_OAIQ081S017
import Definitions.Def_OAIQ081S018
import Definitions.Def_OAIQ081S019

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpSunflowerProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
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

def cfg {l : ℕ} (pc : Option (Fin l)) (value present : Bool)
    (input output : List Bool) : Cfg 2 2 l :=
  ⟨pc, ParserProgram.pair value present, ParserProgram.pair input output⟩

end CountRecords

end SubexponentialSAT.SubexpSunflowerProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparsePriorityProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete components of the sharp clause/core search from Appendix A.
The guard counts actual framed literals and executes the preserving subset tester.
The complete search and its polynomial resource bound are developed separately below. -/


namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram

open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls

namespace Filter

def flags (regs : Regs) (v p f : Bool) : Regs :=
  Function.update (Function.update (Function.update regs 13 v) 14 p) 15 f


end Filter

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_TypeDistribution
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Uniform words induce uniform local types

The outcome space consists of all assignments of words to distinct factor,
head, and padding indices. Local read maps are injective. Read maps at
distinct coordinates sharing no factor have disjoint ranges. Finite product
counting then supplies the actual marginals and pair moments needed by
SubexponentialSAT.Variance; these probabilistic properties are conclusions, not hypotheses.
-/

namespace SubexponentialSAT.TypeDistribution

open scoped BigOperators
open SubexponentialSAT.Variance

section EnumeratedExpectations

variable {I W A B : Type*}

/-- An explicit duplicate-free complete alphabet has the uniform finite mean. -/
theorem list_mean_eq_uniform [Fintype W] [DecidableEq W]
    (alphabet : List W) (hnodup : alphabet.Nodup) (hfull : ∀ w, w ∈ alphabet)
    (f : W → ℚ) :
    SubexponentialSAT.ConditionalExpectation.mean alphabet f = mean uniformWeight f := by
  have hset : alphabet.toFinset = (Finset.univ : Finset W) := by
    ext w
    simp [hfull w]
  rw [mean_uniformWeight]
  unfold SubexponentialSAT.ConditionalExpectation.mean
  rw [← List.sum_toFinset f hnodup, hset,
    ← List.toFinset_card_of_nodup hnodup, hset, Finset.card_univ]

end EnumeratedExpectations

end SubexponentialSAT.TypeDistribution

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingAlgorithm
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A deterministic conditional-expectation algorithm with at most four word reads per term. -/
namespace SubexponentialSAT.SqrtLog.Packing
open scoped BigOperators
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.LocalExpectation

section Algorithm
variable {I V E : Type*} [Fintype I] [Fintype V] [Fintype E]
  [DecidableEq I] [DecidableEq V] [DecidableEq E]
variable (ivar : I → V) (factor : I → E) {r Q : ℕ}

omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] in
theorem scoreSupport_card_le (z : ScoreTerm I V Q) :
    (scoreSupport ivar factor z).card ≤ 4 := by
  cases z with
  | inl p => exact (List.toFinset_card_le _).trans (by simp)
  | inr p => exact (List.toFinset_card_le _).trans (by simp)

end Algorithm
end SubexponentialSAT.SqrtLog.Packing

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpNormalizeProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
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

/-! ## Actual record-filter output step

The predicate's result occupies register 2. The following fixed callback
consumes the reversed record on stack 3, prepends its framed representation to
stack 2 exactly when selected, and resets the iterator's flags. Its two other
stacks are preserved. Computing the selection bit is a separate operation.
-/

theorem emitIfSelected_steps_le (selected : Bool) (bits : List Bool) :
    emitIfSelectedSteps selected bits + 1 ≤ 5 * bits.length + 12 := by
  unfold emitIfSelectedSteps
  split <;> omega

/-! ## A complete record-order reversal pass

Prepending accepted records reverses their order. This second, unconditional
pass restores the order required by `List.filter` and the executable
sparsifier. It reverses the records, never the bits within a record.
-/

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpIncidencePlanPrimitives
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed unary-counter and record-emission instructions for incidence plans. -/
namespace SubexponentialSAT.SubexpIncidencePlanPrimitives

open BitProgram StructuredCalls

theorem emitReg_injective : Function.Injective emitReg := by decide
theorem emitStack_injective : Function.Injective emitStack := by decide

theorem emit_cost (selected : Bool) (bits : List Bool) :
    SubexpNormalizeProgram.emitIfSelectedSteps selected bits + 1 ≤ 5 * bits.length + 12 :=
  SubexpNormalizeProgram.emitIfSelected_steps_le selected bits

end SubexponentialSAT.SubexpIncidencePlanPrimitives

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpScopeMembershipProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
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

theorem stackMap_injective : Function.Injective stackMap := by decide

end SubexponentialSAT.SubexpScopeMembershipProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_AssignmentEnumeration
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Explicit enumerations for the conditional-expectation assignment

Words are enumerated by a finite recursion over the alphabet `List.finRange r`.
Seed indices are enumerated from supplied factor and vertex lists. Numeric
codes use `idxOf`, and inverse lookups use the same lists. No arbitrary finite
equivalence or choice operator occurs in these executable definitions.
-/

namespace SubexponentialSAT.Subexp.AssignmentEnumeration

open SubexponentialSAT.MulticolorTypes

section ChoiceDecoding

variable {I W : Type*}

/-- The search stores chosen values newest first; numerical coordinates use
the reverse list, so coordinate zero is the first choice. -/
theorem decode_eq_reverse_getD (default : W) (values : List W) (n : ℕ) :
    SubexponentialSAT.LocalExpectation.decode default values n = values.reverse.getD n default := by
  induction values with
  | nil => rfl
  | cons w values ih =>
    simp only [SubexponentialSAT.LocalExpectation.decode, List.reverse_cons]
    by_cases heq : n = values.length
    · subst n
      simp only [Function.update_self]
      rw [List.getD_append_right _ _ _ _ (by simp)]
      simp
    · rw [Function.update_of_ne heq, ih]
      by_cases hlt : n < values.length
      · rw [List.getD_append _ _ _ _ (by simpa using hlt)]
      · have hge : values.length + 1 ≤ n := by omega
        rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_succ_le hge),
          List.getD_eq_default _ _ (by simpa using hge)]

end ChoiceDecoding

end SubexponentialSAT.Subexp.AssignmentEnumeration

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PaddedCompletion
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Explicit padded completion leaves

Every optional coordinate branches over the entire word alphabet. A real
coordinate updates the assignment; a dummy coordinate ignores the word.
Padding therefore implements the common-denominator multiplicity by actual
finite leaves rather than a multiplication of the resulting score.
-/

namespace SubexponentialSAT.Subexp.PaddedCompletion

open SubexponentialSAT.LocalExpectation
open SubexponentialSAT.Subexp.LocalExpectation

variable {I W J : Type*} [DecidableEq I]

theorem trueCount_flatMap {α : Type*} (as : List α) (f : α → List Bool) :
    trueCount (as.flatMap f) = (as.map (fun a => trueCount (f a))).sum := by
  simp only [trueCount, successful, List.filter_flatMap, List.length_flatMap]

/-- Dummy coordinates repeat each terminal Boolean once for every tuple of
dummy word choices. -/
theorem trueCount_dummy (alphabet : List W) (f : (I → W) → Bool)
    (n : ℕ) (ω : I → W) :
    trueCount (leaves alphabet f (List.replicate n none) ω) =
      alphabet.length ^ n * boolValue (f ω) := by
  induction n with
  | zero => simp [leaves]
  | succ n ih =>
    simp only [List.replicate_succ, leaves, trueCount_flatMap, assignOptional]
    simp_rw [ih]
    rw [sum_map_const]
    simp only [pow_succ]
    ac_rfl

/-- Padding is precisely the common-denominator factor in the natural
completion count. This equality holds even before imposing the size bound. -/
theorem trueCount_some_append_dummy (alphabet : List W) (f : (I → W) → Bool)
    (remaining : List I) (n : ℕ) (ω : I → W) :
    trueCount (leaves alphabet f
      (remaining.map some ++ List.replicate n none) ω) =
        alphabet.length ^ n *
          completionCount alphabet (fun η => boolValue (f η)) remaining ω := by
  induction remaining generalizing ω with
  | nil => simpa [completionCount] using trueCount_dummy alphabet f n ω
  | cons i remaining ih =>
    simp only [List.map_cons, List.cons_append, leaves, trueCount_flatMap,
      assignOptional, completionCount]
    simp_rw [ih]
    exact List.sum_map_mul_left alphabet
      (fun w => completionCount alphabet (fun η => boolValue (f η))
        remaining (Function.update ω i w)) (alphabet.length ^ n)

theorem trueCount_paddedLeaves (alphabet : List W) (f : (I → W) → Bool)
    (remaining : List I) (S : ℕ) (ω : I → W) :
    trueCount (paddedLeaves alphabet f remaining S ω) =
      alphabet.length ^ (S - remaining.length) *
        completionCount alphabet (fun η => boolValue (f η)) remaining ω :=
  trueCount_some_append_dummy alphabet f remaining (S - remaining.length) ω

end SubexponentialSAT.Subexp.PaddedCompletion

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpIncidencePlanScan
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
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

def pushIndex (j : ℕ) (out : List Bool) : List Bool :=
  true :: (Encoding.frame (unary j) ++ out)

theorem incidenceFrom_length_le (v j : ℕ) (scopes : List (List ℕ)) :
    (Subexp.IncidencePlanSpec.incidenceFrom v j scopes).length ≤ scopes.length := by
  induction scopes generalizing j with
  | nil => rfl
  | cons C Cs ih =>
      have h := ih (j+1)
      by_cases hm : v ∈ C <;>
        simp [Subexp.IncidencePlanSpec.incidenceFrom,hm] <;> omega

end SubexponentialSAT.SubexpIncidencePlanScan

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpPlanAlphabetEmit
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Physical double framing for one vertex-plan alphabet entry. -/
namespace SubexponentialSAT.SubexpPlanAlphabetEmit

open BitProgram StructuredCalls Subexp.TupleProgram

abbrev transfer : Cmd 3 3 := .call (StackRoutines.transferProgram 0 1 0 1)

end SubexponentialSAT.SubexpPlanAlphabetEmit

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_UnaryTally
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# A fixed bit program tallying padded collision leaves

Each successful leaf pushes one false bit. The resulting unary stack is the
exact common numerator used for conditional expectation. This file proves the
actual instruction trace from a prepared Boolean leaf list.
-/

namespace SubexponentialSAT.Subexp.UnaryTally

open SubexponentialSAT.BitProgram SubexponentialSAT.Subexp.PaddedCompletion

abbrev program : Program 2 2 6 where
  inputStack := 0
  outputStack := 1
  entry := 0
  code q := match q.val with
    | 0 => .pop 0 0 1 1
    | 1 => .branch 1 2 5
    | 2 => .branch 0 3 0
    | 3 => .set 0 false 4
    | 4 => .push 1 0 0
    | _ => .halt

end SubexponentialSAT.Subexp.UnaryTally

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_CollisionGenerateProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
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

def resetList : List (Fin 10) → StructuredProgram.Cmd 10 20
  | [] => .skip
  | i :: rest => .seq (.atom (.set i false)) (resetList rest)

abbrev resetCommand : Cmd 10 20 := .base (resetList (List.finRange 10))

end SubexponentialSAT.Subexp.CollisionGenerateProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PairScoreProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
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

abbrev transfer (src dst : Fin 26) : Cmd 13 26 :=
  .call (transferProgram src dst 0 1)

abbrev copyDepth : Cmd 13 26 := .call (copyProgram 23 17 24 0 1)

def resetList : List (Fin 13) → StructuredProgram.Cmd 13 26
  | [] => .skip
  | i :: rest => .seq (.atom (.set i false)) (resetList rest)

abbrev resetInner : Cmd 13 26 := .base (resetList [0, 1, 2, 3, 4, 5, 6, 7, 8, 9])

abbrev tally : Cmd 13 26 :=
  .call (ProgramLinking.liftProgram UnaryTally.program tallyRegs tallyPorts)

end SubexponentialSAT.Subexp.PairScoreProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_CandidateScoreProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
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

/-- Six labels write the reverse of an escaped payload. Label 5 installs the
constant tag bit; the four-instruction loop consumes the runtime payload. -/
abbrev reverseEscapeProgram : Program 3 2 6 where
  inputStack := 0
  outputStack := 1
  entry := 5
  code := ![.pop 0 0 1 1, .branch 1 2 4, .push 1 2 3, .push 1 0 0,
    .halt, .set 2 true 0]

abbrev reverseWriter : Cmd 16 36 :=
  .call (ProgramLinking.liftProgram reverseEscapeProgram writerRegisters writerStacks)

abbrev transferCandidate : Cmd 16 36 := .call (StackRoutines.transferProgram 34 27 0 1)
abbrev copyPairs : Cmd 16 36 := .call (StackRoutines.copyProgram 31 20 33 0 1)

abbrev copyCandidates : Cmd 16 36 := .call (StackRoutines.copyProgram 30 29 33 0 1)

end SubexponentialSAT.Subexp.CandidateScoreProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MinimumProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
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

abbrev atom (a : StructuredProgram.Atom 9 8) : Cmd 9 8 := .base (.atom a)

abbrev copy (src dst : Fin 8) : Cmd 9 8 := .call (copyProgram src dst 5 3 4)

abbrev increment : Cmd 9 8 :=
  .seq (atom (.set 3 false)) (atom (.push 6 3))

end SubexponentialSAT.Subexp.MinimumProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_SequentialProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
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

abbrev atom (a : StructuredProgram.Atom 16 48) : Cmd 16 48 := .base (.atom a)

abbrev resetRegisters : Cmd 16 48 :=
  ([0, 1, 2, 3, 4, 5, 6, 7, 8] : List (Fin 16)).foldr
    (fun j rest => .seq (atom (.set j false)) rest) (.base .skip)

abbrev incrementProcessed : Cmd 16 48 :=
  .seq (atom (.set 9 false)) (atom (.push 19 9))

abbrev peekRemaining : Cmd 16 48 := atom (.peek 11 9 10)
abbrev dropRemaining : Cmd 16 48 := atom (.pop 11 9 10)

abbrev resetList (rs : List (Fin 16)) : Cmd 16 48 :=
  rs.foldr (fun j rest => .seq (atom (.set j false)) rest) (.base .skip)

end SubexponentialSAT.Subexp.SequentialProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingIncidenceInputEmit
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed writer for one double-framed two-address incidence plan. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput.Emit
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

theorem recordPorts_injective : Function.Injective recordPorts := by decide

abbrev copy (src : Fin 6) : Cmd 3 6 := .call (StackRoutines.copyProgram src 2 4 0 1)
theorem framePorts_injective : Function.Injective framePorts := by decide
end SubexponentialSAT.SqrtLog.PackingIncidenceInput.Emit

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_ActivePlanProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
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

abbrev copy (src dst tmp : Fin 12) : Cmd 10 12 := .call (copyProgram src dst tmp 0 1)

end SubexponentialSAT.Subexp.ActivePlanProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PairPlanPreparation
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual parsing and record-order preparation of the two plans in a pair
payload. Registers 0, 1, and 2 are scratch; all other registers are framed. -/

namespace SubexponentialSAT.Subexp.PairPlanPreparation

open BitProgram StackRoutines StructuredCalls

abbrev transfer (src dst : Fin 34) : Cmd 16 34 := .call (transferProgram src dst 0 1)

abbrev copy (src dst : Fin 34) : Cmd 16 34 := .call (copyProgram src dst 1 0 1)

abbrev seedOutputs : Cmd 16 34 := .base
  (.seq (.atom (.set 0 false)) (.seq (.atom (.push 6 0)) (.atom (.push 9 0))))

end SubexponentialSAT.Subexp.PairPlanPreparation

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PairPreparationProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
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

abbrev copy (src dst : Fin 34) : Cmd 16 34 := .call (copyProgram src dst 4 (0 : Fin 16) 1)

abbrev resetList : List (Fin 16) → StructuredProgram.Cmd 16 34
  | [] => .skip
  | i :: rest => .seq (.atom (.set i false)) (resetList rest)

abbrev resetInner : Cmd 16 34 := .base (resetList [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12])
abbrev resetTable : Cmd 16 34 := .base (resetList [0, 1, 2])
abbrev resetAll : Cmd 16 34 := .base (resetList (List.finRange 16))

def sequence : List (Cmd 16 34) → Cmd 16 34
  | [] => .base .skip
  | c :: cs => .seq c (sequence cs)

end SubexponentialSAT.Subexp.PairPreparationProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingIncidenceInputNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


/-! Convert a physically scanned factor-index stream to incidence plans. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput.Rows
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

theorem registers_injective : Function.Injective registers := Fin.castAdd_injective 3 3
theorem ports_injective : Function.Injective ports := by decide
def budget (h n : ℕ) : List ℕ → ℕ
  | [] => 0
  | j::js => 6*j + callbackBound h n j + 7 + budget h n js

end SubexponentialSAT.SqrtLog.PackingIncidenceInput.Rows


/-! Native per-variable incident-factor scan from the original scope stream. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput.Scan
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

theorem registers_injective : Function.Injective registers := Fin.castAdd_injective 10 6
theorem ports_injective : Function.Injective ports := Fin.castAdd_injective 10 22
end SubexponentialSAT.SqrtLog.PackingIncidenceInput.Scan


/-! Fixed cleanup for the native scope-address scanner. -/


/-! Calls to the fixed record mapper inside the native scope scan. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput.Lift
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp
theorem registers_injective : Function.Injective registers := Fin.castAdd_injective 6 10
theorem ports_injective : Function.Injective ports := by decide
end SubexponentialSAT.SqrtLog.PackingIncidenceInput.Lift


/-! One native low-variable step, including its uncovered neutral factor. -/


/-! Runtime high-mask loop for the original-address incidence stream. -/


/-! Count the physical scope stream before constructing native incidence plans. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput.Boot
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp
theorem registers_injective : Function.Injective registers := Fin.castAdd_injective 2 14
theorem ports_injective : Function.Injective ports := by decide
end SubexponentialSAT.SqrtLog.PackingIncidenceInput.Boot

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingIncidenceInputCost
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The native linear-plan builder has cubic cost in its actual input size. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput.Cost
open SubexponentialSAT.Subexp

theorem rows_budget_le (h n J : ℕ) (js : List ℕ) (hj : ∀ j ∈ js, j ≤ J) :
    Rows.budget h n js ≤ js.length * (207*(h+n+J+1)) := by
  induction js with
  | nil => simp [Rows.budget]
  | cons j js ih =>
      have hb := hj j (by simp)
      have ht := ih (fun k hk => hj k (by simp [hk]))
      simp only [Rows.budget,Rows.callbackBound,List.length_cons]
      nlinarith

end SubexponentialSAT.SqrtLog.PackingIncidenceInput.Cost

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_AssignmentInputState
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The physical input boundary for assignment-alphabet construction. -/

namespace SubexponentialSAT.Subexp.AssignmentInputProgram

open BitProgram StructuredCalls

abbrev Code := Cmd 16 48

end SubexponentialSAT.Subexp.AssignmentInputProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_AssignmentPairFrontend
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Physical raw-pair input for assignment setup

The actual all-vertex pair producer runs in a fixed private bank. Two stack
transfers place its bytes, in their original order, on assignment input 45.
The scope source and private bank are then cleared by actual instructions.
-/

namespace SubexponentialSAT.Subexp.AssignmentPairFrontend

open BitProgram StructuredCalls

abbrev Code := Cmd 16 48

def move : Code := .seq
  (.call (StackRoutines.transferProgram (0 : Fin 48) 7 (0 : Fin 16) 1))
  (.call (StackRoutines.transferProgram (7 : Fin 48) 45 (0 : Fin 16) 1))

end SubexponentialSAT.Subexp.AssignmentPairFrontend

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingIncidenceProgramInstall
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid generation and installation of raw pairs from a linear plan stream. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceProgram.Install
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

theorem registers_injective : Function.Injective registers := Fin.castAdd_injective 10 6
theorem ports_injective : Function.Injective ports := by decide

end SubexponentialSAT.SqrtLog.PackingIncidenceProgram.Install

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingIncidenceInputInstall
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Raw scope bytes and a mask produce the actual installed incidence-pair table. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput.Install
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp
theorem ports_injective : Function.Injective ports := by decide
end SubexponentialSAT.SqrtLog.PackingIncidenceInput.Install

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingPrefix
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Heads-first numbering and the actual reverse-list assignment prefix. -/
namespace SubexponentialSAT.SqrtLog.Packing
open scoped BigOperators
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.LocalExpectation

section Enumeration
variable {A B R : Type*} [DecidableEq A] [DecidableEq B]

theorem indexCode_map_injective (f : A → B) (hf : Function.Injective f)
    (xs : List A) (a : A) : indexCode (xs.map f) (f a) = indexCode xs a := by
  let _ : BEq A := instBEqOfDecidableEq
  let _ : BEq B := instBEqOfDecidableEq
  unfold indexCode
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hb : (f x == f a) = (x == a) := by
      apply Bool.eq_iff_iff.mpr
      simp [hf.eq_iff]
    simp only [List.map_cons, List.idxOf_cons, hb, ih]

end Enumeration

section Indices
variable {V E : Type*} [DecidableEq V] [DecidableEq E]

theorem headsFirst_index_head (vertices : List V) (factors : List E)
    (v : V) (hv : v ∈ vertices) :
    indexCode (headsFirstIndices vertices factors) (.inl v) = indexCode vertices v := by
  let _ : BEq (V ⊕ E) := instBEqOfDecidableEq
  unfold headsFirstIndices indexCode
  rw [List.idxOf_append_of_mem (by simpa using hv)]
  exact indexCode_map_injective Sum.inl Sum.inl_injective vertices v

theorem headsFirst_index_factor (vertices : List V) (factors : List E) (e : E) :
    indexCode (headsFirstIndices vertices factors) (.inr e) =
      vertices.length + indexCode factors e := by
  let _ : BEq (V ⊕ E) := instBEqOfDecidableEq
  unfold headsFirstIndices indexCode
  rw [List.idxOf_append_of_notMem (by simp)]
  simp only [List.length_map]
  congr 1
  exact indexCode_map_injective (Sum.inr : E → V ⊕ E) Sum.inr_injective factors e

omit [DecidableEq V] [DecidableEq E] in
theorem headsFirst_complete (vertices : List V) (factors : List E)
    (hv : ∀ v, v ∈ vertices) (he : ∀ e, e ∈ factors) :
    ∀ a, a ∈ headsFirstIndices vertices factors := by
  intro a
  cases a <;> simp [headsFirstIndices, hv, he]

end Indices

section Decoding
variable {W : Type*}

theorem decode_prefix_update (default candidate : W) (fixed : List W) :
    decode default (candidate :: fixed) = Function.update (decode default fixed) fixed.length candidate := rfl

end Decoding

section Sums
variable {V E W R : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    [AddCommMonoid R]

theorem headsFirst_prefix_sum (vertices : List V) (factors : List E)
    (hvn : vertices.Nodup) (hv : ∀ v, v ∈ vertices)
    (default : W) (fixed : List W) (hprefix : fixed.length ≤ vertices.length) (F : W → R) :
    (∑ v : V, if indexCode (headsFirstIndices vertices factors) (.inl v) < fixed.length
      then F (decode default fixed (indexCode (headsFirstIndices vertices factors) (.inl v)))
      else 0) = (fixed.map F).sum := by
  simp_rw [headsFirst_index_head vertices factors _ (hv _)]
  rw [← prefix_enumeration_sum vertices hvn hv]
  let G : ℕ → R := fun i => if i < fixed.length then F (decode default fixed i) else 0
  change (vertices.map (fun v => G (indexCode vertices v))).sum = _
  have hm : vertices.map (fun v => G (indexCode vertices v)) =
      (vertices.map (indexCode vertices)).map G := by
    simp only [List.map_map, Function.comp_def]
  rw [hm, map_idxOf_eq_range vertices hvn]
  rw [← List.sum_toFinset G List.nodup_range]
  have hset : (List.range vertices.length).toFinset = Finset.range vertices.length := by
    ext i
    simp
  rw [hset]
  have hsum : (∑ i ∈ Finset.range vertices.length, G i) =
      ∑ i ∈ Finset.range fixed.length, G i := by
    symm
    apply Finset.sum_subset (Finset.range_mono hprefix)
    intro i hi hnot
    simp only [Finset.mem_range] at hnot
    simp [G, hnot]
  rw [hsum]
  simp only [G]
  have hremove : (∑ i ∈ Finset.range fixed.length,
      if i < fixed.length then F (decode default fixed i) else 0) =
      ∑ i ∈ Finset.range fixed.length, F (decode default fixed i) := by
    apply Finset.sum_congr rfl
    intro i hi
    simp [Finset.mem_range.mp hi]
  rw [hremove]
  have hget : (∑ i ∈ Finset.range fixed.length, F (decode default fixed i)) =
      (fixed.reverse.map F).sum := by
    have hrev : (∑ i ∈ Finset.range fixed.reverse.length, F (fixed.reverse.getD i default)) =
        (fixed.reverse.map F).sum := by
      rw [Finset.sum_range]
      calc
        _ = ∑ i : Fin fixed.reverse.length, F fixed.reverse[i.val] := by
          apply Finset.sum_congr rfl
          intro i _
          rw [List.getD_eq_getElem _ _ i.isLt]
        _ = _ := Fin.sum_univ_fun_getElem fixed.reverse F
    simpa only [List.length_reverse, SubexponentialSAT.Subexp.AssignmentEnumeration.decode_eq_reverse_getD] using hrev
  rw [hget, List.map_reverse, List.sum_reverse]
end Sums

end SubexponentialSAT.SqrtLog.Packing

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingIncidenceInputSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Typed original-variable/factor semantics of the native address list. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput.Semantics
open SubexponentialSAT.Subexp

theorem seedIndices_complete (n f : ℕ) : ∀ x, x ∈ seedIndices n f :=
  Packing.headsFirst_complete _ _ List.mem_finRange List.mem_finRange

end SubexponentialSAT.SqrtLog.PackingIncidenceInput.Semantics

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_AssignmentInitProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Physical initialization of the sequential assignment memory

The input contains the already generated alphabet and incidence records.
This fixed routine duplicates the runtime tables, creates the initial packed
assignment by actual repeated copying, and clears all temporary ports. The
production of the input records is a separate frontend stage.
-/

namespace SubexponentialSAT.Subexp.AssignmentInitProgram

open BitProgram StructuredCalls StackRoutines

abbrev reset : Cmd 16 48 := SequentialProgram.resetList (List.finRange 16)
abbrev copyRemaining : Cmd 16 48 := .call (copyProgram 47 11 1 (0 : Fin 16) 1)
abbrev copyCounter : Cmd 16 48 := .call (copyProgram 47 2 1 (0 : Fin 16) 1)
abbrev copyAlphabet : Cmd 16 48 := .call (copyProgram 30 39 1 (0 : Fin 16) 1)

def sourceCost (ctx : Context) : ℕ :=
  ctx.seedCount * (7 * ctx.defaultWord.length + 21) +
    7 * ctx.alphabetRecords.length + 2 * ctx.defaultWord.length + 38

theorem sourceCost_le (ctx : Context) (B : ℕ)
    (hcount : ctx.seedCount ≤ B) (hword : ctx.defaultWord.length ≤ B)
    (halphabet : ctx.alphabetRecords.length ≤ B) :
    sourceCost ctx ≤ 40 * (B + 1) ^ 2 := by
  calc
    sourceCost ctx ≤ B * (7 * B + 21) + 7 * B + 2 * B + 38 := by
      unfold sourceCost
      gcongr
    _ ≤ 40 * (B + 1) ^ 2 := by nlinarith

end SubexponentialSAT.Subexp.AssignmentInitProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_AssignmentInputCall
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! One-output physical calls in the assignment-input workspace. -/

namespace SubexponentialSAT.Subexp.AssignmentInputCall

open BitProgram StructuredCalls SubexpSetupStorage

abbrev Code := Cmd 16 48

end SubexponentialSAT.Subexp.AssignmentInputCall

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_AssignmentRecordViews
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed parser-based views of an actual framed word alphabet. -/

namespace SubexponentialSAT.Subexp.AssignmentRecordViews

open BitProgram StructuredCalls TupleProgram

abbrev setFlag : Cmd 3 3 := .base (.atom (.set 2 false))

end SubexponentialSAT.Subexp.AssignmentRecordViews

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingProgramAssemblyBasic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete stack transport for the combined packing score producer. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram.Assembly
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

abbrev move (src dst tmp : Fin 48) : Cmd 16 48 :=
  .seq (.call (transferProgram src tmp 0 1))
    (.call (transferProgram tmp dst 0 1))

def moveMany : List (Fin 48 × Fin 48) → Cmd 16 48
  | [] => .base .skip
  | (src,dst)::rest => .seq (move src dst 16) (moveMany rest)

end SubexponentialSAT.SqrtLog.PackingProgram.Assembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingProgramAssemblyMetadata
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid parking of four runtime integer parameters around the incidence scorer. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram.Assembly
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

abbrev park : Cmd 16 48 := moveMany metadata
abbrev unpark : Cmd 16 48 := moveMany (metadata.map Prod.swap)

end SubexponentialSAT.SqrtLog.PackingProgram.Assembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingPrefixScore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact head-term enumeration and physical prefix overlap. -/
namespace SubexponentialSAT.SqrtLog.Packing
open scoped BigOperators
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.LocalExpectation

section Terms
variable {I V R : Type*} [Fintype V] [DecidableEq V] [AddCommMonoid R]

def headScoreTerms (vertices : List V) (Q : ℕ) : List (ScoreTerm I V Q) :=
  (List.finRange Q).flatMap (fun t => (vertices.product vertices).map
    (fun pair => Sum.inr (t, pair.1, pair.2)))

theorem headScoreTerms_sum (vertices : List V) (hvn : vertices.Nodup)
    (hv : ∀ v, v ∈ vertices) (Q : ℕ) (F : ScoreTerm I V Q → R) :
    ((headScoreTerms vertices Q).map F).sum =
      ∑ t : Fin Q, ∑ v : V, ∑ w : V, F (.inr (t,v,w)) := by
  have hp : (vertices.product vertices).Nodup := hvn.product hvn
  have hpf : ∀ p : V × V, p ∈ vertices.product vertices := by
    intro p
    exact List.mem_product.mpr ⟨hv p.1, hv p.2⟩
  simp only [headScoreTerms, List.map_flatMap, prefix_sum_flatMap, List.map_map,
    Function.comp_def]
  simp_rw [prefix_enumeration_sum (vertices.product vertices) hp hpf]
  rw [prefix_enumeration_sum (List.finRange Q) (List.nodup_finRange Q) (by simp)]
  simp only [Fintype.sum_prod_type]
end Terms

section Prior
variable {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
variable {r Q : ℕ}

omit [Fintype V] in
/-- Excluding the fresh key and its future suffix retains exactly earlier head keys. -/
theorem headsFirst_prior_iff (vertices : List V) (factors : List E)
    (hv : ∀ v, v ∈ vertices) (p n : ℕ)
    (hsize : n + 1 + p = (headsFirstIndices vertices factors).length) (v : V) :
    ¬ (indexCode (headsFirstIndices vertices factors) (.inl v) = p ∨
      indexCode (headsFirstIndices vertices factors) (.inl v) ∈ List.range' (p+1) n) ↔
      indexCode (headsFirstIndices vertices factors) (.inl v) < p := by
  simp only [headsFirst_index_head vertices factors v (hv v)]
  have hpos : indexCode vertices v < vertices.length := List.idxOf_lt_length_iff.mpr (hv v)
  rw [headsFirst_length] at hsize
  simp only [List.mem_range'_1]
  omega

end Prior
end SubexponentialSAT.SqrtLog.Packing

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingHeadProgramAnd
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed bit zipper counts coordinate matches of one-hot words by counting
true bitwise intersections. It consumes one candidate copy and the same number
of table bits, preserving the remaining table suffix. -/
namespace SubexponentialSAT.SqrtLog.PackingHeadProgramAnd
open SubexponentialSAT BitProgram StructuredCalls

abbrev program : Program 5 3 11 where
  inputStack := 0
  outputStack := 2
  entry := 0
  code := ![.pop 0 0 1 1, .branch 1 2 7, .pop 1 2 3 3,
    .branch 0 4 0, .branch 2 5 0, .set 4 false 6, .push 2 4 0,
    .set 2 false 8, .set 3 false 9, .set 4 false 10, .halt]

end SubexponentialSAT.SqrtLog.PackingHeadProgramAnd

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingHeadProgramPrefix
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed counted loop over the existing flattened head prefix. Every
iteration copies the candidate and counts its true bitwise intersections with
one prefix word. No per-coordinate metadata or selected-pair stream is supplied. -/
namespace SubexponentialSAT.SqrtLog.PackingHeadProgramPrefix
open SubexponentialSAT BitProgram StructuredCalls StackRoutines

abbrev guard : Cmd 5 6 := .base (.atom (.pop 5 0 1))

abbrev copy : Cmd 5 6 := .call (copyProgram 0 2 3 0 1)

abbrev zip : Cmd 5 6 := .call (ProgramLinking.liftProgram PackingHeadProgramAnd.program id zipPorts)

abbrev body : Cmd 5 6 := .seq copy (.seq zip guard)
abbrev loop : Cmd 5 6 := .while 1 body
abbrev command : Cmd 5 6 := .seq guard loop

abbrev program : Program 5 6 (size command+1) := compiled command 0 4

end SubexponentialSAT.SqrtLog.PackingHeadProgramPrefix

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingHeadProgramPreserve
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A source-preserving wrapper for the actual prefix scan. The only input
streams are one candidate, the flattened prior words, and their unary count. -/
namespace SubexponentialSAT.SqrtLog.PackingHeadProgramPreserve
open SubexponentialSAT BitProgram StructuredCalls StackRoutines
open scoped BigOperators

abbrev copyTable : Cmd 5 8 := .call (copyProgram 1 6 2 0 1)
abbrev copyCount : Cmd 5 8 := .call (copyProgram 5 7 2 0 1)

abbrev scan : Cmd 5 8 :=
  .call (ProgramLinking.liftProgram PackingHeadProgramPrefix.program id ports)

abbrev command : Cmd 5 8 := .seq copyTable (.seq copyCount scan)
abbrev program : Program 5 8 (size command+1) := compiled command 0 4

end SubexponentialSAT.SqrtLog.PackingHeadProgramPreserve

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpInputFrames
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual frame and tag readers for the row/input-pair stream. -/

namespace SubexponentialSAT.SubexpInputFrames

open BitProgram StructuredCalls

abbrev readTag {S : ℕ} (source : Fin S) : Cmd 8 S := .base (.atom (.pop source 7 6))

end SubexponentialSAT.SubexpInputFrames

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpInputZip
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Physical pairing of row and input-coordinate streams

Two ordinary framed lists are read on stacks 0 and 1. The fixed program builds
the exact paired-record stream consumed by `SubexpDotControl`, on stack 6.
No array lookup, pairing, or serialization is a semantic machine instruction.
-/

namespace SubexponentialSAT.SubexpInputZip

open BitProgram StructuredCalls

abbrev move (src dst : Fin 8) : Cmd 8 8 := .call (StackRoutines.transferProgram src dst 0 1)

abbrev popPair : Cmd 8 8 := .base (.atom (.pop 4 0 1))

abbrev tags : Cmd 8 8 :=
  .seq (SubexpInputFrames.readTag 0) (.base (.atom (.pop 1 0 1)))

abbrev finish : Cmd 8 8 :=
  .seq (.base (.atom (.set 0 false)))
    (.seq (.base (.atom (.push 5 0))) (move 5 6))

end SubexponentialSAT.SubexpInputZip

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingWeightProgramBasic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
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

def ports (i : Fin 4) : Ports 13 where
  left := ![0,6,2,7] i
  right := ![1,6,3,7] i
  out := ![6,4,7,5] i
  work := work
  out_ne_left := by fin_cases i <;> decide
  out_ne_right := by fin_cases i <;> decide
  work_ne_left := by intro j; fin_cases i <;> fin_cases j <;> decide
  work_ne_right := by intro j; fin_cases i <;> fin_cases j <;> decide
  work_ne_out := by intro j; fin_cases i <;> fin_cases j <;> decide

end SubexponentialSAT.SqrtLog.PackingWeightProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingCallerProgramModel
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PackingCallerProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open PackingLoaderProgram PackingIncidenceInput

structure Workspace (outside : Store) : Prop where
  temp : outside 52=[]
  width : outside 53=[]
  alphabet : outside 54=[]
  scopes : outside 60=[]
  plans : outside 61=[]
  words : outside 62=[]
  metadata : outside 63=[]

end SubexponentialSAT.SqrtLog.PackingCallerProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingCallerProgramExport
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid export of the computed word table, metadata, and original plans,
followed by erasure of the private bank and parking of the source masters. -/
namespace SubexponentialSAT.SqrtLog.PackingCallerProgram.Wide
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage
attribute [local simp] Fin.coe_ofNat_eq_mod

def exportPairs : List (Fin 768 × Fin 768) :=
  [(ports 62,133),(ports 63,135),(ports 61,136)]
def privatePorts : List (Fin 768) := (List.finRange 64).map ports

theorem mem_privatePorts (i : Fin 768) :
    i∈privatePorts ↔ 417 ≤ i.val ∧ i.val < 481 := by
  simp only [privatePorts,List.mem_map,List.mem_finRange,true_and]
  constructor
  · rintro ⟨j,rfl⟩; have := j.isLt; change 417 ≤ 417+j.val ∧ 417+j.val < 481; omega
  · rintro ⟨hl,hu⟩
    refine ⟨⟨i.val-417,by omega⟩,?_⟩
    apply Fin.ext
    change 417+(i.val-417)=i.val
    omega

end SubexponentialSAT.SqrtLog.PackingCallerProgram.Wide

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingCallerProgramStage
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid copies from the actual query frontend's persistent master bank. -/
namespace SubexponentialSAT.SqrtLog.PackingCallerProgram.Wide
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage
open PackingLoaderProgram PackingIncidenceInput
attribute [local simp] Fin.coe_ofNat_eq_mod

def stagePairs : List (Fin 768 × Fin 768) :=
  [(718,ports 32),(128,ports 33),(719,ports 36),
   (720,ports 55),(709,ports 56),(722,ports 57),(723,ports 58),(721,ports 59)]

end SubexponentialSAT.SqrtLog.PackingCallerProgram.Wide

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingCallerProgramBoundsPolynomial
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PackingCallerProgram.Bounds
open CostAssembly.Polynomial
open SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes

theorem planEnvelope_ordinary : Ordinary planEnvelope := by
  unfold planEnvelope
  exact (ordinary_add (ordinary_const 1) (ordinary_mul (ordinary_add (ordinary_mul (ordinary_const 16) (ordinary_mul (ordinary_const 2) ordinary_id)) (ordinary_const 24)) ordinary_id))

theorem seedEnvelope_ordinary : Ordinary seedEnvelope := by
  unfold seedEnvelope
  exact (ordinary_add (ordinary_const 1) (ordinary_mul (ordinary_add (ordinary_mul (ordinary_const 2) (ordinary_mul (ordinary_const 2) ordinary_id)) (ordinary_const 2)) (ordinary_mul (ordinary_const 2) ordinary_id)))

end SubexponentialSAT.SqrtLog.PackingCallerProgram.Bounds

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingCallerProgramExportCost
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PackingCallerProgram.Wide
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem export_sep : ∀ p∈exportPairs,∀ q∈exportPairs,p.1≠q.2 := by
  intro p hp q hq
  simp only [exportPairs,List.mem_cons,List.not_mem_nil,or_false] at hp hq
  rcases hp with rfl|rfl|rfl <;> rcases hq with rfl|rfl|rfl <;> decide

end SubexponentialSAT.SqrtLog.PackingCallerProgram.Wide

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingCallerProgramCost
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PackingCallerProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes SubexponentialSAT.SubexpSetupStorage
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem stage_separated : ∀ p∈Wide.stagePairs,∀ q∈Wide.stagePairs,p.1≠q.2 := by
  intro p hp q hq h
  have hsrc : p.1.val < 417 ∨ 481 ≤ p.1.val := by
    simp only [Wide.stagePairs,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num
  have hdst : 417 ≤ q.2.val ∧ q.2.val < 481 := by
    simp only [Wide.stagePairs,List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      simp only [Wide.ports_val] <;> omega
  have := congrArg Fin.val h
  omega

end SubexponentialSAT.SqrtLog.PackingCallerProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingCallerProgramReplay
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The native packing caller neither reads nor writes the outer carried
tapes. Their contents therefore do not affect its exact running time. -/
namespace SubexponentialSAT.SqrtLog.PackingCallerProgram.Replay
open SubexponentialSAT BitProgram StructuredCalls
open LeafProgram.OuterCarried
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem away (i : Fin 768) (hi : i.val < 320 ∨ 332 < i.val) : ¬ LeafProgram.OuterCarried.hidden i := by
  intro hh
  simp only [LeafProgram.OuterCarried.hidden,List.mem_cons,List.not_mem_nil,or_false] at hh
  rcases hh with rfl|rfl|rfl  <;>  norm_num at hi

theorem bank_away (i : Fin 64) : ¬ LeafProgram.OuterCarried.hidden (Wide.ports i) :=
  away _ (Or.inr (by change 332 < 417+i.val; omega))

theorem low_away (i : Fin 14) : ¬ LeafProgram.OuterCarried.hidden (LeafProgram.LayoutMasters.low i) :=
  away _ (Or.inl (by change 128+i.val < 320; have := i.isLt; omega))

theorem high_away (i : Fin 14) : ¬ LeafProgram.OuterCarried.hidden (LeafProgram.LayoutMasters.high i) :=
  away _ (Or.inr (by change 332 < 730+i.val; omega))

end SubexponentialSAT.SqrtLog.PackingCallerProgram.Replay

end OAI.Algorithms
end


