-- Prove2me | Definitions.Def_OAIQ081S061
-- name    : OAIQ081S061
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T21:46:49.264454+00:00
-- url     : https://prove2.me/theorems/29053ab6-0d71-473b-838f-e075dc645e1c
-- title:
--   Definitions bundle OAIQ081S061 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 137 declarations of OpenAI's Lean: 101 definitions and 36 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.twoWordEquiv`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgram.prepareBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingHeadProgramCandidates.ports`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInput.Boot.budget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInput.Boot.fullBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInput.Cost.inputSize`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInput.Emit.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInput.Emit.record`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInput.Entry.sourceStacks`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInput.Lift.cleanBound`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInput.Loop.budget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInput.Scan.bound`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInput.Step.bound`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceProgram.incidencePlans`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingWeightProgram.clear`, `OAI.Algorithms.SubexponentialSAT.Subexp.ActivePlanProgram.clear`, `OAI.Algorithms.SubexponentialSAT.Subexp.ActivePlanProgram.compare`, `OAI.Algorithms.SubexponentialSAT.Subexp.ActivePlanProgram.compareCall`, `OAI.Algorithms.SubexponentialSAT.Subexp.ActivePlanProgram.initAccumulator`, `OAI.Algorithms.SubexponentialSAT.Subexp.ActivePlanProgram.initializeOutput`, `OAI.Algorithms.SubexponentialSAT.Subexp.ActivePlanProgram.ports`, `OAI.Algorithms.SubexponentialSAT.Subexp.AssignmentInitProgram.clearDefault`, `OAI.Algorithms.SubexponentialSAT.Subexp.AssignmentInitProgram.command`, `OAI.Algorithms.SubexponentialSAT.Subexp.AssignmentInitProgram.program`, `OAI.Algorithms.SubexponentialSAT.Subexp.AssignmentInitProgram.repeatDefault`, `OAI.Algorithms.SubexponentialSAT.Subexp.AssignmentPairFrontend.Data`, `OAI.Algorithms.SubexponentialSAT.Subexp.CandidateArrayProgram.command`, `OAI.Algorithms.SubexponentialSAT.Subexp.CandidateArrayProgram.program`, `OAI.Algorithms.SubexponentialSAT.Subexp.CandidateArrayProgram.replace`, `OAI.Algorithms.SubexponentialSAT.Subexp.CandidateScoreProgram.cleanup`, `OAI.Algorithms.SubexponentialSAT.Subexp.CandidateScoreProgram.outerPorts`, `OAI.Algorithms.SubexponentialSAT.Subexp.CandidateScoreProgram.resetLow`, `OAI.Algorithms.SubexponentialSAT.Subexp.CandidateScoreProgram.updateCandidate`, `OAI.Algorithms.SubexponentialSAT.Subexp.CollisionGenerateProgram.clearWork`, `OAI.Algorithms.SubexponentialSAT.Subexp.CollisionTupleProgram.ports`, `OAI.Algorithms.SubexponentialSAT.Subexp.MinimumProgram.Data`, `OAI.Algorithms.SubexponentialSAT.Subexp.MinimumProgram.callback`, `OAI.Algorithms.SubexponentialSAT.Subexp.MinimumProgram.cleanup`, `OAI.Algorithms.SubexponentialSAT.Subexp.MinimumProgram.clear`, `OAI.Algorithms.SubexponentialSAT.Subexp.MinimumProgram.command` and 61 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLog_PackingAlgorithm`, `SubexponentialSAT_SqrtLog_PackingCallerProgramBoundsPolynomial`, `SubexponentialSAT_SqrtLog_PackingCallerProgramPrepare`, `SubexponentialSAT_SqrtLog_PackingCompletion`, `SubexponentialSAT_SqrtLog_PackingHeadProgramCandidates`, `SubexponentialSAT_SqrtLog_PackingIncidenceInputCost`, `SubexponentialSAT_SqrtLog_PackingIncidenceInputEmit`, `SubexponentialSAT_SqrtLog_PackingIncidenceInputEntry`, `SubexponentialSAT_SqrtLog_PackingIncidenceInputNative`, `SubexponentialSAT_SqrtLog_PackingIncidenceProgramGenerated`, `SubexponentialSAT_SqrtLog_PackingLoaderProgramBounds`, `SubexponentialSAT_SqrtLog_PackingWeightProgramBasic`, `SubexponentialSAT_SqrtLog_PackingWords`, `SubexponentialSAT_SubexpIncidencePlanPrimitives`, `SubexponentialSAT_SubexpIncidencePlanProgram`, `SubexponentialSAT_SubexpIncidencePlanScan`, `SubexponentialSAT_SubexpInputFrames`, `SubexponentialSAT_SubexpInputZip`, `SubexponentialSAT_SubexpPlanAlphabetEmit`, `SubexponentialSAT_SubexpSunflowerProgram`, `SubexponentialSAT_Subexp_ActivePlanProgram`, `SubexponentialSAT_Subexp_AssignmentInitProgram`, `SubexponentialSAT_Subexp_AssignmentPairFrontend`, `SubexponentialSAT_Subexp_CandidateArrayProgram`, `SubexponentialSAT_Subexp_CandidateScoreProgram`, `SubexponentialSAT_Subexp_CandidateScoreRefinement`, `SubexponentialSAT_Subexp_CollisionGenerateProgram`, `SubexponentialSAT_Subexp_CollisionTupleProgram`, `SubexponentialSAT_Subexp_MinimumProgram`, `SubexponentialSAT_Subexp_OneHotAlphabetProgram`, `SubexponentialSAT_Subexp_PairPlanPreparation`, `SubexponentialSAT_Subexp_PairPreparationProgram`, `SubexponentialSAT_Subexp_PairScoreProgram`, `SubexponentialSAT_Subexp_ScoreBuilderInputBounds`, `SubexponentialSAT_Subexp_ScoreBuilderPorts`, `SubexponentialSAT_Subexp_SelectionTableProgram`, `SubexponentialSAT_Subexp_SelectorPairProgram`, `SubexponentialSAT_Subexp_SequentialProgram`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S023`, `OAIQ081S024`, `OAIQ081S025`, `OAIQ081S026`, `OAIQ081S028`, `OAIQ081S029`, `OAIQ081S032`, `OAIQ081S035`, `OAIQ081S037`, `OAIQ081S039` and `OAIQ081S040` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S078`, `OAIQ081S079` and `OAIQ081S080`; the proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.MassPreserve.command_eval`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S023
import Definitions.Def_OAIQ081S024
import Definitions.Def_OAIQ081S025
import Definitions.Def_OAIQ081S026
import Definitions.Def_OAIQ081S028
import Definitions.Def_OAIQ081S029
import Definitions.Def_OAIQ081S032
import Definitions.Def_OAIQ081S035
import Definitions.Def_OAIQ081S037
import Definitions.Def_OAIQ081S039
import Definitions.Def_OAIQ081S040

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingWords
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.compatibleDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.spectatorsAgreeDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.instDecidableAnchorValid
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

def twoWordEquiv (r Q : ℕ) : (Bool → Word r Q) ≃ UniversalType r Q 1 where
  toFun f := ⟨f false, fun _ => f true⟩
  invFun u b := if b then u.slot 0 else u.head
  left_inv f := by funext b; cases b <;> rfl
  right_inv u := by
    apply UniversalType.ext
    · rfl
    · funext i
      have : i = 0 := Subsingleton.elim _ _
      subst i
      rfl

end Incidences
end
end SubexponentialSAT.SqrtLog.Packing

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingAlgorithm
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
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

variable [NeZero r]

omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] in
theorem numberedScoreSupport_card_le (indices : List (V ⊕ E)) (z : ScoreTerm I V Q) :
    (numberedScoreSupport ivar factor indices z).card ≤ 4 :=
  Finset.card_image_le.trans (scoreSupport_card_le ivar factor z)

end Algorithm
end SubexponentialSAT.SqrtLog.Packing

end OAI.Algorithms
end

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

abbrev Data := StructuredProgram.State 10 10

def incremented (dst : Fin 10) (d : Data) : Data :=
  ⟨Function.update d.regs 0 true, Function.update d.stacks dst (true :: d.stacks dst)⟩

def copied (src dst : Fin 10) (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.copyStacks src dst d.stacks⟩

theorem copy_eval (src dst tmp : Fin 10) (d : Data)
    (hsd : src ≠ dst) (hst : src ≠ tmp) (htd : tmp ≠ dst) (ht : d.stacks tmp = []) :
    Eval (copy src dst tmp) (7 * (d.stacks src).length + 5) d (copied src dst d) :=
  .call _ (ListRegisterProgram.copy_run src dst tmp 0 1 hsd hst htd (by decide)
    d.regs d.stacks ht)

end SubexponentialSAT.SubexpIncidencePlanPrimitives

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

abbrev Data := StructuredProgram.State 10 10

def data (regs : Fin 10 → Bool) (v j : ℕ) (source output payload : List Bool)
    (degree : ℕ) : Data :=
  ⟨regs, ![[], [], (Encoding.encodeNat v).reverse, [], [], unary j,
    source, output, payload, unary degree]⟩

def addedDegree (selected : Bool) (d : Data) : Data :=
  if selected then incremented 9 d else d

/-- The actual scan cost is polynomial in the encoded pattern and unary query. -/
theorem scanBudget_le (v j : ℕ) (scopes : List (List ℕ)) :
    scanBudget v j scopes ≤
      (128*(v+2)+16*(j+scopes.length+2)+20) *
        (Encoding.encodeList scopeBytes scopes).length := by
  induction scopes generalizing j with
  | nil => simp [scanBudget]
  | cons C Cs ih =>
      have h := ih (j+1)
      simp only [scanBudget,callbackBound,Encoding.length_encodeList_cons,List.length_cons]
      nlinarith

end SubexponentialSAT.SubexpIncidencePlanScan

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpIncidencePlanProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Encoded scopes to a concrete incidence read plan

This is one fixed finite program. Runtime stacks supply the encoded scope list,
the vertex token, and unary D and Delta. No slot assignment is supplied to the
machine. Incident slots are allocated in outer-list encounter order.
-/
namespace SubexponentialSAT.SubexpIncidencePlanProgram

open BitProgram StructuredCalls

theorem encode_indexPrefix (js : List ℕ) :
    SubexpIncidencePlanScan.indexPrefix js ++ [false] =
      ProgramEncoding.encodeRecords (js.map unary) := by
  induction js with
  | nil => rfl
  | cons j js ih =>
      simp [SubexpIncidencePlanScan.indexPrefix,ProgramEncoding.encodeRecords,Encoding.encodeList,
        List.append_assoc] at ih ⊢
      exact ih

end SubexponentialSAT.SubexpIncidencePlanProgram

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

abbrev Data := State 3 3

def data (regs : Fin 3 → Bool) (input scratch output : List Bool) : Data :=
  ⟨regs,![input,scratch,output]⟩

def innerPorts : RecordPrograms.Ports 3 3 :=
  ⟨0,1,2,1,0,by decide,by decide,by decide,by decide⟩
def outerPorts : RecordPrograms.Ports 3 3 :=
  ⟨0,1,2,1,2,by decide,by decide,by decide,by decide⟩

def transferred (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none,StackRoutines.transferStacks 0 1 d.stacks⟩

end SubexponentialSAT.SubexpPlanAlphabetEmit

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_CandidateArrayProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# A temporary candidate assignment with fixed control

The current assignment, candidate word, processed-position counter, and width
are preserved. The program copies the assignment and replaces precisely the
processed word in that copy. No restore of the original assignment is needed.
-/

namespace SubexponentialSAT.Subexp.CandidateArrayProgram

open BitProgram StructuredCalls StackRoutines

abbrev replace : Cmd 2 10 := .call (ProgramLinking.liftProgram
  (ArrayUpdatePrograms.replaceProgram (0 : Fin 2) 1) id replacePorts)

abbrev command : Cmd 2 10 :=
  .seq (.call (copyProgram 0 8 4 (0 : Fin 2) 1))
    (.seq (.call (copyProgram 2 9 4 (0 : Fin 2) 1)) replace)

abbrev program : Program 2 10 (size command + 1) := compiled command 0 8

end SubexponentialSAT.Subexp.CandidateArrayProgram

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

def ports : RecordPrograms.Ports 8 18 where
  tag := 5
  present := 6
  found := 7
  source := 16
  payload := 17
  tag_ne_present := by decide
  found_ne_tag := by decide
  found_ne_present := by decide
  source_ne_payload := by decide

theorem streamed_trueCount (current : List Bool) (width : ℕ) (left right : List ℕ)
    (tuples : List (List Bool)) (stream : List Bool) :
    PaddedCompletion.trueCount (streamed current width left right tuples stream) =
      PaddedCompletion.trueCount (tuples.map (leafBit current width left right)) +
        PaddedCompletion.trueCount stream := by
  rw [streamed_eq_reverse_map]
  simp [PaddedCompletion.trueCount, PaddedCompletion.successful, List.filter_reverse]

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

abbrev clearWork : Cmd 10 20 := .call (clearProgram 6 0 1)

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

def ports : RecordPrograms.Ports 13 26 where
  tag := 10
  present := 11
  found := 12
  source := 20
  payload := 21
  tag_ne_present := by decide
  found_ne_tag := by decide
  found_ne_present := by decide
  source_ne_payload := by decide

def fieldPorts : RecordPrograms.Ports 13 26 where
  tag := 0
  present := 1
  found := 2
  source := 22
  payload := 25
  tag_ne_present := by decide
  found_ne_tag := by decide
  found_ne_present := by decide
  source_ne_payload := by decide

abbrev clear (src : Fin 26) : Cmd 13 26 := .call (clearProgram src 0 1)

abbrev prepare : Cmd 13 26 :=
  .seq (transfer 21 22) (.seq (RecordPrograms.reader fieldPorts)
    (.seq (transfer 25 14) (.seq (RecordPrograms.reader fieldPorts)
      (.seq (transfer 25 15) (.seq copyDepth resetInner)))))

abbrev cleanup : Cmd 13 26 := .seq (clear 14) (.seq (clear 15) resetInner)

end SubexponentialSAT.Subexp.PairScoreProgram

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

abbrev resetLow : Cmd 16 36 := .base (resetList ((List.finRange 13).map lowRegisters))

def outerPorts : RecordPrograms.Ports 16 36 :=
  ⟨13,14,15,29,34,by decide,by decide,by decide,by decide⟩

abbrev updateCandidate : Cmd 16 36 :=
  .call (ProgramLinking.liftProgram CandidateArrayProgram.program arrayRegisters arrayStacks)
abbrev cleanup : Cmd 16 36 :=
  .seq (.call (StackRoutines.clearProgram 13 0 1))
    (.call (StackRoutines.clearProgram 27 0 1))

end SubexponentialSAT.Subexp.CandidateScoreProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_OneHotAlphabetProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Runtime one-hot alphabet generation

The unary input length r is data. Each loop iteration constructs one r-bit
one-hot word using the checked repeated-copy program and prepends its frame.
The final order is the decreasing order of the hot bit's position.
-/

namespace SubexponentialSAT.Subexp.OneHotAlphabetProgram

open BitProgram StructuredCalls TupleProgram

def emitter : RecordPrograms.Ports 5 7 :=
  ⟨0, 1, 2, 2, 6, by decide, by decide, by decide, by decide⟩

end SubexponentialSAT.Subexp.OneHotAlphabetProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MinimumProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
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

abbrev Data := State 9 8

def ports : RecordPrograms.Ports 9 8 where
  tag := 0
  present := 1
  found := 2
  source := 0
  payload := 1
  tag_ne_present := by decide
  found_ne_tag := by decide
  found_ne_present := by decide
  source_ne_payload := by decide

abbrev clear (dst : Fin 8) : Cmd 9 8 := .call (clearProgram dst 3 4)

abbrev comparator : Program 9 8 7 :=
  ProgramLinking.liftProgram UnaryCompare.program compareRegs compareStacks

abbrev cleanup : Cmd 9 8 :=
  .seq (clear 1) (.seq (clear 3) (.seq (clear 4) increment))

abbrev replaceBest : Cmd 9 8 :=
  .seq (clear 2) (.seq (copy 1 2) (.seq (clear 7) (copy 6 7)))

abbrev callback : Cmd 9 8 :=
  .seq (copy 2 3) (.seq (copy 1 4)
    (.seq (.call comparator)
      (.seq (.ite 8 (.base .skip) replaceBest) cleanup)))

abbrev initBest : Cmd 9 8 :=
  .seq (copy 1 2) (.seq (clear 1) increment)

/-- The program is one fixed finite instruction table for every nonempty list. -/
abbrev command : Cmd 9 8 :=
  .seq (RecordPrograms.atom (.set ports.found false))
    (.seq (RecordPrograms.atom (.pop ports.source ports.tag ports.present))
      (.seq (RecordPrograms.reader ports)
        (.seq initBest (RecordPrograms.iterate ports callback))))

abbrev program : Program 9 8 (StructuredCalls.size command + 1) :=
  StructuredCalls.compiled command 0 7

def emptyData : Data := ⟨fun _ => false, fun _ => []⟩

end SubexponentialSAT.Subexp.MinimumProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_SequentialProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
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

abbrev minimumProgram : Program 16 48 (size MinimumProgram.command + 1) :=
  ProgramLinking.liftProgram MinimumProgram.program minimumRegisters minimumStacks

abbrev readProgram : Program 16 48 38 :=
  ProgramLinking.liftProgram (ArrayUpdatePrograms.readProgram (9 : Fin 16) 8) id readPorts

abbrev replaceProgram : Program 16 48 44 :=
  ProgramLinking.liftProgram (ArrayUpdatePrograms.replaceProgram (9 : Fin 16) 8) id replacePorts

abbrev wordUpdate : Cmd 16 48 :=
  .seq (.call readProgram)
    (.seq (.call (copyProgram (19 : Fin 48) 17 18 (9 : Fin 16) 8)) (.call replaceProgram))

abbrev cleanAuxiliary : Cmd 16 48 :=
  ([0, 1, 2, 3, 4, 5, 6, 7, 12] : List (Fin 48)).foldr
    (fun j rest => .seq (.call (clearProgram j (9 : Fin 16) 8)) rest) (.base .skip)

/-- The selected unary index is consumed by the alphabet lookup. The
processed index is copied before the assignment update consumes its copy. -/
abbrev selectAndUpdate : Cmd 16 48 :=
  .seq resetRegisters
    (.seq (.call minimumProgram)
      (.seq wordUpdate (.seq cleanAuxiliary incrementProcessed)))

abbrev step (scoreBuilder : Cmd 16 48) : Cmd 16 48 :=
  .seq scoreBuilder selectAndUpdate

abbrev body (scoreBuilder : Cmd 16 48) : Cmd 16 48 :=
  .seq dropRemaining (.seq (step scoreBuilder) peekRemaining)

abbrev loop (scoreBuilder : Cmd 16 48) : Cmd 16 48 :=
  .while 10 (body scoreBuilder)

abbrev command (scoreBuilder : Cmd 16 48) : Cmd 16 48 :=
  .seq peekRemaining (loop scoreBuilder)

abbrev program (scoreBuilder : Cmd 16 48) :
    Program 16 48 (size (command scoreBuilder) + 1) :=
  compiled (command scoreBuilder) 8 8

abbrev clearList (rs : List (Fin 48)) : Cmd 16 48 :=
  rs.foldr (fun j rest => .seq (.call (clearProgram j (9 : Fin 16) 8)) rest) (.base .skip)

end SubexponentialSAT.Subexp.SequentialProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_CandidateScoreRefinement
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Candidate-array and generated-score refinement

The concrete temporary array has the same values as the search decoder after
one candidate is prepended. Generated collision streams may be permuted;
their successful-leaf counts still equal the exact natural evaluator.
-/

namespace SubexponentialSAT.Subexp.CandidateScoreRefinement

open SubexponentialSAT.MulticolorTypes SubexponentialSAT.SlotAssignment

theorem currentArray_eq_padding {r Q : ℕ} (default : Word r Q) (M : ℕ)
    (fixed : List (Word r Q)) (h : fixed.length ≤ M) :
    ReadPlan.currentArray default M fixed =
      fixed.reverse ++ List.replicate (M - fixed.length) default := by
  unfold ReadPlan.currentArray
  change (List.range M).map (fun i => SubexponentialSAT.LocalExpectation.decode default fixed i) = _
  simp_rw [AssignmentEnumeration.decode_eq_reverse_getD]
  simpa using map_range_getD default M fixed.reverse (by simpa using h)

theorem currentArray_after_candidate {r Q : ℕ} (default candidate : Word r Q) (M : ℕ)
    (fixed : List (Word r Q)) (h : fixed.length < M) :
    ReadPlan.currentArray default M (candidate :: fixed) =
      fixed.reverse ++ candidate :: List.replicate (M - (fixed.length + 1)) default := by
  rw [currentArray_eq_padding default M (candidate :: fixed) (by simpa using h)]
  simp [List.reverse_cons, List.append_assoc]

end SubexponentialSAT.Subexp.CandidateScoreRefinement

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

abbrev Data := State 3 6
abbrev record : Cmd 3 6 := .call
  (ProgramLinking.liftProgram SubexpNormalizeProgram.emitRecordProgram id recordPorts)
end SubexponentialSAT.SqrtLog.PackingIncidenceInput.Emit

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

abbrev clear (src : Fin 12) : Cmd 10 12 := .call (clearProgram src 0 1)

abbrev compareCall : Cmd 10 12 :=
  .call (ProgramLinking.liftProgram UnaryCompare.program low4 compareStack)

abbrev compare : Cmd 10 12 :=
  .seq (copy 7 9 4) (.seq (copy 2 10 4) (.seq compareCall (.seq (clear 9) (clear 10))))

def ports : RecordPrograms.Ports 10 12 where
  tag := 7
  present := 8
  found := 9
  source := 5
  payload := 2
  tag_ne_present := by decide
  found_ne_tag := by decide
  found_ne_present := by decide
  source_ne_payload := by decide

abbrev initAccumulator : Cmd 10 12 :=
  .seq (RecordPrograms.atom (.set 0 false)) (RecordPrograms.atom (.push 8 0))

abbrev initializeOutput : Cmd 10 12 :=
  .seq (RecordPrograms.atom (.set 0 false)) (RecordPrograms.atom (.push 11 0))

end SubexponentialSAT.Subexp.ActivePlanProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PairPlanPreparation
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual parsing and record-order preparation of the two plans in a pair
payload. Registers 0, 1, and 2 are scratch; all other registers are framed. -/

namespace SubexponentialSAT.Subexp.PairPlanPreparation

open BitProgram StackRoutines StructuredCalls

abbrev clear (src : Fin 34) : Cmd 16 34 := .call (clearProgram src 0 1)

def fieldPorts : RecordPrograms.Ports 16 34 :=
  ⟨0, 1, 2, 22, 23, by decide, by decide, by decide, by decide⟩

abbrev parsePair : Cmd 16 34 :=
  .seq (transfer 21 22) (.seq (RecordPrograms.reader fieldPorts)
    (.seq (transfer 23 24) (.seq (RecordPrograms.reader fieldPorts) (transfer 23 25))))

end SubexponentialSAT.Subexp.PairPlanPreparation

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_SelectionTableProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Building the selector table at runtime

A fixed program scans framed unary seed indices, pairs each with the current
unary candidate-array position, and increments that position. The output is
the raw sequence `frame key ++ frame value`, with no outer list tags.
-/

namespace SubexponentialSAT.Subexp.SelectionTableProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

def ports : RecordPrograms.Ports 3 6 where
  tag := 0
  present := 1
  found := 2
  source := 0
  payload := 1
  tag_ne_present := by decide
  found_ne_tag := by decide
  found_ne_present := by decide
  source_ne_payload := by decide

abbrev emitter : Program 3 6 17 :=
  ProgramLinking.liftProgram SubexpNormalizeProgram.emitRecordProgram id emitStack

/-- Remove the emitter's record tag, then reverse the raw frame into the
stream accumulator. -/
abbrev emitToAcc : Cmd 3 6 :=
  .seq (.call emitter)
    (.seq (RecordPrograms.atom (.pop 3 0 1))
      (.call (transferProgram (3 : Fin 6) 4 (0 : Fin 3) 1)))

abbrev advance : Cmd 3 6 :=
  .seq (RecordPrograms.atom (.set 0 true))
    (.seq (RecordPrograms.atom (.push 2 0))
      (.seq (RecordPrograms.atom (.set 0 false)) (RecordPrograms.atom (.set 1 true))))

abbrev callback : Cmd 3 6 :=
  .seq emitToAcc
    (.seq (.call (copyProgram (2 : Fin 6) 1 5 (0 : Fin 3) 1))
      (.seq emitToAcc advance))

abbrev command : Cmd 3 6 :=
  .seq (RecordPrograms.iterate ports callback)
    (.call (transferProgram (4 : Fin 6) 3 (0 : Fin 3) 1))

abbrev program : Program 3 6 (size command + 1) := compiled command 0 3

end SubexponentialSAT.Subexp.SelectionTableProgram

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

def rightPorts : RecordPrograms.Ports 8 12 :=
  ⟨0, 1, 2, 9, 8, by decide, by decide, by decide, by decide⟩

def leftPorts : RecordPrograms.Ports 8 12 :=
  ⟨0, 1, 2, 10, 8, by decide, by decide, by decide, by decide⟩

def outputPorts : RecordPrograms.Ports 8 12 :=
  ⟨0, 1, 2, 10, 11, by decide, by decide, by decide, by decide⟩

abbrev prepareRight : Cmd 8 12 :=
  .seq (.call (StackRoutines.transferProgram 8 10 (0 : Fin 8) 1))
    (.seq (.call (StackRoutines.copyProgram 9 6 4 (0 : Fin 8) 1))
      (.call (StackRoutines.clearProgram 9 (0 : Fin 8) 1)))

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

def ports : RecordPrograms.Ports 16 34 where
  tag := 13
  present := 14
  found := 15
  source := 20
  payload := 21
  tag_ne_present := by decide
  found_ne_tag := by decide
  found_ne_present := by decide
  source_ne_payload := by decide

abbrev tableCall : Cmd 16 34 :=
  .call (ProgramLinking.liftProgram SelectionTableProgram.program tableRegs tableStacks)

abbrev clear (src : Fin 34) : Cmd 16 34 := .call (clearProgram src (0 : Fin 16) 1)
abbrev move (src dst : Fin 34) : Cmd 16 34 := .seq (copy src dst) (clear src)

end SubexponentialSAT.Subexp.PairPreparationProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_ScoreBuilderPorts
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# The fixed global scorer stack layout

The preparation and candidate routines use the controller's 48 stacks through
explicit injective maps. The finalizer moves ordered score records to port 0
and clears the temporary selected-pair table, restoring the higher-stack
environment expected by the sequential controller.
-/

namespace SubexponentialSAT.Subexp.ScoreBuilderProgram

open BitProgram StructuredCalls StackRoutines

abbrev finish : Cmd 16 48 :=
  .seq (.call (transferProgram 41 42 0 1))
    (.seq (.call (transferProgram 42 0 0 1)) (.call (clearProgram 40 0 1)))

end SubexponentialSAT.Subexp.ScoreBuilderProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_ScoreBuilderInputBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Literal input-size bounds for every reachable candidate-scoring step. -/

namespace SubexponentialSAT.Subexp.ScoreBuilderInputBounds

open SubexponentialSAT.MulticolorTypes SubexponentialSAT.SlotAssignment

theorem encodedWords_length {r Q : ℕ} (words : List (Word r Q)) :
    (words.map ReadPlan.encodeWord).flatten.length = words.length * ReadPlan.wordWidth r Q := by
  induction words with
  | nil => simp
  | cons word words ih =>
    simp only [List.map_cons, List.flatten_cons, List.length_append,
      ReadPlan.encodeWord_length, List.length_cons, ih]
    ring

end SubexponentialSAT.Subexp.ScoreBuilderInputBounds

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

theorem begin_record (value present : Bool) (input output : List Bool) :
    Trace program 4 (cfg (some 2) value present (true :: input) output)
      (cfg (some 6) true true input (true :: output)) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, program, cfg, execInstr, readRegs,
    ParserProgram.pair]

theorem skip_bit (bit value present : Bool) (input output : List Bool) :
    Trace program 4 (cfg (some 6) value present (true :: bit :: input) output)
      (cfg (some 6) bit true input output) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, program, cfg, execInstr, readRegs,
    ParserProgram.pair]

theorem skip_end (value present : Bool) (input output : List Bool) :
    Trace program 2 (cfg (some 6) value present (false :: input) output)
      (cfg (some 2) false true input output) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, program, cfg, execInstr, readRegs,
    ParserProgram.pair]

theorem frame_trace (bits rest output : List Bool) (value present : Bool) :
    Trace program (4 * bits.length + 2)
      (cfg (some 6) value present (Encoding.frame bits ++ rest) output)
      (cfg (some 2) false true rest output) := by
  induction bits generalizing value present with
  | nil => simpa [Encoding.frame] using skip_end value present rest output
  | cons bit bits ih =>
      have h := (skip_bit bit value present (Encoding.frame bits ++ rest) output).trans
        (ih bit true)
      simpa [Encoding.frame, Nat.mul_add, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using h

theorem record_trace (bits rest output : List Bool) (value present : Bool) :
    Trace program (4 * bits.length + 6)
      (cfg (some 2) value present (true :: (Encoding.frame bits ++ rest)) output)
      (cfg (some 2) false true rest (true :: output)) := by
  have h := (begin_record value present (Encoding.frame bits ++ rest) output).trans
    (frame_trace bits rest (true :: output) true true)
  convert h using 1 ; omega

theorem finish (value present : Bool) (rest output : List Bool) :
    Trace program 5 (cfg (some 2) value present (false :: rest) output)
      (cfg none false false rest output) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, program, cfg, execInstr, readRegs,
    ParserProgram.pair]

theorem loop_trace (records : List (List Bool)) (suffix output : List Bool)
    (value present : Bool) :
    Trace program (loopSteps records)
      (cfg (some 2) value present (Encoding.encodeList id records ++ suffix) output)
      (cfg none false false suffix (List.replicate records.length true ++ output)) := by
  induction records generalizing value present output with
  | nil => simpa [loopSteps, Encoding.encodeList] using finish value present suffix output
  | cons bits records ih =>
      have h := (record_trace bits (Encoding.encodeList id records ++ suffix) output
        value present).trans (ih (true :: output) false true)
      have hout : List.replicate records.length true ++ true :: output =
          List.replicate (records.length + 1) true ++ output := by
        rw [List.replicate_succ', List.append_assoc]
        rfl
      rw [hout] at h
      convert h using 1 <;>
        simp [loopSteps, Encoding.encodeList, Nat.mul_add, Nat.add_assoc,
          Nat.add_comm, Nat.add_left_comm, List.append_assoc]

theorem steps_le_encoded (records : List (List Bool)) :
    steps records ≤ 3 * (Encoding.encodeList id records).length + 4 := by
  have hlen := ProgramEncoding.encodeRecords_length records
  change (Encoding.encodeList id records).length = _ at hlen
  unfold steps loopSteps
  omega

end CountRecords

end SubexponentialSAT.SubexpSunflowerProgram

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

def bound (scopes : List (List ℕ)) (v : ℕ) :=
  7*((scopeBits scopes).length+v)+18+SubexpIncidencePlanScan.scanBudget v 0 scopes

end SubexponentialSAT.SqrtLog.PackingIncidenceInput.Scan


/-! Fixed cleanup for the native scope-address scanner. -/


/-! Calls to the fixed record mapper inside the native scope scan. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput.Lift
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp
def cleanBound (scopes : List (List ℕ)) (v : ℕ) (source : List Bool) :=
  8*(v+scopes.length+(Scan.indices scopes v).length+source.length+1)+13

end SubexponentialSAT.SqrtLog.PackingIncidenceInput.Lift


/-! One native low-variable step, including its uncovered neutral factor. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput.Step
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp
def bound (scopes : List (List ℕ)) (n v z : ℕ) :=
  Scan.bound scopes v + Rows.budget v n (Scan.indices scopes v).reverse +
    Rows.callbackBound v n z + 7*z +
    Lift.cleanBound scopes v [false] + 30

end SubexponentialSAT.SqrtLog.PackingIncidenceInput.Step


/-! Runtime high-mask loop for the original-address incidence stream. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput.Loop
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp
def budget (scopes : List (List ℕ)) (n : ℕ) : ℕ → ℕ → List Bool → ℕ
  | _,_,[] => 2
  | v,z,high::rest => (if high then 2 else Step.bound scopes n v z+1)+4+
      budget scopes n (v+1) (if high then z else Step.next scopes v z) rest

end SubexponentialSAT.SqrtLog.PackingIncidenceInput.Loop


/-! Count the physical scope stream before constructing native incidence plans. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput.Boot
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp
def budget (scopes : List (List ℕ)) :=
  7*(Scan.scopeBits scopes).length+7+SubexpSunflowerProgram.CountRecords.loopSteps (records scopes)

theorem scope_eq (scopes : List (List ℕ)) :
    Scan.scopeBits scopes = Encoding.encodeList id (records scopes) := by
  induction scopes with
  | nil => rfl
  | cons s ss ih => simpa [Scan.scopeBits,records,Encoding.encodeList] using ih

def fullBudget (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool) :=
  budget scopes + Loop.budget scopes n 0 scopes.length mask + 1

end SubexponentialSAT.SqrtLog.PackingIncidenceInput.Boot

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingIncidenceInputCost
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The native linear-plan builder has cubic cost in its actual input size. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput.Cost
open SubexponentialSAT.Subexp

theorem step_budget_le (scopes : List (List ℕ)) (n v z W : ℕ)
    (hW : 1 ≤ W) (hL : (Scan.scopeBits scopes).length ≤ W)
    (hq : scopes.length ≤ W) (hn : n ≤ W) (hv : v ≤ W) (hz : z ≤ W) :
    Step.bound scopes n v z ≤ 3000*W^2 := by
  have hW2 : W ≤ W^2 := by nlinarith
  have hd : (Scan.indices scopes v).length ≤ W :=
    (SubexpIncidencePlanScan.incidenceFrom_length_le v 0 scopes).trans hq
  have hs := SubexpIncidencePlanScan.scanBudget_le v 0 scopes
  have hc : 128*(v+2)+16*(0+scopes.length+2)+20 ≤ 452*W := by omega
  have hs' : SubexpIncidencePlanScan.scanBudget v 0 scopes ≤ 452*W^2 := by
    calc
      _ ≤ (128*(v+2)+16*(0+scopes.length+2)+20)*(Scan.scopeBits scopes).length := hs
      _ ≤ (452*W)*W := Nat.mul_le_mul hc hL
      _ = _ := by ring
  have hj : ∀ j ∈ (Scan.indices scopes v).reverse, j ≤ scopes.length := by
    intro j hj
    exact (IncidencePlanSpec.incidentIndex_lt scopes v j (List.mem_reverse.mp hj)).le
  have hr := rows_budget_le v n scopes.length (Scan.indices scopes v).reverse hj
  have hr' : Rows.budget v n (Scan.indices scopes v).reverse ≤ 828*W^2 := by
    have hcoef : 207*(v+n+scopes.length+1) ≤ 828*W := by omega
    have hlen : (Scan.indices scopes v).reverse.length ≤ W := by simpa using hd
    calc
      _ ≤ (Scan.indices scopes v).reverse.length*(207*(v+n+scopes.length+1)) := hr
      _ ≤ W*(828*W) := Nat.mul_le_mul hlen hcoef
      _ = _ := by ring
  have hcall : Rows.callbackBound v n z ≤ 800*W := by dsimp [Rows.callbackBound]; omega
  have hclean : Lift.cleanBound scopes v [false] ≤ 53*W := by
    simp only [Lift.cleanBound,List.length_cons,List.length_nil]
    omega
  dsimp [Step.bound,Scan.bound]
  nlinarith

theorem loop_budget_le (scopes : List (List ℕ)) (n W : ℕ) (mask : List Bool)
    (hW : 1 ≤ W) (hL : (Scan.scopeBits scopes).length ≤ W)
    (hq : scopes.length ≤ W) (hn : n ≤ W) :
    ∀ v z, v+mask.length ≤ W → z+mask.length ≤ W →
      Loop.budget scopes n v z mask ≤ 3005*mask.length*W^2+2 := by
  induction mask with
  | nil => simp [Loop.budget]
  | cons high mask ih =>
      intro v z hv hz
      have hv' : v+1+mask.length ≤ W := by simp only [List.length_cons] at hv; omega
      have hz' : (if high then z else Step.next scopes v z)+mask.length ≤ W := by
        cases high <;> simp only [Bool.false_eq_true,ite_false,ite_true, if_true]
        · unfold Step.next; split <;> simp only [List.length_cons] at hz <;> omega
        · simp only [List.length_cons] at hz; omega
      have ht := ih (v+1) (if high then z else Step.next scopes v z) hv' hz'
      have hs := step_budget_le scopes n v z W hW hL hq hn (by omega) (by omega)
      cases high <;> simp only [Loop.budget,ite_true, if_true,Bool.false_eq_true,ite_false,List.length_cons] at * <;>
        nlinarith

def inputSize (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool) :=
  (Scan.scopeBits scopes).length+n+mask.length+1

theorem native_cubic (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool) :
    Boot.fullBudget scopes n mask ≤ 4000*(inputSize scopes n mask)^3 := by
  let W := inputSize scopes n mask
  have hW : 1 ≤ W := by dsimp [W,inputSize]; omega
  have hL : (Scan.scopeBits scopes).length ≤ W := by dsimp [W,inputSize]; omega
  have hq : scopes.length+1 ≤ (Scan.scopeBits scopes).length :=
    Encoding.length_encodeList_lower _ scopes
  have hloop := loop_budget_le scopes n W mask hW hL (by omega)
    (by dsimp [W,inputSize]; omega) 0 scopes.length
    (by dsimp [W,inputSize]; omega) (by dsimp [W,inputSize] at *; omega)
  have hcounter := SubexpSunflowerProgram.CountRecords.steps_le_encoded (Boot.records scopes)
  rw [← Boot.scope_eq] at hcounter
  have hboot : Boot.budget scopes ≤ 10*W+9 := by
    dsimp [Boot.budget,SubexpSunflowerProgram.CountRecords.steps] at *
    omega
  have hm : mask.length ≤ W := by dsimp [W,inputSize]; omega
  have hprod := Nat.mul_le_mul_right (3005*W^2) hm
  have hW2 : W ≤ W^2 := by nlinarith
  have hW3 : W ≤ W^3 := by nlinarith [Nat.mul_le_mul_left (W^2) hW]
  dsimp [Boot.fullBudget]
  nlinarith
end SubexponentialSAT.SqrtLog.PackingIncidenceInput.Cost

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_AssignmentPairFrontend
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
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

abbrev Data := State 16 48

end SubexponentialSAT.Subexp.AssignmentPairFrontend

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingCompletion
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
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
theorem numberedActive_length_le (indices : List (V ⊕ E)) (z : ScoreTerm I V Q)
    (remaining : List ℕ) (hn : remaining.Nodup) :
    (active (numberedScoreSupport ivar factor indices z) remaining).length ≤ 4 :=
  (active_length_le _ _ hn).trans (numberedScoreSupport_card_le ivar factor indices z)

end Completion
end SubexponentialSAT.SqrtLog.Packing

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingIncidenceProgramGenerated
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The actual generated incidence-pair order is accepted by the fixed scorer. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp

section Plans
variable {I V E : Type*} [DecidableEq V] [DecidableEq E]
  (ivar : I → V) (factor : I → E)

def incidencePlans (indices : List (V ⊕ E)) (incidences : List I) : List (List ℕ) :=
  incidences.map (incidencePlan ivar factor indices)

end Plans

end SubexponentialSAT.SqrtLog.PackingIncidenceProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingIncidenceInputEntry
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Entry from the actual descending high mask produced by the high-variable pass. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput.Entry
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp
def sourceStacks (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool) : Fin 48 → List Bool :=
  fun j => if j=32 then Scan.scopeBits scopes else if j=33 then Scan.unary n
    else if j=36 then mask else []
end SubexponentialSAT.SqrtLog.PackingIncidenceInput.Entry


/-! Raw scopes and the computed mask feed the actual incidence-pair producer. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_AssignmentInitProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
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

abbrev repeatDefault : Cmd 16 48 :=
  .call (ProgramLinking.liftProgram BlockCopyProgram.program copyRegisters copyPorts)
abbrev clearDefault : Cmd 16 48 := .call (clearProgram 0 (0 : Fin 16) 1)

abbrev command : Cmd 16 48 :=
  .seq reset (.seq copyRemaining (.seq copyCounter
    (.seq repeatDefault (.seq copyAlphabet clearDefault))))

abbrev program : Program 16 48 (size command + 1) := compiled command 0 8

end SubexponentialSAT.Subexp.AssignmentInitProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingLoaderProgramBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The loader's complete native cost, including emitted alphabet size. -/
namespace SubexponentialSAT.SqrtLog.PackingLoaderProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem unary_bound (bits : List Bool) (B : ℕ)
    (hv : SubexponentialSAT.BinaryArithmetic.toNat bits+1 ≤ B) (hl : bits.length+1 ≤ B) (_hB : 1 ≤ B) :
    LeafParametersProgram.Serialization.unaryCopyBound bits+1 ≤ 45*B^2 := by
  rw [LeafParametersProgram.Serialization.unaryCopyBound_eq]
  have hm : (SubexponentialSAT.BinaryArithmetic.toNat bits+1)*(bits.length+1) ≤ B^2 := by
    simpa only [pow_two] using Nat.mul_le_mul hv hl
  have hsq : B ≤ B^2 := by nlinarith
  nlinarith

end SubexponentialSAT.SqrtLog.PackingLoaderProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingHeadProgramCandidates
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed producer of all incremental head scores from the candidate alphabet
and actual flattened prior-head table. No selected pair records are inputs. -/
namespace SubexponentialSAT.SqrtLog.PackingHeadProgramCandidates
open SubexponentialSAT BitProgram StructuredCalls StackRoutines SubexpScanPrimitives
open Subexp

def ports : RecordPrograms.Ports 8 12 where
  tag := 5
  present := 6
  found := 7
  source := 8
  payload := 0
  tag_ne_present := by decide
  found_ne_tag := by decide
  found_ne_present := by decide
  source_ne_payload := by decide

end SubexponentialSAT.SqrtLog.PackingHeadProgramCandidates

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpInputFrames
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual frame and tag readers for the row/input-pair stream. -/

namespace SubexponentialSAT.SubexpInputFrames

open BitProgram StructuredCalls

def ports {S : ℕ} (source target : Fin S) (h : source ≠ target) :
    RecordPrograms.Ports 8 S where
  tag := 0
  present := 1
  found := 2
  source := source
  payload := target
  tag_ne_present := by decide
  found_ne_tag := by decide
  found_ne_present := by decide
  source_ne_payload := h

abbrev readField {S : ℕ} (source target : Fin S) (h : source ≠ target) : Cmd 8 S :=
  RecordPrograms.reader (ports source target h)

end SubexponentialSAT.SubexpInputFrames

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpInputZip
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
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

open BitProgram StructuredCalls SubexpScanPrimitives

abbrev writer : Cmd 8 8 := .call
  (ProgramLinking.liftProgram SubexpNormalizeProgram.emitRecordProgram regPorts writerPorts)

abbrev pairCommand : Cmd 8 8 :=
  .seq (SubexpInputFrames.readField 0 2 (by decide))
    (.seq (SubexpInputFrames.readField 1 3 (by decide))
      (.seq (move 3 7) (.seq writer (.seq popPair
        (.seq (move 2 7) (.seq writer (move 4 5)))))))

abbrev loop : Cmd 8 8 := .while 7 (.seq pairCommand tags)

abbrev command : Cmd 8 8 := .seq tags (.seq loop finish)
abbrev program : Program 8 8 (size command + 1) := compiled command 0 6

end SubexponentialSAT.SubexpInputZip

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

abbrev clear (j : Fin 13) : Cmd 8 13 := .call (SubexponentialSAT.StackRoutines.clearProgram j 0 1)

end SubexponentialSAT.SqrtLog.PackingWeightProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingCallerProgramPrepare
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Stage the actual selected words and owner plans for the native layout
suffix. The incidence dimension is converted from its actual binary master. -/
namespace SubexponentialSAT.SqrtLog.PackingCallerProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.SubexpSetupStorage
open PackingLoaderProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

def prepareBudget (outside : Store) :=
  LeafParametersProgram.Serialization.unaryCopyBound (outside 58)+1+4+
    7*((outside 61).length+(outside 62).length+(outside 53).length+(outside 54).length)+20

end SubexponentialSAT.SqrtLog.PackingCallerProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingCallerProgramBoundsPolynomial
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PackingCallerProgram.Bounds
open CostAssembly.Polynomial
open SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes

theorem pairEnvelope_ordinary : Ordinary pairEnvelope := by
  unfold pairEnvelope
  exact (ordinary_add (ordinary_const 1) (ordinary_mul (ordinary_add (ordinary_mul (ordinary_const 32) (ordinary_add (ordinary_mul (ordinary_const 2) ordinary_id) (ordinary_const 1))) (ordinary_const 14)) (ordinary_pow ordinary_id 2)))

theorem alphabetEnvelope_ordinary : Ordinary alphabetEnvelope := by
  unfold alphabetEnvelope
  exact (ordinary_add (ordinary_const 1) (ordinary_mul (ordinary_add (ordinary_mul (ordinary_const 2) (ordinary_pow ordinary_id 2)) (ordinary_const 2)) ordinary_id))

theorem extentEnvelope_ordinary : Ordinary extentEnvelope := by
  unfold extentEnvelope
  exact (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_const 1) ordinary_id) ordinary_id) (ordinary_const 0)) ordinary_id) ordinary_id) (ordinary_const 1)) (ordinary_const 2)) (ordinary_pow ordinary_id 2)) (ordinary_mul (ordinary_const 2) ordinary_id)) ordinary_id) (ordinary_add (ordinary_const 1) (ordinary_mul (ordinary_add (ordinary_mul (ordinary_const 2) ordinary_id) (ordinary_const 2)) ordinary_id))) alphabetEnvelope_ordinary) (ordinary_pow ordinary_id 2)) (ordinary_mul ordinary_id (ordinary_pow ordinary_id 2))) seedEnvelope_ordinary) pairEnvelope_ordinary)

theorem sourceEnvelope_ordinary : Ordinary sourceEnvelope := by
  unfold sourceEnvelope
  exact (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add ordinary_id (ordinary_const 1)) ordinary_id) (ordinary_pow ordinary_id 2)) (ordinary_mul (ordinary_mul (ordinary_const 2) ordinary_id) (ordinary_pow ordinary_id 2))) alphabetEnvelope_ordinary) planEnvelope_ordinary) (ordinary_const 1))

theorem loaderEnvelope_ordinary : Ordinary loaderEnvelope := by
  unfold loaderEnvelope
  exact (ordinary_mul (ordinary_const 22000) (ordinary_pow (ordinary_add (ordinary_add extentEnvelope_ordinary (ordinary_mul (ordinary_const 11) ordinary_id)) (ordinary_const 1)) 4))

theorem readyEnvelope_ordinary : Ordinary readyEnvelope := by
  unfold readyEnvelope
  exact (ordinary_add (ordinary_add (ordinary_add (ordinary_mul (ordinary_mul (ordinary_const 2) ordinary_id) extentEnvelope_ordinary) extentEnvelope_ordinary) (ordinary_mul (ordinary_const 4) ordinary_id)) (ordinary_const 4))

theorem scoreEnvelope_ordinary : Ordinary scoreEnvelope := by
  unfold scoreEnvelope
  exact (ordinary_add (ordinary_mul (ordinary_pow (ordinary_mul ordinary_id ordinary_id) 2) (ordinary_mul (ordinary_pow ordinary_id 2) (ordinary_pow ordinary_id 4))) (ordinary_mul (ordinary_mul (ordinary_const 8) (ordinary_pow (ordinary_mul ordinary_id ordinary_id) 2)) (ordinary_mul (ordinary_mul (ordinary_const 2) ordinary_id) (ordinary_pow ordinary_id 2))))

theorem controllerEnvelope_ordinary : Ordinary controllerEnvelope := by
  unfold controllerEnvelope PackingProgram.Assembly.uniformBudget
    PackingProgram.Assembly.headBudgetBound SequentialProgram.selectionBudget
    SequentialProgram.minimumBudget SequentialProgram.recordBudget SequentialProgram.updateBudget
  exact (ordinary_add (ordinary_mul (ordinary_mul (ordinary_const 2) ordinary_id) (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_mul (ordinary_mul (ordinary_mul (ordinary_const 10000) (ordinary_pow (ordinary_const 31) 6)) (ordinary_pow (ordinary_add (ordinary_mul (ordinary_const 32) (ordinary_pow (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 2) ordinary_id) (ordinary_pow ordinary_id 2)) ordinary_id) (ordinary_pow ordinary_id 2)) (ordinary_const 1)) 2)) (ordinary_const 1)) 12)) (ordinary_pow ordinary_id 4)) (ordinary_mul (ordinary_const 12) (ordinary_mul (ordinary_const 4) ordinary_id))) (ordinary_const 48)) (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 80) (ordinary_pow (ordinary_add (ordinary_add (ordinary_add ordinary_id (ordinary_mul (ordinary_const 2) ordinary_id)) (ordinary_mul (ordinary_const 4) ordinary_id)) (ordinary_const 1)) 2)) (ordinary_const 1)) (ordinary_add (ordinary_add (ordinary_add (ordinary_mul (ordinary_mul (ordinary_const 24) (ordinary_mul (ordinary_const 2) ordinary_id)) (ordinary_pow ordinary_id 2)) (ordinary_mul (ordinary_const 25) (ordinary_mul (ordinary_const 2) ordinary_id))) (ordinary_mul (ordinary_const 13) (ordinary_pow ordinary_id 2))) (ordinary_const 48))) (ordinary_const 1)) (ordinary_add (ordinary_mul (ordinary_const 7) (ordinary_add (ordinary_const 1) (ordinary_mul (ordinary_add (ordinary_mul (ordinary_const 2) (ordinary_pow ordinary_id 2)) (ordinary_const 2)) ordinary_id))) (ordinary_const 5))) (ordinary_const 16)) (ordinary_add (ordinary_mul ordinary_id (ordinary_add (ordinary_add (ordinary_add (ordinary_mul (ordinary_mul (ordinary_const 43) (ordinary_mul (ordinary_const 2) ordinary_id)) (ordinary_pow ordinary_id 2)) (ordinary_mul (ordinary_const 20) (ordinary_mul (ordinary_const 2) ordinary_id))) (ordinary_mul (ordinary_const 17) (ordinary_pow ordinary_id 2))) (ordinary_const 66))) (ordinary_const 22))) (ordinary_mul (ordinary_const 3) (ordinary_add (ordinary_mul (ordinary_const 2) (ordinary_add (ordinary_mul (ordinary_mul (ordinary_const 2) ordinary_id) (ordinary_pow ordinary_id 2)) (ordinary_mul (ordinary_const 2) ordinary_id))) (ordinary_const 3))))) (ordinary_mul (ordinary_const 500) (ordinary_pow (ordinary_add (ordinary_mul (ordinary_const 2) (ordinary_mul (ordinary_const 4) ordinary_id)) (ordinary_const 4)) 2))) (ordinary_const 1)) (ordinary_mul (ordinary_mul (ordinary_mul (ordinary_const 500) (ordinary_add ordinary_id (ordinary_const 1))) (ordinary_add (ordinary_add (ordinary_mul (ordinary_pow ordinary_id 2) (ordinary_pow ordinary_id 2)) (ordinary_mul (ordinary_mul (ordinary_const 8) (ordinary_pow ordinary_id 2)) (ordinary_pow ordinary_id 2))) (ordinary_const 1))) (ordinary_add (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 2) (ordinary_mul (ordinary_const 4) ordinary_id)) (ordinary_const 6)) (ordinary_add (ordinary_mul (ordinary_pow ordinary_id 2) (ordinary_pow ordinary_id 4)) (ordinary_mul (ordinary_mul (ordinary_const 2) ordinary_id) (ordinary_pow ordinary_id 2)))) (ordinary_const 1)))) (ordinary_mul (ordinary_const 6) (ordinary_add (ordinary_mul ordinary_id (ordinary_add (ordinary_mul (ordinary_mul (ordinary_const 4) (ordinary_add (ordinary_mul (ordinary_pow ordinary_id 2) (ordinary_pow ordinary_id 2)) (ordinary_mul (ordinary_mul (ordinary_const 8) (ordinary_pow ordinary_id 2)) (ordinary_pow ordinary_id 2)))) (ordinary_add (ordinary_mul (ordinary_pow ordinary_id 2) (ordinary_pow ordinary_id 4)) (ordinary_mul (ordinary_mul (ordinary_const 2) ordinary_id) (ordinary_pow ordinary_id 2)))) (ordinary_const 2))) (ordinary_const 1)))) (ordinary_mul (ordinary_const 4) (ordinary_add (ordinary_mul (ordinary_const 2) (ordinary_mul (ordinary_const 4) ordinary_id)) (ordinary_const 6)))) (ordinary_const 14)) (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_const 9) (ordinary_mul (ordinary_const 500) (ordinary_pow (ordinary_mul ordinary_id (ordinary_add scoreEnvelope_ordinary (ordinary_const 1))) 2))) (ordinary_add (ordinary_add (ordinary_add (ordinary_mul ordinary_id (ordinary_add (ordinary_mul (ordinary_const 14) (ordinary_pow ordinary_id 2)) (ordinary_const 10))) (ordinary_mul (ordinary_const 15) (ordinary_pow ordinary_id 2))) (ordinary_const 16)) (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 7) (ordinary_mul (ordinary_const 2) ordinary_id)) (ordinary_const 5)) (ordinary_add (ordinary_add (ordinary_mul (ordinary_mul (ordinary_const 2) ordinary_id) (ordinary_add (ordinary_mul (ordinary_const 14) (ordinary_pow ordinary_id 2)) (ordinary_const 10))) (ordinary_mul (ordinary_const 20) (ordinary_pow ordinary_id 2))) (ordinary_const 21))))) (ordinary_mul (ordinary_const 9) (ordinary_add (ordinary_mul (ordinary_const 2) (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 2) (ordinary_mul ordinary_id scoreEnvelope_ordinary)) (ordinary_mul (ordinary_const 2) ordinary_id)) (ordinary_const 1)) (ordinary_mul (ordinary_const 500) (ordinary_pow (ordinary_mul ordinary_id (ordinary_add scoreEnvelope_ordinary (ordinary_const 1))) 2))) (ordinary_pow ordinary_id 2))) (ordinary_const 3)))) (ordinary_const 2))) (ordinary_const 3))) (ordinary_const 3))

theorem selectionEnvelope_ordinary : Ordinary selectionEnvelope := by
  unfold selectionEnvelope
  exact (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 7) readyEnvelope_ordinary) (ordinary_const 5)) (ordinary_add (ordinary_mul (ordinary_const 7) readyEnvelope_ordinary) (ordinary_const 5))) controllerEnvelope_ordinary) (ordinary_add (ordinary_mul (ordinary_const 7) (ordinary_mul (ordinary_mul (ordinary_const 2) ordinary_id) (ordinary_pow ordinary_id 2))) (ordinary_const 5))) (ordinary_mul (ordinary_const 48) (ordinary_add (ordinary_mul (ordinary_const 2) (ordinary_add (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 48) readyEnvelope_ordinary) (ordinary_mul (ordinary_mul (ordinary_const 2) ordinary_id) (ordinary_pow ordinary_id 2))) (ordinary_mul (ordinary_const 2) ordinary_id)) (ordinary_const 1))) (ordinary_const 3))))

theorem produceEnvelope_ordinary : Ordinary produceEnvelope := by
  unfold produceEnvelope
  exact (ordinary_add (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 4000) (ordinary_pow (ordinary_add (ordinary_mul (ordinary_const 3) ordinary_id) (ordinary_const 1)) 3)) (ordinary_const 1)) (ordinary_add (ordinary_mul (ordinary_const 7) planEnvelope_ordinary) (ordinary_const 5))) (ordinary_add (ordinary_const 4) (ordinary_mul (ordinary_const 100) (ordinary_add (ordinary_add (ordinary_mul (ordinary_mul (ordinary_const 2400) (ordinary_pow (ordinary_add ordinary_id (ordinary_const 1)) 2)) (ordinary_add (ordinary_mul (ordinary_const 24) (ordinary_mul (ordinary_const 2) ordinary_id)) (ordinary_const 34))) (ordinary_const 11)) (ordinary_mul (ordinary_add (ordinary_mul (ordinary_const 16) (ordinary_mul (ordinary_const 2) ordinary_id)) (ordinary_const 24)) ordinary_id)))))

theorem prepareEnvelope_ordinary : Ordinary prepareEnvelope := by
  unfold prepareEnvelope
  exact (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 7) ordinary_id) (ordinary_const 6)) (ordinary_mul (ordinary_mul (ordinary_const 32) (ordinary_add ordinary_id (ordinary_const 1))) (ordinary_add ordinary_id (ordinary_const 1)))) (ordinary_const 1)) (ordinary_const 4)) (ordinary_mul (ordinary_const 7) (ordinary_add (ordinary_add (ordinary_add planEnvelope_ordinary (ordinary_mul (ordinary_mul (ordinary_const 2) ordinary_id) (ordinary_pow ordinary_id 2))) (ordinary_pow ordinary_id 2)) alphabetEnvelope_ordinary))) (ordinary_const 20))

theorem suffixEnvelope_ordinary : Ordinary suffixEnvelope := by
  unfold suffixEnvelope
  exact (ordinary_add (ordinary_add (ordinary_add prepareEnvelope_ordinary (ordinary_mul (ordinary_const 81000000) (ordinary_pow sourceEnvelope_ordinary 12))) (ordinary_add (ordinary_mul (ordinary_const 7) (ordinary_mul (ordinary_const 34) (ordinary_pow sourceEnvelope_ordinary 4))) (ordinary_const 5))) (ordinary_mul (ordinary_const 48) (ordinary_add (ordinary_mul (ordinary_const 2) (ordinary_mul (ordinary_const 34) (ordinary_pow sourceEnvelope_ordinary 4))) (ordinary_const 3))))

theorem coreEnvelope_ordinary : Ordinary coreEnvelope := by
  unfold coreEnvelope
  exact (ordinary_add (ordinary_add (ordinary_add produceEnvelope_ordinary loaderEnvelope_ordinary) selectionEnvelope_ordinary) suffixEnvelope_ordinary)

theorem outputEnvelope_ordinary : Ordinary outputEnvelope := by
  unfold outputEnvelope
  exact (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add ordinary_id (ordinary_pow ordinary_id 2)) alphabetEnvelope_ordinary) planEnvelope_ordinary) (ordinary_mul (ordinary_mul (ordinary_const 2) ordinary_id) (ordinary_pow ordinary_id 2))) (ordinary_mul (ordinary_const 34) (ordinary_pow sourceEnvelope_ordinary 4)))

end SubexponentialSAT.SqrtLog.PackingCallerProgram.Bounds

end OAI.Algorithms
end


