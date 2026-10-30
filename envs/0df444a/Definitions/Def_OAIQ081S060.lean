-- Prove2me | Definitions.Def_OAIQ081S060
-- name    : OAIQ081S060
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T21:48:04.6218+00:00
-- url     : https://prove2.me/theorems/798e564c-2520-4ac9-bcb3-a82800afbacd
-- title:
--   Definitions bundle OAIQ081S060 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 103 declarations of OpenAI's Lean: 67 definitions, 1 inductive type or structure, 2 instances and 33 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Query.cleaned`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Query.cleanup`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Query.cleanupCost`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Query.cleanupPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Query.cleanupPortsWrapped`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Query.markInput`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Query.markedFlag`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Query.noMarkInput`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.QueryReadback.install`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.QueryReadback.project`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Readback.countCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Readback.countProgram`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Readback.remainderProgram`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.SourceReady.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.SourceStaging.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.squarefreeAlgebra`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Query.hashCountBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.arityRegisters`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.clearPrivate`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.finalMajorant`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.resetScopeRegs`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.scanMajorant`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.setRegs`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafScopeResourceBounds.initialPayloads`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Arity.cost`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Arity.decoded`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Arity.ports`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Arity.scopeBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Arity.update`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Lookup.clear`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Lookup.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Lookup.program`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Scope.ports`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Scope.update`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.stepBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.variableBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Moments.Stored`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Moments.Stored.denote`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Moments.Stored.scale`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary.inputTape` and 28 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLog_LeafProgramQueryCleanup`, `SubexponentialSAT_SqrtLog_LeafProgramQueryReadback`, `SubexponentialSAT_SqrtLog_LeafProgramQueryReference`, `SubexponentialSAT_SqrtLog_LeafProgramQueryWidthArithmetic`, `SubexponentialSAT_SqrtLog_LeafProgramReadbackReduce`, `SubexponentialSAT_SqrtLog_LeafProgramRecords`, `SubexponentialSAT_SqrtLog_LeafProgramSourceReadyCore`, `SubexponentialSAT_SqrtLog_LeafProgramSourceStaging`, `SubexponentialSAT_SqrtLog_LeafProgramSquarefree`, `SubexponentialSAT_SqrtLog_LeafQueryFrontendCommand`, `SubexponentialSAT_SqrtLog_LeafQueryFrontendMajorants`, `SubexponentialSAT_SqrtLog_LeafQueryFrontendOps`, `SubexponentialSAT_SqrtLog_LeafQueryFrontendScanBounds`, `SubexponentialSAT_SqrtLog_LeafQueryFrontendUniform`, `SubexponentialSAT_SqrtLog_LeafRingSetupProgramNative`, `SubexponentialSAT_SqrtLog_LeafScopeResourceBoundsDecode`, `SubexponentialSAT_SqrtLog_LeafStatisticsProgramArity`, `SubexponentialSAT_SqrtLog_LeafStatisticsProgramLookup`, `SubexponentialSAT_SqrtLog_LeafStatisticsProgramScope`, `SubexponentialSAT_SqrtLog_LeafStatisticsProgramVariables`, `SubexponentialSAT_SqrtLog_LocalCodeSearch`, `SubexponentialSAT_SqrtLog_MomentsProgramDictionaryInsert`, `SubexponentialSAT_SqrtLog_MomentsProgramProduct`, `SubexponentialSAT_SqrtLog_MomentsProjectionProgramBase`, `SubexponentialSAT_SqrtLog_MomentsProjectionProgramBridge`, `SubexponentialSAT_SqrtLog_MomentsProjectionProgramMask`, `SubexponentialSAT_SqrtLog_MomentsReadoutProgramAccumulate`, `SubexponentialSAT_SqrtLog_MomentsReadoutProgramFetch`, `SubexponentialSAT_SqrtLog_MomentsReadoutProgramNative`, `SubexponentialSAT_SqrtLog_MomentsReadoutProgramState`, `SubexponentialSAT_SqrtLog_MomentsStored`, `SubexponentialSAT_SqrtLog_PackingIncidenceInputNative`, `SubexponentialSAT_SqrtLog_PackingIncidenceInputStats`, `SubexponentialSAT_SqrtLog_PerturbationMaskProgram`, `SubexponentialSAT_SqrtLog_RingProgramTableStep`, `SubexponentialSAT_SqrtLog_SparseCodeBasic`, `SubexponentialSAT_SqrtLog_SquarefreeSparseBounds`, `SubexponentialSAT_SubexpBasePUnranking`, `SubexponentialSAT_SubexpEmptyClauseProgram`, `SubexponentialSAT_SubexpFlatCount`, `SubexponentialSAT_SubexpNodeScanControl`, `SubexponentialSAT_Subexp_CollisionGenerateRefinement`, `SubexponentialSAT_Subexp_CollisionTupleProgram`, `SubexponentialSAT_Subexp_PackingBucketBounds`, `SubexponentialSAT_Subexp_PackingBucketTable`, `SubexponentialSAT_Subexp_PackingExtractionBounds`, `SubexponentialSAT_Subexp_PackingLeftoverEmitter`, `SubexponentialSAT_Subexp_PackingLeftovers`, `SubexponentialSAT_Subexp_PackingTupleBounds`, `SubexponentialSAT_Subexp_ReadPlan`, `SubexponentialSAT_Subexp_SelectorMapProgram`, `SubexponentialSAT_Subexp_SequentialProgram`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S023`, `OAIQ081S024`, `OAIQ081S025`, `OAIQ081S026`, `OAIQ081S027`, `OAIQ081S028`, `OAIQ081S029`, `OAIQ081S030`, `OAIQ081S031`, `OAIQ081S032`, `OAIQ081S033`, `OAIQ081S035`, `OAIQ081S037`, `OAIQ081S038` and `OAIQ081S039` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S074`, `OAIQ081S077`, `OAIQ081S078`, `OAIQ081S079`, `OAIQ081S080` and `OAIQ081S081`; the statements `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ReconstructionSpace.readback_run_space`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.serializedRows_kernel_bound`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LocalCode.exists_local_code_log_bound` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.supplied_kernel_bound_of_coverage`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.accepted`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.marked`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCount.run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.accepted_replay`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.marked_replay`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.serializedRows_kernel_bound`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.MassPreserve.command_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LocalCode.exists_local_code_log_bound` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.supplied_kernel_bound_of_coverage`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S023
import Definitions.Def_OAIQ081S024
import Definitions.Def_OAIQ081S025
import Definitions.Def_OAIQ081S026
import Definitions.Def_OAIQ081S027
import Definitions.Def_OAIQ081S028
import Definitions.Def_OAIQ081S029
import Definitions.Def_OAIQ081S030
import Definitions.Def_OAIQ081S031
import Definitions.Def_OAIQ081S032
import Definitions.Def_OAIQ081S033
import Definitions.Def_OAIQ081S035
import Definitions.Def_OAIQ081S037
import Definitions.Def_OAIQ081S038
import Definitions.Def_OAIQ081S039

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramQueryCleanup
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid reclamation after one marked or accepted query. The port list is part
of the fixed program syntax. Only the collector, immutable formula/row inputs,
and the outer caller's high ports survive. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Query
open SubexponentialSAT BitProgram StructuredCalls

opaque cleanupPortsWrapped :
    {ports : List (Fin 768) //
      ports = (List.finRange 768).filter (fun i => !decide (Protected i) && decide (i ≠ 699))} :=
  ⟨(List.finRange 768).filter (fun i => !decide (Protected i) && decide (i ≠ 699)), rfl⟩

/-- The fixed lower-workspace cleanup table, kept opaque so elaboration does
not reduce its 768 candidates while checking unrelated resource proofs. -/
def cleanupPorts : List (Fin 768) := cleanupPortsWrapped.1

def cleanup : Code := .seq (.call (StackRoutines.clearProgram 699 0 1))
  (BankRoutines.clearCmd 699 0 1 cleanupPorts)

def cleaned (a : Data) : Data :=
  ⟨readRegs a.regs 0 1 none,
    BankRoutines.clearBankStacks cleanupPorts (Function.update a.stacks 699 [])⟩

def cleanupCost (a : Data) : ℕ :=
  2*(a.stacks 699).length+6+3*cleanupPorts.length+
    2*(cleanupPorts.map (fun i => (a.stacks i).length)).sum

end SubexponentialSAT.SqrtLog.LeafProgram.Query

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

abbrev takeCmd : Cmd 8 8 := SubexpScanPrimitives.takeWord 7 1 2 0 6 0 1
abbrev clearCmd : Cmd 8 8 := .call (StackRoutines.clearProgram 0 0 1)

abbrev extractCmd : Cmd 8 8 :=
  .seq peekCmd (.ite 1 (.seq takeCmd clearCmd) (.base .skip))

end SubexponentialSAT.SubexpFlatCount

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramReadbackReduce
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The count reader reduces the extracted scalar word before returning it.
It therefore works for arbitrary valid coefficient codes, including codes
with noncanonical representatives of zero. -/

namespace SubexponentialSAT.SqrtLog.LeafProgram.Readback

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.ProgramLinking SubexponentialSAT.SubexpFlatCount

abbrev remainderProgram : Program 8 8 89 :=
  liftProgram ModularDivisionPrograms.remainderProgram id decoderPorts

abbrev countCommand : Cmd 8 8 := .seq extractCmd (.call remainderProgram)
def countProgram := compiled countCommand 0 0

open RingProgram SubexponentialSAT.SubexpQuarticRing SubexponentialSAT.BinaryArithmetic

end SubexponentialSAT.SqrtLog.LeafProgram.Readback

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

def project (a : Data) : State 8 8 := ⟨a.regs ∘ regMap, a.stacks ∘ stackMap⟩
noncomputable def install (a : Data) (b : State 8 8) : Data := embedState regMap stackMap a b

end SubexponentialSAT.SqrtLog.LeafProgram.QueryReadback

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramQueryReference
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The marked collector supplies a reversed reference payload on321. The
query itself pays to copy and reverse that reference into the frontend's
forward index slot705. The original payload survives until the branch exit. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Query
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

def markedFlag : Code := .base (SubexpParameterProgram.atoms [.set 0 true,.push 706 0])

def markInput : Code := .seq (.call (StackRoutines.copyProgram 321 699 698 0 1))
  (.seq (.call (StackRoutines.transferProgram 699 705 0 1)) markedFlag)

def noMarkInput : Code :=
  .base (SubexpParameterProgram.atoms [.set 0 false,.push 705 0,.push 706 0])

end SubexponentialSAT.SqrtLog.LeafProgram.Query

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeSparseBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.Squarefree

open scoped BigOperators

namespace Sparse

variable {V R : Type*} [DecidableEq V] [CommSemiring R]

def ValidData (vars : Finset V) (t J : ℕ) (l : Data (Index V) R) : Prop :=
  ∀ a ∈ keys l, a.Kept t J ∧ a.Valid ∧ a.vars ⊆ vars

omit [DecidableEq V] in
theorem ValidData.scale {vars : Finset V} {t J : ℕ} {a : Data (Index V) R}
    (ha : ValidData vars t J a) (c : R) : ValidData vars t J (scale c a) := by
  intro k hk
  rw [keys_scale] at hk
  exact ha k hk

end Sparse
end SubexponentialSAT.SqrtLog.Squarefree

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsStored
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The actual normalized sparse representation used by the head loops.
Proof fields erase at execution; every operation is a finite list operation.
The associated costs count ring operations and key scans. -/

namespace SubexponentialSAT.SqrtLog.Moments

open _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree
open scoped BigOperators

variable {V R : Type*} [DecidableEq V] [CommSemiring R]

structure Stored (vars : Finset V) (t J : ℕ) where
  data : Sparse.Data (Index V) R
  valid : Sparse.ValidData vars t J data
  nodup : (Sparse.keys data).Nodup

namespace Stored

variable {vars : Finset V} {t J : ℕ}

noncomputable def denote (a : Stored (R := R) vars t J) : Jet V R := Sparse.denote a.data

def scale (c : R) (a : Stored (R := R) vars t J) : Stored (R := R) vars t J :=
  ⟨Sparse.scale c a.data, a.valid.scale c, by simpa using a.nodup⟩

end Stored
end SubexponentialSAT.SqrtLog.Moments

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

open SubexponentialSAT.MulticolorTypes SubexponentialSAT.SlotAssignment

section PartialVertexPlans

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype E]
variable (P : SubexponentialSAT.Factor.Pattern V E)
  {r Q Δ : ℕ}

theorem currentArray_getD (default : Word r Q) (seedCount : ℕ)
    (fixed : List (Word r Q)) (n : ℕ) (hn : n < seedCount) :
    (currentArray default seedCount fixed).getD n default =
      SubexponentialSAT.LocalExpectation.decode default fixed n := by
  simp [currentArray, List.getD_eq_getElem?_getD, List.getElem?_range hn]

end PartialVertexPlans

end SubexponentialSAT.Subexp.ReadPlan

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

section Completion

open MulticolorTypes SlotAssignment

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype E]
variable {r Q Δ : ℕ}
  (P : Factor.Pattern V E)

def tupleBytes (candidate : List (Word r Q)) : List Bool :=
  (candidate.map ReadPlan.encodeWord).flatten

end Completion

end SubexponentialSAT.Subexp.CollisionTupleProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingTupleBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Bounds for the actual tuple tables used by packing

These estimates use the concrete framed record encoding and the executable
Cartesian-power recurrence.  The cost bound includes an empty alphabet.
-/

namespace SubexponentialSAT.Subexp.PackingTupleBounds

theorem powerRows_width (alphabet rows : List (List Bool)) (n L W : ℕ)
    (hr : ∀ x ∈ rows, x.length ≤ L)
    (ha : ∀ x ∈ alphabet, x.length ≤ W) :
    ∀ x ∈ TupleProgram.powerRows alphabet n rows, x.length ≤ L + n * W := by
  induction n generalizing rows L with
  | zero => simpa only [TupleProgram.powerRows, Nat.zero_mul, Nat.add_zero] using hr
  | succ n ih =>
      have h := ih (TupleProgram.cartesianOutput rows alphabet) (L + W)
        (PairScoreBounds.cartesian_width rows alphabet L W hr ha)
      intro x hx
      calc
        x.length ≤ L + W + n * W := h x hx
        _ = L + (n + 1) * W := by ring

end SubexponentialSAT.Subexp.PackingTupleBounds

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingProgramTableStep
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingProgramTable

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

theorem embed_triple (s : Store) (oldRegs regs : Fin 8 → Bool)
    (left source saved : List Bool) :
    embedState id triplePorts (state oldRegs s)
      (RingScan.addState regs s.modulus left [] [] source saved s.count s.width) =
      state regs {s with left := left, source := source, saved := saved} := by
  apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id triplePorts_injective
  · intro i; rfl
  · intro i hi; exact False.elim (hi ⟨i, rfl⟩)
  · intro i; fin_cases i <;> rfl
  · intro i hi
    have h0 : i ≠ 0 := fun h => hi ⟨0, h.symm⟩
    have h9 : i ≠ 9 := fun h => hi ⟨9, h.symm⟩
    have h10 : i ≠ 10 := fun h => hi ⟨10, h.symm⟩
    fin_cases i <;> simp_all [ tapes]

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

theorem popArity_eval (regs : Fin 8 → Bool)
    (modulus rank arity rev output : List Bool) :
    Eval popArity 1 (state regs modulus rank arity rev output)
      (afterRead regs modulus rank arity rev output) := by
  have h : (StructuredProgram.Atom.pop (8 : Fin 13) (1 : Fin 8) 3).eval
      (state regs modulus rank arity rev output) =
      afterRead regs modulus rank arity rev output := by
    simp [StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, state, afterRead,
      execInstr]
  rw [← h]
  exact .base (.atom _ _)

end SubexponentialSAT.SubexpBasePUnranking

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

abbrev Data := State 16 48

end SubexponentialSAT.Subexp.SequentialProgram

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

theorem initial_clear_preserves_parameter (i : Fin 77) :
    parameters i ∉ workPorts++outputPorts := by
  have ho : ∀ j∈outputPorts, j.val < 340 := by
    intro j hj
    simp [outputPorts] at hj
    omega
  intro hm
  rcases List.mem_append.mp hm with h | h
  · have h' := (mem_workPorts (parameters i)).mp h
    simp only [parameters] at h'
    omega
  · have h' := ho _ h
    simp only [parameters] at h'
    omega

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram



namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram
open BitProgram StructuredCalls
open LeafParametersProgram

/-- A coarse input-dependent bound for each preserving unary conversion. -/
theorem unaryCopyBound_le (bits : List Bool) (V W : ℕ)
    (hv : BinaryArithmetic.toNat bits ≤ V) (hw : bits.length ≤ W) :
    Serialization.unaryCopyBound bits+1 ≤ 7*W+6+32*(V+1)*(W+1) := by
  rw [Serialization.unaryCopyBound_eq]
  nlinarith [Nat.mul_le_mul (Nat.add_le_add_right hv 1) (Nat.add_le_add_right hw 1)]

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramQueryWidthArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed ordinary polynomial bounds the literal ring, interpolation and
layout-denominator setup budgets, including their staging copies. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Query.Width
open SubexponentialSAT LeafParametersProgram SubexpLiftRing CostAssembly.Polynomial

theorem denominatorEnvelope_ordinary :
    Ordinary (fun S=>LayoutDenominatorProgram.polynomialBudget S (2*S) S) := by
  have h := ordinary_id
  have hb := ordinary_mul (ordinary_const 2) h
  have hp := ordinary_mul (ordinary_pow (ordinary_add h (ordinary_const 1)) 3)
    (ordinary_pow (ordinary_add hb (ordinary_const 1)) 2)
  have hprod := ordinary_mul h hb
  have hfirst := ordinary_mul hb (ordinary_add (ordinary_add
    (ordinary_mul (ordinary_const 100000) hp) (ordinary_mul (ordinary_const 80) hprod)) (ordinary_const 110))
  have hsecond := ordinary_add (ordinary_add (ordinary_mul (ordinary_const 200000) hp)
    (ordinary_mul (ordinary_const 203) hprod)) (ordinary_const 251)
  have hthird := ordinary_mul h (ordinary_add (ordinary_add
    (ordinary_mul (ordinary_const 50000) hp) (ordinary_mul (ordinary_const 8) hprod)) (ordinary_const 11))
  have result := ordinary_add (ordinary_add (ordinary_add (ordinary_add
    (ordinary_add hfirst hsecond) hthird) (ordinary_mul (ordinary_const 7) h))
    (ordinary_mul (ordinary_const 27) hprod)) (ordinary_const 32)
  simpa only [LayoutDenominatorProgram.polynomialBudget,Nat.add_assoc,Nat.mul_assoc] using result

theorem arithmeticEnvelope_ordinary (C e : ℕ) : Ordinary (arithmeticEnvelope C e) := by
  have hp := ordinary_add (ordinary_mul (ordinary_const C)
    (ordinary_pow (ordinary_add ordinary_id (ordinary_const 1)) e)) (ordinary_const 1)
  have hr : Ordinary (ringEnvelope C e) := by
    unfold ringEnvelope
    exact ordinary_add hp (ordinary_mul (ordinary_const 10000)
      (ordinary_add (ordinary_add (ordinary_add (ordinary_add ordinary_id hp)
        (ordinary_const 1)) interpolationEnvelope_ordinary) (ordinary_const 2)))
  unfold arithmeticEnvelope
  exact ordinary_add (ordinary_add hr denominatorEnvelope_ordinary)
    (ordinary_mul (ordinary_const 600) (ordinary_add (ordinary_add ordinary_id hr) (ordinary_const 3)))

end SubexponentialSAT.SqrtLog.LeafProgram.Query.Width

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramRecords
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Measured physical folds over sparse-hash records

This module specializes the audited framed-record iterator to an accumulator
fold which visits every record. The callback is an actual finite `Cmd`; its
local execution contract remains explicit. `foldProgram_run` concerns primitive
Boolean-register/stack transitions, not an operation counter or semantic oracle.
The same program shape handles clause-literal products, sparse weighted sums,
coefficient-array maps, and support-key dictionary scans.
-/

namespace SubexponentialSAT.SqrtLog.LeafProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.RecordPrograms

variable {r s : ℕ} {A : Type*}

@[simp] theorem unread_false (records : List (List Bool)) (suffix : List Bool) :
    unread (fun _ => false) records suffix = suffix := by
  induction records with
  | nil => rfl
  | cons bits records ih => simpa only [unread, Bool.false_eq_true, ↓reduceIte] using ih

end SubexponentialSAT.SqrtLog.LeafProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramSourceStaging
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Protect the target-jet caches while the source-polynomial initializer
uses the same private local ports. Source length and target jet order are
independent runtime values. These are actual copy and clear programs. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.SourceStaging

open SubexponentialSAT BitProgram StructuredCalls SubexpSetupStorage

abbrev Data := State 16 768

end SubexponentialSAT.SqrtLog.LeafProgram.SourceStaging

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
abbrev Data := State 16 768

end SubexponentialSAT.SqrtLog.LeafProgram.SourceReady

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramSquarefree
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The sparse-hash circuit projection theorem instantiated at the actual
Boolean-support U/Z jet algebra. This ties local circuit evaluation to the
same source polynomial used by the global interpolation proof. -/

namespace SubexponentialSAT.SqrtLog.LeafProgram

variable {V C R : Type*} [DecidableEq V] [CommRing R]

noncomputable abbrev squarefreeAlgebra (t J : ℕ) : Algebra (Squarefree.Jet V R) :=
  projectedAlgebra (Squarefree.canonical t J)

end SubexponentialSAT.SqrtLog.LeafProgram

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

def setRegs (xs : List (StructuredProgram.Atom 40 768)) : Code := .base (SubexpParameterProgram.atoms xs)

def clearPrivate : Code := BankRoutines.clearCmd 679 0 1
  ((List.finRange 262).map (block 417 262 (by decide)))

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

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

abbrev clear : Code := .call (StackRoutines.clearProgram 2 0 1)
abbrev command : Code := .seq copy (.seq skip (.seq popScan clear))

abbrev program := compiled command 0 2

end SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Lookup

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafStatisticsProgramScope
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Count precisely the unpinned identifiers in an explicit scope. The mask is
in original coordinate order and the framed natural identifiers are read at
runtime. No arity or other statistic is supplied as an input. -/
namespace SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Scope
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
def ports : RecordPrograms.Ports 7 7 :=
  ⟨4,5,6,5,6,by decide,by decide,by decide,by decide⟩

noncomputable def update (mask bits acc : List Bool) :=
  if low mask (decoded bits) then true::acc else acc

end SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Scope

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
def ports : RecordPrograms.Ports 10 12 :=
  ⟨7,8,9,7,8,by decide,by decide,by decide,by decide⟩

def scopeBudget (mask : List Bool) (scope : List ℕ) :=
  4+RecordPrograms.budget (fun _ => 16*(mask.length+1)) (scope.map Encoding.encodeNat)

noncomputable def decoded (bits : List Bool) : List ℕ := by
  classical
  exact if h : ∃ scope, Encoding.encodeList Encoding.encodeNat scope = bits then Classical.choose h else []

noncomputable def cost (mask bits : List Bool) :=
  3*bits.length+scopeBudget mask (decoded bits)+8*(decoded bits).length+14
noncomputable def update (mask bits : List Bool) (t : ℕ × ℕ) : ℕ × ℕ :=
  (max ((decoded bits).filter (Scope.low mask)).length t.1,t.2+1)

end SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Arity

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafStatisticsProgramVariables
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact runtime accumulation of residual variable statistics. Each degree is
computed by scanning the serialized original scopes. -/
namespace SubexponentialSAT.SqrtLog.LeafStatisticsProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def stepBudget (scopes : List (List ℕ)) (v : ℕ) :=
  SubexpIncidenceSlotProgram.budget scopes scopes.length v + 50*(degree scopes v+1)+50

def variableBudget (scopes : List (List ℕ)) : ℕ → List Bool → ℕ
  | _,[] => 1
  | v,_::bs => stepBudget scopes v + variableBudget scopes (v+1) bs + 1

end SubexponentialSAT.SqrtLog.LeafStatisticsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SparseCodeBasic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Shared interfaces for sparse ternary parity checks

The definitions distinguish edge coordinates from graph vertices. Parallel
edges have different ports. All construction theorems built on these interfaces
must eventually discharge the local-distance and graph-mixing hypotheses.
-/

namespace SubexponentialSAT.SqrtLog.SparseCode

open scoped BigOperators

section Words

variable {C R : Type*} [Fintype C]

def HasDistance (Q : CheckMatrix R C) (d : ℕ) : Prop :=
  ∀ w, IsCodeword Q w → w ≠ 0 → d ≤ weight w

end Words

end SubexponentialSAT.SqrtLog.SparseCode

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LocalCodeSearch
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Executable exhaustive enumeration and its complete-search specification. -/

namespace SubexponentialSAT.SqrtLog.LocalCode

open SparseCode

instance decidableIsCodeword {D t : ℕ} (Q : CheckMatrix (Fin t) (Fin D))
    (w : Fin D → F3) : Decidable (IsCodeword Q w) := by
  unfold IsCodeword
  infer_instance

instance decidableHasDistance {D t : ℕ} (Q : CheckMatrix (Fin t) (Fin D))
    (d : ℕ) : Decidable (HasDistance Q d) := by
  unfold HasDistance
  infer_instance

end SubexponentialSAT.SqrtLog.LocalCode

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafQueryFrontendCommand
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed native syntax from physical formula/row masters through the guarded
parameter bank. The only static input is the fixed formula-width bound k. -/
namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls

def resetScopeRegs : Code := setRegs [.set 0 false,.set 1 false,.set 2 false,.set 3 false,.set 4 false,
  .set 5 false,.set 6 false,.set 7 false,.set 8 false,.set 9 false,.set 10 false]
def arityRegisters : Code := setRegs [.set 7 false,.set 8 true,.set 9 false]

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafQueryFrontendUniform
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls LeafParametersProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

def Query.hashCountBudget (q : Query) : ℕ :=
  SubexpScopeCountSetup.countBudget (q.rows.map (HashScopeProgram.RawTable.rowBits q.width.length))

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

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

def scanMajorant (S : ℕ) : ℕ :=
  (42*S+30+21+HashScopeProgram.Complete.polynomialBound S+7*(16*S^3))+
    highMajorant S+measureMajorant S+numericMajorant S

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
open SubexponentialSAT LeafParametersProgram.FrontendBounds

def finalMajorant (C d S : ℕ) : ℕ :=
  (10*S+9)+525*scanMajorant S+525*(C*(parameterSize S+1)^d)+6300*S+5514

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafScopeResourceBoundsDecode
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A single raw-slot decoder for the actual logical records returned by the
selector's parser. It retains zero-coefficient and repeated entries. -/
namespace SubexponentialSAT.SqrtLog.LeafScopeResourceBounds
open HashSelectProgram

abbrev initialPayloads {m : ℕ} (width : ℕ) (rows : List (List (Fin m × ZMod 3))) :=
  rows.map fun row => (CodeRowsProgram.rowPayload width m row).reverse

end SubexponentialSAT.SqrtLog.LeafScopeResourceBounds

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

def inputTape (modulus width count : List Bool) (entries : List (List Bool × List Bool))
    (query coeff : List Bool) : Tape :=
  { modulus := modulus, width := width, count := count,
    dict := Squarefree.Program.rawEntries entries, query := query.reverse, coeff := coeff }

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

def input (modulus width zero table degree uCap zCap left right : List Bool) : Store :=
  {idle modulus width zero table degree uCap zCap with left := left, right := right}

def output (modulus width zero table degree uCap zCap right result : List Bool) : Store :=
  {idle modulus width zero table degree uCap zCap with right := right, acc := result}

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

def scanProgram := compiled scan 0 1

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

abbrev readFrame (src dst : Fin 10) : Cmd 5 10 := .call
  (ProgramLinking.liftProgram ParserProgram.frameProgram readRegsMap (readPorts src dst))

abbrev scanMask : Cmd 5 10 := .call (ProgramLinking.liftProgram scanProgram smallRegs maskPorts)
abbrev emit : Cmd 5 10 := .call
  (ProgramLinking.liftProgram Squarefree.Program.prependRecordProgram smallRegs emitPorts)
abbrev hit : Cmd 5 10 := .seq emit (transfer 9 8)

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

def ofIndex {n : ℕ} (a : Index (Fin n) × List Bool) : Entry :=
  ⟨a.1.u,a.1.z,encodeMask a.1.vars,a.2⟩

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

def fetchBudget (entries : List (List Bool × List Bool)) (query : List Bool)
    (branch : ℕ) : ℕ :=
  9*(Squarefree.Program.rawEntries entries).length +
    Squarefree.Program.lookupBudget query entries + branch + 12

def fetchedTape (modulus width count : List Bool)
    (entries : List (List Bool × List Bool)) (query acc out : List Bool) : Tape :=
  { inputTape modulus width count entries query acc with out := out }

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

def accumulateBudget (B d : ℕ) (entries : List (List Bool × List Bool))
    (query : List Bool) : ℕ :=
  fetchBudget entries query (codeBranchBudget B d) + 8*(d*B)+9

end SubexponentialSAT.SqrtLog.MomentsReadoutProgram

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


/-! One concrete (u,z) coefficient fetch, addition, and index advance. -/
namespace SubexponentialSAT.SqrtLog.MomentsReadoutProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

def slotBudget (B d n u z : ℕ) (encoded : List (List Bool × List Bool)) : ℕ :=
  accumulateBudget B d encoded
    (Squarefree.encodeIndex (⟨u,z,∅⟩ : Squarefree.Index (Fin n))) +
    9*(n+u+z)+40

def innerBudget (B d n z : ℕ) (encoded : List (List Bool × List Bool)) : ℕ → ℕ → ℕ
  | _,0 => 2
  | u,k+1 => slotBudget B d n u z encoded+innerBudget B d n z encoded (u+1) k+2

end SubexponentialSAT.SqrtLog.MomentsReadoutProgram


/-! The U loop is driven by a real unary stack. Every visit invokes the
concrete key builder and dictionary scan; no callback is left abstract. -/


/-! Seed one Z accumulator from the cached zero vector and append the
completed coefficient to the output, paying for every copy and reversal. -/
namespace SubexponentialSAT.SqrtLog.MomentsReadoutProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

def rowBudget (B d n z t : ℕ) (encoded : List (List Bool × List Bool)) : ℕ :=
  innerBudget B d n z encoded 0 t + 10*(d*B)+9*t+18

end SubexponentialSAT.SqrtLog.MomentsReadoutProgram


/-! Runtime Z enumeration. Completed fixed-width coefficients are prepended
in reverse and are restored once by the final output transfer. -/
namespace SubexponentialSAT.SqrtLog.MomentsReadoutProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

def outerBudget (B d n t : ℕ) (encoded : List (List Bool × List Bool)) : ℕ → ℕ → ℕ
  | _,0 => 2
  | z,J+1 => rowBudget B d n z t encoded+outerBudget B d n t encoded (z+1) J+2

end SubexponentialSAT.SqrtLog.MomentsReadoutProgram


/-! Build the all-false support mask from the actual ambient shape stack.
The loop length is the ambient number of variables, including unused ones. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsReadoutProgramNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! End-to-end finite readout machine. Runtime words supply both loop counts,
the ambient shape, and the already constructed coefficient zero vector. -/
namespace SubexponentialSAT.SqrtLog.MomentsReadoutProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

def readoutBudget (B d n t J : ℕ) (encoded : List (List Bool × List Bool)) : ℕ :=
  outerBudget B d n t encoded 0 J + 3*(J*(d*B))+9*J+13*n+21

end SubexponentialSAT.SqrtLog.MomentsReadoutProgram

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

theorem selected_length_le (records : List (List Bool × List Bool)) (query : List Bool) :
    (selected records query).length ≤ query.length + (SelectorProgram.rawRecords records).length := by
  induction records with
  | nil => simp [selected, SelectorProgram.rawRecords]
  | cons pair records ih =>
      rcases pair with ⟨key, value⟩
      by_cases h : query = key
      · subst key
        simp [selected, SelectorProgram.rawRecords]
        omega
      · have hs : selected ((key, value) :: records) query = selected records query := by
          simp [selected, List.lookup_cons, beq_false_of_ne h]
        rw [hs]
        simpa [SelectorProgram.rawRecords] using
          ih.trans (by simp [SelectorProgram.rawRecords]; omega)

theorem scanBudget_bound (records : List (List Bool × List Bool)) (query : List Bool) :
    SelectorProgram.scanBudget query records ≤
      (9 * query.length + 40) * (SelectorProgram.rawRecords records).length + 1 := by
  induction records with
  | nil => simp [SelectorProgram.scanBudget, SelectorProgram.rawRecords]
  | cons pair records ih =>
      rcases pair with ⟨key, value⟩
      have h := Nat.add_le_add (oneRecord_bound key query value) ih
      simp only [SelectorProgram.scanBudget, SelectorProgram.rawRecords,
        List.flatMap_cons, List.length_append, Encoding.length_frame] at h ⊢
      nlinarith

theorem selectorBudget_bound (records : List (List Bool × List Bool)) (query : List Bool) :
    SelectorProgram.budget query records ≤
      60 * ((SelectorProgram.rawRecords records).length + 1) * (query.length + 1) := by
  have hs := scanBudget_bound records query
  have hl := selected_length_le records query
  have hm : SelectorProgram.materializeBudget query (records.lookup query) ≤
      7 * (query.length + (SelectorProgram.rawRecords records).length) + 6 := by
    cases he : records.lookup query with
    | none => simp [ SelectorProgram.materializeBudget]
    | some value =>
        simp only [selected, he, Option.getD_some] at hl
        simp [ SelectorProgram.materializeBudget]
        omega
  dsimp [SelectorProgram.budget]
  nlinarith [Nat.zero_le (query.length * (SelectorProgram.rawRecords records).length)]

end SubexponentialSAT.Subexp.SelectorMapProgram

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

open MulticolorTypes SlotAssignment

theorem generated_word_perm {r Q : ℕ} (alphabet : List (Word r Q)) (n : ℕ) :
    (TupleProgram.powerRows (alphabet.map ReadPlan.encodeWord) n [[]]).Perm
      ((CoefficientSearch.tuples alphabet n).map fun v =>
        CollisionTupleProgram.tupleBytes (List.ofFn v)) := by
  have h := SubexpTupleRefinement.powerRows_empty_perm (alphabet.map ReadPlan.encodeWord) n
  rw [SubexpTupleRefinement.vectors_map, vectors_eq_tuples, List.map_map] at h
  simpa [SubexpTupleRefinement.tuplePayload, CollisionTupleProgram.tupleBytes,
    List.map_ofFn, Function.comp_def] using h

end SubexponentialSAT.Subexp.CollisionGenerateRefinement

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


/-! Fixed cleanup for the native scope-address scanner. -/


/-! Calls to the fixed record mapper inside the native scope scan. -/


/-! One native low-variable step, including its uncovered neutral factor. -/


/-! Runtime high-mask loop for the original-address incidence stream. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput.Loop
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp
def rowPlans (scopes : List (List ℕ)) (n v z : ℕ) : List (List ℕ) :=
  (Step.factors scopes v z).map fun e => [v,n+e]
def plans (scopes : List (List ℕ)) (n : ℕ) : ℕ → ℕ → List Bool → List (List ℕ)
  | _,_,[] => []
  | v,z,high::rest => plans scopes n (v+1)
      (if high then z else Step.next scopes v z) rest ++
        if high then [] else rowPlans scopes n v z
end SubexponentialSAT.SqrtLog.PackingIncidenceInput.Loop


/-! Count the physical scope stream before constructing native incidence plans. -/

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

theorem factors_length (scopes : List (List ℕ)) (v z : ℕ) :
    (Step.factors scopes v z).length = max 1 (degree scopes v) := by
  change (Step.factors scopes v z).length = max 1 (Scan.indices scopes v).length
  cases h : Scan.indices scopes v with
  | nil => simp [Step.factors,h]
  | cons e es => simp [Step.factors,h]

theorem entries_agree (scopes : List (List ℕ)) (mask : List Bool) :
    ∀ v z (t : Totals), (Semantics.entries scopes v z mask).length + t.incidences =
      (variableTotals scopes v mask t).incidences := by
  induction mask with
  | nil => intros; simp [Semantics.entries,variableTotals]
  | cons b bs ih =>
      intro v z t
      cases b
      · have h := ih (v+1) (Step.next scopes v z) (t.add (degree scopes v))
        simp only [Totals.add] at h
        simp only [Semantics.entries,variableTotals,Bool.false_eq_true,ite_false,
          List.length_append,List.length_map,factors_length]
        simp only [Totals.add] at *
        omega
      · simpa [Semantics.entries,variableTotals] using ih (v+1) z t

end SubexponentialSAT.SqrtLog.PackingIncidenceInput.Stats

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationMaskProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed native constructor for original-coordinate singleton masks.
Masters212/218 are retained; output214 and scratch120/221/222/223 are the
only touched stacks. No table of masks or semantic mask oracle is supplied. -/
namespace SubexponentialSAT.SqrtLog.PerturbationMaskProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl SubexpScanPrimitives

def fill (s : Store) (count out : List Bool) : Store :=
  Function.update (Function.update s 221 count) 214 out

@[simp] theorem fill_count (s : Store) (count out : List Bool) :
    fill s count out 221=count := by simp [fill]
@[simp] theorem fill_out (s : Store) (count out : List Bool) :
    fill s count out 214=out := by simp [fill]
@[simp] theorem fill_update_count (s : Store) (count out next : List Bool) :
    Function.update (fill s count out) 221 next=fill s next out := by
  ext i
  by_cases h0 : i=221 <;> by_cases h1 : i=214 <;>
    simp [fill,Function.update_apply,h0,h1]
@[simp] theorem fill_update_out (s : Store) (count out next : List Bool) :
    Function.update (fill s count out) 214 next=fill s count next := by
  simp [fill]

end SubexponentialSAT.SqrtLog.PerturbationMaskProgram

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

abbrev clear (i : Fin 10) : Cmd 10 10 := .call (StackRoutines.clearProgram i 0 1)

end SubexponentialSAT.SubexpEmptyClauseProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpNodeScanControl
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed traversal of flat node cells, skipping one unary-indexed node.
The included-node service is an actual command with an actual execution
contract. This file accounts for all reads, guards, index pops, and cleanup.
-/

namespace SubexponentialSAT.SubexpNodeScanControl

open BitProgram StructuredCalls SubexpConvolutionControl

noncomputable def work (base : Store) (w : Fin 6 → List Bool) : Store :=
  Function.extend ports w base

@[simp] theorem work_port (base : Store) (w : Fin 6 → List Bool) (i : Fin 6) :
    work base w (ports i) = w i := ports.injective.extend_apply _ _ _

@[simp] theorem work_215 (base : Store) (w : Fin 6 → List Bool) : work base w 215 = w 0 :=
  work_port base w 0
@[simp] theorem work_217 (base : Store) (w : Fin 6 → List Bool) : work base w 217 = w 1 :=
  work_port base w 1
@[simp] theorem work_229 (base : Store) (w : Fin 6 → List Bool) : work base w 229 = w 2 :=
  work_port base w 2
@[simp] theorem work_240 (base : Store) (w : Fin 6 → List Bool) : work base w 240 = w 3 :=
  work_port base w 3
@[simp] theorem work_218 (base : Store) (w : Fin 6 → List Bool) : work base w 218 = w 4 :=
  work_port base w 4
@[simp] theorem work_219 (base : Store) (w : Fin 6 → List Bool) : work base w 219 = w 5 :=
  work_port base w 5

end SubexponentialSAT.SubexpNodeScanControl

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingBucketTable
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The fixed all-key bucket/minimum controller. -/

namespace SubexponentialSAT.Subexp.PackingBucketTable

open BitProgram StructuredCalls MatrixProgramSupport PackingBucketCalls

theorem minimum_le (records : List BucketProgram.Record) (keys : List (List Bool)) (initial : ℕ) :
    minimum records keys initial ≤ initial := by
  induction keys generalizing initial with
  | nil => exact le_rfl
  | cons key keys ih =>
    exact (ih _).trans (min_le_left _ _)

end SubexponentialSAT.Subexp.PackingBucketTable

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingBucketBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Polynomial serialized-input bounds for the actual all-type bucket program. -/

namespace SubexponentialSAT.Subexp.PackingBucketTable

open MatrixProgramSupport

theorem iteration_bound (records : List BucketProgram.Record) (keys : List (List Bool))
    (T : ℕ) (hkeys : ∀ key ∈ keys, key.length ≤ T) :
    RecordPrograms.budget (callbackCost records) keys ≤
      keys.length * (6 * T + 100 * ((BucketProgram.encodeRecords records).length + 1) * (T + 1) + 7) := by
  induction keys with
  | nil => simp [RecordPrograms.budget]
  | cons key keys ih =>
    have hk := hkeys key (by simp)
    have ht := ih (fun q hq => hkeys q (by simp [hq]))
    have hc : callbackCost records key ≤
        100 * ((BucketProgram.encodeRecords records).length + 1) * (T + 1) :=
      Nat.mul_le_mul_left _ (Nat.add_le_add_right hk 1)
    simp only [RecordPrograms.budget, List.length_cons, Nat.add_mul]
    omega

end SubexponentialSAT.Subexp.PackingBucketTable

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

theorem emitEntries_address_length (i : ℕ) (entries : List Entry) (c : Context) :
    (emitEntries i entries c).address.length = c.address.length + entries.length := by
  induction entries generalizing c with
  | nil => simp [emitEntries]
  | cons e es ih =>
    change (emitEntries i es (emitted c e.1 (entryVertex i e))).address.length = _
    rw [ih]
    simp [emitted, Nat.add_comm, Nat.add_left_comm]

end SubexponentialSAT.Subexp.PackingExtraction

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingLeftoverEmitter
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual emission and covered-key lookup for the leftover packing pass. -/

namespace SubexponentialSAT.Subexp.PackingCoveredQuery

open BitProgram StructuredCalls

theorem scanBudget_le (query : List Bool) (records : List (List Bool × List Bool)) :
    SelectorProgram.scanBudget query records ≤
      (9*query.length+20)*(SelectorProgram.rawRecords records).length+1 := by
  induction records with
  | nil => simp [SelectorProgram.scanBudget,SelectorProgram.rawRecords]
  | cons p records ih =>
      rcases p with ⟨key,value⟩
      have hlen : (SelectorProgram.rawRecords ((key,value)::records)).length =
          2*key.length+2*value.length+2+(SelectorProgram.rawRecords records).length := by
        simp [SelectorProgram.rawRecords,Encoding.length_frame]
        omega
      have hlocal : 17*key.length+9*query.length+13*value.length+40 ≤
          (9*query.length+20)*(2*key.length+2*value.length+2) := by
        nlinarith [Nat.zero_le (query.length*key.length),Nat.zero_le (query.length*value.length)]
      rw [SelectorProgram.scanBudget,SubexpRecordScan.recordCost,hlen]
      nlinarith

end SubexponentialSAT.Subexp.PackingCoveredQuery


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

theorem advance_rank_le (records : Records) (s : Snapshot) (v : ℕ) :
    (advance records s v).rank ≤ s.rank+1 := by
  unfold advance
  split <;> simp [appendVertex]

theorem advance_address_le (records : Records) (s : Snapshot) (v : ℕ) :
    (advance records s v).address ≤ s.address+1 := by
  unfold advance
  split <;> simp [appendVertex]

end SubexponentialSAT.Subexp.PackingLeftovers

end OAI.Algorithms
end


