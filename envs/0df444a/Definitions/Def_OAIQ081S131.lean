-- Prove2me | Definitions.Def_OAIQ081S131
-- name    : OAIQ081S131
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T22:41:11.041666+00:00
-- url     : https://prove2.me/theorems/a0c92e56-0ea2-48a8-88fd-d4ea6015a2fc
-- title:
--   Definitions bundle OAIQ081S131 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 110 declarations of OpenAI's Lean: 91 definitions, 1 inductive type or structure and 18 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgram.Code`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgram.Problem.raw`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgram.Wide.Code`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgram.Wide.bankCall`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgram.Wide.call`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgram.Wide.exportLocal`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgram.Wide.finish`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgram.Wide.finishLocal`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgram.Wide.stage`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgram.Wide.stageLocal`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgram.cacheInputs`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgram.clearLow`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgram.incidenceTail`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgram.incidenceTailProgram`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgram.loadedStore`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgram.outputStore`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgram.planBits`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgram.planStore`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgram.prepareLiterals`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgram.prepareSuffix`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgram.produceBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgram.saveHigh`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgram.selectedStore`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInput.Clear.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInput.Clear.one`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInput.Install.depth`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInput.Lift.clean`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInput.Lift.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInput.Loop.body`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInput.Rows.callback`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInput.Rows.clear`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInput.Rows.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInput.Rows.copy`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInput.Rows.emit`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInput.Rows.transfer`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInput.Scan.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInput.Scan.copy`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInput.Scan.prepare`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInput.Scan.scan`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInput.Step.branch` and 52 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLogSpace_HighQueryAdapter`, `SubexponentialSAT_SqrtLogSpace_QueryAssembler`, `SubexponentialSAT_SqrtLog_PackingCallerProgramBasic`, `SubexponentialSAT_SqrtLog_PackingCallerProgramBoundsBasic`, `SubexponentialSAT_SqrtLog_PackingCallerProgramBoundsSelection`, `SubexponentialSAT_SqrtLog_PackingCallerProgramCache`, `SubexponentialSAT_SqrtLog_PackingCallerProgramCore`, `SubexponentialSAT_SqrtLog_PackingCallerProgramExport`, `SubexponentialSAT_SqrtLog_PackingCallerProgramIncidence`, `SubexponentialSAT_SqrtLog_PackingCallerProgramModel`, `SubexponentialSAT_SqrtLog_PackingCallerProgramPrepare`, `SubexponentialSAT_SqrtLog_PackingCallerProgramStage`, `SubexponentialSAT_SqrtLog_PackingCallerProgramWide`, `SubexponentialSAT_SqrtLog_PackingIncidenceInputAddress`, `SubexponentialSAT_SqrtLog_PackingIncidenceInputEntry`, `SubexponentialSAT_SqrtLog_PackingIncidenceInputInstall`, `SubexponentialSAT_SqrtLog_PackingIncidenceInputNative`, `SubexponentialSAT_SqrtLog_PackingIncidenceProgram`, `SubexponentialSAT_SqrtLog_PackingIncidenceProgramGenerated`, `SubexponentialSAT_SqrtLog_PackingIncidenceProgramInputs`, `SubexponentialSAT_SqrtLog_PackingIncidenceProgramInstall`, `SubexponentialSAT_SqrtLog_PackingIncidenceProgramPairs`, `SubexponentialSAT_SqrtLog_PackingIncidenceProgramSize`, `SubexponentialSAT_SqrtLog_PackingLoaderProgramFrame`, `SubexponentialSAT_SqrtLog_PackingPrefixProgram`, `SubexponentialSAT_SqrtLog_PackingPrefixProgramRun`, `SubexponentialSAT_SqrtLog_PackingProgramAssemblyHeadSetup`, `SubexponentialSAT_SqrtLog_PackingProgramAssemblyHeads`, `SubexponentialSAT_SqrtLog_PackingProgramAssemblyIncidence`, `SubexponentialSAT_SqrtLog_PackingProgramAssemblyScope`, `SubexponentialSAT_Subexp_AssignmentInputProgram`, `SubexponentialSAT_Subexp_CandidateScoreProgram`, `SubexponentialSAT_Subexp_OneHotAlphabetProgram`, `SubexponentialSAT_Subexp_PairPreparationBounds`, `SubexponentialSAT_Subexp_PairScoreProgram`, `SubexponentialSAT_Subexp_ScoreBuilderProgram`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S100`, `OAIQ081S102`, `OAIQ081S109`, `OAIQ081S110` and `OAIQ081S111` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S141`, `OAIQ081S147`, `OAIQ081S148`, `OAIQ081S149`, `OAIQ081S150` and `OAIQ081S152`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S100
import Definitions.Def_OAIQ081S102
import Definitions.Def_OAIQ081S109
import Definitions.Def_OAIQ081S110
import Definitions.Def_OAIQ081S111

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighQueryAdapter
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete per-high-assignment setup and compressed head overlays.
The routines read physical counter/mask words and preserve ambient coordinates. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter

open OAI BitProgram StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram

namespace NativeHeadSelect
open OAI.Algorithms.SubexponentialSAT.StackRoutines

abbrev Code := Cmd 40 896

end NativeHeadSelect

open OAI.Algorithms.SubexponentialSAT.StackRoutines


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter
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

abbrev generate : Cmd 13 26 :=
  .call (ProgramLinking.liftProgram CollisionGenerateProgram.program generatorRegs generatorPorts)

abbrev callback : Cmd 13 26 := .seq prepare (.seq generate cleanup)

abbrev loop : Cmd 13 26 := RecordPrograms.iterate ports callback

abbrev command : Cmd 13 26 := .seq loop tally

abbrev program : Program 13 26 (StructuredCalls.size command + 1) :=
  StructuredCalls.compiled command 20 18

end SubexponentialSAT.Subexp.PairScoreProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryAssembler
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Physical assembly of the streamed query. Arithmetic caches are installed
from retained produced words by paid finite commands. These local theorems do
not assert completion of the node, pair, or tuple evaluator. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryAssembler

open OAI BitProgram StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProgram

attribute [local simp] Fin.coe_ofNat_eq_mod

abbrev Code := Cmd 40 896

open SubexpLiftRing SubexpQuarticRing
open OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram
open TruncatedRingProgram


/-! The interpolation-node cursor is the actual framed table emitted by the
ring producer. Its low-bank loader is embedded into the common leaf bank;
all high pair/tuple state is preserved by the injective port map. -/


/-! Native multiplication of one completed head sum into the tuple product.
The original accumulator is relocated only at its two persistent operands. -/

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryAssembler
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

abbrev runPairs : Cmd 16 36 :=
  .call (ProgramLinking.liftProgram PairScoreProgram.program lowRegisters lowStacks)

abbrev callback : Cmd 16 36 :=
  .seq transferCandidate (.seq updateCandidate (.seq copyPairs
    (.seq resetLow (.seq runPairs (.seq emitScore cleanup)))))

abbrev iterateCandidates : Cmd 16 36 := RecordPrograms.iterate outerPorts callback

abbrev command : Cmd 16 36 := .seq copyCandidates (.seq iterateCandidates finish)
def program := StructuredCalls.compiled command 30 32

end SubexponentialSAT.Subexp.CandidateScoreProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PairPreparationBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Uniform polynomial bounds for the actual once-per-step pair preparation
program. The common parameter bounds physical input lengths and record count. -/

namespace SubexponentialSAT.Subexp.PairPreparationBounds

open BitProgram PairPreparationProgram

theorem encoded_pairRecords_le (pairs : List PlanPair) (W : ℕ)
    (h : ∀ pair ∈ pairs, (PairScoreProgram.pairBytes pair).length ≤ W) :
    (PairScoreProgram.pairRecords pairs).length ≤ 1 + (2 * W + 2) * pairs.length := by
  have he := ProgramEncoding.encodeRecords_length_le (pairs.map PairScoreProgram.pairBytes) W (by
    intro bytes hbytes
    obtain ⟨pair, hp, rfl⟩ := List.mem_map.mp hbytes
    exact h pair hp)
  simpa only [PairScoreProgram.pairRecords, List.length_map] using he

end SubexponentialSAT.Subexp.PairPreparationBounds

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_ScoreBuilderProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# The actual global candidate-score builder

Pair read plans are prepared once for the current processed position. The
candidate loop then executes the local collision enumeration and emits scores
in candidate order. A final fixed routine restores the temporary table ports.
-/

namespace SubexponentialSAT.Subexp.ScoreBuilderProgram

open BitProgram StructuredCalls

abbrev candidates : Cmd 16 48 := .call
  (ProgramLinking.liftProgram CandidateScoreProgram.program id candidatePorts)

abbrev command : Cmd 16 48 := .seq preparation (.seq candidates finish)

end SubexponentialSAT.Subexp.ScoreBuilderProgram

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

/-- Each incidence reads an original-variable word and a factor word. -/
structure ValidRawPair (M : ℕ) (pair : PlanPair) : Prop where
  left_length : pair.1.length ≤ 2
  right_length : pair.2.length ≤ 2
  left_valid : ∀ i ∈ pair.1, i < M
  right_valid : ∀ i ∈ pair.2, i < M

theorem pairBytes_length_le (M : ℕ) (pair : PlanPair) (hp : ValidRawPair M pair) :
    (PairScoreProgram.pairBytes pair).length ≤ 16 * (M + 1) + 6 := by
  have hl := PairPreparationBounds.planBytes_le pair.1 M
    (fun i hi => (hp.left_valid i hi).le)
  have hr := PairPreparationBounds.planBytes_le pair.2 M
    (fun i hi => (hp.right_valid i hi).le)
  have hleft := hp.left_length
  have hright := hp.right_length
  simp only [PairScoreProgram.pairBytes, List.length_append, Encoding.length_frame]
  nlinarith

abbrev command := ScoreBuilderProgram.command

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

theorem incidencePair_valid (indices : List (V ⊕ E))
    (hindices : ∀ a, a ∈ indices) (pair : I × I) :
    ValidRawPair indices.length (incidencePair ivar factor indices pair) := by
  let _ : BEq (V ⊕ E) := instBEqOfDecidableEq
  have hcode (a : V ⊕ E) : indexCode indices a < indices.length :=
    List.idxOf_lt_length_iff.mpr (hindices a)
  constructor
  · simp [incidencePair, incidencePlan]
  · simp [incidencePair, incidencePlan]
  · intro j hj
    simp only [incidencePair, incidencePlan, List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl <;> exact hcode _
  · intro j hj
    simp only [incidencePair, incidencePlan, List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl <;> exact hcode _

def rawPairs (indices : List (V ⊕ E)) (incidences : List I) : List PlanPair :=
  (incidences.product incidences).map (incidencePair ivar factor indices)

theorem rawPairs_valid (indices : List (V ⊕ E)) (hindices : ∀ a, a ∈ indices)
    (incidences : List I) :
    ∀ pair ∈ rawPairs ivar factor indices incidences, ValidRawPair indices.length pair := by
  intro pair hpair
  obtain ⟨p, _, rfl⟩ := List.mem_map.mp hpair
  exact incidencePair_valid ivar factor indices hindices p

@[simp] theorem rawPairs_length (indices : List (V ⊕ E)) (incidences : List I) :
    (rawPairs ivar factor indices incidences).length = incidences.length^2 := by
  change ((incidences.product incidences).map _).length = _
  rw [List.length_map]
  exact (List.length_product incidences incidences).trans (pow_two _).symm

end Plans

end SubexponentialSAT.SqrtLog.PackingIncidenceProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingIncidenceProgramPairs
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual depth-two tuple program builds all raw incidence-pair records.
Its input has one two-address record per incidence, not a quadratic table. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.Subexp

def generatedRawPairs (plans : List (List ℕ)) : List PlanPair :=
  (TupleProgram.powerRows (planAlphabet plans) 2 [[]]).map PairScoreProgram.readPair

theorem generatedRawPairs_perm (plans : List (List ℕ)) :
    (generatedRawPairs plans).Perm (plans.product plans) :=
  CandidateScoreRefinement.generated_pair_payloads_decode plans

theorem generatedRawPairs_length (plans : List (List ℕ)) :
    (generatedRawPairs plans).length = plans.length^2 := by
  exact (generatedRawPairs_perm plans).length_eq.trans
    ((List.length_product plans plans).trans (pow_two _).symm)

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
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput.Rows
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

abbrev copy : Cmd 6 9 := .call (StackRoutines.copyProgram 1 3 4 0 1)
abbrev transfer : Cmd 6 9 := .call (StackRoutines.transferProgram 2 3 0 1)
abbrev clear : Cmd 6 9 := .call (StackRoutines.clearProgram 3 0 1)
abbrev emit : Cmd 6 9 := .call
  (ProgramLinking.liftProgram (compiled Emit.command 0 5) registers ports)
abbrev callback : Cmd 6 9 := .seq copy (.seq transfer (.seq emit clear))
abbrev command : Cmd 6 9 := RecordPrograms.iterate readerPorts callback
end SubexponentialSAT.SqrtLog.PackingIncidenceInput.Rows


/-! Native per-variable incident-factor scan from the original scope stream. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput.Scan
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

abbrev copy (src dst : Fin 32) : Cmd 16 32 :=
  .call (StackRoutines.copyProgram src dst 31 0 1)

abbrev prepare : Cmd 16 32 := .seq (copy 20 6) (.seq (copy 22 2)
  (.seq (TupleProgram.pushConst 2 0 false) (TupleProgram.pushConst 7 0 false)))
abbrev scan : Cmd 16 32 := .call (ProgramLinking.liftProgram
  (compiled SubexpIncidencePlanScan.command 6 7) registers ports)
abbrev command : Cmd 16 32 := .seq prepare scan
end SubexponentialSAT.SqrtLog.PackingIncidenceInput.Scan


/-! Fixed cleanup for the native scope-address scanner. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

namespace Clear
abbrev one (j : Fin 32) : Cmd 16 32 := .call (StackRoutines.clearProgram j 0 1)
def command : List (Fin 32) → Cmd 16 32
  | [] => .base .skip
  | j::js => .seq (one j) (command js)
end Clear
end SubexponentialSAT.SqrtLog.PackingIncidenceInput


/-! Calls to the fixed record mapper inside the native scope scan. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput.Lift
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp
abbrev command (c : Cmd 6 9) : Cmd 16 32 :=
  .call (ProgramLinking.liftProgram (compiled c 8 7) registers ports)

abbrev clean : Cmd 16 32 := Clear.command [2,5,7,9]
end SubexponentialSAT.SqrtLog.PackingIncidenceInput.Lift


/-! One native low-variable step, including its uncovered neutral factor. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput.Step
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

def rows := Lift.command Rows.command
abbrev neutral : Cmd 16 32 := .seq (Scan.copy 24 12)
  (.seq (Lift.command Rows.callback) (TupleProgram.pushConst 24 0 true))
abbrev peek : Cmd 16 32 := .seq (.base (.atom (.pop 7 10 11)))
  (.base (.atom (.push 7 10)))
abbrev branch : Cmd 16 32 := .ite 10 rows neutral
abbrev command : Cmd 16 32 := .seq Scan.command (.seq peek (.seq branch Lift.clean))

end SubexponentialSAT.SqrtLog.PackingIncidenceInput.Step


/-! Runtime high-mask loop for the original-address incidence stream. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput.Loop
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp
abbrev body : Cmd 16 32 := .seq (.ite 14 (.base .skip) Step.command)
  (TupleProgram.pushConst 22 0 true)
end SubexponentialSAT.SqrtLog.PackingIncidenceInput.Loop


/-! Count the physical scope stream before constructing native incidence plans. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingIncidenceProgramInstall
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid generation and installation of raw pairs from a linear plan stream. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceProgram.Install
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

def budget (plans : List (List ℕ)) : ℕ :=
  100 * (TupleProgram.powerCost (planAlphabet plans) 2 [[]] + 9 +
    (ProgramEncoding.encodeRecords (planAlphabet plans)).length + 1)

end SubexponentialSAT.SqrtLog.PackingIncidenceProgram.Install

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
abbrev depth : Cmd 16 48 := .seq (TupleProgram.pushConst 27 0 true) (TupleProgram.pushConst 27 0 true)
end SubexponentialSAT.SqrtLog.PackingIncidenceInput.Install

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

theorem generatedIncidencePairs_perm (indices : List (V ⊕ E)) (incidences : List I) :
    (generatedRawPairs (incidencePlans ivar factor indices incidences)).Perm
      (rawPairs ivar factor indices incidences) := by
  simpa [incidencePlans, rawPairs, incidencePair, List.product, List.flatMap_map,
    List.map_flatMap, List.map_map, Function.comp_def] using
    generatedRawPairs_perm (incidencePlans ivar factor indices incidences)

theorem incidencePlans_valid (indices : List (V ⊕ E)) (hi : ∀ x, x ∈ indices)
    (incidences : List I) :
    (∀ p ∈ incidencePlans ivar factor indices incidences, p.length ≤ 2) ∧
    (∀ p ∈ incidencePlans ivar factor indices incidences, ∀ i ∈ p, i < indices.length) := by
  constructor
  · intro p hp
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hp
    simp [incidencePlan]
  · intro p hp j hj
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hp
    exact (incidencePair_valid ivar factor indices hi (i,i)).left_valid j hj

end Plans

end SubexponentialSAT.SqrtLog.PackingIncidenceProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingIncidenceProgramSize
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Input size, produced table size, and binary size of the exact numerator. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.MulticolorTypes SubexponentialSAT.LocalExpectation SubexponentialSAT.Subexp
open SubexponentialSAT.Subexp.LocalExpectation SubexponentialSAT.SqrtLog.Packing SubexponentialSAT.SqrtLog.PackingProgram

theorem planInput_length_le (M : ℕ) (plans : List (List ℕ))
    (hlen : ∀ p ∈ plans, p.length ≤ 2) (hindex : ∀ p ∈ plans, ∀ i ∈ p, i < M) :
    (ProgramEncoding.encodeRecords (planAlphabet plans)).length ≤
      1 + (16*M+24)*plans.length := by
  have h := ProgramEncoding.encodeRecords_length_le (planAlphabet plans) (8*M+11)
    (planAlphabet_width M plans hlen hindex)
  have hc : 2*(8*M+11)+2 = 16*M+24 := by omega
  rw [hc] at h
  simpa only [planAlphabet, List.length_map] using h

section Sizes
variable {I V E : Type*} [Fintype I] [Fintype V] [Fintype E]
  [DecidableEq I] [DecidableEq V] [DecidableEq E]
  (ivar : I → V) (factor : I → E) {r Q : ℕ}

omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] in
theorem generatedPairRecords_length_le (indices : List (V ⊕ E)) (hi : ∀ x, x ∈ indices)
    (incidences : List I) :
    (PairScoreProgram.pairRecords
      (generatedRawPairs (incidencePlans ivar factor indices incidences))).length ≤
      1 + (32*(indices.length+1)+14)*incidences.length^2 := by
  have h := PairPreparationBounds.encoded_pairRecords_le
    (generatedRawPairs (incidencePlans ivar factor indices incidences))
    (16*(indices.length+1)+6) (by
      intro pair hp
      have hraw := (generatedIncidencePairs_perm ivar factor indices incidences).mem_iff.mp hp
      exact pairBytes_length_le indices.length pair
        (rawPairs_valid ivar factor indices hi incidences pair hraw))
  have hc : 2*(16*(indices.length+1)+6)+2 = 32*(indices.length+1)+14 := by omega
  rw [hc] at h
  simpa only [generatedRawPairs_length, incidencePlans, List.length_map] using h

end Sizes
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


/-! Raw scopes and the computed mask feed the actual incidence-pair producer. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput.Finished
open SubexponentialSAT.BitProgram SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp

theorem output_bits_le (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool)
    (hm : mask.length ≤ n) :
    (PairScoreProgram.pairRecords (PackingIncidenceProgram.generatedRawPairs
      (Install.plans scopes n mask))).length ≤
      1 + (32*(n+Semantics.factorCount scopes mask+1)+14)*
        (Semantics.nativeEntries scopes mask).length^2 := by
  rw [Install.plans, ← Semantics.incidencePlans_eq scopes n mask hm]
  have h := PackingIncidenceProgram.generatedPairRecords_length_le
    (Semantics.owner scopes n mask hm) (Semantics.factor scopes n mask hm)
    (Semantics.seedIndices n (Semantics.factorCount scopes mask))
    (Semantics.seedIndices_complete _ _) (incidenceList scopes mask)
  simpa [Semantics.seedIndices,Packing.headsFirst_length,incidenceList] using h
theorem pair_budget_le (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool)
    (hm : mask.length ≤ n) :
    PackingIncidenceProgram.Install.budget (Install.plans scopes n mask) ≤
      100*(2400*((Semantics.nativeEntries scopes mask).length+1)^2*
        (24*(n+Semantics.factorCount scopes mask)+34)+11+
        (16*(n+Semantics.factorCount scopes mask)+24)*
          (Semantics.nativeEntries scopes mask).length) := by
  let S := n+Semantics.factorCount scopes mask
  let ps := Install.plans scopes n mask
  have hlen : ps.length = (Semantics.nativeEntries scopes mask).length := by
    simp [ps,Install.plans,Semantics.plans_eq,Semantics.nativeEntries]
  have hi : (Semantics.seedIndices n (Semantics.factorCount scopes mask)).length = S := by
    simp [Semantics.seedIndices,Packing.headsFirst_length,S]
  have hv := PackingIncidenceProgram.incidencePlans_valid
    (Semantics.owner scopes n mask hm) (Semantics.factor scopes n mask hm)
    (Semantics.seedIndices n (Semantics.factorCount scopes mask))
    (Semantics.seedIndices_complete _ _) (incidenceList scopes mask)
  rw [Semantics.incidencePlans_eq,hi] at hv
  have hb := PackingIncidenceProgram.planInput_length_le S ps hv.1 hv.2
  have hp : TupleProgram.powerCost (PackingIncidenceProgram.planAlphabet ps) 2 [[]]+9 ≤
      2400*(ps.length+1)^2*(24*S+34)+9 := by
    by_cases hn : ps = []
    · have hz : TupleProgram.powerCost [] 2 [[]]+9 ≤ 2400*34+9 := by decide
      simp only [hn,PackingIncidenceProgram.planAlphabet,List.map_nil,List.length_nil,
        zero_add,one_pow,mul_one]
      nlinarith
    · have h := PackingIncidenceProgram.rawPairProgram_cost S ps hn hv.1 hv.2
      have hsq : ps.length^2 ≤ (ps.length+1)^2 := by nlinarith
      have hmul := Nat.mul_le_mul_right (2400*(24*S+34)) hsq
      nlinarith
  change PackingIncidenceProgram.Install.budget ps ≤ _
  dsimp [PackingIncidenceProgram.Install.budget]
  rw [← hlen]
  change _ ≤ 100*(2400*(ps.length+1)^2*(24*S+34)+11+(16*S+24)*ps.length)
  omega

end SubexponentialSAT.SqrtLog.PackingIncidenceInput.Finished

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingLoaderProgramFrame
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Framing and paid parameter serialization for the packing loader. -/
namespace SubexponentialSAT.SqrtLog.PackingLoaderProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
def unaryCommand (ports : Fin 14 ↪ Fin 64) : Code :=
  liftCommand (LeafParametersProgram.Serialization.unaryCopy 0 1) 0 1 unaryRegs ports

end SubexponentialSAT.SqrtLog.PackingLoaderProgram

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

abbrev copy (src dst : Fin 7) : Cmd 5 7 :=
  .call (StackRoutines.copyProgram src dst 4 0 1)

abbrev repeatZeros : Cmd 5 7 :=
  .call (ProgramLinking.liftProgram BlockCopyProgram.program repeatRegisters repeatStacks)

abbrev zeroThird : Cmd 5 7 := .base (.atom (.set 2 false))

abbrev body : Cmd 5 7 :=
  .seq (copy 1 2) (.seq (pushConst 2 0 true) (.seq (copy 0 3)
    (.seq zeroThird (.seq repeatZeros (.seq (pushConst 6 0 false)
      (.seq (escape emitter) (.seq (pushConst 6 0 true) (pushConst 1 0 false))))))))

def loopPorts : UnaryForPrograms.Ports 5 7 := ⟨0, 3, 4⟩
abbrev enumerate : Cmd 5 7 := UnaryForPrograms.forCmd loopPorts body

abbrev reset : Cmd 5 7 := .base (CandidateScoreProgram.resetList (List.finRange 5))
abbrev command : Cmd 5 7 :=
  .seq (pushConst 5 0 false) (.seq (pushConst 6 0 false) (.seq enumerate
    (.seq (.call (StackRoutines.clearProgram 1 0 1))
      (.seq (.call (StackRoutines.clearProgram 5 0 1)) reset))))

abbrev program : Program 5 7 (size command + 1) := compiled command 0 6

end SubexponentialSAT.Subexp.OneHotAlphabetProgram

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

open BitProgram StructuredCalls SubexpSetupStorage AssignmentInputCall

def colorAlphabet : Code := AssignmentInputCall.call OneHotAlphabetProgram.program
  (by decide) (by decide) [(1, 12)] 6 7

def firstWord : Code := AssignmentInputCall.call AssignmentRecordViews.firstProgram
  (by decide) (by decide) [(30, 12)] 2 0

def packedAlphabet : Code := AssignmentInputCall.call AssignmentRecordViews.flattenProgram
  (by decide) (by decide) [(30, 12)] 2 9

def deltaPlusOne : Code := .seq (copyCmd 3 6 31) (TupleProgram.pushConst 6 0 true)

def seedProduct : Code := AssignmentInputCall.call BlockCopyProgram.program
  (by decide) (by decide) [(4, 12), (6, 15)] 1 47

def seedRange : Code := AssignmentInputCall.call AssignmentSeedRange.program
  (by decide) (by decide) [(47, 12)] 5 46

def cleanup : Code := .seq (clearMany [1, 2, 3, 4, 5, 6, 7]) (resetMany (List.finRange 16))

end SubexponentialSAT.Subexp.AssignmentInputProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingCallerProgramBasic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Framed local storage for the concrete packing caller. Ports53/54 retain
width/alphabet,55..59 parameters,60 scopes,61 plans,62 words,63 metadata. -/
namespace SubexponentialSAT.SqrtLog.PackingCallerProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage
open PackingLoaderProgram
abbrev Code := Cmd 16 64

def saveHigh (src : Fin 48) (dst : Fin 64) : Code := copyCmd (lowPorts src) dst 52

def clearLow : Code := clearMany lowClearPorts

end SubexponentialSAT.SqrtLog.PackingCallerProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingCallerProgramIncidence
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Preserve the physically generated owner/factor plans before the incidence
pair installer consumes them. The extra master is local port61. -/
namespace SubexponentialSAT.SqrtLog.PackingCallerProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp
open PackingLoaderProgram PackingIncidenceInput

def planBits (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool) :=
  ProgramEncoding.encodeRecords (PackingIncidenceProgram.planAlphabet (Install.plans scopes n mask))

abbrev incidenceTail : Cmd 16 48 := .seq Install.depth PackingIncidenceProgram.Install.command
def incidenceTailProgram := compiled incidenceTail 20 45

def produceBudget (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool) :=
  Boot.fullBudget scopes n mask+1 + (7*(planBits scopes n mask).length+5) +
    (4+PackingIncidenceProgram.Install.budget (Install.plans scopes n mask))

end SubexponentialSAT.SqrtLog.PackingCallerProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingCallerProgramCache
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PackingCallerProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open PackingLoaderProgram

def cacheInputs : Code := .seq (saveHigh 10 53) (saveHigh 39 54)

end SubexponentialSAT.SqrtLog.PackingCallerProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingPrefixProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid prefix preparation. Raw unary inputs may contain arbitrary bits;
only their lengths matter. The persistent table and both counters survive. -/

namespace SubexponentialSAT.SqrtLog.PackingPrefixProgram

open SubexponentialSAT BitProgram StructuredCalls
open SubexponentialSAT.Subexp

abbrev normalize (out : Fin 11) : Cmd 3 11 :=
  .call (ProgramLinking.liftProgram PackingHeadProgramPrepareCount.program id (normStack out))

abbrev readPrefix : Cmd 3 11 :=
  .call (ProgramLinking.liftProgram (ArrayUpdatePrograms.readProgram (0 : Fin 3) 1) id readStack)

end SubexponentialSAT.SqrtLog.PackingPrefixProgram

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

abbrev copy (source target : Fin 11) : Cmd 3 11 :=
  .call (StackRoutines.copyProgram source target 7 0 1)

abbrev clear (stack : Fin 11) : Cmd 3 11 := .call (StackRoutines.clearProgram stack 0 1)

end SubexponentialSAT.SqrtLog.PackingPrefixProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingProgramAssemblyHeadSetup
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The native head-stage gate and paid extraction of its prior-word prefix. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram.Assembly
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes

abbrev gate : Cmd 16 48 :=
  liftCommand PackingWeightProgram.Gate.command 0 2 gateRegisters gatePorts

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

abbrev copyAlphabet : Cmd 16 48 := .call (SubexponentialSAT.StackRoutines.copyProgram 30 14 17 0 1)
abbrev resetHead : Cmd 16 48 := SequentialProgram.resetList (List.finRange 16)
abbrev headCandidates : Cmd 16 48 := PackingHeadProgramCandidates.lifted headRegisters headPorts
abbrev headCleanup : Cmd 16 48 := SequentialProgram.clearList [1,2,18]

end SubexponentialSAT.SqrtLog.PackingProgram.Assembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingProgramAssemblyIncidence
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The real incidence scorer with paid parameter parking and restoration. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram.Assembly
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes

abbrev incidence : Cmd 16 48 := .seq park (.seq PackingIncidenceProgram.command unpark)

end SubexponentialSAT.SqrtLog.PackingProgram.Assembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingProgramAssemblyScope
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native-scope specialization of the fixed weighted packing selector. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram.Assembly.Scope
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open SubexponentialSAT.SqrtLog.Packing

def raw (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool) :=
  PackingIncidenceProgram.generatedRawPairs (PackingIncidenceInput.Install.plans scopes n mask)

def cost (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool)
    {r Q : ℕ} (a : Word r Q) (tail : List (Word r Q)) (s : ℕ)
    (nb sb mb rb : List Bool) : ℕ :=
  controllerCost a tail (pairs scopes mask) (List.finRange n)
    (List.finRange (PackingIncidenceInput.Semantics.factorCount scopes mask)) (raw scopes n mask)
    s (PackingIncidenceInput.Semantics.nativeEntries scopes mask).length nb sb mb rb

end SubexponentialSAT.SqrtLog.PackingProgram.Assembly.Scope

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

def prepareLiterals : Code := .seq (TupleProgram.pushConst 43 0 true)
  (TupleProgram.pushConst 44 0 false)
def prepareSuffix : Code := .seq (unaryCommand dimensionPorts)
  (.seq prepareLiterals (copyMany 52 prepareCopies))

end SubexponentialSAT.SqrtLog.PackingCallerProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingIncidenceInputAddress
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The saved native plan stream is exactly the layout's typed word-address
stream, in the native incidence enumeration order. No conversion is required. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput.Address
open SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes

variable {r Q : ℕ}

/-- The physically saved plan bytes are already the layout frontend input. -/
theorem planBytes_eq (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool)
    (hm : mask.length ≤ n) (words : List (Word r Q))
    (hw : words.length = n + Semantics.factorCount scopes mask) :
    ProgramEncoding.encodeRecords
      ((LayoutProgram.labelPlans words (address scopes n mask hm words hw)).map
        PackingVertexLabels.planPayload) =
    ProgramEncoding.encodeRecords
      (PackingIncidenceProgram.planAlphabet (Install.plans scopes n mask)) := by
  rw [labelPlans_eq]
  rfl

end SubexponentialSAT.SqrtLog.PackingIncidenceInput.Address

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingCallerProgramModel
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PackingCallerProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open PackingLoaderProgram PackingIncidenceInput

namespace Problem

def raw (p : Problem) := PackingProgram.Assembly.Scope.raw p.scopes p.n p.mask

end Problem

end SubexponentialSAT.SqrtLog.PackingCallerProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingCallerProgramCore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.allCompatibleDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.compatibleDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.spectatorsAgreeDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.instDecidableAnchorValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! All local computation is now composed: native plans and pairs, actual
word selection, and the native layout metadata suffix. -/
namespace SubexponentialSAT.SqrtLog.PackingCallerProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open PackingLoaderProgram PackingIncidenceInput

def planStore (outside : Store) (p : Problem) :=
  Function.update outside 61 (planBits p.scopes p.n p.mask)
def loadedStore (outside : Store) (p : Problem) :=
  Function.update (planStore outside p) 60 (Scan.scopeBits p.scopes)
def selectedStore (outside : Store) (p : Problem) (a : Word p.r p.Q) (tail : List (Word p.r p.Q)) :=
  Function.update (cached (loadedStore outside p) (List.replicate (p.Q*p.r) true)
    (ProgramEncoding.encodeRecords (AssignmentAlphabetSemantics.wordBytes p.r p.Q)))
      62 ((p.words a tail).map ReadPlan.encodeWord).flatten
noncomputable def outputStore (outside : Store) (p : Problem)
    (a : Word p.r p.Q) (tail : List (Word p.r p.Q)) :=
  Function.update (selectedStore outside p a tail) 63 (p.spec a tail).suffix.metadata

end SubexponentialSAT.SqrtLog.PackingCallerProgram

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

theorem pair_bytes_le {outside : Store} {p : Problem} {S : ℕ} (h : Cap outside p S) :
    (PairScoreProgram.pairRecords p.raw).length ≤ pairEnvelope S := by
  have hp := Finished.output_bits_le p.scopes p.n p.mask p.mask_le
  change (PairScoreProgram.pairRecords p.raw).length ≤
    1+(32*(p.n+p.factors+1)+14)*p.incidences^2 at hp
  apply hp.trans
  unfold pairEnvelope
  have hn : p.n+p.factors ≤ 2*S := by have := h.n; have := h.factors; omega
  gcongr ; exact h.incidences

theorem alphabet_bytes_le {outside : Store} {p : Problem} {S : ℕ} (h : Cap outside p S) :
    (ProgramEncoding.encodeRecords (AssignmentAlphabetSemantics.wordBytes p.r p.Q)).length ≤
      alphabetEnvelope S := by
  have ha := ProgramEncoding.encodeRecords_length_le (AssignmentAlphabetSemantics.wordBytes p.r p.Q)
    (p.Q*p.r) (fun row hm => (AssignmentAlphabetSemantics.wordBytes_width p.hr row hm).le)
  rw [AssignmentAlphabetSemantics.wordBytes_length] at ha
  apply ha.trans
  unfold alphabetEnvelope
  have hw := width_le h
  gcongr ; exact h.alphabet

theorem raw_length (p : Problem) : p.raw.length=p.incidences^2 := by
  simp [Problem.raw,PackingProgram.Assembly.Scope.raw,PackingIncidenceProgram.generatedRawPairs_length,
    Install.plans,Semantics.plans_eq,Semantics.nativeEntries,Problem.incidences,pow_two]

end SubexponentialSAT.SqrtLog.PackingCallerProgram.Bounds

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingCallerProgramBoundsSelection
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PackingCallerProgram.Bounds
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open PackingLoaderProgram PackingIncidenceInput

theorem controller_le {outside : Store} {p : Problem} {S : ℕ} (h : Cap outside p S)
    (a : Word p.r p.Q) (tail : List (Word p.r p.Q))
    (hrows : (a::tail).map ReadPlan.encodeWord=AssignmentAlphabetSemantics.wordBytes p.r p.Q) :
    PackingProgram.Assembly.Scope.cost p.scopes p.n p.mask a tail p.s
      (outside 56) (outside 57) (outside 58) (outside 59) ≤ controllerEnvelope S := by
  have ha : (a::tail).length=p.r^p.Q := by
    have hh := congrArg List.length hrows
    simpa only [List.length_map,AssignmentAlphabetSemantics.wordBytes_length] using hh
  have hn : p.n+p.factors ≤ 2*S := by have := h.n; have := h.factors; omega
  have hw := width_le h
  have hparam : (outside 56).length+(outside 57).length+(outside 58).length+(outside 59).length ≤ 4*S := by
    have := h.l56; have := h.l57; have := h.l58; have := h.l59; omega
  unfold PackingProgram.Assembly.Scope.cost PackingProgram.Assembly.controllerCost
  simp only [Packing.headsFirst_length,List.length_finRange]
  change (p.n+p.factors)*(PackingProgram.Assembly.uniformBudget (p.n+p.factors)
    (PackingProgram.Assembly.Scope.pairs p.scopes p.mask).length p.raw.length (a::tail).length
    (p.Q*p.r) p.n (PackingProgram.Assembly.magnitude p.n p.s p.incidences p.r)
    (PackingProgram.Assembly.parameterBits (outside 56) (outside 57) (outside 58) (outside 59))+
    SequentialProgram.selectionBudget (a::tail).length
      (PackingProgram.Assembly.scoreBound (a::tail)
        (PackingProgram.Assembly.Scope.pairs p.scopes p.mask)
        (Packing.headsFirstIndices (List.finRange p.n) (List.finRange p.factors)) p.n p.s p.incidences)
      (p.n+p.factors) (ReadPlan.encodeWord a).length+3)+3 ≤ _
  simp only [ha,raw_length,pairs_length,ReadPlan.encodeWord_length,ReadPlan.wordWidth,
    PackingProgram.Assembly.scoreBound,Packing.headsFirst_length,List.length_finRange]
  unfold controllerEnvelope scoreEnvelope PackingProgram.Assembly.magnitude
    PackingProgram.Assembly.parameterBits PackingProgram.Assembly.uniformBudget
    PackingProgram.Assembly.headBudgetBound SequentialProgram.selectionBudget
    SequentialProgram.minimumBudget SequentialProgram.recordBudget SequentialProgram.updateBudget
  dsimp only
  gcongr <;> first | exact hn | exact hw | exact hparam | exact h.n | exact h.s | exact h.r | exact h.incidences | exact h.alphabet

end SubexponentialSAT.SqrtLog.PackingCallerProgram.Bounds

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingCallerProgramWide
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The caller's private64-stack workspace lies after the live native
parameter bank340..416, which must survive until ring setup. -/
namespace SubexponentialSAT.SqrtLog.PackingCallerProgram.Wide
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
abbrev Code := Cmd 40 768

abbrev call (c : Cmd 16 768) : Code := .call
  (ProgramLinking.liftProgram (compiled c 684 133) registers id)

abbrev bankCall {L : ℕ} (p : Program 16 64 L) : Code :=
  .call (ProgramLinking.liftProgram p registers ports)

end SubexponentialSAT.SqrtLog.PackingCallerProgram.Wide

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingCallerProgramExport
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
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

abbrev exportLocal : Cmd 16 768 := .seq (copyMany 684 exportPairs) (clearMany privatePorts)

abbrev finishLocal : Cmd 16 768 := .seq exportLocal LeafProgram.LayoutMasters.parkLocal

def finish : Code := call finishLocal

end SubexponentialSAT.SqrtLog.PackingCallerProgram.Wide

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingCallerProgramStage
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
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

abbrev stageLocal : Cmd 16 768 := copyMany 684 stagePairs

def stage : Code := call stageLocal

end SubexponentialSAT.SqrtLog.PackingCallerProgram.Wide

end OAI.Algorithms
end


