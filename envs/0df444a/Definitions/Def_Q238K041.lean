-- Prove2me | Definitions.Def_Q238K041
-- name    : Q238K041
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T23:43:18.603454+00:00
-- url     : https://prove2.me/theorems/5552242c-e0f6-495f-8bce-192e484bac2d
-- title:
--   Definitions bundle Q238K041 of the split of OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 101 declarations of OpenAI's Lean: 101 definitions. The definitions and types are `OAI.MetricKMedianRecovery.BitMachine.BinaryAssignmentWeight.count_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryAssignmentWeight.identities_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryAssignmentWeight.identity_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryAssignmentWeight.run_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBisection.fuel_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBisection.input_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBisection.run_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueBlocks.atCall_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueBlocks.at_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueBlocks.itemCall_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueBlocks.run_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueCell.block_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueCell.ctx_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueCell.old_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueCell.op_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueCell.run_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueCell.whole_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueItem.op_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueItem.price_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueItem.response_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueItem.run_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueItem.sourceL_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueItem.sourceR_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueItem.targetL_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueLookup.matchKey_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueLookup.run_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueLoop.initial_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueLoop.loop_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueLoop.newBest_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueLoop.newTable_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueLoop.nextCtx_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueLoop.oldBest_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueLoop.oldTable_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueLoop.run_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueLoop.step_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueOutput.destination_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueOutput.matching_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueOutput.pick_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueOutput.prepared_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueOutput.query_computes` and 61 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedianRecovery_Branching_BlueBlocksMachine`, `KMedianRecovery_Branching_BlueItem`, `KMedianRecovery_Branching_BlueLookup`, `KMedianRecovery_Branching_BlueNextTable`, `KMedianRecovery_Branching_BlueProgram`, `KMedianRecovery_Branching_BlueTable`, `KMedianRecovery_Branching_BlueTableSize`, `KMedianRecovery_Branching_BranchBalls`, `KMedianRecovery_Branching_BranchContext`, `KMedianRecovery_Branching_BranchPhysical`, `KMedianRecovery_Branching_BranchWeights`, `KMedianRecovery_Branching_RationalSurrogate`, `KMedianRecovery_Encoding_ColorLabelMachine`, `KMedianRecovery_Encoding_RationalSort`, `KMedianRecovery_Encoding_WordExtras`, `KMedianRecovery_Machines_BisectionMachine`, `KMedianRecovery_Recovery_ClassFilter`, `KMedianRecovery_Sampling_SamplerUpdateParts`, `KMedianRecovery_Sampling_SamplingReference`, `KMedianRecovery_Sampling_SamplingStateMachine`.
--
--   **Imports.** It imports the published bundle `Def_KMedianRefinedRecovery`; the bundles `Q238K039` and `Q238K040` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q238K048`, `Q238K049` and `Q238K050`.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_KMedianRefinedRecovery
import Definitions.Def_Q238K039
import Definitions.Def_Q238K040

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_WordExtras
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace WordEq
noncomputable def eq_computes : PolyComputes (fun x=>[eq x]) := by
  have h:= (NatOps.eq extractPrefix_computes discardPrefix_computes).and
    (NatOps.eq (extractPrefix_computes.comp UnaryResources.lengthBits_computes)
      (discardPrefix_computes.comp UnaryResources.lengthBits_computes))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  simp only [eq,Function.comp_apply,UnaryResources.lengthBits_eq,value_bits,←Bool.decide_and]
  congr 1
  apply decide_eq_decide.mpr
  constructor
  · intro he; rw [he]; exact ⟨rfl,rfl⟩
  · intro he; exact value_length_injective he.2 he.1
end WordEq
namespace WordList
noncomputable def lengthBits_computes : PolyComputes lengthBits := Count.run_computes.comp UnaryResources.lengthBits_computes
end WordList
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_RationalSort
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRationalSort
open WordOperations WordList BinaryArithmetic

noncomputable def lt_computes : PolyComputes (fun x=>[lt x]) :=
  (RatOps.lt (RatOps.ofWords (extractPrefix_computes.comp extractPrefix_computes))
    (RatOps.ofWords (discardPrefix_computes.comp extractPrefix_computes))).or
  ((RatOps.eq (RatOps.ofWords (extractPrefix_computes.comp extractPrefix_computes))
    (RatOps.ofWords (discardPrefix_computes.comp extractPrefix_computes))).and
  (NatOps.lt (extractPrefix_computes.comp discardPrefix_computes) (discardPrefix_computes.comp discardPrefix_computes)))
noncomputable def sort_computes : PolyComputes sort := Sort.run_computes lt_computes
attribute [local irreducible] sort ranked Take.run
end MetricKMedianRecovery.BitMachine.BinaryRationalSort

namespace MetricKMedianRecovery.BitMachine.BinaryNatSet
open WordOperations WordList BinaryArithmetic
noncomputable def lt_computes : PolyComputes (fun x=>[lt x]) := NatOps.lt extractPrefix_computes discardPrefix_computes
noncomputable def sort_computes : PolyComputes sort := Sort.run_computes lt_computes
noncomputable def contains_computes : PolyComputes (fun x=>[contains x]) := BinaryPhaseFirst.contains_computes
noncomputable def absent_computes : PolyComputes (fun x=>[absent x]) :=
  ((discardPrefix_computes.pair extractPrefix_computes).comp contains_computes).not
noncomputable def diff_computes : PolyComputes diff :=
  ((discardPrefix_computes.pair extractPrefix_computes).comp (filterWith_computes absent_computes)).comp sort_computes
end MetricKMedianRecovery.BitMachine.BinaryNatSet

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_ColorLabelMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRationalMinKey
open WordOperations WordList
open BinaryRationalSort (entryBits)
noncomputable def run_computes : PolyComputes run := BinaryRationalSort.sort_computes.comp WordList.head_computes
end MetricKMedianRecovery.BitMachine.BinaryRationalMinKey

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_SamplingReference
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySamplingReference
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
open BinaryRationalSort (entryBits)
attribute [local irreducible] WordList.mapWith
variable {n l : ℕ}
noncomputable def original_computes : PolyComputes original :=
  ((discardPrefix_computes.pair extractPrefix_computes).comp Lookup.run_computes).pair discardPrefix_computes
noncomputable def originals_computes : PolyComputes originals :=
  ((field_computes 4).pair (field_computes 2)).comp (mapWith_computes original_computes)
noncomputable def leaf_computes : PolyComputes leaf := by
  have hn : PolyComputes (fun x=>(value (extractPrefix (extractPrefix x))+value (extractPrefix (discardPrefix x))+1).bits) := by
    simpa only [Function.comp_def,value_bits] using
      (NatOps.add (NatOps.add (extractPrefix_computes.comp extractPrefix_computes)
        (discardPrefix_computes.comp extractPrefix_computes)) (const_computes (1:ℕ).bits))
  exact (RatOps.add (RatOps.ofWords (((discardPrefix_computes.comp discardPrefix_computes).comp extractPrefix_computes).pair
      (extractPrefix_computes.comp discardPrefix_computes) |>.comp Lookup.run_computes))
    (RatOps.ofWords ((discardPrefix_computes.comp discardPrefix_computes).comp discardPrefix_computes))).pair hn
noncomputable def leaves_computes : PolyComputes leaves :=
  (((field_computes 0).pair (field_computes 4)).pair
    ((((field_computes 3).comp Indices.run_computes).pair (field_computes 3)).comp Zip.run_computes)).comp (mapWith_computes leaf_computes)
noncomputable def entries_computes : PolyComputes entries :=
  originals_computes.append (cons_computes ((field_computes 1).pair (field_computes 0)) leaves_computes)
noncomputable def run_computes : PolyComputes run := entries_computes.comp BinaryRationalMinKey.run_computes
end MetricKMedianRecovery.BitMachine.BinarySamplingReference

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_SamplingStateMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySamplingState
open WordOperations WordList BinaryArithmetic RationalSampling
open BinaryOpeningPayment (field field_computes field_encode)
variable {n : ℕ}
noncomputable def referenceInput_computes : PolyComputes referenceInput :=
  extractPrefix_computes.append (cons_computes discardPrefix_computes (const_computes []))
noncomputable def reference_computes : PolyComputes reference := referenceInput_computes.comp BinarySamplingReference.run_computes
end MetricKMedianRecovery.BitMachine.BinarySamplingState

namespace MetricKMedianRecovery.BitMachine.BinarySamplingOracle
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
variable {n : ℕ}
noncomputable def row_computes : PolyComputes row :=
  (discardPrefix_computes.pair (extractPrefix_computes.comp (field_computes 0))).comp Lookup.run_computes
noncomputable def reference_computes : PolyComputes reference :=
  ((extractPrefix_computes.comp (field_computes 2)).pair row_computes).comp BinarySamplingState.reference_computes
end MetricKMedianRecovery.BitMachine.BinarySamplingOracle

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BranchWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryAssignmentWeight
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
variable {n : ℕ}
noncomputable def identity_computes : PolyComputes identity := BinarySamplingOracle.reference_computes.comp discardPrefix_computes
noncomputable def identities_computes : PolyComputes identities := by
  have identitiesComputes := (id_computes.pair (field_computes 1)).comp (mapWith_computes identity_computes)
  unfold identities
  simpa only [Function.comp_def,id_eq] using identitiesComputes
noncomputable def count_computes : PolyComputes count := (filterWith_computes WordEq.eq_computes).comp Count.run_computes
noncomputable def run_computes : PolyComputes run := by
  change PolyComputes (fun x=>BinaryRational.encode ((count x).length:ℚ))
  simpa only [Function.comp_apply,UnaryResources.lengthBits_eq,value_bits] using RatOps.nat (count_computes.comp UnaryResources.lengthBits_computes)
end MetricKMedianRecovery.BitMachine.BinaryAssignmentWeight

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BlueItem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBlueItem
open WordOperations WordList
variable {L R : Type*} [LinearOrder R] [LinearOrder L] {n : ℕ}
noncomputable def targetL_computes : PolyComputes targetL := extractPrefix_computes.comp extractPrefix_computes
noncomputable def sourceR_computes : PolyComputes sourceR := discardPrefix_computes.comp extractPrefix_computes
noncomputable def sourceL_computes : PolyComputes sourceL := (discardPrefix_computes.comp discardPrefix_computes).comp extractPrefix_computes
noncomputable def price_computes : PolyComputes price := (targetY_computes.pair sourceRow_computes).comp Lookup.run_computes
noncomputable def response_computes : PolyComputes response :=
  cons_computes (price_computes.pair (cons_computes (targetL_computes.pair (sourceR_computes.pair targetY_computes)) (const_computes []))) (const_computes [])
noncomputable def op_computes : PolyComputes op :=
  ((sourceL_computes.pair targetL_computes).comp WordEq.eq_computes).cond response_computes (const_computes [])
noncomputable def run_computes : PolyComputes run := (mapWith_computes op_computes).comp BinaryBlueChoice.select_computes
end MetricKMedianRecovery.BitMachine.BinaryBlueItem

namespace MetricKMedianRecovery.BitMachine.BinaryBlueRecords
open WordOperations WordList
open BinaryOpeningPayment (field field_computes field_encode)
variable {n m : ℕ}
noncomputable def oracleInput_computes : PolyComputes oracleInput :=
  (extractPrefix_computes.comp (field_computes 0)).pair discardPrefix_computes
noncomputable def row_computes : PolyComputes row := by
  unfold row
  have computes := oracleInput_computes.comp BinarySamplingOracle.row_computes
  simpa only [Function.comp_def] using computes
noncomputable def weight_computes : PolyComputes weight := by
  unfold weight
  have computes := (discardPrefix_computes.pair ((extractPrefix_computes.comp (field_computes 0)).comp BinaryAssignmentWeight.identities_computes)).comp
    BinaryAssignmentWeight.run_computes
  simpa only [Function.comp_def] using computes
noncomputable def scaled_computes : PolyComputes scaled := by
  unfold scaled
  have computes := (weight_computes.pair row_computes).comp RationalMatrix.vectorScale_computes
  simpa only [Function.comp_def] using computes
noncomputable def tag_computes : PolyComputes tag :=
  (discardPrefix_computes.pair (extractPrefix_computes.comp (field_computes 2))).comp Lookup.run_computes
noncomputable def op_computes : PolyComputes op := discardPrefix_computes.pair (tag_computes.pair scaled_computes)
noncomputable def run_computes : PolyComputes run := by
  unfold run
  have computes := (id_computes.pair (field_computes 1)).comp (mapWith_computes op_computes)
  simpa only [Function.comp_def,id_eq] using computes
end MetricKMedianRecovery.BitMachine.BinaryBlueRecords

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BlueBlocksMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBlueBlocks
open WordOperations WordList
variable {L R : Type*} [LinearOrder L] [LinearOrder R] {n : ℕ}
noncomputable def itemCall_computes : PolyComputes itemCall :=
  ((discardPrefix_computes.pair (extractPrefix_computes.comp discardPrefix_computes)).pair
    (extractPrefix_computes.comp extractPrefix_computes)).comp BinaryBlueItem.run_computes
noncomputable def at_computes : PolyComputes atCenter := (mapWith_computes itemCall_computes).comp BinaryBlueCollect.run_computes
noncomputable def atCall_computes : PolyComputes atCall :=
  (((extractPrefix_computes.comp extractPrefix_computes).pair discardPrefix_computes).pair
    (extractPrefix_computes.comp discardPrefix_computes)).comp at_computes
noncomputable def run_computes : PolyComputes run := (mapWith_computes atCall_computes).comp BinaryBlueChoice.select_computes
end MetricKMedianRecovery.BitMachine.BinaryBlueBlocks

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BlueTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBlueStates
open WordOperations WordList
variable {n : ℕ}
noncomputable def run_computes (d : ℕ) : PolyComputes (run d) := Subsets.run_computes d
noncomputable def nonemptyKey_computes : PolyComputes (fun x=>[nonemptyKey x]) := by
  simpa only [nonemptyKey,beq_iff_eq] using (discardPrefix_computes.comp isEmpty_computes).not
noncomputable def blocks_computes (d : ℕ) : PolyComputes (blocks d) :=
  ((const_computes []).pair (run_computes d)).comp (filterWith_computes nonemptyKey_computes)
end MetricKMedianRecovery.BitMachine.BinaryBlueStates

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BlueLookup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBlueLookup
open WordOperations WordList
variable {L A : Type*} [LinearOrder L]
noncomputable def matchKey_computes : PolyComputes (fun x=>[matchKey x]) :=
  (extractPrefix_computes.pair (discardPrefix_computes.comp extractPrefix_computes)).comp WordEq.eq_computes
noncomputable def run_computes : PolyComputes run := ((Find.run_computes matchKey_computes).comp WordOperations.tail_computes).comp discardPrefix_computes
end MetricKMedianRecovery.BitMachine.BinaryBlueLookup

namespace MetricKMedianRecovery.BitMachine.BinaryBlueCell
open WordOperations WordList
open BinaryOpeningPayment (field field_computes field_encode)
variable {n m : ℕ} {R : Type*} [LinearOrder R]
noncomputable def ctx_computes : PolyComputes ctx := extractPrefix_computes.comp extractPrefix_computes
noncomputable def whole_computes : PolyComputes whole := extractPrefix_computes.comp discardPrefix_computes
noncomputable def block_computes : PolyComputes block :=
  (((ctx_computes.comp (field_computes 0)).pair discardPrefix_computes).pair
    (ctx_computes.comp (field_computes 1))).comp BinaryBlueBlocks.run_computes
noncomputable def old_computes : PolyComputes old :=
  (((whole_computes.pair discardPrefix_computes).comp BinaryNatSet.diff_computes).pair
    (ctx_computes.comp (field_computes 3))).comp BinaryBlueLookup.run_computes
noncomputable def op_computes : PolyComputes op := by
  unfold op
  have computes := (block_computes.pair old_computes).comp BinaryBlueMerge.run_computes
  simpa only [Function.comp_def] using computes
noncomputable def run_computes : PolyComputes run := by
  unfold run
  have computes := ((id_computes.pair (BinaryBlueStates.blocks_computes 3)).comp (mapWith_computes op_computes)).comp BinaryBlueChoice.select_computes
  simpa only [Function.comp_def,id_eq] using computes
end MetricKMedianRecovery.BitMachine.BinaryBlueCell

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BlueNextTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBlueTable
open WordOperations WordList
open BinaryOpeningPayment (field field_computes field_encode)
variable {n m : ℕ} {R : Type*} [LinearOrder R]
noncomputable def row_computes : PolyComputes row := discardPrefix_computes.pair BinaryBlueCell.run_computes
noncomputable def next_computes : PolyComputes next := by
  unfold next
  have computes := (id_computes.pair (field_computes 2)).comp (mapWith_computes row_computes)
  simpa only [Function.comp_def,id_eq] using computes
noncomputable def initRow_computes : PolyComputes initRow := by
  unfold initRow
  simpa only [decide_eq_true_eq] using discardPrefix_computes.pair ((discardPrefix_computes.comp isEmpty_computes).cond
    (const_computes (BinaryBlueChoice.encode id (some (0,[])))) (const_computes []))
noncomputable def initial_computes : PolyComputes initial := by
  unfold initial
  have computes := ((const_computes []).pair id_computes).comp (mapWith_computes initRow_computes)
  simpa only [Function.comp_def,id_eq] using computes
end MetricKMedianRecovery.BitMachine.BinaryBlueTable

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BlueTableSize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBlueLoop
open WordOperations WordList
open BinaryOpeningPayment (field field_computes field_encode)
variable {n m : ℕ} {R : Type*} [LinearOrder R]
noncomputable def oldTable_computes : PolyComputes oldTable := discardPrefix_computes.comp extractPrefix_computes
noncomputable def oldBest_computes : PolyComputes oldBest := discardPrefix_computes.comp discardPrefix_computes
noncomputable def nextCtx_computes : PolyComputes nextCtx :=
  cons_computes (extractPrefix_computes.comp (field_computes 0)) (cons_computes (extractPrefix_computes.comp (field_computes 1))
    (cons_computes (extractPrefix_computes.comp (field_computes 2)) (cons_computes oldTable_computes (const_computes []))))
noncomputable def newTable_computes : PolyComputes newTable := by
  unfold newTable
  have computes := nextCtx_computes.comp BinaryBlueTable.next_computes
  simpa only [Function.comp_def] using computes
noncomputable def newBest_computes : PolyComputes newBest :=
  (oldBest_computes.pair (((extractPrefix_computes.comp (field_computes 3)).pair newTable_computes).comp BinaryBlueLookup.run_computes)).comp
    BinaryBlueChoice.run_computes
noncomputable def step_computes : PolyComputes step := extractPrefix_computes.pair (newTable_computes.pair newBest_computes)
noncomputable def initial_computes : PolyComputes initial := by
  unfold initial
  have computes := id_computes.pair (((field_computes 2).comp BinaryBlueTable.initial_computes).pair (const_computes []))
  simpa only [Function.comp_def,id_eq] using computes
noncomputable def loop_computes : PolyComputes loop :=
  ((field_computes 4).pair (cap.computes.pair initial_computes)).comp (BoundedIteration.run_computes step_computes)
noncomputable def run_computes : PolyComputes run := by
  unfold run
  simpa only [decide_eq_true_eq,Function.comp_def] using ((field_computes 3).comp isEmpty_computes).cond
    (const_computes (BinaryBlueChoice.encode id (some (0,[])))) (loop_computes.comp oldBest_computes)
end MetricKMedianRecovery.BitMachine.BinaryBlueLoop

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BlueProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBlueProgram
open WordOperations WordList
open BinaryOpeningPayment (field field_computes field_encode)
variable {n m : ℕ} {R : Type*} [LinearOrder R]
noncomputable def states_computes (d : ℕ) : PolyComputes (states d) :=
  (id_computes.pair (field_computes 2)).comp (BinaryBlueStates.run_computes d)
noncomputable def prepare_computes (d : ℕ) : PolyComputes (prepare d) :=
  cons_computes (field_computes 0) (cons_computes (field_computes 1) (cons_computes (states_computes d)
    (cons_computes (field_computes 2) (cons_computes (field_computes 3) (const_computes [])))))
noncomputable def run_computes (d : ℕ) : PolyComputes (run d) := (prepare_computes d).comp BinaryBlueLoop.run_computes
end MetricKMedianRecovery.BitMachine.BinaryBlueProgram

namespace MetricKMedianRecovery.BitMachine.BinaryBlueOutput
open WordOperations WordList
open BinaryOpeningPayment (field field_computes field_encode)
variable {m n r : ℕ}
noncomputable def matching_computes : PolyComputes (fun x=>[matching x]) :=
  ((discardPrefix_computes.comp extractPrefix_computes).pair extractPrefix_computes).comp WordEq.eq_computes
noncomputable def pick_computes : PolyComputes pick := (filterWith_computes matching_computes).comp WordList.head_computes
noncomputable def query_computes : PolyComputes query := discardPrefix_computes.pair extractPrefix_computes
noncomputable def source_computes : PolyComputes source :=
  ((query_computes.comp pick_computes).comp discardPrefix_computes).comp extractPrefix_computes
noncomputable def destination_computes : PolyComputes destination :=
  ((query_computes.comp pick_computes).comp discardPrefix_computes).comp discardPrefix_computes
noncomputable def prepared_computes : PolyComputes prepared :=
  (extractPrefix_computes.comp BinaryBlueMerge.payload_computes).pair discardPrefix_computes
noncomputable def run_computes : PolyComputes run := by
  unfold run
  have computes := cons_computes (prepared_computes.comp (mapWith_computes source_computes))
    (cons_computes (prepared_computes.comp (mapWith_computes destination_computes)) (const_computes []))
  simpa only [Function.comp_def,encode] using computes
end MetricKMedianRecovery.BitMachine.BinaryBlueOutput

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_SamplerUpdateParts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySampler.Update
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
open Weights (actionField )
attribute [local irreducible] BinaryMenu.radius WordList.filterWith Client.row
variable {n : ℕ}
noncomputable def within_computes : PolyComputes (fun x=>[within x]) :=
  RatOps.le (RatOps.ofWords ((discardPrefix_computes.pair (extractPrefix_computes.comp extractPrefix_computes)).comp Lookup.run_computes))
    (RatOps.ofWords (extractPrefix_computes.comp discardPrefix_computes))
end MetricKMedianRecovery.BitMachine.BinarySampler.Update

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BranchBalls
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBranchBalls
open WordOperations WordList
open BinaryOpeningPayment (field field_computes field_encode)
variable {n a : ℕ}
noncomputable def row_computes : PolyComputes row :=
  ((discardPrefix_computes.comp extractPrefix_computes).pair (extractPrefix_computes.comp (field_computes 0))).comp Lookup.run_computes
noncomputable def input_computes : PolyComputes input :=
  (row_computes.pair (discardPrefix_computes.comp discardPrefix_computes)).pair (extractPrefix_computes.comp (field_computes 1))
noncomputable def ball_computes : PolyComputes ball := input_computes.comp (filterWith_computes BinarySampler.Update.within_computes)
noncomputable def balls_computes : PolyComputes balls := by
  have ballsComputes := (id_computes.pair (field_computes 2)).comp (mapWith_computes ball_computes)
  unfold balls
  simpa only [Function.comp_def, id_eq] using ballsComputes
noncomputable def run_computes : PolyComputes run := cons_computes ((field_computes 0).comp Count.run_computes)
  (cons_computes balls_computes (const_computes []))
end MetricKMedianRecovery.BitMachine.BinaryBranchBalls

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_ClassFilter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryClassFilter
open WordOperations WordList
open BinaryOpeningPayment (field field_computes field_encode)
variable {n m : ℕ}
noncomputable def tag_computes : PolyComputes tag :=
  (discardPrefix_computes.pair (extractPrefix_computes.comp extractPrefix_computes)).comp Lookup.run_computes
noncomputable def matching_computes : PolyComputes (fun x=>[matching x]) :=
  (tag_computes.pair (extractPrefix_computes.comp discardPrefix_computes)).comp WordEq.eq_computes
noncomputable def run_computes : PolyComputes run := filterWith_computes matching_computes
end MetricKMedianRecovery.BitMachine.BinaryClassFilter

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BranchContext
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBranchContext
open WordOperations WordList
open BinaryOpeningPayment (field field_computes field_encode)
variable {n m : ℕ}
noncomputable def remaining_computes : PolyComputes remaining :=
  ((field_computes 3).pair ((field_computes 5).comp extractPrefix_computes)).comp BinaryNatSet.diff_computes
attribute [local irreducible] remaining
attribute [local irreducible] context
attribute [local irreducible] oracle
noncomputable def classOf_computes (j : ℕ) : PolyComputes (classOf j) :=
  (((field_computes 6).pair (const_computes j.bits)).pair remaining_computes).comp BinaryClassFilter.run_computes
attribute [local irreducible] classOf
attribute [local irreducible] greenContext
attribute [local irreducible] greenOracle
noncomputable def ballInput_computes : PolyComputes ballInput :=
  (cons_computes (field_computes 0) (cons_computes (field_computes 2) (cons_computes ((field_computes 5).comp discardPrefix_computes) (const_computes []))))
attribute [local irreducible] ballInput
noncomputable def copyData_computes : PolyComputes copyData :=
  ballInput_computes.comp BinaryBranchBalls.run_computes
attribute [local irreducible] copyData
attribute [local irreducible] parts
attribute [local irreducible] origins
attribute [local irreducible] locations
end MetricKMedianRecovery.BitMachine.BinaryBranchContext

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_RationalSurrogate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBranchRows
open WordOperations WordList
open BinaryOpeningPayment (field field_computes field_encode)
variable {n q r : ℕ}
noncomputable def oracleInput_computes (j : ℕ) : PolyComputes (oracleInput j) :=
  (extractPrefix_computes.comp (field_computes j)).pair discardPrefix_computes
end MetricKMedianRecovery.BitMachine.BinaryBranchRows

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BranchPhysical
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBranchCheck
open WordOperations WordList BinaryArithmetic BinaryBranchContext
open BinaryOpeningPayment (field field_computes field_encode)
variable {n m : ℕ}
noncomputable def outside_computes : PolyComputes outside :=
  (((field_computes 5).comp extractPrefix_computes).pair (field_computes 3)).comp BinaryNatSet.diff_computes
noncomputable def badBall_computes : PolyComputes (fun x=>[badBall x]) := discardPrefix_computes.comp isEmpty_computes
noncomputable def badBalls_computes : PolyComputes badBalls :=
  ((const_computes []).pair (copyData_computes.comp (field_computes 1))).comp (filterWith_computes badBall_computes)
noncomputable def badRadius_computes : PolyComputes (fun x=>[badRadius x]) :=
  RatOps.lt (RatOps.ofWords (discardPrefix_computes.comp discardPrefix_computes)) (RatOps.const 0)
noncomputable def badRadii_computes : PolyComputes badRadii :=
  ((const_computes []).pair ((field_computes 5).comp discardPrefix_computes)).comp (filterWith_computes badRadius_computes)
noncomputable def lhs_computes : PolyComputes lhs := by
  unfold lhs
  simpa only [lhs,Function.comp_def,UnaryResources.lengthBits_eq,value_bits] using NatOps.add (((field_computes 5).comp discardPrefix_computes).comp lengthBits_computes)
    ((field_computes 10).comp UnaryResources.lengthBits_computes)
noncomputable def rhs_computes : PolyComputes rhs := by
  unfold rhs
  simpa only [rhs,Function.comp_def,value_bits] using NatOps.add (NatOps.add (((field_computes 5).comp extractPrefix_computes).comp lengthBits_computes) (field_computes 9))
    ((field_computes 8).comp lengthBits_computes)
noncomputable def run_computes : PolyComputes (fun x=>[run x]) := by
  simpa only [run,Bool.decide_and,Function.comp_def] using
    (outside_computes.comp isEmpty_computes).and ((badBalls_computes.comp isEmpty_computes).and
      ((badRadii_computes.comp isEmpty_computes).and ((NatOps.le (field_computes 9) ((classOf_computes 1).comp lengthBits_computes)).and
        (NatOps.le lhs_computes rhs_computes))))
end MetricKMedianRecovery.BitMachine.BinaryBranchCheck

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_BisectionMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBisection
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
noncomputable def fuel_computes : PolyComputes fuel := (field_computes 0).append (widthCeil_computes.comp logWord_computes)
noncomputable def input_computes : PolyComputes input := fuel_computes.pair context_computes
noncomputable def run_computes {query : List Bool→List Bool} (hq : PolyComputes query) : PolyComputes (run query) :=
  input_computes.comp (BinaryGrid.run_computes hq)
end MetricKMedianRecovery.BitMachine.BinaryBisection

end OAI
end


