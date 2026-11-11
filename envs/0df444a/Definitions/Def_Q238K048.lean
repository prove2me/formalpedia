-- Prove2me | Definitions.Def_Q238K048
-- name    : Q238K048
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T23:48:39.004618+00:00
-- url     : https://prove2.me/theorems/bf2a2e81-158a-4195-932c-dbd169873c44
-- title:
--   Definitions bundle Q238K048 of the split of OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 79 declarations of OpenAI's Lean: 79 definitions. The definitions and types are `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchContext.context_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchContext.greenContext_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchContext.greenOracle_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchContext.locations_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchContext.oracle_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchContext.origins_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchContext.parts_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.best_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.blueInput_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.bluePack_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.completion_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.plan_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.records_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.rowInput_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.rows_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.run_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchRandomize.blog_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchRandomize.colors_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchRandomize.labels_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchRandomize.lraw_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchRandomize.lshape_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchRandomize.lsize_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchRandomize.tailBits_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchRows.base_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchRows.capRow_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchRows.clients_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchRows.distances_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchRows.redRow_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchRows.reds_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchRows.row_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchRows.run_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchRows.weight_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchTape.Count.bword_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchTape.Count.cut_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchTape.Count.dimensions_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchTape.Count.leftShape_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchTape.Count.lword_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchTape.Count.qword_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchTape.Count.rightShape_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchTape.Count.run_computes` and 39 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedianRecovery_Algorithms_CandidateSanitize`, `KMedianRecovery_Algorithms_CompletionAlgorithm`, `KMedianRecovery_Branching_BranchContext`, `KMedianRecovery_Branching_BranchSeedLayout`, `KMedianRecovery_Branching_CompletionFair`, `KMedianRecovery_Branching_CompletionFillMath`, `KMedianRecovery_Branching_CompletionRealize`, `KMedianRecovery_Branching_CopyGround`, `KMedianRecovery_Branching_RandomizedZeroBranch`, `KMedianRecovery_Branching_RationalSurrogate`, `KMedianRecovery_Encoding_ColorLabelMachine`, `KMedianRecovery_Encoding_FinSets`, `KMedianRecovery_Encoding_RationalBottomIndices`, `KMedianRecovery_Encoding_RationalSort`, `KMedianRecovery_Encoding_WordTake`, `KMedianRecovery_Recovery_CrossCount`, `KMedianRecovery_Recovery_FinImages`, `KMedianRecovery_Recovery_PlanResult`.
--
--   **Imports.** It imports the published bundle `Def_KMedianRefinedRecovery`; the bundles `Q238K041`, `Q238K042`, `Q238K043` and `Q238K044` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q238K051` and `Q238K052`; the statement `OAI_MetricKMedianRecovery_BitMachine_BinaryPhaseRun_run_bound_invariant_s238`; the proof of `OAI_MetricKMedianRecovery_BitMachine_BinaryPhaseRun_run_bound_invariant_s238`.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_KMedianRefinedRecovery
import Definitions.Def_Q238K041
import Definitions.Def_Q238K042
import Definitions.Def_Q238K043
import Definitions.Def_Q238K044

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_WordTake
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.WordList.Take
open WordOperations BinaryArithmetic
noncomputable def number_computes : PolyComputes number :=
  NatOps.sub (discardPrefix_computes.comp lengthBits_computes) extractPrefix_computes
attribute [local irreducible] number reverse Drop.run
noncomputable def run_computes : PolyComputes run :=
  ((number_computes.pair (discardPrefix_computes.comp reverse_computes)).comp Drop.run_computes).comp reverse_computes
end MetricKMedianRecovery.BitMachine.WordList.Take

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_RationalSort
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRationalSort
open WordOperations WordList BinaryArithmetic

attribute [local irreducible] sort ranked Take.run
noncomputable def bottom_computes : PolyComputes bottom :=
  (extractPrefix_computes.pair ((discardPrefix_computes.comp ranked_computes).comp sort_computes)).comp Take.run_computes
end MetricKMedianRecovery.BitMachine.BinaryRationalSort

namespace MetricKMedianRecovery.BitMachine.BinaryNatSet
open WordOperations WordList BinaryArithmetic
noncomputable def union_computes : PolyComputes union := (extractPrefix_computes.append discardPrefix_computes).comp sort_computes
end MetricKMedianRecovery.BitMachine.BinaryNatSet

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CompletionFillMath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCompletionPad
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
noncomputable def need_computes : PolyComputes need := NatOps.sub (field_computes 2) ((field_computes 1).comp lengthBits_computes)
noncomputable def remaining_computes : PolyComputes remaining := ((field_computes 0).pair (field_computes 1)).comp BinaryNatSet.diff_computes
attribute [local irreducible] need remaining BinaryNatSet.union Take.run
noncomputable def run_computes : PolyComputes run :=
  ((field_computes 1).pair ((need_computes.pair remaining_computes).comp Take.run_computes)).comp BinaryNatSet.union_computes
end MetricKMedianRecovery.BitMachine.BinaryCompletionPad

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_FinSets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRationalSort
open WordOperations WordList BinaryArithmetic
attribute [local irreducible] mapWith
noncomputable def sumBottom_computes : PolyComputes sumBottom := by
  unfold sumBottom
  exact (((const_computes []).pair bottom_computes).comp
    (mapWith_computes (discardPrefix_computes.comp extractPrefix_computes))).comp RationalArray.sumWords_computes
end MetricKMedianRecovery.BitMachine.BinaryRationalSort

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_RationalBottomIndices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRationalSort
open WordOperations WordList BinaryArithmetic
noncomputable def rawIndices_computes : PolyComputes rawIndices := by
  have rawIndicesComputes :=
    ((const_computes []).pair bottom_computes).comp
      (mapWith_computes (discardPrefix_computes.comp discardPrefix_computes))
  unfold rawIndices
  simpa only [Function.comp_def] using rawIndicesComputes
end MetricKMedianRecovery.BitMachine.BinaryRationalSort

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_FinImages
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryFinSet
open WordOperations WordList
variable {m n : ℕ}
noncomputable def image_computes : PolyComputes image := BinaryIndexMap.run_computes.comp BinaryNatSet.sort_computes
end MetricKMedianRecovery.BitMachine.BinaryFinSet

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CopyGround
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCopyTables
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
variable {n a : ℕ}
noncomputable def entry_computes : PolyComputes entry :=
  (((discardPrefix_computes.pair extractPrefix_computes).comp BinaryNatSet.contains_computes).cond
    discardPrefix_computes (extractPrefix_computes.comp WordList.head_computes))
attribute [local irreducible] mapWith flatMapWith
noncomputable def row_computes : PolyComputes row := by
  unfold row
  exact (ball_computes.pair columns_computes).comp (mapWith_computes entry_computes)
noncomputable def locations_computes : PolyComputes locations := by
  unfold locations
  exact (id_computes.pair indices_computes).comp (flatMapWith_computes row_computes)
end MetricKMedianRecovery.BitMachine.BinaryCopyTables

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_ColorLabelMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryColorLabel
open WordOperations WordList BinaryArithmetic
attribute [local irreducible] WordList.mapWith
noncomputable def colors_computes : PolyComputes colors :=
  ((const_computes []).pair (BinarySeed.nest_computes 1)).comp
    (mapWith_computes (discardPrefix_computes.comp colorWord_computes))
noncomputable def labels_computes : PolyComputes labels :=
  (extractPrefix_computes.pair (discardPrefix_computes.comp (BinarySeed.nest_computes 1))).comp (mapWith_computes labelOp_computes)
end MetricKMedianRecovery.BitMachine.BinaryColorLabel

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_CandidateSanitize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCandidateSanitize
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
noncomputable def keep_computes : PolyComputes (fun x=>[keep x]) :=
  (discardPrefix_computes.pair extractPrefix_computes).comp BinaryNatSet.contains_computes
noncomputable def clip_computes : PolyComputes clip :=
  ((field_computes 3).pair (field_computes 0)).comp (filterWith_computes keep_computes)
noncomputable def size_computes : PolyComputes size := (clip_computes.comp Count.run_computes).comp UnaryResources.lengthBits_computes
end MetricKMedianRecovery.BitMachine.BinaryCandidateSanitize

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_RationalSurrogate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCompletion
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
variable {q p r : ℕ}
noncomputable def surrogate_computes : PolyComputes surrogate := by
  have surrogateComputes :=
    RatOps.add (RatOps.ofWords (clientValues_computes.comp RationalArray.sumWords_computes))
      (RatOps.ofWords (((extractPrefix_computes.comp (field_computes 0)).pair redValues_computes).comp BinaryRationalSort.sumBottom_computes))
  unfold surrogate
  simpa only [Function.comp_def] using surrogateComputes
noncomputable def saving_computes : PolyComputes saving :=
  RatOps.sub (RatOps.ofWords ((extractPrefix_computes.pair (const_computes [])).comp surrogate_computes))
    (RatOps.ofWords surrogate_computes)
end MetricKMedianRecovery.BitMachine.BinaryCompletion

namespace MetricKMedianRecovery.BitMachine.BinaryBranchRows
open WordOperations WordList
open BinaryOpeningPayment (field field_computes field_encode)
variable {n q r : ℕ}
noncomputable def row_computes : PolyComputes row := by
  have rowComputes := (oracleInput_computes 0).comp BinarySamplingOracle.row_computes
  unfold row
  simpa only [Function.comp_def] using rowComputes
noncomputable def distances_computes : PolyComputes distances := by
  have distancesComputes :=
    (row_computes.pair (extractPrefix_computes.comp (field_computes 2))).comp BinaryIndexMap.run_computes
  unfold distances
  simpa only [Function.comp_def] using distancesComputes
noncomputable def base_computes (j : ℕ) : PolyComputes (base j) :=
  ((oracleInput_computes j).comp BinarySamplingOracle.reference_computes).comp extractPrefix_computes
noncomputable def capRow_computes (j : ℕ) : PolyComputes (capRow j) :=
  cons_computes (base_computes j) (cons_computes distances_computes (const_computes []))
noncomputable def weight_computes : PolyComputes weight := by
  have weightComputes :=
    (discardPrefix_computes.pair ((extractPrefix_computes.comp (field_computes 0)).comp BinaryAssignmentWeight.identities_computes)).comp
      BinaryAssignmentWeight.run_computes
  unfold weight
  simpa only [Function.comp_def] using weightComputes
noncomputable def redRow_computes : PolyComputes redRow := weight_computes.pair (capRow_computes 1)
noncomputable def clients_computes : PolyComputes clients := by
  have clientsComputes :=
    (id_computes.pair ((field_computes 0).comp (field_computes 1))).comp (mapWith_computes (capRow_computes 0))
  unfold clients
  simpa only [Function.comp_def,id_eq] using clientsComputes
noncomputable def reds_computes : PolyComputes reds := by
  have redsComputes :=
    (id_computes.pair (field_computes 3)).comp (mapWith_computes redRow_computes)
  unfold reds
  simpa only [Function.comp_def,id_eq] using redsComputes
noncomputable def run_computes : PolyComputes run := cons_computes (field_computes 4)
  (cons_computes clients_computes (cons_computes reds_computes (const_computes [])))
end MetricKMedianRecovery.BitMachine.BinaryBranchRows

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CompletionRealize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCompletionRealize
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
variable {n q a p r b : ℕ}
attribute [local irreducible] fillInput BinaryCompletionFill.run BinaryFinSet.image
noncomputable def filled_computes : PolyComputes filled :=
  ((field_computes 5).pair (fillInput_computes.comp BinaryCompletionFill.run_computes)).comp BinaryFinSet.image_computes
attribute [local irreducible] redValues BinaryNatSet.sort BinaryRationalSort.rawIndices
noncomputable def redIndices_computes : PolyComputes redIndices :=
  ((((field_computes 10).comp (field_computes 0)).pair redValues_computes).comp BinaryRationalSort.rawIndices_computes).comp BinaryNatSet.sort_computes
attribute [local irreducible] redIndices
noncomputable def red_computes : PolyComputes red := ((field_computes 6).pair redIndices_computes).comp BinaryFinSet.image_computes
noncomputable def blue_computes : PolyComputes blue := (field_computes 7).comp BinaryNatSet.sort_computes
noncomputable def dest_computes : PolyComputes dest := (field_computes 8).comp BinaryNatSet.sort_computes
attribute [local irreducible] red blue dest BinaryNatSet.union
noncomputable def removed_computes : PolyComputes removed :=
  ((((field_computes 2).pair red_computes).comp BinaryNatSet.union_computes).pair blue_computes).comp BinaryNatSet.union_computes
attribute [local irreducible] removed BinaryNatSet.diff
noncomputable def remain_computes : PolyComputes remain := ((field_computes 1).pair removed_computes).comp BinaryNatSet.diff_computes
attribute [local irreducible] filled
noncomputable def added_computes : PolyComputes added := (filled_computes.pair dest_computes).comp BinaryNatSet.union_computes
attribute [local irreducible] remain added
noncomputable def core_computes : PolyComputes core := (remain_computes.pair added_computes).comp BinaryNatSet.union_computes
attribute [local irreducible] core
noncomputable def runInput_computes : PolyComputes runInput :=
  cons_computes (field_computes 0) (cons_computes core_computes
    (cons_computes ((field_computes 1).comp lengthBits_computes) (const_computes [])))
noncomputable def run_computes : PolyComputes run := runInput_computes.comp BinaryCompletionPad.run_computes
end MetricKMedianRecovery.BitMachine.BinaryCompletionRealize

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_CompletionAlgorithm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCompletionAlgorithm
open WordOperations WordList BinaryArithmetic
variable {n q a p r b T L : ℕ}
noncomputable def selected_computes : PolyComputes selected :=
  discardPrefix_computes.comp (BinaryCategorical.output_computes BinaryCompletion.saving_computes)
attribute [local irreducible] selected Set.run
noncomputable def input_computes : PolyComputes input :=
  (Set.pack_computes extractPrefix_computes (const_computes (9:ℕ).bits) selected_computes).comp Set.run_computes
noncomputable def run_computes : PolyComputes run := input_computes.comp BinaryCompletionRealize.run_computes
end MetricKMedianRecovery.BitMachine.BinaryCompletionAlgorithm

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
attribute [local irreducible] remaining
noncomputable def context_computes : PolyComputes context :=
  (cons_computes ((field_computes 0).comp lengthBits_computes) (cons_computes (field_computes 4) (cons_computes remaining_computes (cons_computes ((field_computes 5).comp discardPrefix_computes) (const_computes [])))))
attribute [local irreducible] context
noncomputable def oracle_computes : PolyComputes oracle :=
  (cons_computes (field_computes 0) (cons_computes (field_computes 1) (cons_computes context_computes (const_computes []))))
attribute [local irreducible] oracle
attribute [local irreducible] classOf
noncomputable def greenContext_computes : PolyComputes greenContext :=
  (cons_computes ((field_computes 0).comp lengthBits_computes) (cons_computes (field_computes 4) (cons_computes (classOf_computes 0) (cons_computes ((field_computes 5).comp discardPrefix_computes) (const_computes [])))))
attribute [local irreducible] greenContext
noncomputable def greenOracle_computes : PolyComputes greenOracle :=
  (cons_computes (field_computes 0) (cons_computes (field_computes 1) (cons_computes greenContext_computes (const_computes []))))
attribute [local irreducible] greenOracle
attribute [local irreducible] ballInput
attribute [local irreducible] copyData
noncomputable def parts_computes : PolyComputes parts :=
  copyData_computes.comp BinaryCopyTables.parts_computes
attribute [local irreducible] parts
noncomputable def origins_computes : PolyComputes origins := by
  have originsComputes := copyData_computes.comp BinaryCopyTables.origins_computes
  unfold origins
  simpa only [Function.comp_def] using originsComputes
attribute [local irreducible] origins
noncomputable def locations_computes : PolyComputes locations :=
  copyData_computes.comp BinaryCopyTables.locations_computes
attribute [local irreducible] locations
end MetricKMedianRecovery.BitMachine.BinaryBranchContext

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CompletionFair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCompletionFair
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
open Categorical.Explicit
variable {n q a p r c : ℕ}
noncomputable def prepared_computes : PolyComputes prepared :=
  (context_computes.pair discardPrefix_computes).comp BinaryCategorical.Prepare.run_computes
attribute [local irreducible] prepared
noncomputable def run_computes : PolyComputes run :=
  (extractPrefix_computes.pair prepared_computes).comp BinaryCompletionAlgorithm.run_computes
end MetricKMedianRecovery.BitMachine.BinaryCompletionFair

namespace MetricKMedianRecovery.BitMachine.BinaryBranchProgram
open WordOperations WordList BinaryBranchContext
open BinaryOpeningPayment (field field_computes field_encode)
variable {n m : ℕ}
noncomputable def blueInput_computes : PolyComputes (blueInput) :=
  (cons_computes oracle_computes (cons_computes (classOf_computes 2) (cons_computes (field_computes 7) (const_computes []))))
attribute [local irreducible] blueInput
noncomputable def records_computes : PolyComputes (records) := by
  unfold records
  have computes := blueInput_computes.comp BinaryBlueRecords.run_computes
  simpa only [Function.comp_def] using computes
attribute [local irreducible] records
noncomputable def bluePack_computes : PolyComputes (bluePack) :=
  (cons_computes records_computes (cons_computes (field_computes 2) (cons_computes (field_computes 8) (cons_computes (field_computes 10) (cons_computes (field_computes 11) (const_computes []))))))
attribute [local irreducible] bluePack
noncomputable def best_computes (d : ℕ) : PolyComputes (best d) := by
  unfold best
  have computes := bluePack_computes.comp (BinaryBlueProgram.run_computes d)
  simpa only [Function.comp_def] using computes
attribute [local irreducible] best
noncomputable def plan_computes (d : ℕ) : PolyComputes (plan d) :=
  ((best_computes d).pair (field_computes 8)).comp BinaryBlueOutput.run_computes
attribute [local irreducible] plan
noncomputable def rowInput_computes : PolyComputes (rowInput) :=
  (cons_computes oracle_computes (cons_computes greenOracle_computes (cons_computes locations_computes (cons_computes (classOf_computes 1) (cons_computes (field_computes 9) (const_computes []))))))
attribute [local irreducible] rowInput
noncomputable def rows_computes : PolyComputes (rows) :=
  rowInput_computes.comp BinaryBranchRows.run_computes
attribute [local irreducible] rows
noncomputable def completion_computes (d : ℕ) : PolyComputes (completion d) :=
  (cons_computes (field_computes 2) (cons_computes (field_computes 3) (cons_computes ((field_computes 5).comp extractPrefix_computes) (cons_computes parts_computes (cons_computes origins_computes (cons_computes locations_computes (cons_computes (classOf_computes 1) (cons_computes ((plan_computes d).comp (field_computes 0)) (cons_computes ((plan_computes d).comp (field_computes 1)) (cons_computes (const_computes []) (cons_computes rows_computes (const_computes []))))))))))))
attribute [local irreducible] completion
noncomputable def run_computes (d : ℕ) : PolyComputes (run d) :=
  ((extractPrefix_computes.comp (completion_computes d)).pair discardPrefix_computes).comp BinaryCompletionFair.run_computes
attribute [local irreducible] run
end MetricKMedianRecovery.BitMachine.BinaryBranchProgram

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BranchSeedLayout
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBranchRandomize
open WordOperations WordList BinaryArithmetic BinaryBranchContext
open BinaryOpeningPayment (field field_computes field_encode)
attribute [local irreducible] Count.run BinaryBisection.logWord RawTake.run RawDrop.run BinaryColorLabel.colors BinaryColorLabel.labels
noncomputable def blog_computes : PolyComputes blog := ((field_computes 8).comp lengthBits_computes).comp BinaryBisection.logWord_computes
noncomputable def lshape_computes : PolyComputes lshape := cons_computes nword_computes (cons_computes blog_computes (const_computes []))
noncomputable def lsize_computes : PolyComputes lsize := by
  unfold lsize
  simpa only [Function.comp_def] using NatOps.mul (nword_computes.comp UnaryResources.lengthBits_computes) (blog_computes.comp UnaryResources.lengthBits_computes)
noncomputable def lraw_computes : PolyComputes lraw :=
  ((extractPrefix_computes.comp lsize_computes).pair rest_computes).comp RawTake.run_computes
noncomputable def tailBits_computes : PolyComputes tailBits :=
  ((extractPrefix_computes.comp lsize_computes).pair rest_computes).comp RawDrop.run_computes
noncomputable def colors_computes : PolyComputes colors :=
  ((extractPrefix_computes.comp cshape_computes).pair craw_computes).comp BinaryColorLabel.colors_computes
noncomputable def labels_computes : PolyComputes labels :=
  (((extractPrefix_computes.comp (field_computes 8)).comp lengthBits_computes).pair
    ((extractPrefix_computes.comp lshape_computes).pair lraw_computes)).comp BinaryColorLabel.labels_computes
end MetricKMedianRecovery.BitMachine.BinaryBranchRandomize

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_RandomizedZeroBranch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBranchTape.Count
open WordOperations WordList BinaryArithmetic BinaryBranchContext
open BinaryOpeningPayment (field field_computes field_encode)
open BinaryCategorical
noncomputable def qword_computes : PolyComputes qword := UnaryResources.copy_computes pword_computes BinaryBranchRandomize.nword_computes
noncomputable def dimensions_computes : PolyComputes dimensions := qword_computes.pair pword_computes
attribute [local irreducible] dimensions Resources.tword Resources.lword Resources.bword BinarySeed.product
noncomputable def tword_computes : PolyComputes tword := dimensions_computes.comp Resources.tword_computes
noncomputable def lword_computes : PolyComputes lword := dimensions_computes.comp Resources.lword_computes
noncomputable def bword_computes : PolyComputes bword := dimensions_computes.comp Resources.bword_computes
noncomputable def leftShape_computes : PolyComputes leftShape := cons_computes tword_computes
  (cons_computes qword_computes (cons_computes lword_computes (cons_computes pword_computes (cons_computes bword_computes (const_computes [])))))
noncomputable def rightShape_computes : PolyComputes rightShape := cons_computes pword_computes (cons_computes bword_computes (const_computes []))
attribute [local irreducible] leftShape rightShape BinaryBranchRandomize.csize BinaryBranchRandomize.lsize
noncomputable def run_computes : PolyComputes run := by
  unfold run
  simpa only [value_bits,Function.comp_def] using NatOps.add (NatOps.add BinaryBranchRandomize.csize_computes BinaryBranchRandomize.lsize_computes)
    (NatOps.add (leftShape_computes.comp (BinarySeed.product_computes 5)) (rightShape_computes.comp (BinarySeed.product_computes 2)))
attribute [local irreducible] run RawTake.run
noncomputable def cut_computes : PolyComputes cut := extractPrefix_computes.pair
  (((extractPrefix_computes.comp run_computes).pair discardPrefix_computes).comp RawTake.run_computes)
end MetricKMedianRecovery.BitMachine.BinaryBranchTape.Count

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_CrossCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryFiniteContext
open WordOperations WordList RationalLeaves BinaryArithmetic
noncomputable def countInter_computes : PolyComputes countInter := inter_computes.comp lengthBits_computes
end MetricKMedianRecovery.BitMachine.BinaryFiniteContext

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_PlanResult
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryPlanResult
open WordOperations WordList BinaryArithmetic RationalLeaves CanonicalCoupledMerge CanonicalLengthView
open BinaryOpeningPayment (field field_computes field_encode)
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)

noncomputable def price_computes : PolyComputes price := (sf_computes 0).comp (field_computes 7)
end MetricKMedianRecovery.BitMachine.BinaryPlanResult

end OAI
end


