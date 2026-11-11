-- Prove2me | Definitions.Def_Q238K037
-- name    : Q238K037
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T23:32:53.459394+00:00
-- url     : https://prove2.me/theorems/5cf06179-f346-4125-9c48-b87bad666c97
-- title:
--   Definitions bundle Q238K037 of the split of OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 99 declarations of OpenAI's Lean: 99 definitions. The definitions and types are `OAI.MetricKMedianRecovery.BitMachine.BinaryBisection.width_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueCollect.bad_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueCollect.result_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueCollect.run_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueMerge.output_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueMerge.run_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueMerge.sum_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.run`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchRandomize.colors`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchRandomize.context`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchRandomize.labels`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.Prepare.left`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.Prepare.right`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.Prepare.run`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.Prepare.runInput`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.advanceItem_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.advance_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.bagTest_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.bagWords_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.drawItems_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.drawPick_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.draw_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.marginalDraw_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.marginalValues_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.marginal_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.output`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.score_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryColorLabel.colors`, `OAI.MetricKMedianRecovery.BitMachine.BinaryColorLabel.labels`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletion.saving`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletion.surrogate`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionAlgorithm.input`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionAlgorithm.run`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionAlgorithm.selected`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionFair.prepared`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionFair.run`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionPad.run`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionRealize.core`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionRealize.red`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionRealize.redIndices` and 59 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedianRecovery_Algorithms_CompletionAlgorithm`, `KMedianRecovery_Algorithms_IntegralRecoveryAll`, `KMedianRecovery_Branching_BlueMerge`, `KMedianRecovery_Branching_BranchObjective`, `KMedianRecovery_Branching_BranchPrefix`, `KMedianRecovery_Branching_BranchSeedLayout`, `KMedianRecovery_Branching_CategoricalChoice`, `KMedianRecovery_Branching_CategoricalOutput`, `KMedianRecovery_Branching_CategoricalRawPrep`, `KMedianRecovery_Branching_CategoricalScore`, `KMedianRecovery_Branching_CategoricalTable`, `KMedianRecovery_Branching_CompletionFair`, `KMedianRecovery_Branching_CompletionFillMath`, `KMedianRecovery_Branching_CompletionRealize`, `KMedianRecovery_Branching_ObservableCapacity`, `KMedianRecovery_Branching_RandomizedZeroBranch`, `KMedianRecovery_Branching_RationalSurrogate`, `KMedianRecovery_Encoding_BoundedNatWord`, `KMedianRecovery_Encoding_ColorLabelMachine`, `KMedianRecovery_Encoding_DuplicateMatrix`, `KMedianRecovery_Encoding_FinSets`, `KMedianRecovery_Encoding_RationalBottomIndices`, `KMedianRecovery_Encoding_RationalSort`, `KMedianRecovery_Encoding_WordTake`, `KMedianRecovery_Geometry_LocalFuel`, `KMedianRecovery_Geometry_MetricAnchor`, `KMedianRecovery_Machines_BisectionMachine`, `KMedianRecovery_Machines_GridMachine`, `KMedianRecovery_Machines_SliceFold`, `KMedianRecovery_Recovery_Min`, `KMedianRecovery_Recovery_OrientedSearch`, `KMedianRecovery_Recovery_RecoveryEnumeration`, `KMedianRecovery_Sampling_InverseCDF`, `KMedianRecovery_Sampling_SeedTensor`, `KMedianRecovery_Strictness_SurplusPostprocess`.
--
--   **Imports.** It imports the published bundle `Def_KMedianRefinedRecovery`; the bundles `Q238K032`, `Q238K033` and `Q238K034` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q238K039` and `Q238K040`; the statements `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchRandomize.context_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchRandomize.labels_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.Prepare.left_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.Prepare.run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.output_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionRealize.redIndices_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionRealize.run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletion.saving_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDyadic.lookup_draw_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFinSet.pad_pack_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryInputParser_Metric_matrix_bits_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInverseCDF.find_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryLocalAnchor.run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryLocalAnchor.state_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMetricAnchor.produce_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryObservableBranch.run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRandomizedBranch.source_run_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRandomizedZeroBranch.Prefix.run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRationalSort.sumBottom_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRecovery.atBranch_context_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRecovery.atBranch_source_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinarySeed.nest_tensor_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinarySurplusPostprocess.integral_spec_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinarySurplusPostprocess.localInput_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryZeroBranch.check_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryZeroBranch.completion_pack_s238` and `OAI.MetricKMedianRecovery.BitMachine.BinaryZeroBranch.run_pack_s238`; the proofs of `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchRandomize.context_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchRandomize.labels_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.Prepare.left_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.Prepare.run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.output_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionRealize.redIndices_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionRealize.run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletion.saving_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDyadic.lookup_draw_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFinSet.pad_pack_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryInputParser_Metric_matrix_bits_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInverseCDF.find_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryLocalAnchor.run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryLocalAnchor.state_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMetricAnchor.produce_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryObservableBranch.run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRandomizedBranch.source_run_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRandomizedZeroBranch.Prefix.run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRationalSort.sumBottom_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRecovery.atBranch_context_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRecovery.atBranch_source_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinarySeed.nest_tensor_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinarySurplusPostprocess.integral_spec_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinarySurplusPostprocess.localInput_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryZeroBranch.check_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryZeroBranch.completion_pack_s238` and `OAI.MetricKMedianRecovery.BitMachine.BinaryZeroBranch.run_pack_s238`.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_KMedianRefinedRecovery
import Definitions.Def_Q238K032
import Definitions.Def_Q238K033
import Definitions.Def_Q238K034

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CategoricalTable
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCategorical
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes )
variable {E : Type*} {a T : ℕ}
noncomputable def drawItems_computes : PolyComputes drawItems :=
  (((field_computes 1).comp Indices.run_computes).pair (field_computes 1)).comp Zip.run_computes
noncomputable def drawPick_computes : PolyComputes drawPick := by
  have h := (NatOps.eq (discardPrefix_computes.comp extractPrefix_computes)
    (extractPrefix_computes.comp (field_computes 2))).cond (const_computes [])
    (((discardPrefix_computes.comp discardPrefix_computes).pair drawRow_computes).comp Lookup.run_computes)
  unfold drawPick
  simpa only [decide_eq_true_eq,Function.comp_def] using h
noncomputable def draw_computes : PolyComputes draw := (id_computes.pair drawItems_computes).comp (flatMapWith_computes drawPick_computes)
attribute [local irreducible] Set.run mapWith
noncomputable def advanceItem_computes : PolyComputes advanceItem := by
  unfold advanceItem
  have h0 := (discardPrefix_computes.pair (extractPrefix_computes.comp (field_computes 0))).comp Lookup.run_computes
  have h1 := (discardPrefix_computes.pair (extractPrefix_computes.comp (field_computes 1))).comp Lookup.run_computes
  exact (h0.pair ((extractPrefix_computes.comp (field_computes 2)).pair
    (cons_computes h1 (const_computes [])))).comp Set.run_computes
noncomputable def advance_computes : PolyComputes advance := by
  unfold advance
  exact (id_computes.pair ((field_computes 1).comp Indices.run_computes)).comp (mapWith_computes advanceItem_computes)
end MetricKMedianRecovery.BitMachine.BinaryCategorical

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CategoricalScore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCategorical
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes )
variable {q a T L : ℕ}
noncomputable def marginalDraw_computes : PolyComputes marginalDraw :=
  (cons_computes ((extractPrefix_computes.comp extractPrefix_computes).comp (field_computes 1))
    (cons_computes discardPrefix_computes (cons_computes (extractPrefix_computes.comp elementPart_computes)
      (const_computes [])))).comp draw_computes
noncomputable def marginal_computes {g : List Bool→List Bool} (hg : PolyComputes g) : PolyComputes (marginal g) :=
  RatOps.sub (RatOps.ofWords ((((extractPrefix_computes.comp extractPrefix_computes).comp (field_computes 0)).pair
    (cons_computes (extractPrefix_computes.comp discardPrefix_computes) marginalDraw_computes)).comp hg))
    (RatOps.ofWords ((((extractPrefix_computes.comp extractPrefix_computes).comp (field_computes 0)).pair
      marginalDraw_computes).comp hg))
attribute [local irreducible] mapWith
noncomputable def marginalValues_computes {g : List Bool→List Bool} (hg : PolyComputes g) : PolyComputes (marginalValues g) := by
  unfold marginalValues
  exact (id_computes.pair elementSamples_computes).comp (mapWith_computes (marginal_computes hg))
noncomputable def score_computes {g : List Bool→List Bool} (hg : PolyComputes g) : PolyComputes (score g) :=
  RatOps.div (RatOps.ofWords ((marginalValues_computes hg).comp RationalArray.sumWords_computes))
    (RatOps.nat ((elementSamples_computes.comp Count.run_computes).comp UnaryResources.lengthBits_computes))
end MetricKMedianRecovery.BitMachine.BinaryCategorical

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CategoricalChoice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCategorical
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes )
variable {q a T L : ℕ}
noncomputable def bagTest_computes : PolyComputes (fun x=>[bagTest x]) :=
  NatOps.eq ((((extractPrefix_computes.comp extractPrefix_computes).pair discardPrefix_computes).comp elementPart_computes))
    (extractPrefix_computes.comp discardPrefix_computes)
noncomputable def bagWords_computes : PolyComputes bagWords :=
  (id_computes.pair ((extractPrefix_computes.comp (field_computes 3)).comp Indices.run_computes)).comp
    (filterWith_computes bagTest_computes)
attribute [local irreducible] mapWith
end MetricKMedianRecovery.BitMachine.BinaryCategorical

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Min
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic WordList
namespace BinaryPhaseAdvance
open EffectiveOpenability RationalPhase BinaryPhaseUpdate BinaryOpeningPayment

noncomputable def paramV_computes : PolyComputes (fun x=>BinaryRational.encode (paramV x)) := RatOps.ofWords (sf_computes 2)
noncomputable def paramZ_computes : PolyComputes (fun x=>BinaryRational.encode (paramZ x)) := RatOps.ofWords (sf_computes 3)
noncomputable def phase_computes : PolyComputes (fun x=>BinaryRational.encode (phase x)) :=
  RatOps.mul (RatOps.add (RatOps.const 1) (RatOps.mul paramV_computes paramV_computes)) paramZ_computes
noncomputable def context_computes : PolyComputes context :=
  cons_computes (sf_computes 0) (cons_computes (sf_computes 1) (cons_computes (sf_computes 2)
    (cons_computes phase_computes (cons_computes (sf_computes 4) (cons_computes (sf_computes 5)
    (cons_computes (sf_computes 6) (cons_computes (sf_computes 7) (cons_computes (sf_computes 8) (const_computes [])))))))))
end BinaryPhaseAdvance
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_WordTake
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.WordList.Take
open WordOperations BinaryArithmetic
noncomputable def run (x : List Bool) : List Bool :=
  reverse (Drop.run (pairBits (number x,reverse (discardPrefix x))))
attribute [local irreducible] number reverse Drop.run
end MetricKMedianRecovery.BitMachine.WordList.Take

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_SeedTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySeed
open WordOperations WordList BinaryArithmetic
attribute [local irreducible] width RawTake.run RawDrop.run
noncomputable def child (d : ℕ) (x : List Bool) : List Bool :=
  pairBits (tail (extractPrefix (extractPrefix x)),chunk d x)
noncomputable def nest : ℕ→List Bool→List Bool
  | 0,x =>normalizeBig (discardPrefix x)
  | d+1,x =>mapWith (fun y=>nest d (child d y)) (pairBits (x,indices x))
end MetricKMedianRecovery.BitMachine.BinarySeed

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CategoricalOutput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCategorical
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes )
variable {q a T L : ℕ}
noncomputable def output (g : List Bool→List Bool) (x : List Bool) : List Bool :=
  draw (encode [field 1 (run g (extractPrefix x)),discardPrefix x,
    UnaryResources.lengthBits (field 2 (extractPrefix x))])
end MetricKMedianRecovery.BitMachine.BinaryCategorical

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
noncomputable def bottom (x : List Bool) : List Bool :=
  Take.run (pairBits (extractPrefix x,sort (ranked (discardPrefix x))))
end MetricKMedianRecovery.BitMachine.BinaryRationalSort

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
open BinaryOpeningPayment (field field_computes )
noncomputable def run (x : List Bool) : List Bool := BinaryNatSet.union (pairBits (field 1 x,Take.run (pairBits (need x,remaining x))))
attribute [local irreducible] need remaining BinaryNatSet.union Take.run
end MetricKMedianRecovery.BitMachine.BinaryCompletionPad

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CategoricalRawPrep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCategorical.Prepare
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes )
open Categorical.Explicit
variable {q a : ℕ}
attribute [local irreducible] Resources.tword Resources.lword Resources.bword dimensions
attribute [local irreducible] BinarySeed.product leftShape
noncomputable def left (x : List Bool) : List Bool := BinarySeed.nest 4 (pairBits (leftShape x,RawTake.run (pairBits (cut x,discardPrefix x))))
noncomputable def right (x : List Bool) : List Bool := BinarySeed.nest 1 (pairBits (rightShape x,RawDrop.run (pairBits (cut x,discardPrefix x))))
attribute [local irreducible] BinarySeed.nest RawTake.run RawDrop.run cut rightShape tword lword bword
noncomputable def runInput (x : List Bool) : List Bool := encode [field 0 (extractPrefix x),field 1 (extractPrefix x),aword x,tword x,left x]
noncomputable def run (x : List Bool) : List Bool := pairBits (runInput x,right x)
end MetricKMedianRecovery.BitMachine.BinaryCategorical.Prepare

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

noncomputable def sumBottom (x : List Bool) : List Bool :=
  RationalArray.sumWords (mapWith (fun y=>extractPrefix (discardPrefix y)) (pairBits ([],bottom x)))
attribute [local irreducible] mapWith
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
noncomputable def rawIndices (x : List Bool) : List Bool :=
  mapWith (fun y=>discardPrefix (discardPrefix y)) (pairBits ([],bottom x))
end MetricKMedianRecovery.BitMachine.BinaryRationalSort

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
noncomputable def colors (x : List Bool) : List Bool :=
  mapWith (colorWord ∘ discardPrefix) (pairBits ([],BinarySeed.nest 1 x))
noncomputable def labels (x : List Bool) : List Bool :=
  mapWith labelOp (pairBits (extractPrefix x,BinarySeed.nest 1 (discardPrefix x)))
end MetricKMedianRecovery.BitMachine.BinaryColorLabel

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
open BinaryOpeningPayment (field field_computes )
variable {q p r : ℕ}
noncomputable def surrogate (x : List Bool) : List Bool :=
  BinaryRational.encode (BinaryRational.decode (RationalArray.sumWords (clientValues x))+
    BinaryRational.decode (BinaryRationalSort.sumBottom (pairBits (field 0 (extractPrefix x),redValues x))))
noncomputable def saving (x : List Bool) : List Bool :=
  BinaryRational.encode (BinaryRational.decode (surrogate (pairBits (extractPrefix x,[])))-
    BinaryRational.decode (surrogate x))
end MetricKMedianRecovery.BitMachine.BinaryCompletion

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
open BinaryOpeningPayment (field field_computes )
variable {n q a p r b : ℕ}
attribute [local irreducible] fillInput BinaryCompletionFill.run BinaryFinSet.image
noncomputable def redIndices (x : List Bool) : List Bool := BinaryNatSet.sort
  (BinaryRationalSort.rawIndices (pairBits (field 0 (field 10 x),redValues x)))
attribute [local irreducible] redValues BinaryNatSet.sort BinaryRationalSort.rawIndices
noncomputable def red (x : List Bool) : List Bool := BinaryFinSet.image (pairBits (field 6 x,redIndices x))
attribute [local irreducible] redIndices
noncomputable def removed (x : List Bool) : List Bool := BinaryNatSet.union
  (pairBits (BinaryNatSet.union (pairBits (field 2 x,red x)),blue x))
attribute [local irreducible] red blue dest BinaryNatSet.union
noncomputable def remain (x : List Bool) : List Bool := BinaryNatSet.diff (pairBits (field 1 x,removed x))
attribute [local irreducible] removed BinaryNatSet.diff
attribute [local irreducible] filled
noncomputable def core (x : List Bool) : List Bool := BinaryNatSet.union (pairBits (remain x,added x))
attribute [local irreducible] remain added
noncomputable def runInput (x : List Bool) : List Bool := encode [field 0 x,core x,lengthBits (field 1 x)]
attribute [local irreducible] core
noncomputable def run (x : List Bool) : List Bool := BinaryCompletionPad.run (runInput x)
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
noncomputable def selected (x : List Bool) : List Bool := BinaryCategorical.output BinaryCompletion.saving (discardPrefix x)
noncomputable def input (x : List Bool) : List Bool := Set.run (Set.pack (extractPrefix x) (9:ℕ).bits (selected x))
attribute [local irreducible] selected Set.run
noncomputable def run (x : List Bool) : List Bool := BinaryCompletionRealize.run (input x)
end MetricKMedianRecovery.BitMachine.BinaryCompletionAlgorithm

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_InverseCDF
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryInverseCDF
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes )
open Dyadic.Canonical

noncomputable def prefixCounts (x : List Bool) : List Bool :=
  Take.run (pairBits (UnaryResources.inc (discardPrefix x),extractPrefix (extractPrefix x)))
attribute [local irreducible] Take.run UnaryResources.inc
noncomputable def total (x : List Bool) : List Bool := NaturalArray.sumWords (prefixCounts x)
attribute [local irreducible] prefixCounts NaturalArray.sumWords
noncomputable def predicate (x : List Bool) : Bool :=
  decide (value (discardPrefix (extractPrefix x))<value (total x))
attribute [local irreducible] total
noncomputable def find (x : List Bool) : List Bool :=
  Find.run predicate (pairBits (x,Indices.run (extractPrefix x)))
noncomputable def searched (x : List Bool) : List Bool := find (pairBits (field 1 x,BinarySeed.normalizeBig (field 2 x)))
attribute [local irreducible] searched
noncomputable def run (x : List Bool) : List Bool := if searched x=[] then field 0 x else (searched x).tail
end MetricKMedianRecovery.BitMachine.BinaryInverseCDF

namespace MetricKMedianRecovery.BitMachine.BinaryDyadic
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes )
noncomputable def run (x : List Bool) : List Bool := BinaryInverseCDF.run (prepared x)
end MetricKMedianRecovery.BitMachine.BinaryDyadic

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BlueMerge
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBlueMerge
open WordOperations WordList
variable {A : Type*}
noncomputable def sum_computes : PolyComputes sum :=
  RatOps.add (RatOps.ofWords (extractPrefix_computes.comp BinaryBlueChoice.score_computes))
    (RatOps.ofWords (discardPrefix_computes.comp BinaryBlueChoice.score_computes))
noncomputable def output_computes : PolyComputes output :=
  cons_computes (sum_computes.pair ((extractPrefix_computes.comp payload_computes).append
    (discardPrefix_computes.comp payload_computes))) (const_computes [])
noncomputable def run_computes : PolyComputes run := by
  unfold run
  simpa only [Function.comp_def,decide_eq_true_eq] using
    (extractPrefix_computes.comp isEmpty_computes).cond (const_computes [])
      ((discardPrefix_computes.comp isEmpty_computes).cond (const_computes []) output_computes)
end MetricKMedianRecovery.BitMachine.BinaryBlueMerge

namespace MetricKMedianRecovery.BitMachine.BinaryBlueCollect
open WordOperations WordList
variable {A : Type*}
noncomputable def bad_computes : PolyComputes bad := ((const_computes []).pair id_computes).comp (Find.run_computes invalid_computes)
attribute [local irreducible] mapWith
noncomputable def result_computes : PolyComputes result :=
  cons_computes ((scores_computes.comp RationalArray.sumWords_computes).pair contents_computes) (const_computes [])
noncomputable def run_computes : PolyComputes run := by
  unfold run
  simpa only [Function.comp_def,decide_eq_true_eq] using
    (bad_computes.comp isEmpty_computes).cond result_computes (const_computes [])
end MetricKMedianRecovery.BitMachine.BinaryBlueCollect

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
open BinaryOpeningPayment (field field_computes )
open Categorical.Explicit
variable {n q a p r c : ℕ}
noncomputable def prepared (x : List Bool) : List Bool := BinaryCategorical.Prepare.run (pairBits (context x,discardPrefix x))
attribute [local irreducible] prepared
noncomputable def run (x : List Bool) : List Bool := BinaryCompletionAlgorithm.run (pairBits (extractPrefix x,prepared x))
end MetricKMedianRecovery.BitMachine.BinaryCompletionFair

namespace MetricKMedianRecovery.BitMachine.BinaryBranchProgram
open WordOperations WordList BinaryBranchContext
open BinaryOpeningPayment (field field_computes )
variable {n m : ℕ}
attribute [local irreducible] blueInput
attribute [local irreducible] records
attribute [local irreducible] bluePack
attribute [local irreducible] best
attribute [local irreducible] plan
attribute [local irreducible] rowInput
attribute [local irreducible] rows
attribute [local irreducible] completion
noncomputable def run (d : ℕ) (x : List Bool) : List Bool := BinaryCompletionFair.run (pairBits (completion d (extractPrefix x),discardPrefix x))
attribute [local irreducible] run
end MetricKMedianRecovery.BitMachine.BinaryBranchProgram

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BranchObjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryObservableBranch
open WordOperations WordList BinaryBranchContext BinaryBranchProgram
open BinaryOpeningPayment (field field_computes )
variable {n m : ℕ}
noncomputable def run (d : ℕ) (x : List Bool) : List Bool :=
  if BinaryBranchCheck.run (extractPrefix x) then
    if best d (extractPrefix x)=[] then field 3 (extractPrefix x) else BinaryBranchProgram.run d x
  else field 3 (extractPrefix x)
end MetricKMedianRecovery.BitMachine.BinaryObservableBranch

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_GridMachine
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryGrid
open WordOperations WordList BinaryArithmetic DyadicGrid
open BinaryOpeningPayment (field field_computes )
noncomputable def pointWords_computes : PolyComputes pointWords :=
  RatOps.add (RatOps.ofWords (cf_computes 2))
    (RatOps.div (RatOps.mul (RatOps.sub (RatOps.ofWords (cf_computes 3)) (RatOps.ofWords (cf_computes 2)))
      (RatOps.nat num_computes)) (RatOps.nat den_computes))
noncomputable def midpoint_computes : PolyComputes midpoint :=
  (extractPrefix_computes.pair (summed_computes.pair (doubled_computes 2))).comp pointWords_computes
noncomputable def queryInput_computes : PolyComputes queryInput := (cf_computes 0).pair midpoint_computes
noncomputable def chooseLeft_computes {query : List Bool→List Bool} (hq : PolyComputes query) :
    PolyComputes (fun x=>[chooseLeft query x]) := NatOps.le (cf_computes 1) (queryInput_computes.comp hq)
noncomputable def step_computes {query : List Bool→List Bool} (hq : PolyComputes query) : PolyComputes (step query) :=
  extractPrefix_computes.pair ((chooseLeft_computes hq).cond upLeft_computes upRight_computes)
noncomputable def stateRun_computes {query : List Bool→List Bool} (hq : PolyComputes query) : PolyComputes (stateRun query) :=
  runInput_computes.comp (BoundedIteration.run_computes (step_computes hq))
noncomputable def endpoint_computes (n : ℕ) : PolyComputes (endpoint n) :=
  (extractPrefix_computes.pair ((gf_computes n).pair (gf_computes 2))).comp pointWords_computes
noncomputable def finish_computes : PolyComputes finish := (endpoint_computes 0).pair (endpoint_computes 1)
noncomputable def run_computes {query : List Bool→List Bool} (hq : PolyComputes query) : PolyComputes (run query) :=
  (stateRun_computes hq).comp finish_computes
end MetricKMedianRecovery.BitMachine.BinaryGrid

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
open BinaryOpeningPayment (field field_computes )
noncomputable def width_computes : PolyComputes (fun x=>BinaryRational.encode (width x)) :=
  RatOps.sub (RatOps.ofWords (field_computes 4)) (RatOps.ofWords (field_computes 3))
end MetricKMedianRecovery.BitMachine.BinaryBisection

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
open BinaryOpeningPayment (field field_computes )
attribute [local irreducible] Count.run BinaryBisection.logWord RawTake.run RawDrop.run BinaryColorLabel.colors BinaryColorLabel.labels
noncomputable def colors (x : List Bool) : List Bool := BinaryColorLabel.colors (pairBits (cshape (extractPrefix x),craw x))
noncomputable def labels (x : List Bool) : List Bool := BinaryColorLabel.labels
  (pairBits (lengthBits (field 8 (extractPrefix x)),pairBits (lshape (extractPrefix x),lraw x)))
noncomputable def context (x : List Bool) : List Bool :=
  encode [field 0 (extractPrefix x),field 1 (extractPrefix x),field 2 (extractPrefix x),field 3 (extractPrefix x),
    field 4 (extractPrefix x),field 5 (extractPrefix x),colors x,labels x,field 8 (extractPrefix x),
    field 9 (extractPrefix x),field 10 (extractPrefix x),field 11 (extractPrefix x)]
end MetricKMedianRecovery.BitMachine.BinaryBranchRandomize

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_ObservableCapacity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRandomizedBranch
open WordOperations WordList BinaryBranchContext BinaryObservableBranch
noncomputable def run (d : ℕ) (x : List Bool) : List Bool :=
  BinaryObservableBranch.run d (pairBits (BinaryBranchRandomize.context x,BinaryBranchRandomize.tailBits x))
end MetricKMedianRecovery.BitMachine.BinaryRandomizedBranch

namespace MetricKMedianRecovery.BitMachine.BinaryZeroBranch
open WordOperations WordList BinaryBranchContext BinaryBranchProgram BinaryArithmetic
attribute [local instance] Classical.propDecidable
open BinaryOpeningPayment (field field_computes )
variable {n : ℕ}
noncomputable def check (x : List Bool) : Bool :=
  decide (BinaryBranchCheck.outside x=[] ∧ BinaryBranchCheck.badBalls x=[] ∧ BinaryBranchCheck.badRadii x=[] ∧
    value (field 9 x)≤value (lengthBits (classOf 1 x)) ∧ value (BinaryBranchCheck.lhs x)≤value (rhs x))
noncomputable def completion (x : List Bool) : List Bool :=
  encode [field 2 x,field 3 x,extractPrefix (field 5 x),parts x,origins x,locations x,classOf 1 x,[],[],[],rows x]
noncomputable def run (x : List Bool) : List Bool :=
  if check (extractPrefix x) then
    BinaryCompletionFair.run (pairBits (completion (extractPrefix x),discardPrefix x))
  else field 3 (extractPrefix x)
end MetricKMedianRecovery.BitMachine.BinaryZeroBranch

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_RandomizedZeroBranch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRandomizedZeroBranch
open WordOperations WordList BinaryBranchContext
variable {n : ℕ}
noncomputable def run (x : List Bool) : List Bool := BinaryZeroBranch.run
  (pairBits (BinaryBranchRandomize.context x,BinaryBranchRandomize.tailBits x))
end MetricKMedianRecovery.BitMachine.BinaryRandomizedZeroBranch

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BranchPrefix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRandomizedBranch.Prefix
open WordOperations BinaryBranchContext
noncomputable def run (d : ℕ) : List Bool→List Bool := BinaryRandomizedBranch.run d ∘ BinaryBranchTape.Count.cut
end MetricKMedianRecovery.BitMachine.BinaryRandomizedBranch.Prefix
namespace MetricKMedianRecovery.BitMachine.BinaryRandomizedZeroBranch.Prefix
open WordOperations
noncomputable def run : List Bool→List Bool := BinaryRandomizedZeroBranch.run ∘ BinaryBranchTape.Count.cut
end MetricKMedianRecovery.BitMachine.BinaryRandomizedZeroBranch.Prefix

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_RecoveryEnumeration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRecovery
open WordOperations WordList
open BinaryOpeningPayment (field field_computes )
attribute [local irreducible] context zeroContext BinaryRandomizedBranch.Prefix.run BinaryRandomizedZeroBranch.Prefix.run
noncomputable def atBranch (d : ℕ) (x : List Bool) : List Bool :=
  BinaryRandomizedBranch.Prefix.run d (pairBits (context x,src 9 x))
noncomputable def atZero (x : List Bool) : List Bool :=
  BinaryRandomizedZeroBranch.Prefix.run (pairBits (zeroContext (promote x),src 9 x))
noncomputable def candidateWords (d : ℕ) (x : List Bool) : List Bool :=
  mapWith atZero (pairBits (x,range x))++ mapWith (atBranch d) (pairBits (x,choices x))
attribute [local irreducible] mapWith
attribute [local irreducible] metricContext candidateWords
end MetricKMedianRecovery.BitMachine.BinaryRecovery

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_BoundedNatWord
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BoundedNatWord
open WordOperations
attribute [local irreducible] RawTake.run RawUnary.run counter
noncomputable def run_computes (P : Polynomial ℕ) : PolyComputes (run P) :=
  ((extractPrefix_computes.pair (discardPrefix_computes.comp (counter P).computes)).comp
    RawTake.run_computes).comp RawUnary.run_computes
end MetricKMedianRecovery.BitMachine.BoundedNatWord

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_SliceFold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.WordList.Slices
open WordOperations CanonicalSlices
open BinaryOpeningPayment (field field_computes )

noncomputable def result_computes : PolyComputes result :=
  (capacity.computes.pair initial_computes).comp (CappedFold.run_computes step_computes)
noncomputable def run_computes : PolyComputes run := result_computes.comp (field_computes 2)
end MetricKMedianRecovery.BitMachine.WordList.Slices

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_OrientedSearch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryOrientedSearch
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes )
noncomputable def reversedInput_computes : PolyComputes reversedInput :=
  (extractPrefix_computes.comp extractPrefix_computes).pair
    (RatOps.sub (RatOps.ofWords (extractPrefix_computes.comp discardPrefix_computes)) (RatOps.ofWords discardPrefix_computes))
noncomputable def reversed_computes {query : List Bool→List Bool} (hq : PolyComputes query) : PolyComputes (reversed query) :=
  reversedInput_computes.comp hq
noncomputable def reflect_computes : PolyComputes reflect :=
  (RatOps.sub (RatOps.ofWords extractPrefix_computes) (RatOps.ofWords (discardPrefix_computes.comp discardPrefix_computes))).pair
    (RatOps.sub (RatOps.ofWords extractPrefix_computes) (RatOps.ofWords (discardPrefix_computes.comp extractPrefix_computes)))
noncomputable def isReversed_computes {query : List Bool→List Bool} (hq : PolyComputes query) :
    PolyComputes (fun x=>[isReversed query x]) :=
  NatOps.lt (((field_computes 1).pair (const_computes (BinaryRational.encode 0))).comp hq) (field_computes 2)
end MetricKMedianRecovery.BitMachine.BinaryOrientedSearch

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_LocalFuel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryLocalAnchor
open WordOperations WordList BinaryArithmetic RationalLeaves Polynomial
open BinaryFiniteContext (labels setBits)
open BinaryOpeningPayment (field field_computes )
noncomputable def seed (x : List Bool) : List Bool :=
  BinaryLabel.sort (Take.run (pairBits (field 3 x,field 2 x)))
attribute [local irreducible] Take.run BinaryLabel.sort
noncomputable def state (x : List Bool) : List Bool :=
  encode [field 0 x,field 1 x,field 2 x,seed x]
noncomputable def run (x : List Bool) : List Bool :=
  BinaryLocalSearch.run 5 (pairBits (fuel.word x,state x))
end MetricKMedianRecovery.BitMachine.BinaryLocalAnchor

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_MetricAnchor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryMetricAnchor
open WordOperations WordList RationalLeaves
open BinaryOpeningPayment (field field_computes )
attribute [local irreducible] BinaryLocalAnchor.run BinaryProjection.run BinaryMetricArrays.run
variable {n : ℕ}
attribute [local irreducible] WordList.map
noncomputable def run : List Bool→List Bool := BinaryProjection.run ∘ BinaryLocalAnchor.run ∘ anchorInput
attribute [local semireducible] WordList.map
end MetricKMedianRecovery.BitMachine.BinaryMetricAnchor

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_IntegralRecoveryAll
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch
open WordOperations WordList
open BinaryOpeningPayment (field field_computes )
variable {n : ℕ}
noncomputable def anchor : List Bool→List Bool := BinaryMetricAnchor.run ∘ anchorInput
noncomputable def recoveryParams (x : List Bool) : List Bool :=
  encode [src 0 x,src 1 x,src 2 x,src 3 x,anchor x,src 4 x,BinaryRational.encode 0,(0:ℕ).bits]
noncomputable def bare (x : List Bool) : List Bool := pairBits (recoveryParams x,pairBits (src 6 x,[]))
attribute [local irreducible] bare RawTake.run UnaryResources.lengthBits
attribute [local irreducible] mapWith
end MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_DuplicateMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryDuplicateMatrix
open WordOperations WordList
variable {n : ℕ}
noncomputable def run_computes : PolyComputes run := (map_computes twice_computes).comp twice_computes

end MetricKMedianRecovery.BitMachine.BinaryDuplicateMatrix

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Strictness_SurplusPostprocess
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySurplusPostprocess
open WordOperations WordList BinaryArithmetic RationalLeaves
open BinaryOpeningPayment (field field_computes )
open BinaryFiniteContext (labels setBits)
variable {m d : ℕ}
noncomputable def padded (x : List Bool) : List Bool :=
  BinaryCompletionPad.run (encode [field 2 x,field 3 x,target x])
noncomputable def localInput (x : List Bool) : List Bool :=
  encode [field 0 x,field 1 x,map BinaryProjection.originalWord (field 2 x),BinaryProjection.lift (padded x)]
noncomputable def run : List Bool→List Bool := BinaryProjection.run ∘ BinaryLocalRefine.run ∘ localInput
end MetricKMedianRecovery.BitMachine.BinarySurplusPostprocess

end OAI
end


