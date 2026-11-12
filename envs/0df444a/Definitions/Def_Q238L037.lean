-- Prove2me | Definitions.Def_Q238L037
-- name    : Q238L037
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T11:36:21.315509+00:00
-- url     : https://prove2.me/theorems/ca0e40c3-8bcd-4622-b2fd-4cfa5f69ba37
-- title:
--   Definitions bundle Q238L037 of the split of OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 94 declarations of OpenAI's Lean: 94 definitions. The definitions and types are `OAI.MetricKMedianRecovery.BitMachine.BinaryBisection.width_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueCollect.bad_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueMerge.output_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueMerge.run_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueMerge.sum_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.run`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.advanceItem_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.advance_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.bagTest_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.choices`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.drawItems_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.drawPick_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.nextTable`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.output`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.run`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.step`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionAlgorithm.input`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionAlgorithm.run`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionAlgorithm.selected`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionFair.run`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCross.edge`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCross.forward`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCross.leftPaid`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCross.rightPaid`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCross.transition`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDuplicateMatrix.run_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteInsert.keep_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGrid.chooseLeft_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGrid.endpoint_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGrid.finish_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGrid.midpoint_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGrid.pointWords_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGrid.queryInput_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGrid.run_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGrid.stateRun_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGrid.step_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch.anchor`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch.bare`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch.recoveryParams`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair.demandWord` and 54 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedianRecovery_Algorithms_CandidateSanitize`, `KMedianRecovery_Algorithms_CompletionAlgorithm`, `KMedianRecovery_Algorithms_IntegralRecoveryAll`, `KMedianRecovery_Algorithms_IntegralRecoveryAmplified`, `KMedianRecovery_Algorithms_IntegralRecoveryDemand`, `KMedianRecovery_Algorithms_IntegralRecoveryGuesses`, `KMedianRecovery_Algorithms_IntegralRecoveryMachine`, `KMedianRecovery_Algorithms_IntegralRecoveryRepeat`, `KMedianRecovery_Algorithms_IntegralRecoverySelection`, `KMedianRecovery_Algorithms_IntegralRecoverySuccess`, `KMedianRecovery_Branching_BlueMerge`, `KMedianRecovery_Branching_BranchObjective`, `KMedianRecovery_Branching_BranchPrefix`, `KMedianRecovery_Branching_CategoricalChoice`, `KMedianRecovery_Branching_CategoricalOutput`, `KMedianRecovery_Branching_CategoricalSize`, `KMedianRecovery_Branching_CategoricalTable`, `KMedianRecovery_Branching_CompletionFair`, `KMedianRecovery_Branching_ObservableCapacity`, `KMedianRecovery_Branching_RandomizedZeroBranch`, `KMedianRecovery_Encoding_BoundedNatWord`, `KMedianRecovery_Encoding_DuplicateMatrix`, `KMedianRecovery_Geometry_LocalFuel`, `KMedianRecovery_Geometry_MetricAnchor`, `KMedianRecovery_Machines_BisectionMachine`, `KMedianRecovery_Machines_GridMachine`, `KMedianRecovery_Machines_SliceFold`, `KMedianRecovery_Recovery_Answer`, `KMedianRecovery_Recovery_CrossEdge`, `KMedianRecovery_Recovery_FilterItem`, `KMedianRecovery_Recovery_FirstPresent`, `KMedianRecovery_Recovery_Min`, `KMedianRecovery_Recovery_OrientedSearch`, `KMedianRecovery_Recovery_RecoveryEnumeration`, `KMedianRecovery_Recovery_RowInput`, `KMedianRecovery_Sampling_SamplerParameters`.
--
--   **Imports.** It imports the published bundle `Def_KMedianRecovery`; the bundles `Q238L032`, `Q238L033`, `Q238L034` and `Q238L035` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q238L039` and `Q238L040`; the statements `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.run_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.nextTable_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.output_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCross.edge_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair.demandWord_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair.repack_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses.ranges_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat.FiniteTape.demandWord_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.recoveryContext_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.sampleContext_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryLocalAnchor.run_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryLocalAnchor.state_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMetricAnchor.produce_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryNodeScan.markers_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryObservableBranch.run_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRandomizedBranch.source_run_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRandomizedZeroBranch.Prefix.run_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRecovery.atBranch_context_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRecovery.atBranch_source_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRecovery.run_source_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryZeroBranch.completion_pack_s238r` and `OAI.MetricKMedianRecovery.BitMachine.BinaryZeroBranch.run_pack_s238r`; the proofs of `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.run_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.nextTable_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.output_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCross.edge_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair.demandWord_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair.repack_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses.ranges_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat.FiniteTape.demandWord_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.recoveryContext_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.sampleContext_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryLocalAnchor.run_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryLocalAnchor.state_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMetricAnchor.produce_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryNodeScan.markers_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryObservableBranch.run_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRandomizedBranch.source_run_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRandomizedZeroBranch.Prefix.run_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRecovery.atBranch_context_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRecovery.atBranch_source_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRecovery.run_source_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryZeroBranch.completion_pack_s238r` and `OAI.MetricKMedianRecovery.BitMachine.BinaryZeroBranch.run_pack_s238r`.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_KMedianRecovery
import Definitions.Def_Q238L032
import Definitions.Def_Q238L033
import Definitions.Def_Q238L034
import Definitions.Def_Q238L035

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_RowInput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryPhaseFirst
open WordOperations BinaryArithmetic WordList EffectiveOpenability RationalOpenability
open BinaryOpeningPayment

noncomputable def contains_computes : PolyComputes (fun x=>[contains x]) := by
  have h := ((Find.run_computes natEq_computes).comp isEmpty_computes).cond
    (const_computes [false]) (const_computes [true])
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  by_cases hx : Find.run natEq x=[] <;> simp [contains,hx]
end MetricKMedianRecovery.BitMachine.BinaryPhaseFirst

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_FilterItem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace BinaryFiniteInsert
open WordList BinaryPhaseFirst EffectiveOpenability
noncomputable def keep_computes : PolyComputes (fun x=>[keep x]) := by
  have h := ((new_computes.pair discardPrefix_computes).comp natEq_computes).cond
    (const_computes [true]) ((discardPrefix_computes.pair old_computes).comp contains_computes)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  cases he : natEq (pairBits (new x,discardPrefix x)) <;> simp only [keep,he,Function.comp_apply,Bool.false_eq_true,ite_false, if_false,ite_true, if_true]
end BinaryFiniteInsert
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Answer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryPhaseFinish
open WordOperations BinaryArithmetic WordList EffectiveOpenability RationalPhase BinaryPhaseUpdate
noncomputable def step (x : List Bool) : List Bool :=
  if answer x=[] then x else BinaryPhaseUpdate.run (pairBits (x,(answer x).tail))
end MetricKMedianRecovery.BitMachine.BinaryPhaseFinish

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
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CategoricalTable
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCategorical
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
variable {E : Type*} {a T : ℕ}
noncomputable def drawItems_computes : PolyComputes drawItems :=
  (((field_computes 1).comp Indices.run_computes).pair (field_computes 1)).comp Zip.run_computes
noncomputable def drawPick_computes : PolyComputes drawPick := by
  have h := (NatOps.eq (discardPrefix_computes.comp extractPrefix_computes)
    (extractPrefix_computes.comp (field_computes 2))).cond (const_computes [])
    (((discardPrefix_computes.comp discardPrefix_computes).pair drawRow_computes).comp Lookup.run_computes)
  unfold drawPick
  simpa only [decide_eq_true_eq,Function.comp_def] using h
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
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_CandidateSanitize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySanitizedBest
open WordOperations WordList
open BinaryOpeningPayment (field field_computes field_encode)
noncomputable def atRaw : List Bool→List Bool := BinaryCandidateSanitize.run ∘ atRawInput
end MetricKMedianRecovery.BitMachine.BinarySanitizedBest

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
open BinaryOpeningPayment (field field_computes field_encode)
variable {q a T L : ℕ}
noncomputable def bagTest_computes : PolyComputes (fun x=>[bagTest x]) :=
  NatOps.eq ((((extractPrefix_computes.comp extractPrefix_computes).pair discardPrefix_computes).comp elementPart_computes))
    (extractPrefix_computes.comp discardPrefix_computes)
noncomputable def choices (g : List Bool→List Bool) (x : List Bool) : List Bool :=
  mapWith (choose g) (pairBits (x,Indices.run (field 1 x)))
attribute [local irreducible] mapWith
end MetricKMedianRecovery.BitMachine.BinaryCategorical

namespace MetricKMedianRecovery.BitMachine.BinaryCategorical
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
variable {q a T L : ℕ}
noncomputable def nextTable (g : List Bool→List Bool) (x : List Bool) : List Bool :=
  advance (encode [field 1 (Fold.accum x),choices g (stepScore x),field 0 (Fold.accum x)])
attribute [local irreducible] advance choices
noncomputable def step (g : List Bool→List Bool) (x : List Bool) : List Bool :=
  if value (field 0 (Fold.accum x))<(field 2 (Find.context x)).length then
    encode [(value (field 0 (Fold.accum x))+1).bits,nextTable g x]
  else Fold.accum x
end MetricKMedianRecovery.BitMachine.BinaryCategorical

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CategoricalSize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCategorical
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
variable {q a T L : ℕ}
noncomputable def run (g : List Bool→List Bool) (x : List Bool) : List Bool :=
  CappedFold.run (step g) (pairBits (runCap.word x,Fold.pack (field 4 x) (context x) (initial x)))
end MetricKMedianRecovery.BitMachine.BinaryCategorical

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
open BinaryOpeningPayment (field field_computes field_encode)
variable {q a T L : ℕ}
noncomputable def output (g : List Bool→List Bool) (x : List Bool) : List Bool :=
  draw (encode [field 1 (run g (extractPrefix x)),discardPrefix x,
    UnaryResources.lengthBits (field 2 (extractPrefix x))])
end MetricKMedianRecovery.BitMachine.BinaryCategorical

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
open BinaryOpeningPayment (field field_computes field_encode)
open Categorical.Explicit
variable {n q a p r c : ℕ}
attribute [local irreducible] prepared
noncomputable def run (x : List Bool) : List Bool := BinaryCompletionAlgorithm.run (pairBits (extractPrefix x,prepared x))
end MetricKMedianRecovery.BitMachine.BinaryCompletionFair

namespace MetricKMedianRecovery.BitMachine.BinaryBranchProgram
open WordOperations WordList BinaryBranchContext
open BinaryOpeningPayment (field field_computes field_encode)
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
open BinaryOpeningPayment (field field_computes field_encode)
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
open BinaryOpeningPayment (field field_computes field_encode)
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
open BinaryOpeningPayment (field field_computes field_encode)
noncomputable def width_computes : PolyComputes (fun x=>BinaryRational.encode (width x)) :=
  RatOps.sub (RatOps.ofWords (field_computes 4)) (RatOps.ofWords (field_computes 3))
end MetricKMedianRecovery.BitMachine.BinaryBisection

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
open BinaryOpeningPayment (field field_computes field_encode)
variable {n : ℕ}
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
open BinaryOpeningPayment (field field_computes field_encode)
attribute [local irreducible] context zeroContext BinaryRandomizedBranch.Prefix.run BinaryRandomizedZeroBranch.Prefix.run
noncomputable def atBranch (d : ℕ) (x : List Bool) : List Bool :=
  BinaryRandomizedBranch.Prefix.run d (pairBits (context x,src 9 x))
noncomputable def atZero (x : List Bool) : List Bool :=
  BinaryRandomizedZeroBranch.Prefix.run (pairBits (zeroContext (promote x),src 9 x))
noncomputable def candidateWords (d : ℕ) (x : List Bool) : List Bool :=
  mapWith atZero (pairBits (x,range x))++ mapWith (atBranch d) (pairBits (x,choices x))
attribute [local irreducible] mapWith
noncomputable def run (d : ℕ) (x : List Bool) : List Bool := BinaryMetricBest.run
  (pairBits (metricContext x,pairBits (field 3 x,candidateWords d x)))
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
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_SamplerParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySampler.Parameters
open WordOperations WordList BinaryArithmetic Polynomial RadiusMenus Sampling Sampling.Comparison
open BinaryOpeningPayment (field field_computes field_encode)
noncomputable def unary (j : ℕ) (x : List Bool) : List Bool := BoundedNatWord.run bound (pairBits (field j x,x))
attribute [local irreducible] BoundedNatWord.run bound
noncomputable def Jword (x : List Bool) : List Bool := [true]++RepeatedAppend.copies (unary 7 x).length (List.replicate 2000000 true)
noncomputable def precision (x : List Bool) : List Bool :=
  nword x++unary 5 x++List.replicate M true++List.replicate E true++Jword x++List.replicate 5 true
noncomputable def menus (x : List Bool) : List Bool := encode [List.replicate M true,List.replicate E true,Jword x]
noncomputable def run (x : List Bool) : List Bool := encode [dimension x,field 0 x,field 2 x,field 3 x,field 4 x,
  diameter x,field 6 x,BinaryRational.encode (1/1000000),field 7 x,menus x]
end MetricKMedianRecovery.BitMachine.BinarySampler.Parameters

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_IntegralRecoveryMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery
open WordOperations WordList
open BinaryOpeningPayment (field field_computes field_encode)
noncomputable def mword : List Bool→List Bool := BinarySampler.Parameters.unary 7 ∘ params
noncomputable def cfg : List Bool→List Bool := BinarySampler.Parameters.run ∘ params
noncomputable def precision : List Bool→List Bool := BinarySampler.Parameters.precision ∘ params
noncomputable def sampleContext (x : List Bool) : List Bool :=
  encode [cfg x,mword x,mword x++mword x,precision x,sampleRaw x]
noncomputable def recoveryContext (x : List Bool) : List Bool :=
  encode [src 0 x,src 2 x,src 3 x,src 4 x,BinaryRational.natWords (src 5 x),pairBits ([],[]),src 1 x,mword x,extra x,completeRaw x]
attribute [local irreducible] src mword extra completeRaw BinaryRational.natWords
attribute [local irreducible] mapWith recoveryContext sampleContext
end MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_IntegralRecoverySuccess
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair
open WordOperations WordList Sampling.Comparison BinaryArithmetic
noncomputable def sampleCount (x : List Bool) : List Bool :=
  (2*(mword x).length*(precision x).length).bits
noncomputable def repack (x : List Bool) : List Bool := pairBits (extractPrefix x,
  pairBits (extra x,pairBits (RawTake.run (pairBits (sampleCount x,raw x)),RawDrop.run (pairBits (sampleCount x,raw x)))))
attribute [local irreducible] mword precision sampleCount raw extra RawTake.run RawDrop.run
end MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_IntegralRecoveryDemand
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair
open WordOperations Polynomial
open BinaryOpeningPayment (field field_computes field_encode)
noncomputable def sampleWord (x : List Bool) : List Bool := RepeatedAppend.copies (mword x++mword x).length (precision x)
noncomputable def demandWord (x : List Bool) : List Bool := sampleWord x++completionWord x
attribute [local irreducible] extra raw RawTake.run
end MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_IntegralRecoveryRepeat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat
open WordOperations WordList Sampling.Comparison
attribute [local irreducible] extra Fair.raw Fair.demandWord BinaryMetricBest.run RawUnary.run BinaryIntegralRecovery.result BinaryFinSet.encode BinarySampler.Parameters.pack BinaryMetricBest.best Fair.output List.ofFn BinarySeed.raw
noncomputable def bword : List Bool→List Bool := RawUnary.run ∘ Fair.demandWord
attribute [local irreducible] mapWith
end MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_IntegralRecoveryAmplified
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat.FiniteTape
open WordOperations WordList Sampling.Comparison FiniteSampling
attribute [local irreducible] Fair.pack Fair.raw Repeat.rword Repeat.bword RawTake.run extra
noncomputable def demandWord (Q : Polynomial ℕ) (x : List Bool) : List Bool :=
  RepeatedAppend.copies (Repeat.rword Q x).length (Repeat.bword x)
noncomputable def demandBits (Q : Polynomial ℕ) : List Bool→List Bool := UnaryResources.lengthBits ∘ demandWord Q
attribute [local irreducible] demandBits
noncomputable def cut (Q : Polynomial ℕ) (x : List Bool) : List Bool :=
  pairBits (extractPrefix x,pairBits (extra x,RawTake.run (pairBits (demandBits Q x,Fair.raw x))))
end MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat.FiniteTape

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_IntegralRecoveryGuesses
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses
open WordOperations WordList
open BinaryOpeningPayment (field field_computes field_encode)
attribute [local irreducible] BinaryFinSet.encode BinarySampler.Parameters.unary Count.run src
noncomputable def costWord (x : List Bool) : List Bool := RepeatedAppend.copies (Count.run (src 2 x)).length
  (BinarySampler.Parameters.unary 5 (extractPrefix x))
noncomputable def costRange (x : List Bool) : List Bool := BinaryEllipsoidInitial.indices (costWord x++[true])
noncomputable def choices (x : List Bool) : List Bool := cross (pairBits (costRange x,countRange x))
attribute [local irreducible] mapWith
attribute [local irreducible] sizeWord
end MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_IntegralRecoverySelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses
open WordOperations WordList
attribute [local irreducible] atInput choices Repeat.FiniteTape.demandWord
noncomputable def atDemand (Q : Polynomial ℕ) : List Bool→List Bool := Repeat.FiniteTape.demandWord Q ∘ atInput
noncomputable def demandWords (Q : Polynomial ℕ) (x : List Bool) : List Bool :=
  mapWith (atDemand Q) (pairBits (x,choices x))
attribute [local irreducible] mapWith
end MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses

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
open BinaryOpeningPayment (field field_computes field_encode)

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
open BinaryOpeningPayment (field field_computes field_encode)
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
open BinaryOpeningPayment (field field_computes field_encode)
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
open BinaryOpeningPayment (field field_computes field_encode)
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
open BinaryOpeningPayment (field field_computes field_encode)
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
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_CrossEdge
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCross
open WordOperations WordList RationalLeaves BinaryArithmetic
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
open BinaryOpeningPayment (field field_computes field_encode)
attribute [local irreducible] paid finalCount

noncomputable def leftPaid : List Bool → List Bool := paid ∘ leftData
noncomputable def rightPaid : List Bool → List Bool := paid ∘ rightData
noncomputable def forward (x : List Bool) : Bool :=
  if decide (value (leftPaid x)=value (rightPaid x)) then decide (value (leftLength x)<value (rightLength x))
  else decide (value (rightPaid x)<value (leftPaid x))
noncomputable def edge (x : List Bool) : List Bool := if forward x then directed x else directed (flipped x)
end MetricKMedianRecovery.BitMachine.BinaryCross

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_FirstPresent
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCross
open WordOperations WordList RationalLeaves BinaryArithmetic
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
open BinaryOpeningPayment (field field_computes field_encode)
attribute [local irreducible] finalCount paid edge
noncomputable def transition (x : List Bool) : List Bool :=
  if decide (value (rightCount x)=value (cf 2 x)) then true::successNode (rightNode x)
  else if sandwiched x then true::edge x else []
end MetricKMedianRecovery.BitMachine.BinaryCross

namespace MetricKMedianRecovery.BitMachine.BinaryNodeScan
open WordOperations WordList RationalLeaves CanonicalMergeRefinement CanonicalMergeCrossing
open BinaryCross (ctxBits nodeBits resultBits)
open BinaryFiniteMachine (historyBits)
open BinaryOpeningPayment (field field_computes field_encode)
attribute [local irreducible] BinaryCross.transition
noncomputable def cutOp (x : List Bool) : List Bool :=
  if suffix x=[] then [] else BinaryCross.transition (transitionInput x)
noncomputable def markers : List Bool → List Bool := mapWith cutOp ∘ scanInput
noncomputable def run (x : List Bool) : List Bool := FirstPresent.run (pairBits (fallback x,markers x))
end MetricKMedianRecovery.BitMachine.BinaryNodeScan

end OAI
end


