-- Prove2me | Definitions.Def_Q238L050
-- name    : Q238L050
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T11:48:45.723317+00:00
-- url     : https://prove2.me/theorems/9dc7bcd2-0619-4682-9ce5-41c33f3928a5
-- title:
--   Definitions bundle Q238L050 of the split of OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 84 declarations of OpenAI's Lean: 84 definitions. The definitions and types are `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.fallbackInput_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.nonempty_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.fallbackInput_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.maskCount_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.scales_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalZero.one_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalZero.rowRun_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalZero.run_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalZero.values_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInitial.bracketInput_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInitialProject.extract_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralAll.Dsp.run`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch.anchorInput_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch.call`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch.callInput`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch.calls`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch.cutRaw`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch.run`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch.runInput`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair.repack_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair.sampleCount_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses.sizeWord_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat.FiniteTape.cut_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat.FiniteTape.demandBits_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat.context_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat.rows_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.cfg_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.metricContext_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.recoveryContext_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.sampleContext_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMaskParser.run_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMetricAnchor.anchorInput_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMetricAnchor.rectangle_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMetricArrays.column_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMetricArrays.run_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMetricBest.run_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMetricBest.score_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMetricCost.run_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMetricSurplus.initial_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMetricSurplus.rectangle_computes` and 44 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedianRecovery_Algorithms_GlobalCall`, `KMedianRecovery_Algorithms_GlobalOuter`, `KMedianRecovery_Algorithms_GlobalZero`, `KMedianRecovery_Algorithms_IntegralAll`, `KMedianRecovery_Algorithms_IntegralRecoveryAll`, `KMedianRecovery_Algorithms_IntegralRecoveryAmplified`, `KMedianRecovery_Algorithms_IntegralRecoveryGuesses`, `KMedianRecovery_Algorithms_IntegralRecoveryMachine`, `KMedianRecovery_Algorithms_IntegralRecoveryRepeat`, `KMedianRecovery_Algorithms_IntegralRecoverySuccess`, `KMedianRecovery_Branching_ObservableCapacity`, `KMedianRecovery_Branching_PopulationMachine`, `KMedianRecovery_Encoding_FinSets`, `KMedianRecovery_Geometry_MetricAnchor`, `KMedianRecovery_Geometry_MetricArrays`, `KMedianRecovery_Geometry_MetricCost2`, `KMedianRecovery_Machines_InitialLoop`, `KMedianRecovery_Machines_ProjectionMachine`, `KMedianRecovery_Machines_StepMachine`, `KMedianRecovery_Recovery_FinImages`, `KMedianRecovery_Recovery_InitialProject`, `KMedianRecovery_Recovery_NormalizeInput`, `KMedianRecovery_Recovery_OrientedSearch`, `KMedianRecovery_Sampling_SamplerContext`, `KMedianRecovery_Sampling_SamplerDraw`, `KMedianRecovery_Sampling_SamplerParameters`, `KMedianRecovery_Sampling_SamplerResources`, `KMedianRecovery_Sampling_SamplerTraceMachine`, `KMedianRecovery_Sampling_SamplerUpdate`, `KMedianRecovery_Sampling_SamplerUpdateParts`, `KMedianRecovery_Sampling_SamplerWeights`, `KMedianRecovery_Sampling_SamplingStateMachine`, `KMedianRecovery_Strictness_MetricSurplus`, `KMedianRecovery_Strictness_SurplusPostprocess`.
--
--   **Imports.** It imports the published bundle `Def_KMedianRecovery`; the bundles `Q238L041`, `Q238L042`, `Q238L043`, `Q238L045`, `Q238L046` and `Q238L047` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q238L052` and `Q238L053`.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_KMedianRecovery
import Definitions.Def_Q238L041
import Definitions.Def_Q238L042
import Definitions.Def_Q238L043
import Definitions.Def_Q238L045
import Definitions.Def_Q238L046
import Definitions.Def_Q238L047

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_FinSets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryMaskParser
open WordOperations WordList
noncomputable def run_computes : PolyComputes run :=
  (id_computes.pair (RawUnary.run_computes.comp BinaryEllipsoidInitial.indices_computes)).comp
    ((filterWith_computes member_computes).comp BinaryNatSet.sort_computes)
end MetricKMedianRecovery.BitMachine.BinaryMaskParser

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_FinImages
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryTaggedSets
open WordOperations WordList BinaryArithmetic
variable {n : ℕ}
noncomputable def shift_computes : PolyComputes shift := (mapWith_computes plus_computes).comp BinaryNatSet.sort_computes
noncomputable def unshift_computes : PolyComputes unshift := (mapWith_computes minus_computes).comp BinaryNatSet.sort_computes
end MetricKMedianRecovery.BitMachine.BinaryTaggedSets

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_PopulationMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryPopulation
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
attribute [local irreducible] WordList.mapWith
noncomputable def candidate_computes : PolyComputes (fun x=>BinaryRational.encode (candidate x)) :=
  RatOps.max (RatOps.ofWords discardPrefix_computes)
    (RatOps.div (RatOps.ofWords (extractPrefix_computes.comp (field_computes 0)))
      (RatOps.mul (RatOps.nat (extractPrefix_computes.comp (field_computes 1)))
        (RatOps.nat ((discardPrefix_computes.pair (extractPrefix_computes.comp (field_computes 2))).comp count_computes))))
noncomputable def candidates_computes : PolyComputes candidates :=
  (id_computes.pair (field_computes 2)).comp (mapWith_computes candidate_computes)
noncomputable def run_computes : PolyComputes run := candidates_computes.comp RationalMin.run_computes
end MetricKMedianRecovery.BitMachine.BinaryPopulation

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_SamplingStateMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySamplingOracle
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
variable {n : ℕ}
noncomputable def weight_computes : PolyComputes (fun x=>BinaryRational.encode (weight x)) :=
  RatOps.max (RatOps.const 0) (RatOps.ofWords (reference_computes.comp extractPrefix_computes))
noncomputable def weights_computes : PolyComputes weights := by
  have computation := (id_computes.pair (field_computes 1)).comp (mapWith_computes weight_computes)
  unfold weights
  simpa only [Function.comp_def, id_eq] using computation
noncomputable def total_computes : PolyComputes (fun x=>BinaryRational.encode (total x)) :=
  RatOps.ofWords (weights_computes.comp RationalArray.sumWords_computes)
end MetricKMedianRecovery.BitMachine.BinarySamplingOracle

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_SamplerContext
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySampler
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
variable {n : ℕ}
noncomputable def undeleted_computes : PolyComputes undeleted := ((c_computes 4).pair deleted_computes).comp BinaryNatSet.diff_computes
noncomputable def reference_computes : PolyComputes reference := cons_computes (c_computes 0)
  (cons_computes (c_computes 5) (cons_computes undeleted_computes (cons_computes leaves_computes (const_computes []))))
noncomputable def oracle_computes : PolyComputes oracle := cons_computes (c_computes 1)
  (cons_computes (c_computes 2) (cons_computes reference_computes (const_computes [])))
end MetricKMedianRecovery.BitMachine.BinarySampler

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_SamplerWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySampler.Weights
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
variable {n : ℕ}
noncomputable def context_computes : PolyComputes context :=
  cons_computes (stateInput_computes.comp oracle_computes)
    (cons_computes ((stateInput_computes.comp oracle_computes).comp BinarySamplingOracle.total_computes)
      (cons_computes (c_computes 9) (cons_computes discardPrefix_computes (const_computes []))))
noncomputable def base_computes : PolyComputes (fun x=>BinaryRational.encode (base x)) :=
  RatOps.div (((c_computes 0).pair (actionField_computes 1)).comp BinarySamplingOracle.weight_computes)
    (RatOps.mul (RatOps.const 2) (RatOps.ofWords (c_computes 1)))
noncomputable def weight_computes : PolyComputes (fun x=>BinaryRational.encode (weight x)) := by
  have hh := active_computes.cond ((kind_computes 0).cond (RatOps.const 0)
    ((kind_computes 1).cond base_computes
      (RatOps.mul base_computes (((c_computes 2).pair (actionField_computes 2)).comp BinaryMenu.weight_computes))))
    ((kind_computes 0).cond (RatOps.const 1) (RatOps.const 0))
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  unfold weight
  split_ifs <;> rfl
end MetricKMedianRecovery.BitMachine.BinarySampler.Weights

namespace MetricKMedianRecovery.BitMachine.BinarySampler.Client
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
attribute [local irreducible] BinarySamplingOracle.row BinaryIndexMap.run
variable {n : ℕ}
noncomputable def row_computes : PolyComputes row := ((extractPrefix_computes.comp oracle_computes).pair discardPrefix_computes).comp BinarySamplingOracle.row_computes
noncomputable def distances_computes : PolyComputes distances := (row_computes.pair (extractPrefix_computes.comp (c_computes 2))).comp BinaryIndexMap.run_computes
noncomputable def population_computes : PolyComputes population :=
  (cons_computes (extractPrefix_computes.comp (c_computes 6)) (cons_computes (extractPrefix_computes.comp (c_computes 8))
    (cons_computes distances_computes (const_computes [])))).comp BinaryPopulation.run_computes
noncomputable def near_computes : PolyComputes near := (row_computes.pair (extractPrefix_computes.comp leaves_computes)).comp BinaryNearestLeaf.run_computes
noncomputable def radii_computes : PolyComputes radii := cons_computes (extractPrefix_computes.comp (c_computes 7))
  (cons_computes population_computes (cons_computes near_computes (const_computes [])))
end MetricKMedianRecovery.BitMachine.BinarySampler.Client

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
open Weights (actionField actionField_computes)
attribute [local irreducible] BinaryMenu.radius WordList.filterWith Client.row
variable {n : ℕ}
noncomputable def chosen_computes : PolyComputes chosen :=
  ((((input_computes.comp oracle_computes).pair (actionField_computes 1)).comp BinarySamplingOracle.reference_computes).comp discardPrefix_computes)
noncomputable def radius_computes : PolyComputes radius :=
  ((clientInput_computes.comp Client.radii_computes).pair (actionField_computes 2)).comp BinaryMenu.radius_computes
noncomputable def ball_computes : PolyComputes ball :=
  (((clientInput_computes.comp Client.row_computes).pair (radius_computes.comp WordList.head_computes)).pair
    (input_computes.comp (c_computes 3))).comp (filterWith_computes within_computes)
end MetricKMedianRecovery.BitMachine.BinarySampler.Update

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_MetricArrays
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryMetricArrays
open WordOperations WordList
open BinaryOpeningPayment (field field_computes field_encode)
variable {n p q : ℕ}
attribute [local irreducible] BinaryIndexMap.run
noncomputable def column_computes : PolyComputes column :=
  (row_computes.pair (extractPrefix_computes.comp (field_computes 2))).comp BinaryIndexMap.run_computes
attribute [local irreducible] mapWith
noncomputable def run_computes : PolyComputes run :=
  (id_computes.pair (field_computes 1)).comp (mapWith_computes column_computes)
end MetricKMedianRecovery.BitMachine.BinaryMetricArrays

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_MetricCost2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryMetricCost
open WordOperations WordList
variable {n : ℕ}
noncomputable def run_computes : PolyComputes run := by
  unfold run
  have computes := ((const_computes []).pair BinaryMetricArrays.run_computes).comp
    ((mapWith_computes near_computes).comp RationalArray.sumWords_computes)
  simpa only [Function.comp_def] using computes
end MetricKMedianRecovery.BitMachine.BinaryMetricCost

namespace MetricKMedianRecovery.BitMachine.BinaryMetricBest
open WordOperations WordList
open BinaryOpeningPayment (field field_computes field_encode)
variable {n : ℕ}
noncomputable def score_computes : PolyComputes score :=
  (cons_computes (extractPrefix_computes.comp (field_computes 0))
    (cons_computes (extractPrefix_computes.comp (field_computes 1))
      (cons_computes discardPrefix_computes (const_computes [])))).comp
        (BinaryMetricCost.run_computes.comp BinaryRational.negWords_computes)
noncomputable def run_computes : PolyComputes run := BinaryRationalBest.run_computes score_computes
end MetricKMedianRecovery.BitMachine.BinaryMetricBest

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_ObservableCapacity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryZeroBranch
open WordOperations WordList BinaryBranchContext BinaryBranchProgram BinaryArithmetic
attribute [local instance] Classical.propDecidable
open BinaryOpeningPayment (field field_computes field_encode)
variable {n : ℕ}
noncomputable def rhs_computes : PolyComputes rhs := by
  unfold rhs
  simpa only [Function.comp_def,value_bits] using
    NatOps.add (((field_computes 5).comp extractPrefix_computes).comp lengthBits_computes) (field_computes 9)
end MetricKMedianRecovery.BitMachine.BinaryZeroBranch

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
attribute [local irreducible] BoundedNatWord.run bound
noncomputable def menus_computes : PolyComputes menus := cons_computes (const_computes (List.replicate M true))
  (cons_computes (const_computes (List.replicate E true)) (cons_computes Jword_computes (const_computes [])))
noncomputable def run_computes : PolyComputes run := list_computes
  [dimension,field 0,field 2,field 3,field 4,diameter,field 6,fun _=>BinaryRational.encode (1/1000000),field 7,menus] (by
    intro f hf; refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact ⟨dimension_computes⟩
    · exact ⟨field_computes 0⟩
    · exact ⟨field_computes 2⟩
    · exact ⟨field_computes 3⟩
    · exact ⟨field_computes 4⟩
    · exact ⟨diameter_computes⟩
    · exact ⟨field_computes 6⟩
    · exact ⟨const_computes _⟩
    · exact ⟨field_computes 7⟩
    · exact ⟨menus_computes⟩)
end MetricKMedianRecovery.BitMachine.BinarySampler.Parameters

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_SamplerDraw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySampler.Draw
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
variable {n : ℕ}
noncomputable def weights_computes : PolyComputes weights := by
  have computation := ((input_computes.comp Weights.context_computes).pair actions_computes).comp (mapWith_computes Weights.weight_computes)
  unfold weights
  simpa only [Function.comp_def] using computation
end MetricKMedianRecovery.BitMachine.BinarySampler.Draw

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_SamplerUpdate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySampler.Update
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
open Weights (actionField actionField_computes)
attribute [local irreducible] radius
variable {n : ℕ}
noncomputable def active_computes : PolyComputes (fun x=>[active x]) :=
  (((extractPrefix_computes.comp Weights.context_computes).pair (const_computes [])).comp Weights.active_computes)
noncomputable def old_computes : PolyComputes (fun x=>[old x]) := NatOps.lt chosen_computes (input_computes.comp (c_computes 0))
noncomputable def add_computes : PolyComputes add :=
  ((input_computes.comp (c_computes 8)).pair (((input_computes.comp discardPrefix_computes).pair
    ((actionField_computes 1).pair (radius_computes.comp WordList.head_computes))).comp BinarySamplingState.add_computes)).comp BinarySamplingState.retain_computes

end MetricKMedianRecovery.BitMachine.BinarySampler.Update

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_SamplerResources
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySeed
open WordOperations WordList
attribute [local irreducible] WordList.mapWith
noncomputable def rows_computes : PolyComputes rows :=
  (id_computes.pair indices_computes).comp (mapWith_computes (chunk_computes 0))
attribute [local irreducible] indices chunk
end MetricKMedianRecovery.BitMachine.BinarySeed

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_SamplerTraceMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySampler.Trace
open WordOperations WordList
open BinaryOpeningPayment (field field_computes field_encode)
attribute [local irreducible] BinarySeed.rows Take.run Loop.run BinaryEllipsoidInitial.indices WordList.mapWith
noncomputable def rows_computes : PolyComputes rows :=
  ((cons_computes (field_computes 2) (cons_computes (field_computes 3) (const_computes []))).pair
    (field_computes 4)).comp BinarySeed.rows_computes
noncomputable def input_computes : PolyComputes input :=
  cons_computes (field_computes 0) (cons_computes (field_computes 1)
    (cons_computes (field_computes 3) (cons_computes rows_computes (const_computes []))))
end MetricKMedianRecovery.BitMachine.BinarySampler.Trace

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
noncomputable def cfg_computes : PolyComputes cfg := extractPrefix_computes.comp BinarySampler.Parameters.run_computes
noncomputable def sampleContext_computes : PolyComputes sampleContext := cons_computes cfg_computes
  (cons_computes mword_computes (cons_computes (mword_computes.append mword_computes)
    (cons_computes precision_computes (cons_computes sampleRaw_computes (const_computes [])))))
attribute [local irreducible] src mword extra completeRaw BinaryRational.natWords
noncomputable def recoveryContext_computes : PolyComputes recoveryContext := list_computes
  [src 0,src 2,src 3,src 4,BinaryRational.natWords ∘ src 5,fun _=>pairBits ([],[]),src 1,mword,extra,completeRaw] (by
    intro f hf; refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals first | exact ⟨src_computes _⟩ | exact ⟨(src_computes 5).comp BinaryRational.natWords_computes⟩ |
      exact ⟨const_computes _⟩ | exact ⟨mword_computes⟩ | exact ⟨extra_computes⟩ | exact ⟨completeRaw_computes⟩)
attribute [local irreducible] mapWith recoveryContext sampleContext BinarySampler.Trace.run
noncomputable def metricContext_computes : PolyComputes metricContext := cons_computes (src_computes 0) (cons_computes (src_computes 2) (const_computes []))
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
noncomputable def sampleCount_computes : PolyComputes sampleCount := by
  have hh := NatOps.mul (NatOps.mul (const_computes (2:ℕ).bits)
    (mword_computes.comp UnaryResources.lengthBits_computes))
    (precision_computes.comp UnaryResources.lengthBits_computes)
  change PolyComputes (fun x=>(2*(mword x).length*(precision x).length).bits)
  simpa only [UnaryResources.lengthBits_eq,value_bits,Function.comp_def] using hh
attribute [local irreducible] mword precision sampleCount raw extra RawTake.run RawDrop.run
noncomputable def repack_computes : PolyComputes repack := extractPrefix_computes.pair
  (extra_computes.pair (((sampleCount_computes.pair raw_computes).comp RawTake.run_computes).pair
    ((sampleCount_computes.pair raw_computes).comp RawDrop.run_computes)))
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
attribute [local irreducible] extra Fair.raw Fair.demandWord Fair.run BinaryMetricBest.run RawUnary.run BinarySeed.rows
  BinaryIntegralRecovery.result BinaryFinSet.encode BinarySampler.Parameters.pack BinaryMetricBest.best Fair.output List.ofFn BinarySeed.raw
noncomputable def rows_computes (Q : Polynomial ℕ) : PolyComputes (rows Q) :=
  ((cons_computes (rword_computes Q) (cons_computes bword_computes (const_computes []))).pair Fair.raw_computes).comp
    BinarySeed.rows_computes
noncomputable def context_computes : PolyComputes context := extractPrefix_computes.pair extra_computes
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
attribute [local irreducible] Repeat.run Fair.pack Fair.raw Repeat.rword Repeat.bword RawTake.run extra
noncomputable def demandBits_computes (Q : Polynomial ℕ) : PolyComputes (demandBits Q) :=
  (demandWord_computes Q).comp UnaryResources.lengthBits_computes
attribute [local irreducible] demandBits
noncomputable def cut_computes (Q : Polynomial ℕ) : PolyComputes (cut Q) :=
  extractPrefix_computes.pair (extra_computes.pair (((demandBits_computes Q).pair Fair.raw_computes).comp RawTake.run_computes))
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
attribute [local irreducible] Repeat.FiniteTape.run BinarySanitizedBest.run BinaryFinSet.encode BinarySampler.Parameters.unary Count.run src
attribute [local irreducible] mapWith
noncomputable def sizeWord_computes : PolyComputes sizeWord :=
  ((src_computes 4).comp Count.run_computes).comp UnaryResources.lengthBits_computes
attribute [local irreducible] sizeWord candidateWords
end MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses

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
noncomputable def reverseRun_computes {query : List Bool→List Bool} (hq : PolyComputes query) : PolyComputes (reverseRun query) :=
  ((field_computes 4).pair (reverseInput_computes.comp (BinaryBisection.run_computes (reversed_computes hq)))).comp reflect_computes
noncomputable def run_computes {query : List Bool→List Bool} (hq : PolyComputes query) : PolyComputes (run query) :=
  (isReversed_computes hq).cond (reverseRun_computes hq) (BinaryBisection.run_computes hq)
end MetricKMedianRecovery.BitMachine.BinaryOrientedSearch

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_ProjectionMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryProjection
open WordOperations WordList BinaryArithmetic RationalLeaves
open BinaryFiniteContext (labels setBits)
noncomputable def run_computes : PolyComputes run :=
  (map_computes BinaryLabel.parentWords_computes).comp BinaryNatSet.sort_computes
end MetricKMedianRecovery.BitMachine.BinaryProjection

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
noncomputable def rectangle_computes : PolyComputes rectangle := rectInput_computes.comp BinaryMetricArrays.run_computes
attribute [local irreducible] WordList.map
noncomputable def anchorInput_computes : PolyComputes anchorInput :=
  cons_computes rectangle_computes (cons_computes ((field_computes 2).comp Count.run_computes)
    (cons_computes (PolyComputes.comp (f := field 3) (g := map BinaryProjection.originalWord)
      (field_computes 3) (map_computes BinaryProjection.originalWord_computes))
      (cons_computes (field_computes 4) (const_computes []))))
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
noncomputable def anchorInput_computes : PolyComputes anchorInput := list_computes
  [src 0,src 1,src 2,src 3,discardPrefix] (by
    intro f hf; refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl|rfl|rfl
    all_goals first | exact ⟨src_computes _⟩ | exact ⟨discardPrefix_computes⟩)
attribute [local irreducible] counter demand bare RawTake.run UnaryResources.lengthBits BinaryIntegralRecovery.Guesses.budget BinaryIntegralRecovery.Guesses.run
noncomputable def cutRaw (Q : Polynomial ℕ) (x : List Bool) : List Bool :=
  RawTake.run (pairBits (UnaryResources.lengthBits (demand Q x),src 7 x))
noncomputable def callInput (Q : Polynomial ℕ) (x : List Bool) : List Bool :=
  pairBits (recoveryParams x,pairBits (src 6 x,cutRaw Q x))
noncomputable def call (Q : Polynomial ℕ) (d : ℕ) : List Bool→List Bool := R.run Q d ∘ callInput Q
noncomputable def calls (Q : Polynomial ℕ) (d : ℕ) (x : List Bool) : List Bool := mapWith (call Q d) (pairBits (x,ranks x))
attribute [local irreducible] mapWith
noncomputable def runInput (Q : Polynomial ℕ) (d : ℕ) (x : List Bool) : List Bool :=
  encode [field 0 x,field 2 x,field 3 x,start x,field 5 x,calls Q d x]
attribute [local irreducible] start calls
noncomputable def run (Q : Polynomial ℕ) (d : ℕ) : List Bool→List Bool := BinarySanitizedBest.run ∘ runInput Q d
end MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_StepMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCoupledStep
open WordOperations WordList BinaryArithmetic RationalLeaves CanonicalCoupledMerge PhaseHistoryTransfer
open BinaryOpeningPayment (field field_computes field_encode)
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
open BinaryCoupled (stateBits outcomeBits)
noncomputable def fallbackInput_computes : PolyComputes fallbackInput :=
  list_computes [sf 0,sf 3,sf 1,(fun _=>[])] (by
    intro f hf; refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl|rfl
    · exact ⟨sf_computes 0⟩
    · exact ⟨sf_computes 3⟩
    · exact ⟨sf_computes 1⟩
    · exact ⟨const_computes []⟩
)
noncomputable def nonempty_computes : PolyComputes (fun x=>[nonempty x]) :=
  ((sf_computes 5).comp isEmpty_computes).not.and (((sf_computes 6).comp isEmpty_computes).not)
end MetricKMedianRecovery.BitMachine.BinaryCoupledStep

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_InitialLoop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryInitial
open WordOperations WordList BinaryArithmetic RationalLeaves CanonicalCoupledMerge
open BinaryOpeningPayment (field field_computes field_encode)
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
open BinaryCoupled (stateBits outputBits)
attribute [local irreducible] BinaryInitialQuery.count BinaryInitialQuery.history BinaryBisection.run
noncomputable def bracketInput_computes : PolyComputes bracketInput := list_computes [field 2,ctx,field 4,field 5,high] (by
  intro f hf; refine Classical.choice ?_
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
  rcases hf with rfl|rfl|rfl|rfl|rfl
  · exact ⟨field_computes 2⟩
  · exact ⟨ctx_computes⟩
  · exact ⟨field_computes 4⟩
  · exact ⟨field_computes 5⟩
  · exact ⟨high_computes⟩)

end MetricKMedianRecovery.BitMachine.BinaryInitial

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_InitialProject
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryInitialProject
open WordOperations WordList BinaryArithmetic RationalLeaves CanonicalCoupledMerge
open BinaryOpeningPayment (field field_computes field_encode)
open BinaryFiniteContext (labels setBits)
variable {m d : ℕ}
attribute [local irreducible] BinaryProjection.run BinaryFiniteMachine.after
noncomputable def extract_computes : PolyComputes extract :=
  ((const_computes []).pair (discardPrefix_computes.comp (field_computes 2))).comp
    (BinaryFiniteMachine.after_computes.comp BinaryProjection.run_computes)
end MetricKMedianRecovery.BitMachine.BinaryInitialProject

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
open BinaryOpeningPayment (field field_computes field_encode)
open BinaryFiniteContext (labels setBits)
variable {m d : ℕ}
noncomputable def target_computes : PolyComputes target :=
  NatOps.max (field_computes 4) ((field_computes 3).comp lengthBits_computes)
end MetricKMedianRecovery.BitMachine.BinarySurplusPostprocess

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Strictness_MetricSurplus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryMetricSurplus
open WordOperations WordList
open BinaryOpeningPayment (field field_computes field_encode)
variable {n : ℕ}
noncomputable def rectangle_computes : PolyComputes rectangle := anchorInput_computes.comp BinaryMetricAnchor.rectangle_computes
noncomputable def initial_computes : PolyComputes initial :=
  cons_computes rectangle_computes (cons_computes ((field_computes 2).comp Count.run_computes)
    (cons_computes (field_computes 3) (cons_computes (field_computes 2)
      (cons_computes ((field_computes 4).comp BinaryRational.natWords_computes)
        (cons_computes (field_computes 5) (const_computes []))))))
noncomputable def runInput_computes : PolyComputes runInput := initial_computes.pair total_computes
end MetricKMedianRecovery.BitMachine.BinaryMetricSurplus

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_IntegralAll
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryIntegralAll
open WordOperations WordList
open BinaryOpeningPayment (field field_computes field_encode)
namespace Dsp
noncomputable abbrev run := BinaryIntegralDispatch.run
end Dsp
attribute [local irreducible] mapWith
end MetricKMedianRecovery.BitMachine.BinaryIntegralAll

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_NormalizeInput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryNormalizeInput
open WordOperations WordList
open BinaryOpeningPayment (field field_computes field_encode)
namespace P
noncomputable def clients_computes : PolyComputes clients := BinaryInputParser.Metric.clients_computes.comp BinaryMaskParser.run_computes
noncomputable def facilities_computes : PolyComputes facilities := BinaryInputParser.Metric.facilities_computes.comp BinaryMaskParser.run_computes
end P
attribute [local irreducible] P.points P.clients P.facilities
  BinaryInputParser.Metric.matrix BinaryInputParser.Metric.count BinaryInputParser.Metric.budget
  BinaryNormalization.run BinaryNormalization.cap BinaryNormalization.mesh
noncomputable def clients_computes : PolyComputes clients := raw_computes.comp P.clients_computes
noncomputable def clientCount_computes : PolyComputes clientCount := clients_computes.comp Count.run_computes
noncomputable def plainFacilities_computes : PolyComputes plainFacilities := raw_computes.comp P.facilities_computes
noncomputable def facilitiesInput_computes : PolyComputes facilitiesInput := count_computes.pair plainFacilities_computes
noncomputable def facilities_computes : PolyComputes facilities := facilitiesInput_computes.comp BinaryTaggedSets.shift_computes
end MetricKMedianRecovery.BitMachine.BinaryNormalizeInput

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_GlobalCall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryGlobalZero
open WordOperations WordList
open BinaryRationalSort (entryBits)
variable {n : ℕ}
noncomputable def rowRun_computes : PolyComputes rowRun :=
  ((mapWith_computes BinarySamplingReference.original_computes).comp BinaryRationalMinKey.run_computes).comp discardPrefix_computes
end MetricKMedianRecovery.BitMachine.BinaryGlobalZero

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_GlobalZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryGlobalZero
open WordOperations WordList LocalSearch
open BinaryOpeningPayment (field field_computes field_encode)
variable {n : ℕ}
noncomputable def one_computes : PolyComputes one :=
  (BinaryMetricArrays.row_computes.pair (extractPrefix_computes.comp (field_computes 2))).comp rowRun_computes
noncomputable def values_computes : PolyComputes values := by
  unfold values
  simpa only [Function.comp_def,id_eq] using
    (id_computes.pair (field_computes 1)).comp (mapWith_computes one_computes)
noncomputable def run_computes : PolyComputes run := values_computes.comp BinaryNatSet.sort_computes
end MetricKMedianRecovery.BitMachine.BinaryGlobalZero

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_GlobalOuter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryGlobalOuter
open WordOperations WordList
open BinaryOpeningPayment (field field_computes field_encode)
noncomputable def scales_computes : PolyComputes scales :=
  BinaryInputParser.Metric.rawMatrix_computes.comp BinaryInputParser.Stream.run_computes
noncomputable def fallbackInput_computes : PolyComputes fallbackInput :=
  cons_computes BinaryNormalizeInput.P.facilities_computes
    (cons_computes (const_computes []) (cons_computes (const_computes (1:ℕ).bits) (const_computes [])))
attribute [local irreducible] BinaryInputParser.Metric.matrix BinaryNormalizeInput.P.clients
  BinaryNormalizeInput.P.facilities BinaryInputParser.Metric.budget fallback
noncomputable def maskCount_computes : PolyComputes maskCount :=
  (extractPrefix_computes.comp BinaryInputParser.Metric.clients_computes).comp RawUnary.run_computes
end MetricKMedianRecovery.BitMachine.BinaryGlobalOuter

end OAI
end


