-- Prove2me | Definitions.Def_Q238K050
-- name    : Q238K050
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T23:47:50.128001+00:00
-- url     : https://prove2.me/theorems/3692afb6-8e2f-4b42-85d0-e68f26843fec
-- title:
--   Definitions bundle Q238K050 of the split of OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 52 declarations of OpenAI's Lean: 52 definitions. The definitions and types are `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.fallbackInput_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.maskCount_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalZero.one_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalZero.rowRun_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalZero.run_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalZero.values_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair.repack_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses.sizeWord_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat.context_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.metricContext_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.recoveryContext_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMaskOutput.member_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMaskOutput.run_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMaskParser.run_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryNormalizeInput.P.clients_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryNormalizeInput.P.facilities_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryNormalizeInput.clientCount_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryNormalizeInput.clients_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryNormalizeInput.facilitiesInput_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryNormalizeInput.facilities_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryNormalizeInput.plainFacilities_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseRun.budgetBound`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRecovery.choices_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Client.distances_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Client.near_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Client.population_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Client.radii_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Client.row_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Draw.actions_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Draw.weights_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Trace.input_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Trace.rows_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Update.active_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Update.add_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Update.ball_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Update.chosen_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Update.old_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Update.radius_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Weights.base_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Weights.context_computes` and 12 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedianRecovery_Algorithms_GlobalCall`, `KMedianRecovery_Algorithms_GlobalOuter`, `KMedianRecovery_Algorithms_GlobalZero`, `KMedianRecovery_Algorithms_IntegralRecoveryGuesses`, `KMedianRecovery_Algorithms_IntegralRecoveryMachine`, `KMedianRecovery_Algorithms_IntegralRecoveryRepeat`, `KMedianRecovery_Algorithms_IntegralRecoverySuccess`, `KMedianRecovery_Branching_ObservableCapacity`, `KMedianRecovery_Encoding_FinSets`, `KMedianRecovery_Encoding_MaskOutput`, `KMedianRecovery_Recovery_FinImages`, `KMedianRecovery_Recovery_NormalizeInput`, `KMedianRecovery_Recovery_RecoveryEnumeration`, `KMedianRecovery_Sampling_SamplerContext`, `KMedianRecovery_Sampling_SamplerDraw`, `KMedianRecovery_Sampling_SamplerResources`, `KMedianRecovery_Sampling_SamplerTraceMachine`, `KMedianRecovery_Sampling_SamplerUpdate`, `KMedianRecovery_Sampling_SamplerUpdateParts`, `KMedianRecovery_Sampling_SamplerWeights`, `KMedianRecovery_Sampling_SamplingStateMachine`, `KMedianRecovery_Strictness_BidBound`.
--
--   **Imports.** It imports the published bundle `Def_KMedianRefinedRecovery`; the bundles `Q238K041`, `Q238K042`, `Q238K043`, `Q238K045`, `Q238K046` and `Q238K047` of this split.
--
--   **Imported by** (directly, in this split): the bundle `Q238K052`; the statement `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseRun.finish_bound_s238`; the proofs of `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseRun.finish_bound_s238` and `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseRun.run_length_bound_s238`.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_KMedianRefinedRecovery
import Definitions.Def_Q238K041
import Definitions.Def_Q238K042
import Definitions.Def_Q238K043
import Definitions.Def_Q238K045
import Definitions.Def_Q238K046
import Definitions.Def_Q238K047

section
-- module Solutions.Q238_KM.KMedianRecovery_Strictness_BidBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryPhaseRun
open WordOperations BinaryArithmetic WordList EffectiveOpenability RationalPhase BinaryPhaseUpdate RationalHeight
open BinaryPhaseFinish
noncomputable def budgetBound : Polynomial ℕ := Polynomial.X+bidBound+100*(Polynomial.X+1)^2
end MetricKMedianRecovery.BitMachine.BinaryPhaseRun

end OAI
end

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
noncomputable def check_computes : PolyComputes (fun x=>[check x]) := by
  simpa only [check,Bool.decide_and,Function.comp_def] using
    (BinaryBranchCheck.outside_computes.comp isEmpty_computes).and
      ((BinaryBranchCheck.badBalls_computes.comp isEmpty_computes).and
        ((BinaryBranchCheck.badRadii_computes.comp isEmpty_computes).and
          ((NatOps.le (field_computes 9) ((classOf_computes 1).comp lengthBits_computes)).and
            (NatOps.le BinaryBranchCheck.lhs_computes rhs_computes))))
end MetricKMedianRecovery.BitMachine.BinaryZeroBranch

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
noncomputable def choices_computes : PolyComputes choices :=
  (range_computes.pair ((range_computes.pair blueRange_computes).comp cross_computes)).comp cross_computes
attribute [local irreducible] mapWith
attribute [local irreducible] metricContext candidateWords
end MetricKMedianRecovery.BitMachine.BinaryRecovery

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
noncomputable def actions_computes : PolyComputes actions := by
  have computation := ((input_computes.comp (c_computes 2)).pair (input_computes.comp (c_computes 9))).comp BinaryActions.run_computes
  unfold actions
  simpa only [Function.comp_def] using computation
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
noncomputable def context_computes : PolyComputes context := extractPrefix_computes.pair extra_computes
attribute [local irreducible] mapWith
end MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat

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
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_MaskOutput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryMaskOutput
open WordOperations WordList
variable {n : ℕ}
noncomputable def member_computes : PolyComputes member :=
  (discardPrefix_computes.pair extractPrefix_computes).comp BinaryNatSet.contains_computes
noncomputable def run_computes : PolyComputes run := by
  unfold run
  have computes := (discardPrefix_computes.pair (extractPrefix_computes.comp BinaryEllipsoidInitial.indices_computes)).comp
    ((mapWith_computes member_computes).comp Flatten.run_computes)
  simpa only [Function.comp_def] using computes
end MetricKMedianRecovery.BitMachine.BinaryMaskOutput

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


