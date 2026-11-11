-- Prove2me | Definitions.Def_Q238K047
-- name    : Q238K047
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T23:44:23.618872+00:00
-- url     : https://prove2.me/theorems/74d2590d-61e1-4ac5-85cf-bd9fd15a4711
-- title:
--   Definitions bundle Q238K047 of the split of OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 41 declarations of OpenAI's Lean: 41 definitions. The definitions and types are `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.callInput_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat.atSeedInput_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMenu.denominatorPower_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMenu.denominator_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMenu.divide_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMenu.exponent_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMenu.first_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMenu.halfNormalizer_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMenu.halfNumerator_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMenu.index_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMenu.radius_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMenu.relative_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMenu.uniformRadius_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMenu.weight_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryNearestLeaf.distance_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryNearestLeaf.distances_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryNearestLeaf.empty_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryNearestLeaf.run_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRationalPower.items_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRationalPower.op_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRationalPower.prepared_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRationalPower.run_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRecovery.metricContext_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Loop.drawInput_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Loop.input_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Update.clientInput_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Update.input_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Weights.actionField_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Weights.active_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Weights.kind_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Weights.stateInput_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.c_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.deleted_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.leaves_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinarySamplingState.add_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinarySamplingState.keep_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinarySamplingState.retain_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinarySanitizedBest.atRawInput_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinarySanitizedBest.metricContext_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinarySanitizedBest.sanitizeContext_computes` and 1 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedianRecovery_Algorithms_CandidateSanitize`, `KMedianRecovery_Algorithms_GlobalOuter`, `KMedianRecovery_Algorithms_IntegralRecoveryRepeat`, `KMedianRecovery_Encoding_ColorLabelMachine`, `KMedianRecovery_Geometry_NearestLeafMachine`, `KMedianRecovery_Machines_MenuMachine`, `KMedianRecovery_Recovery_FinImages`, `KMedianRecovery_Recovery_RecoveryEnumeration`, `KMedianRecovery_Sampling_SamplerContext`, `KMedianRecovery_Sampling_SamplerUpdateParts`, `KMedianRecovery_Sampling_SamplerWeights`, `KMedianRecovery_Sampling_SamplingPotential`, `KMedianRecovery_Sampling_SamplingStateMachine`.
--
--   **Imports.** It imports the published bundle `Def_KMedianRefinedRecovery`; the bundles `Q238K031` and `Q238K039` of this split.
--
--   **Imported by** (directly, in this split): the bundle `Q238K050`; the statement `OAI_MetricKMedianRecovery_BitMachine_BinaryCoupledLoop_step_pack_s238`; the proof of `OAI_MetricKMedianRecovery_BitMachine_BinaryCoupledLoop_step_pack_s238`.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_KMedianRefinedRecovery
import Definitions.Def_Q238K031
import Definitions.Def_Q238K039

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
noncomputable def minus_computes : PolyComputes minus := NatOps.sub discardPrefix_computes extractPrefix_computes
end MetricKMedianRecovery.BitMachine.BinaryTaggedSets

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_ColorLabelMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRationalPower
open WordOperations WordList RationalHeight
noncomputable def op_computes : PolyComputes op := RatOps.mul (RatOps.ofWords extractPrefix_computes)
  (RatOps.ofWords (discardPrefix_computes.comp discardPrefix_computes))
noncomputable def items_computes : PolyComputes items := (extractPrefix_computes.pair (const_computes [])).comp repeatWords_computes
noncomputable def prepared_computes : PolyComputes prepared := cap.computes.pair
  (Fold.pack_computes items_computes discardPrefix_computes (const_computes (BinaryRational.encode 1)))
noncomputable def run_computes : PolyComputes run := prepared_computes.comp (CappedFold.run_computes op_computes)
end MetricKMedianRecovery.BitMachine.BinaryRationalPower

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_MenuMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryMenu
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
noncomputable def exponent_computes : PolyComputes exponent := discardPrefix_computes.comp discardPrefix_computes
noncomputable def index_computes : PolyComputes index := exponent_computes.comp UnaryResources.lengthBits_computes
noncomputable def relative_computes : PolyComputes (fun x=>[relative x]) :=
  NatOps.eq (discardPrefix_computes.comp extractPrefix_computes) (const_computes (1:ℕ).bits)
noncomputable def first_computes : PolyComputes (fun x=>[first x]) :=
  NatOps.eq (discardPrefix_computes.comp extractPrefix_computes) (const_computes (0:ℕ).bits)
attribute [local irreducible] UnaryResources.lengthBits
noncomputable def denominator_computes (i : ℕ) : PolyComputes (denominator i) := by
  unfold denominator
  exact (extractPrefix_computes.comp (field_computes i)).comp UnaryResources.lengthBits_computes
noncomputable def halfNumerator_computes : PolyComputes halfNumerator :=
  ((exponent_computes.append (const_computes [true])).pair (const_computes (BinaryRational.encode (1/2)))).comp BinaryRationalPower.run_computes
noncomputable def halfNormalizer_computes : PolyComputes halfNormalizer :=
  ((extractPrefix_computes.comp (field_computes 2)).pair (const_computes (BinaryRational.encode (1/2)))).comp BinaryRationalPower.run_computes
noncomputable def weight_computes : PolyComputes (fun x=>BinaryRational.encode (weight x)) := by
  have hh := first_computes.cond (RatOps.div (RatOps.const 1) (RatOps.mul (RatOps.const 3) (RatOps.nat (denominator_computes 0))))
    (relative_computes.cond (RatOps.div (RatOps.const 1) (RatOps.mul (RatOps.const 3)
      (RatOps.add (RatOps.nat (denominator_computes 1)) (RatOps.const 1))))
      (RatOps.mul (RatOps.const (1/3)) (RatOps.div (RatOps.ofWords halfNumerator_computes)
        (RatOps.sub (RatOps.const 1) (RatOps.ofWords halfNormalizer_computes)))))
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  unfold weight
  split_ifs <;> rfl
noncomputable def denominatorPower_computes : PolyComputes denominatorPower :=
  (exponent_computes.pair (RatOps.add (RatOps.const 1) (RatOps.ofWords (extractPrefix_computes.comp (field_computes 0))))).comp BinaryRationalPower.run_computes
noncomputable def divide_computes : PolyComputes divide := RatOps.div (RatOps.ofWords discardPrefix_computes) (RatOps.ofWords extractPrefix_computes)
noncomputable def uniformRadius_computes : PolyComputes (fun x=>BinaryRational.encode (uniformRadius x)) :=
  RatOps.mul (RatOps.mul (RatOps.add (RatOps.nat index_computes) (RatOps.const 1))
    (RatOps.ofWords (extractPrefix_computes.comp (field_computes 0))))
    (RatOps.ofWords (extractPrefix_computes.comp (field_computes 1)))
attribute [local irreducible] mapWith
noncomputable def radius_computes : PolyComputes radius := by
  unfold radius
  exact relative_computes.cond
    ((denominatorPower_computes.pair (extractPrefix_computes.comp (field_computes 2))).comp (mapWith_computes divide_computes))
    (cons_computes uniformRadius_computes (const_computes []))
end MetricKMedianRecovery.BitMachine.BinaryMenu

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_NearestLeafMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryNearestLeaf
open WordOperations WordList BinaryArithmetic
variable {n : ℕ}
noncomputable def distance_computes : PolyComputes (fun x=>BinaryRational.encode (distance x)) :=
  RatOps.add (RatOps.ofWords (((discardPrefix_computes.comp extractPrefix_computes).pair extractPrefix_computes).comp Lookup.run_computes))
    (RatOps.ofWords (discardPrefix_computes.comp discardPrefix_computes))
noncomputable def distances_computes : PolyComputes distances := mapWith_computes distance_computes
noncomputable def empty_computes : PolyComputes (fun x=>[empty x]) := discardPrefix_computes.comp isEmpty_computes
noncomputable def run_computes : PolyComputes run := by
  have computation := empty_computes.cond (const_computes [])
    (cons_computes (distances_computes.comp RationalMin.run_computes) (const_computes []))
  unfold run
  simpa only [Function.comp_def, encode] using computation
end MetricKMedianRecovery.BitMachine.BinaryNearestLeaf

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
noncomputable def add_computes : PolyComputes add := (extractPrefix_computes.comp extractPrefix_computes).pair
  ((extractPrefix_computes.comp discardPrefix_computes).append (cons_computes discardPrefix_computes (const_computes [])))
noncomputable def keep_computes : PolyComputes (fun x=>[keep x]) := by
  simpa only [keep,Bool.decide_and,Function.comp_def] using (NatOps.le (((discardPrefix_computes.comp discardPrefix_computes).comp Count.run_computes).comp UnaryResources.lengthBits_computes)
    extractPrefix_computes).and
      (NatOps.le (((discardPrefix_computes.comp extractPrefix_computes).comp Count.run_computes).comp UnaryResources.lengthBits_computes)
        extractPrefix_computes)
noncomputable def retain_computes : PolyComputes retain := keep_computes.cond
  (cons_computes discardPrefix_computes (const_computes [])) (const_computes [])
end MetricKMedianRecovery.BitMachine.BinarySamplingState

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
noncomputable def c_computes (i : ℕ) : PolyComputes (c i) := extractPrefix_computes.comp (field_computes i)
noncomputable def deleted_computes : PolyComputes deleted := discardPrefix_computes.comp extractPrefix_computes
noncomputable def leaves_computes : PolyComputes leaves := discardPrefix_computes.comp discardPrefix_computes
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
noncomputable def stateInput_computes : PolyComputes stateInput :=
  extractPrefix_computes.pair (discardPrefix_computes.comp WordList.head_computes)
noncomputable def actionField_computes (i : ℕ) : PolyComputes (actionField i) := discardPrefix_computes.comp (field_computes i)
noncomputable def kind_computes (k : ℕ) : PolyComputes (fun x=>[kind k x]) := by
  simpa only [kind,value_bits] using NatOps.eq (actionField_computes 0) (const_computes k.bits)
noncomputable def active_computes : PolyComputes (fun x=>[active x]) :=
  (((c_computes 3).comp isEmpty_computes).not).and (RatOps.lt (RatOps.const 0) (RatOps.ofWords (c_computes 1)))
end MetricKMedianRecovery.BitMachine.BinarySampler.Weights

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
noncomputable def input_computes : PolyComputes input := extractPrefix_computes.comp Weights.stateInput_computes
noncomputable def clientInput_computes : PolyComputes clientInput := input_computes.pair (actionField_computes 1)
end MetricKMedianRecovery.BitMachine.BinarySampler.Update

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
noncomputable def metricContext_computes : PolyComputes metricContext := cons_computes (field_computes 0)
  (cons_computes (field_computes 1) (const_computes []))
noncomputable def sanitizeContext_computes : PolyComputes sanitizeContext := cons_computes (field_computes 2)
  (cons_computes (field_computes 3) (cons_computes (field_computes 4) (const_computes [])))
noncomputable def atRawInput_computes : PolyComputes atRawInput := cons_computes (extractPrefix_computes.comp (field_computes 0))
  (cons_computes (extractPrefix_computes.comp (field_computes 1)) (cons_computes (extractPrefix_computes.comp (field_computes 2))
    (cons_computes discardPrefix_computes (const_computes []))))
end MetricKMedianRecovery.BitMachine.BinarySanitizedBest

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
attribute [local irreducible] mapWith
noncomputable def metricContext_computes : PolyComputes metricContext := cons_computes (field_computes 0) (cons_computes (field_computes 1) (const_computes []))
attribute [local irreducible] metricContext candidateWords
end MetricKMedianRecovery.BitMachine.BinaryRecovery

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_SamplingPotential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySampler.Loop
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
variable {n : ℕ}

noncomputable def input_computes : PolyComputes input := (extractPrefix_computes.comp extractPrefix_computes).pair
  (discardPrefix_computes.comp discardPrefix_computes)
noncomputable def drawInput_computes : PolyComputes drawInput := cons_computes (extractPrefix_computes.comp extractPrefix_computes)
  (cons_computes (discardPrefix_computes.comp discardPrefix_computes)
    (cons_computes (extractPrefix_computes.comp discardPrefix_computes)
      (cons_computes (discardPrefix_computes.comp extractPrefix_computes) (const_computes []))))
end MetricKMedianRecovery.BitMachine.BinarySampler.Loop

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
noncomputable def atSeedInput_computes : PolyComputes atSeedInput := (extractPrefix_computes.comp extractPrefix_computes).pair
  ((extractPrefix_computes.comp discardPrefix_computes).pair discardPrefix_computes)
attribute [local irreducible] mapWith
end MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat

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
noncomputable def callInput_computes : PolyComputes callInput := list_computes
  [extractPrefix ∘ extractPrefix,discardPrefix,discardPrefix ∘ extractPrefix] (by
    intro f hf;refine Classical.choice ?_;simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl
    · exact ⟨extractPrefix_computes.comp extractPrefix_computes⟩
    · exact ⟨discardPrefix_computes⟩
    · exact ⟨extractPrefix_computes.comp discardPrefix_computes⟩)
attribute [local irreducible] BinaryInputParser.Metric.budget
end MetricKMedianRecovery.BitMachine.BinaryGlobalOuter

end OAI
end


