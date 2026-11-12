-- Prove2me | Definitions.Def_Q238L046
-- name    : Q238L046
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T11:45:36.098329+00:00
-- url     : https://prove2.me/theorems/cf0de6d7-57b4-4b42-849f-62b578d634f0
-- title:
--   Definitions bundle Q238L046 of the split of OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 94 declarations of OpenAI's Lean: 94 definitions. The definitions and types are `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalCall.normInput_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInputParser.Metric.afterClients_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInputParser.Metric.budget_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInputParser.Metric.clients_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInputParser.Metric.count_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInputParser.Metric.facilities_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInputParser.Metric.header_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInputParser.Metric.masks_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInputParser.Metric.rawMatrix_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInputParser.Metric.tailHeader_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInputParser.Rows.offset_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralAll.less_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralAll.src_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralAll.surplusInput_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch.ranks_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat.atSeedInput_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.completeRaw_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.sampleRaw_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMaskParser.member_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMenu.denominatorPower_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMenu.denominator_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMenu.divide_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMenu.exponent_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMenu.first_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMenu.halfNormalizer_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMenu.halfNumerator_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMenu.index_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMenu.radius_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMenu.relative_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMenu.uniformRadius_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMenu.weight_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMetricAnchor.rectInput_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMetricArrays.row_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMetricCost.near_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMetricSurplus.anchorInput_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMetricSurplus.total_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryNearestLeaf.distance_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryNearestLeaf.distances_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryNearestLeaf.empty_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryNearestLeaf.run_computes` and 54 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedianRecovery_Algorithms_CandidateSanitize`, `KMedianRecovery_Algorithms_GlobalCall`, `KMedianRecovery_Algorithms_IntegralAll`, `KMedianRecovery_Algorithms_IntegralRecoveryAll`, `KMedianRecovery_Algorithms_IntegralRecoveryMachine`, `KMedianRecovery_Algorithms_IntegralRecoveryRepeat`, `KMedianRecovery_Branching_PopulationMachine`, `KMedianRecovery_Encoding_ColorLabelMachine`, `KMedianRecovery_Encoding_FinSets`, `KMedianRecovery_Encoding_MatrixRows`, `KMedianRecovery_Geometry_MetricAnchor`, `KMedianRecovery_Geometry_MetricArrays`, `KMedianRecovery_Geometry_MetricCost2`, `KMedianRecovery_Geometry_MetricParser`, `KMedianRecovery_Geometry_NearestLeafMachine`, `KMedianRecovery_Geometry_RoundingArithmetic`, `KMedianRecovery_Geometry_RoundingMatrix`, `KMedianRecovery_Machines_MenuMachine`, `KMedianRecovery_Machines_NormalizationMachine`, `KMedianRecovery_Machines_RecoveryOptionMachine`, `KMedianRecovery_Recovery_FinImages`, `KMedianRecovery_Recovery_NormalizeInput`, `KMedianRecovery_Recovery_RecoveryContext`, `KMedianRecovery_Recovery_RecoveryEnumeration`, `KMedianRecovery_Sampling_SamplerContext`, `KMedianRecovery_Sampling_SamplerDraw`, `KMedianRecovery_Sampling_SamplerParameters`, `KMedianRecovery_Sampling_SamplerResources`, `KMedianRecovery_Sampling_SamplerUpdateParts`, `KMedianRecovery_Sampling_SamplerWeights`, `KMedianRecovery_Sampling_SamplingPotential`, `KMedianRecovery_Strictness_MetricSurplus`.
--
--   **Imports.** It imports the published bundle `Def_KMedianRecovery`; the bundles `Q238L039` and `Q238L040` of this split.
--
--   **Imported by** (directly, in this split): the bundle `Q238L050`.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_KMedianRecovery
import Definitions.Def_Q238L039
import Definitions.Def_Q238L040

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_MatrixRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryInputParser.Rows
open WordOperations WordList BinaryArithmetic
noncomputable def offset_computes : PolyComputes offset :=
  NatOps.mul ((extractPrefix_computes.comp extractPrefix_computes).comp UnaryResources.lengthBits_computes) discardPrefix_computes
attribute [local irreducible] offset Drop.run Take.run
attribute [local irreducible] mapWith
end MetricKMedianRecovery.BitMachine.BinaryInputParser.Rows

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_MetricParser
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryInputParser.Metric
open WordOperations WordList
attribute [local irreducible] nat RawTake.run RawDrop.run Stream.run Rows.run RawUnary.run
attribute [local irreducible] header count tailHeader budget masks clients afterClients facilities rawMatrix
noncomputable def header_computes : PolyComputes header := by
  unfold header
  exact nat_computes
noncomputable def count_computes : PolyComputes count := by
  unfold count
  exact header_computes.comp extractPrefix_computes
noncomputable def tailHeader_computes : PolyComputes tailHeader := by
  unfold tailHeader
  exact (header_computes.comp discardPrefix_computes).comp nat_computes
noncomputable def budget_computes : PolyComputes budget := by
  unfold budget
  exact tailHeader_computes.comp extractPrefix_computes
noncomputable def masks_computes : PolyComputes masks := by
  unfold masks
  exact tailHeader_computes.comp discardPrefix_computes
noncomputable def clients_computes : PolyComputes clients := by
  unfold clients
  exact (count_computes.pair masks_computes).comp RawTake.run_computes
noncomputable def afterClients_computes : PolyComputes afterClients := by
  unfold afterClients
  exact (count_computes.pair masks_computes).comp RawDrop.run_computes
noncomputable def facilities_computes : PolyComputes facilities := by
  unfold facilities
  exact (count_computes.pair afterClients_computes).comp RawTake.run_computes
noncomputable def rawMatrix_computes : PolyComputes rawMatrix := by
  unfold rawMatrix
  exact (count_computes.pair afterClients_computes).comp RawDrop.run_computes
attribute [local irreducible] matrix
end MetricKMedianRecovery.BitMachine.BinaryInputParser.Metric

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
noncomputable def member_computes : PolyComputes (fun x=>[member x]) :=
  ((discardPrefix_computes.pair extractPrefix_computes).comp RawDrop.run_computes).comp MetricKMedianRecovery.BitMachine.head_computes
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
noncomputable def plus_computes : PolyComputes plus := NatOps.add extractPrefix_computes discardPrefix_computes
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
noncomputable def count_computes : PolyComputes count :=
  ((filterWith_computes near_computes).comp Count.run_computes).comp UnaryResources.lengthBits_computes
end MetricKMedianRecovery.BitMachine.BinaryPopulation

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
noncomputable def row_computes : PolyComputes row :=
  (discardPrefix_computes.pair (extractPrefix_computes.comp (field_computes 0))).comp Lookup.run_computes
attribute [local irreducible] BinaryIndexMap.run
attribute [local irreducible] mapWith
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
noncomputable def near_computes : PolyComputes near := discardPrefix_computes.comp RationalMin.run_computes
end MetricKMedianRecovery.BitMachine.BinaryMetricCost

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
noncomputable def sanitizeContext_computes : PolyComputes sanitizeContext := cons_computes (field_computes 2)
  (cons_computes (field_computes 3) (cons_computes (field_computes 4) (const_computes [])))
end MetricKMedianRecovery.BitMachine.BinarySanitizedBest

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_RecoveryContext
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRecovery
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
noncomputable def qbits_computes : PolyComputes qbits := discardPrefix_computes.comp extractPrefix_computes
noncomputable def cbits_computes : PolyComputes cbits := (discardPrefix_computes.comp discardPrefix_computes).comp extractPrefix_computes
noncomputable def bbits_computes : PolyComputes bbits := ((discardPrefix_computes.comp discardPrefix_computes).comp discardPrefix_computes).comp UnaryResources.inc_computes
noncomputable def src_computes (j : ℕ) : PolyComputes (src j) := extractPrefix_computes.comp (field_computes j)
attribute [local irreducible] RawTake.run BinaryEllipsoidInitial.indices
noncomputable def cword_computes : PolyComputes cword := (cbits_computes.pair (src_computes 6)).comp RawTake.run_computes
noncomputable def bword_computes : PolyComputes bword := (bbits_computes.pair (src_computes 7)).comp RawTake.run_computes
attribute [local irreducible] mapWith
noncomputable def zeros_computes : PolyComputes zeros :=
  PolyComputes.comp (f := fun input=>pairBits ([],BinaryEllipsoidInitial.indices (src 6 input)))
    (g := mapWith (fun _=>[]))
    ((const_computes []).pair ((src_computes 6).comp BinaryEllipsoidInitial.indices_computes))
    (mapWith_computes (const_computes []))
noncomputable def labels_computes : PolyComputes labels := bword_computes.comp BinaryEllipsoidInitial.indices_computes
attribute [local irreducible] src zeros labels qbits cword bword
noncomputable def context_computes : PolyComputes context := list_computes
  [src 0,src 1,src 2,src 3,src 4,src 5,zeros,zeros,labels,qbits,cword,src 8] (by
    intro f hf; refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals first | exact ⟨src_computes _⟩ | exact ⟨zeros_computes⟩ | exact ⟨labels_computes⟩ | exact ⟨qbits_computes⟩ | exact ⟨cword_computes⟩)
noncomputable def zeroContext_computes : PolyComputes zeroContext := list_computes
  [src 0,src 1,src 2,src 3,src 4,src 5,zeros,zeros,fun _=>encode [[]],qbits,fun _=>[],src 8] (by
    intro f hf; refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals first | exact ⟨src_computes _⟩ | exact ⟨zeros_computes⟩ | exact ⟨qbits_computes⟩ | exact ⟨const_computes _⟩)
end MetricKMedianRecovery.BitMachine.BinaryRecovery

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
noncomputable def promote_computes : PolyComputes promote := extractPrefix_computes.pair (discardPrefix_computes.pair (const_computes _))
noncomputable def range_computes : PolyComputes range := ((field_computes 6).append (const_computes _)).comp BinaryEllipsoidInitial.indices_computes
noncomputable def blueRange_computes : PolyComputes blueRange := (field_computes 7).comp BinaryEllipsoidInitial.indices_computes
noncomputable def choices_computes : PolyComputes choices :=
  (range_computes.pair ((range_computes.pair blueRange_computes).comp cross_computes)).comp cross_computes
attribute [local irreducible] mapWith
noncomputable def metricContext_computes : PolyComputes metricContext := cons_computes (field_computes 0) (cons_computes (field_computes 1) (const_computes []))
attribute [local irreducible] metricContext candidateWords
end MetricKMedianRecovery.BitMachine.BinaryRecovery

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_RecoveryOptionMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRecovery
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
attribute [local irreducible] run
noncomputable def replaceState_computes : PolyComputes replaceState := list_computes
  [src 0,src 1,src 2,src 3,src 4,field 0 ∘ discardPrefix,src 6,src 7,src 8,src 9] (by
    intro f hf; refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals first | exact ⟨src_computes _⟩ | exact ⟨discardPrefix_computes.comp (field_computes 0)⟩)
end MetricKMedianRecovery.BitMachine.BinaryRecovery

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
noncomputable def dimension_computes : PolyComputes dimension := (field_computes 1).comp UnaryResources.lengthBits_computes
noncomputable def diameter_computes : PolyComputes diameter := (field_computes 5).comp BinaryRational.natWords_computes
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
noncomputable def input_computes : PolyComputes input := (field_computes 0).pair (field_computes 1)
noncomputable def actions_computes : PolyComputes actions := by
  have computation := ((input_computes.comp (c_computes 2)).pair (input_computes.comp (c_computes 9))).comp BinaryActions.run_computes
  unfold actions
  simpa only [Function.comp_def] using computation
end MetricKMedianRecovery.BitMachine.BinarySampler.Draw

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
attribute [local irreducible] Update.run Draw.run
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
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_SamplerResources
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySampler.Loop
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
variable {n : ℕ}
noncomputable def fixedContext_computes : PolyComputes fixedContext := (field_computes 0).pair (field_computes 2)
end MetricKMedianRecovery.BitMachine.BinarySampler.Loop

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
noncomputable def sampleRaw_computes : PolyComputes sampleRaw := discardPrefix_computes.comp (discardPrefix_computes.comp extractPrefix_computes)
noncomputable def completeRaw_computes : PolyComputes completeRaw := discardPrefix_computes.comp (discardPrefix_computes.comp discardPrefix_computes)
attribute [local irreducible] src mword extra completeRaw BinaryRational.natWords
attribute [local irreducible] mapWith recoveryContext sampleContext BinarySampler.Trace.run
end MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery

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
noncomputable def atSeedInput_computes : PolyComputes atSeedInput := (extractPrefix_computes.comp extractPrefix_computes).pair
  ((extractPrefix_computes.comp discardPrefix_computes).pair discardPrefix_computes)
attribute [local irreducible] mapWith
end MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat

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
noncomputable def rectInput_computes : PolyComputes rectInput :=
  cons_computes (field_computes 0) (cons_computes ((field_computes 1).comp BinaryEllipsoidInitial.indices_computes)
    (cons_computes (field_computes 2) (const_computes [])))
attribute [local irreducible] WordList.map
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
attribute [local irreducible] bare RawTake.run UnaryResources.lengthBits BinaryIntegralRecovery.Guesses.run
noncomputable def ranks_computes : PolyComputes ranks :=
  (((field_computes 3).comp Count.run_computes).append (const_computes [true])).comp BinaryEllipsoidInitial.indices_computes
attribute [local irreducible] mapWith
attribute [local irreducible] start
end MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_RoundingArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace BinaryRound
open WordList BinaryOpeningPayment

noncomputable def ceil_computes : PolyComputes ceil :=
  RatOps.natCeil (RatOps.div (RatOps.ofWords (field_computes 0)) (RatOps.ofWords (field_computes 1)))
noncomputable def positive_computes : PolyComputes positive := by
  have hh:=NatOps.min (field_computes 2) (NatOps.max (const_computes (1:ℕ).bits) ceil_computes)
  change PolyComputes (fun x=>(min (value (field 2 x)) (max 1 (value (ceil x)))).bits)
  simpa only [value_bits] using hh
noncomputable def rational_computes : PolyComputes rational := RatOps.nat positive_computes
end BinaryRound
end MetricKMedianRecovery.BitMachine

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
noncomputable def anchorInput_computes : PolyComputes anchorInput := list_computes
  [field 0,field 1,field 2,field 3,field 5] (by
    intro f hf; refine Classical.choice ?_; simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl|rfl|rfl <;> exact ⟨field_computes _⟩)
noncomputable def total_computes : PolyComputes total := MetricKMedianRecovery.BitMachine.NatOps.add (field_computes 5) (field_computes 6)
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
variable {n : ℕ}
noncomputable def src_computes (j : ℕ) : PolyComputes (src j) := extractPrefix_computes.comp (field_computes j)
noncomputable def less_computes : PolyComputes less := NatOps.sub (src_computes 5) discardPrefix_computes
noncomputable def surplusInput_computes : PolyComputes surplusInput := list_computes
  [src 0,src 1,src 2,src 3,src 4,less,discardPrefix] (by
    intro f hf; refine Classical.choice ?_; simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals first | exact ⟨src_computes _⟩ | exact ⟨less_computes⟩ | exact ⟨discardPrefix_computes⟩)
attribute [local irreducible] mapWith
end MetricKMedianRecovery.BitMachine.BinaryIntegralAll

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_RoundingMatrix
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRoundingMatrix
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
variable {n : ℕ}
noncomputable def entry_computes : PolyComputes entry := by
  change PolyComputes (fun x=>if value (rowIndex x)=value (colIndex x) then BinaryRational.encode 0 else BinaryRound.rational (entryInput x))
  simpa only [decide_eq_true_eq,Function.comp_def] using
    (NatOps.eq rowIndex_computes colIndex_computes).cond (const_computes (BinaryRational.encode 0))
      (entryInput_computes.comp BinaryRound.rational_computes)
noncomputable def row_computes : PolyComputes row := by
  unfold row
  have computes := (id_computes.pair ((extractPrefix_computes.comp (field_computes 1)).comp BinaryEllipsoidInitial.indices_computes)).comp
    (mapWith_computes entry_computes)
  simpa only [Function.comp_def,id_eq] using computes
noncomputable def run_computes : PolyComputes run := by
  unfold run
  have computes := (id_computes.pair ((field_computes 1).comp BinaryEllipsoidInitial.indices_computes)).comp (mapWith_computes row_computes)
  simpa only [Function.comp_def,id_eq] using computes
end MetricKMedianRecovery.BitMachine.BinaryRoundingMatrix

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_NormalizationMachine
attribute [-instance] _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryNormalization
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
open IntegralAssembly (gammaRat)
noncomputable def cap_computes : PolyComputes cap := by
  change PolyComputes (fun x=>(⌈BinaryRational.decode (capArgument x)⌉₊+1).bits)
  simpa only [value_bits] using NatOps.add (RatOps.natCeil (RatOps.ofWords capArgument_computes)) (const_computes (1:ℕ).bits)
noncomputable def roundingInput_computes : PolyComputes roundingInput := by
  unfold roundingInput
  have computes := cons_computes ((field_computes 0).comp BinaryDuplicateMatrix.run_computes)
    (cons_computes ((field_computes 1).comp BinaryDuplicateMatrix.twice_computes)
      (cons_computes mesh_computes (cons_computes cap_computes (const_computes []))))
  simpa only [Function.comp_def,encode] using computes
noncomputable def run_computes : PolyComputes run := roundingInput_computes.comp BinaryRoundingMatrix.run_computes
end MetricKMedianRecovery.BitMachine.BinaryNormalization

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
noncomputable def points_computes : PolyComputes points := BinaryInputParser.Metric.clients_computes.comp RawUnary.run_computes
end P
attribute [local irreducible] P.points P.clients P.facilities
  BinaryInputParser.Metric.matrix BinaryInputParser.Metric.count BinaryInputParser.Metric.budget
  BinaryNormalization.run BinaryNormalization.cap BinaryNormalization.mesh
noncomputable def raw_computes : PolyComputes raw := extractPrefix_computes
noncomputable def points_computes : PolyComputes points := raw_computes.comp P.points_computes
noncomputable def count_computes : PolyComputes count := raw_computes.comp BinaryInputParser.Metric.count_computes
noncomputable def twice_computes : PolyComputes twice := points_computes.comp BinaryDuplicateMatrix.twice_computes
noncomputable def budget_computes : PolyComputes budget := raw_computes.comp BinaryInputParser.Metric.budget_computes
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

namespace MetricKMedianRecovery.BitMachine.BinaryGlobalCall
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
noncomputable def normInput_computes : PolyComputes normInput := (field_computes 0).pair (field_computes 1)
attribute [local irreducible] base RawTake.run UnaryResources.lengthBits
attribute [local irreducible] norm src clamp BinaryInputParser.Metric.count
end MetricKMedianRecovery.BitMachine.BinaryGlobalCall

end OAI
end


