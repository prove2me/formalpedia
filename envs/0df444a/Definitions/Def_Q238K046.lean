-- Prove2me | Definitions.Def_Q238K046
-- name    : Q238K046
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T23:42:39.839813+00:00
-- url     : https://prove2.me/theorems/ff70777a-ccab-4c6f-8fa4-7b63c9479a11
-- title:
--   Definitions bundle Q238K046 of the split of OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 73 declarations of OpenAI's Lean: 73 definitions. The definitions and types are `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalCall.normInput_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInputParser.Metric.afterClients_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInputParser.Metric.budget_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInputParser.Metric.clients_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInputParser.Metric.count_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInputParser.Metric.facilities_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInputParser.Metric.header_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInputParser.Metric.masks_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInputParser.Metric.rawMatrix_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInputParser.Metric.tailHeader_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInputParser.Rows.offset_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralAll.less_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralAll.src_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralAll.surplusInput_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch.anchorInput_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch.ranks_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch.src_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair.sampleCount_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair.sampleWord_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat.rword_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.cfg_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.completeRaw_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.extra_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.mword_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.precision_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.sampleContext_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.sampleRaw_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMaskParser.member_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMetricAnchor.rectInput_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMetricArrays.row_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMetricCost.near_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMetricSurplus.anchorInput_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMetricSurplus.total_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryNormalization.cap_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryNormalization.roundingInput_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryNormalization.run_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryNormalizeInput.P.points_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryNormalizeInput.budget_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryNormalizeInput.count_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryNormalizeInput.points_computes` and 33 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedianRecovery_Algorithms_GlobalCall`, `KMedianRecovery_Algorithms_IntegralAll`, `KMedianRecovery_Algorithms_IntegralRecoveryAll`, `KMedianRecovery_Algorithms_IntegralRecoveryDemand`, `KMedianRecovery_Algorithms_IntegralRecoveryMachine`, `KMedianRecovery_Algorithms_IntegralRecoveryRepeat`, `KMedianRecovery_Algorithms_IntegralRecoverySuccess`, `KMedianRecovery_Encoding_FinSets`, `KMedianRecovery_Encoding_MatrixRows`, `KMedianRecovery_Geometry_MetricAnchor`, `KMedianRecovery_Geometry_MetricArrays`, `KMedianRecovery_Geometry_MetricCost2`, `KMedianRecovery_Geometry_MetricParser`, `KMedianRecovery_Geometry_RoundingArithmetic`, `KMedianRecovery_Geometry_RoundingMatrix`, `KMedianRecovery_Machines_NormalizationMachine`, `KMedianRecovery_Machines_RecoveryOptionMachine`, `KMedianRecovery_Recovery_FinImages`, `KMedianRecovery_Recovery_NormalizeInput`, `KMedianRecovery_Recovery_RecoveryContext`, `KMedianRecovery_Recovery_RecoveryEnumeration`, `KMedianRecovery_Sampling_SamplerDraw`, `KMedianRecovery_Sampling_SamplerParameters`, `KMedianRecovery_Sampling_SamplerResources`, `KMedianRecovery_Strictness_MetricSurplus`.
--
--   **Imports.** It imports the published bundle `Def_KMedianRefinedRecovery`; the bundles `Q238K038` and `Q238K039` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q238K049` and `Q238K050`.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_KMedianRefinedRecovery
import Definitions.Def_Q238K038
import Definitions.Def_Q238K039

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
attribute [local irreducible] nat RawTake.run RawDrop.run Stream.run RawUnary.run
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
attribute [local irreducible] mapWith
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
noncomputable def unary_computes (j : ℕ) : PolyComputes (unary j) :=
  ((field_computes j).pair id_computes).comp (BoundedNatWord.run_computes bound)
noncomputable def Jword_computes : PolyComputes Jword :=
  (const_computes [true]).append (UnaryResources.copy_computes (unary_computes 7) (const_computes (List.replicate 2000000 true)))
noncomputable def nword_computes : PolyComputes nword := (field_computes 2).comp Count.run_computes
noncomputable def precision_computes : PolyComputes precision :=
  (((nword_computes.append (unary_computes 5)).append (const_computes (List.replicate M true))).append
    (const_computes (List.replicate E true))).append Jword_computes |>.append (const_computes (List.replicate 5 true))
noncomputable def menus_computes : PolyComputes menus := cons_computes (const_computes (List.replicate M true))
  (cons_computes (const_computes (List.replicate E true)) (cons_computes Jword_computes (const_computes [])))
noncomputable def dimension_computes : PolyComputes dimension := (field_computes 1).comp UnaryResources.lengthBits_computes
noncomputable def diameter_computes : PolyComputes diameter := (field_computes 5).comp BinaryRational.natWords_computes
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
noncomputable def input_computes : PolyComputes input := (field_computes 0).pair (field_computes 1)
end MetricKMedianRecovery.BitMachine.BinarySampler.Draw

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
noncomputable def extra_computes : PolyComputes extra := discardPrefix_computes.comp extractPrefix_computes
noncomputable def mword_computes : PolyComputes mword := extractPrefix_computes.comp (BinarySampler.Parameters.unary_computes 7)
noncomputable def cfg_computes : PolyComputes cfg := extractPrefix_computes.comp BinarySampler.Parameters.run_computes
noncomputable def precision_computes : PolyComputes precision := extractPrefix_computes.comp BinarySampler.Parameters.precision_computes
noncomputable def sampleContext_computes : PolyComputes sampleContext := cons_computes cfg_computes
  (cons_computes mword_computes (cons_computes (mword_computes.append mword_computes)
    (cons_computes precision_computes (cons_computes sampleRaw_computes (const_computes [])))))
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
noncomputable def sampleCount_computes : PolyComputes sampleCount := by
  have hh := NatOps.mul (NatOps.mul (const_computes (2:ℕ).bits)
    (mword_computes.comp UnaryResources.lengthBits_computes))
    (precision_computes.comp UnaryResources.lengthBits_computes)
  change PolyComputes (fun x=>(2*(mword x).length*(precision x).length).bits)
  simpa only [UnaryResources.lengthBits_eq,value_bits,Function.comp_def] using hh
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
noncomputable def sampleWord_computes : PolyComputes sampleWord := UnaryResources.copy_computes
  (mword_computes.append mword_computes) precision_computes
attribute [local irreducible] extra raw demandBits RawTake.run
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
attribute [local irreducible] extra Fair.raw Fair.demandWord BinaryMetricBest.run RawUnary.run BinarySeed.rows
  BinaryIntegralRecovery.result BinaryFinSet.encode BinarySampler.Parameters.pack BinaryMetricBest.best Fair.output List.ofFn BinarySeed.raw
noncomputable def rword_computes (Q : Polynomial ℕ) : PolyComputes (rword Q) :=
  (extra_computes.comp (counter Q).computes).comp RawUnary.run_computes
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
noncomputable def src_computes (j : ℕ) : PolyComputes (src j) := extractPrefix_computes.comp (field_computes j)
noncomputable def anchorInput_computes : PolyComputes anchorInput := list_computes
  [src 0,src 1,src 2,src 3,discardPrefix] (by
    intro f hf; refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl|rfl|rfl
    all_goals first | exact ⟨src_computes _⟩ | exact ⟨discardPrefix_computes⟩)
attribute [local irreducible] bare RawTake.run UnaryResources.lengthBits
noncomputable def ranks_computes : PolyComputes ranks :=
  (((field_computes 3).comp Count.run_computes).append (const_computes [true])).comp BinaryEllipsoidInitial.indices_computes
attribute [local irreducible] mapWith
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
  BinaryInputParser.Metric.count BinaryInputParser.Metric.budget
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
attribute [local irreducible] RawTake.run UnaryResources.lengthBits
attribute [local irreducible] BinaryInputParser.Metric.count
end MetricKMedianRecovery.BitMachine.BinaryGlobalCall

end OAI
end


