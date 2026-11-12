-- Prove2me | Definitions.Def_Q238L052
-- name    : Q238L052
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T11:54:23.417072+00:00
-- url     : https://prove2.me/theorems/62a8b343-5fe2-4a31-a858-254c62d5a3e4
-- title:
--   Definitions bundle Q238L052 of the split of OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 88 declarations of OpenAI's Lean: 88 definitions. The definitions and types are `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchRandomize.context_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchRandomize.labels_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchRandomize.lraw_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchRandomize.lshape_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchRandomize.tailBits_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchTape.Count.bword_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchTape.Count.cut_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchTape.Count.leftShape_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchTape.Count.lword_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchTape.Count.rightShape_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchTape.Count.run_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchTape.Count.tword_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCanonicalSurplus.postInput_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCanonicalSurplus.run`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCanonicalSurplus.run_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledLoop.next_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledLoop.run_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledLoop.stateRun_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledLoop.step_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.active_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.run_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDyadic.run_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalCall.A.budget`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInitial.bracket_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInitial.initialOutcome_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInitial.initialState_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInitial.loopInput_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInitial.lowerCount_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInitial.lowerFinish_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInitial.lowerHistory_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInitial.lowerInput_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInitial.lower_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInitial.normal_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInitial.run_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInitial.upperCount_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInitial.upperFinish_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInitial.upperHistory_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInitial.upperInput_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInitial.upper_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInitialAuto.run_computes` and 48 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedianRecovery_Algorithms_GlobalCall`, `KMedianRecovery_Algorithms_IntegralAll`, `KMedianRecovery_Algorithms_IntegralRecoveryAll`, `KMedianRecovery_Branching_BranchSeedLayout`, `KMedianRecovery_Branching_RandomizedZeroBranch`, `KMedianRecovery_Geometry_LocalFuel`, `KMedianRecovery_Geometry_MetricAnchor`, `KMedianRecovery_Machines_InitialLoop`, `KMedianRecovery_Machines_LengthQuery`, `KMedianRecovery_Machines_LoopMachine`, `KMedianRecovery_Machines_LoopSize`, `KMedianRecovery_Machines_ResolveMachine`, `KMedianRecovery_Machines_SensitiveMachine`, `KMedianRecovery_Machines_StepMachine`, `KMedianRecovery_Recovery_InitialAuto`, `KMedianRecovery_Recovery_InitialProject`, `KMedianRecovery_Recovery_PlanResult`, `KMedianRecovery_Sampling_InverseCDF`, `KMedianRecovery_Strictness_MetricSurplus`, `KMedianRecovery_Strictness_SurplusPostprocess`.
--
--   **Imports.** It imports the published bundle `Def_KMedianRecovery`; the bundles `Q238L048`, `Q238L049` and `Q238L050` of this split.
--
--   **Imported by** (directly, in this split): the bundle `Q238L054`; the statements `OAI.MetricKMedianRecovery.BitMachine.BinaryCanonicalSurplus.produce_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch.demand_bound_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch.designated_recovery_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMetricSurplus.low_candidate_s238r` and `OAI.MetricKMedianRecovery.BitMachine.BinaryMetricSurplus.run_pack_s238r`; the proofs of `OAI.MetricKMedianRecovery.BitMachine.BinaryCanonicalSurplus.produce_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch.demand_bound_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch.designated_recovery_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMetricSurplus.low_candidate_s238r` and `OAI.MetricKMedianRecovery.BitMachine.BinaryMetricSurplus.run_pack_s238r`.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_KMedianRecovery
import Definitions.Def_Q238L048
import Definitions.Def_Q238L049
import Definitions.Def_Q238L050

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_InverseCDF
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryInverseCDF
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
open Dyadic.Canonical

attribute [local irreducible] Take.run UnaryResources.inc
noncomputable def prefix_computes : PolyComputes prefixCounts :=
  ((discardPrefix_computes.comp UnaryResources.inc_computes).pair
    (extractPrefix_computes.comp extractPrefix_computes)).comp Take.run_computes
attribute [local irreducible] prefixCounts NaturalArray.sumWords
noncomputable def total_computes : PolyComputes total := prefix_computes.comp NaturalArray.sumWords_computes
attribute [local irreducible] total
noncomputable def predicate_computes : PolyComputes (fun x=>[predicate x]) :=
  NatOps.lt (extractPrefix_computes.comp discardPrefix_computes) total_computes
noncomputable def find_computes : PolyComputes find :=
  (id_computes.pair (extractPrefix_computes.comp Indices.run_computes)).comp (Find.run_computes predicate_computes)
noncomputable def searched_computes : PolyComputes searched :=
  ((field_computes 1).pair ((field_computes 2).comp BinarySeed.normalizeBig_computes)).comp find_computes
attribute [local irreducible] searched
noncomputable def run_computes : PolyComputes run := by
  have hh := (searched_computes.comp isEmpty_computes).cond (field_computes 0) (searched_computes.comp WordOperations.tail_computes)
  unfold run
  simpa only [decide_eq_true_eq,Function.comp_def] using hh
end MetricKMedianRecovery.BitMachine.BinaryInverseCDF

namespace MetricKMedianRecovery.BitMachine.BinaryDyadic
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
noncomputable def run_computes : PolyComputes run := prepared_computes.comp BinaryInverseCDF.run_computes
end MetricKMedianRecovery.BitMachine.BinaryDyadic

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
noncomputable def lshape_computes : PolyComputes lshape := cons_computes nword_computes (cons_computes blog_computes (const_computes []))
noncomputable def lraw_computes : PolyComputes lraw :=
  ((extractPrefix_computes.comp lsize_computes).pair rest_computes).comp RawTake.run_computes
noncomputable def tailBits_computes : PolyComputes tailBits :=
  ((extractPrefix_computes.comp lsize_computes).pair rest_computes).comp RawDrop.run_computes
noncomputable def labels_computes : PolyComputes labels :=
  (((extractPrefix_computes.comp (field_computes 8)).comp lengthBits_computes).pair
    ((extractPrefix_computes.comp lshape_computes).pair lraw_computes)).comp BinaryColorLabel.labels_computes
noncomputable def context_computes : PolyComputes context :=
  cons_computes (extractPrefix_computes.comp (field_computes 0)) (cons_computes (extractPrefix_computes.comp (field_computes 1)) (cons_computes (extractPrefix_computes.comp (field_computes 2)) (cons_computes (extractPrefix_computes.comp (field_computes 3)) (cons_computes (extractPrefix_computes.comp (field_computes 4)) (cons_computes (extractPrefix_computes.comp (field_computes 5)) (cons_computes (colors_computes) (cons_computes (labels_computes) (cons_computes (extractPrefix_computes.comp (field_computes 8)) (cons_computes (extractPrefix_computes.comp (field_computes 9)) (cons_computes (extractPrefix_computes.comp (field_computes 10)) (cons_computes (extractPrefix_computes.comp (field_computes 11)) (const_computes []))))))))))))
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
-- module Solutions.Q238_KM.KMedianRecovery_Machines_LengthQuery
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryLengthQuery
open WordOperations WordList BinaryArithmetic RationalLeaves
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
open BinaryOpeningPayment (field field_computes field_encode)
attribute [local irreducible] BinaryFiniteMachine.continuation

noncomputable def finalOpened_computes : PolyComputes finalOpened :=
  (opened_computes.pair chosen_computes).comp BinaryFiniteMachine.after_computes
noncomputable def count_computes : PolyComputes count :=
  (finalOpened_computes.pair ((cf_computes 0).comp (field_computes 2))).comp BinaryFiniteContext.countInter_computes
end MetricKMedianRecovery.BitMachine.BinaryLengthQuery

namespace MetricKMedianRecovery.BitMachine.BinaryLengthSearch
open WordOperations WordList BinaryArithmetic RationalLeaves
open BinaryFiniteMachine (historyBits)
open BinaryOpeningPayment (field field_computes field_encode)
noncomputable def leftHistory_computes : PolyComputes leftHistory := leftInput_computes.comp BinaryLengthQuery.chosen_computes
noncomputable def rightHistory_computes : PolyComputes rightHistory := rightInput_computes.comp BinaryLengthQuery.chosen_computes
noncomputable def leftSuccess_computes : PolyComputes leftSuccess :=
  list_computes [(fun _=>(0:ℕ).bits),lower,(fun _=>[]),leftHistory,(fun _=>[])] (by
    intro f hf; refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl|rfl|rfl
    · exact ⟨const_computes _⟩
    · exact ⟨lower_computes⟩
    · exact ⟨const_computes _⟩
    · exact ⟨leftHistory_computes⟩
    · exact ⟨const_computes _⟩)
noncomputable def rightSuccess_computes : PolyComputes rightSuccess :=
  list_computes [(fun _=>(0:ℕ).bits),upper,(fun _=>[]),rightHistory,(fun _=>[])] (by
    intro f hf; refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl|rfl|rfl
    · exact ⟨const_computes _⟩
    · exact ⟨upper_computes⟩
    · exact ⟨const_computes _⟩
    · exact ⟨rightHistory_computes⟩
    · exact ⟨const_computes _⟩)
noncomputable def bracket_computes : PolyComputes bracket :=
  list_computes [(fun _=>(1:ℕ).bits),lower,upper,leftHistory,rightHistory] (by
    intro f hf; refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl|rfl|rfl
    · exact ⟨const_computes _⟩
    · exact ⟨lower_computes⟩
    · exact ⟨upper_computes⟩
    · exact ⟨leftHistory_computes⟩
    · exact ⟨rightHistory_computes⟩)
noncomputable def leftEqual_computes : PolyComputes (fun x=>[leftEqual x]) :=
  NatOps.eq (leftInput_computes.comp BinaryLengthQuery.count_computes) boundK_computes
noncomputable def rightEqual_computes : PolyComputes (fun x=>[rightEqual x]) :=
  NatOps.eq (rightInput_computes.comp BinaryLengthQuery.count_computes) boundK_computes
noncomputable def finish_computes : PolyComputes finish := leftEqual_computes.cond leftSuccess_computes
  (rightEqual_computes.cond rightSuccess_computes bracket_computes)
noncomputable def input_computes : PolyComputes input := id_computes.pair (BinaryOrientedSearch.run_computes BinaryLengthQuery.count_computes)
noncomputable def run_computes : PolyComputes run := input_computes.comp finish_computes
end MetricKMedianRecovery.BitMachine.BinaryLengthSearch

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_SensitiveMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySensitive
open WordOperations WordList BinaryArithmetic RationalLeaves CanonicalLengthView
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
open BinaryOpeningPayment (field field_computes field_encode)
noncomputable def earlyEqual_computes : PolyComputes (fun x=>[earlyEqual x]) :=
  NatOps.eq (atZero_computes.comp BinaryLengthQuery.count_computes) (field_computes 5)
noncomputable def run_computes : PolyComputes run := earlyEqual_computes.cond early_computes
  (searchInput_computes.comp BinaryLengthSearch.run_computes)
end MetricKMedianRecovery.BitMachine.BinarySensitive

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
attribute [local irreducible] Take.run BinaryLabel.sort
noncomputable def seed_computes : PolyComputes seed :=
  (((field_computes 3).pair (field_computes 2)).comp Take.run_computes).comp BinaryLabel.sort_computes
noncomputable def state_computes : PolyComputes state :=
  list_computes [field 0,field 1,field 2,seed] (by
    intro f hf; refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl|rfl
    · exact ⟨field_computes 0⟩
    · exact ⟨field_computes 1⟩
    · exact ⟨field_computes 2⟩
    · exact ⟨seed_computes⟩)
noncomputable def run_computes : PolyComputes run :=
  (fuel.computes.pair state_computes).comp (BinaryLocalSearch.run_computes 5)
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
noncomputable def run_computes : PolyComputes run :=
  anchorInput_computes.comp (BinaryLocalAnchor.run_computes.comp BinaryProjection.run_computes)
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
noncomputable def anchor_computes : PolyComputes anchor := anchorInput_computes.comp BinaryMetricAnchor.run_computes
noncomputable def recoveryParams_computes : PolyComputes recoveryParams := list_computes
  [src 0,src 1,src 2,src 3,anchor,src 4,fun _=>BinaryRational.encode 0,fun _=>(0:ℕ).bits] (by
    intro f hf; refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals first | exact ⟨src_computes _⟩ | exact ⟨anchor_computes⟩ | exact ⟨const_computes _⟩)
noncomputable def bare_computes : PolyComputes bare := recoveryParams_computes.pair ((src_computes 6).pair (const_computes []))
noncomputable def demand_computes (Q : Polynomial ℕ) : PolyComputes (demand Q) := bare_computes.comp (counter Q).computes
attribute [local irreducible] counter demand bare RawTake.run UnaryResources.lengthBits BinaryIntegralRecovery.Guesses.budget BinaryIntegralRecovery.Guesses.run
attribute [local irreducible] mapWith
attribute [local irreducible] start calls
noncomputable def demands_computes (Q : Polynomial ℕ) : PolyComputes (demands Q) :=
  PolyComputes.comp (f := fun input=>pairBits (input,ranks input)) (g := mapWith (demand Q))
    (id_computes.pair ranks_computes) (mapWith_computes (demand_computes Q))
noncomputable def budget (Q : Polynomial ℕ) : Polynomial ℕ := (demands_computes Q).lengthPolynomial
end MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch

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

noncomputable def leafInput_computes : PolyComputes leafInput :=
  list_computes [field 1,field 2,price,sf 3,root,common,rf 1,rightHeight,rf 3,rf 4] (by
    intro f hf; refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact ⟨field_computes 1⟩
    · exact ⟨field_computes 2⟩
    · exact ⟨price_computes⟩
    · exact ⟨sf_computes 3⟩
    · exact ⟨root_computes⟩
    · exact ⟨common_computes⟩
    · exact ⟨rf_computes 1⟩
    · exact ⟨rightHeight_computes⟩
    · exact ⟨rf_computes 3⟩
    · exact ⟨rf_computes 4⟩)
noncomputable def finishInput_computes : PolyComputes finishInput :=
  list_computes [BinaryCoupled.leafBank ∘ leafInput,price,BinaryCoupled.leafPrefix ∘ leafInput,rf 3] (by
    intro f hf; refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl|rfl
    · exact ⟨leafInput_computes.comp BinaryCoupled.leafBank_computes⟩
    · exact ⟨price_computes⟩
    · exact ⟨leafInput_computes.comp BinaryCoupled.leafPrefix_computes⟩
    · exact ⟨rf_computes 3⟩)
noncomputable def run_computes : PolyComputes run := by
  unfold run
  simpa only [Function.comp_def] using success_computes.cond
    ((const_computes []).pair (finishInput_computes.comp BinaryCoupled.finish_computes))
    ((const_computes [true]).pair (leafInput_computes.comp BinaryCoupled.leafResult_computes))
end MetricKMedianRecovery.BitMachine.BinaryPlanResult

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_ResolveMachine
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryResolve
open WordOperations WordList BinaryArithmetic RationalLeaves CanonicalCoupledMerge CanonicalLengthView
open BinaryOpeningPayment (field field_computes field_encode)
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
noncomputable def viewInput_computes : PolyComputes viewInput :=
  list_computes [bf 2,bf 2,H,G,(fun x=>pairBits (bf 0 x,bf 1 x))] (by
    intro f hf; refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl|rfl|rfl
    · exact ⟨bf_computes _⟩
    · exact ⟨bf_computes _⟩
    · exact ⟨H_computes⟩
    · exact ⟨G_computes⟩
    · exact ⟨(bf_computes 0).pair (bf_computes 1)⟩)
noncomputable def view_computes : PolyComputes view := viewInput_computes.comp BinaryLength.view_computes
noncomputable def plan_computes : PolyComputes plan := view_computes.comp WordOperations.tail_computes
noncomputable def sensitiveInput_computes : PolyComputes sensitiveInput :=
  list_computes [field 0,field 1,field 2,field 3,field 4,field 5,field 6,H,T,U,plan] (by
    intro f hf; refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact ⟨field_computes 0⟩
    · exact ⟨field_computes 1⟩
    · exact ⟨field_computes 2⟩
    · exact ⟨field_computes 3⟩
    · exact ⟨field_computes 4⟩
    · exact ⟨field_computes 5⟩
    · exact ⟨field_computes 6⟩
    · exact ⟨H_computes⟩
    · exact ⟨T_computes⟩
    · exact ⟨U_computes⟩
    · exact ⟨plan_computes⟩)
noncomputable def planResultInput_computes : PolyComputes planResultInput :=
  list_computes [sensitiveInput,field 7,field 8,BinarySensitive.run ∘ sensitiveInput] (by
    intro f hf; refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl|rfl
    · exact ⟨sensitiveInput_computes⟩
    · exact ⟨field_computes _⟩
    · exact ⟨field_computes _⟩
    · exact ⟨sensitiveInput_computes.comp BinarySensitive.run_computes⟩)
noncomputable def sensitive_computes : PolyComputes sensitive := by
  change PolyComputes (fun x=>if view x=[] then pairBits ([],BinaryCoupled.finish (fallbackInput x)) else BinaryPlanResult.run (planResultInput x))
  simpa only [Function.comp_def,decide_eq_true_eq] using (view_computes.comp isEmpty_computes).cond
    ((const_computes []).pair (fallbackInput_computes.comp BinaryCoupled.finish_computes))
    (planResultInput_computes.comp BinaryPlanResult.run_computes)
noncomputable def run_computes : PolyComputes run := by
  have h0:=NatOps.eq (rf_computes 0) (const_computes (0:ℕ).bits)
  have h1:=NatOps.eq (rf_computes 0) (const_computes (1:ℕ).bits)
  change PolyComputes (fun x=>if value (rf 0 x)=0 then pairBits ([],BinaryCoupled.finish (finishInput x)) else
    if value (rf 0 x)=1 then pairBits ([true],BinaryCoupled.same (sameInput x)) else sensitive x)
  simpa only [value_bits,decide_eq_true_eq,Function.comp_def] using h0.cond
    ((const_computes []).pair (finishInput_computes.comp BinaryCoupled.finish_computes))
    (h1.cond ((const_computes [true]).pair (sameInput_computes.comp BinaryCoupled.same_computes)) sensitive_computes)
end MetricKMedianRecovery.BitMachine.BinaryResolve

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_StepMachine
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
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
noncomputable def active_computes : PolyComputes active := by
  unfold active
  simpa only [Function.comp_def] using
    (NatOps.eq c_computes (field_computes 5)).cond
      ((const_computes []).pair (finishInput_computes.comp BinaryCoupled.finish_computes))
      (sandwiched_computes.cond (resolveInput_computes.comp BinaryResolve.run_computes)
        ((const_computes [true]).pair (advanceInput_computes.comp BinaryCoupled.advance_computes)))
noncomputable def run_computes : PolyComputes run := by
  unfold run
  simpa only [Function.comp_def] using
    nonempty_computes.cond active_computes ((const_computes []).pair (fallbackInput_computes.comp BinaryCoupled.finish_computes))
end MetricKMedianRecovery.BitMachine.BinaryCoupledStep

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_LoopMachine
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCoupledLoop
open WordOperations WordList BinaryArithmetic RationalLeaves CanonicalCoupledMerge
open BinaryOpeningPayment (field field_computes field_encode)
open BinaryCoupled (stateBits outcomeBits outputBits)
noncomputable def next_computes : PolyComputes next := by
  unfold next
  simpa only [List.map_cons,List.map_nil,Function.comp_def] using list_computes
    [field 0,List.tail ∘ field 1,List.cons true ∘ field 2,field 3,field 4,field 5,BinaryCoupledStep.run ∘ input] (by
      intro component membership; refine Classical.choice ?_
      simp only [List.mem_cons,List.not_mem_nil,or_false] at membership
      rcases membership with rfl|rfl|rfl|rfl|rfl|rfl|rfl
      · exact ⟨field_computes 0⟩
      · exact ⟨(field_computes 1).comp WordOperations.tail_computes⟩
      · exact ⟨(const_computes [true]).append (field_computes 2)⟩
      · exact ⟨field_computes 3⟩
      · exact ⟨field_computes 4⟩
      · exact ⟨field_computes 5⟩
      · exact ⟨input_computes.comp BinaryCoupledStep.run_computes⟩)
noncomputable def step_computes : PolyComputes step := by
  change PolyComputes (fun x=>if extractPrefix (field 6 x)=[] then x else if field 1 x=[] then x else next x)
  simpa only [Function.comp_def,decide_eq_true_eq,id_eq] using
    ((field_computes 6).comp extractPrefix_computes |>.comp isEmpty_computes).cond id_computes
      (((field_computes 1).comp isEmpty_computes).cond id_computes next_computes)
attribute [local instance] RationalLeaves.metric
end MetricKMedianRecovery.BitMachine.BinaryCoupledLoop

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_LoopSize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCoupledLoop
open WordOperations WordList BinaryArithmetic RationalLeaves RationalHeight CanonicalCoupledMerge
open BinaryOpeningPayment (field field_computes field_encode)
open BinaryCoupled (stateBits outcomeBits outputBits)
noncomputable def stateRun_computes : PolyComputes stateRun :=
  iterationInput_computes.comp (BoundedIteration.run_computes step_computes)
noncomputable def run_computes : PolyComputes run := by
  unfold run
  simpa only [Function.comp_def] using
    stateRun_computes.comp ((field_computes 6).comp discardPrefix_computes)
attribute [local instance] RationalLeaves.metric
attribute [local irreducible] BinaryCoupledStep.run
end MetricKMedianRecovery.BitMachine.BinaryCoupledLoop

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_InitialLoop
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
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
attribute [local irreducible] BinaryInitialQuery.count BinaryInitialQuery.history BinaryCoupledLoop.run BinaryBisection.run
noncomputable def bracket_computes : PolyComputes bracket := bracketInput_computes.comp (BinaryBisection.run_computes BinaryInitialQuery.count_computes)

noncomputable def lower_computes : PolyComputes lower := bracket_computes.comp extractPrefix_computes

noncomputable def lowerInput_computes : PolyComputes lowerInput := ctx_computes.pair lower_computes

noncomputable def lowerCount_computes : PolyComputes lowerCount := lowerInput_computes.comp BinaryInitialQuery.count_computes

noncomputable def lowerHistory_computes : PolyComputes lowerHistory := lowerInput_computes.comp BinaryInitialQuery.history_computes

noncomputable def lowerFinish_computes : PolyComputes lowerFinish := list_computes [(fun _=>[]),lower,lowerHistory] (by
  intro f hf; refine Classical.choice ?_
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
  rcases hf with rfl|rfl|rfl
  · exact ⟨const_computes []⟩
  · exact ⟨lower_computes⟩
  · exact ⟨lowerHistory_computes⟩)

noncomputable def upper_computes : PolyComputes upper := bracket_computes.comp discardPrefix_computes

noncomputable def upperInput_computes : PolyComputes upperInput := ctx_computes.pair upper_computes

noncomputable def upperCount_computes : PolyComputes upperCount := upperInput_computes.comp BinaryInitialQuery.count_computes

noncomputable def upperHistory_computes : PolyComputes upperHistory := upperInput_computes.comp BinaryInitialQuery.history_computes

noncomputable def upperFinish_computes : PolyComputes upperFinish := list_computes [(fun _=>[]),upper,upperHistory] (by
  intro f hf; refine Classical.choice ?_
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
  rcases hf with rfl|rfl|rfl
  · exact ⟨const_computes []⟩
  · exact ⟨upper_computes⟩
  · exact ⟨upperHistory_computes⟩)

noncomputable def initialState_computes : PolyComputes initialState := list_computes [(fun _=>[]),(fun _=>[]),(fun _=>[]),lower,upper,upperHistory,lowerHistory] (by
  intro f hf; refine Classical.choice ?_
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
  rcases hf with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact ⟨const_computes []⟩
  · exact ⟨const_computes []⟩
  · exact ⟨const_computes []⟩
  · exact ⟨lower_computes⟩
  · exact ⟨upper_computes⟩
  · exact ⟨upperHistory_computes⟩
  · exact ⟨lowerHistory_computes⟩)

noncomputable def initialOutcome_computes : PolyComputes initialOutcome := (const_computes [true]).pair initialState_computes

noncomputable def loopInput_computes : PolyComputes loopInput := list_computes [field 0,field 3,(fun _=>[]),far,field 2,field 4,initialOutcome] (by
  intro f hf; refine Classical.choice ?_
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
  rcases hf with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact ⟨field_computes 0⟩
  · exact ⟨field_computes 3⟩
  · exact ⟨const_computes []⟩
  · exact ⟨far_computes⟩
  · exact ⟨field_computes 2⟩
  · exact ⟨field_computes 4⟩
  · exact ⟨initialOutcome_computes⟩)

noncomputable def normal_computes : PolyComputes normal := by
  change PolyComputes (fun x=>if value (lowerCount x)=value (field 4 x) then lowerFinish x else
    if value (upperCount x)=value (field 4 x) then upperFinish x else BinaryCoupledLoop.run (loopInput x))
  simpa only [decide_eq_true_eq,Function.comp_def] using (NatOps.eq lowerCount_computes (field_computes 4)).cond
    lowerFinish_computes ((NatOps.eq upperCount_computes (field_computes 4)).cond
      upperFinish_computes (loopInput_computes.comp BinaryCoupledLoop.run_computes))

noncomputable def run_computes : PolyComputes run := by
  change PolyComputes (fun x=>if value (loCount x)≤value (field 4 x) then pairBits ([],loFinish x) else pairBits ([true],normal x))
  simpa only [decide_eq_true_eq,Function.comp_def] using (NatOps.le loCount_computes (field_computes 4)).cond
    ((const_computes []).pair loFinish_computes) ((const_computes [true]).pair normal_computes)

end MetricKMedianRecovery.BitMachine.BinaryInitial

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_InitialAuto
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryInitialAuto
open WordOperations WordList BinaryArithmetic RationalLeaves
open BinaryOpeningPayment (field field_computes field_encode)
open BinaryFiniteContext (labels setBits)
variable {m d : ℕ}
noncomputable def run_computes (v : ℚ) (C : ℕ) : PolyComputes (run v C) :=
  (initialInput_computes v C).comp BinaryInitial.run_computes
end MetricKMedianRecovery.BitMachine.BinaryInitialAuto

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
noncomputable def run_computes (v : ℚ) (C : ℕ) : PolyComputes (run v C) :=
  (BinaryInitialAuto.run_computes v C).comp extract_computes
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
noncomputable def padded_computes : PolyComputes padded :=
  (cons_computes (field_computes 2) (cons_computes (field_computes 3)
    (cons_computes target_computes (const_computes [])))).comp BinaryCompletionPad.run_computes
noncomputable def localInput_computes : PolyComputes localInput := by
  unfold localInput
  simpa only [Function.comp_def,encode] using
    cons_computes (field_computes 0) (cons_computes (field_computes 1)
      (cons_computes ((field_computes 2).comp (map_computes BinaryProjection.originalWord_computes))
        (cons_computes (padded_computes.comp BinaryProjection.lift_computes) (const_computes []))))
noncomputable def run_computes : PolyComputes run := by
  unfold run
  simpa only [Function.comp_def] using
    localInput_computes.comp (BinaryLocalRefine.run_computes.comp BinaryProjection.run_computes)
end MetricKMedianRecovery.BitMachine.BinarySurplusPostprocess

namespace MetricKMedianRecovery.BitMachine.BinaryCanonicalSurplus
open WordOperations WordList BinaryArithmetic RationalLeaves CanonicalCoupledMerge
open BinaryOpeningPayment (field field_computes field_encode)
variable {m : ℕ}
noncomputable def postInput_computes (v : ℚ) (C : ℕ) : PolyComputes (postInput v C) := by
  unfold postInput
  simpa only [Function.comp_def,encode] using
    cons_computes (extractPrefix_computes.comp (field_computes 0))
      (cons_computes (extractPrefix_computes.comp (field_computes 1))
        (cons_computes (extractPrefix_computes.comp (field_computes 2))
          (cons_computes (extractPrefix_computes.comp (BinaryInitialProject.run_computes v C))
            (cons_computes discardPrefix_computes (const_computes [])))))
noncomputable def run (v : ℚ) (C : ℕ) : List Bool→List Bool := BinarySurplusPostprocess.run ∘ postInput v C
noncomputable def run_computes (v : ℚ) (C : ℕ) : PolyComputes (run v C) :=
  (postInput_computes v C).comp BinarySurplusPostprocess.run_computes
end MetricKMedianRecovery.BitMachine.BinaryCanonicalSurplus

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
noncomputable def run (v : ℚ) (C : ℕ) : List Bool→List Bool := BinaryCanonicalSurplus.run v C ∘ runInput
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
noncomputable def surplus (v : ℚ) (C : ℕ) : List Bool→ List Bool := BinaryMetricSurplus.run v C ∘ surplusInput
noncomputable def surplusCalls (v : ℚ) (C : ℕ) (x : List Bool) : List Bool :=
  mapWith (surplus v C) (pairBits (x,BinaryIntegralDispatch.ranks x))
attribute [local irreducible] mapWith
noncomputable def candidates (v : ℚ) (C : ℕ) (Q : Polynomial ℕ) (d : ℕ) (x : List Bool) : List Bool :=
  cons (Dsp.run Q d x) (surplusCalls v C x)
end MetricKMedianRecovery.BitMachine.BinaryIntegralAll

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
namespace A
noncomputable abbrev budget := BinaryIntegralDispatch.budget
end A
attribute [local irreducible] base RawTake.run UnaryResources.lengthBits
attribute [local irreducible] BinaryIntegralDispatch.budget norm src clamp BinaryInputParser.Metric.count
end MetricKMedianRecovery.BitMachine.BinaryGlobalCall

end OAI
end


