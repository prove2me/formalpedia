-- Prove2me | Definitions.Def_Q238K049
-- name    : Q238K049
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T23:48:31.064187+00:00
-- url     : https://prove2.me/theorems/0fb1fe6a-8e8a-45e1-ab7a-00797b9408bf
-- title:
--   Definitions bundle Q238K049 of the split of OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 104 declarations of OpenAI's Lean: 104 definitions. The definitions and types are `OAI.MetricKMedianRecovery.BitMachine.BinaryCanonicalSurplus.run`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCorrection.mapSet_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupled.mapFree_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.H_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.QG_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.Q_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.T_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.W_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.advanceInput_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.bankInput_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.banks_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.base_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.contBase_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.crossInput_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.ctx_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.fallbackInput_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.finishInput_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.mappedFree_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.mappedPrefix_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.nonempty_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.power_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.prefixG_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCross.finalOpened_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCross.leftLength_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCross.rightLength_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteCross.scanInput_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.scales_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInitial.bracketInput_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInitialProject.extract_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralAll.Dsp.run`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch.R.budget`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch.call`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch.callInput`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch.calls`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch.counter`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch.cutRaw`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch.demand`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch.demands`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch.run`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch.runInput` and 64 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedianRecovery_Algorithms_GlobalOuter`, `KMedianRecovery_Algorithms_IntegralAll`, `KMedianRecovery_Algorithms_IntegralRecoveryAll`, `KMedianRecovery_Algorithms_IntegralRecoveryAmplified`, `KMedianRecovery_Algorithms_IntegralRecoveryDemand`, `KMedianRecovery_Algorithms_IntegralRecoveryGuesses`, `KMedianRecovery_Algorithms_IntegralRecoveryRepeat`, `KMedianRecovery_Algorithms_IntegralRecoverySelection`, `KMedianRecovery_Encoding_CoupledEncode`, `KMedianRecovery_Encoding_LengthEncode`, `KMedianRecovery_Encoding_WordExtras`, `KMedianRecovery_Geometry_MetricAnchor`, `KMedianRecovery_Geometry_MetricArrays`, `KMedianRecovery_Machines_InitialLoop`, `KMedianRecovery_Machines_LengthQuery`, `KMedianRecovery_Machines_MatchFold`, `KMedianRecovery_Machines_MatchSize`, `KMedianRecovery_Machines_ProjectionMachine`, `KMedianRecovery_Machines_RefineMachine`, `KMedianRecovery_Machines_ResolveMachine`, `KMedianRecovery_Machines_ScanMachine`, `KMedianRecovery_Machines_StepMachine`, `KMedianRecovery_Recovery_CrossCount`, `KMedianRecovery_Recovery_CrossEdge`, `KMedianRecovery_Recovery_InitialProject`, `KMedianRecovery_Recovery_LengthCandidates`, `KMedianRecovery_Recovery_OrientedSearch`, `KMedianRecovery_Recovery_PlanResult`, `KMedianRecovery_Recovery_RefineMath`, `KMedianRecovery_Recovery_RegularChain`, `KMedianRecovery_Strictness_SurplusPostprocess`.
--
--   **Imports.** It imports the published bundle `Def_KMedianRefinedRecovery`; the bundles `Q238K041`, `Q238K042`, `Q238K043`, `Q238K044`, `Q238K045` and `Q238K046` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q238K051` and `Q238K052`; the statements `OAI.MetricKMedianRecovery.BitMachine.BinaryCanonicalSurplus.produce_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses.all_counts_budget_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses.integral_recovery_s238` and `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses.polynomial_recovery_s238`; the proofs of `OAI.MetricKMedianRecovery.BitMachine.BinaryCanonicalSurplus.produce_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses.all_counts_budget_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses.integral_recovery_s238` and `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses.polynomial_recovery_s238`.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_KMedianRefinedRecovery
import Definitions.Def_Q238K041
import Definitions.Def_Q238K042
import Definitions.Def_Q238K043
import Definitions.Def_Q238K044
import Definitions.Def_Q238K045
import Definitions.Def_Q238K046

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_WordExtras
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryJump
open WordOperations WordList RationalLeaves CanonicalMergeRefinement BinaryArithmetic
open BinaryFiniteContext (labels setBits)
open BinaryOpeningPayment (field field_computes field_encode)
noncomputable def accepts_computes : PolyComputes (fun x=>[accepts x]) :=
  ((source_computes.pair (cf_computes 3)).comp WordEq.eq_computes).and
    (((target_computes.pair (cf_computes 4)).comp WordEq.eq_computes).and
      ((((jf_computes 4).pair (cf_computes 0)).comp BinaryLabel.contains_computes).and
        labelsCheck_computes))

end MetricKMedianRecovery.BitMachine.BinaryJump

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
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_IntegralRecoveryDemand
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair
open WordOperations Polynomial
open BinaryOpeningPayment (field field_computes field_encode)
noncomputable def completionWord_computes : PolyComputes completionWord := (src_computes 1).comp completionCounter.computes
noncomputable def demandWord_computes : PolyComputes demandWord := sampleWord_computes.append completionWord_computes
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
attribute [local irreducible] extra Fair.raw Fair.demandWord Fair.run BinaryMetricBest.run RawUnary.run BinarySeed.rows
  BinaryIntegralRecovery.result BinaryFinSet.encode BinarySampler.Parameters.pack BinaryMetricBest.best Fair.output List.ofFn BinarySeed.raw
noncomputable def bword_computes : PolyComputes bword := Fair.demandWord_computes.comp RawUnary.run_computes
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
noncomputable def demandWord_computes (Q : Polynomial ℕ) : PolyComputes (demandWord Q) :=
  UnaryResources.copy_computes (Repeat.rword_computes Q) Repeat.bword_computes
attribute [local irreducible] demandBits
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
noncomputable def costWord_computes : PolyComputes costWord := UnaryResources.copy_computes
  ((src_computes 2).comp Count.run_computes) (extractPrefix_computes.comp (BinarySampler.Parameters.unary_computes 5))
noncomputable def costRange_computes : PolyComputes costRange :=
  (costWord_computes.append (const_computes _)).comp BinaryEllipsoidInitial.indices_computes
noncomputable def countRange_computes : PolyComputes countRange :=
  ((src_computes 1).append (const_computes _)).comp BinaryEllipsoidInitial.indices_computes
noncomputable def choices_computes : PolyComputes choices := (costRange_computes.pair countRange_computes).comp cross_computes
noncomputable def source_computes (j : ℕ) : PolyComputes (source j) := extractPrefix_computes.comp (src_computes j)
noncomputable def atParams_computes : PolyComputes atParams := list_computes
  [source 0,source 1,source 2,source 3,source 4,source 5,price,count] (by
    intro f hf; refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals first | exact ⟨source_computes _⟩ | exact ⟨price_computes⟩ | exact ⟨count_computes⟩)
noncomputable def atInput_computes : PolyComputes atInput := atParams_computes.pair
  ((extractPrefix_computes.comp extra_computes).pair (extractPrefix_computes.comp Fair.raw_computes))
attribute [local irreducible] mapWith
attribute [local irreducible] sizeWord candidateWords
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
noncomputable def atDemand_computes (Q : Polynomial ℕ) : PolyComputes (atDemand Q) :=
  atInput_computes.comp (Repeat.FiniteTape.demandWord_computes Q)
attribute [local irreducible] mapWith
noncomputable def demandWords_computes (Q : Polynomial ℕ) : PolyComputes (demandWords Q) :=
  PolyComputes.comp (f := fun input=>pairBits (input,choices input)) (g := mapWith (atDemand Q))
    (id_computes.pair choices_computes) (mapWith_computes (atDemand_computes Q))
noncomputable def budget (Q : Polynomial ℕ) : Polynomial ℕ := (demandWords_computes Q).lengthPolynomial
end MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_LengthEncode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryLength
open WordOperations WordList RationalLeaves CanonicalLengthView BinaryArithmetic
open BinaryFiniteContext (labels setBits)
open BinaryOpeningPayment (field field_computes field_encode)
attribute [local irreducible] BinaryLabelMatrix.row
noncomputable def sameRow_computes : PolyComputes (fun x=>[sameRow x]) :=
  ((row_computes 1).pair (row_computes 2)).comp WordEq.eq_computes
noncomputable def extra_computes : PolyComputes (fun x=>[extra x]) := by
  have h:=isFree_computes.cond (freeOut_computes.and sameRow_computes) (const_computes [true])
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  unfold extra
  split_ifs <;> rfl
noncomputable def accepts_computes : PolyComputes (fun x=>[accepts x]) := rootIn_computes.and
  (((cf_computes 2).pair source_computes |>.comp WordEq.eq_computes).and
    (((cf_computes 3).pair target_computes |>.comp WordEq.eq_computes).and extra_computes))
end MetricKMedianRecovery.BitMachine.BinaryLength

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_CrossCount
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

noncomputable def finalOpened_computes : PolyComputes finalOpened :=
  (opened_computes.pair (discardPrefix_computes.comp discardPrefix_computes)).comp BinaryFiniteMachine.after_computes
end MetricKMedianRecovery.BitMachine.BinaryCross

namespace MetricKMedianRecovery.BitMachine.BinaryJump
open WordOperations WordList RationalLeaves CanonicalMergeRefinement BinaryArithmetic
open BinaryFiniteContext (labels setBits)
open BinaryOpeningPayment (field field_computes field_encode)
noncomputable def removedTail_computes : PolyComputes removedTail := by
  unfold removedTail
  have h:=NatOps.sub ((field_computes 3).comp lengthBits_computes) (const_computes (1:ℕ).bits)
  simpa only [Function.comp_def,value_bits] using (h.pair (field_computes 4)).comp Drop.run_computes
attribute [local irreducible] removedTail
noncomputable def removeOp_computes : PolyComputes removeOp :=
  list_computes [fun _=>(1:ℕ).bits,jf 0,jf 2,removedTail ∘ extractPrefix,jf 1] (by
    intro f hf; refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl|rfl|rfl
    · exact ⟨const_computes _⟩
    · exact ⟨jf_computes _⟩
    · exact ⟨jf_computes _⟩
    · exact ⟨extractPrefix_computes.comp removedTail_computes⟩
    · exact ⟨jf_computes _⟩)
noncomputable def removes_computes : PolyComputes removes := by
  have removesComputes :=
    (id_computes.pair ((field_computes 3).comp Slices.run_computes)).comp (mapWith_computes removeOp_computes)
  unfold removes
  simpa only [Function.comp_def, id_eq] using removesComputes
noncomputable def candidates_computes : PolyComputes candidates := (adds_computes.append removes_computes).append replaces_computes
noncomputable def view_computes : PolyComputes view := (id_computes.pair candidates_computes).comp (Find.run_computes accepts_computes)
end MetricKMedianRecovery.BitMachine.BinaryJump

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

noncomputable def interior_computes : PolyComputes interior :=
  ((cf_computes 1).pair ((cf_computes 2).pair base_computes)).comp BinaryFiniteMachine.continuation_computes
noncomputable def chosen_computes : PolyComputes chosen := isZero_computes.cond (cf_computes 6)
  (isUpper_computes.cond (cf_computes 7) interior_computes)
noncomputable def finalOpened_computes : PolyComputes finalOpened :=
  (opened_computes.pair chosen_computes).comp BinaryFiniteMachine.after_computes
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
end MetricKMedianRecovery.BitMachine.BinaryLengthSearch

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
namespace R
noncomputable abbrev budget := BinaryIntegralRecovery.Guesses.budget
end R
variable {n : ℕ}
noncomputable def counter (Q : Polynomial ℕ) : PolynomialCounter (R.budget Q) := PolynomialCounter.choose _
noncomputable def demand (Q : Polynomial ℕ) : List Bool→List Bool := (counter Q).word ∘ bare
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
noncomputable def demands (Q : Polynomial ℕ) (x : List Bool) : List Bool := mapWith (demand Q) (pairBits (x,ranks x))
end MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_CoupledEncode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCorrection
open WordOperations WordList BinaryArithmetic RationalLeaves CanonicalCoupledMerge
open BinaryOpeningPayment (field field_computes field_encode)
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
noncomputable def mapSet_computes : PolyComputes mapSet := mapRow_computes.comp BinaryLabel.sort_computes
end MetricKMedianRecovery.BitMachine.BinaryCorrection

namespace MetricKMedianRecovery.BitMachine.BinaryCoupled
open WordOperations WordList BinaryArithmetic RationalLeaves CanonicalCoupledMerge
open BinaryOpeningPayment (field field_computes field_encode)
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
noncomputable def mapFree_computes : PolyComputes mapFree := ((field_computes 2).pair (field_computes 0)).comp BinaryCorrection.mapSet_computes
attribute [local irreducible] BinaryCorrection.mapHistory
end MetricKMedianRecovery.BitMachine.BinaryCoupled

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_CrossEdge
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

noncomputable def leftLength_computes : PolyComputes leftLength := (leftNode_computes.comp extractPrefix_computes).comp lengthBits_computes
noncomputable def rightLength_computes : PolyComputes rightLength := (rightNode_computes.comp extractPrefix_computes).comp lengthBits_computes
end MetricKMedianRecovery.BitMachine.BinaryCross

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_LengthCandidates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryLength
open WordOperations WordList RationalLeaves CanonicalLengthView BinaryArithmetic CanonicalMergeRefinement
open BinaryFiniteContext (labels setBits)
open BinaryOpeningPayment (field field_computes field_encode)
attribute [local irreducible] WordList.mapWith
noncomputable def view_computes : PolyComputes view :=
  (id_computes.pair candidates_computes).comp (Find.run_computes accepts_computes)
end MetricKMedianRecovery.BitMachine.BinaryLength

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

noncomputable def root_computes : PolyComputes root := (sf_computes 10).comp (field_computes 1)
end MetricKMedianRecovery.BitMachine.BinaryPlanResult

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_ResolveMachine
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
end MetricKMedianRecovery.BitMachine.BinaryResolve

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_MatchFold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryMatch
open WordOperations WordList RationalLeaves CanonicalMatch
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
open BinaryOpeningPayment (field field_computes field_encode)

attribute [local irreducible] BinaryLabel.copied
noncomputable def advanced_computes : PolyComputes advanced := advancingInput_computes.comp BinaryAdvance.run_computes
attribute [local irreducible] advanced
noncomputable def suffix_computes : PolyComputes rest := advanced_computes.comp (field_computes 0)
noncomputable def vertices_computes : PolyComputes vertices :=
  (sf_computes 2).append (advanced_computes.comp (field_computes 1))
noncomputable def step_computes : PolyComputes step := list_computes [front,rest,vertices] (by
  intro f hf; refine Classical.choice ?_
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
  rcases hf with rfl|rfl|rfl
  · exact ⟨prefix_computes⟩
  · exact ⟨suffix_computes⟩
  · exact ⟨vertices_computes⟩)

end MetricKMedianRecovery.BitMachine.BinaryMatch

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_MatchSize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryMatch
open WordOperations WordList RationalLeaves CanonicalMatch CanonicalMergePath PhaseSequence
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)

noncomputable def run_computes : PolyComputes run :=
  (capacity.computes.pair id_computes).comp (CappedFold.run_computes step_computes)
end MetricKMedianRecovery.BitMachine.BinaryMatch

namespace MetricKMedianRecovery.BitMachine.BinaryRegular
open WordOperations WordList RationalLeaves CanonicalMergePath PhaseSequence
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
open BinaryOpeningPayment (field field_computes field_encode)

noncomputable def matched_computes : PolyComputes matched := matchInput_computes.comp BinaryMatch.run_computes
noncomputable def prunedInput_computes : PolyComputes prunedInput := by
  unfold prunedInput
  simpa only [Function.comp_def] using (field_computes 2).pair (matched_computes.comp (field_computes 1))
noncomputable def run_computes : PolyComputes run := by
  have composeComputes (matchedFunction prunedFunction : List Bool → List Bool)
      (matchedComputes : PolyComputes matchedFunction) (prunedComputes : PolyComputes prunedFunction) :
      PolyComputes (fun input=>field 2 (matchedFunction input)++BinarySuffix.prune (prunedFunction input)) := by
    simpa only [Function.comp_def] using
      (matchedComputes.comp (field_computes 2)).append (prunedComputes.comp BinarySuffix.prune_computes)
  exact composeComputes matched prunedInput matched_computes prunedInput_computes
end MetricKMedianRecovery.BitMachine.BinaryRegular

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_RefineMath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryJump
open WordOperations WordList RationalLeaves CanonicalMergeRefinement
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
open BinaryOpeningPayment (field field_computes field_encode)
noncomputable def edgeView_computes : PolyComputes edgeView := (field_computes 0).comp view_computes
noncomputable def edge_computes : PolyComputes edge := by
  unfold edge
  simpa only [Function.comp_def,decide_eq_true_eq] using
    ((edgeView_computes.comp isEmpty_computes).cond (cons_computes edgeG_computes (const_computes []))
    ((edgeData_computes.pair (edgeView_computes.comp WordOperations.tail_computes)).comp expand_computes))
end MetricKMedianRecovery.BitMachine.BinaryJump

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_RefineMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRefine
open WordOperations WordList RationalLeaves CanonicalMergeRefinement
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
open BinaryOpeningPayment (field field_computes field_encode)
noncomputable def cutOp_computes : PolyComputes cutOp := by
  unfold cutOp
  simpa only [Function.comp_def,decide_eq_true_eq] using
    (cutTail_computes.comp isEmpty_computes).cond (const_computes []) (edgeInput_computes.comp BinaryJump.edge_computes)
noncomputable def run_computes : PolyComputes run := runInput_computes.comp (flatMapWith_computes cutOp_computes)
end MetricKMedianRecovery.BitMachine.BinaryRefine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_RegularChain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRegularChain
open WordOperations WordList RationalLeaves CanonicalMergePath PhaseSequence
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
open BinaryOpeningPayment (field field_computes field_encode)
attribute [local irreducible] BinaryRegular.run BinaryRefine.run
noncomputable def vertices_computes : PolyComputes vertices :=
  cons_computes (field_computes 4) (regularInput_computes.comp BinaryRegular.run_computes)
noncomputable def run_computes : PolyComputes run := (context_computes.pair vertices_computes).comp BinaryRefine.run_computes
end MetricKMedianRecovery.BitMachine.BinaryRegularChain

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_ScanMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryScan
open WordOperations WordList RationalLeaves CanonicalMergeCrossing
open BinaryCross (ctxBits nodeBits resultBits)
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
open BinaryOpeningPayment (field field_computes field_encode)
attribute [local irreducible] BinaryFiniteMachine.continuation BinaryNodeScan.run
noncomputable def opened_computes : PolyComputes opened :=
  ((cf_computes 0).comp (field_computes 3) |>.pair discardPrefix_computes).comp BinaryFiniteContext.union_computes
noncomputable def base_computes : PolyComputes base :=
  ((cf_computes 0).pair opened_computes).comp BinaryFiniteContext.replaceOpen_computes
noncomputable def contInput_computes : PolyComputes contInput := (cf_computes 1).pair ((cf_computes 2).pair base_computes)
noncomputable def node_computes : PolyComputes node := discardPrefix_computes.pair (contInput_computes.comp BinaryFiniteMachine.continuation_computes)
noncomputable def nodes_computes : PolyComputes nodes := by
  have composeComputes (contextFunction nodeFunction : List Bool → List Bool)
      (contextComputes : PolyComputes contextFunction) (nodeComputes : PolyComputes nodeFunction) :
      PolyComputes (fun input=>cons (field 5 input)
        (mapWith nodeFunction (pairBits (contextFunction input,field 6 input)))) := by
    simpa only [Function.comp_def] using cons_computes (field_computes 5)
      ((contextComputes.pair (field_computes 6)).comp (mapWith_computes nodeComputes))
  exact composeComputes mapCtx node mapCtx_computes node_computes
noncomputable def scanInput_computes : PolyComputes scanInput := list_computes [field 3,field 4,nodes] (by
  intro f hf; refine Classical.choice ?_
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
  rcases hf with rfl|rfl|rfl
  · exact ⟨field_computes _⟩
  · exact ⟨field_computes _⟩
  · exact ⟨nodes_computes⟩)
end MetricKMedianRecovery.BitMachine.BinaryScan

namespace MetricKMedianRecovery.BitMachine.BinaryFiniteCross
open WordOperations WordList RationalLeaves CanonicalMergePath PhaseSequence
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
open BinaryOpeningPayment (field field_computes field_encode)
attribute [local irreducible] BinaryRegularChain.run BinaryScan.run
noncomputable def scanInput_computes : PolyComputes scanInput :=
  list_computes [field 0,field 4,nextQ,crossCtx,field 9,firstNode,BinaryRegularChain.run ∘ chainInput] (by
    intro f hf; refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact ⟨field_computes _⟩
    · exact ⟨field_computes _⟩
    · exact ⟨nextQ_computes⟩
    · exact ⟨crossCtx_computes⟩
    · exact ⟨field_computes _⟩
    · exact ⟨firstNode_computes⟩
    · exact ⟨chainInput_computes.comp BinaryRegularChain.run_computes⟩)
end MetricKMedianRecovery.BitMachine.BinaryFiniteCross

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
noncomputable def mappedFree_computes : PolyComputes mappedFree :=
  (field_computes 6).comp (BinaryCoupled.mapFree_computes)
noncomputable def mappedPrefix_computes : PolyComputes mappedPrefix := by
  unfold mappedPrefix
  simpa only [Function.comp_def] using
    (field_computes 6).comp BinaryCoupled.mapPrefix_computes
noncomputable def Q_computes : PolyComputes Q :=
  ((const_computes []).pair mappedPrefix_computes).comp BinaryFiniteMachine.after_computes
noncomputable def power_computes : PolyComputes power := by
  unfold power
  simpa only [Function.comp_def] using
    ((field_computes 2).pair (bf_computes 5)).comp BinaryPhaseCount.power_computes
noncomputable def base_computes : PolyComputes base :=
  list_computes [bf 0,bf 1,bf 2,Q,bf 4,bf 5,power,sf 4] (by
    intro f hf; refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact ⟨bf_computes 0⟩
    · exact ⟨bf_computes 1⟩
    · exact ⟨bf_computes 2⟩
    · exact ⟨Q_computes⟩
    · exact ⟨bf_computes 4⟩
    · exact ⟨bf_computes 5⟩
    · exact ⟨power_computes⟩
    · exact ⟨sf_computes 4⟩
)
noncomputable def H_computes : PolyComputes H :=
  (sf_computes 5).comp (WordList.head_computes)
noncomputable def T_computes : PolyComputes T :=
  (sf_computes 5).comp (WordList.tail_computes)
noncomputable def QG_computes : PolyComputes QG :=
  (Q_computes.pair G_computes).comp BinaryFiniteContext.union_computes
noncomputable def contBase_computes : PolyComputes contBase :=
  list_computes [bf 0,bf 1,bf 2,QG,bf 4,bf 5,power,sf 4] (by
    intro f hf; refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact ⟨bf_computes 0⟩
    · exact ⟨bf_computes 1⟩
    · exact ⟨bf_computes 2⟩
    · exact ⟨QG_computes⟩
    · exact ⟨bf_computes 4⟩
    · exact ⟨bf_computes 5⟩
    · exact ⟨power_computes⟩
    · exact ⟨sf_computes 4⟩
)
noncomputable def W_computes : PolyComputes W := by
  unfold W
  simpa only [Function.comp_def,List.cons_append,List.nil_append] using
    ((field_computes 1).pair (((const_computes [true]).append (field_computes 2)).pair contBase_computes)).comp BinaryFiniteMachine.continuation_computes
noncomputable def ctx_computes : PolyComputes ctx :=
  list_computes [bf 2,Q,field 5] (by
    intro f hf; refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl
    · exact ⟨bf_computes 2⟩
    · exact ⟨Q_computes⟩
    · exact ⟨field_computes 5⟩
)
noncomputable def crossInput_computes : PolyComputes crossInput :=
  list_computes [base,key,spare,field 5,field 1,field 2,H,G,T,W] (by
    intro f hf; refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact ⟨base_computes⟩
    · exact ⟨key_computes⟩
    · exact ⟨spare_computes⟩
    · exact ⟨field_computes 5⟩
    · exact ⟨field_computes 1⟩
    · exact ⟨field_computes 2⟩
    · exact ⟨H_computes⟩
    · exact ⟨G_computes⟩
    · exact ⟨T_computes⟩
    · exact ⟨W_computes⟩
)
noncomputable def bankInput_computes : PolyComputes bankInput :=
  list_computes [bf 2,mappedFree,qbits] (by
    intro f hf; refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl
    · exact ⟨bf_computes 2⟩
    · exact ⟨mappedFree_computes⟩
    · exact ⟨qbits_computes⟩
)
noncomputable def banks_computes : PolyComputes banks :=
  bankInput_computes.comp BinaryFiniteContext.banks_computes
noncomputable def prefixG_computes : PolyComputes prefixG :=
  mappedPrefix_computes.append (cons_computes G_computes (const_computes []))
noncomputable def finishInput_computes : PolyComputes finishInput :=
  list_computes [mappedFree,sf 4,prefixG,W] (by
    intro f hf; refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl|rfl
    · exact ⟨mappedFree_computes⟩
    · exact ⟨sf_computes 4⟩
    · exact ⟨prefixG_computes⟩
    · exact ⟨W_computes⟩
)
noncomputable def advanceInput_computes : PolyComputes advanceInput :=
  list_computes [field 6,G,W,U] (by
    intro f hf; refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl|rfl
    · exact ⟨field_computes 6⟩
    · exact ⟨G_computes⟩
    · exact ⟨W_computes⟩
    · exact ⟨U_computes⟩
)
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
attribute [local irreducible] BinaryInitialQuery.count BinaryInitialQuery.history BinaryCoupledLoop.run BinaryBisection.run
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

namespace MetricKMedianRecovery.BitMachine.BinaryCanonicalSurplus
open WordOperations WordList BinaryArithmetic RationalLeaves CanonicalCoupledMerge
open BinaryOpeningPayment (field field_computes field_encode)
variable {m : ℕ}
noncomputable def run (v : ℚ) (C : ℕ) : List Bool→List Bool := BinarySurplusPostprocess.run ∘ postInput v C
end MetricKMedianRecovery.BitMachine.BinaryCanonicalSurplus

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
attribute [local irreducible] BinaryInputParser.Metric.matrix BinaryNormalizeInput.P.clients
  BinaryNormalizeInput.P.facilities BinaryInputParser.Metric.budget fallback
end MetricKMedianRecovery.BitMachine.BinaryGlobalOuter

end OAI
end


