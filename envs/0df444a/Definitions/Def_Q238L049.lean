-- Prove2me | Definitions.Def_Q238L049
-- name    : Q238L049
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T11:48:49.991538+00:00
-- url     : https://prove2.me/theorems/eace1c8d-a825-4c74-a52c-6634fd4c0ab5
-- title:
--   Definitions bundle Q238L049 of the split of OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 117 declarations of OpenAI's Lean: 117 definitions. The definitions and types are `OAI.MetricKMedianRecovery.BitMachine.BinaryCandidateSanitize.clip_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCandidateSanitize.keep_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCandidateSanitize.run_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCandidateSanitize.size_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCanonicalSurplus.postInput`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupled.endLeaf_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupled.leafBank_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupled.leafPrefix_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupled.leafResult_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledLoop.next`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledLoop.run`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledLoop.stateRun`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledLoop.step`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.W_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.a_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.active`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.advanceInput_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.c_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.crossInput_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.finishInput_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.leafKey_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.resolveInput`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.resolveInput_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.run`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.sandwiched_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.spare_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCross.directed_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCross.edge_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCross.finalCount_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCross.forward_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCross.leftCount_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCross.leftLength_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCross.leftPaid_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCross.mixedCount_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCross.paid_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCross.rightCount_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCross.rightLength_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCross.rightPaid_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCross.sandwiched_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCross.transition_computes` and 77 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedianRecovery_Algorithms_CandidateSanitize`, `KMedianRecovery_Encoding_LabelLookup`, `KMedianRecovery_Encoding_LengthEncode`, `KMedianRecovery_Encoding_WordExtras`, `KMedianRecovery_Machines_CoupledPrimitives`, `KMedianRecovery_Machines_FiniteMachine`, `KMedianRecovery_Machines_InitialLoop`, `KMedianRecovery_Machines_LengthQuery`, `KMedianRecovery_Machines_LoopMachine`, `KMedianRecovery_Machines_LoopSize`, `KMedianRecovery_Machines_MatchFold`, `KMedianRecovery_Machines_MatchSize`, `KMedianRecovery_Machines_RefineMachine`, `KMedianRecovery_Machines_ResolveMachine`, `KMedianRecovery_Machines_ScanMachine`, `KMedianRecovery_Machines_StartResources`, `KMedianRecovery_Machines_StepMachine`, `KMedianRecovery_Recovery_CrossCount`, `KMedianRecovery_Recovery_CrossEdge`, `KMedianRecovery_Recovery_FirstPresent`, `KMedianRecovery_Recovery_InitialAuto`, `KMedianRecovery_Recovery_InitialProject`, `KMedianRecovery_Recovery_LengthCandidates`, `KMedianRecovery_Recovery_PlanResult`, `KMedianRecovery_Recovery_RefineMath`, `KMedianRecovery_Recovery_RegularChain`, `KMedianRecovery_Strictness_SurplusPostprocess`.
--
--   **Imports.** It imports the published bundle `Def_KMedianRecovery`; the bundles `Q238L041`, `Q238L042`, `Q238L043`, `Q238L044` and `Q238L045` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q238L052` and `Q238L053`; the statements `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledLoop.run_initial_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.run_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteCross.run_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInitialProject.run_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInitial.run_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMatch.run_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMatch.step_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRegularChain.run_pack_s238r` and `OAI.MetricKMedianRecovery.BitMachine.BinaryRegular.run_pack_s238r`; the proofs of `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledLoop.run_initial_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.run_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteCross.run_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInitialProject.run_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInitial.run_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMatch.run_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMatch.step_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRegularChain.run_pack_s238r` and `OAI.MetricKMedianRecovery.BitMachine.BinaryRegular.run_pack_s238r`.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_KMedianRecovery
import Definitions.Def_Q238L041
import Definitions.Def_Q238L042
import Definitions.Def_Q238L043
import Definitions.Def_Q238L044
import Definitions.Def_Q238L045

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_LabelLookup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryLabelLookup
open WordOperations WordList RationalLeaves
noncomputable def history_computes : PolyComputes history := mapWith_computes run_computes
end MetricKMedianRecovery.BitMachine.BinaryLabelLookup

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_FiniteMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryFiniteMachine
open WordOperations WordList RationalLeaves
open BinaryOpeningPayment (field field_computes field_encode)
open BinaryFiniteContext (pack labels)

noncomputable def continuation_computes : PolyComputes continuation := by
  have continuationComputes :=
    ((data_computes.comp BinaryFiniteContext.alphabet_computes).pair history_computes).comp
      BinaryLabelLookup.history_computes
  unfold continuation
  simpa only [Function.comp_def] using continuationComputes
end MetricKMedianRecovery.BitMachine.BinaryFiniteMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_WordExtras
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryJump
open WordOperations WordList RationalLeaves CanonicalMergeRefinement BinaryArithmetic
open BinaryFiniteContext (labels setBits)
open BinaryOpeningPayment (field field_computes field_encode)
noncomputable def copied_computes : PolyComputes copied := by
  have copiedComputes := ((cf_computes 2).pair (jf_computes 4)).comp BinaryLabel.copied_computes
  unfold copied
  simpa only [Function.comp_def] using copiedComputes
noncomputable def source_computes : PolyComputes source :=
  (tagIs_computes 0).cond (cf_computes 3)
    ((jf_computes 1).append (cons_computes ((tagIs_computes 1).cond (jf_computes 4) copied_computes) (jf_computes 2)))
noncomputable def target_computes : PolyComputes target :=
  (tagIs_computes 0).cond ((cf_computes 3).append (cons_computes copied_computes (const_computes [])))
    ((tagIs_computes 1).cond (((jf_computes 1).append (jf_computes 2)).append (jf_computes 3))
      ((jf_computes 1).append (cons_computes (jf_computes 4) (jf_computes 2))))
noncomputable def accepts_computes : PolyComputes (fun x=>[accepts x]) :=
  ((source_computes.pair (cf_computes 3)).comp WordEq.eq_computes).and
    (((target_computes.pair (cf_computes 4)).comp WordEq.eq_computes).and
      ((((jf_computes 4).pair (cf_computes 0)).comp BinaryLabel.contains_computes).and
        labelsCheck_computes))

end MetricKMedianRecovery.BitMachine.BinaryJump

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
noncomputable def run_computes : PolyComputes run := by
  have hp:=NatOps.lt (const_computes (0:ℕ).bits) size_computes
  have hk:=NatOps.le size_computes (field_computes 2)
  unfold run
  simpa only [value_bits,decide_eq_true_eq] using
    hp.cond (hk.cond clip_computes (field_computes 1)) (field_computes 1)
end MetricKMedianRecovery.BitMachine.BinaryCandidateSanitize

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
-- module Solutions.Q238_KM.KMedianRecovery_Machines_CoupledPrimitives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCoupled
open WordOperations WordList BinaryArithmetic RationalLeaves CanonicalCoupledMerge
open BinaryOpeningPayment (field field_computes field_encode)
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
noncomputable def endLeaf_computes (j : ℕ) : PolyComputes (endLeaf j) :=
  (cons_computes (field_computes 3) (cons_computes (field_computes 4) (cons_computes (field_computes j) (const_computes [])))).comp BinaryLabel.makeLeaf_computes
noncomputable def leafBank_computes : PolyComputes leafBank := ((field_computes 0).pair (cons_computes (endLeaf_computes 7) (const_computes []))).comp BinaryFiniteContext.union_computes
noncomputable def leafPrefix_computes : PolyComputes leafPrefix := (field_computes 1).append
  (cons_computes ((field_computes 5).append (cons_computes (endLeaf_computes 7) (const_computes []))) (const_computes []))
noncomputable def leafResult_computes : PolyComputes leafResult :=
  list_computes [leafBank,leafPrefix,(fun x=>pairBits (endLeaf 7 x,endLeaf 6 x)),field 2,field 2,field 8,field 9] (by
    intro f hf; refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact ⟨leafBank_computes⟩
    · exact ⟨leafPrefix_computes⟩
    · exact ⟨(endLeaf_computes 7).pair (endLeaf_computes 6)⟩
    all_goals exact ⟨field_computes _⟩)
end MetricKMedianRecovery.BitMachine.BinaryCoupled

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

namespace MetricKMedianRecovery.BitMachine.BinaryCross
open WordOperations WordList RationalLeaves BinaryArithmetic
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
open BinaryOpeningPayment (field field_computes field_encode)

noncomputable def paid_computes : PolyComputes paid :=
  (opened_computes.pair (cf_computes 0)).comp BinaryFiniteContext.countInter_computes
noncomputable def finalCount_computes : PolyComputes finalCount :=
  (finalOpened_computes.pair (cf_computes 0)).comp BinaryFiniteContext.countInter_computes
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
end MetricKMedianRecovery.BitMachine.BinaryLengthQuery

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

noncomputable def leftPaid_computes : PolyComputes leftPaid := leftData_computes.comp paid_computes
noncomputable def rightPaid_computes : PolyComputes rightPaid := rightData_computes.comp paid_computes
noncomputable def leftLength_computes : PolyComputes leftLength := (leftNode_computes.comp extractPrefix_computes).comp lengthBits_computes
noncomputable def rightLength_computes : PolyComputes rightLength := (rightNode_computes.comp extractPrefix_computes).comp lengthBits_computes
noncomputable def forward_computes : PolyComputes (fun x=>[forward x]) :=
  (NatOps.eq leftPaid_computes rightPaid_computes).boolCond
    (NatOps.lt leftLength_computes rightLength_computes) (NatOps.lt rightPaid_computes leftPaid_computes)
noncomputable def mixedCount_computes : PolyComputes mixedCount :=
  (extractPrefix_computes.pair mixed_computes).comp finalCount_computes
noncomputable def directed_computes : PolyComputes directed :=
  (NatOps.eq leftLength_computes rightLength_computes).cond
    ((NatOps.eq mixedCount_computes (cf_computes 2)).cond (mixed_computes.comp successNode_computes) mixedCommon_computes)
    (discardPrefix_computes.comp (taggedPair_computes 2))
noncomputable def edge_computes : PolyComputes edge := forward_computes.cond directed_computes (flipped_computes.comp directed_computes)
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
noncomputable def G_computes : PolyComputes G := (rf_computes 2).comp extractPrefix_computes
noncomputable def U_computes : PolyComputes U := (rf_computes 2).comp discardPrefix_computes
noncomputable def fallbackInput_computes : PolyComputes fallbackInput := cons_computes (field_computes 7)
  (cons_computes (bf_computes 7) (cons_computes (field_computes 8) (cons_computes (const_computes []) (const_computes []))))
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
noncomputable def copied_computes : PolyComputes copied :=
  ((cf_computes 1).pair item_computes).comp BinaryLabel.copied_computes
noncomputable def advancingInput_computes : PolyComputes advancingInput := list_computes
  [cf 0,sf 0,sf 1,item,copied] (by
    intro f hf; refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl|rfl|rfl
    · exact ⟨cf_computes _⟩
    · exact ⟨sf_computes _⟩
    · exact ⟨sf_computes _⟩
    · exact ⟨item_computes⟩
    · exact ⟨copied_computes⟩)
noncomputable def advanced : List Bool → List Bool := BinaryAdvance.run ∘ advancingInput
noncomputable def advanced_computes : PolyComputes advanced := advancingInput_computes.comp BinaryAdvance.run_computes
attribute [local irreducible] advanced
noncomputable def rest : List Bool → List Bool := field 0 ∘ advanced
noncomputable def suffix_computes : PolyComputes rest := advanced_computes.comp (field_computes 0)
noncomputable def vertices (x : List Bool) : List Bool := sf 2 x++field 1 (advanced x)
noncomputable def vertices_computes : PolyComputes vertices :=
  (sf_computes 2).append (advanced_computes.comp (field_computes 1))
noncomputable def step (x : List Bool) : List Bool := encode [front x,rest x,vertices x]
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

noncomputable def run (x : List Bool) : List Bool := CappedFold.run step (pairBits (capacity.word x,x))
noncomputable def run_computes : PolyComputes run :=
  (capacity.computes.pair id_computes).comp (CappedFold.run_computes step_computes)
end MetricKMedianRecovery.BitMachine.BinaryMatch

namespace MetricKMedianRecovery.BitMachine.BinaryRegular
open WordOperations WordList RationalLeaves CanonicalMergePath PhaseSequence
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
open BinaryOpeningPayment (field field_computes field_encode)

noncomputable def pool_computes : PolyComputes pool := poolInput_computes.comp (mapWith_computes BinaryLabel.copied_computes)
noncomputable def context_computes : PolyComputes context := list_computes [field 0,field 1,pool] (by
  intro f hf; refine Classical.choice ?_
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
  rcases hf with rfl|rfl|rfl
  · exact ⟨field_computes _⟩
  · exact ⟨field_computes _⟩
  · exact ⟨pool_computes⟩)
noncomputable def matchInput_computes : PolyComputes matchInput := Fold.pack_computes (field_computes 2) context_computes state0_computes
noncomputable def matched : List Bool → List Bool := BinaryMatch.run ∘ matchInput
noncomputable def matched_computes : PolyComputes matched := matchInput_computes.comp BinaryMatch.run_computes
noncomputable def prunedInput (x : List Bool) : List Bool := pairBits (field 2 x,field 1 (matched x))
noncomputable def prunedInput_computes : PolyComputes prunedInput := by
  unfold prunedInput
  simpa only [Function.comp_def] using (field_computes 2).pair (matched_computes.comp (field_computes 1))
noncomputable def run (x : List Bool) : List Bool := field 2 (matched x)++BinarySuffix.prune (prunedInput x)
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
noncomputable def spareWord_computes : PolyComputes spareWord := by
  have spareWordComputes := ((cf_computes 0).pair (jf_computes 4)).comp BinaryLabel.copied_computes
  unfold spareWord
  simpa only [Function.comp_def] using spareWordComputes
noncomputable def ctSpare_computes : PolyComputes ctSpare := ct_computes.append (cons_computes spareWord_computes (const_computes []))
noncomputable def grown_computes : PolyComputes grown := by
  have grownComputes :=
    ((ct_computes.pair spareWord_computes).pair (jf_computes 3)).comp BinarySuffix.grow_computes
  unfold grown
  simpa only [Function.comp_def] using grownComputes
noncomputable def removeOut_computes : PolyComputes removeOut :=
  cons_computes ctSpare_computes (grown_computes.append (cons_computes (ct_computes.append (jf_computes 3)) (const_computes [])))
noncomputable def expand_computes : PolyComputes expand :=
  (tagIs_computes 1).cond removeOut_computes (cons_computes (cf_computes 1) (const_computes []))
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
noncomputable def vertices (x : List Bool) : List Bool := cons (field 4 x) (BinaryRegular.run (regularInput x))
noncomputable def vertices_computes : PolyComputes vertices :=
  cons_computes (field_computes 4) (regularInput_computes.comp BinaryRegular.run_computes)
noncomputable def run (x : List Bool) : List Bool := BinaryRefine.run (pairBits (context x,vertices x))
noncomputable def run_computes : PolyComputes run := (context_computes.pair vertices_computes).comp BinaryRefine.run_computes
end MetricKMedianRecovery.BitMachine.BinaryRegularChain

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
noncomputable def leftCount_computes : PolyComputes leftCount := leftData_computes.comp finalCount_computes
noncomputable def rightCount_computes : PolyComputes rightCount := rightData_computes.comp finalCount_computes
noncomputable def sandwiched_computes : PolyComputes (fun x=>[sandwiched x]) :=
  ((NatOps.lt leftCount_computes (cf_computes 2)).and (NatOps.lt (cf_computes 2) rightCount_computes)).or
    ((NatOps.lt rightCount_computes (cf_computes 2)).and (NatOps.lt (cf_computes 2) leftCount_computes))
noncomputable def transition_computes : PolyComputes transition :=
  (NatOps.eq rightCount_computes (cf_computes 2)).cond
    ((const_computes [true]).append (rightNode_computes.comp successNode_computes))
    (sandwiched_computes.cond ((const_computes [true]).append edge_computes) (const_computes []))
end MetricKMedianRecovery.BitMachine.BinaryCross

namespace MetricKMedianRecovery.BitMachine.BinaryNodeScan
open WordOperations WordList RationalLeaves CanonicalMergeRefinement CanonicalMergeCrossing
open BinaryCross (ctxBits nodeBits resultBits)
open BinaryFiniteMachine (historyBits)
open BinaryOpeningPayment (field field_computes field_encode)
attribute [local irreducible] BinaryCross.transition
noncomputable def cutOp_computes : PolyComputes cutOp := by
  unfold cutOp
  simpa only [Function.comp_def,decide_eq_true_eq] using
    (suffix_computes.comp isEmpty_computes).cond (const_computes [])
      (transitionInput_computes.comp BinaryCross.transition_computes)
noncomputable def markers_computes : PolyComputes markers := scanInput_computes.comp (mapWith_computes cutOp_computes)
noncomputable def run_computes : PolyComputes run := (fallback_computes.pair markers_computes).comp FirstPresent.run_computes
end MetricKMedianRecovery.BitMachine.BinaryNodeScan

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
noncomputable def run_computes : PolyComputes run := scanInput_computes.comp BinaryNodeScan.run_computes
end MetricKMedianRecovery.BitMachine.BinaryScan

namespace MetricKMedianRecovery.BitMachine.BinaryFiniteCross
open WordOperations WordList RationalLeaves CanonicalMergePath PhaseSequence
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
open BinaryOpeningPayment (field field_computes field_encode)
attribute [local irreducible] BinaryRegularChain.run BinaryScan.run
noncomputable def scanInput (x : List Bool) : List Bool :=
  encode [field 0 x,field 4 x,nextQ x,crossCtx x,field 9 x,firstNode x,BinaryRegularChain.run (chainInput x)]
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
noncomputable def run : List Bool → List Bool := BinaryScan.run ∘ scanInput
noncomputable def run_computes : PolyComputes run := scanInput_computes.comp BinaryScan.run_computes
end MetricKMedianRecovery.BitMachine.BinaryFiniteCross

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
noncomputable def W_computes : PolyComputes W := by
  unfold W
  simpa only [Function.comp_def,List.cons_append,List.nil_append] using
    ((field_computes 1).pair (((const_computes [true]).append (field_computes 2)).pair contBase_computes)).comp BinaryFiniteMachine.continuation_computes
noncomputable def c_computes : PolyComputes c :=
  (ctx_computes.pair (G_computes.pair W_computes)).comp BinaryCross.finalCount_computes
noncomputable def a_computes : PolyComputes a :=
  (((Q_computes.pair (sf_computes 5)).comp BinaryFiniteMachine.after_computes).pair (bf_computes 2)).comp BinaryFiniteContext.countInter_computes
noncomputable def spare_computes : PolyComputes spare :=
  by
  change PolyComputes (fun x=>(value (key x)+1).bits)
  simpa only [value_bits] using NatOps.add key_computes (const_computes (1:ℕ).bits)
noncomputable def leafKey_computes : PolyComputes leafKey :=
  by
  change PolyComputes (fun x=>(value (key x)+2).bits)
  simpa only [value_bits] using NatOps.add key_computes (const_computes (2:ℕ).bits)
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
noncomputable def resolveInput (x : List Bool) : List Bool := encode [base x,field 1 x,field 2 x,leafKey x,field 3 x,field 5 x,field 4 x,banks x,mappedPrefix x,(BinaryFiniteCross.run ∘ crossInput) x]
noncomputable def resolveInput_computes : PolyComputes resolveInput :=
  list_computes [base,field 1,field 2,leafKey,field 3,field 5,field 4,banks,mappedPrefix,(BinaryFiniteCross.run ∘ crossInput)] (by
    intro f hf; refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact ⟨base_computes⟩
    · exact ⟨field_computes 1⟩
    · exact ⟨field_computes 2⟩
    · exact ⟨leafKey_computes⟩
    · exact ⟨field_computes 3⟩
    · exact ⟨field_computes 5⟩
    · exact ⟨field_computes 4⟩
    · exact ⟨banks_computes⟩
    · exact ⟨mappedPrefix_computes⟩
    · exact ⟨crossInput_computes.comp BinaryFiniteCross.run_computes⟩
)
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
noncomputable def sandwiched_computes : PolyComputes (fun x=>[sandwiched x]) :=
  ((NatOps.lt a_computes (field_computes 5)).and (NatOps.lt (field_computes 5) c_computes)).or
    ((NatOps.lt c_computes (field_computes 5)).and (NatOps.lt (field_computes 5) a_computes))
noncomputable def active (x : List Bool) : List Bool := if decide (value (c x)=value (field 5 x)) then pairBits ([],BinaryCoupled.finish (finishInput x))
  else if sandwiched x then BinaryResolve.run (resolveInput x) else pairBits ([true],BinaryCoupled.advance (advanceInput x))
noncomputable def run (x : List Bool) : List Bool := if nonempty x then active x else pairBits ([],BinaryCoupled.finish (fallbackInput x))
end MetricKMedianRecovery.BitMachine.BinaryCoupledStep

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_LoopMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCoupledLoop
open WordOperations WordList BinaryArithmetic RationalLeaves CanonicalCoupledMerge
open BinaryOpeningPayment (field field_computes field_encode)
open BinaryCoupled (stateBits outcomeBits outputBits)
noncomputable def next (x : List Bool) : List Bool := encode [field 0 x,(field 1 x).tail,true::field 2 x,
  field 3 x,field 4 x,field 5 x,BinaryCoupledStep.run (input x)]
noncomputable def step (x : List Bool) : List Bool :=
  if extractPrefix (field 6 x)=[] then x else if field 1 x=[] then x else next x
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
noncomputable def stateRun : List Bool→List Bool := BoundedIteration.run step ∘ iterationInput
noncomputable def run : List Bool→List Bool := discardPrefix ∘ field 6 ∘ stateRun
attribute [local instance] RationalLeaves.metric
attribute [local irreducible] BinaryCoupledStep.run
end MetricKMedianRecovery.BitMachine.BinaryCoupledLoop

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_StartResources
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryInitialQuery
open WordOperations WordList BinaryArithmetic RationalLeaves CanonicalCoupledMerge
open BinaryOpeningPayment (field field_computes field_encode)
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
attribute [local irreducible] BinaryFiniteMachine.continuation

noncomputable def history_computes : PolyComputes history :=
  ((extractPrefix_computes.comp extractPrefix_computes).pair ((const_computes []).pair atPrice_computes)).comp
    BinaryFiniteMachine.continuation_computes
noncomputable def opened_computes : PolyComputes opened :=
  ((const_computes []).pair history_computes).comp BinaryFiniteMachine.after_computes
noncomputable def count_computes : PolyComputes count := (opened_computes.pair (bf_computes 2)).comp BinaryFiniteContext.countInter_computes
end MetricKMedianRecovery.BitMachine.BinaryInitialQuery

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
noncomputable def loCount_computes : PolyComputes loCount := loInput_computes.comp BinaryInitialQuery.count_computes

noncomputable def loHistory_computes : PolyComputes loHistory := loInput_computes.comp BinaryInitialQuery.history_computes

noncomputable def loFinish_computes : PolyComputes loFinish := list_computes [(fun _=>[]),field 5,loHistory] (by
  intro f hf; refine Classical.choice ?_
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
  rcases hf with rfl|rfl|rfl
  · exact ⟨const_computes []⟩
  · exact ⟨field_computes 5⟩
  · exact ⟨loHistory_computes⟩)

noncomputable def normal (x : List Bool) : List Bool := if value (lowerCount x)=value (field 4 x) then lowerFinish x else
  if value (upperCount x)=value (field 4 x) then upperFinish x else BinaryCoupledLoop.run (loopInput x)

noncomputable def run (x : List Bool) : List Bool := if value (loCount x)≤value (field 4 x) then pairBits ([],loFinish x) else pairBits ([true],normal x)

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
noncomputable def run (v : ℚ) (C : ℕ) : List Bool→List Bool := BinaryInitial.run ∘ initialInput v C
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
noncomputable def run (v : ℚ) (C : ℕ) : List Bool→List Bool := extract ∘ BinaryInitialAuto.run v C
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

namespace MetricKMedianRecovery.BitMachine.BinaryCanonicalSurplus
open WordOperations WordList BinaryArithmetic RationalLeaves CanonicalCoupledMerge
open BinaryOpeningPayment (field field_computes field_encode)
variable {m : ℕ}
noncomputable def postInput (v : ℚ) (C : ℕ) (x : List Bool) : List Bool :=
  encode [field 0 (extractPrefix x),field 1 (extractPrefix x),field 2 (extractPrefix x),
    BinaryInitialProject.run v C (extractPrefix x),discardPrefix x]
end MetricKMedianRecovery.BitMachine.BinaryCanonicalSurplus

end OAI
end


