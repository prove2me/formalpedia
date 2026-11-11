-- Prove2me | Definitions.Def_Q238K044
-- name    : Q238K044
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T23:44:04.810215+00:00
-- url     : https://prove2.me/theorems/b2094d7f-11f1-40dd-ad68-94cd53bb40da
-- title:
--   Definitions bundle Q238K044 of the split of OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 82 declarations of OpenAI's Lean: 82 definitions. The definitions and types are `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.bf_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.key_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.leafKey_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.qbits_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.spare_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCross.cf_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCross.flipped_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCross.leftData_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCross.leftNode_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCross.mixedCommon_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCross.mixed_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCross.opened_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCross.rightData_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCross.rightNode_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCross.successNode_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCross.taggedPair_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.bankFirst_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.banks_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.copiedSet_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.pool_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.threeQOne_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.threeQ_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteCross.chainInput_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteCross.crossCtx_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteCross.firstNode_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteCross.nextQ_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryJump.addOp_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryJump.adds_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryJump.cf_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryJump.copied_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryJump.ctSpare_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryJump.ct_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryJump.edgeData_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryJump.edgeG_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryJump.expand_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryJump.grown_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryJump.jf_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryJump.labelsCheck_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryJump.removeOut_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryJump.replaceOp_computes` and 42 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedianRecovery_Encoding_WordExtras`, `KMedianRecovery_Machines_FiniteMachine`, `KMedianRecovery_Machines_MatchFold`, `KMedianRecovery_Machines_MatchSize`, `KMedianRecovery_Machines_RefineMachine`, `KMedianRecovery_Machines_ScanMachine`, `KMedianRecovery_Machines_StepMachine`, `KMedianRecovery_Machines_SuffixMachine`, `KMedianRecovery_Recovery_CrossCount`, `KMedianRecovery_Recovery_CrossEdge`, `KMedianRecovery_Recovery_FirstPresent`, `KMedianRecovery_Recovery_PlanResult`, `KMedianRecovery_Recovery_RefineMath`, `KMedianRecovery_Recovery_RegularChain`.
--
--   **Imports.** It imports the published bundle `Def_KMedianRefinedRecovery`; the bundle `Q238K039` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q238K048` and `Q238K049`.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_KMedianRefinedRecovery
import Definitions.Def_Q238K039

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_FiniteMachine
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryLabel
open WordOperations BinaryArithmetic RationalLeaves
noncomputable def copied_computes : PolyComputes copied := by
  have hi : PolyComputes (fun x=>(value (extractPrefix x)+1).bits) := by
    simpa only [value_bits] using NatOps.add extractPrefix_computes (const_computes (1:ℕ).bits)
  have ht:=hi.pair ((discardPrefix_computes.comp parentWords_computes).pair (const_computes (BinaryRational.encode 0)))
  have hh := (NatOps.zero (discardPrefix_computes.comp levelWords_computes)).cond ht discardPrefix_computes
  unfold copied
  simpa only [Function.comp_def,decide_eq_true_eq] using hh
end MetricKMedianRecovery.BitMachine.BinaryLabel

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

namespace MetricKMedianRecovery.BitMachine.BinaryLabel
open WordOperations WordList RationalLeaves
noncomputable def missing_computes : PolyComputes (fun x=>[missing x]) :=
  ((discardPrefix_computes.pair extractPrefix_computes).comp contains_computes).not
noncomputable def allIn_computes : PolyComputes (fun x=>[allIn x]) :=
  (Find.run_computes missing_computes).comp isEmpty_computes
end MetricKMedianRecovery.BitMachine.BinaryLabel
namespace MetricKMedianRecovery.BitMachine.BinaryJump
open WordOperations WordList RationalLeaves CanonicalMergeRefinement BinaryArithmetic
open BinaryFiniteContext (labels setBits)
open BinaryOpeningPayment (field field_computes )
noncomputable def cf_computes (n : ℕ) : PolyComputes (cf n) := extractPrefix_computes.comp (field_computes n)
noncomputable def jf_computes (n : ℕ) : PolyComputes (jf n) := discardPrefix_computes.comp (field_computes n)
noncomputable def tagIs_computes (n : ℕ) : PolyComputes (fun x=>[tagIs n x]) := by
  simpa only [tagIs,value_bits] using NatOps.eq (jf_computes 0) (const_computes n.bits)
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
noncomputable def labelsCheck_computes : PolyComputes (fun x=>[labelsCheck x]) := by
  have h:=(tagIs_computes 1).cond (((cf_computes 0).pair (jf_computes 3)).comp BinaryLabel.allIn_computes)
    (const_computes [true])
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  unfold labelsCheck
  split_ifs <;> rfl

end MetricKMedianRecovery.BitMachine.BinaryJump

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
open BinaryOpeningPayment (field field_computes )

noncomputable def cf_computes (n : ℕ) : PolyComputes (cf n) := extractPrefix_computes.comp (field_computes n)
noncomputable def sf_computes (n : ℕ) : PolyComputes (sf n) :=
  (discardPrefix_computes.comp discardPrefix_computes).comp (field_computes n)
noncomputable def item_computes : PolyComputes item := discardPrefix_computes.comp extractPrefix_computes
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
noncomputable def prefix_computes : PolyComputes front :=
  (sf_computes 0).append (cons_computes item_computes (const_computes []))
end MetricKMedianRecovery.BitMachine.BinaryMatch

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_SuffixMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySuffix
open WordOperations WordList RationalLeaves
open BinaryFiniteContext (labels)
open BinaryFiniteMachine (historyBits)
open BinaryOpeningPayment (field field_computes )
noncomputable def pruneOp_computes : PolyComputes pruneOp := extractPrefix_computes.append (discardPrefix_computes.comp (field_computes 2))
noncomputable def pruneInput_computes : PolyComputes pruneInput := extractPrefix_computes.pair (discardPrefix_computes.comp Slices.run_computes)
noncomputable def prune_computes : PolyComputes prune := pruneInput_computes.comp (mapWith_computes pruneOp_computes)
noncomputable def growOp_computes : PolyComputes growOp :=
  ((extractPrefix_computes.comp extractPrefix_computes).append
    (cons_computes (discardPrefix_computes.comp (field_computes 1)) (discardPrefix_computes.comp (field_computes 2)))).append
    (cons_computes (extractPrefix_computes.comp discardPrefix_computes) (const_computes []))
noncomputable def grow_computes : PolyComputes grow :=
  (pruneInput_computes.comp (mapWith_computes growOp_computes)).comp WordList.reverse_computes
end MetricKMedianRecovery.BitMachine.BinarySuffix

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
open BinaryOpeningPayment (field field_computes )

noncomputable def cf_computes (n : ℕ) : PolyComputes (cf n) := extractPrefix_computes.comp (field_computes n)
noncomputable def opened_computes : PolyComputes opened :=
  ((cf_computes 1).pair (discardPrefix_computes.comp extractPrefix_computes)).comp BinaryFiniteContext.union_computes
end MetricKMedianRecovery.BitMachine.BinaryCross

namespace MetricKMedianRecovery.BitMachine.BinaryJump
open WordOperations WordList RationalLeaves CanonicalMergeRefinement BinaryArithmetic
open BinaryFiniteContext (labels setBits)
open BinaryOpeningPayment (field field_computes )
attribute [local irreducible] removedTail
noncomputable def addOp_computes : PolyComputes addOp := list_computes [fun _=>(0:ℕ).bits,fun _=>[],fun _=>[],fun _=>[],discardPrefix] (by
  intro f hf; refine Classical.choice ?_
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
  rcases hf with rfl|rfl|rfl|rfl|rfl
  · exact ⟨const_computes _⟩
  · exact ⟨const_computes _⟩
  · exact ⟨const_computes _⟩
  · exact ⟨const_computes _⟩
  · exact ⟨discardPrefix_computes⟩)
noncomputable def replaceOp_computes : PolyComputes replaceOp := list_computes [fun _=>(2:ℕ).bits,jf 0,jf 2,fun _=>[],jf 1] (by
  intro f hf; refine Classical.choice ?_
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
  rcases hf with rfl|rfl|rfl|rfl|rfl
  · exact ⟨const_computes _⟩
  · exact ⟨jf_computes _⟩
  · exact ⟨jf_computes _⟩
  · exact ⟨const_computes _⟩
  · exact ⟨jf_computes _⟩)
noncomputable def adds_computes : PolyComputes adds := by
  have addsComputes := (id_computes.pair (field_computes 1)).comp (mapWith_computes addOp_computes)
  unfold adds
  simpa only [Function.comp_def, id_eq] using addsComputes
noncomputable def replaces_computes : PolyComputes replaces := by
  have replacesComputes :=
    (id_computes.pair ((field_computes 4).comp Slices.run_computes)).comp (mapWith_computes replaceOp_computes)
  unfold replaces
  simpa only [Function.comp_def, id_eq] using replacesComputes
end MetricKMedianRecovery.BitMachine.BinaryJump

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
open BinaryOpeningPayment (field field_computes )
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)

noncomputable def sf_computes (n : ℕ) : PolyComputes (sf n) := (field_computes 0).comp (field_computes n)
end MetricKMedianRecovery.BitMachine.BinaryPlanResult

namespace MetricKMedianRecovery.BitMachine.BinaryFiniteContext
open WordOperations WordList BinaryArithmetic RationalLeaves
open BinaryOpeningPayment (field field_computes )
noncomputable def copiedSet_computes : PolyComputes copiedSet := (mapWith_computes BinaryLabel.copied_computes).comp BinaryLabel.sort_computes
noncomputable def pool_computes : PolyComputes pool :=
  ((field_computes 1).pair (((field_computes 2).pair (field_computes 0)).comp copiedSet_computes)).comp union_computes
noncomputable def threeQ_computes : PolyComputes threeQ := by
  change PolyComputes (fun x=>(3*value (field 2 x)).bits)
  simpa only [value_bits] using NatOps.mul (const_computes (3:ℕ).bits) (field_computes 2)
noncomputable def threeQOne_computes : PolyComputes threeQOne := by
  change PolyComputes (fun x=>(value (threeQ x)+1).bits)
  simpa only [value_bits] using NatOps.add threeQ_computes (const_computes (1:ℕ).bits)
noncomputable def bankFirst_computes : PolyComputes bankFirst :=
  (cons_computes (field_computes 0) (cons_computes (field_computes 1) (cons_computes threeQ_computes (const_computes [])))).comp pool_computes
noncomputable def banks_computes : PolyComputes banks :=
  (cons_computes (field_computes 0) (cons_computes bankFirst_computes (cons_computes threeQOne_computes (const_computes [])))).comp pool_computes
end MetricKMedianRecovery.BitMachine.BinaryFiniteContext

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_MatchSize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRegular
open WordOperations WordList RationalLeaves CanonicalMergePath PhaseSequence
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
open BinaryOpeningPayment (field field_computes )

noncomputable def poolInput_computes : PolyComputes poolInput :=
  (field_computes 1).pair ((field_computes 0).comp (field_computes 2))
noncomputable def pool_computes : PolyComputes pool := poolInput_computes.comp (mapWith_computes BinaryLabel.copied_computes)
noncomputable def context_computes : PolyComputes context := list_computes [field 0,field 1,pool] (by
  intro f hf; refine Classical.choice ?_
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
  rcases hf with rfl|rfl|rfl
  · exact ⟨field_computes _⟩
  · exact ⟨field_computes _⟩
  · exact ⟨pool_computes⟩)
noncomputable def state0_computes : PolyComputes state0 := list_computes [fun _=>[],field 3,fun _=>[]] (by
  intro f hf; refine Classical.choice ?_
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
  rcases hf with rfl|rfl|rfl
  · exact ⟨const_computes []⟩
  · exact ⟨field_computes _⟩
  · exact ⟨const_computes []⟩)
noncomputable def matchInput_computes : PolyComputes matchInput := Fold.pack_computes (field_computes 2) context_computes state0_computes
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
open BinaryOpeningPayment (field field_computes )
noncomputable def spareWord_computes : PolyComputes spareWord := by
  have spareWordComputes := ((cf_computes 0).pair (jf_computes 4)).comp BinaryLabel.copied_computes
  unfold spareWord
  simpa only [Function.comp_def] using spareWordComputes
noncomputable def ct_computes : PolyComputes ct := (jf_computes 1).append (jf_computes 2)
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
noncomputable def edgeG_computes : PolyComputes edgeG := (field_computes 0).comp (field_computes 4)
noncomputable def edgeData_computes : PolyComputes edgeData := list_computes [field 1,edgeG] (by
  intro f hf; refine Classical.choice ?_
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
  rcases hf with rfl|rfl
  · exact ⟨field_computes _⟩
  · exact ⟨edgeG_computes⟩)
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
open BinaryOpeningPayment (field field_computes )
noncomputable def cutTail_computes : PolyComputes cutTail := discardPrefix_computes.comp (field_computes 2)
noncomputable def source_computes : PolyComputes source := discardPrefix_computes.comp (field_computes 1)
noncomputable def target_computes : PolyComputes target := cutTail_computes.comp WordList.head_computes
noncomputable def cf_computes (n : ℕ) : PolyComputes (cf n) := extractPrefix_computes.comp (field_computes n)
noncomputable def jumpContext_computes : PolyComputes jumpContext := list_computes [cf 0,cf 1,cf 2,source,target] (by
  intro f hf; refine Classical.choice ?_
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
  rcases hf with rfl|rfl|rfl|rfl|rfl
  · exact ⟨cf_computes _⟩
  · exact ⟨cf_computes _⟩
  · exact ⟨cf_computes _⟩
  · exact ⟨source_computes⟩
  · exact ⟨target_computes⟩)
noncomputable def edgeInput_computes : PolyComputes edgeInput := list_computes [jumpContext,cf 3] (by
  intro f hf; refine Classical.choice ?_
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
  rcases hf with rfl|rfl
  · exact ⟨jumpContext_computes⟩
  · exact ⟨cf_computes _⟩)
noncomputable def runInput_computes : PolyComputes runInput := extractPrefix_computes.pair (discardPrefix_computes.comp Slices.run_computes)
end MetricKMedianRecovery.BitMachine.BinaryRefine

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

namespace MetricKMedianRecovery.BitMachine
noncomputable def PolyComputes.boolCond {p f g : List Bool → Bool}
    (hp : PolyComputes (fun x=>[p x])) (hf : PolyComputes (fun x=>[f x]))
    (hg : PolyComputes (fun x=>[g x])) : PolyComputes (fun x=>[if p x then f x else g x]) := by
  convert hp.cond hf hg using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  split_ifs <;> rfl
end MetricKMedianRecovery.BitMachine
namespace MetricKMedianRecovery.BitMachine.BinaryCross
open WordOperations WordList RationalLeaves BinaryArithmetic
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
open BinaryOpeningPayment (field field_computes )
attribute [local irreducible] paid finalCount

noncomputable def leftNode_computes : PolyComputes leftNode := discardPrefix_computes.comp extractPrefix_computes
noncomputable def rightNode_computes : PolyComputes rightNode := discardPrefix_computes.comp discardPrefix_computes
noncomputable def leftData_computes : PolyComputes leftData := extractPrefix_computes.pair leftNode_computes
noncomputable def rightData_computes : PolyComputes rightData := extractPrefix_computes.pair rightNode_computes
noncomputable def mixed_computes : PolyComputes mixed :=
  (rightNode_computes.comp extractPrefix_computes).pair (leftNode_computes.comp discardPrefix_computes)
noncomputable def successNode_computes : PolyComputes successNode :=
  list_computes [fun _=>(0:ℕ).bits,id,fun _=>[]] (by
    intro f hf; refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl
    · exact ⟨const_computes _⟩
    · exact ⟨id_computes⟩
    · exact ⟨const_computes _⟩)
noncomputable def taggedPair_computes (tag : ℕ) : PolyComputes (taggedPair tag) :=
  list_computes [fun _=>tag.bits,extractPrefix,discardPrefix] (by
    intro f hf; refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl
    · exact ⟨const_computes _⟩
    · exact ⟨extractPrefix_computes⟩
    · exact ⟨discardPrefix_computes⟩)
noncomputable def mixedCommon_computes : PolyComputes mixedCommon :=
  (mixed_computes.pair (rightNode_computes.comp discardPrefix_computes)).comp (taggedPair_computes 1)
noncomputable def flipped_computes : PolyComputes flipped := extractPrefix_computes.pair (rightNode_computes.pair leftNode_computes)
end MetricKMedianRecovery.BitMachine.BinaryCross

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
open BinaryOpeningPayment (field field_computes )
attribute [local irreducible] BinaryRefine.run
noncomputable def regularInput_computes : PolyComputes regularInput := list_computes [field 0,field 1,field 5,field 4] (by
  intro f hf; refine Classical.choice ?_
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
  rcases hf with rfl|rfl|rfl|rfl <;> exact ⟨field_computes _⟩)
noncomputable def context_computes : PolyComputes context :=
  list_computes [field 2 ∘ field 0,field 3,field 1,field 2] (by
    intro f hf; refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl|rfl
    · exact ⟨(field_computes 0).comp (field_computes 2)⟩
    · exact ⟨field_computes _⟩
    · exact ⟨field_computes _⟩
    · exact ⟨field_computes _⟩)
end MetricKMedianRecovery.BitMachine.BinaryRegularChain

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_FirstPresent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryNodeScan
open WordOperations WordList RationalLeaves CanonicalMergeRefinement CanonicalMergeCrossing
open BinaryCross (ctxBits nodeBits resultBits)
open BinaryFiniteMachine (historyBits)
open BinaryOpeningPayment (field field_computes )
attribute [local irreducible] BinaryCross.transition
noncomputable def suffix_computes : PolyComputes suffix := discardPrefix_computes.comp (field_computes 2)
noncomputable def current_computes : PolyComputes current := discardPrefix_computes.comp (field_computes 1)
noncomputable def transitionInput_computes : PolyComputes transitionInput :=
  extractPrefix_computes.pair (current_computes.pair (suffix_computes.comp WordList.head_computes))
noncomputable def scanInput_computes : PolyComputes scanInput :=
  (field_computes 0).pair ((field_computes 2).comp Slices.run_computes)
noncomputable def lastNode_computes : PolyComputes lastNode :=
  ((field_computes 2).comp WordList.reverse_computes).comp WordList.head_computes
noncomputable def fallback_computes : PolyComputes fallback := list_computes [fun _=>(1:ℕ).bits,lastNode,field 1] (by
  intro f hf; refine Classical.choice ?_
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
  rcases hf with rfl|rfl|rfl
  · exact ⟨const_computes _⟩
  · exact ⟨lastNode_computes⟩
  · exact ⟨field_computes _⟩)
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
open BinaryOpeningPayment (field field_computes )
attribute [local irreducible] BinaryNodeScan.run
noncomputable def cf_computes (n : ℕ) : PolyComputes (cf n) := extractPrefix_computes.comp (field_computes n)
end MetricKMedianRecovery.BitMachine.BinaryScan

namespace MetricKMedianRecovery.BitMachine.BinaryFiniteCross
open WordOperations WordList RationalLeaves CanonicalMergePath PhaseSequence
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
open BinaryOpeningPayment (field field_computes )
noncomputable def chainInput_computes : PolyComputes chainInput :=
  list_computes [field 0,field 1,field 2,field 2 ∘ field 0,field 6,field 7] (by
    intro f hf; refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl|rfl|rfl|rfl
    · exact ⟨field_computes _⟩
    · exact ⟨field_computes _⟩
    · exact ⟨field_computes _⟩
    · exact ⟨(field_computes 0).comp (field_computes 2)⟩
    · exact ⟨field_computes _⟩
    · exact ⟨field_computes _⟩)
noncomputable def crossCtx_computes : PolyComputes crossCtx :=
  list_computes [field 2 ∘ field 0,field 3 ∘ field 0,field 3] (by
    intro f hf; refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl
    · exact ⟨(field_computes 0).comp (field_computes 2)⟩
    · exact ⟨(field_computes 0).comp (field_computes 3)⟩
    · exact ⟨field_computes _⟩)
noncomputable def nextQ_computes : PolyComputes nextQ := (const_computes [true]).append (field_computes 5)
noncomputable def firstNode_computes : PolyComputes firstNode := (field_computes 6).pair (field_computes 8)
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
open BinaryOpeningPayment (field field_computes )
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
open BinaryCoupled (stateBits outcomeBits)
noncomputable def bf_computes (i : ℕ) : PolyComputes (bf i) := (field_computes 0).comp (field_computes i)
noncomputable def qbits_computes : PolyComputes qbits :=
  by
  change PolyComputes (fun x=>(field 2 x).length.bits)
  simpa only [Function.comp_def,UnaryResources.lengthBits_eq] using (field_computes 2).comp UnaryResources.lengthBits_computes
noncomputable def key_computes : PolyComputes key :=
  by
  change PolyComputes (fun x=>(3*value (qbits x)).bits)
  simpa only [value_bits] using NatOps.mul (const_computes (3:ℕ).bits) qbits_computes
noncomputable def spare_computes : PolyComputes spare :=
  by
  change PolyComputes (fun x=>(value (key x)+1).bits)
  simpa only [value_bits] using NatOps.add key_computes (const_computes (1:ℕ).bits)
noncomputable def leafKey_computes : PolyComputes leafKey :=
  by
  change PolyComputes (fun x=>(value (key x)+2).bits)
  simpa only [value_bits] using NatOps.add key_computes (const_computes (2:ℕ).bits)
end MetricKMedianRecovery.BitMachine.BinaryCoupledStep

end OAI
end


