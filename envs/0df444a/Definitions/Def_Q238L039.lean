-- Prove2me | Definitions.Def_Q238L039
-- name    : Q238L039
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T11:39:57.685899+00:00
-- url     : https://prove2.me/theorems/1da4016c-b0a8-4623-9147-9b908e03ca71
-- title:
--   Definitions bundle Q238L039 of the split of OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 92 declarations of OpenAI's Lean: 92 definitions. The definitions and types are `OAI.MetricKMedianRecovery.BitMachine.BinaryActions.add_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryActions.block_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryActions.delete_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryActions.entry_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryActions.menus_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryActions.run_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryAdvance.deleted`, `OAI.MetricKMedianRecovery.BitMachine.BinaryAdvance.deletionInput_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDelete.added`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDelete.cf_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDelete.extended_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDelete.extras`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDelete.openSet_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDelete.rest_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDelete.retained_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDelete.run`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDelete.sf_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDelete.step`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDelete.vertex`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDelete.vertices`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.alphabet_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.matrix_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.replaceOpen_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.run_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.selected_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.union_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteInsert.run_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteMachine.complete`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteMachine.completed`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteMachine.completedTrace`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteMachine.completed_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteMachine.completed_trace_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteMachine.finished`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteMachine.finished_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteMachine.initial_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryHistoryRun.chunk`, `OAI.MetricKMedianRecovery.BitMachine.BinaryHistoryRun.chunk_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryLabel.contains_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryLabel.eq_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryLabel.lt_computes` and 52 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedianRecovery_Encoding_HistoryBits`, `KMedianRecovery_Encoding_InstructionBits`, `KMedianRecovery_Encoding_LabelLookup`, `KMedianRecovery_Encoding_LabelMember`, `KMedianRecovery_Encoding_LabelOrder`, `KMedianRecovery_Encoding_NatWords`, `KMedianRecovery_Encoding_StateBits`, `KMedianRecovery_Machines_ActionMachine`, `KMedianRecovery_Machines_DeleteFold`, `KMedianRecovery_Machines_DeleteSize`, `KMedianRecovery_Machines_FiniteMachine`, `KMedianRecovery_Recovery_Answer`, `KMedianRecovery_Recovery_Basic2`, `KMedianRecovery_Recovery_DecisionOps`, `KMedianRecovery_Recovery_FilterItem`, `KMedianRecovery_Recovery_FiniteContext`, `KMedianRecovery_Recovery_IfNat`, `KMedianRecovery_Recovery_Pack11`, `KMedianRecovery_Recovery_RowInput`, `KMedianRecovery_Recovery_SortMath`, `KMedianRecovery_Strictness_BidPoly`.
--
--   **Imports.** It imports the published bundle `Def_KMedianRecovery`; the bundles `Q238L036` and `Q238L037` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q238L041`, `Q238L042`, `Q238L043`, `Q238L044`, `Q238L045`, `Q238L046` and `Q238L047`; the statements `OAI.MetricKMedianRecovery.BitMachine.BinaryDelete.step_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteMachine.completed_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseFinish.finish_length_s238r` and `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseTrace.iterate_length_s238r`; the proofs of `OAI.MetricKMedianRecovery.BitMachine.BinaryDelete.step_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteMachine.completed_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseFinish.finish_length_s238r` and `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseTrace.iterate_length_s238r`.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_KMedianRecovery
import Definitions.Def_Q238L036
import Definitions.Def_Q238L037

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_NatWords
attribute [-instance] _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace RatOps
noncomputable def natCeil {f : List Bool → ℚ} (hf : PolyComputes (fun x=>BinaryRational.encode (f x))) :
    PolyComputes (fun x=>(⌈f x⌉₊).bits) := by
  have hh := (hf.comp BinaryRational.ceilWords_computes).comp Signed.natWords_computes
  simpa only [Function.comp_def,BinaryRational.ceilWords_encode,Signed.natWords_encode,Int.ceil_toNat] using hh
end RatOps
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Basic2
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace BinaryOpeningConstant
open WordList RationalLinearFeasibility RationalOpenability

noncomputable def constant_computes : PolyComputes (fun x=>BinaryRational.encode (constant x)) := by
  have hz := BinaryOpeningPayment.paramZ_computes
  have hv := BinaryOpeningPayment.paramV_computes
  have h0 := RatOps.const 0
  have hn : PolyComputes (fun x=>BinaryRational.encode (if near x then 0 else -BinaryOpeningPayment.paramZ x)) := by
    have hh := near_computes.cond h0 (RatOps.neg hz)
    simpa only [decide_eq_true_eq,apply_ite] using hh
  exact chooseTag 0 (chooseActive 1 hz h0)
    (chooseTag 1 (chooseActive 1 (RatOps.neg (RatOps.mul (RatOps.add (RatOps.const 1) (RatOps.mul hv hv)) hz)) h0)
    (chooseTag 2 (chooseActive 1 (RatOps.neg (RatOps.mul BinaryOpeningPayment.scale_computes (distance_computes 2 1))) h0)
    (chooseTag 3 (chooseActive 1 hn h0)
    (chooseTag 4 (RatOps.ofWords (extractPrefix_computes.comp BinaryOpeningPayment.run_computes))
    (chooseTag 6 (chooseActive 3
      (chooseActive 1 (RatOps.neg (distance_computes 2 1))
        (RatOps.neg (RatOps.add (RatOps.mul (RatOps.const 2) (distance_computes 2 1)) (distance_computes 2 3)))) h0)
    (chooseTag 7 (chooseActive 1 (RatOps.neg (RatOps.ofWords (BinaryOpeningPayment.itemField_computes 4))) h0) h0))))))

end BinaryOpeningConstant
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_IfNat
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace BinaryOpeningCoefficient
open WordList RationalLinearFeasibility RationalOpenability

noncomputable def chooseActive {f g : List Bool → ℚ} (k : ℕ)
    (hf : PolyComputes (fun x=>BinaryRational.encode (f x)))
    (hg : PolyComputes (fun x=>BinaryRational.encode (g x))) :
    PolyComputes (fun x=>BinaryRational.encode (if BinaryOpeningConstant.active k (extractPrefix x) then f x else g x)) := by
  have hh := (extractPrefix_computes.comp (BinaryOpeningConstant.active_computes k)).cond hf hg
  simpa only [Function.comp_def,apply_ite] using hh
noncomputable def chooseNear {f g : List Bool → ℚ}
    (hf : PolyComputes (fun x=>BinaryRational.encode (f x)))
    (hg : PolyComputes (fun x=>BinaryRational.encode (g x))) :
    PolyComputes (fun x=>BinaryRational.encode (if BinaryOpeningConstant.near (extractPrefix x) then f x else g x)) := by
  have hh := (extractPrefix_computes.comp BinaryOpeningConstant.near_computes).cond hf hg
  simpa only [Function.comp_def,decide_eq_true_eq,apply_ite] using hh

noncomputable def paymentNear_computes : PolyComputes (fun x=>[decide (paymentNear x)]) := by
  have distanceComputes : PolyComputes
      (fun input=>BinaryRational.encode (BinaryOpeningPayment.distance (paymentQuery input))) := by
    simpa only [Function.comp_def] using
      (PolyComputes.comp (f:=paymentQuery)
        (g:=fun input=>BinaryRational.encode (BinaryOpeningPayment.distance input))
        paymentQuery_computes BinaryOpeningPayment.distance_computes)
  have paramVComputes : PolyComputes
      (fun input=>BinaryRational.encode (BinaryOpeningPayment.paramV (paymentQuery input))) := by
    simpa only [Function.comp_def] using
      (PolyComputes.comp (f:=paymentQuery)
        (g:=fun input=>BinaryRational.encode (BinaryOpeningPayment.paramV input))
        paymentQuery_computes BinaryOpeningPayment.paramV_computes)
  have paramZComputes : PolyComputes
      (fun input=>BinaryRational.encode (BinaryOpeningPayment.paramZ (paymentQuery input))) := by
    simpa only [Function.comp_def] using
      (PolyComputes.comp (f:=paymentQuery)
        (g:=fun input=>BinaryRational.encode (BinaryOpeningPayment.paramZ input))
        paymentQuery_computes BinaryOpeningPayment.paramZ_computes)
  unfold paymentNear
  exact RatOps.le distanceComputes (RatOps.mul paramVComputes paramZComputes)
noncomputable def payment_computes : PolyComputes (fun x=>BinaryRational.encode (payment x)) := by
  have hn : PolyComputes (fun x=>BinaryRational.encode (if paymentNear x then (1:ℚ) else 0)) := by
    have hh := paymentNear_computes.cond (RatOps.const 1) (RatOps.const 0)
    simpa only [decide_eq_true_eq,apply_ite] using hh
  have ha := (paymentQuery_computes.comp BinaryOpeningPayment.active_computes).cond hn (RatOps.const 0)
  have ha' : PolyComputes (fun x=>BinaryRational.encode (if BinaryOpeningPayment.active (paymentQuery x) then
      if paymentNear x then (1:ℚ) else 0 else 0)) := by
    simpa only [Function.comp_def,apply_ite] using ha
  exact chooseColTag 0 ha' (RatOps.const 0)

noncomputable def coefficient_computes : PolyComputes (fun x=>BinaryRational.encode (coefficient x)) :=
  chooseTag 0 (chooseActive 1 (RatOps.neg (bid_computes 1)) (RatOps.const 0))
  (chooseTag 1 (chooseActive 1 (bid_computes 1) (RatOps.const 0))
  (chooseTag 2 (chooseActive 1 (bid_computes 1) (RatOps.const 0))
  (chooseTag 3 (chooseActive 1 (chooseNear (RatOps.const 0) (bid_computes 1)) (RatOps.const 0))
  (chooseTag 4 (RatOps.neg payment_computes)
  (chooseTag 5 (chooseActive 3 (RatOps.neg slack_computes) (RatOps.const 0))
  (chooseTag 6 (chooseActive 3 (RatOps.sub (chooseActive 1 (bid_computes 1) (bid_computes 3)) slack_computes) (RatOps.const 0))
  (chooseTag 7 (chooseActive 1 dual_computes (RatOps.const 0)) (RatOps.const 0))))))))

end BinaryOpeningCoefficient
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_RowInput
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRawOpening
open WordOperations BinaryArithmetic WordList RationalLinearFeasibility RationalOpenability EffectiveOpenability
open BinaryOpeningPayment BinaryOpeningEnumeration
noncomputable def rowInput_computes : PolyComputes rowInput := by
  have computation := id_computes.pair (extractPrefix_computes.comp columns_computes)
  exact computation
noncomputable def rowCoefficients_computes : PolyComputes rowCoefficients := by
  have computation := rowInput_computes.comp (mapWith_computes BinaryOpeningCoefficient.coefficient_computes)
  unfold rowCoefficients
  simpa only [Function.comp_def] using computation
noncomputable def rowWord_computes : PolyComputes rowWord :=
  rowCoefficients_computes.pair (RatOps.neg BinaryOpeningConstant.constant_computes)
noncomputable def rows_computes : PolyComputes rows := by
  have computation := (id_computes.pair kinds_computes).comp (mapWith_computes rowWord_computes)
  unfold rows
  simpa only [Function.comp_def, id_eq] using computation
noncomputable def prepared_computes : PolyComputes prepared :=
  (columns_computes.comp Count.run_computes).pair
    ((kinds_computes.comp Count.run_computes).pair ((RatOps.natCeil bound_computes).pair rows_computes))
noncomputable def run_computes : PolyComputes run := prepared_computes.comp BinaryExactSolve.run_computes
end MetricKMedianRecovery.BitMachine.BinaryRawOpening

namespace MetricKMedianRecovery.BitMachine.BinaryPhaseFirst
open WordOperations BinaryArithmetic WordList EffectiveOpenability RationalOpenability
open BinaryOpeningPayment

noncomputable def answer_computes : PolyComputes answer := query_computes.comp BinaryRawOpening.run_computes
noncomputable def eligible_computes : PolyComputes (fun x=>[eligible x]) := by
  have ha := (answer_computes.comp isEmpty_computes).cond (const_computes [false]) (const_computes [true])
  have h := ((discardPrefix_computes.pair (itemField_computes 8)).comp contains_computes).cond
    (((discardPrefix_computes.pair (itemField_computes 1)).comp contains_computes).cond
      (const_computes [false]) ha) (const_computes [false])
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  cases hF : contains (pairBits (discardPrefix x,itemField 8 x)) <;>
    cases hW : contains (pairBits (discardPrefix x,itemField 1 x)) <;>
      by_cases ha : answer x=[] <;> simp [eligible,hF,hW,ha]
noncomputable def chosen_computes : PolyComputes chosen := Find.run_computes eligible_computes
noncomputable def chosenQuery_computes : PolyComputes chosenQuery :=
  extractPrefix_computes.pair (chosen_computes.comp WordOperations.tail_computes)

noncomputable def bids_computes : PolyComputes bids := by
  have computation := ((answer_computes.comp WordOperations.tail_computes).pair
    (extractPrefix_computes.comp BinaryOpeningEnumeration.clients_computes)).comp
      (mapWith_computes (RationalMatrix.swapWords_computes.comp Lookup.run_computes))
  unfold bids
  simpa only [Function.comp_def] using computation
noncomputable def run_computes : PolyComputes run :=
  by
  have h := (chosen_computes.comp isEmpty_computes).cond (const_computes [])
    (((chosen_computes.comp WordOperations.tail_computes).pair (chosenQuery_computes.comp bids_computes)).comp
      (prefix_computes true))
  change PolyComputes (fun x=>if chosen x=[] then [] else true::pairBits ((chosen x).tail,bids (chosenQuery x)))
  simpa only [decide_eq_true_eq,Function.comp_def] using h

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
namespace WordList
noncomputable def filterWith_computes {p : List Bool → Bool} (hp : PolyComputes (fun x=>[p x])) :
    PolyComputes (filterWith p) := flatMapWith_computes (filterItem_computes hp)
end WordList
namespace BinaryFiniteInsert
open WordList BinaryPhaseFirst EffectiveOpenability
noncomputable def run_computes : PolyComputes run := filterWith_computes keep_computes
end BinaryFiniteInsert
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_StateBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryPhaseUpdate
open WordOperations BinaryArithmetic WordList EffectiveOpenability RationalPhase
open BinaryOpeningPayment

noncomputable def opened_computes : PolyComputes opened :=
  (((ctxField_computes 1).pair newFacility_computes).pair (context_computes.comp allFacilities_computes)).comp
    BinaryFiniteInsert.run_computes
noncomputable def updatedContext_computes : PolyComputes updatedContext :=
  cons_computes (ctxField_computes 0) (cons_computes opened_computes (cons_computes (ctxField_computes 2)
    (cons_computes (ctxField_computes 3) (cons_computes (ctxField_computes 4) (cons_computes (ctxField_computes 5)
    (cons_computes (ctxField_computes 6) (cons_computes (ctxField_computes 7)
    (cons_computes (ctxField_computes 8) (const_computes [])))))))))
noncomputable def active_computes : PolyComputes (fun x=>[active x]) :=
  ((extractPrefix_computes.comp context_computes).pair discardPrefix_computes).comp BinaryOpeningPayment.active_computes
noncomputable def budgetItem_computes : PolyComputes budgetItem := by
  have h := active_computes.cond
    ((discardPrefix_computes.pair (extractPrefix_computes.comp newBudget_computes)).comp Lookup.run_computes)
    ((discardPrefix_computes.pair (extractPrefix_computes.comp oldBudget_computes)).comp Lookup.run_computes)
  exact h
noncomputable def updatedBudget_computes : PolyComputes updatedBudget := by
  have computation := (id_computes.pair (context_computes.comp BinaryOpeningEnumeration.clients_computes)).comp
    (mapWith_computes budgetItem_computes)
  unfold updatedBudget
  simpa only [Function.comp_def, id_eq] using computation
noncomputable def run_computes : PolyComputes run := updatedContext_computes.pair updatedBudget_computes
end MetricKMedianRecovery.BitMachine.BinaryPhaseUpdate

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
noncomputable def answer_computes : PolyComputes answer :=
  (extractPrefix_computes.pair (extractPrefix_computes.comp allFacilities_computes)).comp BinaryPhaseFirst.run_computes
end MetricKMedianRecovery.BitMachine.BinaryPhaseFinish

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Strictness_BidPoly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryPhaseFinish
open WordOperations BinaryArithmetic WordList EffectiveOpenability RationalPhase BinaryPhaseUpdate
noncomputable def bidPoly : Polynomial ℕ := BinaryPhaseFirst.run_computes.lengthPolynomial.comp (20*(Polynomial.X+1)^2)
noncomputable def capPoly : Polynomial ℕ := 40*(Polynomial.X+1)^2+4*(Polynomial.X+1)*bidPoly
end MetricKMedianRecovery.BitMachine.BinaryPhaseFinish

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Pack11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryPhaseTrace
open WordOperations BinaryArithmetic WordList EffectiveOpenability RationalPhase BinaryPhaseUpdate
open BinaryPhaseFinish
noncomputable def answer_computes : PolyComputes answer := extractPrefix_computes.comp BinaryPhaseFinish.answer_computes
noncomputable def step_computes : PolyComputes step := by
  have ha := answer_computes.comp WordOperations.tail_computes
  have h := (answer_computes.comp isEmpty_computes).cond id_computes
    (((extractPrefix_computes.pair ha).comp BinaryPhaseUpdate.run_computes).pair (cons_computes ha discardPrefix_computes))
  change PolyComputes (fun x=>if answer x=[] then x else pairBits
    (BinaryPhaseUpdate.run (pairBits (extractPrefix x,(answer x).tail)),cons (answer x).tail (discardPrefix x)))
  simpa only [Function.comp_def,decide_eq_true_eq,id_eq] using h
noncomputable def traceCapPoly : Polynomial ℕ := 2*capPoly+1+Polynomial.X*(2*capPoly+2)
noncomputable def resource : PolynomialCounter traceCapPoly := PolynomialCounter.choose traceCapPoly
noncomputable def loop (x : List Bool) : List Bool :=
  BoundedIteration.run step (pairBits (extractPrefix x,pairBits (resource.word x,pairBits (discardPrefix x,[]))))
noncomputable def loop_computes : PolyComputes loop :=
  (extractPrefix_computes.pair (resource.computes.pair (discardPrefix_computes.pair (const_computes [])))).comp
    (BoundedIteration.run_computes step_computes)
attribute [local irreducible] loop loop_computes
noncomputable def run (x : List Bool) : List Bool :=
  pairBits (extractPrefix (loop x),WordList.reverse (discardPrefix (loop x)))
noncomputable def run_computes : PolyComputes run :=
  loop_computes.comp (extractPrefix_computes.pair (discardPrefix_computes.comp WordList.reverse_computes))
end MetricKMedianRecovery.BitMachine.BinaryPhaseTrace

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_InstructionBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRunTrace
open WordOperations BinaryArithmetic WordList EffectiveOpenability RationalPhase BinaryPhaseUpdate

noncomputable def finished (x : List Bool) : List Bool := BinaryPhaseTrace.run (pairBits (BinaryPhaseRun.fuel x,x))
noncomputable def finished_computes : PolyComputes finished :=
  (BinaryPhaseRun.fuel_computes.pair id_computes).comp BinaryPhaseTrace.run_computes
end MetricKMedianRecovery.BitMachine.BinaryRunTrace

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_HistoryBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryHistoryRun
open WordOperations BinaryArithmetic WordList EffectiveOpenability RationalPhase BinaryPhaseUpdate
open BinaryRunTrace (finished finished_computes )
attribute [local irreducible] finished finished_computes
noncomputable def chunk (x : List Bool) : List Bool :=
  cons (WordList.map extractPrefix (discardPrefix (finished x))) []
noncomputable def chunk_computes : PolyComputes chunk := by
  have hc : PolyComputes (fun x=>WordList.map extractPrefix (discardPrefix (finished x))) := by
    simpa only [Function.comp_def] using
      ((finished_computes.comp discardPrefix_computes).comp (map_computes extractPrefix_computes))
  unfold chunk
  exact cons_computes hc (const_computes [])
attribute [local irreducible] chunk chunk_computes
end MetricKMedianRecovery.BitMachine.BinaryHistoryRun

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_DecisionOps
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace RatOps
noncomputable def lt {f g : List Bool → ℚ}
    (hf : PolyComputes (fun x=>BinaryRational.encode (f x)))
    (hg : PolyComputes (fun x=>BinaryRational.encode (g x))) :
    PolyComputes (fun x=>[decide (f x<g x)]) := by
  simpa only [←decide_not,not_le] using (le hg hf).not
noncomputable def eq {f g : List Bool → ℚ}
    (hf : PolyComputes (fun x=>BinaryRational.encode (f x)))
    (hg : PolyComputes (fun x=>BinaryRational.encode (g x))) :
    PolyComputes (fun x=>[decide (f x=g x)]) := by
  simpa only [←Bool.decide_and,le_antisymm_iff] using ((le hf hg).and (le hg hf))
end RatOps
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_SortMath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations
namespace WordList.Sort

noncomputable def insert_computes {p : List Bool → Bool} (hp : PolyComputes (fun x=>[p x])) :
    PolyComputes (insert p) :=
  (filterWith_computes (reverseTest_computes hp)).append
    (cons_computes extractPrefix_computes (filterWith_computes hp))

variable {α : Type*} [LinearOrder α]
noncomputable def op_computes {p : List Bool → Bool} (hp : PolyComputes (fun x=>[p x])) :
    PolyComputes (op p) :=
  (Find.item_computes.pair Fold.accum_computes).comp (insert_computes hp)
noncomputable def run_computes {p : List Bool → Bool} (hp : PolyComputes (fun x=>[p x])) :
    PolyComputes (run p) :=
  (Fold.pack_computes id_computes (const_computes []) (const_computes [])).comp
    (Fold.run_computes (op_computes hp) (3*Polynomial.X+3))
end WordList.Sort
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_LabelOrder
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryLabel
open WordOperations BinaryArithmetic RationalLeaves

noncomputable def lt_computes : PolyComputes (fun x=>[lt x]) :=
  (NatOps.lt (extractPrefix_computes.comp levelWords_computes) (discardPrefix_computes.comp levelWords_computes)).or
    ((NatOps.eq (extractPrefix_computes.comp levelWords_computes) (discardPrefix_computes.comp levelWords_computes)).and
      ((NatOps.lt (extractPrefix_computes.comp parentWords_computes) (discardPrefix_computes.comp parentWords_computes)).or
        ((NatOps.eq (extractPrefix_computes.comp parentWords_computes) (discardPrefix_computes.comp parentWords_computes)).and
          (RatOps.lt (RatOps.ofWords (extractPrefix_computes.comp heightWords_computes))
            (RatOps.ofWords (discardPrefix_computes.comp heightWords_computes))))))

noncomputable def sort_computes : PolyComputes sort := WordList.Sort.run_computes lt_computes
attribute [local irreducible] MetricTable.get
noncomputable def row_computes : PolyComputes row :=
  RatOps.add (RatOps.ofWords rawRow_computes)
    (RatOps.max (RatOps.ofWords (label_computes.comp heightWords_computes)) (RatOps.const 0))
end MetricKMedianRecovery.BitMachine.BinaryLabel

namespace MetricKMedianRecovery.BitMachine.BinaryLabelMatrix
open WordOperations WordList RationalLeaves
attribute [local irreducible] mapWith

noncomputable def entry_computes : PolyComputes entry :=
  ((table_computes.pair item_computes).pair col_computes).comp BinaryLabel.row_computes
noncomputable def row_computes : PolyComputes row :=
  (id_computes.pair ((extractPrefix_computes.comp discardPrefix_computes).comp BinaryEllipsoidInitial.indices_computes)).comp
    (mapWith_computes entry_computes)
noncomputable def run_computes : PolyComputes run := mapWith_computes row_computes
end MetricKMedianRecovery.BitMachine.BinaryLabelMatrix

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_LabelMember
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryLabel
open WordOperations BinaryArithmetic WordList RationalLeaves

noncomputable def eq_computes : PolyComputes (fun x=>[eq x]) :=
  (NatOps.eq (extractPrefix_computes.comp levelWords_computes) (discardPrefix_computes.comp levelWords_computes)).and
    ((NatOps.eq (extractPrefix_computes.comp parentWords_computes) (discardPrefix_computes.comp parentWords_computes)).and
      (RatOps.eq (RatOps.ofWords (extractPrefix_computes.comp heightWords_computes))
        (RatOps.ofWords (discardPrefix_computes.comp heightWords_computes))))
noncomputable def contains_computes : PolyComputes (fun x=>[contains x]) := by
  have h := ((Find.run_computes eq_computes).comp isEmpty_computes).not
  simpa only [contains,←decide_not] using h

end MetricKMedianRecovery.BitMachine.BinaryLabel

namespace MetricKMedianRecovery.BitMachine.BinaryLabelSelect
open Classical
open WordOperations BinaryArithmetic WordList RationalLeaves EffectiveOpenability

noncomputable def test_computes : PolyComputes (fun x=>[test x]) :=
  (((index_computes.pair alphabet_computes).comp Lookup.run_computes).pair target_computes).comp
    BinaryLabel.contains_computes
noncomputable def run_computes : PolyComputes run :=
  (id_computes.pair (extractPrefix_computes.comp Indices.run_computes)).comp (filterWith_computes test_computes)
end MetricKMedianRecovery.BitMachine.BinaryLabelSelect

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_LabelLookup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryLabelLookup
open WordOperations WordList RationalLeaves
noncomputable def item_computes : PolyComputes item :=
  (discardPrefix_computes.pair extractPrefix_computes).comp Lookup.run_computes
end MetricKMedianRecovery.BitMachine.BinaryLabelLookup

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_FiniteContext
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryFiniteContext
open Classical
open WordOperations WordList BinaryOpeningPayment RationalLeaves
open BinaryLabel (orderedSort)

noncomputable def alphabet_computes : PolyComputes alphabet :=
  (((field_computes 2).append (field_computes 3)).append (field_computes 4)).comp BinaryLabel.sort_computes
noncomputable def selected_computes (k : ℕ) : PolyComputes (selected k) :=
  (alphabet_computes.pair (field_computes k)).comp BinaryLabelSelect.run_computes
attribute [local irreducible] BinaryLabelMatrix.run
noncomputable def matrix_computes : PolyComputes matrix :=
  (((field_computes 0).pair (field_computes 1)).pair alphabet_computes).comp BinaryLabelMatrix.run_computes
attribute [local irreducible] matrix selected
noncomputable def run_computes : PolyComputes run :=
  list_computes [matrix,selected 3,field 5,field 6,field 7,(fun _=>BinaryRational.encode 0),(fun _=>[]),field 1,selected 2] (by
    intro f hf
    refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals first | exact ⟨matrix_computes⟩ | exact ⟨selected_computes _⟩ | exact ⟨field_computes _⟩ | exact ⟨const_computes _⟩)
end MetricKMedianRecovery.BitMachine.BinaryFiniteContext

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

noncomputable def initial_computes : PolyComputes initial :=
  (BinaryFiniteContext.run_computes.pair (field_computes 6)).comp BinaryPhaseCount.start_computes

noncomputable def finished : List Bool → List Bool := BinaryRunTrace.finished ∘ initial
noncomputable def finished_computes : PolyComputes finished :=
  PolyComputes.comp (f:=initial) (g:=BinaryRunTrace.finished) initial_computes BinaryRunTrace.finished_computes
noncomputable def completedTrace : List Bool → List Bool := discardPrefix ∘ finished
noncomputable def completed_trace_computes : PolyComputes completedTrace :=
  PolyComputes.comp (f:=finished) (g:=discardPrefix) finished_computes discardPrefix_computes
noncomputable def completed : List Bool → List Bool := WordList.map extractPrefix ∘ completedTrace
noncomputable def completed_computes : PolyComputes completed :=
  PolyComputes.comp (f:=completedTrace) (g:=WordList.map extractPrefix)
    completed_trace_computes (map_computes extractPrefix_computes)
noncomputable def complete (x : List Bool) : List Bool :=
  BinaryLabelLookup.run (pairBits (BinaryFiniteContext.alphabet x,completed x))
end MetricKMedianRecovery.BitMachine.BinaryFiniteMachine

namespace MetricKMedianRecovery.BitMachine.BinaryFiniteContext
open WordOperations WordList RationalLeaves
open BinaryOpeningPayment (field field_computes field_encode)
noncomputable def union_computes : PolyComputes union :=
  (extractPrefix_computes.append discardPrefix_computes).comp BinaryLabel.sort_computes
noncomputable def replaceOpen_computes : PolyComputes replaceOpen :=
  list_computes [field 0 ∘ extractPrefix,field 1 ∘ extractPrefix,field 2 ∘ extractPrefix,discardPrefix,
    field 4 ∘ extractPrefix,field 5 ∘ extractPrefix,field 6 ∘ extractPrefix,field 7 ∘ extractPrefix] (by
    intro f hf
    refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals first | exact ⟨extractPrefix_computes.comp (field_computes _)⟩ | exact ⟨discardPrefix_computes⟩)
end MetricKMedianRecovery.BitMachine.BinaryFiniteContext

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_ActionMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryActions
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
open RationalSampling
variable {n : ℕ}
attribute [local irreducible] RawTake.run
noncomputable def entry_computes (k : ℕ) : PolyComputes (entry k) :=
  (const_computes k.bits).pair ((discardPrefix_computes.pair extractPrefix_computes).comp RawTake.run_computes)
noncomputable def block_computes (k : ℕ) : PolyComputes (block k) := by
  have computation := (id_computes.pair BinaryEllipsoidInitial.indices_computes).comp (mapWith_computes (entry_computes k))
  unfold block
  simpa only [Function.comp_def, id_eq] using computation
noncomputable def menus_computes : PolyComputes menus := by
  have computation := (((field_computes 0).comp (block_computes 0)).append (((field_computes 1).append (const_computes [true])).comp (block_computes 1))).append
    ((field_computes 2).comp (block_computes 2))
  unfold menus
  simpa only [Function.comp_def] using computation
noncomputable def delete_computes : PolyComputes delete := cons_computes (const_computes _) (cons_computes discardPrefix_computes (const_computes (encode [[]])))
noncomputable def add_computes : PolyComputes add := cons_computes (const_computes _) (cons_computes extractPrefix_computes (cons_computes discardPrefix_computes (const_computes [])))
noncomputable def run_computes : PolyComputes run := by
  have computation := ((const_computes (encode [encode [(0:ℕ).bits,[],[]]])).append (((const_computes []).pair extractPrefix_computes).comp (mapWith_computes delete_computes))).append
    ((extractPrefix_computes.pair (discardPrefix_computes.comp menus_computes)).comp (crossWith_computes add_computes))
  unfold run
  simpa only [Function.comp_def] using computation
end MetricKMedianRecovery.BitMachine.BinaryActions

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_DeleteFold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryDelete
open WordOperations WordList RationalLeaves CanonicalDelete
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
open BinaryOpeningPayment (field field_computes field_encode)

noncomputable def cf_computes (n : ℕ) : PolyComputes (cf n) := extractPrefix_computes.comp (field_computes n)
noncomputable def sf_computes (n : ℕ) : PolyComputes (sf n) :=
  (discardPrefix_computes.comp discardPrefix_computes).comp (field_computes n)
noncomputable def rest_computes : PolyComputes rest := (sf_computes 0).comp WordList.tail_computes
noncomputable def retained_computes : PolyComputes retained :=
  ((cf_computes 1).append rest_computes).append (cons_computes (cf_computes 2) (sf_computes 1))
noncomputable def openSet_computes : PolyComputes openSet :=
  (((cf_computes 0).comp (field_computes 3)).pair retained_computes).comp BinaryFiniteContext.union_computes
noncomputable def extended_computes : PolyComputes extended :=
  ((cf_computes 0).pair openSet_computes).comp BinaryFiniteContext.replaceOpen_computes
noncomputable def added : List Bool → List Bool := BinaryFiniteMachine.complete ∘ extended
noncomputable def extras (x : List Bool) : List Bool := sf 1 x++added x
noncomputable def vertex (x : List Bool) : List Bool := cf 1 x++rest x++WordList.cons (cf 2 x) (extras x)
noncomputable def vertices (x : List Bool) : List Bool := sf 2 x++WordList.cons (vertex x) []
noncomputable def step (x : List Bool) : List Bool := encode [rest x,extras x,vertices x]
end MetricKMedianRecovery.BitMachine.BinaryDelete

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_DeleteSize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryDelete
open WordOperations WordList RationalLeaves CanonicalDelete
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)

noncomputable def run (x : List Bool) : List Bool := CappedFold.run step (pairBits (capacity.word x,x))
end MetricKMedianRecovery.BitMachine.BinaryDelete

namespace MetricKMedianRecovery.BitMachine.BinaryAdvance
open WordOperations WordList RationalLeaves
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
open BinaryOpeningPayment (field field_computes field_encode)

noncomputable def deletionInput_computes : PolyComputes deletionInput := by
  have hctx := list_computes [field 0,field 1,field 4] (by
    intro f hf; refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl <;> exact ⟨field_computes _⟩)
  have hacc := list_computes [field 2,fun _=>[],fun _=>[]] (by
    intro f hf; refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl
    · exact ⟨field_computes _⟩
    all_goals exact ⟨const_computes []⟩)
  exact Fold.pack_computes (field_computes 2) hctx hacc
noncomputable def deleted : List Bool → List Bool := BinaryDelete.run ∘ deletionInput
end MetricKMedianRecovery.BitMachine.BinaryAdvance

end OAI
end


