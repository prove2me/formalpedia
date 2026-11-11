-- Prove2me | Definitions.Def_Q238K024
-- name    : Q238K024
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T23:18:37.991776+00:00
-- url     : https://prove2.me/theorems/26355806-7a63-4844-abd6-6ba81ca2025a
-- title:
--   Definitions bundle Q238K024 of the split of OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 107 declarations of OpenAI's Lean: 97 definitions and 10 theorems. The definitions and types are `OAI.MetricKMedianRecovery.BitMachine.BinaryArithmetic.add_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBoundedDecision.run`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.base`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.count`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.dim`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.doubledGap`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.epsilon`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.gap`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.power`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.precision`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.precisionArg`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.prepared`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.radius`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.radiusPrecision`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.relaxedWords`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.rowFactor`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.run`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.solved`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidAdvance.nextState`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidAdvance.run`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidAdvance.updated`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidCut.gridInput`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidCut.inflateInput`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidCut.inflateWords`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidCut.shapeWords`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidInitial.dummy_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidIteration.boundCounter`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidIteration.prepared`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidIteration.run`, `OAI.MetricKMedianRecovery.BitMachine.BinaryExactSolve.gram`, `OAI.MetricKMedianRecovery.BitMachine.BinaryExactSolve.point`, `OAI.MetricKMedianRecovery.BitMachine.BinaryExactSolve.rhs`, `OAI.MetricKMedianRecovery.BitMachine.BinaryExactSolve.run`, `OAI.MetricKMedianRecovery.BitMachine.BinaryExactSolve.transposed`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFace.decision`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFace.op`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFace.run`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFinalFace.run`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningConstant.constant`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningPayment.run` and 57 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedianRecovery_Branching_CopyComputes`, `KMedianRecovery_Encoding_OptionEncode`, `KMedianRecovery_Encoding_PushWord`, `KMedianRecovery_Machines_SubProgram`, `KMedianRecovery_Recovery_Basic2`, `KMedianRecovery_Recovery_BoundOp`, `KMedianRecovery_Recovery_BoundedDecision`, `KMedianRecovery_Recovery_Copies`, `KMedianRecovery_Recovery_FaceSelection`, `KMedianRecovery_Recovery_LengthPolynomial`, `KMedianRecovery_Recovery_Normalize`, `KMedianRecovery_Recovery_Op`, `KMedianRecovery_Recovery_Pack3`, `KMedianRecovery_Recovery_Pack5`, `KMedianRecovery_Recovery_Pack6`, `KMedianRecovery_Recovery_Pack7`, `KMedianRecovery_Recovery_Pack8`, `KMedianRecovery_Recovery_Pack9`, `KMedianRecovery_Recovery_ProcessOutputs`, `KMedianRecovery_Recovery_Rectangular`, `KMedianRecovery_Recovery_RowInput`, `KMedianRecovery_Recovery_Step`, `KMedianRecovery_Recovery_Step2`, `KMedianRecovery_Recovery_StepThen`, `KMedianRecovery_Recovery_Values`, `KMedianRecovery_Sampling_ExtractPrefix`.
--
--   **Imports.** It imports the published bundle `Def_KMedianRefinedRecovery`; the bundles `Q238K017`, `Q238K018` and `Q238K019` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q238K028`, `Q238K029`, `Q238K030` and `Q238K031`; the statements `OAI.MetricKMedianRecovery.BitMachine.BinaryBoundedDecision.run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.prepared_pack_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryDecision_run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidCut.inflateWords_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidCut.shapeWords_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidIteration.run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryExactSolve.gram_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryExactSolve.point_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryExactSolve.rhs_pack_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryExactSolve_run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryExactSolve.transposed_pack_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryFace_run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFinalFace.run_pack_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryGlobalOuter_scales_bits_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseFirst.bids_context_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseFirst.eligible_context_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRawOpening.prepared_pack_s238` and `OAI.MetricKMedianRecovery.BitMachine.BinaryRawOpening.rowWord_pack_s238`; the proofs of `OAI_MetricKMedianRecovery_BitMachine_BinaryBlueBlocks_run_pack_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryBranchContext_classOf_pack_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryDecision_run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidCut.inflateWords_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidCut.shapeWords_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidIteration.run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryExactSolve.gram_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryExactSolve.point_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryExactSolve.rhs_pack_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryExactSolve_run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryExactSolve.transposed_pack_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryFace_run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFinalFace.run_pack_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryGlobalOuter_scales_bits_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryLabelSelect_run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseFirst.bids_context_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseFirst.eligible_context_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRawOpening.prepared_pack_s238`, `OAI_MetricKMedianRecovery_BitMachine_Rectangular_mulVec_encode_s238`, `OAI_MetricKMedianRecovery_BitMachine_WordList_CappedFold_run_typed_s238` and `OAI_MetricKMedianRecovery_BitMachine_WordList_Set_run_encode_s238`.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_KMedianRefinedRecovery
import Definitions.Def_Q238K017
import Definitions.Def_Q238K018
import Definitions.Def_Q238K019

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_StepThen
attribute [-simp] _root_.OAI.MetricKMedianRecovery.BitMachine.discardPrefix_pairBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open Turing Turing.TM2 StateTransition

noncomputable def tail_outputs (xs : List Bool) :
    EvalsToInTime tailProgram.machine.step (tailCfg xs) (some (tailEnd (discardPrefix xs)))
      (xs.length+1) := by
  induction xs using List.twoStepInduction with
  | nil => exact one_step tail_step_nil
  | singleton b =>
    cases b with
    | false => exact time_mono (one_step (tail_step_false [])) (by decide)
    | true => exact step_then (tail_step_true []) (one_step tail_step_nil)
  | cons_cons b c xs ih _ihc =>
    cases b with
    | false => exact time_mono (one_step (tail_step_false (c::xs))) (by simp)
    | true =>
      have hh := step_then (tail_step_true (c::xs)) ih
      exact time_mono hh (by simp)

noncomputable def discardPrefix_computes : PolyComputes discardPrefix where
  program := tailProgram
  time := Polynomial.X+1
  outputs xs := by
    simpa only [TM2OutputsInTime,Option.map_some,tail_initial,tail_final,
      Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one] using tail_outputs xs

end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_ExtractPrefix
attribute [-simp] _root_.OAI.MetricKMedianRecovery.BitMachine.extractPrefix_pairBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open Turing Turing.TM2 StateTransition

noncomputable def head_outputs (xs ys : List Bool) :
    EvalsToInTime headProgram.machine.step (headCfg false xs ys)
      (some (headEnd ((extractPrefix xs).reverse++ys))) (xs.length+2) := by
  induction xs using List.twoStepInduction generalizing ys with
  | nil => exact step_then (head_step_nil ys) (one_step (head_clear_nil ys))
  | singleton b =>
    cases b with
    | false => exact time_mono (step_then (head_step_false [] ys) (head_clear_outputs [] ys)) (by decide)
    | true => exact time_mono (one_step (head_step_one ys)) (by decide)
  | cons_cons b c xs ih _ =>
    cases b with
    | false =>
      exact time_mono (step_then (head_step_false (c::xs) ys) (head_clear_outputs (c::xs) ys)) (by simp)
    | true =>
      have hh := step_then (head_step_true c xs ys) (ih (c::ys))
      simp only [extractPrefix,List.reverse_cons,List.append_assoc,List.singleton_append] at ⊢
      exact time_mono hh (by simp)

noncomputable def extractReverse_computes : PolyComputes (fun xs => (extractPrefix xs).reverse) where
  program := headProgram
  time := Polynomial.X+2
  outputs xs := by
    simpa only [TM2OutputsInTime,Option.map_some,head_initial,head_final,
      Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_ofNat,List.append_nil] using head_outputs xs []

noncomputable def extractPrefix_computes : PolyComputes extractPrefix := by
  have hh := extractReverse_computes.comp reverse_computes
  simpa only [Function.comp_def,List.reverse_reverse] using hh

end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Normalize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open Turing Turing.TM2 StateTransition
namespace BinaryArithmetic

noncomputable def add_computes : PolyComputes (fun xs =>
    normalize (add false (extractPrefix xs) (discardPrefix xs))) := by
  have hh := (addReverse_computes.comp trim_computes).comp reverse_computes
  exact hh

end BinaryArithmetic
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_SubProgram
attribute [-simp] _root_.OAI.MetricKMedianRecovery.BitMachine.MapLeft.stacks_left _root_.OAI.MetricKMedianRecovery.BitMachine.MapLeft.stacks_one _root_.OAI.MetricKMedianRecovery.BitMachine.MapLeft.stacks_zero _root_.OAI.MetricKMedianRecovery.BitMachine.frameStacks_inl _root_.OAI.MetricKMedianRecovery.BitMachine.frameStacks_inr
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open Turing Turing.TM2 StateTransition
namespace BinarySubtraction
open BinaryArithmetic

lemma parse_nil (ys : List Bool) :
    subProgram.machine.step (cfg 0 false [] ys [])=some (cfg 1 false [] ys []) := by
  simp [FinTM2.step,cfg,subProgram,TM2.step,TM2.stepAux,update_zero]
  rfl
lemma parse_one (ys : List Bool) :
    subProgram.machine.step (cfg 0 false [true] ys [])=some (cfg 1 false [] ys []) := by
  simp [FinTM2.step,cfg,subProgram,TM2.step,TM2.stepAux,update_zero]
  rfl
lemma parse_false (xs ys : List Bool) :
    subProgram.machine.step (cfg 0 false (false::xs) ys [])=some (cfg 1 false xs ys []) := by
  simp [FinTM2.step,cfg,subProgram,TM2.step,TM2.stepAux,update_zero]
  rfl
lemma parse_true (b : Bool) (xs ys : List Bool) :
    subProgram.machine.step (cfg 0 false (true::b::xs) ys [])=some (cfg 0 false xs (b::ys) []) := by
  simp [FinTM2.step,cfg,subProgram,TM2.step,TM2.stepAux,update_zero,update_one]
  rfl

lemma rev_nil (xs zs : List Bool) :
    subProgram.machine.step (cfg 1 false xs [] zs)=some (cfg 2 false xs [] zs) := by
  simp [FinTM2.step,cfg,subProgram,TM2.step,TM2.stepAux,update_one]
  rfl
lemma rev_cons (b : Bool) (xs ys zs : List Bool) :
    subProgram.machine.step (cfg 1 false xs (b::ys) zs)=some (cfg 1 false xs ys (b::zs)) := by
  simp [FinTM2.step,cfg,subProgram,TM2.step,TM2.stepAux,update_one,update_two]
  rfl

lemma clear_cons (b : Bool) (xs : List Bool) :
    subProgram.machine.step (cfg 3 false [] (b::xs) [])=some (cfg 3 false [] xs []) := by
  simp [FinTM2.step,cfg,subProgram,TM2.step,TM2.stepAux,update_one]
  rfl

end BinarySubtraction
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_PushWord
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open Turing Turing.TM2 StateTransition

noncomputable def head_computes : PolyComputes (fun xs=>[xs.head?.getD false]) := by
  have hh := FiniteFold.computes (none : Option Bool) (fun q b=>q.orElse (fun _=>some b)) (fun q=>[q.getD false])
  simpa only [fold_orElse,Option.orElse_none] using hh

end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_ProcessOutputs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine

open WordOperations BinaryArithmetic
namespace NatOps

noncomputable def add {f g : List Bool → List Bool} (hf : PolyComputes f) (hg : PolyComputes g) :
    PolyComputes (fun x=>(value (f x)+value (g x)).bits) := by
  have hh := (hf.pair hg).comp BinaryArithmetic.add_computes
  simpa only [Function.comp_def,pairBits,extractPrefix_pair,discardPrefix_pair,normalize_eq_bits,value_add,Bool.toNat_false,Nat.add_zero] using hh

end NatOps
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Pack3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace UnaryTake

noncomputable def counter_computes : PolyComputes counter := tail_computes.comp extractPrefix_computes
noncomputable def data_computes : PolyComputes data :=
  (tail_computes.comp discardPrefix_computes).comp extractPrefix_computes
noncomputable def output_computes : PolyComputes output :=
  (tail_computes.comp discardPrefix_computes).comp discardPrefix_computes
noncomputable def step_computes : PolyComputes step := by
  have hc := counter_computes.comp isEmpty_computes
  have hd := data_computes.comp isEmpty_computes
  have ho := hd.cond output_computes ((data_computes.comp head_computes).append output_computes)
  have ht := pack_computes true (counter_computes.comp tail_computes)
    (data_computes.comp tail_computes) ho
  have hh := hc.cond (pack_computes false (const_computes []) data_computes output_computes) ht
  unfold step
  simpa only [Function.comp_def,decide_eq_true_eq,List.singleton_append] using hh

noncomputable def loop_computes : PolyComputes (fun x=>next^[rank x] x) := by
  apply step_computes.whileLoop rank (Polynomial.X+1) (7*Polynomial.X+3)
  · intro x
    have h := (projection_bounds x).1
    simp only [Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one]
    unfold rank; split_ifs <;> omega
  · intro x j _
    have h := (iterate_bounds x j).2.1
    obtain ⟨hc,hd,ho⟩ := projection_bounds x
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X]
    change (next^[j] x).length ≤ _
    unfold mass at h
    omega
  · exact stop

noncomputable def takeWords_computes : PolyComputes takeWords := by
  have hi := pack_computes true extractPrefix_computes discardPrefix_computes (const_computes [])
  have hh := ((hi.comp loop_computes).comp output_computes).comp reverse_computes
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  simp only [Function.comp_apply,rank,pack,List.head?_cons,ite_true, if_true,counter,List.tail_cons,
    extractPrefix_pairBits]
  change takeWords x=(output (next^[(extractPrefix x).length+1]
    (pack true (extractPrefix x) (discardPrefix x) []))).reverse
  rw [loop_spec,output_pack,List.append_nil,List.reverse_reverse]
  rfl

end UnaryTake
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Step
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations UnaryTake
namespace BoundedIteration

noncomputable def step_computes {f : List Bool → List Bool} (hf : PolyComputes f) :
    PolyComputes (step f) := by
  have hu := (data_computes.pair (output_computes.comp hf)).comp takeWords_computes
  have ht := pack_computes true (counter_computes.comp tail_computes) data_computes hu
  have hh := (counter_computes.comp isEmpty_computes).cond
    (pack_computes false (const_computes []) data_computes output_computes) ht
  unfold step
  simpa only [Function.comp_def,takeWords,extractPrefix_pairBits,discardPrefix_pairBits,
    decide_eq_true_eq] using hh

noncomputable def loop_computes {f : List Bool → List Bool} (hf : PolyComputes f) :
    PolyComputes (fun x=>(next f)^[rank x] x) := by
  apply (step_computes hf).whileLoop rank (Polynomial.X+1) (7*Polynomial.X+3)
  · intro x
    have h := (projection_bounds x).1
    simp only [Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one]
    unfold rank; split_ifs <;> omega
  · intro x j _
    have h := (iterate_bounds f x j).2.2.2.1
    obtain ⟨hc,hd,ho⟩ := projection_bounds x
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X]
    change ((next f)^[j] x).length ≤ _
    omega
  · exact stop f

noncomputable def run_computes {f : List Bool → List Bool} (hf : PolyComputes f) : PolyComputes (run f) := by
  have hi := pack_computes true extractPrefix_computes
    (discardPrefix_computes.comp extractPrefix_computes)
    (discardPrefix_computes.comp discardPrefix_computes)
  have hh := (hi.comp (loop_computes hf)).comp output_computes
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  simp only [Function.comp_apply,rank,head_pack,ite_true, if_true,counter_pack,loop_spec,output_pack]
  rfl

end BoundedIteration
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Copies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations UnaryTake
namespace RepeatedAppend

noncomputable def step_computes : PolyComputes step := by
  have ht := pack_computes true (counter_computes.comp tail_computes) data_computes
    (data_computes.append output_computes)
  have hh := (counter_computes.comp isEmpty_computes).cond
    (pack_computes false (const_computes []) data_computes output_computes) ht
  unfold step
  simpa only [Function.comp_def,decide_eq_true_eq] using hh

noncomputable def loop_computes : PolyComputes (fun x=>next^[rank x] x) := by
  apply step_computes.whileLoop rank (Polynomial.X+1) (20*(Polynomial.X+1)^2)
  · intro x
    have h := (projection_bounds x).1
    simp only [Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one]
    unfold rank; split_ifs <;> omega
  · intro x j hj
    have h := (iterate_bounds x j).2.2.2.1
    obtain ⟨hc,hd,ho⟩ := projection_bounds x
    have hr : rank x ≤ x.length+1 := by unfold rank; split_ifs <;> omega
    have hjd : j*(data x).length ≤ (x.length+1)*x.length := Nat.mul_le_mul (hj.trans hr) hd
    simp only [Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_pow,Polynomial.eval_add,
      Polynomial.eval_X,Polynomial.eval_one]
    change (next^[j] x).length ≤ _
    nlinarith
  · exact stop
noncomputable def run_computes : PolyComputes run := by
  have hi := pack_computes true extractPrefix_computes discardPrefix_computes (const_computes [])
  have hh := (hi.comp loop_computes).comp output_computes
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  simp only [Function.comp_apply,rank,head_pack,ite_true, if_true,counter_pack,loop_spec,output_pack,List.append_nil]
  rfl

end RepeatedAppend

namespace PolynomialCounter
noncomputable def mul {P Q : Polynomial ℕ} (p : PolynomialCounter P) (q : PolynomialCounter Q) :
    PolynomialCounter (P*Q) where
  word x := RepeatedAppend.copies (p.word x).length (q.word x)
  computes := by
    have hh := (p.computes.pair q.computes).comp RepeatedAppend.run_computes
    simpa only [Function.comp_def,RepeatedAppend.run_pair] using hh
  word_length x := by simp only [RepeatedAppend.length_copies,p.word_length,q.word_length,Polynomial.eval_mul]

theorem nonempty (P : Polynomial ℕ) : Nonempty (PolynomialCounter P) := by
  induction P using Polynomial.induction_on with
  | C n => exact ⟨constant n⟩
  | add P Q hp hq => obtain ⟨p⟩ := hp; obtain ⟨q⟩ := hq; exact ⟨p.add q⟩
  | monomial n a ih =>
    obtain ⟨p⟩ := ih
    rw [pow_succ,←mul_assoc]
    exact ⟨p.mul identity⟩
noncomputable def choose (P : Polynomial ℕ) : PolynomialCounter P := Classical.choice (nonempty P)
end PolynomialCounter

namespace BoundedIteration

noncomputable def polynomialRun_computes {f : List Bool → List Bool} (hf : PolyComputes f)
    (Q R : Polynomial ℕ) : PolyComputes (polynomialRun f Q R) := by
  let q := PolynomialCounter.choose Q
  let r := PolynomialCounter.choose R
  have hh := (q.computes.pair (r.computes.pair id_computes)).comp (run_computes hf)
  unfold polynomialRun
  simpa only [Function.comp_def,run_pair,q.word_length,r.word_length,id_eq] using hh
end BoundedIteration
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_LengthPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations UnaryTake

lemma PolyComputes.length_bound {f : List Bool → List Bool} (hf : PolyComputes f) (x : List Bool) :
    (f x).length ≤ hf.lengthPolynomial.eval x.length := by
  simpa only [PolyComputes.lengthPolynomial,Polynomial.eval_add,Polynomial.eval_X,
    Polynomial.eval_mul,Polynomial.eval_C] using hf.program.output_length (hf.outputs x)

namespace WordList

noncomputable def head_computes : PolyComputes head := _root_.OAI.MetricKMedianRecovery.BitMachine.WordOperations.tail_computes.comp extractPrefix_computes
noncomputable def tail_computes : PolyComputes tail :=
  WordOperations.tail_computes.comp discardPrefix_computes
noncomputable def cons_computes {h t : List Bool → List Bool} (hh : PolyComputes h) (ht : PolyComputes t) :
    PolyComputes (fun x=>cons (h x) (t x)) := (hh.pair ht).comp (prefix_computes true)

namespace ReverseMap

noncomputable def step_computes {f : List Bool → List Bool} (hf : PolyComputes f) : PolyComputes (step f) := by
  have hn := (data_computes.pair (counter_computes.comp head_computes)).comp hf
  have ht := pack_computes true (counter_computes.comp tail_computes) data_computes
    (cons_computes hn output_computes)
  have hh := (counter_computes.comp isEmpty_computes).cond
    (pack_computes false (const_computes []) data_computes output_computes) ht
  unfold step
  simpa only [Function.comp_def,decide_eq_true_eq] using hh

lemma output_next {f : List Bool → List Bool} (hf : PolyComputes f) (x : List Bool) :
    (output (next f x)).length ≤ (output x).length+
      2*hf.lengthPolynomial.eval (2*(data x).length+1+(counter x).length)+2 := by
  have hp := hf.length_bound (pairBits (data x,head (counter x)))
  rw [pairBits_length] at hp
  have hl := head_length (counter x)
  have hm := polynomial_monotone hf.lengthPolynomial (show
    2*(data x).length+1+(head (counter x)).length ≤ 2*(data x).length+1+(counter x).length by omega)
  dsimp only at hm hp
  unfold next While.next; split_ifs
  · unfold step; split_ifs <;> simp only [output_pack,length_cons] <;> omega
  · omega
end ReverseMap

end WordList
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Step2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine

open WordOperations
namespace WordList
namespace Fold

noncomputable def items_computes : PolyComputes items := extractPrefix_computes
noncomputable def context_computes : PolyComputes context := discardPrefix_computes.comp extractPrefix_computes
noncomputable def accum_computes : PolyComputes accum := discardPrefix_computes.comp discardPrefix_computes
noncomputable def pack_computes {w c a : List Bool → List Bool} (hw : PolyComputes w)
    (hc : PolyComputes c) (ha : PolyComputes a) : PolyComputes (fun x=>pack (w x) (c x) (a x)) :=
  hw.pair (hc.pair ha)

noncomputable def step_computes {f : List Bool → List Bool} (hf : PolyComputes f) : PolyComputes (step f) := by
  have ha := (context_computes.pair ((items_computes.comp head_computes).pair accum_computes)).comp hf
  have ht := pack_computes (items_computes.comp tail_computes) context_computes ha
  have hh := (items_computes.comp isEmpty_computes).cond id_computes ht
  unfold step
  simpa only [Function.comp_def,decide_eq_true_eq,id_eq] using hh

noncomputable def run_computes {f : List Bool → List Bool} (hf : PolyComputes f) (R : Polynomial ℕ) :
    PolyComputes (run f R) :=
  (BoundedIteration.polynomialRun_computes (step_computes hf) Polynomial.X R).comp accum_computes

end Fold
end WordList
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Op
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine

open WordOperations BinaryArithmetic
namespace WordList
namespace Indices

noncomputable def op_computes : PolyComputes op := by
  let a : PolyComputes (fun x=>discardPrefix (discardPrefix x)) := discardPrefix_computes.comp discardPrefix_computes
  let l := a.comp extractPrefix_computes
  let r := a.comp discardPrefix_computes
  have hi := NatOps.add l (const_computes [true])
  have hh := hi.pair (cons_computes l r)
  unfold op
  simpa only [Function.comp_def,value,Bool.toNat_true,Nat.mul_zero,Nat.add_zero] using hh
end Indices
end WordList
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CopyComputes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace UnaryResources
noncomputable def copy_computes {f g : List Bool → List Bool} (hf : PolyComputes f) (hg : PolyComputes g) :
    PolyComputes (fun x=>RepeatedAppend.copies (f x).length (g x)) := by
  have hh := (hf.pair hg).comp RepeatedAppend.run_computes
  simpa only [Function.comp_def,RepeatedAppend.run_pair] using hh

noncomputable def cap : PolynomialCounter (2*Polynomial.X+2) := PolynomialCounter.choose _
noncomputable def lengthBits (x : List Bool) : List Bool :=
  BoundedIteration.run inc (pairBits (x,pairBits (cap.word x,(0:ℕ).bits)))
noncomputable def threePower (x : List Bool) : List Bool :=
  BoundedIteration.run triple (pairBits (x,pairBits (cap.word x,(1:ℕ).bits)))
end UnaryResources
namespace WordList
noncomputable def repeatWords_computes : PolyComputes repeatWords :=
  UnaryResources.copy_computes extractPrefix_computes
    (cons_computes discardPrefix_computes (const_computes []))
end WordList
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Pack5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
open scoped Matrix
namespace BinaryEllipsoidCut
open RationalMatrix

noncomputable def inflateInput (x : List Bool) : List Bool := pairBits (coefInflate x,cutWords x)
noncomputable def inflateWords : List Bool → List Bool := matrixScale ∘ inflateInput
end BinaryEllipsoidCut
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Pack6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
open scoped Matrix
namespace BinaryEllipsoidCut
noncomputable def gridInput (x : List Bool) : List Bool := pairBits (dim x,pairBits (precision x,inflateWords x))
noncomputable def shapeWords : List Bool → List Bool := BinaryEllipsoidGrid.run ∘ gridInput
end BinaryEllipsoidCut
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_OptionEncode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine

open WordOperations BinaryArithmetic RationalLinearFeasibility
namespace BinaryEllipsoidAdvance
open Ellipsoid RationalMatrix
open scoped Matrix

noncomputable def updated (x : List Bool) : List Bool :=
  pairBits (BinaryEllipsoidCut.shapeWords (cutInput x),BinaryEllipsoidCut.centerWords (cutInput x))
noncomputable def nextState (x : List Bool) : List Bool :=
  if found x=[] then stored x else if zeroDirection x then stored x else updated x
noncomputable def run (x : List Bool) : List Bool :=
  pairBits (dim x,pairBits (precision x,pairBits (rows x,nextState x)))
end BinaryEllipsoidAdvance
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Pack7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine

section
open WordOperations BinaryArithmetic RationalLinearFeasibility Ellipsoid
namespace BinaryEllipsoidInitial
open RationalMatrix WordList

noncomputable def dummy_computes : PolyComputes dummy :=
  (id_computes.pair (const_computes [])).comp repeatWords_computes
end BinaryEllipsoidInitial
end
open WordOperations BinaryArithmetic RationalLinearFeasibility Ellipsoid
namespace BinaryEllipsoidIteration
open RationalMatrix BinaryEllipsoidAdvance

noncomputable def boundCounter : PolynomialCounter storagePoly := PolynomialCounter.choose storagePoly
noncomputable def prepared (x : List Bool) : List Bool :=
  pairBits (extractPrefix x,pairBits (boundCounter.word x,discardPrefix (discardPrefix x)))
noncomputable def run : List Bool → List Bool := BoundedIteration.run BinaryEllipsoidAdvance.run ∘ prepared
end BinaryEllipsoidIteration
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Pack8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic RationalLinearFeasibility Ellipsoid
open UnaryResources
namespace BinaryWeakSolve
open RationalMatrix

noncomputable def dimBits : List Bool → List Bool := lengthBits ∘ nword
noncomputable def powerWords (x : List Bool) : List Bool := threePower (budgetWord x++[true])
noncomputable def cubeWords (x : List Bool) : List Bool := (value (dimBits x)*value (dimBits x)*value (dimBits x)).bits
noncomputable def gridWords (x : List Bool) : List Bool := (16*value (cubeWords x)*value (powerWords x)).bits
noncomputable def advanceInput (x : List Bool) : List Bool :=
  pairBits (dimBits x,pairBits (gridWords x,pairBits (rows x,pairBits (shapeWords x,centerWords x))))
noncomputable def prepared (x : List Bool) : List Bool := pairBits (budgetWord x,pairBits (radius x,advanceInput x))
noncomputable def iterated : List Bool → List Bool := BinaryEllipsoidIteration.run ∘ prepared
noncomputable def run : List Bool → List Bool := result ∘ iterated
end BinaryWeakSolve
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Pack9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic RationalLinearFeasibility Ellipsoid
namespace BinaryDecision
open UnaryResources NaturalArray

noncomputable def dim : List Bool → List Bool := lengthBits ∘ nword
noncomputable def count : List Bool → List Bool := lengthBits ∘ mword
noncomputable def rowFactor (x : List Bool) : List Bool :=
  (value (count x)+2*value (dim x)+2*(value (dim x)+1)).bits
noncomputable def base (x : List Bool) : List Bool := (value (rowFactor x)*(value (height x)*value (height x))).bits
noncomputable def power (x : List Bool) : List Bool := exponentiate (pairBits (nextDim x,base x))
noncomputable def gap (x : List Bool) : List Bool := (value (factorial x)*value (power x)).bits
noncomputable def doubledGap (x : List Bool) : List Bool := (2*value (gap x)).bits
noncomputable def epsilon (x : List Bool) : List Bool := BinaryRational.encode (1/(value (doubledGap x):ℚ))
noncomputable def precisionArg (x : List Bool) : List Bool := (value (doubledGap x)*value (height x)).bits
noncomputable def precision : List Bool → List Bool := unaryLog ∘ precisionArg
noncomputable def radius (x : List Bool) : List Bool := (value (dim x)*(value (bound x)+1)).bits
noncomputable def radiusPrecision : List Bool → List Bool := unaryLog ∘ radius
end BinaryDecision
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_BoundOp
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine

section
open WordOperations BinaryArithmetic RationalLinearFeasibility Ellipsoid
namespace BinaryDecision
open WordList RationalMatrix

noncomputable def relaxedWords (x : List Bool) : List Bool := mapWith relaxedOp (pairBits (epsilon x,boundedWords x))
noncomputable def prepared (x : List Bool) : List Bool :=
  pairBits (nword x,pairBits (precision x,pairBits (radiusPrecision x,pairBits (radius x,relaxedWords x))))
noncomputable def solved : List Bool → List Bool := BinaryWeakSolve.run ∘ prepared
noncomputable def run (x : List Bool) : List Bool := [!decide (solved x=[])]
end BinaryDecision
end
open WordOperations BinaryArithmetic
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_BoundedDecision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine

namespace BinaryBoundedDecision
open WordOperations BinaryArithmetic RationalLinearFeasibility Ellipsoid
open WordList RationalMatrix

noncomputable def run : List Bool → List Bool := BinaryDecision.run ∘ prepared
end BinaryBoundedDecision
namespace BinaryRationalDecision
open WordOperations BinaryArithmetic RationalLinearFeasibility Ellipsoid
open WordList

noncomputable def run : List Bool → List Bool := BinaryBoundedDecision.run ∘ prepared
end BinaryRationalDecision

open WordOperations
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_FaceSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic RationalLinearFeasibility Ellipsoid
namespace BinaryFace
open WordList
noncomputable def decision : List Bool → List Bool := BinaryRationalDecision.run ∘ decisionInput
noncomputable def op (x : List Bool) : List Bool := if (decision x).head?.getD false then proposed x else Find.accum x
noncomputable def run : List Bool → List Bool := Fold.run op (4*Polynomial.X+4)
end BinaryFace
namespace BinaryFinalFace
open WordList BinaryRationalDecision
noncomputable def run (x : List Bool) : List Bool := BinaryFace.run (Fold.pack (allRows x) (context x) [])
end BinaryFinalFace
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Rectangular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine

open WordOperations BinaryArithmetic RationalLinearFeasibility Ellipsoid Matrix
namespace BinaryExactSolve
open WordList BinaryRationalDecision RationalMatrix
noncomputable def transposed (x : List Bool) : List Bool :=
  Rectangular.transpose (pairBits (first x,coeffs (BinaryFinalFace.run x)))
noncomputable def gram (x : List Bool) : List Bool := mapWith rightRowOp (pairBits (transposed x,transposed x))
noncomputable def rhs (x : List Bool) : List Bool :=
  RationalMatrix.mulVec (pairBits (transposed x,bounds (BinaryFinalFace.run x)))
noncomputable def point (x : List Bool) : List Bool := solveWords (pairBits (gram x,rhs x))
noncomputable def run (x : List Bool) : List Bool :=
  if (BinaryRationalDecision.run x).head?.getD false then true::point x else []
end BinaryExactSolve
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Values
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace BinaryOpeningPayment
open WordList RationalLinearFeasibility

noncomputable def run (x : List Bool) : List Bool := BinaryRational.encode
  (BinaryRational.decode (field 4 x) -
    (BinaryArithmetic.value (UnaryResources.lengthBits (field 7 x)):ℚ)*BinaryRational.decode (field 5 x) -
    BinaryRational.decode (sumWords x))
end BinaryOpeningPayment
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Basic2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace BinaryOpeningConstant
open WordList RationalLinearFeasibility

noncomputable def constant (x : List Bool) : ℚ :=
  if tag x=0 then if active 1 x then BinaryOpeningPayment.paramZ x else 0
  else if tag x=1 then if active 1 x then -((1+BinaryOpeningPayment.paramV x*BinaryOpeningPayment.paramV x)*BinaryOpeningPayment.paramZ x) else 0
  else if tag x=2 then if active 1 x then -(BinaryOpeningPayment.scale x*distance 2 1 x) else 0
  else if tag x=3 then if active 1 x then if near x then 0 else -BinaryOpeningPayment.paramZ x else 0
  else if tag x=4 then BinaryRational.decode (BinaryOpeningPayment.run (extractPrefix x))
  else if tag x=6 then if active 3 x then
    if active 1 x then -distance 2 1 x else -(2*distance 2 1 x+distance 2 3 x) else 0
  else if tag x=7 then if active 1 x then -BinaryRational.decode (BinaryOpeningPayment.itemField 4 x) else 0
  else 0

end BinaryOpeningConstant
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_RowInput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRawOpening
open WordOperations BinaryArithmetic WordList RationalLinearFeasibility
open BinaryOpeningPayment BinaryOpeningEnumeration
noncomputable def rowWord (x : List Bool) : List Bool :=
  pairBits (rowCoefficients x,BinaryRational.encode (-BinaryOpeningConstant.constant x))
noncomputable def rows (x : List Bool) : List Bool := mapWith rowWord (pairBits (x,kinds x))
noncomputable def prepared (x : List Bool) : List Bool :=
  pairBits (Count.run (columns x),pairBits (Count.run (kinds x),pairBits ((⌈bound x⌉₊).bits,rows x)))

noncomputable def run : List Bool → List Bool := BinaryExactSolve.run ∘ prepared
end MetricKMedianRecovery.BitMachine.BinaryRawOpening

namespace MetricKMedianRecovery.BitMachine.BinaryPhaseFirst
open WordOperations BinaryArithmetic WordList
open BinaryOpeningPayment

noncomputable def answer : List Bool → List Bool := BinaryRawOpening.run ∘ query
noncomputable def eligible (x : List Bool) : Bool :=
  if contains (pairBits (discardPrefix x,itemField 8 x)) then
    if contains (pairBits (discardPrefix x,itemField 1 x)) then false else decide (answer x≠[]) else false

noncomputable def chosen : List Bool → List Bool := Find.run eligible
noncomputable def chosenQuery (x : List Bool) : List Bool := pairBits (extractPrefix x,(chosen x).tail)

noncomputable def bids (x : List Bool) : List Bool :=
  mapWith (Lookup.run ∘ RationalMatrix.swapWords) (pairBits ((answer x).tail,BinaryOpeningEnumeration.clients (extractPrefix x)))
noncomputable def run (x : List Bool) : List Bool :=
  if chosen x=[] then [] else true::pairBits ((chosen x).tail,bids (chosenQuery x))
end MetricKMedianRecovery.BitMachine.BinaryPhaseFirst

end OAI
end


