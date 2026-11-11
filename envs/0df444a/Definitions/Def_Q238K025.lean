-- Prove2me | Definitions.Def_Q238K025
-- name    : Q238K025
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T23:19:20.5911+00:00
-- url     : https://prove2.me/theorems/ce0a6e8b-d3ed-467e-b07d-477b24d9f2b9
-- title:
--   Definitions bundle Q238K025 of the split of OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 121 declarations of OpenAI's Lean: 84 definitions and 37 theorems. The definitions and types are `OAI.MetricKMedianRecovery.BitMachine.BinaryArithmetic.Multiplication.add_cycle`, `OAI.MetricKMedianRecovery.BitMachine.BinaryArithmetic.Multiplication.cfg`, `OAI.MetricKMedianRecovery.BitMachine.BinaryArithmetic.Multiplication.clear_outputs`, `OAI.MetricKMedianRecovery.BitMachine.BinaryArithmetic.Multiplication.done`, `OAI.MetricKMedianRecovery.BitMachine.BinaryArithmetic.Multiplication.parse_phase`, `OAI.MetricKMedianRecovery.BitMachine.BinaryArithmetic.Multiplication.process_outputs`, `OAI.MetricKMedianRecovery.BitMachine.BinaryArithmetic.Multiplication.raw_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryArithmetic.Multiplication.resta_outputs`, `OAI.MetricKMedianRecovery.BitMachine.BinaryArithmetic.Multiplication.resty_outputs`, `OAI.MetricKMedianRecovery.BitMachine.BinaryArithmetic.Multiplication.sum_outputs`, `OAI.MetricKMedianRecovery.BitMachine.BinaryArithmetic.multiply_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryArithmetic.normalize_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryAssignmentWeight.count`, `OAI.MetricKMedianRecovery.BitMachine.BinaryAssignmentWeight.identities`, `OAI.MetricKMedianRecovery.BitMachine.BinaryAssignmentWeight.identity`, `OAI.MetricKMedianRecovery.BitMachine.BinaryAssignmentWeight.run`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueCell.old`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueCell.op`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueOutput.destination`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueOutput.pick`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueOutput.run`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueOutput.source`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueRecords.op`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueRecords.run`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueRecords.scaled`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueRecords.weight`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchBalls.ball`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchBalls.balls`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchBalls.run`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchCheck.badBalls`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchCheck.badRadii`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchCheck.outside`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchContext.classOf`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchContext.copyData`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchContext.locations`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchContext.origins`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchContext.remaining`, `OAI.MetricKMedianRecovery.BitMachine.BinaryClassFilter.run`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCopyTables.entry`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCopyTables.locations` and 44 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedianRecovery_Branching_BlueItem`, `KMedianRecovery_Branching_BlueLookup`, `KMedianRecovery_Branching_BlueProgram`, `KMedianRecovery_Branching_BranchBalls`, `KMedianRecovery_Branching_BranchContext`, `KMedianRecovery_Branching_BranchPhysical`, `KMedianRecovery_Branching_BranchWeights`, `KMedianRecovery_Branching_CopyComputes`, `KMedianRecovery_Branching_CopyGround`, `KMedianRecovery_Encoding_ColorLabelMachine`, `KMedianRecovery_Encoding_DivNatWords`, `KMedianRecovery_Encoding_Encode`, `KMedianRecovery_Encoding_LabelMember`, `KMedianRecovery_Encoding_RationalSort`, `KMedianRecovery_Encoding_StateBits`, `KMedianRecovery_Encoding_Words`, `KMedianRecovery_Machines_CappedFold`, `KMedianRecovery_Machines_FiniteMachine`, `KMedianRecovery_Machines_SubProgram`, `KMedianRecovery_Recovery_ClassFilter`, `KMedianRecovery_Recovery_DecisionOps`, `KMedianRecovery_Recovery_DigitBit`, `KMedianRecovery_Recovery_FilterItem`, `KMedianRecovery_Recovery_FiniteContext`, `KMedianRecovery_Recovery_LeftNum`, `KMedianRecovery_Recovery_Mul`, `KMedianRecovery_Recovery_NumAbs`, `KMedianRecovery_Recovery_Pack`, `KMedianRecovery_Recovery_Pack2`, `KMedianRecovery_Recovery_ProcessOutputs`, `KMedianRecovery_Sampling_SamplingReference`, `KMedianRecovery_Sampling_SamplingStateMachine`.
--
--   **Imports.** It imports the published bundle `Def_KMedianRefinedRecovery`; the bundles `Q238K017`, `Q238K018`, `Q238K019` and `Q238K020` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q238K028`, `Q238K029`, `Q238K030` and `Q238K031`; the statements `OAI.MetricKMedianRecovery.BitMachine.BinaryAssignmentWeight.identities_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueCell.op_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchCheck.badBalls_nil_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchContext.copyData_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchContext.locations_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchContext.origins_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCopyTables.locations_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFinSet.diff_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.selected_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseUpdate.updatedBudget_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinarySamplingOracle.reference_pair_s238` and `OAI_MetricKMedianRecovery_BitMachine_BinarySanitizedBest_run_pack_s238`; the proofs of `OAI.MetricKMedianRecovery.BitMachine.BinaryAssignmentWeight.identities_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueCell.op_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchCheck.badBalls_nil_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchContext.copyData_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchContext.locations_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchContext.origins_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCopyTables.locations_pack_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryDecision_run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFinSet.diff_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.selected_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseUpdate.updatedBudget_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinarySamplingOracle.reference_pair_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinarySanitizedBest_run_pack_s238` and `OAI.MetricKMedianRecovery.BitMachine.RationalMatrix.solveWords_bird_s238`.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_KMedianRefinedRecovery
import Definitions.Def_Q238K017
import Definitions.Def_Q238K018
import Definitions.Def_Q238K019
import Definitions.Def_Q238K020

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Mul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open Turing Turing.TM2 StateTransition

namespace BinaryArithmetic

namespace Multiplication

@[simp] lemma mStacks_0 (a b c d e : List Bool) : mStacks a b c d e 0=a := rfl
@[simp] lemma mStacks_1 (a b c d e : List Bool) : mStacks a b c d e 1=b := rfl
@[simp] lemma mStacks_2 (a b c d e : List Bool) : mStacks a b c d e 2=c := rfl
@[simp] lemma mStacks_3 (a b c d e : List Bool) : mStacks a b c d e 3=d := rfl
@[simp] lemma mStacks_4 (a b c d e : List Bool) : mStacks a b c d e 4=e := rfl

lemma upd0 (a b c d e t : List Bool) :
    Function.update (mStacks a b c d e) 0 t=mStacks t b c d e := by
  funext i; fin_cases i <;> simp [mStacks]
lemma upd1 (a b c d e t : List Bool) :
    Function.update (mStacks a b c d e) 1 t=mStacks a t c d e := by
  funext i; fin_cases i <;> simp [mStacks]
lemma upd2 (a b c d e t : List Bool) :
    Function.update (mStacks a b c d e) 2 t=mStacks a b t d e := by
  funext i; fin_cases i <;> simp [mStacks]
lemma upd3 (a b c d e t : List Bool) :
    Function.update (mStacks a b c d e) 3 t=mStacks a b c t e := by
  funext i; fin_cases i <;> simp [mStacks]
lemma upd4 (a b c d e t : List Bool) :
    Function.update (mStacks a b c d e) 4 t=mStacks a b c d t := by
  funext i; fin_cases i <;> simp [mStacks]

def cfg (l : Fin 6) (c : Bool) (a b d e f : List Bool) : program.machine.Cfg :=
  ⟨some l,(c,none,none),mStacks a b d e f⟩
def done (ys : List Bool) : program.machine.Cfg :=
  ⟨none,(false,none,none),mStacks [] [] [] ys []⟩

lemma initial (xs : List Bool) : initList program.machine xs=cfg 0 false xs [] [] [] [] := by
  rw [initList_bool]; congr 1
  funext i; fin_cases i <;> simp [program,mStacks]
lemma final (xs : List Bool) : haltList program.machine xs=done xs := by
  rw [haltList_bool]; congr 1
  funext i; fin_cases i <;> simp [program,mStacks]

lemma parse_nil (bs : List Bool) :
    program.machine.step (cfg 0 false [] bs [] [] [])=some (cfg 1 false [] bs [] [] []) := by
  simp [FinTM2.step,cfg,program,TM2.step,TM2.stepAux,upd0]; rfl
lemma parse_one (bs : List Bool) :
    program.machine.step (cfg 0 false [true] bs [] [] [])=some (cfg 1 false [] bs [] [] []) := by
  simp [FinTM2.step,cfg,program,TM2.step,TM2.stepAux,upd0]; rfl
lemma parse_false (as bs : List Bool) :
    program.machine.step (cfg 0 false (false::as) bs [] [] [])=some (cfg 1 false as bs [] [] []) := by
  simp [FinTM2.step,cfg,program,TM2.step,TM2.stepAux,upd0]; rfl
lemma parse_true (b : Bool) (as bs : List Bool) :
    program.machine.step (cfg 0 false (true::b::as) bs [] [] [])=some (cfg 0 false as (b::bs) [] [] []) := by
  simp [FinTM2.step,cfg,program,TM2.step,TM2.stepAux,upd0,upd1]; rfl

lemma process_nil (ys acc : List Bool) :
    program.machine.step (cfg 1 false ys [] [] acc [])=some (cfg 5 false ys [] [] acc []) := by
  simp [FinTM2.step,cfg,program,TM2.step,TM2.stepAux,upd1]; rfl
lemma process_false (xs ys acc : List Bool) :
    program.machine.step (cfg 1 false ys (false::xs) [] acc [])=some (cfg 1 false ys xs [] (false::acc) []) := by
  simp [FinTM2.step,cfg,program,TM2.step,TM2.stepAux,upd1,upd3]; rfl
lemma process_true (xs ys acc : List Bool) :
    program.machine.step (cfg 1 false ys (true::xs) [] acc [])=some (cfg 2 false ys xs [] (false::acc) []) := by
  simp [FinTM2.step,cfg,program,TM2.step,TM2.stepAux,upd1,upd3]; rfl

lemma sum_nil (c : Bool) (bs ds fs : List Bool) :
    program.machine.step (cfg 2 c [] bs ds [] fs)=
      some (cfg 3 false [] bs ds [] ((if c then [true] else [])++fs)) := by
  cases c <;> simp [FinTM2.step,cfg,program,TM2.step,TM2.stepAux,upd0,upd3,upd4]
  all_goals rfl
lemma sum_left (c x : Bool) (as bs ds fs : List Bool) :
    program.machine.step (cfg 2 c (x::as) bs ds [] fs)=
      some (cfg 2 (carryBit c x false) as bs (x::ds) [] (sumBit c x false::fs)) := by
  simp [FinTM2.step,cfg,program,TM2.step,TM2.stepAux,upd0,upd3,upd2,upd4]; rfl
lemma sum_right (c y : Bool) (bs ds es fs : List Bool) :
    program.machine.step (cfg 2 c [] bs ds (y::es) fs)=
      some (cfg 2 (carryBit c false y) [] bs ds es (sumBit c false y::fs)) := by
  simp [FinTM2.step,cfg,program,TM2.step,TM2.stepAux,upd0,upd3,upd4]; rfl
lemma sum_both (c x y : Bool) (as bs ds es fs : List Bool) :
    program.machine.step (cfg 2 c (x::as) bs ds (y::es) fs)=
      some (cfg 2 (carryBit c x y) as bs (x::ds) es (sumBit c x y::fs)) := by
  simp [FinTM2.step,cfg,program,TM2.step,TM2.stepAux,upd0,upd3,upd2,upd4]; rfl

lemma resty_nil (a b e : List Bool) :
    program.machine.step (cfg 3 false a b [] [] e)=some (cfg 4 false a b [] [] e) := by
  simp [FinTM2.step,cfg,program,TM2.step,TM2.stepAux,upd2]; rfl
lemma resty_cons (t : Bool) (a b c e : List Bool) :
    program.machine.step (cfg 3 false a b (t::c) [] e)=some (cfg 3 false (t::a) b c [] e) := by
  simp [FinTM2.step,cfg,program,TM2.step,TM2.stepAux,upd2,upd0]; rfl
lemma resta_nil (a b d : List Bool) :
    program.machine.step (cfg 4 false a b [] d [])=some (cfg 1 false a b [] d []) := by
  simp [FinTM2.step,cfg,program,TM2.step,TM2.stepAux,upd4]; rfl
lemma resta_cons (t : Bool) (a b d e : List Bool) :
    program.machine.step (cfg 4 false a b [] d (t::e))=some (cfg 4 false a b [] (t::d) e) := by
  simp [FinTM2.step,cfg,program,TM2.step,TM2.stepAux,upd4,upd3]; rfl
lemma clear_nil (acc : List Bool) :
    program.machine.step (cfg 5 false [] [] [] acc [])=some (done acc) := by
  simp [FinTM2.step,cfg,done,program,TM2.step,TM2.stepAux,upd0]; rfl
lemma clear_cons (t : Bool) (ys acc : List Bool) :
    program.machine.step (cfg 5 false (t::ys) [] [] acc [])=some (cfg 5 false ys [] [] acc []) := by
  simp [FinTM2.step,cfg,program,TM2.step,TM2.stepAux,upd0]; rfl

noncomputable def sum_outputs (c : Bool) (as bs ds es fs : List Bool) :
    EvalsToInTime program.machine.step (cfg 2 c as bs ds es fs)
      (some (cfg 3 false [] bs (as.reverse++ds) [] ((add c as es).reverse++fs)))
      (as.length+es.length+1) := by
  induction as generalizing c es ds fs with
  | nil =>
    induction es generalizing c fs with
    | nil =>
      cases c with
      | false => simpa [add] using one_step (sum_nil false bs ds fs)
      | true => simpa [add] using one_step (sum_nil true bs ds fs)
    | cons y es ih =>
      have hh := step_then (sum_right c y bs ds es fs) (ih (carryBit c false y) (sumBit c false y::fs))
      simpa only [add,List.reverse_cons,List.append_assoc,List.singleton_append,List.length_cons,List.length_nil,Nat.zero_add]
        using hh
  | cons x as ih =>
    cases es with
    | nil =>
      have hh := step_then (sum_left c x as bs ds fs) (ih (carryBit c x false) (x::ds) [] (sumBit c x false::fs))
      simpa only [add,List.reverse_cons,List.append_assoc,List.singleton_append,List.length_cons,List.length_nil,Nat.add_zero]
        using hh
    | cons y es =>
      have hh := step_then (sum_both c x y as bs ds es fs)
        (ih (carryBit c x y) (x::ds) es (sumBit c x y::fs))
      simp only [add,List.reverse_cons,List.append_assoc,List.singleton_append] at ⊢
      exact time_mono hh (by simp; omega)

noncomputable def resta_outputs (a b d e : List Bool) :
    EvalsToInTime program.machine.step (cfg 4 false a b [] d e)
      (some (cfg 1 false a b [] (e.reverse++d) [])) (e.length+1) := by
  induction e generalizing d with
  | nil => exact one_step (resta_nil a b d)
  | cons t e ih =>
    simpa only [List.reverse_cons,List.append_assoc,List.singleton_append,List.length_cons] using
      step_then (resta_cons t a b d e) (ih (t::d))

noncomputable def resty_outputs (a b c e : List Bool) :
    EvalsToInTime program.machine.step (cfg 3 false a b c [] e)
      (some (cfg 1 false (c.reverse++a) b [] e.reverse [])) (c.length+e.length+2) := by
  induction c generalizing a with
  | nil =>
    simpa only [List.reverse_nil,List.nil_append,List.length_nil,List.append_nil,Nat.zero_add,Nat.add_assoc] using
      step_then (resty_nil a b e) (resta_outputs a b [] e)
  | cons t c ih =>
    have hh := step_then (resty_cons t a b c e) (ih (t::a))
    simpa only [List.reverse_cons,List.append_assoc,List.singleton_append,List.length_cons,Nat.add_right_comm] using hh

noncomputable def add_cycle (xs ys acc : List Bool) :
    EvalsToInTime program.machine.step (cfg 2 false ys xs [] acc [])
      (some (cfg 1 false ys xs [] (add false ys acc) []))
      (2*ys.length+acc.length+(add false ys acc).length+3) := by
  have h1 := sum_outputs false ys xs [] acc []
  have h2 := resty_outputs [] xs ys.reverse (add false ys acc).reverse
  simp only [List.append_nil] at h1
  simp only [List.reverse_reverse,List.append_nil,List.length_reverse] at h2
  have hh := MetricKMedianRecovery.BitMachine.eval_trans h1 h2
  exact time_mono hh (by omega)

noncomputable def clear_outputs (ys acc : List Bool) :
    EvalsToInTime program.machine.step (cfg 5 false ys [] [] acc []) (some (done acc)) (ys.length+1) := by
  induction ys with
  | nil => exact one_step (clear_nil acc)
  | cons t ys ih => exact step_then (clear_cons t ys acc) ih

end Multiplication
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

lemma clear_nil : subProgram.machine.step (cfg 3 false [] [] [])=some (done []) := by
  simp [FinTM2.step,cfg,done,subProgram,TM2.step,TM2.stepAux,update_one]
  rfl

lemma sum_nil_false (zs : List Bool) :
    subProgram.machine.step (cfg 2 false [] zs [])=some (done zs) := by
  simp [FinTM2.step,cfg,done,subProgram,TM2.step,TM2.stepAux,update_zero,update_two]
  rfl
lemma sum_nil_true (zs : List Bool) :
    subProgram.machine.step (cfg 2 true [] zs [])=some (cfg 3 false [] zs []) := by
  simp [FinTM2.step,cfg,subProgram,TM2.step,TM2.stepAux,update_zero,update_two]
  rfl
lemma sum_cons_nil (c x : Bool) (xs zs : List Bool) :
    subProgram.machine.step (cfg 2 c [] zs (x::xs))=
      some (cfg 2 (borrowBit c x false) [] (sumBit c x false::zs) xs) := by
  simp [FinTM2.step,cfg,subProgram,TM2.step,TM2.stepAux,update_zero,update_two,update_one]
  rfl
lemma sum_nil_cons (c y : Bool) (ys zs : List Bool) :
    subProgram.machine.step (cfg 2 c (y::ys) zs [])=
      some (cfg 2 (borrowBit c false y) ys (sumBit c false y::zs) []) := by
  simp [FinTM2.step,cfg,subProgram,TM2.step,TM2.stepAux,update_zero,update_two,update_one]
  rfl
lemma sum_cons_cons (c x y : Bool) (xs ys zs : List Bool) :
    subProgram.machine.step (cfg 2 c (y::ys) zs (x::xs))=
      some (cfg 2 (borrowBit c x y) ys (sumBit c x y::zs) xs) := by
  simp [FinTM2.step,cfg,subProgram,TM2.step,TM2.stepAux,update_zero,update_two,update_one]
  rfl

end BinarySubtraction
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Pack
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open Turing
namespace BinaryDivision
open BinaryArithmetic BinarySubtraction WordOperations

noncomputable def pack_computes {d y q r : List Bool → List Bool}
    (a : Bool) (hd : PolyComputes d) (hy : PolyComputes y)
    (hq : PolyComputes q) (hr : PolyComputes r) :
    PolyComputes (fun x=>pack a (d x) (y x) (q x) (r x)) := by
  exact (const_computes [a]).append (hd.pair (hy.pair (hq.pair hr)))

end BinaryDivision
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_DigitBit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open Turing
namespace BinaryDivision
open BinaryArithmetic BinarySubtraction WordOperations

noncomputable def normalize_computes : PolyComputes BinaryArithmetic.normalize :=
  (reverse_computes.comp trim_computes).comp reverse_computes

noncomputable def zeroTest_computes : PolyComputes (fun x=>[decide (value x=0)]) := by
  have h := normalize_computes.comp isEmpty_computes
  simpa only [Function.comp_def,normalize_eq_bits,bits_eq_nil] using h

end BinaryDivision
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Pack2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open Turing
namespace BinaryGCD
open BinaryArithmetic BinarySubtraction WordOperations

noncomputable def pack_computes {f g : List Bool → List Bool} (b : Bool)
    (hf : PolyComputes f) (hg : PolyComputes g) : PolyComputes (fun x=>pack b (f x) (g x)) :=
  (const_computes [b]).append (hf.pair hg)

end BinaryGCD
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_ProcessOutputs
attribute [-simp] _root_.OAI.MetricKMedianRecovery.BitMachine.discardPrefix_pairBits _root_.OAI.MetricKMedianRecovery.BitMachine.extractPrefix_pairBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine

section
open Turing Turing.TM2 StateTransition
namespace BinaryArithmetic.Multiplication

noncomputable def process_outputs (xs ys acc : List Bool) (B : ℕ)
    (hB : acc.length+xs.length*(ys.length+2)≤B) :
    EvalsToInTime program.machine.step (cfg 1 false ys xs [] acc [])
      (some (done (mulFrom xs ys acc))) (10*(xs.length+1)*(B+ys.length+2)) := by
  induction xs generalizing acc with
  | nil =>
    have hh := step_then (process_nil ys acc) (clear_outputs ys acc)
    exact time_mono hh (by simp only [List.length_nil]; omega)
  | cons b xs ih =>
    have hacc : acc.length≤B := by omega
    cases b with
    | false =>
      have hB' : (false::acc).length+xs.length*(ys.length+2)≤B := by
        simp only [List.length_cons,Nat.add_mul] at hB ⊢
        omega
      have hh := step_then (process_false xs ys acc) (ih (false::acc) hB')
      change EvalsToInTime program.machine.step _ (some (done (mulFrom xs ys (false::acc)))) _
      exact time_mono hh (by simp only [List.length_cons] <;> nlinarith)
    | true =>
      have hl := add_length false ys (false::acc)
      have hB' : (add false ys (false::acc)).length+xs.length*(ys.length+2)≤B := by
        simp only [List.length_cons,Nat.add_mul] at hB hl ⊢
        omega
      have hh := eval_trans (add_cycle xs ys (false::acc)) (ih _ hB')
      have hh' := step_then (process_true xs ys acc) hh
      change EvalsToInTime program.machine.step _
        (some (done (mulFrom xs ys (add false ys (false::acc))))) _
      exact time_mono hh' (by simp only [List.length_cons] at hl ⊢ <;> nlinarith)

noncomputable def parse_phase (xs bs : List Bool) :
    EvalsToInTime program.machine.step (cfg 0 false xs bs [] [] [])
      (some (cfg 1 false (discardPrefix xs) ((extractPrefix xs).reverse++bs) [] [] [])) (xs.length+1) := by
  induction xs using List.twoStepInduction generalizing bs with
  | nil => exact one_step (parse_nil bs)
  | singleton b =>
    cases b with
    | false => simpa only [extractPrefix,discardPrefix,List.reverse_nil,List.nil_append,List.length_cons,List.length_nil] using
        time_mono (one_step (parse_false [] bs)) (by decide : 1≤2)
    | true => simpa only [extractPrefix,discardPrefix,List.reverse_nil,List.nil_append,List.length_cons,List.length_nil] using
        time_mono (one_step (parse_one bs)) (by decide : 1≤2)
  | cons_cons b c xs ih _ =>
    cases b with
    | false => simpa only [extractPrefix,discardPrefix,List.reverse_nil,List.nil_append] using
        time_mono (one_step (parse_false (c::xs) bs)) (by simp : 1≤(false::c::xs).length+1)
    | true =>
      have hh := step_then (parse_true c xs bs) (ih (c::bs))
      simp only [extractPrefix,discardPrefix,List.reverse_cons,List.append_assoc,List.singleton_append] at ⊢
      exact time_mono hh (by simp)

noncomputable def raw_computes : PolyComputes (fun xs =>
    mulFrom (extractPrefix xs).reverse (discardPrefix xs) []) where
  program := program
  time := 30*(Polynomial.X+1)^3
  outputs xs := by
    let n := xs.length
    let x := (extractPrefix xs).reverse
    let y := discardPrefix xs
    have hx : x.length≤n := by simpa only [x,List.length_reverse] using (projections_length xs).1
    have hy : y.length≤n := (projections_length xs).2
    have h1 := parse_phase xs []
    simp only [List.append_nil] at h1
    have h2 := process_outputs x y [] (n*(n+2)) (by
      simp only [List.length_nil,Nat.zero_add]
      exact Nat.mul_le_mul hx (Nat.add_le_add_right hy 2))
    have hh := eval_trans h1 h2
    change TM2OutputsInTime program.machine xs
      (some (mulFrom x y [])) _
    simp only [TM2OutputsInTime,Option.map_some,initial,final,Polynomial.eval_mul,Polynomial.eval_ofNat,
      Polynomial.eval_pow,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one]
    apply time_mono hh
    have htime : 10*(x.length+1)*(n*(n+2)+y.length+2)≤
        10*(n+1)*(n*(n+2)+n+2) := by gcongr
    change 10*(x.length+1)*(n*(n+2)+y.length+2)+(n+1)≤30*(n+1)^3
    calc
      _ ≤ 10*(n+1)*(n*(n+2)+n+2)+(n+1) := Nat.add_le_add_right htime _
      _ ≤ _ := by nlinarith [Nat.zero_le (n^3)]

end BinaryArithmetic.Multiplication
namespace BinaryArithmetic

noncomputable def normalize_computes : PolyComputes normalize :=
  (reverse_computes.comp trim_computes).comp reverse_computes

noncomputable def multiply_computes : PolyComputes (fun xs =>
    normalize (mulFrom (extractPrefix xs).reverse (discardPrefix xs) [])) :=
  Multiplication.raw_computes.comp normalize_computes

end BinaryArithmetic
end
open WordOperations BinaryArithmetic
namespace NatOps

noncomputable def mul {f g : List Bool → List Bool} (hf : PolyComputes f) (hg : PolyComputes g) :
    PolyComputes (fun x=>(value (f x)*value (g x)).bits) := by
  have hh := (hf.pair hg).comp multiply_computes
  simpa only [Function.comp_def,pairBits,extractPrefix_pair,discardPrefix_pair,normalize_mulFrom] using hh

noncomputable def zero {f : List Bool → List Bool} (hf : PolyComputes f) :
    PolyComputes (fun x=>[decide (value (f x)=0)]) := by
  have hh := hf.comp BinaryDivision.zeroTest_computes
  exact hh

end NatOps
namespace Signed

noncomputable def pack_computes {s : List Bool → Bool} {f : List Bool → List Bool}
    (hs : PolyComputes (fun x=>[s x])) (hf : PolyComputes f) :
    PolyComputes (fun x=>pack (s x) (f x)) := by
  have hp := hs.append (hf.comp normalize_computes)
  have hh := (NatOps.zero hf).cond (const_computes [false]) hp
  simpa only [pack,Function.comp_def,List.singleton_append,decide_eq_true_eq] using hh

noncomputable def cast_computes {f : List Bool → List Bool} (hf : PolyComputes f) :
    PolyComputes (fun x=>encode (value (f x):ℤ)) := by
  have hh := pack_computes (const_computes [false]) (hf.comp normalize_computes)
  simpa only [Function.comp_def,normalize_eq_bits,pack_bits,signed,Bool.false_eq_true,ite_false, if_false] using hh

end Signed
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_LeftNum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace BinaryRational

lemma invWords_encode (x : ℚ) : invWords (encode x)=encode x⁻¹ := by
  simp only [invWords,Function.comp_apply,reduce_correct,rawInv,numerator_encode,denominator_encode,
    Signed.encode_mag,Signed.sign_encode,value_bits,
    Signed.pack_bits,decode_pair]
  by_cases hz : x.num=0
  · have hx : x=0 := Rat.num_eq_zero.mp hz
    subst x
    simp only [Rat.num_zero,Int.natAbs_zero,Rat.mkRat_zero,inv_zero]
  · rw [signed_sign x.num x.den hz]
    exact congrArg encode (by simpa only [Rat.num_inv,Rat.den_inv,hz,ite_false, if_false] using Rat.mkRat_self x⁻¹)

end BinaryRational
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_Encode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace IntegerArray

noncomputable def prefixEmpty_computes : PolyComputes (fun x=>pairBits ([],x)) :=
  PolyComputes.pair (f:=fun _=>[]) (g:=id) (const_computes []) id_computes
end IntegerArray
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
noncomputable def triple_computes : PolyComputes triple := by
  change PolyComputes (fun x=>(3*value x).bits)
  have hh := NatOps.mul (const_computes (3:ℕ).bits) id_computes
  simpa only [triple,Function.comp_def,id_eq,value_bits] using hh
end UnaryResources
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_DivNatWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace BinaryRational

noncomputable def castIntWords_computes : PolyComputes castIntWords := id_computes.pair (const_computes (Nat.bits 1))

end BinaryRational
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_NumAbs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
open WordOperations BinaryArithmetic
open scoped Matrix
namespace BinaryRational

def secondInverse : List Bool → List Bool := invWords ∘ discardPrefix
def divInput (x : List Bool) : List Bool := pairBits (extractPrefix x,secondInverse x)
def divWords : List Bool → List Bool := mulWords ∘ divInput
lemma divWords_pair (a b : ℚ) : divWords (pairBits (encode a,encode b))=encode (a/b) := by
  simp only [divWords,Function.comp_apply,divInput,secondInverse,extractPrefix_pairBits,discardPrefix_pairBits,
    invWords_encode,mulWords_pair,div_eq_mul_inv]
noncomputable def natWords_computes : PolyComputes natWords :=
  (Signed.cast_computes id_computes).comp castIntWords_computes
end BinaryRational
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_Words
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace RatOps
open BinaryRational
noncomputable def nat {f : List Bool → List Bool} (hf : PolyComputes f) :
    PolyComputes (fun x=>encode (value (f x):ℚ)) := by
  have hh := hf.comp BinaryRational.natWords_computes
  simpa only [Function.comp_def,BinaryRational.natWords,BinaryRational.castIntWords_encode,Int.cast_natCast] using hh
noncomputable def const (r : ℚ) : PolyComputes (fun _ : List Bool=>encode r) := const_computes (encode r)
end RatOps
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_CappedFold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations
noncomputable def RepeatedAppend.fixed_computes (n : ℕ) : PolyComputes (RepeatedAppend.copies n) := by
  induction n with
  | zero => exact const_computes []
  | succ n ih => exact ih.append id_computes
end MetricKMedianRecovery.BitMachine

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
namespace BinaryFiniteInsert
open WordList BinaryPhaseFirst EffectiveOpenability
noncomputable def keep (x : List Bool) : Bool :=
  if natEq (pairBits (new x,discardPrefix x)) then true else contains (pairBits (discardPrefix x,old x))
noncomputable def run : List Bool → List Bool := filterWith keep
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

noncomputable def opened (x : List Bool) : List Bool := BinaryFiniteInsert.run
  (pairBits (pairBits (ctxField 1 x,newFacility x),allFacilities (context x)))
noncomputable def updatedContext (x : List Bool) : List Bool := encode [ctxField 0 x,opened x,ctxField 2 x,
  ctxField 3 x,ctxField 4 x,ctxField 5 x,ctxField 6 x,ctxField 7 x,ctxField 8 x]

noncomputable def active (x : List Bool) : Bool := BinaryOpeningPayment.active (pairBits (context (extractPrefix x),discardPrefix x))
noncomputable def budgetItem (x : List Bool) : List Bool :=
  if active x then Lookup.run (pairBits (discardPrefix x,newBudget (extractPrefix x)))
  else Lookup.run (pairBits (discardPrefix x,oldBudget (extractPrefix x)))
noncomputable def updatedBudget (x : List Bool) : List Bool :=
  mapWith budgetItem (pairBits (x,BinaryOpeningEnumeration.clients (context x)))
noncomputable def run (x : List Bool) : List Bool := pairBits (updatedContext x,updatedBudget x)
end MetricKMedianRecovery.BitMachine.BinaryPhaseUpdate

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_DecisionOps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
noncomputable def PolyComputes.not {p : List Bool → Bool} (hp : PolyComputes (fun x=>[p x])) :
    PolyComputes (fun x=>[!p x]) := by
  have h:=hp.cond (const_computes [false]) (const_computes [true])
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  cases p x <;> rfl
noncomputable def PolyComputes.and {p q : List Bool → Bool}
    (hp : PolyComputes (fun x=>[p x])) (hq : PolyComputes (fun x=>[q x])) :
    PolyComputes (fun x=>[p x && q x]) := by
  have h:=hp.cond hq (const_computes [false])
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  cases p x <;> rfl
noncomputable def PolyComputes.or {p q : List Bool → Bool}
    (hp : PolyComputes (fun x=>[p x])) (hq : PolyComputes (fun x=>[q x])) :
    PolyComputes (fun x=>[p x || q x]) := by
  have h:=hp.cond (const_computes [true]) hq
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  cases p x <;> rfl
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_LabelMember
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryLabelSelect
open Classical
open WordOperations BinaryArithmetic WordList RationalLeaves EffectiveOpenability

noncomputable def run (x : List Bool) : List Bool :=
  filterWith test (pairBits (x,Indices.run (extractPrefix x)))
end MetricKMedianRecovery.BitMachine.BinaryLabelSelect

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

noncomputable def selected (k : ℕ) (x : List Bool) : List Bool :=
  BinaryLabelSelect.run (pairBits (alphabet x,field k x))

noncomputable def matrix (x : List Bool) : List Bool :=
  BinaryLabelMatrix.run (pairBits (pairBits (field 0 x,field 1 x),alphabet x))
attribute [local irreducible] BinaryLabelMatrix.run

noncomputable def run (x : List Bool) : List Bool := encode
  [matrix x,selected 3 x,field 5 x,field 6 x,field 7 x,BinaryRational.encode 0,[],field 1 x,selected 2 x]
attribute [local irreducible] matrix selected
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
open BinaryOpeningPayment (field )
open BinaryFiniteContext (labels)

noncomputable def initial (x : List Bool) : List Bool := BinaryPhaseCount.start
  (pairBits (BinaryFiniteContext.run x,field 6 x))
end MetricKMedianRecovery.BitMachine.BinaryFiniteMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_RationalSort
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryNatSet
open WordOperations WordList BinaryArithmetic
noncomputable def sort : List Bool→List Bool := Sort.run lt
noncomputable def union (x : List Bool) : List Bool := sort (extractPrefix x++discardPrefix x)
noncomputable def contains : List Bool→Bool := BinaryPhaseFirst.contains
noncomputable def absent (x : List Bool) : Bool := !contains (pairBits (discardPrefix x,extractPrefix x))
noncomputable def diff (x : List Bool) : List Bool := sort (filterWith absent (pairBits (discardPrefix x,extractPrefix x)))
end MetricKMedianRecovery.BitMachine.BinaryNatSet

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_ColorLabelMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRationalMinKey
open WordOperations WordList
noncomputable def run (x : List Bool) : List Bool := head (BinaryRationalSort.sort x)
end MetricKMedianRecovery.BitMachine.BinaryRationalMinKey

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_SamplingReference
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySamplingReference
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field )
attribute [local irreducible] WordList.mapWith
variable {n l : ℕ}
noncomputable def run (x : List Bool) : List Bool := BinaryRationalMinKey.run (entries x)
end MetricKMedianRecovery.BitMachine.BinarySamplingReference

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
open BinaryOpeningPayment (field )
variable {n : ℕ}
noncomputable def reference (x : List Bool) : List Bool := BinarySamplingReference.run (referenceInput x)
end MetricKMedianRecovery.BitMachine.BinarySamplingState

namespace MetricKMedianRecovery.BitMachine.BinarySamplingOracle
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field )
variable {n : ℕ}
noncomputable def reference (x : List Bool) : List Bool := BinarySamplingState.reference (pairBits (field 2 (extractPrefix x),row x))
end MetricKMedianRecovery.BitMachine.BinarySamplingOracle

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BranchWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryAssignmentWeight
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field )
variable {n : ℕ}
noncomputable def identity (x : List Bool) : List Bool := discardPrefix (BinarySamplingOracle.reference x)
noncomputable def identities (x : List Bool) : List Bool := mapWith identity (pairBits (x,field 1 x))
noncomputable def count (x : List Bool) : List Bool := Count.run (filterWith WordEq.eq x)
noncomputable def run (x : List Bool) : List Bool := BinaryRational.encode ((count x).length:ℚ)
end MetricKMedianRecovery.BitMachine.BinaryAssignmentWeight

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BlueItem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBlueRecords
open WordOperations WordList
open BinaryOpeningPayment (field )
variable {n m : ℕ}
noncomputable def weight (x : List Bool) : List Bool := BinaryAssignmentWeight.run (pairBits
  (discardPrefix x,BinaryAssignmentWeight.identities (field 0 (extractPrefix x))))
noncomputable def scaled (x : List Bool) : List Bool := RationalMatrix.vectorScale (pairBits (weight x,row x))
noncomputable def op (x : List Bool) : List Bool := pairBits (discardPrefix x,pairBits (tag x,scaled x))
noncomputable def run (x : List Bool) : List Bool := mapWith op (pairBits (x,field 1 x))
end MetricKMedianRecovery.BitMachine.BinaryBlueRecords

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BlueLookup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBlueCell
open WordOperations WordList
open BinaryOpeningPayment (field )
variable {n m : ℕ} {R : Type*} [LinearOrder R]
noncomputable def old (x : List Bool) : List Bool := BinaryBlueLookup.run
  (pairBits (BinaryNatSet.diff (pairBits (whole x,discardPrefix x)),field 3 (ctx x)))
noncomputable def op (x : List Bool) : List Bool := BinaryBlueMerge.run (pairBits (block x,old x))
end MetricKMedianRecovery.BitMachine.BinaryBlueCell

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BlueProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBlueOutput
open WordOperations WordList
open BinaryOpeningPayment (field )
variable {m n r : ℕ}
noncomputable def pick (x : List Bool) : List Bool := head (filterWith matching x)
noncomputable def source (x : List Bool) : List Bool := extractPrefix (discardPrefix (pick (query x)))
noncomputable def destination (x : List Bool) : List Bool := discardPrefix (discardPrefix (pick (query x)))
noncomputable def run (x : List Bool) : List Bool := encode [mapWith source (prepared x),mapWith destination (prepared x)]
end MetricKMedianRecovery.BitMachine.BinaryBlueOutput

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CopyGround
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCopyTables
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field )
variable {n a : ℕ}
noncomputable def entry (x : List Bool) : List Bool :=
  if BinaryNatSet.contains (pairBits (discardPrefix x,extractPrefix x)) then discardPrefix x
  else head (extractPrefix x)
noncomputable def row (x : List Bool) : List Bool := mapWith entry (pairBits (ball x,columns x))
attribute [local irreducible] mapWith flatMapWith
noncomputable def locations (x : List Bool) : List Bool := flatMapWith row (pairBits (x,indices x))
end MetricKMedianRecovery.BitMachine.BinaryCopyTables

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BranchBalls
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBranchBalls
open WordOperations WordList
open BinaryOpeningPayment (field )
variable {n a : ℕ}
noncomputable def ball : List Bool→List Bool := filterWith BinarySampler.Update.within ∘ input
noncomputable def balls (x : List Bool) : List Bool := mapWith ball (pairBits (x,field 2 x))
noncomputable def run (x : List Bool) : List Bool := encode [Count.run (field 0 x),balls x]
end MetricKMedianRecovery.BitMachine.BinaryBranchBalls

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_ClassFilter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryClassFilter
open WordOperations WordList
open BinaryOpeningPayment (field )
variable {n m : ℕ}
noncomputable def run : List Bool→List Bool := filterWith matching
end MetricKMedianRecovery.BitMachine.BinaryClassFilter

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BranchContext
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBranchContext
open WordOperations WordList
open BinaryOpeningPayment (field )
variable {n m : ℕ}
noncomputable def remaining (x : List Bool) : List Bool := BinaryNatSet.diff (pairBits (field 3 x,extractPrefix (field 5 x)))
attribute [local irreducible] remaining
noncomputable def classOf (j : ℕ) (x : List Bool) : List Bool := BinaryClassFilter.run
  (pairBits (pairBits (field 6 x,j.bits),remaining x))
attribute [local irreducible] classOf
attribute [local irreducible] ballInput
noncomputable def copyData (x : List Bool) : List Bool := BinaryBranchBalls.run (ballInput x)
attribute [local irreducible] copyData
noncomputable def origins (x : List Bool) : List Bool := BinaryCopyTables.origins (copyData x)
attribute [local irreducible] origins
noncomputable def locations (x : List Bool) : List Bool := BinaryCopyTables.locations (copyData x)
attribute [local irreducible] locations
end MetricKMedianRecovery.BitMachine.BinaryBranchContext

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BranchPhysical
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBranchCheck
open WordOperations WordList BinaryArithmetic BinaryBranchContext
open BinaryOpeningPayment (field )
variable {n m : ℕ}
noncomputable def outside (x : List Bool) : List Bool := BinaryNatSet.diff (pairBits (extractPrefix (field 5 x),field 3 x))
noncomputable def badBalls (x : List Bool) : List Bool := filterWith badBall (pairBits ([],field 1 (copyData x)))
noncomputable def badRadii (x : List Bool) : List Bool := filterWith badRadius (pairBits ([],discardPrefix (field 5 x)))
end MetricKMedianRecovery.BitMachine.BinaryBranchCheck

end OAI
end


