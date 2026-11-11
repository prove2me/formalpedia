-- Prove2me | Definitions.Def_Q238K018
-- name    : Q238K018
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T23:16:11.535143+00:00
-- url     : https://prove2.me/theorems/90985044-e131-4a72-9c64-c42310dce6c9
-- title:
--   Definitions bundle Q238K018 of the split of OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 127 declarations of OpenAI's Lean: 101 definitions and 26 theorems. The definitions and types are `OAI.MetricKMedianRecovery.BitMachine.BinaryArithmetic.Multiplication.mStacks`, `OAI.MetricKMedianRecovery.BitMachine.BinaryArithmetic.addProgram`, `OAI.MetricKMedianRecovery.BitMachine.BinaryArithmetic.addReverse_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryArithmetic.cfg`, `OAI.MetricKMedianRecovery.BitMachine.BinaryArithmetic.done`, `OAI.MetricKMedianRecovery.BitMachine.BinaryArithmetic.parse_outputs`, `OAI.MetricKMedianRecovery.BitMachine.BinaryArithmetic.rev_outputs`, `OAI.MetricKMedianRecovery.BitMachine.BinaryArithmetic.sum_outputs`, `OAI.MetricKMedianRecovery.BitMachine.BinaryArithmetic.trimCfg`, `OAI.MetricKMedianRecovery.BitMachine.BinaryArithmetic.trimDone`, `OAI.MetricKMedianRecovery.BitMachine.BinaryArithmetic.trimProgram`, `OAI.MetricKMedianRecovery.BitMachine.BinaryArithmetic.trim_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryArithmetic.trim_outputs`, `OAI.MetricKMedianRecovery.BitMachine.BinaryClearRow.coeffWords`, `OAI.MetricKMedianRecovery.BitMachine.BinaryClearRow.run`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidAdvance.normWords`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidAdvance.zeroDirection`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidCut.centerWords`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidCut.coefA`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidCut.coefB`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidCut.cutInput`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidCut.cutWords`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidCut.difference`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidCut.differenceInput`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidCut.outerInput`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidCut.outerWords`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidCut.precision`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidCut.scaledOuter`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidCut.scaledOuterInput`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidGrid.entry`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidGrid.entryWords`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidGrid.floorValue`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidGrid.qvalue`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidGrid.rowWords`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidGrid.run`, `OAI.MetricKMedianRecovery.BitMachine.BinaryExactSolve.bounds`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFinalFace.allRows`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFinalFace.box`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFinalFace.context`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFinalFace.shape` and 61 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedianRecovery_Encoding_Encode2`, `KMedianRecovery_Encoding_OptionEncode`, `KMedianRecovery_Encoding_RationalLeaves`, `KMedianRecovery_Machines_LoopInput2`, `KMedianRecovery_Recovery_Basic`, `KMedianRecovery_Recovery_Basic2`, `KMedianRecovery_Recovery_BoundedDecision`, `KMedianRecovery_Recovery_FaceSelection`, `KMedianRecovery_Recovery_GetRow2`, `KMedianRecovery_Recovery_IfNat`, `KMedianRecovery_Recovery_LeftNum`, `KMedianRecovery_Recovery_LengthPolynomial`, `KMedianRecovery_Recovery_Mul`, `KMedianRecovery_Recovery_Normalize`, `KMedianRecovery_Recovery_NumAbs`, `KMedianRecovery_Recovery_Pack3`, `KMedianRecovery_Recovery_Pack4`, `KMedianRecovery_Recovery_Pack5`, `KMedianRecovery_Recovery_Pack6`, `KMedianRecovery_Recovery_Pack8`, `KMedianRecovery_Recovery_Rectangular`, `KMedianRecovery_Recovery_RowInput`, `KMedianRecovery_Recovery_Step`, `KMedianRecovery_Recovery_Store2`, `KMedianRecovery_Recovery_Value`, `KMedianRecovery_Recovery_Values`.
--
--   **Imports.** It imports the published bundle `Def_KMedianRefinedRecovery`; the bundles `Q238K006`, `Q238K007`, `Q238K008` and `Q238K010` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q238K024`, `Q238K025`, `Q238K026` and `Q238K027`; the statements `OAI_MetricKMedianRecovery_BitMachine_BinaryBranchRows_run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.RationalMatrix.determinantWords_encode_s238`, `OAI.MetricKMedianRecovery.BitMachine.RationalMatrix.fold_steps_s238`, `OAI.MetricKMedianRecovery.BitMachine.RationalMatrix.mulWords_encode_s238`, `OAI.MetricKMedianRecovery.BitMachine.RationalMatrix.solveWords_bird_s238`, `OAI.MetricKMedianRecovery.RationalLeaves.prefix_leaf_s238` and `OAI.MetricKMedianRecovery.RationalLeaves.zero_free_replay_s238`; the proofs of `OAI.MetricKMedianRecovery.BitMachine.RationalMatrix.determinantWords_encode_s238`, `OAI.MetricKMedianRecovery.BitMachine.RationalMatrix.fold_steps_s238`, `OAI.MetricKMedianRecovery.BitMachine.RationalMatrix.mulWords_encode_s238`, `OAI.MetricKMedianRecovery.RationalLeaves.prefix_leaf_s238` and `OAI.MetricKMedianRecovery.RationalLeaves.zero_free_replay_s238`.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_KMedianRefinedRecovery
import Definitions.Def_Q238K006
import Definitions.Def_Q238K007
import Definitions.Def_Q238K008
import Definitions.Def_Q238K010

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Value
attribute [-simp] _root_.OAI.MetricKMedianRecovery.BitMachine.MapLeft.stacks_left _root_.OAI.MetricKMedianRecovery.BitMachine.MapLeft.stacks_one _root_.OAI.MetricKMedianRecovery.BitMachine.MapLeft.stacks_zero _root_.OAI.MetricKMedianRecovery.BitMachine.discardPrefix_pairBits _root_.OAI.MetricKMedianRecovery.BitMachine.extractPrefix_pairBits _root_.OAI.MetricKMedianRecovery.BitMachine.frameStacks_inl _root_.OAI.MetricKMedianRecovery.BitMachine.frameStacks_inr
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open Turing Turing.TM2 StateTransition

namespace BinaryArithmetic

lemma update_zero (x y z t : List Bool) :
    Function.update (triStacks x y z) 0 t=triStacks t y z := by
  funext i
  fin_cases i <;> simp [triStacks]
lemma update_one (x y z t : List Bool) :
    Function.update (triStacks x y z) 1 t=triStacks x t z := by
  funext i
  fin_cases i <;> simp [triStacks]
lemma update_two (x y z t : List Bool) :
    Function.update (triStacks x y z) 2 t=triStacks x y t := by
  funext i
  fin_cases i <;> simp [triStacks]

abbrev addProgram : Program where
  K := Fin 3
  input := 0
  output := 1
  Label := Fin 3
  main := 0
  State := Bool × Option Bool × Option Bool
  initial := (false,none,none)
  code l := if l=0 then
    .pop 0 (fun s b => (s.1,b,none))
      (.branch (fun s => decide (s.2.1=some true))
        (.pop 0 (fun s b => (s.1,b,none))
          (.branch (fun s => s.2.1.isSome)
            (.push 1 (fun s => s.2.1.getD false)
              (.load (fun _ => (false,none,none)) (.goto (fun _ => 0))))
            (.load (fun _ => (false,none,none)) (.goto (fun _ => 1)))))
        (.load (fun _ => (false,none,none)) (.goto (fun _ => 1))))
    else if l=1 then
      .pop 1 (fun s b => (s.1,b,none))
        (.branch (fun s => s.2.1.isSome)
          (.push 2 (fun s => s.2.1.getD false)
            (.load (fun _ => (false,none,none)) (.goto (fun _ => 1))))
          (.load (fun _ => (false,none,none)) (.goto (fun _ => 2))))
    else
      .pop 2 (fun s b => (s.1,b,none))
        (.pop 0 (fun s b => (s.1,s.2.1,b))
          (.branch (fun s => s.2.1.isSome || s.2.2.isSome)
            (.push 1 (fun s => sumBit s.1 (s.2.1.getD false) (s.2.2.getD false))
              (.load (fun s => (carryBit s.1 (s.2.1.getD false) (s.2.2.getD false),none,none))
                (.goto (fun _ => 2))))
            (.branch Prod.fst
              (.push 1 (fun _ => true) (.load (fun _ => (false,none,none)) .halt))
              (.load (fun _ => (false,none,none)) .halt))))

def cfg (l : Fin 3) (c : Bool) (x y z : List Bool) : addProgram.machine.Cfg :=
  ⟨some l,(c,none,none),triStacks x y z⟩
def done (ys : List Bool) : addProgram.machine.Cfg :=
  ⟨none,(false,none,none),triStacks [] ys []⟩

lemma add_initial (xs : List Bool) : initList addProgram.machine xs=cfg 0 false xs [] [] := by
  rw [initList_bool]
  congr 1
  funext i
  fin_cases i <;> simp [addProgram,triStacks]

lemma add_final (xs : List Bool) : haltList addProgram.machine xs=done xs := by
  rw [haltList_bool]
  congr 1
  funext i
  fin_cases i <;> simp [addProgram,triStacks]

lemma parse_nil (ys : List Bool) :
    addProgram.machine.step (cfg 0 false [] ys [])=some (cfg 1 false [] ys []) := by
  simp [FinTM2.step,cfg,addProgram,TM2.step,TM2.stepAux,update_zero]
  rfl
lemma parse_one (ys : List Bool) :
    addProgram.machine.step (cfg 0 false [true] ys [])=some (cfg 1 false [] ys []) := by
  simp [FinTM2.step,cfg,addProgram,TM2.step,TM2.stepAux,update_zero]
  rfl
lemma parse_false (xs ys : List Bool) :
    addProgram.machine.step (cfg 0 false (false::xs) ys [])=some (cfg 1 false xs ys []) := by
  simp [FinTM2.step,cfg,addProgram,TM2.step,TM2.stepAux,update_zero]
  rfl
lemma parse_true (b : Bool) (xs ys : List Bool) :
    addProgram.machine.step (cfg 0 false (true::b::xs) ys [])=some (cfg 0 false xs (b::ys) []) := by
  simp [FinTM2.step,cfg,addProgram,TM2.step,TM2.stepAux,update_zero,update_one]
  rfl

lemma rev_nil (xs zs : List Bool) :
    addProgram.machine.step (cfg 1 false xs [] zs)=some (cfg 2 false xs [] zs) := by
  simp [FinTM2.step,cfg,addProgram,TM2.step,TM2.stepAux,update_one]
  rfl
lemma rev_cons (b : Bool) (xs ys zs : List Bool) :
    addProgram.machine.step (cfg 1 false xs (b::ys) zs)=some (cfg 1 false xs ys (b::zs)) := by
  simp [FinTM2.step,cfg,addProgram,TM2.step,TM2.stepAux,update_one,update_two]
  rfl

lemma sum_nil (c : Bool) (zs : List Bool) :
    addProgram.machine.step (cfg 2 c [] zs [])=some (done ((if c then [true] else [])++zs)) := by
  cases c <;> simp [FinTM2.step,cfg,done,addProgram,TM2.step,TM2.stepAux,update_zero,update_two,update_one]
  all_goals rfl

lemma sum_cons_nil (c x : Bool) (xs zs : List Bool) :
    addProgram.machine.step (cfg 2 c [] zs (x::xs))=
      some (cfg 2 (carryBit c x false) [] (sumBit c x false::zs) xs) := by
  simp [FinTM2.step,cfg,addProgram,TM2.step,TM2.stepAux,update_zero,update_two,update_one]
  rfl
lemma sum_nil_cons (c y : Bool) (ys zs : List Bool) :
    addProgram.machine.step (cfg 2 c (y::ys) zs [])=
      some (cfg 2 (carryBit c false y) ys (sumBit c false y::zs) []) := by
  simp [FinTM2.step,cfg,addProgram,TM2.step,TM2.stepAux,update_zero,update_two,update_one]
  rfl
lemma sum_cons_cons (c x y : Bool) (xs ys zs : List Bool) :
    addProgram.machine.step (cfg 2 c (y::ys) zs (x::xs))=
      some (cfg 2 (carryBit c x y) ys (sumBit c x y::zs) xs) := by
  simp [FinTM2.step,cfg,addProgram,TM2.step,TM2.stepAux,update_zero,update_two,update_one]
  rfl

noncomputable def sum_outputs (c : Bool) (xs ys zs : List Bool) :
    EvalsToInTime addProgram.machine.step (cfg 2 c ys zs xs)
      (some (done ((add c xs ys).reverse++zs))) (xs.length+ys.length+1) := by
  induction xs generalizing c ys zs with
  | nil =>
    induction ys generalizing c zs with
    | nil =>
      cases c with
      | false => simpa [add] using one_step (sum_nil false zs)
      | true => simpa [add] using one_step (sum_nil true zs)
    | cons y ys ih =>
      have hh := step_then (sum_nil_cons c y ys zs) (ih (carryBit c false y) (sumBit c false y::zs))
      simpa only [add,List.reverse_cons,List.append_assoc,List.singleton_append,List.length_cons,
        List.length_nil,Nat.zero_add] using hh
  | cons x xs ih =>
    cases ys with
    | nil =>
      have hh := step_then (sum_cons_nil c x xs zs) (ih (carryBit c x false) [] (sumBit c x false::zs))
      simpa only [add,List.reverse_cons,List.append_assoc,List.singleton_append,List.length_cons,
        List.length_nil,Nat.add_zero] using hh
    | cons y ys =>
      have hh := step_then (sum_cons_cons c x y xs ys zs) (ih (carryBit c x y) ys (sumBit c x y::zs))
      simp only [add,List.reverse_cons,List.append_assoc,List.singleton_append] at ⊢
      exact time_mono hh (by simp; omega)

noncomputable def rev_outputs (xs ys zs : List Bool) :
    EvalsToInTime addProgram.machine.step (cfg 1 false xs ys zs)
      (some (done ((add false (ys.reverse++zs) xs).reverse)))
        (ys.length+(ys.length+zs.length)+xs.length+2) := by
  induction ys generalizing zs with
  | nil =>
    have hh := step_then (rev_nil xs zs) (sum_outputs false zs xs [])
    simpa only [List.reverse_nil,List.nil_append,List.append_nil,List.length_nil,Nat.zero_add,Nat.add_assoc]
      using hh
  | cons b ys ih =>
    have hh := step_then (rev_cons b xs ys zs) (ih (b::zs))
    simp only [List.reverse_cons,List.append_assoc,List.singleton_append] at ⊢
    exact time_mono hh (by simp; omega)

noncomputable def parse_outputs (xs ys : List Bool) :
    EvalsToInTime addProgram.machine.step (cfg 0 false xs ys [])
      (some (done ((add false ((extractPrefix xs).reverse++ys).reverse (discardPrefix xs)).reverse)))
        (2*xs.length+2*ys.length+3) := by
  induction xs using List.twoStepInduction generalizing ys with
  | nil =>
    have hh := step_then (parse_nil ys) (rev_outputs [] ys [])
    simpa only [extractPrefix,discardPrefix,List.reverse_nil,List.nil_append,List.append_nil,
      List.length_nil,Nat.add_zero,Nat.zero_add] using time_mono hh (by simp; omega)
  | singleton b =>
    cases b with
    | false =>
      have hh := step_then (parse_false [] ys) (rev_outputs [] ys [])
      simpa only [extractPrefix,discardPrefix,List.reverse_nil,List.nil_append,List.append_nil,List.length_nil,List.length_singleton] using
        time_mono hh (by simp; omega)
    | true =>
      have hh := step_then (parse_one ys) (rev_outputs [] ys [])
      simpa only [extractPrefix,discardPrefix,List.reverse_nil,List.nil_append,List.append_nil,List.length_nil,List.length_singleton] using
        time_mono hh (by simp; omega)
  | cons_cons b c xs ih _ =>
    cases b with
    | false =>
      have hh := step_then (parse_false (c::xs) ys) (rev_outputs (c::xs) ys [])
      simpa only [extractPrefix,discardPrefix,List.reverse_nil,List.nil_append,List.append_nil] using
        time_mono hh (by simp; omega)
    | true =>
      have hh := step_then (parse_true c xs ys) (ih (c::ys))
      simp only [extractPrefix,discardPrefix,List.reverse_cons,List.append_assoc,List.singleton_append] at ⊢
      exact time_mono hh (by simp; omega)

noncomputable def addReverse_computes : PolyComputes (fun xs =>
    (add false (extractPrefix xs) (discardPrefix xs)).reverse) where
  program := addProgram
  time := 2*Polynomial.X+3
  outputs xs := by
    simpa only [TM2OutputsInTime,Option.map_some,add_initial,add_final,List.append_nil,
      List.reverse_reverse,List.length_nil,Nat.mul_zero,Nat.add_zero,Polynomial.eval_add,
      Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X] using parse_outputs xs []

end BinaryArithmetic
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Normalize
attribute [-simp] _root_.OAI.MetricKMedianRecovery.BitMachine.MapLeft.stacks_left _root_.OAI.MetricKMedianRecovery.BitMachine.MapLeft.stacks_one _root_.OAI.MetricKMedianRecovery.BitMachine.MapLeft.stacks_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open Turing Turing.TM2 StateTransition
namespace BinaryArithmetic

abbrev trimProgram : Program where
  K := Unit
  input := ()
  output := ()
  Label := Unit
  main := ()
  State := Option Bool
  initial := none
  code _ := .pop () (fun _ b => b)
    (.branch (fun s => decide (s=some false))
      (.load (fun _ => none) (.goto (fun _ => ())))
      (.branch Option.isSome
        (.push () (fun _ => true) (.load (fun _ => none) .halt))
        (.load (fun _ => none) .halt)))

def trimCfg (xs : List Bool) : trimProgram.machine.Cfg := ⟨some (),none,fun _ => xs⟩
def trimDone (xs : List Bool) : trimProgram.machine.Cfg := ⟨none,none,fun _ => xs⟩

lemma trim_initial (xs : List Bool) : initList trimProgram.machine xs=trimCfg xs := by
  rw [initList_bool]
  congr 1
lemma trim_final (xs : List Bool) : haltList trimProgram.machine xs=trimDone xs := by
  rw [haltList_bool]
  congr 1
lemma trim_nil : trimProgram.machine.step (trimCfg [])=some (trimDone []) := by
  simp [FinTM2.step,trimCfg,trimDone,trimProgram,TM2.step,TM2.stepAux,unit_update]
  rfl
lemma trim_false (xs : List Bool) :
    trimProgram.machine.step (trimCfg (false::xs))=some (trimCfg xs) := by
  simp [FinTM2.step,trimCfg,trimProgram,TM2.step,TM2.stepAux,unit_update]
  rfl
lemma trim_true (xs : List Bool) :
    trimProgram.machine.step (trimCfg (true::xs))=some (trimDone (true::xs)) := by
  simp [FinTM2.step,trimCfg,trimDone,trimProgram,TM2.step,TM2.stepAux,unit_update]
  rfl

noncomputable def trim_outputs (xs : List Bool) :
    EvalsToInTime trimProgram.machine.step (trimCfg xs)
      (some (trimDone (xs.dropWhile (fun b => !b)))) (xs.length+1) := by
  induction xs with
  | nil => exact one_step trim_nil
  | cons b xs ih =>
    cases b with
    | false => simpa using step_then (trim_false xs) ih
    | true => simpa using time_mono (one_step (trim_true xs)) (by omega : 1≤(true::xs).length+1)

noncomputable def trim_computes : PolyComputes (fun xs => xs.dropWhile (fun b => !b)) where
  program := trimProgram
  time := Polynomial.X+1
  outputs xs := by
    simpa only [TM2OutputsInTime,Option.map_some,trim_initial,trim_final,Polynomial.eval_add,
      Polynomial.eval_X,Polynomial.eval_one] using trim_outputs xs

end BinaryArithmetic
end MetricKMedianRecovery.BitMachine

end OAI
end

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

def mStacks (a b c d e : List Bool) : Stacks (Fin 5) := ![a,b,c,d,e]

end Multiplication
end BinaryArithmetic
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Store2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open Turing Turing.TM2 StateTransition
namespace WordOperations

abbrev prefixProgram (b : Bool) : Program where
  K := Unit
  input := ()
  output := ()
  Label := Unit
  main := ()
  State := Unit
  initial := ()
  code _ := .push () (fun _=>b) .halt

noncomputable def prefix_computes (b : Bool) : PolyComputes (List.cons b) where
  program := prefixProgram b
  time := 1
  outputs xs := by
    simp only [TM2OutputsInTime,Option.map_some,Polynomial.eval_one]
    apply one_step
    simp [initList_bool,haltList_bool,FinTM2.step,prefixProgram,TM2.step,TM2.stepAux,unit_update]
    rfl

end WordOperations

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

def rawInv (x : List Bool) : List Bool :=
  pairBits (Signed.pack (Signed.sign (numerator x)) (value (denominator x)).bits,
    (Signed.mag (numerator x)).bits)
def invWords : List Bool → List Bool := reduce ∘ rawInv

end BinaryRational
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

lemma length_next (x : List Bool) : (next x).length ≤ max x.length (2*mass (next x)+3) := by
  unfold next While.next
  split_ifs
  · unfold step
    split_ifs <;> simp only [length_pack,mass,counter_pack,data_pack,output_pack,
      List.length_nil,List.length_tail,List.length_cons] <;> omega
  · exact Nat.le_max_left _ _
lemma iterate_bounds (x : List Bool) (j : ℕ) :
    mass (next^[j] x) ≤ mass x ∧ (next^[j] x).length ≤ x.length+2*mass x+3 ∧
    rank (next^[j] x) ≤ rank x-j := by
  induction j with
  | zero => simp only [Function.iterate_zero_apply,Nat.sub_zero,Nat.le_refl,true_and,and_true]; omega
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    have hm := mass_next (next^[j] x)
    have hl := length_next (next^[j] x)
    have hr := rank_next (next^[j] x)
    refine ⟨hm.trans ih.1,?_,?_⟩
    · apply hl.trans; apply max_le ih.2.1; omega
    · omega
lemma stop (x : List Bool) : (next^[rank x] x).head?≠some true := by
  have hh := (iterate_bounds x (rank x)).2.2
  simp only [Nat.sub_self,Nat.le_zero] at hh
  intro hp
  change (if (next^[rank x] x).head?=some true then _ else 0)=0 at hh
  rw [ite_eq_left hp] at hh
  omega

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

lemma length_next (f : List Bool → List Bool) (x : List Bool) :
    (next f x).length ≤ max x.length
      (2*(counter (next f x)).length+2*(data (next f x)).length+(output (next f x)).length+3) := by
  unfold next While.next; split_ifs
  · unfold step; split_ifs <;> simp only [length_pack,counter_pack,data_pack,output_pack] <;> omega
  · exact Nat.le_max_left _ _

lemma iterate_bounds (f : List Bool → List Bool) (x : List Bool) (j : ℕ) :
    (counter ((next f)^[j] x)).length ≤ (counter x).length ∧
    data ((next f)^[j] x)=data x ∧
    (output ((next f)^[j] x)).length ≤ max (output x).length (data x).length ∧
    ((next f)^[j] x).length ≤ x.length+2*(counter x).length+3*(data x).length+(output x).length+3 ∧
    rank ((next f)^[j] x) ≤ rank x-j := by
  induction j with
  | zero =>
    simp only [Function.iterate_zero_apply,Nat.sub_zero,Nat.le_refl,true_and,and_true]
    exact ⟨Nat.le_max_left _ _,by omega⟩
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    have hc := counter_next f ((next f)^[j] x)
    have hd := data_next f ((next f)^[j] x)
    have ho := output_next f ((next f)^[j] x)
    have hl := length_next f ((next f)^[j] x)
    have hr := rank_next f ((next f)^[j] x)
    rw [ih.2.1] at hd ho
    refine ⟨hc.trans ih.1,hd,?_,?_,?_⟩
    · omega
    · apply hl.trans; apply max_le ih.2.2.2.1
      rw [hd]
      omega
    · omega
lemma stop (f : List Bool → List Bool) (x : List Bool) : ((next f)^[rank x] x).head?≠some true := by
  have hh := (iterate_bounds f x (rank x)).2.2.2.2
  simp only [Nat.sub_self,Nat.le_zero] at hh
  intro hp
  change (if ((next f)^[rank x] x).head?=some true then _ else 0)=0 at hh
  rw [ite_eq_left hp] at hh; omega

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

noncomputable def PolyComputes.lengthPolynomial {f : List Bool → List Bool} (hf : PolyComputes f) : Polynomial ℕ :=
  Polynomial.X+hf.time*Polynomial.C hf.program.maxPush
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_Encode2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace RationalMatrix
open WordList

def columnOp : List Bool → List Bool := (WordList.mapWith Lookup.run) ∘ swapWords
noncomputable def transposeWords : List Bool → List Bool := (mapWith columnOp) ∘ matrixIndices

noncomputable def rightRowOp : List Bool → List Bool := (mapWith RationalArray.dotListsWords) ∘ swapWords
noncomputable def mulInput (x : List Bool) : List Bool :=
  pairBits (transposeWords (discardPrefix x),extractPrefix x)
noncomputable def mulWords : List Bool → List Bool := (mapWith rightRowOp) ∘ mulInput
end RationalMatrix
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_GetRow2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace RationalMatrix
open WordList

def getRow : List Bool → List Bool := Lookup.run ∘ swapWords

def entryInput (x : List Bool) : List Bool := pairBits (discardPrefix x,getRow (extractPrefix x))
def getEntry : List Bool → List Bool := Lookup.run ∘ entryInput
def diagAt : List Bool → List Bool := getEntry ∘ diagInput
def tailDiagValue : List Bool → List Bool := diagAt ∘ tailDiagInput

def tailDiagOp (x : List Bool) : List Bool :=
  if value (discardPrefix x)≤value (contextIndex x) then BinaryRational.encode 0 else tailDiagValue x
noncomputable def tailDiagMap : List Bool → List Bool := (mapWith tailDiagOp) ∘ tailDiagMapInput
noncomputable def tailDiag : List Bool → List Bool := RationalArray.sumWords ∘ tailDiagMap

noncomputable def negDiag : List Bool → List Bool :=
  BinaryRational.negWords ∘ tailDiag ∘ extractPrefix
noncomputable def muEntry (x : List Bool) : List Bool :=
  if value (discardPrefix x)≤value (contextIndex x) then
    if value (contextIndex x)≤value (discardPrefix x) then negDiag x else BinaryRational.encode 0
  else getEntry x

noncomputable def muRow : List Bool → List Bool := (mapWith muEntry) ∘ tailDiagMapInput
noncomputable def muWords : List Bool → List Bool := (mapWith muRow) ∘ matrixIndices
noncomputable def stepInput (x : List Bool) : List Bool := pairBits (muWords (discardPrefix x),extractPrefix x)
noncomputable def stepWords (x : List Bool) : List Bool := mulWords (stepInput x)

end RationalMatrix
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
namespace WordList
noncomputable def pointwise (f : List Bool → List Bool) (x : List Bool) : List Bool :=
  mapWith (f ∘ discardPrefix) (pairBits ([],Zip.run x))
end WordList
namespace RationalMatrix
open WordList
noncomputable def vectorSub : List Bool → List Bool := pointwise BinaryRational.subWords
noncomputable def matrixSub : List Bool → List Bool := pointwise vectorSub
noncomputable def matrixScale : List Bool → List Bool := mapWith vectorScale
noncomputable def outerRow : List Bool → List Bool := vectorScale ∘ swapWords
noncomputable def outer : List Bool → List Bool := (mapWith outerRow) ∘ swapWords
end RationalMatrix
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

def precision : List Bool → List Bool := discardPrefix ∘ rest₃

def coefA (x : List Bool) : List Bool := BinaryRational.encode (dimension x^2/(dimension x^2-1))
noncomputable def coefB (x : List Bool) : List Bool := BinaryRational.encode (2/((dimension x+1)*qvalue x))
noncomputable def centerWords : List Bool → List Bool := vectorSub ∘ centerInput

noncomputable def outerInput (x : List Bool) : List Bool := pairBits (haWords x,haWords x)
noncomputable def outerWords : List Bool → List Bool := outer ∘ outerInput
noncomputable def scaledOuterInput (x : List Bool) : List Bool := pairBits (coefB x,outerWords x)
noncomputable def scaledOuter : List Bool → List Bool := matrixScale ∘ scaledOuterInput
noncomputable def differenceInput (x : List Bool) : List Bool := pairBits (shape x,scaledOuter x)
noncomputable def difference : List Bool → List Bool := matrixSub ∘ differenceInput
noncomputable def cutInput (x : List Bool) : List Bool := pairBits (coefA x,difference x)
noncomputable def cutWords : List Bool → List Bool := matrixScale ∘ cutInput
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
namespace BinaryEllipsoidGrid
open RationalMatrix WordList

def entry : List Bool → List Bool := getEntry ∘ entryInput
noncomputable def qvalue (x : List Bool) : ℚ := BinaryRational.decode (entry x)
noncomputable def floorValue (x : List Bool) : ℚ := (⌊scale x*qvalue x⌋:ℤ)/scale x
noncomputable def entryWords (x : List Bool) : List Bool :=
  if value (row x)≤value (col x) then
    if value (col x)≤value (row x) then BinaryRational.encode (floorValue x+diagonal x)
    else BinaryRational.encode (floorValue x)
  else BinaryRational.encode (floorValue x)
noncomputable def rowWords : List Bool → List Bool := (mapWith entryWords) ∘ rowInput
noncomputable def run : List Bool → List Bool := (mapWith rowWords) ∘ runInput
end BinaryEllipsoidGrid
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

noncomputable def normWords (x : List Bool) : List Bool :=
  RationalArray.dotListsWords (pairBits (direction x,direction x))
noncomputable def zeroDirection (x : List Bool) : Bool := decide (BinaryRational.decode (normWords x)≤0)
end BinaryEllipsoidAdvance
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_RationalLeaves
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalLeaves
variable {V : Type*} [PseudoMetricSpace V]

attribute [local instance] metric

def leaf (key : ℕ) (i : V) (s : ℚ) : Label V := Sum.inr (key,i,s)

end MetricKMedianRecovery.RationalLeaves

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_LoopInput2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace RationalMatrix
open WordList
noncomputable def loopOp (x : List Bool) : List Bool := stepWords (loopInput x)
noncomputable def iterateWords : List Bool → List Bool :=
  (Fold.run loopOp (200*(Polynomial.X+1)^6)) ∘ iterationInput

noncomputable def rawDet : List Bool → List Bool := WordList.head ∘ WordList.head ∘ iterateWords
noncomputable def determinantInput (x : List Bool) : List Bool := Fold.pack (WordList.tail x) [] (rawDet x)
noncomputable def signedDet : List Bool → List Bool := signRun ∘ determinantInput
noncomputable def determinantWords (x : List Bool) : List Bool :=
  if x=[] then BinaryRational.encode 1 else signedDet x
end RationalMatrix
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

noncomputable def shapeWords (x : List Bool) : List Bool :=
  BinaryEllipsoidInitial.run (pairBits (nword x,radiusSquare x))
noncomputable def result (x : List Bool) : List Bool :=
  if BinaryEllipsoidAdvance.found x=[] then true::BinaryEllipsoidAdvance.center x else []
end BinaryWeakSolve
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

namespace BinaryClearRow
open WordOperations BinaryArithmetic RationalLinearFeasibility Ellipsoid
open WordList RationalMatrix

noncomputable def coeffWords (x : List Bool) : List Bool := mapWith BinaryRational.mulWords (pairBits (scalar x,extractPrefix x))
noncomputable def run (x : List Bool) : List Bool := pairBits (coeffWords x,boundWords x)
end BinaryClearRow
namespace BinaryRationalDecision
open WordOperations BinaryArithmetic RationalLinearFeasibility Ellipsoid
open WordList

noncomputable def clearOp : List Bool → List Bool := BinaryClearRow.run ∘ discardPrefix
noncomputable def clearedRows (x : List Bool) : List Bool := mapWith clearOp (pairBits ([],rows x))
noncomputable def prepared (x : List Bool) : List Bool :=
  pairBits (first x,pairBits (second x,pairBits (bound x,clearedRows x)))
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
namespace BinaryFinalFace
open WordList BinaryRationalDecision
noncomputable def shape (s : Bool) (x : List Bool) : List Bool :=
  BinaryEllipsoidInitial.run (pairBits (first x,BinaryRational.encode (if s then 1 else -1)))
noncomputable def box (s : Bool) (x : List Bool) : List Bool :=
  mapWith BinaryDecision.boundOp (pairBits (BinaryRational.encode (value (bound x)),shape s x))
noncomputable def allRows (x : List Bool) : List Bool := rows x++(box true x++box false x)
noncomputable def context (x : List Bool) : List Bool :=
  pairBits (first x,pairBits (Count.run (allRows x),pairBits (bound x,allRows x)))
end BinaryFinalFace
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Pack4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
open WordOperations BinaryArithmetic
open scoped Matrix
namespace RationalMatrix
open WordList

noncomputable def updateInput (x : List Bool) : List Bool :=
  Set.pack (transposeWords (extractPrefix x)) (extractPrefix (discardPrefix x))
    (discardPrefix (discardPrefix x))
noncomputable def updateColWords (x : List Bool) : List Bool :=
  transposeWords (Set.run (updateInput x))
noncomputable def cramerOp (x : List Bool) : List Bool :=
  determinantWords (updateColWords (cramerOpInput x))
noncomputable def cramerWords (x : List Bool) : List Bool := mapWith cramerOp (cramerInput x)

noncomputable def firstDet : List Bool → List Bool := determinantWords ∘ extractPrefix
noncomputable def inverseDet : List Bool → List Bool := BinaryRational.invWords ∘ firstDet
noncomputable def solveInput (x : List Bool) : List Bool := pairBits (inverseDet x,cramerWords x)
noncomputable def solveWords (x : List Bool) : List Bool := mapWith BinaryRational.mulWords (solveInput x)
end RationalMatrix
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

section
open WordOperations BinaryArithmetic Matrix
namespace Rectangular
open WordList RationalMatrix

noncomputable def transpose (x : List Bool) : List Bool :=
  mapWith columnOp (pairBits (discardPrefix x,BinaryEllipsoidInitial.indices (extractPrefix x)))
end Rectangular
end

open WordOperations BinaryArithmetic RationalLinearFeasibility Ellipsoid Matrix
namespace BinaryExactSolve
open WordList BinaryRationalDecision RationalMatrix
noncomputable def bounds (x : List Bool) : List Bool := mapWith BinaryRow.bound (pairBits ([],x))
end BinaryExactSolve
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine

section
open WordOperations BinaryArithmetic RationalLinearFeasibility
namespace BinaryOpeningActivity
open WordList

noncomputable def run (x : List Bool) : List Bool := [decide (Find.run fails x=[])]
end BinaryOpeningActivity
end
open WordOperations BinaryArithmetic
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

noncomputable def active (x : List Bool) : Bool :=
  (BinaryOpeningActivity.run (activityInput x)).head?.getD false

noncomputable def summand (x : List Bool) : ℚ :=
  if active x then
    if distance x≤paramV x*paramZ x then -(scale x*distance x)
    else max (paramZ x-scale x*distance x) 0
  else max (scale x*nearest x-scale x*distance x) 0
noncomputable def values : List Bool → List Bool := mapWith (fun x=>BinaryRational.encode (summand x)) ∘ input
noncomputable def sumWords : List Bool → List Bool := RationalArray.sumWords ∘ values
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

noncomputable def active (k : ℕ) (x : List Bool) : Bool := BinaryOpeningPayment.active (query k x)

end BinaryOpeningConstant
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_IfNat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace BinaryOpeningCoefficient
open WordList RationalLinearFeasibility

noncomputable def payment (x : List Bool) : ℚ :=
  if value (col 0 x)=0 then if BinaryOpeningPayment.active (paymentQuery x) then
    if paymentNear x then 1 else 0 else 0 else 0

noncomputable def coefficient (x : List Bool) : ℚ :=
  if BinaryOpeningConstant.tag (extractPrefix x)=0 then
    if BinaryOpeningConstant.active 1 (extractPrefix x) then -bid 1 x else 0
  else if BinaryOpeningConstant.tag (extractPrefix x)=1 then
    if BinaryOpeningConstant.active 1 (extractPrefix x) then bid 1 x else 0
  else if BinaryOpeningConstant.tag (extractPrefix x)=2 then
    if BinaryOpeningConstant.active 1 (extractPrefix x) then bid 1 x else 0
  else if BinaryOpeningConstant.tag (extractPrefix x)=3 then
    if BinaryOpeningConstant.active 1 (extractPrefix x) then
      if BinaryOpeningConstant.near (extractPrefix x) then 0 else bid 1 x else 0
  else if BinaryOpeningConstant.tag (extractPrefix x)=4 then -payment x
  else if BinaryOpeningConstant.tag (extractPrefix x)=5 then
    if BinaryOpeningConstant.active 3 (extractPrefix x) then -slack x else 0
  else if BinaryOpeningConstant.tag (extractPrefix x)=6 then
    if BinaryOpeningConstant.active 3 (extractPrefix x) then
      (if BinaryOpeningConstant.active 1 (extractPrefix x) then bid 1 x else bid 3 x) - slack x else 0
  else if BinaryOpeningConstant.tag (extractPrefix x)=7 then
    if BinaryOpeningConstant.active 1 (extractPrefix x) then dual x else 0
  else 0
end BinaryOpeningCoefficient
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
noncomputable def rowCoefficients (x : List Bool) : List Bool :=
  mapWith (fun y=>BinaryRational.encode (BinaryOpeningCoefficient.coefficient y)) (rowInput x)
end MetricKMedianRecovery.BitMachine.BinaryRawOpening

namespace MetricKMedianRecovery.BitMachine.BinaryPhaseFirst
open WordOperations BinaryArithmetic WordList
open BinaryOpeningPayment

noncomputable def contains (x : List Bool) : Bool := decide (Find.run natEq x≠[])
end MetricKMedianRecovery.BitMachine.BinaryPhaseFirst

end OAI
end


