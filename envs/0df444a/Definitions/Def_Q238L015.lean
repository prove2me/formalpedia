-- Prove2me | Definitions.Def_Q238L015
-- name    : Q238L015
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T11:23:48.489198+00:00
-- url     : https://prove2.me/theorems/de32a378-1811-4e6c-aec6-d0c3330df513
-- title:
--   Definitions bundle Q238L015 of the split of OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 122 declarations of OpenAI's Lean: 79 definitions, 2 instances and 41 theorems. The definitions and types are `OAI.MetricKMedianRecovery.BitMachine.BinaryArithmetic.addProgram`, `OAI.MetricKMedianRecovery.BitMachine.BinaryArithmetic.addReverse_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryArithmetic.cfg`, `OAI.MetricKMedianRecovery.BitMachine.BinaryArithmetic.done`, `OAI.MetricKMedianRecovery.BitMachine.BinaryArithmetic.parse_outputs`, `OAI.MetricKMedianRecovery.BitMachine.BinaryArithmetic.rev_outputs`, `OAI.MetricKMedianRecovery.BitMachine.BinaryArithmetic.sum_outputs`, `OAI.MetricKMedianRecovery.BitMachine.BinaryArithmetic.trimCfg`, `OAI.MetricKMedianRecovery.BitMachine.BinaryArithmetic.trimDone`, `OAI.MetricKMedianRecovery.BitMachine.BinaryArithmetic.trimProgram`, `OAI.MetricKMedianRecovery.BitMachine.BinaryArithmetic.trim_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryArithmetic.trim_outputs`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGCD.firstRem`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningActivity.client`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningActivity.distanceWord`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningActivity.fails`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningActivity.paramV`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningActivity.paramZ`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningActivity.table`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningCoefficient.bid`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningCoefficient.col`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningCoefficient.dual`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningCoefficient.paymentNear`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningCoefficient.paymentQuery`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningCoefficient.row`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningCoefficient.slack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningConstant.distance`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningConstant.distanceWords`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningConstant.field`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningConstant.near`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningConstant.query`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningConstant.tag`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningEnumeration.caps`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningEnumeration.columns`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningEnumeration.doubles`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningEnumeration.dualTag`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningEnumeration.duals`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningEnumeration.kinds`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningEnumeration.pairTag`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningEnumeration.tripleTag` and 39 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedianRecovery_Recovery_Basic`, `KMedianRecovery_Recovery_Basic2`, `KMedianRecovery_Recovery_IfNat`, `KMedianRecovery_Recovery_LengthPolynomial`, `KMedianRecovery_Recovery_Normalize`, `KMedianRecovery_Recovery_Op2`, `KMedianRecovery_Recovery_Pack2`, `KMedianRecovery_Recovery_Pack3`, `KMedianRecovery_Recovery_RowInput`, `KMedianRecovery_Recovery_Step`, `KMedianRecovery_Recovery_Step2`, `KMedianRecovery_Recovery_Store2`, `KMedianRecovery_Recovery_Value`, `KMedianRecovery_Recovery_Values`.
--
--   **Imports.** It imports the published bundle `Def_KMedianRecovery`; the bundles `Q238L006` and `Q238L007` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q238L022`, `Q238L023`, `Q238L024`, `Q238L025` and `Q238L026`; the statement `OAI.MetricKMedianRecovery.BitMachine.WordList.flatMapWith_typed_s238r`.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_KMedianRecovery
import Definitions.Def_Q238L006
import Definitions.Def_Q238L007

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

end WordOperations

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

def firstRem (x : List Bool) : List Bool := (value (first x)%value (second x)).bits

end BinaryGCD
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

def step (x : List Bool) : List Bool :=
  if counter x=[] then pack false [] (data x) (output x)
  else pack true (counter x).tail (data x).tail
    (if data x=[] then output x else (data x).head?.getD false::output x)

def next := While.next step
def mass (x : List Bool) : ℕ := (counter x).length+(data x).length+(output x).length
lemma mass_next (x : List Bool) : mass (next x) ≤ mass x := by
  unfold next While.next
  split_ifs
  · unfold step
    by_cases hc : counter x=[]
    · rw [ite_eq_left hc]
      simp only [mass,counter_pack,data_pack,output_pack,List.length_nil]
      omega
    · rw [ite_eq_right hc]
      have hp := List.length_pos_iff.mpr hc
      split_ifs <;> simp only [mass,counter_pack,data_pack,output_pack,List.length_tail,List.length_cons] <;> omega
  · exact le_rfl
lemma rank_next (x : List Bool) : rank (next x) ≤ rank x-1 := by
  unfold next While.next
  split_ifs with hx
  · unfold step
    by_cases hc : counter x=[]
    · rw [ite_eq_left hc]
      simp only [rank,head_pack,Option.some.injEq,Bool.false_eq_true,ite_false, if_false,Nat.zero_le]
    · rw [ite_eq_right hc]
      have hp : 0<(counter x).length := List.length_pos_iff.mpr hc
      simp only [rank,head_pack,ite_true, if_true,counter_pack,List.length_tail,hx]
      omega
  · simp only [rank,hx,ite_false, if_false,Nat.zero_sub,Nat.le_refl]

lemma next_nil (d o : List Bool) : next (pack true [] d o)=pack false [] d o := by
  simp only [next,While.next,pack,List.head?_cons,ite_true, if_true,step,counter,List.tail_cons,
    extractPrefix_pairBits,data,discardPrefix_pairBits,output]
lemma next_cons (b : Bool) (c d o : List Bool) : next (pack true (b::c) d o)=
    pack true c d.tail (if d=[] then o else d.head?.getD false::o) := by
  simp only [next,While.next,pack,List.head?_cons,ite_true, if_true,step,counter,List.tail_cons,
    extractPrefix_pairBits,reduceCtorEq,ite_false, if_false,data,discardPrefix_pairBits,output]
lemma loop_spec (c d o : List Bool) : next^[c.length+1] (pack true c d o)=
    pack false [] (d.drop c.length) ((d.take c.length).reverse++o) := by
  induction c generalizing d o with
  | nil => simp only [List.length_nil,Nat.zero_add,Function.iterate_one,next_nil,
      List.drop_zero,List.take_zero,List.reverse_nil,List.nil_append]
  | cons b c ih =>
    rw [List.length_cons,show c.length+1+1=(c.length+1)+1 from rfl,
      Function.iterate_succ_apply,next_cons,ih]
    cases d with
    | nil => simp only [List.tail_nil,ite_true, if_true,List.drop_nil,List.take_nil,List.reverse_nil,List.nil_append]
    | cons a d => simp only [List.tail_cons,reduceCtorEq,ite_false, if_false,List.head?_cons,Option.getD_some,
        List.drop_succ_cons,List.take_succ_cons,List.reverse_cons,List.append_assoc,List.singleton_append]

def takeWords (x : List Bool) : List Bool := (discardPrefix x).take (extractPrefix x).length

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

def step (f : List Bool → List Bool) (x : List Bool) : List Bool :=
  if counter x=[] then pack false [] (data x) (output x)
  else pack true (counter x).tail (data x) ((f (output x)).take (data x).length)

def next (f : List Bool → List Bool) := While.next (step f)
lemma data_next (f : List Bool → List Bool) (x : List Bool) : data (next f x)=data x := by
  unfold next While.next; split_ifs
  · unfold step; split_ifs <;> simp only [data_pack]
  · rfl
lemma counter_next (f : List Bool → List Bool) (x : List Bool) :
    (counter (next f x)).length ≤ (counter x).length := by
  unfold next While.next; split_ifs
  · unfold step; split_ifs <;> simp only [counter_pack,List.length_nil,List.length_tail] <;> omega
  · exact le_rfl
lemma output_next (f : List Bool → List Bool) (x : List Bool) :
    (output (next f x)).length ≤ max (output x).length (data x).length := by
  unfold next While.next; split_ifs
  · unfold step; split_ifs
    · simp only [output_pack]; exact Nat.le_max_left _ _
    · simp only [output_pack,List.length_take]; omega
  · exact Nat.le_max_left _ _
lemma rank_next (f : List Bool → List Bool) (x : List Bool) : rank (next f x) ≤ rank x-1 := by
  unfold next While.next; split_ifs with hx
  · unfold step
    by_cases hc : counter x=[]
    · rw [ite_eq_left hc]
      simp only [rank,head_pack,Option.some.injEq,Bool.false_eq_true,ite_false, if_false,Nat.zero_le]
    · rw [ite_eq_right hc]
      have hp := List.length_pos_iff.mpr hc
      simp only [rank,head_pack,ite_true, if_true,counter_pack,List.length_tail,hx]
      omega
  · simp only [rank,hx,ite_false, if_false,Nat.zero_sub,Nat.le_refl]

lemma next_nil (f : List Bool → List Bool) (d o : List Bool) :
    next f (pack true [] d o)=pack false [] d o := by
  simp only [next,While.next,head_pack,ite_true, if_true,step,counter_pack,data_pack,output_pack]
lemma next_cons (f : List Bool → List Bool) (b : Bool) (c d o : List Bool) :
    next f (pack true (b::c) d o)=pack true c d ((f o).take d.length) := by
  simp only [next,While.next,head_pack,ite_true, if_true,step,counter_pack,reduceCtorEq,ite_false, if_false,
    data_pack,output_pack,List.tail_cons]
lemma loop_spec (f : List Bool → List Bool) (c d o : List Bool) :
    (next f)^[c.length+1] (pack true c d o)=
    pack false [] d ((fun s=>(f s).take d.length)^[c.length] o) := by
  induction c generalizing o with
  | nil => simp only [List.length_nil,Nat.zero_add,Function.iterate_one,next_nil,
      Function.iterate_zero_apply]
  | cons b c ih =>
    rw [List.length_cons,Function.iterate_succ_apply,next_cons,ih,Function.iterate_succ_apply]

lemma run_pair (f : List Bool → List Bool) (c d s : List Bool) :
    run f (pairBits (c,pairBits (d,s)))=(fun s=>(f s).take d.length)^[c.length] s := by
  simp only [run,extractPrefix_pairBits,discardPrefix_pairBits]

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
lemma PolyComputes.length_bound {f : List Bool → List Bool} (hf : PolyComputes f) (x : List Bool) :
    (f x).length ≤ hf.lengthPolynomial.eval x.length := by
  simpa only [PolyComputes.lengthPolynomial,Polynomial.eval_add,Polynomial.eval_X,
    Polynomial.eval_mul,Polynomial.eval_C] using hf.program.output_length (hf.outputs x)

namespace WordList

lemma length_cons (w ws : List Bool) : (cons w ws).length=2*w.length+ws.length+2 := by
  simp only [cons,List.length_cons,pairBits_length]; omega
lemma head_length (x : List Bool) : (head x).length ≤ x.length := by
  have h := (ProductBits.projections_length x.tail).1
  simp only [List.length_tail] at h
  exact h.trans (Nat.sub_le _ _)
lemma tail_length (x : List Bool) : (tail x).length ≤ x.length-1 := by
  simpa only [tail,List.length_tail] using (ProductBits.projections_length x.tail).2

namespace ReverseMap

lemma data_next (f : List Bool → List Bool) (x : List Bool) : data (next f x)=data x := by
  unfold next While.next; split_ifs
  · unfold step; split_ifs <;> simp only [data_pack]
  · rfl
lemma counter_next (f : List Bool → List Bool) (x : List Bool) :
    (counter (next f x)).length ≤ (counter x).length := by
  unfold next While.next; split_ifs
  · unfold step; split_ifs
    · simp only [counter_pack,List.length_nil,Nat.zero_le]
    · simp only [counter_pack]; exact (tail_length _).trans (Nat.sub_le _ _)
  · exact le_rfl

def growth (P : Polynomial ℕ) (x : List Bool) : ℕ := 2*P.eval (2*(data x).length+1+(counter x).length)+2
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

section
open WordOperations BinaryArithmetic
namespace WordList.Lookup

lemma decrement_length (x : List Bool) : (value x-1).bits.length ≤ x.length := by
  rw [Nat.size_eq_bits_len]
  apply Nat.size_le_size (Nat.sub_le _ _) |>.trans
  simpa only [normalize_eq_bits,Nat.size_eq_bits_len] using BinaryDivision.normalize_length x
lemma first_step (x : List Bool) : (extractPrefix (step x)).length ≤ (extractPrefix x).length := by
  unfold step; split_ifs
  · exact le_rfl
  · rw [extractPrefix_pairBits]; exact decrement_length _
lemma rest_step (x : List Bool) : (discardPrefix (step x)).length ≤ (discardPrefix x).length := by
  unfold step; split_ifs
  · exact le_rfl
  · rw [discardPrefix_pairBits]; exact (WordList.tail_length _).trans (Nat.sub_le _ _)
lemma length_step (x : List Bool) : (step x).length ≤ max x.length
    (2*(extractPrefix x).length+1+(discardPrefix x).length) := by
  unfold step; split_ifs
  · exact Nat.le_max_left _ _
  · rw [pairBits_length]
    dsimp only
    have hi := decrement_length (extractPrefix x)
    have hl := WordList.tail_length (discardPrefix x)
    omega
lemma iterate_bounds (x : List Bool) (n : ℕ) :
    (extractPrefix (step^[n] x)).length ≤ (extractPrefix x).length ∧
    (discardPrefix (step^[n] x)).length ≤ (discardPrefix x).length ∧
    (step^[n] x).length ≤ max x.length (2*(extractPrefix x).length+1+(discardPrefix x).length) := by
  induction n with
  | zero => exact ⟨le_rfl,le_rfl,Nat.le_max_left _ _⟩
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    have hf := first_step (step^[n] x)
    have hr := rest_step (step^[n] x)
    have hl := length_step (step^[n] x)
    exact ⟨hf.trans ih.1,hr.trans ih.2.1,by omega⟩

end WordList.Lookup
end
open WordOperations
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
namespace MetricTable
open WordList

def context : List Bool → List Bool := extractPrefix ∘ extractPrefix
def row : List Bool → List Bool := discardPrefix ∘ extractPrefix
def col : List Bool → List Bool := discardPrefix
noncomputable def getRow (x : List Bool) : List Bool := Lookup.run (pairBits (row x,context x))
noncomputable def get (x : List Bool) : List Bool := Lookup.run (pairBits (col x,getRow x))
end MetricTable
namespace BinaryOpeningActivity
open WordList

def table : List Bool → List Bool := extractPrefix ∘ extractPrefix ∘ extractPrefix
def client : List Bool → List Bool := discardPrefix ∘ extractPrefix ∘ extractPrefix
def paramV : List Bool → List Bool := extractPrefix ∘ discardPrefix ∘ extractPrefix
def paramZ : List Bool → List Bool := discardPrefix ∘ discardPrefix ∘ extractPrefix
noncomputable def distanceWord (x : List Bool) : List Bool :=
  MetricTable.get (pairBits (pairBits (table x,discardPrefix x),client x))
noncomputable def fails (x : List Bool) : Bool := decide
  ((1-3*BinaryRational.decode (paramV x))*BinaryRational.decode (distanceWord x)≤
    BinaryRational.decode (paramZ x))
end BinaryOpeningActivity
end
open WordOperations BinaryArithmetic
namespace RationalMin
open WordList
def choose (x : List Bool) : List Bool :=
  if BinaryRational.decode (Find.item x)≤BinaryRational.decode (Fold.accum x)
  then Find.item x else Fold.accum x

def seed (x : List Bool) : List Bool := if x=[] then BinaryRational.encode 0 else WordList.head x
noncomputable def run (x : List Bool) : List Bool :=
  Fold.run choose (3*Polynomial.X+3) (Fold.pack x [] (seed x))
end RationalMin
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

namespace MetricKMedianRecovery.BitMachine.BinaryOpeningNearest
open WordOperations BinaryArithmetic WordList BinaryOpeningActivity
noncomputable def values : List Bool → List Bool := mapWith distanceWord
noncomputable def run : List Bool → List Bool := RationalMin.run ∘ values
end MetricKMedianRecovery.BitMachine.BinaryOpeningNearest
namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace BinaryOpeningPayment
open WordList RationalLinearFeasibility

def paramV (x : List Bool) : ℚ := BinaryRational.decode (itemField 2 x)
def paramZ (x : List Bool) : ℚ := BinaryRational.decode (itemField 3 x)
def scale (x : List Bool) : ℚ := 1-3*paramV x
noncomputable def activityInput (x : List Bool) : List Bool :=
  pairBits (pairBits (pairBits (itemField 0 x,discardPrefix x),
    pairBits (itemField 2 x,itemField 3 x)),itemField 1 x)
noncomputable def nearest (x : List Bool) : ℚ :=
  BinaryRational.decode (BinaryOpeningNearest.run (activityInput x))
noncomputable def distanceWords (x : List Bool) : List Bool :=
  MetricTable.get (pairBits (pairBits (itemField 0 x,itemField 6 x),discardPrefix x))
noncomputable def distance (x : List Bool) : ℚ := BinaryRational.decode (distanceWords x)

noncomputable def input (x : List Bool) : List Bool :=
  pairBits (x,BinaryEllipsoidInitial.indices (field 7 x))
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

def field (k : ℕ) : List Bool → List Bool := BinaryOpeningPayment.field k ∘ discardPrefix
def query (k : ℕ) (x : List Bool) : List Bool := pairBits (extractPrefix x,field k x)
noncomputable def distanceWords (f j : ℕ) (x : List Bool) : List Bool :=
  MetricTable.get (pairBits (pairBits (BinaryOpeningPayment.itemField 0 x,field f x),field j x))
noncomputable def distance (f j : ℕ) (x : List Bool) : ℚ := BinaryRational.decode (distanceWords f j x)
def tag (x : List Bool) : ℕ := value (field 0 x)
noncomputable def near (x : List Bool) : Prop :=
  BinaryOpeningPayment.distance (query 1 x)≤BinaryOpeningPayment.paramV x*BinaryOpeningPayment.paramZ x
noncomputable instance nearDecidable (x : List Bool) : Decidable (near x) :=
  inferInstanceAs (Decidable (_≤_))

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

def col (k : ℕ) : List Bool → List Bool := BinaryOpeningPayment.field k ∘ discardPrefix
def row (k : ℕ) : List Bool → List Bool := BinaryOpeningConstant.field k ∘ extractPrefix

def bid (j : ℕ) (x : List Bool) : ℚ :=
  if value (col 0 x)=0 then if value (col 1 x)=value (row j x) then 1 else 0 else 0
def slack (x : List Bool) : ℚ :=
  if value (col 0 x)=1 then if value (col 1 x)=value (row 2 x) then
    if value (col 2 x)=value (row 3 x) then if value (col 3 x)=value (row 1 x) then 1 else 0 else 0 else 0 else 0
def dual (x : List Bool) : ℚ :=
  if value (col 0 x)=1 then if value (col 1 x)=value (row 2 x) then
    if value (col 2 x)=value (row 1 x) then 1 else 0 else 0 else 0

def paymentQuery (x : List Bool) : List Bool := pairBits (extractPrefix (extractPrefix x),col 1 x)
noncomputable def paymentNear (x : List Bool) : Prop :=
  BinaryOpeningPayment.distance (paymentQuery x)≤
    BinaryOpeningPayment.paramV (paymentQuery x)*BinaryOpeningPayment.paramZ (paymentQuery x)
noncomputable instance paymentNearDecidable (x : List Bool) : Decidable (paymentNear x) := inferInstanceAs (Decidable (_≤_))
end BinaryOpeningCoefficient
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Op2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations
namespace WordList
namespace Flatten

def op (x : List Bool) : List Bool := Fold.accum x++Find.item x
noncomputable def run (x : List Bool) : List Bool := Fold.run op (3*Polynomial.X+3) (Fold.pack x [] [])
end Flatten
noncomputable def flatMapWith (f : List Bool → List Bool) : List Bool → List Bool := Flatten.run ∘ mapWith f
end WordList
end MetricKMedianRecovery.BitMachine
namespace MetricKMedianRecovery.BitMachine
open WordOperations
namespace WordList
noncomputable def crossWith (f : List Bool → List Bool) (x : List Bool) : List Bool :=
  flatMapWith (fun w=>mapWith f (pairBits (discardPrefix w,extractPrefix w)))
    (pairBits (discardPrefix x,extractPrefix x))
noncomputable def cross : List Bool → List Bool := crossWith id
end WordList
end MetricKMedianRecovery.BitMachine

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace WordList
noncomputable def map (f : List Bool → List Bool) (x : List Bool) : List Bool :=
  mapWith (f ∘ discardPrefix) (pairBits ([],x))
end WordList
namespace BinaryOpeningEnumeration
open WordList BinaryOpeningPayment
noncomputable def doubles (x : List Bool) : List Bool := cross (pairBits (clients x,clients x))
noncomputable def triples (x : List Bool) : List Bool := cross (pairBits (field 8 x,doubles x))
noncomputable def caps (x : List Bool) : List Bool := cross (pairBits (clients x,field 1 x))
noncomputable def duals (x : List Bool) : List Bool := cross (pairBits (field 8 x,clients x))

def unaryTag (tag : ℕ) (x : List Bool) : List Bool := encode [tag.bits,x]
def pairTag (tag : ℕ) (x : List Bool) : List Bool := encode [tag.bits,extractPrefix x,discardPrefix x]
def tripleTag (tag : ℕ) (x : List Bool) : List Bool :=
  encode [tag.bits,discardPrefix (discardPrefix x),extractPrefix x,extractPrefix (discardPrefix x)]
def dualTag (x : List Bool) : List Bool := encode [(7:ℕ).bits,discardPrefix x,extractPrefix x]
def variableTag (x : List Bool) : List Bool :=
  encode [(1:ℕ).bits,extractPrefix x,extractPrefix (discardPrefix x),discardPrefix (discardPrefix x)]
noncomputable def kinds (x : List Bool) : List Bool :=
  WordList.map (unaryTag 0) (clients x)++WordList.map (unaryTag 1) (clients x)++
  WordList.map (pairTag 2) (caps x)++WordList.map (unaryTag 3) (clients x)++
  encode [encode [(4:ℕ).bits]]++WordList.map (tripleTag 5) (triples x)++
  WordList.map (tripleTag 6) (triples x)++WordList.map dualTag (duals x)
noncomputable def columns (x : List Bool) : List Bool :=
  WordList.map (unaryTag 0) (clients x)++WordList.map variableTag (triples x)
end BinaryOpeningEnumeration
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

noncomputable def rowInput (x : List Bool) : List Bool := pairBits (x,columns (extractPrefix x))
noncomputable def bound (x : List Bool) : ℚ :=
  (1+BinaryRational.decode (field 2 x)*BinaryRational.decode (field 2 x))*BinaryRational.decode (field 3 x)
end MetricKMedianRecovery.BitMachine.BinaryRawOpening

namespace MetricKMedianRecovery.BitMachine.BinaryPhaseFirst
open WordOperations BinaryArithmetic WordList
open BinaryOpeningPayment

noncomputable def natEq (x : List Bool) : Bool := decide (value (extractPrefix x)=value (discardPrefix x))
end MetricKMedianRecovery.BitMachine.BinaryPhaseFirst

end OAI
end


