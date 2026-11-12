-- Prove2me | Definitions.Def_Q238L016
-- name    : Q238L016
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T11:23:43.226901+00:00
-- url     : https://prove2.me/theorems/7b05ce67-5d62-48a0-a07a-cedc1f62d8a5
-- title:
--   Definitions bundle Q238L016 of the split of OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 90 declarations of OpenAI's Lean: 33 definitions and 57 theorems. The definitions and types are `OAI.MetricKMedianRecovery.BitMachine.BinaryArithmetic.Multiplication.add_cycle`, `OAI.MetricKMedianRecovery.BitMachine.BinaryArithmetic.Multiplication.cfg`, `OAI.MetricKMedianRecovery.BitMachine.BinaryArithmetic.Multiplication.clear_outputs`, `OAI.MetricKMedianRecovery.BitMachine.BinaryArithmetic.Multiplication.done`, `OAI.MetricKMedianRecovery.BitMachine.BinaryArithmetic.Multiplication.mStacks`, `OAI.MetricKMedianRecovery.BitMachine.BinaryArithmetic.Multiplication.parse_phase`, `OAI.MetricKMedianRecovery.BitMachine.BinaryArithmetic.Multiplication.process_outputs`, `OAI.MetricKMedianRecovery.BitMachine.BinaryArithmetic.Multiplication.program`, `OAI.MetricKMedianRecovery.BitMachine.BinaryArithmetic.Multiplication.raw_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryArithmetic.Multiplication.resta_outputs`, `OAI.MetricKMedianRecovery.BitMachine.BinaryArithmetic.Multiplication.resty_outputs`, `OAI.MetricKMedianRecovery.BitMachine.BinaryArithmetic.Multiplication.sum_outputs`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDivision.doubled`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDivision.next`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDivision.nextBit`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDivision.rank`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDivision.rawDivide`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDivision.reduced`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDivision.setupWords`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDivision.step`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDivision.withDivision`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGCD.rank`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGCD.secondRem`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRational.castIntWords`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRational.natWords`, `OAI.MetricKMedianRecovery.BitMachine.BinarySubtraction.cfg`, `OAI.MetricKMedianRecovery.BitMachine.BinarySubtraction.clear_outputs`, `OAI.MetricKMedianRecovery.BitMachine.BinarySubtraction.done`, `OAI.MetricKMedianRecovery.BitMachine.BinarySubtraction.parse_outputs`, `OAI.MetricKMedianRecovery.BitMachine.BinarySubtraction.rev_outputs`, `OAI.MetricKMedianRecovery.BitMachine.BinarySubtraction.subProgram`, `OAI.MetricKMedianRecovery.BitMachine.BinarySubtraction.subtractReverse_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinarySubtraction.sum_outputs`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: [`KMedianRecovery_Encoding_DivNatWords`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Encoding/DivNatWords.lean), [`KMedianRecovery_Machines_SubProgram`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Machines/SubProgram.lean), [`KMedianRecovery_Recovery_DigitBit`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/DigitBit.lean), [`KMedianRecovery_Recovery_Mul`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/Mul.lean), [`KMedianRecovery_Recovery_NumAbs`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/NumAbs.lean), [`KMedianRecovery_Recovery_Pack`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/Pack.lean), [`KMedianRecovery_Recovery_Pack2`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/Pack2.lean), [`KMedianRecovery_Recovery_ProcessOutputs`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/ProcessOutputs.lean).
--
--   **Imports.** It imports the published bundle `Def_KMedianRecovery`; the bundles `Q238L006`, `Q238L007` and `Q238L008` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q238L023` and `Q238L025`.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_KMedianRecovery
import Definitions.Def_Q238L006
import Definitions.Def_Q238L007
import Definitions.Def_Q238L008

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Mul
attribute [-simp] _root_.OAI.MetricKMedianRecovery.BitMachine.BinaryGCD.measure_pack
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open Turing Turing.TM2 StateTransition

namespace BinaryArithmetic

lemma add_length (c : Bool) (xs ys : List Bool) :
    (add c xs ys).length≤xs.length+ys.length+1 := by
  induction xs generalizing c ys with
  | nil =>
    induction ys generalizing c with
    | nil => cases c <;> simp [add]
    | cons y ys ih => simp only [add,List.length_cons,List.length_nil] at ⊢; have hh:=ih (carryBit c false y); simp only [List.length_nil] at hh; omega
  | cons x xs ih =>
    cases ys with
    | nil => simp only [add,List.length_cons,List.length_nil] at ⊢; have hh:=ih (carryBit c x false) []; simp only [List.length_nil] at hh; omega
    | cons y ys => simp only [add,List.length_cons]; have hh:=ih (carryBit c x y) ys; omega

lemma value_mulFrom (xs ys acc : List Bool) :
    value (mulFrom xs ys acc)=2^xs.length*value acc+value xs.reverse*value ys := by
  induction xs generalizing acc with
  | nil => simp [mulFrom,value]
  | cons b xs ih =>
    simp only [mulFrom,ih,List.length_cons,pow_succ,List.reverse_cons,value_append,List.length_reverse]
    cases b <;> simp only [Bool.false_eq_true,ite_false, if_false,ite_true, if_true,value_add,value,Bool.toNat_false,
      Bool.toNat_true,Nat.mul_zero,Nat.add_zero,Nat.zero_add]
    all_goals ring

lemma normalize_mulFrom (xs ys : List Bool) :
    normalize (mulFrom xs.reverse ys [])=(value xs*value ys).bits := by
  rw [normalize_eq_bits,value_mulFrom,List.reverse_reverse,value,Nat.mul_zero,Nat.zero_add]

namespace Multiplication

def mStacks (a b c d e : List Bool) : Stacks (Fin 5) := ![a,b,c,d,e]
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

abbrev program : Program where
  K := Fin 5
  input := 0
  output := 3
  Label := Fin 6
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
          (.push 3 (fun _ => false)
            (.branch (fun s => s.2.1.getD false)
              (.load (fun _ => (false,none,none)) (.goto (fun _ => 2)))
              (.load (fun _ => (false,none,none)) (.goto (fun _ => 1)))))
          (.load (fun _ => (false,none,none)) (.goto (fun _ => 5))))
    else if l=2 then
      .pop 0 (fun s b => (s.1,b,none))
        (.pop 3 (fun s b => (s.1,s.2.1,b))
          (.branch (fun s => s.2.1.isSome || s.2.2.isSome)
            (.branch (fun s => s.2.1.isSome)
              (.push 2 (fun s => s.2.1.getD false)
                (.push 4 (fun s => sumBit s.1 (s.2.1.getD false) (s.2.2.getD false))
                  (.load (fun s => (carryBit s.1 (s.2.1.getD false) (s.2.2.getD false),none,none))
                    (.goto (fun _ => 2)))))
              (.push 4 (fun s => sumBit s.1 false (s.2.2.getD false))
                (.load (fun s => (carryBit s.1 false (s.2.2.getD false),none,none))
                  (.goto (fun _ => 2)))))
            (.branch Prod.fst
              (.push 4 (fun _ => true)
                (.load (fun _ => (false,none,none)) (.goto (fun _ => 3))))
              (.load (fun _ => (false,none,none)) (.goto (fun _ => 3))))))
    else if l=3 then
      .pop 2 (fun s b => (s.1,b,none))
        (.branch (fun s => s.2.1.isSome)
          (.push 0 (fun s => s.2.1.getD false)
            (.load (fun _ => (false,none,none)) (.goto (fun _ => 3))))
          (.load (fun _ => (false,none,none)) (.goto (fun _ => 4))))
    else if l=4 then
      .pop 4 (fun s b => (s.1,b,none))
        (.branch (fun s => s.2.1.isSome)
          (.push 3 (fun s => s.2.1.getD false)
            (.load (fun _ => (false,none,none)) (.goto (fun _ => 4))))
          (.load (fun _ => (false,none,none)) (.goto (fun _ => 1))))
    else
      .pop 0 (fun s b => (s.1,b,none))
        (.branch (fun s => s.2.1.isSome)
          (.load (fun _ => (false,none,none)) (.goto (fun _ => 5)))
          (.load (fun _ => (false,none,none)) .halt))

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
attribute [-simp] _root_.OAI.MetricKMedianRecovery.BitMachine.MapLeft.stacks_left _root_.OAI.MetricKMedianRecovery.BitMachine.MapLeft.stacks_one _root_.OAI.MetricKMedianRecovery.BitMachine.MapLeft.stacks_zero _root_.OAI.MetricKMedianRecovery.BitMachine.discardPrefix_pairBits _root_.OAI.MetricKMedianRecovery.BitMachine.extractPrefix_pairBits _root_.OAI.MetricKMedianRecovery.BitMachine.frameStacks_inl _root_.OAI.MetricKMedianRecovery.BitMachine.frameStacks_inr
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open Turing Turing.TM2 StateTransition
namespace BinarySubtraction
open BinaryArithmetic

abbrev subProgram : Program where
  K := Fin 3
  input := 0
  output := 1
  Label := Fin 4
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
    else if l=2 then
      .pop 2 (fun s b => (s.1,b,none))
        (.pop 0 (fun s b => (s.1,s.2.1,b))
          (.branch (fun s => s.2.1.isSome || s.2.2.isSome)
            (.push 1 (fun s => sumBit s.1 (s.2.1.getD false) (s.2.2.getD false))
              (.load (fun s => (borrowBit s.1 (s.2.1.getD false) (s.2.2.getD false),none,none))
                (.goto (fun _ => 2))))
            (.branch Prod.fst
              (.load (fun _ => (false,none,none)) (.goto (fun _ => 3)))
              (.load (fun _ => (false,none,none)) .halt))))
    else
      .pop 1 (fun s b => (s.1,b,none))
        (.branch (fun s => s.2.1.isSome)
          (.load (fun _ => (false,none,none)) (.goto (fun _ => 3)))
          (.load (fun _ => (false,none,none)) .halt))

def cfg (l : Fin 4) (c : Bool) (x y z : List Bool) : subProgram.machine.Cfg :=
  ⟨some l,(c,none,none),triStacks x y z⟩
def done (ys : List Bool) : subProgram.machine.Cfg :=
  ⟨none,(false,none,none),triStacks [] ys []⟩

lemma sub_initial (xs : List Bool) : initList subProgram.machine xs=cfg 0 false xs [] [] := by
  rw [initList_bool]
  congr 1
  funext i
  fin_cases i <;> simp [subProgram,triStacks]

lemma sub_final (xs : List Bool) : haltList subProgram.machine xs=done xs := by
  rw [haltList_bool]
  congr 1
  funext i
  fin_cases i <;> simp [subProgram,triStacks]

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

lemma clear_nil : subProgram.machine.step (cfg 3 false [] [] [])=some (done []) := by
  simp [FinTM2.step,cfg,done,subProgram,TM2.step,TM2.stepAux,update_one]
  rfl
lemma clear_cons (b : Bool) (xs : List Bool) :
    subProgram.machine.step (cfg 3 false [] (b::xs) [])=some (cfg 3 false [] xs []) := by
  simp [FinTM2.step,cfg,subProgram,TM2.step,TM2.stepAux,update_one]
  rfl

noncomputable def clear_outputs (xs : List Bool) :
    EvalsToInTime subProgram.machine.step (cfg 3 false [] xs []) (some (done [])) (xs.length+1) := by
  induction xs with
  | nil => exact one_step clear_nil
  | cons b xs ih => simpa only [List.length_cons,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using
        (step_then (clear_cons b xs) ih)

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

noncomputable def sum_outputs (c : Bool) (xs ys zs : List Bool) :
    EvalsToInTime subProgram.machine.step (cfg 2 c ys zs xs)
      (some (done (if (difference c xs ys).2 then [] else (difference c xs ys).1.reverse++zs)))
        (2*(xs.length+ys.length)+zs.length+2) := by
  induction xs generalizing c ys zs with
  | nil =>
    induction ys generalizing c zs with
    | nil =>
      cases c with
      | false => simpa only [difference,Bool.false_eq_true,ite_false, if_false,List.reverse_nil,List.nil_append,
          List.length_nil,Nat.add_zero,Nat.mul_zero,Nat.zero_add] using
          time_mono (one_step (sum_nil_false zs)) (by omega : 1≤zs.length+2)
      | true => simpa only [difference,ite_true, if_true,List.length_nil,Nat.add_zero,Nat.mul_zero,Nat.zero_add,
          Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using
          step_then (sum_nil_true zs) (clear_outputs zs)
    | cons y ys ih =>
      have hh := step_then (sum_nil_cons c y ys zs) (ih (borrowBit c false y) (sumBit c false y::zs))
      simp only [difference,List.reverse_cons,List.append_assoc,List.singleton_append] at ⊢
      exact time_mono hh (by simp only [List.length_cons]; omega)
  | cons x xs ih =>
    cases ys with
    | nil =>
      have hh := step_then (sum_cons_nil c x xs zs) (ih (borrowBit c x false) [] (sumBit c x false::zs))
      simp only [difference,List.reverse_cons,List.append_assoc,List.singleton_append] at ⊢
      exact time_mono hh (by simp only [List.length_cons]; omega)
    | cons y ys =>
      have hh := step_then (sum_cons_cons c x y xs ys zs) (ih (borrowBit c x y) ys (sumBit c x y::zs))
      simp only [difference,List.reverse_cons,List.append_assoc,List.singleton_append] at ⊢
      exact time_mono hh (by simp only [List.length_cons]; omega)

noncomputable def rev_outputs (xs ys zs : List Bool) :
    EvalsToInTime subProgram.machine.step (cfg 1 false xs ys zs)
      (some (done ((subtract (ys.reverse++zs) xs).reverse)))
        (3*ys.length+2*zs.length+2*xs.length+3) := by
  induction ys generalizing zs with
  | nil =>
    have hh := step_then (rev_nil xs zs) (sum_outputs false zs xs [])
    simp only [List.reverse_nil,List.nil_append,List.length_nil,Nat.mul_zero,Nat.zero_add]
    dsimp only [subtract]
    split_ifs with hc
    · simpa only [hc,ite_true, if_true,List.reverse_nil] using time_mono hh (by simp only [List.length_nil]; omega)
    · simpa only [hc,Bool.false_eq_true,ite_false, if_false,List.append_nil] using time_mono hh (by simp only [List.length_nil]; omega)
  | cons b ys ih =>
    have hh := step_then (rev_cons b xs ys zs) (ih (b::zs))
    simp only [List.reverse_cons,List.append_assoc,List.singleton_append] at ⊢
    exact time_mono hh (by simp only [List.length_cons]; omega)

noncomputable def parse_outputs (xs ys : List Bool) :
    EvalsToInTime subProgram.machine.step (cfg 0 false xs ys [])
      (some (done ((subtract ((extractPrefix xs).reverse++ys).reverse (discardPrefix xs)).reverse)))
        (4*xs.length+3*ys.length+4) := by
  induction xs using List.twoStepInduction generalizing ys with
  | nil =>
    have hh := step_then (parse_nil ys) (rev_outputs [] ys [])
    simpa only [extractPrefix,discardPrefix,List.reverse_nil,List.nil_append,List.append_nil,
      List.length_nil,Nat.add_zero,Nat.zero_add] using time_mono hh (by simp)
  | singleton b =>
    cases b with
    | false =>
      have hh := step_then (parse_false [] ys) (rev_outputs [] ys [])
      simpa only [extractPrefix,discardPrefix,List.reverse_nil,List.nil_append,List.append_nil,List.length_nil,List.length_singleton] using
        time_mono hh (by simp)
    | true =>
      have hh := step_then (parse_one ys) (rev_outputs [] ys [])
      simpa only [extractPrefix,discardPrefix,List.reverse_nil,List.nil_append,List.append_nil,List.length_nil,List.length_singleton] using
        time_mono hh (by simp)
  | cons_cons b c xs ih _ =>
    cases b with
    | false =>
      have hh := step_then (parse_false (c::xs) ys) (rev_outputs (c::xs) ys [])
      simpa only [extractPrefix,discardPrefix,List.reverse_nil,List.nil_append,List.append_nil] using
        time_mono hh (by simp only [List.length_nil,List.length_cons]; omega)
    | true =>
      have hh := step_then (parse_true c xs ys) (ih (c::ys))
      simp only [extractPrefix,discardPrefix,List.reverse_cons,List.append_assoc,List.singleton_append] at ⊢
      exact time_mono hh (by simp only [List.length_cons]; omega)

noncomputable def subtractReverse_computes : PolyComputes (fun xs =>
    (subtract (extractPrefix xs) (discardPrefix xs)).reverse) where
  program := subProgram
  time := 4*Polynomial.X+4
  outputs xs := by
    simpa only [TM2OutputsInTime,Option.map_some,sub_initial,sub_final,List.append_nil,
      List.reverse_reverse,List.length_nil,Nat.mul_zero,Nat.add_zero,Polynomial.eval_add,
      Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X] using parse_outputs xs []

end BinarySubtraction
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Pack
attribute [-simp] _root_.OAI.MetricKMedianRecovery.BitMachine.BinaryRational.decode_pair _root_.OAI.MetricKMedianRecovery.BitMachine.discardPrefix_pairBits _root_.OAI.MetricKMedianRecovery.BitMachine.extractPrefix_pairBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open Turing
namespace BinaryDivision
open BinaryArithmetic BinarySubtraction WordOperations

@[simp] lemma decode_pack (a : Bool) (d y q r : List Bool) :
    digits (pack a d y q r)=d ∧ divisor (pack a d y q r)=y ∧
    quotient (pack a d y q r)=q ∧ remainder (pack a d y q r)=r := by
  simp only [digits,divisor,quotient,remainder,pack,List.tail_cons,pairBits,
    extractPrefix_pair,discardPrefix_pair,and_self]

@[simp] lemma digits_pack (a : Bool) (d y q r : List Bool) : digits (pack a d y q r)=d :=
  (decode_pack a d y q r).1
@[simp] lemma divisor_pack (a : Bool) (d y q r : List Bool) : divisor (pack a d y q r)=y :=
  (decode_pack a d y q r).2.1
@[simp] lemma quotient_pack (a : Bool) (d y q r : List Bool) : quotient (pack a d y q r)=q :=
  (decode_pack a d y q r).2.2.1
@[simp] lemma remainder_pack (a : Bool) (d y q r : List Bool) : remainder (pack a d y q r)=r :=
  (decode_pack a d y q r).2.2.2

def doubled (x : List Bool) : List Bool := (digits x).head?.getD false :: remainder x
def nextBit (x : List Bool) : Bool := decide (value (divisor x) ≤ value (doubled x))
def reduced (x : List Bool) : List Bool :=
  if nextBit x then normalize (subtract (doubled x) (divisor x)) else doubled x

def step (x : List Bool) : List Bool :=
  if digits x=[] then pack false [] (divisor x) (quotient x) (remainder x)
  else pack true (digits x).tail (divisor x) (nextBit x::quotient x) (reduced x)

def next := While.next step

def rank (x : List Bool) : ℕ := if x.head?=some true then (digits x).length+1 else 0

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

def setupWords (x : List Bool) : List Bool :=
  pack true (extractPrefix x).reverse (discardPrefix x) [] []

def withDivision (x : List Bool) : List Bool := next^[rank (setupWords x)] (setupWords x)

def rawDivide (x : List Bool) : List Bool :=
  pairBits (normalize (quotient (withDivision x)),normalize (remainder (withDivision x)))

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

def secondRem (x : List Bool) : List Bool :=
  (value (second x)%(value (first x)%value (second x))).bits

def rank (x : List Bool) : ℕ := if x.head?=some true then measure x+1 else 0
@[simp] lemma rank_true (a b : List Bool) : rank (pack true a b)=measure (pack true a b)+1 := rfl
@[simp] lemma rank_false (a b : List Bool) : rank (pack false a b)=0 := rfl

lemma measure_bound (x : List Bool) : measure x ≤ 2*x.length := by
  have ha := (ProductBits.projections_length x.tail).1
  have hb := (ProductBits.projections_length x.tail).2
  have hsa := Nat.size_le.mpr (BinarySubtraction.value_lt (first x))
  have hsb := Nat.size_le.mpr (BinarySubtraction.value_lt (second x))
  simp only [first,second] at hsa hsb
  simp only [List.length_tail] at ha hb
  simp only [measure,first,second]
  omega

lemma rank_bound (x : List Bool) : rank x ≤ 2*x.length+1 := by
  have hm := measure_bound x
  unfold rank
  split_ifs <;> omega

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
end
open WordOperations BinaryArithmetic
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

def castIntWords (x : List Bool) : List Bool := pairBits (x,Nat.bits 1)
lemma castIntWords_encode (z : ℤ) : castIntWords (Signed.encode z)=encode (z:ℚ) := by
  simp only [castIntWords,encode,Rat.num_intCast,Rat.den_intCast]

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

def natWords (x : List Bool) : List Bool := castIntWords (Signed.encode (value x:ℤ))
end BinaryRational
end MetricKMedianRecovery.BitMachine

end OAI
end


