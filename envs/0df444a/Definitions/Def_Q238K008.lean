-- Prove2me | Definitions.Def_Q238K008
-- name    : Q238K008
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T23:13:13.524406+00:00
-- url     : https://prove2.me/theorems/6e9c726b-ee7f-41e1-a4aa-2dbc7a358986
-- title:
--   Definitions bundle Q238K008 of the split of OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 154 declarations of OpenAI's Lean: 121 definitions, 2 instances and 31 theorems. The definitions and types are `OAI.MetricKMedianRecovery.BitMachine.BinaryArithmetic.triStacks`, `OAI.MetricKMedianRecovery.BitMachine.BinaryClearRow.boundWords`, `OAI.MetricKMedianRecovery.BitMachine.BinaryClearRow.denOp`, `OAI.MetricKMedianRecovery.BitMachine.BinaryClearRow.denominator`, `OAI.MetricKMedianRecovery.BitMachine.BinaryClearRow.denominators`, `OAI.MetricKMedianRecovery.BitMachine.BinaryClearRow.entries`, `OAI.MetricKMedianRecovery.BitMachine.BinaryClearRow.scalar`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidGrid.col`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidGrid.ctx`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidGrid.diagonal`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidGrid.dim`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidGrid.dimension`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidGrid.entryInput`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidGrid.precision`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidGrid.rest`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidGrid.row`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidGrid.rowInput`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidGrid.runInput`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidGrid.scale`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidGrid.shape`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidInitial.zeroVector`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGCD.firstRem`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningActivity.client`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningActivity.distanceWord`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningActivity.fails`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningActivity.paramV`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningActivity.paramZ`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningActivity.table`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningCoefficient.bid`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningCoefficient.col`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningCoefficient.dual`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningCoefficient.paymentNear`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningCoefficient.paymentQuery`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningCoefficient.row`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningCoefficient.slack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningConstant.distance`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningConstant.distanceWords`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningConstant.field`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningConstant.near`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningConstant.query` and 81 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedianRecovery_Branching_CopyComputes`, `KMedianRecovery_Encoding_Encode2`, `KMedianRecovery_Machines_LoopInput2`, `KMedianRecovery_Recovery_Basic`, `KMedianRecovery_Recovery_Basic2`, `KMedianRecovery_Recovery_BorrowBit`, `KMedianRecovery_Recovery_BoundedDecision`, `KMedianRecovery_Recovery_Computes`, `KMedianRecovery_Recovery_Copies`, `KMedianRecovery_Recovery_GetRow2`, `KMedianRecovery_Recovery_IfNat`, `KMedianRecovery_Recovery_LengthPolynomial`, `KMedianRecovery_Recovery_Normalize`, `KMedianRecovery_Recovery_Op2`, `KMedianRecovery_Recovery_Pack2`, `KMedianRecovery_Recovery_Pack3`, `KMedianRecovery_Recovery_Pack4`, `KMedianRecovery_Recovery_Pack6`, `KMedianRecovery_Recovery_Pack7`, `KMedianRecovery_Recovery_Pack8`, `KMedianRecovery_Recovery_ProcessOutputs`, `KMedianRecovery_Recovery_RowInput`, `KMedianRecovery_Recovery_Step`, `KMedianRecovery_Recovery_Step2`, `KMedianRecovery_Recovery_Value`, `KMedianRecovery_Recovery_Values`.
--
--   **Imports.** It imports the published bundle `Def_KMedianRefinedRecovery`; the bundles `Q238K000`, `Q238K001` and `Q238K002` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q238K018`, `Q238K019`, `Q238K020`, `Q238K021` and `Q238K022`; the statement `OAI.MetricKMedianRecovery.BitMachine.WordList.flatMapWith_typed_s238`.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_KMedianRefinedRecovery
import Definitions.Def_Q238K000
import Definitions.Def_Q238K001
import Definitions.Def_Q238K002

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Value
attribute [-simp] _root_.OAI.MetricKMedianRecovery.BitMachine.BinaryGCD.measure_pack
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open Turing Turing.TM2 StateTransition

namespace BinaryArithmetic

lemma value_add (c : Bool) (xs ys : List Bool) :
    value (add c xs ys)=value xs+value ys+c.toNat := by
  induction xs generalizing c ys with
  | nil =>
    induction ys generalizing c with
    | nil => cases c <;> simp [add,value]
    | cons y ys ih =>
      simp only [add,value,ih]
      have he := fullAdder c false y
      simp only [Bool.toNat_false] at he
      omega
  | cons x xs ih =>
    cases ys with
    | nil =>
      simp only [add,value,ih]
      have he := fullAdder c x false
      simp only [Bool.toNat_false] at he
      omega
    | cons y ys =>
      simp only [add,value,ih]
      have he := fullAdder c x y
      omega

def triStacks (x y z : List Bool) : Stacks (Fin 3) := ![x,y,z]

@[simp] lemma stacks_zero (x y z : List Bool) : triStacks x y z 0=x := rfl
@[simp] lemma stacks_one (x y z : List Bool) : triStacks x y z 1=y := rfl
@[simp] lemma stacks_two (x y z : List Bool) : triStacks x y z 2=z := rfl

end BinaryArithmetic
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Normalize
attribute [-simp] _root_.OAI.MetricKMedianRecovery.BitMachine.BinaryGCD.measure_pack
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open Turing Turing.TM2 StateTransition
namespace BinaryArithmetic

lemma value_append (xs ys : List Bool) : value (xs++ys)=value xs+2^xs.length*value ys := by
  induction xs with
  | nil => simp [value]
  | cons b xs ih => simp only [List.cons_append,value,ih,List.length_cons,pow_succ] <;> ring

lemma value_append_true_pos (xs : List Bool) : 0<value (xs++[true]) := by
  rw [value_append]
  simp only [value,Bool.toNat_true,Nat.mul_zero,Nat.add_zero,Nat.mul_one]
  have hh : 0<2^xs.length := pow_pos (by norm_num) _
  omega

lemma bits_value_append_true (xs : List Bool) : (value (xs++[true])).bits=xs++[true] := by
  induction xs with
  | nil => simp [value]
  | cons b xs ih =>
    simp only [List.cons_append,value]
    have he (n : ℕ) : b.toNat+2*n=Nat.bit b n := by cases b <;> simp [Nat.bit,Nat.add_comm]
    rw [he,Nat.bits_append_bit _ _ (fun h => (value_append_true_pos xs).ne' h |>.elim),ih]

lemma bits_value_reverse (xs : List Bool) :
    (value xs.reverse).bits=(xs.dropWhile (fun b => !b)).reverse := by
  induction xs with
  | nil => simp [value]
  | cons b xs ih =>
    cases b with
    | false => simpa [List.reverse_cons,value_append,value] using ih
    | true => simpa using bits_value_append_true xs.reverse

lemma normalize_eq_bits (xs : List Bool) : normalize xs=(value xs).bits := by
  simpa only [List.reverse_reverse,normalize] using (bits_value_reverse xs.reverse).symm

end BinaryArithmetic
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_BorrowBit
attribute [-simp] _root_.OAI.MetricKMedianRecovery.BitMachine.BinaryGCD.measure_pack
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open Turing Turing.TM2 StateTransition
namespace BinarySubtraction
open BinaryArithmetic

lemma value_lt (xs : List Bool) : value xs<2^xs.length := by
  induction xs with
  | nil => simp [value]
  | cons b xs ih =>
    cases b <;> simp only [value,List.length_cons,pow_succ,Bool.toNat_true,Bool.toNat_false] <;> omega

lemma difference_balance (c : Bool) (xs ys : List Bool) :
    value (difference c xs ys).1+value ys+c.toNat=
      value xs+2^(max xs.length ys.length)*(difference c xs ys).2.toNat := by
  induction xs generalizing c ys with
  | nil =>
    induction ys generalizing c with
    | nil => simp [difference,value]
    | cons y ys ih =>
      have h := ih (borrowBit c false y)
      have hs := fullSubtractor c false y
      simp only [difference,value,List.length_cons,List.length_nil,Nat.zero_max,pow_succ] at ⊢
      simp only [List.length_nil,Nat.zero_max,value,Bool.toNat_false] at h hs
      nlinarith
  | cons x xs ih =>
    cases ys with
    | nil =>
      have h := ih (borrowBit c x false) []
      have hs := fullSubtractor c x false
      simp only [difference,value,List.length_cons,List.length_nil,Nat.max_zero,pow_succ] at ⊢
      simp only [List.length_nil,Nat.max_zero,value,Bool.toNat_false] at h hs
      nlinarith
    | cons y ys =>
      have h := ih (borrowBit c x y) ys
      have hs := fullSubtractor c x y
      simp only [difference,value,List.length_cons,max_add_add_right,pow_succ] at ⊢
      nlinarith

end BinarySubtraction
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Computes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine

section
open Turing
namespace BinarySubtraction
open BinaryArithmetic

lemma bits_eq_nil (n : ℕ) : n.bits=[] ↔ n=0 := by
  constructor
  · intro h
    have hh := value_bits n
    rw [h] at hh
    exact hh.symm
  · rintro rfl
    rfl

end BinarySubtraction
end
open Turing Turing.TM2 StateTransition

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
open BinaryArithmetic BinarySubtraction

def firstRem (x : List Bool) : List Bool := (value (first x)%value (second x)).bits

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

lemma projections_length (xs : List Bool) :
    (extractPrefix xs).length≤xs.length ∧ (discardPrefix xs).length≤xs.length := by
  induction xs using List.twoStepInduction with
  | nil => simp [extractPrefix,discardPrefix]
  | singleton b => cases b <;> simp [extractPrefix,discardPrefix]
  | cons_cons b c xs ih _ => cases b <;> simp only [extractPrefix,discardPrefix,List.length_cons,List.length_nil] <;> omega

end BinaryArithmetic.Multiplication
end
open BinaryArithmetic
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
open BinaryArithmetic
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
open UnaryTake
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
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Copies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open UnaryTake

namespace BoundedIteration

lemma polynomialRun_eq (f : List Bool → List Bool) (Q R : Polynomial ℕ) (x : List Bool)
    (h : ∀ j, j ≤ Q.eval x.length → (f^[j] x).length ≤ R.eval x.length) :
    polynomialRun f Q R x=f^[Q.eval x.length] x :=
  clamp_iterate_eq f (R.eval x.length) (Q.eval x.length) x h
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
open UnaryTake

namespace WordList

lemma length_cons (w ws : List Bool) : (cons w ws).length=2*w.length+ws.length+2 := by
  simp only [cons,List.length_cons,pairBits_length]; omega

namespace ReverseMap

lemma data_next (f : List Bool → List Bool) (x : List Bool) : data (next f x)=data x := by
  unfold next While.next; split_ifs
  · unfold step; split_ifs <;> simp only [data_pack]
  · rfl

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
open BinaryArithmetic
namespace WordList.Lookup

lemma decrement_length (x : List Bool) : (value x-1).bits.length ≤ x.length := by
  rw [Nat.size_eq_bits_len]
  apply Nat.size_le_size (Nat.sub_le _ _) |>.trans
  simpa only [normalize_eq_bits,Nat.size_eq_bits_len] using BinaryDivision.normalize_length x
lemma first_step (x : List Bool) : (extractPrefix (step x)).length ≤ (extractPrefix x).length := by
  unfold step; split_ifs
  · exact le_rfl
  · rw [extractPrefix_pairBits]; exact decrement_length _
end WordList.Lookup
end
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
open BinaryArithmetic
namespace UnaryResources

def triple (x : List Bool) : List Bool := (3*value x).bits
end UnaryResources
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
open BinaryArithmetic
namespace RationalMatrix
open WordList

noncomputable def matrixIndices (x : List Bool) : List Bool := pairBits (x,Indices.run x)
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
open BinaryArithmetic
namespace RationalMatrix
open WordList

def diagInput (x : List Bool) : List Bool := pairBits (x,discardPrefix x)

def contextMatrix (x : List Bool) : List Bool := extractPrefix (extractPrefix x)
def contextIndex (x : List Bool) : List Bool := discardPrefix (extractPrefix x)
def tailDiagInput (x : List Bool) : List Bool := pairBits (contextMatrix x,discardPrefix x)

noncomputable def tailDiagMapInput (x : List Bool) : List Bool :=
  pairBits (x,Indices.run (extractPrefix x))

end RationalMatrix
end MetricKMedianRecovery.BitMachine

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
open BinaryArithmetic
namespace RationalMatrix
open WordList

def loopInput (x : List Bool) : List Bool := pairBits (extractPrefix x,discardPrefix (discardPrefix x))

noncomputable def iterationInput (x : List Bool) : List Bool := Fold.pack (WordList.tail x) x x

noncomputable def signOp : List Bool → List Bool :=
  BinaryRational.negWords ∘ discardPrefix ∘ discardPrefix

noncomputable def signRun : List Bool → List Bool := Fold.run signOp (4*Polynomial.X+4)
end RationalMatrix
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
open BinaryArithmetic
open scoped Matrix
namespace BinaryEllipsoidGrid
open RationalMatrix WordList

def dim : List Bool → List Bool := extractPrefix
def rest : List Bool → List Bool := discardPrefix
def precision : List Bool → List Bool := extractPrefix ∘ rest
def shape : List Bool → List Bool := discardPrefix ∘ rest

def ctx : List Bool → List Bool := extractPrefix ∘ extractPrefix
def row : List Bool → List Bool := discardPrefix ∘ extractPrefix
def col : List Bool → List Bool := discardPrefix

def entryInput (x : List Bool) : List Bool := pairBits (pairBits (shape (ctx x),row x),col x)

def dimension (x : List Bool) : ℚ := value (dim (ctx x))
def scale (x : List Bool) : ℚ := value (precision (ctx x))
def diagonal (x : List Bool) : ℚ := dimension x/scale x

noncomputable def rowInput (x : List Bool) : List Bool := pairBits (x,Indices.run (shape (extractPrefix x)))

noncomputable def runInput (x : List Bool) : List Bool := pairBits (x,Indices.run (shape x))
end BinaryEllipsoidGrid
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
open BinaryArithmetic RationalLinearFeasibility Ellipsoid
namespace BinaryEllipsoidInitial
open RationalMatrix WordList

def zeroVector (x : List Bool) : List Bool := repeatWords (pairBits (x,BinaryRational.encode 0))
end BinaryEllipsoidInitial
end
open BinaryArithmetic RationalLinearFeasibility Ellipsoid
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
open BinaryArithmetic RationalLinearFeasibility Ellipsoid
open UnaryResources
namespace BinaryWeakSolve
open RationalMatrix

def nword : List Bool → List Bool := extractPrefix
def rest₁ : List Bool → List Bool := discardPrefix
def rest₂ : List Bool → List Bool := discardPrefix ∘ rest₁
def rest₃ : List Bool → List Bool := discardPrefix ∘ rest₂
def pword : List Bool → List Bool := extractPrefix ∘ rest₁
def sword : List Bool → List Bool := extractPrefix ∘ rest₂
def radius : List Bool → List Bool := extractPrefix ∘ rest₃
def rows : List Bool → List Bool := discardPrefix ∘ rest₃

def twice (x : List Bool) : List Bool := nword x++nword x
def blocks (x : List Bool) : List Bool :=
  RepeatedAppend.copies (nword x).length (nword x)++
    RepeatedAppend.copies (twice x).length (pword x++sword x)++[true]
def budgetWord (x : List Bool) : List Bool := RepeatedAppend.copies (twice x).length (blocks x)

def radiusSquare (x : List Bool) : List Bool := BinaryRational.encode ((value (radius x):ℚ)*(value (radius x):ℚ))

def centerWords (x : List Bool) : List Bool := BinaryEllipsoidInitial.zeroVector (nword x)
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
open BinaryArithmetic RationalLinearFeasibility Ellipsoid
open WordList RationalMatrix

def entries (x : List Bool) : List Bool := cons (discardPrefix x) (extractPrefix x)
def denOp : List Bool → List Bool := BinaryRational.denominator ∘ discardPrefix
noncomputable def denominators (x : List Bool) : List Bool := mapWith denOp (pairBits ([],entries x))
noncomputable def denominator : List Bool → List Bool := NaturalArray.productWords ∘ denominators
noncomputable def scalar (x : List Bool) : List Bool := BinaryRational.encode (value (denominator x):ℚ)
noncomputable def boundWords (x : List Bool) : List Bool := BinaryRational.encode
  ((value (denominator x):ℚ)*BinaryRational.decode (discardPrefix x))
end BinaryClearRow
namespace BinaryRationalDecision
open BinaryArithmetic RationalLinearFeasibility Ellipsoid
open WordList

def second : List Bool → List Bool := extractPrefix ∘ rest₁
end BinaryRationalDecision

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
open BinaryArithmetic
namespace WordList.Set

def pack (xs j v : List Bool) : List Bool := pairBits (xs,pairBits (j,v))
def target (x : List Bool) : List Bool := extractPrefix (discardPrefix (extractPrefix x))
def replacement (x : List Bool) : List Bool := discardPrefix (discardPrefix (extractPrefix x))
def oldInput (x : List Bool) : List Bool := pairBits (discardPrefix x,extractPrefix (extractPrefix x))
def oldValue (x : List Bool) : List Bool := Lookup.run (oldInput x)

def op (x : List Bool) : List Bool :=
  if value (discardPrefix x)≤value (target x) then
    if value (target x)≤value (discardPrefix x) then replacement x else oldValue x
  else oldValue x

noncomputable def input (x : List Bool) : List Bool := pairBits (x,Indices.run (extractPrefix x))
noncomputable def run (x : List Bool) : List Bool := mapWith op (input x)
end WordList.Set
open BinaryArithmetic
open scoped Matrix
namespace RationalMatrix
open WordList

def cramerOpInput (x : List Bool) : List Bool :=
  Set.pack (extractPrefix (extractPrefix x)) (discardPrefix x) (discardPrefix (extractPrefix x))
noncomputable def cramerInput (x : List Bool) : List Bool := pairBits (x,Indices.run (extractPrefix x))
end RationalMatrix
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
open BinaryArithmetic RationalLinearFeasibility
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
open BinaryArithmetic
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
open BinaryArithmetic WordList BinaryOpeningActivity
noncomputable def values : List Bool → List Bool := mapWith distanceWord
noncomputable def run : List Bool → List Bool := RationalMin.run ∘ values
end MetricKMedianRecovery.BitMachine.BinaryOpeningNearest
namespace MetricKMedianRecovery.BitMachine
open BinaryArithmetic
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
open BinaryArithmetic
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
open BinaryArithmetic
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
namespace WordList
namespace Flatten

def op (x : List Bool) : List Bool := Fold.accum x++Find.item x
noncomputable def run (x : List Bool) : List Bool := Fold.run op (3*Polynomial.X+3) (Fold.pack x [] [])
end Flatten
noncomputable def flatMapWith (f : List Bool → List Bool) : List Bool → List Bool := Flatten.run ∘ mapWith f
end WordList
end MetricKMedianRecovery.BitMachine
namespace MetricKMedianRecovery.BitMachine
namespace WordList
noncomputable def crossWith (f : List Bool → List Bool) (x : List Bool) : List Bool :=
  flatMapWith (fun w=>mapWith f (pairBits (discardPrefix w,extractPrefix w)))
    (pairBits (discardPrefix x,extractPrefix x))
noncomputable def cross : List Bool → List Bool := crossWith id
end WordList
end MetricKMedianRecovery.BitMachine

namespace MetricKMedianRecovery.BitMachine
open BinaryArithmetic
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
open BinaryArithmetic WordList RationalLinearFeasibility
open BinaryOpeningPayment BinaryOpeningEnumeration

noncomputable def rowInput (x : List Bool) : List Bool := pairBits (x,columns (extractPrefix x))
noncomputable def bound (x : List Bool) : ℚ :=
  (1+BinaryRational.decode (field 2 x)*BinaryRational.decode (field 2 x))*BinaryRational.decode (field 3 x)
end MetricKMedianRecovery.BitMachine.BinaryRawOpening

namespace MetricKMedianRecovery.BitMachine.BinaryPhaseFirst
open BinaryArithmetic WordList
open BinaryOpeningPayment

noncomputable def natEq (x : List Bool) : Bool := decide (value (extractPrefix x)=value (discardPrefix x))
end MetricKMedianRecovery.BitMachine.BinaryPhaseFirst

end OAI
end


