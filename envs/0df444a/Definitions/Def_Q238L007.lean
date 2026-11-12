-- Prove2me | Definitions.Def_Q238L007
-- name    : Q238L007
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T11:22:16.658317+00:00
-- url     : https://prove2.me/theorems/7026ba68-d89e-4f47-86be-859d831d37c5
-- title:
--   Definitions bundle Q238L007 of the split of OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 42 declarations of OpenAI's Lean: 7 definitions and 35 theorems. The definitions and types are `OAI.MetricKMedianRecovery.BitMachine.BinaryArithmetic.add`, `OAI.MetricKMedianRecovery.BitMachine.BinaryArithmetic.mulFrom`, `OAI.MetricKMedianRecovery.BitMachine.BinaryArithmetic.triStacks`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDivision.digits`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDivision.divisor`, `OAI.MetricKMedianRecovery.BitMachine.WordSelection.choose`, `OAI.MetricKMedianRecovery.BlueDP.pick`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: [`KMedianRecovery_Branching_BluePlan`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Branching/BluePlan.lean), [`KMedianRecovery_Machines_Program2`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Machines/Program2.lean), [`KMedianRecovery_Recovery_BorrowBit`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/BorrowBit.lean), [`KMedianRecovery_Recovery_Computes`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/Computes.lean), [`KMedianRecovery_Recovery_Copies`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/Copies.lean), [`KMedianRecovery_Recovery_Mul`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/Mul.lean), [`KMedianRecovery_Recovery_Normalize`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/Normalize.lean), [`KMedianRecovery_Recovery_Pack`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/Pack.lean), [`KMedianRecovery_Recovery_ProcessOutputs`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/ProcessOutputs.lean), [`KMedianRecovery_Recovery_Value`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/Value.lean).
--
--   **Imports.** It imports the bundles `Q238L000`, `Q238L001` and `Q238L002` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q238L013`, `Q238L015`, `Q238L016`, `Q238L017` and `Q238L018`.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_Q238L000
import Definitions.Def_Q238L001
import Definitions.Def_Q238L002

section
-- module Solutions.Q238_KM.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
@[simp] theorem fin5_lit_0_3 : ((0 : Fin 5) = 3) ↔ False := by decide
@[simp] theorem fin5_lit_0_4 : ((0 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_1_3 : ((1 : Fin 5) = 3) ↔ False := by decide
@[simp] theorem fin5_lit_1_4 : ((1 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_2_3 : ((2 : Fin 5) = 3) ↔ False := by decide
@[simp] theorem fin5_lit_2_4 : ((2 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_3_0 : ((3 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_3_1 : ((3 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_3_2 : ((3 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_3_4 : ((3 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_4_0 : ((4 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_4_1 : ((4 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_4_2 : ((4 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_4_3 : ((4 : Fin 5) = 3) ↔ False := by decide
end OAICompat434

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open Turing Turing.TM2 StateTransition

namespace BinaryArithmetic

lemma fullAdder (c x y : Bool) :
    (sumBit c x y).toNat+2*(carryBit c x y).toNat=c.toNat+x.toNat+y.toNat := by
  cases c <;> cases x <;> cases y <;> rfl

def add : Bool → List Bool → List Bool → List Bool
  | c,[],[] => if c then [true] else []
  | c,x::xs,[] => sumBit c x false :: add (carryBit c x false) xs []
  | c,[],y::ys => sumBit c false y :: add (carryBit c false y) [] ys
  | c,x::xs,y::ys => sumBit c x y :: add (carryBit c x y) xs ys
termination_by _ xs ys => xs.length+ys.length

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

end BinaryArithmetic
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
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Mul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open Turing Turing.TM2 StateTransition

namespace BinaryArithmetic

def mulFrom : List Bool → List Bool → List Bool → List Bool
  | [],_,acc => acc
  | b::bs,ys,acc => mulFrom bs ys (if b then add false ys (false::acc) else false::acc)

end BinaryArithmetic
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_Program2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open Turing Turing.TM2 StateTransition

namespace While
variable (p : Program)

lemma next_fixed (f : List Bool → List Bool) (x : List Bool) (h : x.head? ≠ some true) (n : ℕ) :
    (next f)^[n] x = x := Function.iterate_fixed (show next f x = x from ite_eq_right h) n

end While

end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_BorrowBit
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

lemma value_subtract (xs ys : List Bool) : value (subtract xs ys)=value xs-value ys := by
  have h := difference_balance false xs ys
  have hb := value_lt (difference false xs ys).1
  rw [difference_length] at hb
  simp only [Bool.toNat_false,Nat.add_zero] at h
  dsimp only [subtract]
  split_ifs with hc
  · simp only [hc,Bool.toNat_true,Nat.mul_one] at h
    simp only [value]
    omega
  · have he : (difference false xs ys).2=false := Bool.eq_false_of_not_eq_true hc
    simp only [he,Bool.toNat_false,Nat.mul_zero,Nat.add_zero] at h
    omega

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
namespace WordSelection

def choose (xs : List Bool) : List Bool :=
  if xs.head?=some true then extractPrefix xs.tail else discardPrefix xs.tail

end WordSelection

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
open BinaryArithmetic BinarySubtraction

def digits (x : List Bool) := extractPrefix x.tail
def divisor (x : List Bool) := extractPrefix (discardPrefix x.tail)

lemma normalize_length (x : List Bool) : (normalize x).length ≤ x.length := by
  simpa only [BinaryArithmetic.normalize,List.length_reverse] using List.length_dropWhile_le (fun b:Bool=>!b) x.reverse

end BinaryDivision
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
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Copies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine

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
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BluePlan
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BlueDP
variable {L R Y : Type*} [LinearOrder L] [LinearOrder R] [LinearOrder Y]
def pick (r0 : R) (y0 : Y) (xs : List (Atom L R Y)) (l : L) : Atom L R Y :=
  (xs.find? (fun a=>a.1=l)).getD (l,r0,y0)
end MetricKMedianRecovery.BlueDP

end OAI
end


