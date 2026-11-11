-- Prove2me | Definitions.Def_Q238K019
-- name    : Q238K019
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T23:15:42.639503+00:00
-- url     : https://prove2.me/theorems/4a505afc-f176-4735-bc30-201276af99ad
-- title:
--   Definitions bundle Q238K019 of the split of OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 79 declarations of OpenAI's Lean: 31 definitions and 48 theorems. The definitions and types are `OAI.MetricKMedianRecovery.BitMachine.BinaryArithmetic.Multiplication.program`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDelete.extended`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDelete.openSet`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDelete.retained`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidRoot.run`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.alphabet`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.union`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGCD.gcdWords`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGCD.next`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGCD.step`, `OAI.MetricKMedianRecovery.BitMachine.BinaryLabel.rawRow`, `OAI.MetricKMedianRecovery.BitMachine.BinaryLabel.row`, `OAI.MetricKMedianRecovery.BitMachine.BinaryLabel.sort`, `OAI.MetricKMedianRecovery.BitMachine.BinaryLabelMatrix.entry`, `OAI.MetricKMedianRecovery.BitMachine.BinaryLabelMatrix.row`, `OAI.MetricKMedianRecovery.BitMachine.BinaryLabelMatrix.run`, `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseCount.contextAt`, `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseCount.start`, `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseCount.zeroBudget`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRational.ceilWords`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRational.floorWords`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRational.leWords`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRationalSort.sort`, `OAI.MetricKMedianRecovery.BitMachine.BinarySubtraction.cfg`, `OAI.MetricKMedianRecovery.BitMachine.BinarySubtraction.done`, `OAI.MetricKMedianRecovery.BitMachine.BinarySubtraction.subProgram`, `OAI.MetricKMedianRecovery.BitMachine.Signed.divNatWords`, `OAI.MetricKMedianRecovery.BitMachine.WordList.Sort.insert`, `OAI.MetricKMedianRecovery.BitMachine.WordList.Sort.op`, `OAI.MetricKMedianRecovery.BitMachine.WordList.Sort.run`, `OAI.MetricKMedianRecovery.BitMachine.WordList.filterWith`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedianRecovery_Encoding_DivNatWords`, `KMedianRecovery_Encoding_LabelOrder`, `KMedianRecovery_Encoding_NatWords`, `KMedianRecovery_Encoding_RationalSort`, `KMedianRecovery_Machines_DeleteFold`, `KMedianRecovery_Machines_FiniteMachine`, `KMedianRecovery_Machines_SubProgram`, `KMedianRecovery_Recovery_BorrowBit`, `KMedianRecovery_Recovery_DigitBit`, `KMedianRecovery_Recovery_FilterItem`, `KMedianRecovery_Recovery_FinishPhase`, `KMedianRecovery_Recovery_FiniteContext`, `KMedianRecovery_Recovery_LeftNum`, `KMedianRecovery_Recovery_LengthPolynomial`, `KMedianRecovery_Recovery_Mul`, `KMedianRecovery_Recovery_MulComputes`, `KMedianRecovery_Recovery_Next`, `KMedianRecovery_Recovery_NumAbs`, `KMedianRecovery_Recovery_Pack`, `KMedianRecovery_Recovery_Pack2`, `KMedianRecovery_Recovery_ProcessOutputs`, `KMedianRecovery_Recovery_RawSlices`, `KMedianRecovery_Recovery_SortMath`, `KMedianRecovery_Recovery_Step2`.
--
--   **Imports.** It imports the published bundle `Def_KMedianRefinedRecovery`; the bundles `Q238K006`, `Q238K007`, `Q238K008`, `Q238K009` and `Q238K010` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q238K024`, `Q238K025` and `Q238K026`; the statements `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.union_list_pack_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryLabelSelect_run_pack_s238`, `OAI_MetricKMedianRecovery_EffectiveOpenability_storedOpening_none_iff_s238`, `OAI_MetricKMedianRecovery_LocalSearch_executableAnchorFuel_spec_s238`, `OAI_MetricKMedianRecovery_LocalSearch_executableRefineFuel_spec_s238` and `OAI_MetricKMedianRecovery_RationalLinearFeasibility_storedForms_complete_s238`; the proofs of `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueBlocks.at_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidAdvance.found_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.union_list_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningPayment.sumWords_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.RationalMatrix.fold_steps_s238`, `OAI.MetricKMedianRecovery.BitMachine.RationalMatrix.mulWords_encode_s238`, `OAI_MetricKMedianRecovery_EffectiveOpenability_storedOpening_none_iff_s238`, `OAI_MetricKMedianRecovery_LocalSearch_executableAnchorFuel_spec_s238`, `OAI_MetricKMedianRecovery_LocalSearch_executableRefineFuel_spec_s238` and `OAI_MetricKMedianRecovery_RationalLinearFeasibility_storedForms_complete_s238`.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_KMedianRefinedRecovery
import Definitions.Def_Q238K006
import Definitions.Def_Q238K007
import Definitions.Def_Q238K008
import Definitions.Def_Q238K009
import Definitions.Def_Q238K010

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

end Multiplication
end BinaryArithmetic
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
-- module Solutions.Q238_KM.KMedianRecovery_Machines_SubProgram
attribute [-simp] _root_.OAI.MetricKMedianRecovery.BitMachine.MapLeft.stacks_left _root_.OAI.MetricKMedianRecovery.BitMachine.MapLeft.stacks_one _root_.OAI.MetricKMedianRecovery.BitMachine.MapLeft.stacks_zero
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

lemma projection_bounds (x : List Bool) :
    (digits x).length ≤ x.length ∧ (divisor x).length ≤ x.length ∧
    (quotient x).length ≤ x.length ∧ (remainder x).length ≤ x.length := by
  have h0 : x.tail.length ≤ x.length := by simp only [List.length_tail]; omega
  have h1 := ProductBits.projections_length x.tail
  have h2 := ProductBits.projections_length (discardPrefix x.tail)
  have h3 := ProductBits.projections_length (discardPrefix (discardPrefix x.tail))
  dsimp only [digits,divisor,quotient,remainder]
  omega

lemma rank_bound (x : List Bool) : rank x ≤ x.length+1 := by
  have h := (projection_bounds x).1
  unfold rank
  split_ifs <;> omega

end BinaryDivision
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_DigitBit
attribute [-simp] _root_.OAI.MetricKMedianRecovery.BitMachine.BinaryGCD.measure_pack
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open Turing
namespace BinaryDivision
open BinaryArithmetic BinarySubtraction WordOperations

lemma evalMSB_eq (ds : List Bool) (a : ℕ) :
    evalMSB ds a=2^ds.length*a+value ds.reverse := by
  induction ds generalizing a with
  | nil => simp [evalMSB,value]
  | cons b ds ih =>
    simp only [evalMSB,ih,List.length_cons,pow_succ,List.reverse_cons,value_append,
      List.length_reverse,value,Nat.mul_zero,Nat.add_zero]
    ring

lemma digit_balance (b : Bool) (y q r : List Bool) (hr : value r < value y) :
    value (digitBit b y r::q)*value y+value (digitRem b y r)=
      2*(value q*value y+value r)+b.toNat ∧
    value (digitRem b y r)<value y := by
  have hb : b.toNat ≤ 1 := by cases b <;> decide
  have htwo : value (b::r)<2*value y := by simp only [value]; omega
  by_cases h : value y ≤ value (b::r)
  · have ht : digitBit b y r=true := by simp only [digitBit,h,decide_true]
    have he := Nat.sub_add_cancel h
    simp only [value] at he htwo
    simp only [digitRem,ht,ite_true, if_true,normalize_eq_bits,value_bits,
      value_subtract,value,Bool.toNat_true]
    constructor <;> nlinarith
  · have ht : digitBit b y r=false := by simp only [digitBit,h,decide_false]
    have hl : value (b::r)<value y := Nat.lt_of_not_ge h
    simp only [value] at hl
    simp only [digitRem,ht,Bool.false_eq_true,ite_false, if_false,value,
      Bool.toNat_false,Nat.zero_add]
    constructor
    · ring
    · exact hl

lemma process_spec (ds y q r : List Bool) (hr : value r<value y) :
    value (process ds y q r).1*value y+value (process ds y q r).2=
      evalMSB ds (value q*value y+value r) ∧
    value (process ds y q r).2<value y := by
  induction ds generalizing q r with
  | nil => exact ⟨rfl,hr⟩
  | cons b ds ih =>
    have hb := digit_balance b y q r hr
    have hh := ih (digitBit b y r::q) (digitRem b y r) hb.2
    simpa only [process,evalMSB,hb.1] using hh

lemma divide_pair (x y : List Bool) :
    divide (pairBits (x,y))=pairBits ((value x/value y).bits,(value x%value y).bits) := by
  have ep : extractPrefix (pairBits (x,y))=x := extractPrefix_pair x y
  have er : discardPrefix (pairBits (x,y))=y := discardPrefix_pair x y
  by_cases hy : value y=0
  · simp only [divide,er,ep,hy,ite_true, if_true,Nat.div_zero,show Nat.bits 0=[] from rfl,Nat.mod_zero,normalize_eq_bits]
  · have hpos : 0<value y := Nat.pos_of_ne_zero hy
    have hs := process_spec x.reverse y [] [] hpos
    simp only [evalMSB_eq,List.reverse_reverse,value,Nat.zero_mul,Nat.mul_zero,Nat.zero_add] at hs
    have hdiv : value x/value y=value (process x.reverse y [] []).1 := by
      apply Nat.div_eq_of_lt_le
      · omega
      · nlinarith [hs.2]
    have hmod : value x%value y=value (process x.reverse y [] []).2 := by
      have hd := Nat.mod_add_div (value x) (value y)
      rw [hdiv] at hd
      nlinarith [hs.1]
    simp only [divide,er,hy,ite_false, if_false,rawDivide,withDivision,setupWords,ep,rank_pack,
      iterate_pack,quotient_pack,remainder_pack,normalize_eq_bits,hdiv,hmod]

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

def step (x : List Bool) : List Bool :=
  if value (second x)=0 then pack false (normalize (first x)) []
  else if value (first x)%value (second x)=0 then pack false (normalize (second x)) []
  else pack true (firstRem x) (secondRem x)

def next := While.next step

lemma step_bounds (x : List Bool) :
    measure (step x) ≤ measure x ∧ rank (step x) ≤ measure x ∧
    (step x).length ≤ 2*measure x+2 := by
  unfold step
  split_ifs with hy hz
  · simp only [measure_pack,normalize_eq_bits,value_bits,value,Nat.size_zero,Nat.add_zero,
      rank_false,length_pack,Nat.size_eq_bits_len,List.length_nil]
    simp only [measure]
    omega
  · simp only [measure_pack,normalize_eq_bits,value_bits,value,Nat.size_zero,Nat.add_zero,
      rank_false,length_pack,Nat.size_eq_bits_len,List.length_nil]
    simp only [measure]
    omega
  · have hh := second_mod_size_drop (value (first x)) (value (second x))
      (Nat.pos_of_ne_zero hy) (Nat.pos_of_ne_zero hz)
    simp only [rank_true,length_pack,firstRem,secondRem,measure,first_pack,second_pack,value_bits,Nat.size_eq_bits_len]
    omega

lemma gcd_step (x : List Bool) :
    Nat.gcd (value (first (step x))) (value (second (step x)))=
      Nat.gcd (value (first x)) (value (second x)) := by
  have h1 := Nat.gcd_rec (value (second x)) (value (first x))
  have h2 := Nat.gcd_rec (value (first x)%value (second x)) (value (second x))
  unfold step
  split_ifs with hy hz
  · simp only [first_pack,second_pack,normalize_eq_bits,value_bits,value,hy,Nat.gcd_zero_right]
  · simp only [first_pack,second_pack,normalize_eq_bits,value_bits,value,Nat.gcd_zero_right]
    rw [hz,Nat.gcd_zero_left] at h1
    exact h1.symm.trans (Nat.gcd_comm _ _)
  · simp only [first_pack,second_pack,firstRem,secondRem,value_bits]
    exact (Nat.gcd_comm _ _).trans (h2.symm.trans (h1.symm.trans (Nat.gcd_comm _ _)))

lemma step_good (x : List Bool) : Good (step x) := by
  unfold step
  split_ifs
  · exact Or.inr (by simp only [second_pack,value])
  · exact Or.inr (by simp only [second_pack,value])
  · exact Or.inl rfl

lemma next_bounds (x : List Bool) :
    measure (next x) ≤ measure x ∧ rank (next x) ≤ rank x-1 ∧
    (next x).length ≤ max x.length (2*measure x+2) := by
  unfold next While.next
  split_ifs with hx
  · have hh := step_bounds x
    change measure (step x) ≤ measure x ∧ rank (step x) ≤ (if x.head?=some true then measure x+1 else 0)-1 ∧ _
    rw [ite_eq_left hx]
    exact ⟨hh.1,by simpa using hh.2.1,hh.2.2.trans (Nat.le_max_right _ _)⟩
  · have hr : rank x=0 := ite_eq_right hx
    exact ⟨le_rfl,by simp only [hr,Nat.zero_sub,Nat.le_refl],Nat.le_max_left _ _⟩

lemma gcd_next (x : List Bool) :
    Nat.gcd (value (first (next x))) (value (second (next x)))=
      Nat.gcd (value (first x)) (value (second x)) := by
  unfold next While.next
  split_ifs
  · exact gcd_step x
  · rfl
lemma good_next (x : List Bool) (h : Good x) : Good (next x) := by
  unfold next While.next
  split_ifs
  · exact step_good x
  · exact h

lemma iterate_bounds (x : List Bool) (n : ℕ) :
    measure (next^[n] x) ≤ measure x ∧ rank (next^[n] x) ≤ rank x-n ∧
    (next^[n] x).length ≤ max x.length (2*measure x+2) := by
  induction n with
  | zero => simp only [Function.iterate_zero_apply,Nat.sub_zero,Nat.le_refl,true_and]; exact Nat.le_max_left _ _
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    have hh := next_bounds (next^[n] x)
    refine ⟨hh.1.trans ih.1,by omega,?_⟩
    apply hh.2.2.trans
    apply max_le ih.2.2
    apply le_trans _ (Nat.le_max_right _ _)
    omega

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
lemma stop (x : List Bool) : (next^[rank x] x).head?≠some true := by
  have hh := (iterate_bounds x (rank x)).2.1
  simp only [Nat.sub_self,Nat.le_zero] at hh
  intro h
  change (if (next^[rank x] x).head?=some true then measure (next^[rank x] x)+1 else 0)=0 at hh
  rw [ite_eq_left h] at hh
  omega

lemma loop_correct (a b : List Bool) :
    value (first (next^[rank (pack true a b)] (pack true a b)))=Nat.gcd (value a) (value b) := by
  have hh (n : ℕ) : Good (next^[n] (pack true a b)) ∧
      Nat.gcd (value (first (next^[n] (pack true a b))))
        (value (second (next^[n] (pack true a b))))=Nat.gcd (value a) (value b) := by
    induction n with
    | zero => exact ⟨Or.inl rfl,by simp only [Function.iterate_zero_apply,first_pack,second_pack]⟩
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact ⟨good_next _ ih.1,(gcd_next _).trans ih.2⟩
  obtain ⟨hg,he⟩ := hh (rank (pack true a b))
  have hz := hg.resolve_left (stop (pack true a b))
  simpa only [hz,Nat.gcd_zero_right] using he

def gcdWords (x : List Bool) : List Bool :=
  normalize (first (next^[rank (pack true (extractPrefix x) (discardPrefix x))]
    (pack true (extractPrefix x) (discardPrefix x))))

lemma gcdWords_pair (a b : List Bool) : gcdWords (pairBits (a,b))=(Nat.gcd (value a) (value b)).bits := by
  simp only [gcdWords,pairBits,extractPrefix_pair,discardPrefix_pair,normalize_eq_bits,loop_correct]

end BinaryGCD
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_ProcessOutputs
attribute [-simp] _root_.OAI.MetricKMedianRecovery.BitMachine.BinaryRational.decode_pair _root_.OAI.MetricKMedianRecovery.BitMachine.BinaryRational.numerator_encode _root_.OAI.MetricKMedianRecovery.BitMachine.Signed.natAbs_signed _root_.OAI.MetricKMedianRecovery.BitMachine.Signed.sign_encode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine

open WordOperations BinaryArithmetic
namespace Signed

lemma pack_bits (s : Bool) (n : ℕ) : pack s n.bits=encode (signed s n) := by
  simp only [pack,value_bits,normalize_eq_bits]
  cases s <;> by_cases hn : n=0 <;> simp [signed,encode,hn]; omega

end Signed
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_MulComputes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace BinaryRational

lemma reduce_correct (x : List Bool) : reduce x=encode (decode x) := by
  let s := Signed.sign (numerator x)
  let n := Signed.mag (numerator x)
  let d := value (denominator x)
  have hn : Signed.decode (numerator x)=Signed.signed s n := rfl
  by_cases hd : d=0
  · simp only [reduce,show value (denominator x)=0 from hd,ite_true, if_true,decode,Rat.mkRat_zero]
  · have hn' : (mkRat (Signed.signed s n) d).num=Signed.signed s (n/Nat.gcd n d) := by
      rw [Rat.num_mkRat,ite_eq_right hd,Signed.natAbs_signed,Nat.gcd_comm,
        Signed.signed_div_nat s n (Nat.gcd n d) (Nat.gcd_dvd_left n d)]
    have hd' : (mkRat (Signed.signed s n) d).den=d/Nat.gcd n d := by
      rw [Rat.den_mkRat,ite_eq_right hd,Signed.natAbs_signed,Nat.gcd_comm]
    change (if d=0 then _ else _)=_
    rw [ite_eq_right hd]
    simp only [reduceNonzero,divisor,value_bits]
    change pairBits (Signed.pack s (n/(Nat.gcd n d)).bits,(d/(Nat.gcd n d)).bits)=_
    rw [Signed.pack_bits]
    change _=pairBits (Signed.encode (mkRat (Signed.signed s n) d).num,
      (mkRat (Signed.signed s n) d).den.bits)
    rw [hn',hd']

end BinaryRational
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

lemma addWords_pair (x y : ℚ) : addWords (pairBits (encode x,encode y))=encode (x+y) := by
  have h := Rat.mkRat_add_mkRat x.num y.num x.den_nz y.den_nz
  simp only [Rat.mkRat_self] at h
  simp only [addWords,Function.comp_apply,reduce_correct,rawAdd,leftNum,rightNum,leftDen,rightDen,
    extractPrefix_pairBits,discardPrefix_pairBits,numerator_encode,denominator_encode,
    Signed.encode_decode,value_bits,decode_pair]
  change encode (mkRat (x.num*(y.den:ℤ)+y.num*(x.den:ℤ)) (x.den*y.den))=encode (x+y)
  rw [← h]

lemma mulWords_pair (x y : ℚ) : mulWords (pairBits (encode x,encode y))=encode (x*y) := by
  simp only [mulWords,Function.comp_apply,reduce_correct,rawMul,leftNum,rightNum,leftDen,rightDen,
    extractPrefix_pairBits,discardPrefix_pairBits,numerator_encode,denominator_encode,
    Signed.encode_decode,value_bits,decode_pair]
  rw [← Rat.mul_eq_mkRat]

def leWords (x : List Bool) : List Bool :=
  [decide (Signed.decode (leftNum x)*(value (rightDen x):ℤ) ≤
    Signed.decode (rightNum x)*(value (leftDen x):ℤ))]
lemma leWords_pair (x y : ℚ) : leWords (pairBits (encode x,encode y))=[decide (x≤y)] := by
  simp only [leWords,leftNum,rightNum,leftDen,rightDen,extractPrefix_pairBits,discardPrefix_pairBits,
    numerator_encode,denominator_encode,Signed.encode_decode,value_bits,Rat.le_iff]

end BinaryRational
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
namespace Signed

def divNatWords (x : List Bool) : List Bool :=
  if value (discardPrefix x)=0 then encode 0
  else if sign (extractPrefix x) then
    if mag (extractPrefix x)%value (discardPrefix x)=0 then
      pack true (mag (extractPrefix x)/value (discardPrefix x)).bits
    else pack true (mag (extractPrefix x)/value (discardPrefix x)+1).bits
  else pack false (mag (extractPrefix x)/value (discardPrefix x)).bits

lemma divNatWords_spec (x : List Bool) : divNatWords x=
    encode (decode (extractPrefix x)/(value (discardPrefix x):ℤ)) := by
  change _=encode (signed (sign (extractPrefix x)) (mag (extractPrefix x))/_)
  rw [signed_ediv_nat]
  unfold divNatWords
  split_ifs <;> simp only [pack_bits]

end Signed
namespace BinaryRational

def floorWords : List Bool → List Bool := Signed.divNatWords
lemma floorWords_encode (x : ℚ) : floorWords (encode x)=Signed.encode (⌊x⌋:ℤ) := by
  simp only [floorWords,Signed.divNatWords_spec,encode,extractPrefix_pairBits,discardPrefix_pairBits,
    Signed.encode_decode,value_bits,Rat.floor_def']

def ceilWords : List Bool → List Bool := (fun x=>Signed.encode (-Signed.decode x)) ∘ floorWords ∘ negWords
lemma ceilWords_encode (x : ℚ) : ceilWords (encode x)=Signed.encode (⌈x⌉:ℤ) := by
  simp only [ceilWords,Function.comp_apply,negWords_encode,floorWords_encode,Signed.encode_decode,
    Int.floor_neg,neg_neg]

end BinaryRational
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

namespace WordList

lemma head_length (x : List Bool) : (head x).length ≤ x.length := by
  have h := (ProductBits.projections_length x.tail).1
  simp only [List.length_tail] at h
  exact h.trans (Nat.sub_le _ _)
lemma tail_length (x : List Bool) : (tail x).length ≤ x.length-1 := by
  simpa only [tail,List.length_tail] using (ProductBits.projections_length x.tail).2

namespace ReverseMap

lemma counter_next (f : List Bool → List Bool) (x : List Bool) :
    (counter (next f x)).length ≤ (counter x).length := by
  unfold next While.next; split_ifs
  · unfold step; split_ifs
    · simp only [counter_pack,List.length_nil,Nat.zero_le]
    · simp only [counter_pack]; exact (tail_length _).trans (Nat.sub_le _ _)
  · exact le_rfl
lemma length_next (f : List Bool → List Bool) (x : List Bool) :
    (next f x).length ≤ max x.length
      (2*(counter (next f x)).length+2*(data (next f x)).length+(output (next f x)).length+3) := by
  unfold next While.next; split_ifs
  · unfold step; split_ifs <;> simp only [length_pack,counter_pack,data_pack,output_pack] <;> omega
  · exact Nat.le_max_left _ _
lemma rank_next (f : List Bool → List Bool) (x : List Bool) : rank (next f x) ≤ rank x-1 := by
  unfold next While.next; split_ifs with hx
  · unfold step
    by_cases hc : counter x=[]
    · rw [ite_eq_left hc]
      simp only [rank,head_pack,Option.some.injEq,Bool.false_eq_true,ite_false, if_false,Nat.zero_le]
    · rw [ite_eq_right hc]
      have hp := List.length_pos_iff.mpr hc
      have ht := tail_length (counter x)
      simp only [rank,head_pack,ite_true, if_true,counter_pack,hx]
      omega
  · simp only [rank,hx,ite_false, if_false,Nat.zero_sub,Nat.le_refl]

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
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Next
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace BinarySqrt

lemma run_bits (n : ℕ) : run n.bits=(Nat.sqrt n).bits := by
  rw [run,startWords_bits,BoundedIteration.polynomialRun_eq]
  · rw [iterate_pack]
    simp only [low,pack,discardPrefix_pairBits,extractPrefix_pairBits]
    congr 1
    apply interval_correct
    have hp := length_pack n 0 (n+1)
    simp only [pack] at hp
    simp only [Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one]
    omega
  · intro j _
    have hh := iterate_length n j
    simp only [Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_add,
      Polynomial.eval_X,Polynomial.eval_one,length_pack]
    omega
end BinarySqrt
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
namespace BinaryEllipsoidRoot

noncomputable def run : List Bool → List Bool := BinaryRational.reduce ∘ rawWords
lemma run_encode (q : ℚ) (D : ℕ) : run (pairBits (BinaryRational.encode q,D.bits))=
    BinaryRational.encode (Ellipsoid.rationalRootUpper D q) := by
  simp only [run,Function.comp_apply,rawWords,upper,denom,radicand,numAbs,den,precision,
    BinaryRational.encode,extractPrefix_pairBits,discardPrefix_pairBits,Signed.encode,
    List.tail_cons,value_bits,BinarySqrt.run_bits]
  rw [BinaryRational.reduce_correct]
  change BinaryRational.encode (BinaryRational.decode (pairBits
    (Signed.encode (((Nat.sqrt (q.num.natAbs*q.den*(D*D))+1):ℕ):ℤ),
      (q.den*D).bits)))=BinaryRational.encode _
  rw [BinaryRational.decode_pair,Rat.mkRat_eq_div]
  congr 1
  simp only [Ellipsoid.rationalRootUpper,Ellipsoid.sqrtUpperFraction,pow_two,Int.cast_natCast]

end BinaryEllipsoidRoot
open WordOperations BinaryArithmetic
open scoped Matrix
namespace BinaryRational

lemma subWords_pair (a b : ℚ) : subWords (pairBits (encode a,encode b))=encode (a-b) := by
  simp only [subWords,Function.comp_apply,subInput,extractPrefix_pairBits,discardPrefix_pairBits,
    negWords_encode,addWords_pair,sub_eq_add_neg]
end BinaryRational
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_NatWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace Signed
lemma natWords_eq (x : List Bool) : natWords x=(decode x).toNat.bits := by
  cases h : sign x <;> simp [natWords,decode,h,normalize_eq_bits,mag]
lemma natWords_encode (z : ℤ) : natWords (encode z)=z.toNat.bits := by
  rw [natWords_eq,encode_decode]
end Signed
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
namespace WordList
noncomputable def filterWith (p : List Bool → Bool) : List Bool → List Bool := flatMapWith (filterItem p)
end WordList
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

noncomputable def insert (p : List Bool → Bool) (x : List Bool) : List Bool :=
  filterWith (reverseTest p) x ++ cons (extractPrefix x) (filterWith p x)

variable {α : Type*} [LinearOrder α]

noncomputable def op (p : List Bool → Bool) (x : List Bool) : List Bool :=
  insert p (pairBits (Find.item x,Fold.accum x))

noncomputable def run (p : List Bool → Bool) (x : List Bool) : List Bool :=
  Fold.run (op p) (3*Polynomial.X+3) (Fold.pack x [] [])
end WordList.Sort
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_LabelOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryLabel
open WordOperations BinaryArithmetic RationalLeaves

noncomputable def sort : List Bool → List Bool := WordList.Sort.run lt
noncomputable def rawRow (x : List Bool) : List Bool :=
  MetricTable.get (pairBits (pairBits (table x,parentWords (label x)),col x))
attribute [local irreducible] MetricTable.get
noncomputable def row (x : List Bool) : List Bool :=
  BinaryRational.encode (BinaryRational.decode (rawRow x)+max (BinaryRational.decode (heightWords (label x))) 0)
end MetricKMedianRecovery.BitMachine.BinaryLabel

namespace MetricKMedianRecovery.BitMachine.BinaryLabelMatrix
open WordOperations WordList RationalLeaves
attribute [local irreducible] mapWith

noncomputable def entry (x : List Bool) : List Bool :=
  BinaryLabel.row (pairBits (pairBits (table x,item x),col x))

noncomputable def row (x : List Bool) : List Bool :=
  mapWith entry (pairBits (x,BinaryEllipsoidInitial.indices (discardPrefix (extractPrefix x))))

noncomputable def run : List Bool → List Bool := mapWith row
end MetricKMedianRecovery.BitMachine.BinaryLabelMatrix

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_FinishPhase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryPhaseCount
open WordOperations BinaryArithmetic WordList BinaryPhaseUpdate BinaryOpeningPayment
attribute [local irreducible] WordList.map WordList.Indices.run WordList.Lookup.run
  WordList.Fold.run
noncomputable def contextAt (x : List Bool) : List Bool := encode
  [cf 0 x,cf 1 x,cf 2 x,discardPrefix x,cf 4 x,cf 5 x,cf 6 x,cf 7 x,cf 8 x]
noncomputable def zeroBudget : List Bool → List Bool :=
  WordList.map (fun _=>BinaryRational.encode 0) ∘ BinaryOpeningEnumeration.clients
noncomputable def start (x : List Bool) : List Bool :=
  pairBits (contextAt x,zeroBudget (extractPrefix x))
end MetricKMedianRecovery.BitMachine.BinaryPhaseCount

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
noncomputable def alphabet (x : List Bool) : List Bool :=
  BinaryLabel.sort (field 2 x++field 3 x++field 4 x)
attribute [local irreducible] BinaryLabelMatrix.run
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

namespace MetricKMedianRecovery.BitMachine.BinaryFiniteContext
open WordOperations WordList RationalLeaves
open BinaryOpeningPayment (field )

noncomputable def union (x : List Bool) : List Bool := BinaryLabel.sort (extractPrefix x++discardPrefix x)
end MetricKMedianRecovery.BitMachine.BinaryFiniteContext

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_RationalSort
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRationalSort
open WordOperations WordList BinaryArithmetic

noncomputable def sort : List Bool→List Bool := Sort.run lt
attribute [local irreducible] sort
end MetricKMedianRecovery.BitMachine.BinaryRationalSort

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
open WordOperations WordList RationalLeaves
open BinaryFiniteContext (labels )
open BinaryOpeningPayment (field )

noncomputable def retained (x : List Bool) : List Bool := cf 1 x++rest x++WordList.cons (cf 2 x) (sf 1 x)
noncomputable def openSet (x : List Bool) : List Bool :=
  BinaryFiniteContext.union (pairBits (field 3 (cf 0 x),retained x))
noncomputable def extended (x : List Bool) : List Bool :=
  BinaryFiniteContext.replaceOpen (pairBits (cf 0 x,openSet x))
end MetricKMedianRecovery.BitMachine.BinaryDelete

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_RawSlices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.RawDrop
open WordOperations BinaryArithmetic
lemma decrement_length (x : List Bool) : (value x-1).bits.length ≤ x.length := by
  rw [Nat.size_eq_bits_len]
  apply Nat.size_le_size (Nat.sub_le _ _) |>.trans
  simpa only [normalize_eq_bits,Nat.size_eq_bits_len] using BinaryDivision.normalize_length x
lemma first_step (x : List Bool) : (extractPrefix (step x)).length ≤ (extractPrefix x).length := by
  unfold step; split_ifs
  · exact le_rfl
  · rw [extractPrefix_pairBits]; exact decrement_length _
lemma length_step (x : List Bool) : (step x).length ≤ max x.length
    (2*(extractPrefix x).length+1+(discardPrefix x).length) := by
  unfold step; split_ifs
  · exact Nat.le_max_left _ _
  · rw [pairBits_length]
    dsimp only
    have hi := decrement_length (extractPrefix x)
    have hl : (discardPrefix x).tail.length ≤ (discardPrefix x).length := by simp only [List.length_tail]; omega
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

end MetricKMedianRecovery.BitMachine.RawDrop

end OAI
end


