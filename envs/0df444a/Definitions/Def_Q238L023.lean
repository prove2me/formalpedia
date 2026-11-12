-- Prove2me | Definitions.Def_Q238L023
-- name    : Q238L023
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T11:25:17.10314+00:00
-- url     : https://prove2.me/theorems/cd3def0a-88d9-4ff5-b09e-ca88a0c4dd16
-- title:
--   Definitions bundle Q238L023 of the split of OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 96 declarations of OpenAI's Lean: 55 definitions and 41 theorems. The definitions and types are `OAI.MetricKMedianRecovery.BitMachine.BinaryArithmetic.add_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryArithmetic.multiply_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryArithmetic.normalize_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBoundedDecision.rest₁_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBoundedDecision.rest₂_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBoundedDecision.rows_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.rest₁_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.rest₂_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.rest₃_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.rows_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDivision.divide`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDivision.mass`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDivision.normalize_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDivision.pack_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidAdvance.center_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidAdvance.rest₂_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidAdvance.stored_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidCut.rest_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidCut.rest₂_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidCut.rest₃_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidInitial.col_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidRoot.precision_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidRoot.run`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGCD.gcdWords`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGCD.next`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGCD.pack_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGCD.step`, `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseFirst.contains`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRational.castIntWords_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRational.denominator_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRational.leWords`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRational.rightDen_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRationalDecision.rest₁_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRationalDecision.rest₂_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRationalDecision.rows_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRow.bound_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinarySqrt.high_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinarySqrt.startWords_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinarySubtraction.subtract_computes`, `OAI.MetricKMedianRecovery.BitMachine.IntegerArray.prefixEmpty_computes` and 15 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedianRecovery_Branching_CopyComputes`, `KMedianRecovery_Encoding_DivNatWords`, `KMedianRecovery_Encoding_Encode`, `KMedianRecovery_Encoding_Encode2`, `KMedianRecovery_Encoding_Encode3`, `KMedianRecovery_Encoding_OptionEncode`, `KMedianRecovery_Encoding_PushWord`, `KMedianRecovery_Encoding_Words`, `KMedianRecovery_Machines_SubProgram`, `KMedianRecovery_Recovery_BoundedDecision`, `KMedianRecovery_Recovery_DigitBit`, `KMedianRecovery_Recovery_LeftNum`, `KMedianRecovery_Recovery_LengthPolynomial`, `KMedianRecovery_Recovery_MulComputes`, `KMedianRecovery_Recovery_Next`, `KMedianRecovery_Recovery_Normalize`, `KMedianRecovery_Recovery_NumAbs`, `KMedianRecovery_Recovery_Pack`, `KMedianRecovery_Recovery_Pack2`, `KMedianRecovery_Recovery_Pack3`, `KMedianRecovery_Recovery_Pack5`, `KMedianRecovery_Recovery_Pack7`, `KMedianRecovery_Recovery_Pack9`, `KMedianRecovery_Recovery_ProcessOutputs`, `KMedianRecovery_Recovery_RowInput`, `KMedianRecovery_Recovery_Step`, `KMedianRecovery_Recovery_Step2`, `KMedianRecovery_Recovery_Store2`.
--
--   **Imports.** It imports the published bundle `Def_KMedianRecovery`; the bundles `Q238L013`, `Q238L014`, `Q238L015`, `Q238L016` and `Q238L017` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q238L027`, `Q238L028`, `Q238L029` and `Q238L030`; the proofs of `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueBlocks.at_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.RationalMatrix.fold_steps_s238r` and `OAI.MetricKMedianRecovery.BitMachine.RationalMatrix.mulWords_encode_s238r`.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_KMedianRecovery
import Definitions.Def_Q238L013
import Definitions.Def_Q238L014
import Definitions.Def_Q238L015
import Definitions.Def_Q238L016
import Definitions.Def_Q238L017

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
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open Turing Turing.TM2 StateTransition
namespace BinarySubtraction
open BinaryArithmetic

noncomputable def subtract_computes : PolyComputes (fun xs =>
    normalize (subtract (extractPrefix xs) (discardPrefix xs))) :=
  (subtractReverse_computes.comp trim_computes).comp reverse_computes

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
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Store2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open Turing Turing.TM2 StateTransition
namespace WordOperations

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

lemma length_pack (a : Bool) (d y q r : List Bool) :
    (pack a d y q r).length=2*d.length+2*y.length+2*q.length+r.length+4 := by
  simp only [pack,List.length_cons,pairBits_length]
  omega

noncomputable def pack_computes {d y q r : List Bool → List Bool}
    (a : Bool) (hd : PolyComputes d) (hy : PolyComputes y)
    (hq : PolyComputes q) (hr : PolyComputes r) :
    PolyComputes (fun x=>pack a (d x) (y x) (q x) (r x)) := by
  exact (const_computes [a]).append (hd.pair (hy.pair (hq.pair hr)))

lemma reduced_length (x : List Bool) :
    (reduced x).length ≤ (remainder x).length+(divisor x).length+1 := by
  have hn := normalize_length (subtract (doubled x) (divisor x))
  have hs := subtract_length (doubled x) (divisor x)
  have hd : (doubled x).length=(remainder x).length+1 := rfl
  rw [hd] at hs
  unfold reduced
  split_ifs
  · omega
  · simp only [doubled,List.length_cons]; omega

def mass (x : List Bool) : ℕ :=
  (digits x).length+(divisor x).length+(quotient x).length+(remainder x).length

lemma divisor_next (x : List Bool) : divisor (next x)=divisor x := by
  unfold next While.next
  split_ifs
  · unfold step
    split_ifs <;> simp only [divisor_pack]
  · rfl

lemma mass_next (x : List Bool) : mass (next x) ≤ mass x+(divisor x).length+2 := by
  unfold next While.next
  split_ifs
  · unfold step
    split_ifs with h
    · simp only [mass,digits_pack,divisor_pack,quotient_pack,remainder_pack,List.length_nil]
      omega
    · have hr := reduced_length x
      simp only [mass,digits_pack,divisor_pack,quotient_pack,remainder_pack,List.length_cons,
        List.length_tail]
      omega
  · omega

lemma length_next (x : List Bool) :
    (next x).length ≤ max x.length (2*mass (next x)+4) := by
  unfold next While.next
  split_ifs
  · unfold step
    split_ifs <;> simp only [length_pack,mass,digits_pack,divisor_pack,quotient_pack,
      remainder_pack,List.length_nil,List.length_cons,List.length_tail] <;> omega
  · exact Nat.le_max_left _ _

lemma rank_next (x : List Bool) : rank (next x) ≤ rank x-1 := by
  unfold next While.next
  split_ifs with hx
  · unfold step
    split_ifs with hd
    · simp only [rank,pack,List.head?_cons,Option.some.injEq,Bool.false_eq_true,ite_false, if_false]
      exact Nat.zero_le _
    · have hh : (pack true (digits x).tail (divisor x) (nextBit x::quotient x) (reduced x)).head?=some true := rfl
      simp only [rank,hh,ite_true, if_true,digits_pack,hx,List.length_tail]
      have hp : 0<(digits x).length := List.length_pos_iff.mpr hd
      omega
  · simp only [rank,hx,ite_false, if_false,Nat.zero_sub,Nat.le_refl]

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

lemma iterate_bounds (x : List Bool) (j : ℕ) :
    divisor (next^[j] x)=divisor x ∧
    mass (next^[j] x) ≤ mass x+j*((divisor x).length+2) ∧
    (next^[j] x).length ≤ x.length+2*mass x+2*j*((divisor x).length+2)+4 ∧
    rank (next^[j] x) ≤ rank x-j := by
  induction j with
  | zero => simp only [Function.iterate_zero_apply,Nat.zero_mul,Nat.add_zero,Nat.sub_zero,
      Nat.le_refl,true_and,and_true]; omega
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    have hd := divisor_next (next^[j] x)
    have hm := mass_next (next^[j] x)
    have hl := length_next (next^[j] x)
    have hr := rank_next (next^[j] x)
    rw [ih.1] at hd hm
    refine ⟨hd,?_,?_,?_⟩
    · nlinarith [ih.2.1]
    · apply hl.trans
      apply max_le
      · nlinarith [ih.2.2.1]
      · nlinarith [ih.2.1]
    · omega

lemma stop (x : List Bool) : (next^[rank x] x).head?≠some true := by
  have hh := (iterate_bounds x (rank x)).2.2.2
  simp only [Nat.sub_self,Nat.le_zero] at hh
  intro hp
  change (if (next^[rank x] x).head?=some true then (digits (next^[rank x] x)).length+1 else 0)=0 at hh
  rw [ite_eq_left hp] at hh
  omega

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

lemma next_pack_nil (y q r : List Bool) :
    next (pack true [] y q r)=pack false [] y q r := by
  change step (pack true [] y q r)=_
  simp only [step,digits_pack,divisor_pack,quotient_pack,remainder_pack,ite_true, if_true]

lemma next_pack_cons (b : Bool) (ds y q r : List Bool) :
    next (pack true (b::ds) y q r)=
      pack true ds y (digitBit b y r::q) (digitRem b y r) := by
  change step (pack true (b::ds) y q r)=_
  simp only [step,digits_pack,divisor_pack,quotient_pack,remainder_pack,List.cons_ne_nil,
    ite_false, if_false,List.tail_cons,nextBit,doubled,List.head?_cons,Option.getD_some,reduced,
    digitRem,digitBit]
  rfl

lemma iterate_pack (ds y q r : List Bool) :
    next^[ds.length+1] (pack true ds y q r)=
      pack false [] y (process ds y q r).1 (process ds y q r).2 := by
  induction ds generalizing q r with
  | nil => exact next_pack_nil y q r
  | cons b ds ih =>
    simp only [List.length_cons,Function.iterate_succ_apply,next_pack_cons,process]
    exact ih _ _

lemma rank_pack (ds y q r : List Bool) : rank (pack true ds y q r)=ds.length+1 := by
  have h : (pack true ds y q r).head?=some true := rfl
  simp only [BinaryDivision.rank,h,ite_true, if_true,digits_pack]

noncomputable def normalize_computes : PolyComputes BinaryArithmetic.normalize :=
  (reverse_computes.comp trim_computes).comp reverse_computes

def divide (x : List Bool) : List Bool :=
  if value (discardPrefix x)=0 then pairBits ([],normalize (extractPrefix x)) else rawDivide x

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

noncomputable def pack_computes {f g : List Bool → List Bool} (b : Bool)
    (hf : PolyComputes f) (hg : PolyComputes g) : PolyComputes (fun x=>pack b (f x) (g x)) :=
  (const_computes [b]).append (hf.pair hg)

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

section
open Turing Turing.TM2 StateTransition
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

noncomputable def add {f g : List Bool → List Bool} (hf : PolyComputes f) (hg : PolyComputes g) :
    PolyComputes (fun x=>(value (f x)+value (g x)).bits) := by
  have hh := (hf.pair hg).comp BinaryArithmetic.add_computes
  simpa only [Function.comp_def,pairBits,extractPrefix_pair,discardPrefix_pair,normalize_eq_bits,value_add,Bool.toNat_false,Nat.add_zero] using hh

noncomputable def sub {f g : List Bool → List Bool} (hf : PolyComputes f) (hg : PolyComputes g) :
    PolyComputes (fun x=>(value (f x)-value (g x)).bits) := by
  have hh := (hf.pair hg).comp BinarySubtraction.subtract_computes
  simpa only [Function.comp_def,pairBits,extractPrefix_pair,discardPrefix_pair,
    normalize_eq_bits,BinarySubtraction.value_subtract] using hh

noncomputable def mul {f g : List Bool → List Bool} (hf : PolyComputes f) (hg : PolyComputes g) :
    PolyComputes (fun x=>(value (f x)*value (g x)).bits) := by
  have hh := (hf.pair hg).comp multiply_computes
  simpa only [Function.comp_def,pairBits,extractPrefix_pair,discardPrefix_pair,normalize_mulFrom] using hh

end NatOps
namespace Signed

lemma pack_bits (s : Bool) (n : ℕ) : pack s n.bits=encode (signed s n) := by
  simp only [pack,value_bits,normalize_eq_bits]
  cases s <;> by_cases hn : n=0 <;> simp [signed,encode,hn]; omega

noncomputable def sign_computes : PolyComputes (fun x=>[sign x]) := head_computes

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

noncomputable def denominator_computes : PolyComputes denominator := discardPrefix_computes

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

noncomputable def rightDen_computes : PolyComputes rightDen := discardPrefix_computes.comp denominator_computes

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

namespace WordList

noncomputable def cons_computes {h t : List Bool → List Bool} (hh : PolyComputes h) (ht : PolyComputes t) :
    PolyComputes (fun x=>cons (h x) (t x)) := (hh.pair ht).comp (prefix_computes true)

namespace ReverseMap

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

lemma iterate_bounds {f : List Bool → List Bool} (hf : PolyComputes f) (x : List Bool) (j : ℕ) :
    (counter ((next f)^[j] x)).length ≤ (counter x).length ∧ data ((next f)^[j] x)=data x ∧
    (output ((next f)^[j] x)).length ≤ (output x).length+j*growth hf.lengthPolynomial x ∧
    ((next f)^[j] x).length ≤ x.length+2*(counter x).length+2*(data x).length+(output x).length+
      j*growth hf.lengthPolynomial x+3 ∧ rank ((next f)^[j] x) ≤ rank x-j := by
  induction j with
  | zero => simp only [Function.iterate_zero_apply,Nat.sub_zero,Nat.le_refl,Nat.zero_mul,
      Nat.add_zero,true_and,and_true]; omega
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    have hc := counter_next f ((next f)^[j] x)
    have hd := data_next f ((next f)^[j] x)
    have ho := output_next hf ((next f)^[j] x)
    have hl := length_next f ((next f)^[j] x)
    have hr := rank_next f ((next f)^[j] x)
    rw [ih.2.1] at hd ho
    have hm := polynomial_monotone hf.lengthPolynomial
      (Nat.add_le_add_left ih.1 (2*(data x).length+1))
    dsimp only at hm
    have hog : (output (next f ((next f)^[j] x))).length ≤
        (output ((next f)^[j] x)).length+growth hf.lengthPolynomial x := by unfold growth; omega
    refine ⟨hc.trans ih.1,hd,?_,?_,?_⟩
    · nlinarith [ih.2.2.1]
    · apply hl.trans; apply max_le
      · nlinarith [ih.2.2.2.1]
      · rw [hd]; nlinarith [ih.1,ih.2.2.1]
    · omega
lemma stop {f : List Bool → List Bool} (hf : PolyComputes f) (x : List Bool) :
    ((next f)^[rank x] x).head?≠some true := by
  have hh := (iterate_bounds hf x (rank x)).2.2.2.2
  simp only [Nat.sub_self,Nat.le_zero] at hh
  intro hp
  change (if ((next f)^[rank x] x).head?=some true then _ else 0)=0 at hh
  rw [ite_eq_left hp] at hh; omega
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

noncomputable def accum_computes : PolyComputes accum := discardPrefix_computes.comp discardPrefix_computes
noncomputable def pack_computes {w c a : List Bool → List Bool} (hw : PolyComputes w)
    (hc : PolyComputes c) (ha : PolyComputes a) : PolyComputes (fun x=>pack (w x) (c x) (a x)) :=
  hw.pair (hc.pair ha)

end Fold
end WordList
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
noncomputable def inc_computes : PolyComputes inc := by
  change PolyComputes (fun x=>(value x+1).bits)
  have hh := NatOps.add id_computes (const_computes (1:ℕ).bits)
  simpa only [inc,Function.comp_def,id_eq,value_bits] using hh
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
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_Encode2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace RationalArray
noncomputable def sumInput_computes : PolyComputes sumInput :=
  WordList.Fold.pack_computes id_computes (const_computes []) (const_computes (BinaryRational.encode 0))
end RationalArray
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

noncomputable def high_computes : PolyComputes high := discardPrefix_computes.comp discardPrefix_computes

noncomputable def startWords_computes : PolyComputes startWords := by
  have hs := NatOps.add id_computes (const_computes (Nat.bits 1))
  have hh := id_computes.pair ((const_computes []).pair hs)
  change PolyComputes (fun x => pairBits (x,pairBits ([],(value x+1).bits)))
  simpa only [value_bits,id_eq] using hh
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

noncomputable def precision_computes : PolyComputes precision := discardPrefix_computes

noncomputable def run : List Bool → List Bool := BinaryRational.reduce ∘ rawWords
end BinaryEllipsoidRoot
open WordOperations BinaryArithmetic
open scoped Matrix
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
noncomputable def const (r : ℚ) : PolyComputes (fun _ : List Bool=>encode r) := const_computes (encode r)
end RatOps
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

noncomputable def rest_computes : PolyComputes rest := discardPrefix_computes
noncomputable def rest₂_computes : PolyComputes rest₂ := rest_computes.comp discardPrefix_computes
noncomputable def rest₃_computes : PolyComputes rest₃ := rest₂_computes.comp discardPrefix_computes
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

section
open WordOperations
namespace WordList.Find

noncomputable def accum_computes : PolyComputes accum := discardPrefix_computes.comp discardPrefix_computes

end WordList.Find
end
open WordOperations BinaryArithmetic RationalLinearFeasibility
namespace BinaryRow
open RationalMatrix

noncomputable def bound_computes : PolyComputes bound := discardPrefix_computes.comp discardPrefix_computes
end BinaryRow
namespace BinaryEllipsoidAdvance
open Ellipsoid RationalMatrix
open scoped Matrix

noncomputable def rest₂_computes : PolyComputes rest₂ := discardPrefix_computes.comp discardPrefix_computes
noncomputable def stored_computes : PolyComputes stored := rest₂_computes.comp discardPrefix_computes
noncomputable def center_computes : PolyComputes center := stored_computes.comp discardPrefix_computes
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

noncomputable def col_computes : PolyComputes col := discardPrefix_computes

end BinaryEllipsoidInitial
end
open WordOperations BinaryArithmetic RationalLinearFeasibility Ellipsoid
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_Encode3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace NaturalArray
open WordList
noncomputable def nextOp_computes : PolyComputes nextOp := discardPrefix_computes.comp UnaryResources.inc_computes
end NaturalArray
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

noncomputable def rest₁_computes : PolyComputes rest₁ := discardPrefix_computes
noncomputable def rest₂_computes : PolyComputes rest₂ := rest₁_computes.comp discardPrefix_computes
noncomputable def rest₃_computes : PolyComputes rest₃ := rest₂_computes.comp discardPrefix_computes
noncomputable def rows_computes : PolyComputes rows := rest₃_computes.comp discardPrefix_computes
end BinaryDecision
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

noncomputable def rest₁_computes : PolyComputes rest₁ := discardPrefix_computes
noncomputable def rest₂_computes : PolyComputes rest₂ := rest₁_computes.comp discardPrefix_computes
noncomputable def rows_computes : PolyComputes rows := rest₂_computes.comp discardPrefix_computes
end BinaryBoundedDecision
namespace BinaryRationalDecision
open WordOperations BinaryArithmetic RationalLinearFeasibility Ellipsoid
open WordList

noncomputable def rest₁_computes : PolyComputes rest₁ := discardPrefix_computes
noncomputable def rest₂_computes : PolyComputes rest₂ := rest₁_computes.comp discardPrefix_computes
noncomputable def rows_computes : PolyComputes rows := rest₂_computes.comp discardPrefix_computes
end BinaryRationalDecision

open WordOperations
namespace WordList
namespace Count
noncomputable def op_computes : PolyComputes op := Fold.accum_computes.comp (prefix_computes true)
end Count
end WordList
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

namespace MetricKMedianRecovery.BitMachine.BinaryPhaseFirst
open WordOperations BinaryArithmetic WordList
open BinaryOpeningPayment

noncomputable def contains (x : List Bool) : Bool := decide (Find.run natEq x≠[])
end MetricKMedianRecovery.BitMachine.BinaryPhaseFirst

end OAI
end


