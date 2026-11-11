-- Prove2me | Definitions.Def_Q238K028
-- name    : Q238K028
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T23:22:53.622353+00:00
-- url     : https://prove2.me/theorems/40f54c97-ecd5-4bf7-ba54-11ada48d6b4c
-- title:
--   Definitions bundle Q238K028 of the split of OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 125 declarations of OpenAI's Lean: 123 definitions and 2 theorems. The definitions and types are `OAI.MetricKMedianRecovery.BitMachine.BinaryBoundedDecision.bound_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBoundedDecision.coeffAbs_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBoundedDecision.coeffSum_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBoundedDecision.heightSum_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBoundedDecision.height_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBoundedDecision.mword_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBoundedDecision.numAbsOp_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBoundedDecision.numAbs_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBoundedDecision.nword_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBoundedDecision.padRowOp_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBoundedDecision.padRow_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBoundedDecision.paddedRows_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBoundedDecision.prepared_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBoundedDecision.rest₁_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBoundedDecision.rest₂_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBoundedDecision.rowHeightOp_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBoundedDecision.rowHeight_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBoundedDecision.rowHeights_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBoundedDecision.rows_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.base_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.boundOp_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.bound_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.boundedWords_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.boxShape_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.boxWords_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.count_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.dim_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.doubledGap_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.factorial_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.gap_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.height_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.mword_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.nextDim_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.nword_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.power_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.precisionArg_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.precision_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.radiusPrecision_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.radius_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.rest₁_computes` and 83 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedianRecovery_Branching_CopyComputes`, `KMedianRecovery_Encoding_Encode`, `KMedianRecovery_Encoding_Encode3`, `KMedianRecovery_Encoding_OptionEncode`, `KMedianRecovery_Machines_SubProgram`, `KMedianRecovery_Recovery_BoundOp`, `KMedianRecovery_Recovery_BoundedDecision`, `KMedianRecovery_Recovery_Computes`, `KMedianRecovery_Recovery_DigitBit`, `KMedianRecovery_Recovery_FaceSelection`, `KMedianRecovery_Recovery_LeftNum`, `KMedianRecovery_Recovery_LengthPolynomial`, `KMedianRecovery_Recovery_MulComputes`, `KMedianRecovery_Recovery_Op`, `KMedianRecovery_Recovery_Op2`, `KMedianRecovery_Recovery_Pack`, `KMedianRecovery_Recovery_Pack2`, `KMedianRecovery_Recovery_Pack7`, `KMedianRecovery_Recovery_Pack9`, `KMedianRecovery_Recovery_ProcessOutputs`, `KMedianRecovery_Recovery_Rectangular`, `KMedianRecovery_Recovery_RowInput`, `KMedianRecovery_Recovery_Step2`, `KMedianRecovery_Recovery_Values`.
--
--   **Imports.** It imports the published bundle `Def_KMedianRefinedRecovery`; the bundles `Q238K024` and `Q238K025` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q238K032`, `Q238K033`, `Q238K034` and `Q238K035`; the statements `OAI_MetricKMedianRecovery_BitMachine_BinaryCategorical_choices_pack_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryCategorical_step_pack_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryJump_expand_pack_s238` and `OAI_MetricKMedianRecovery_BitMachine_BinaryPhaseAdvance_run_pack_s238`; the proofs of `OAI_MetricKMedianRecovery_BitMachine_BinaryCategorical_choices_pack_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryCategorical_step_pack_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryJump_expand_pack_s238` and `OAI_MetricKMedianRecovery_BitMachine_BinaryPhaseAdvance_run_pack_s238`.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_KMedianRefinedRecovery
import Definitions.Def_Q238K024
import Definitions.Def_Q238K025

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_SubProgram
attribute [-simp] _root_.OAI.MetricKMedianRecovery.BitMachine.discardPrefix_pairBits _root_.OAI.MetricKMedianRecovery.BitMachine.extractPrefix_pairBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open Turing Turing.TM2 StateTransition
namespace BinarySubtraction
open BinaryArithmetic

noncomputable def clear_outputs (xs : List Bool) :
    EvalsToInTime subProgram.machine.step (cfg 3 false [] xs []) (some (done [])) (xs.length+1) := by
  induction xs with
  | nil => exact one_step clear_nil
  | cons b xs ih => simpa only [List.length_cons,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using
        (step_then (clear_cons b xs) ih)

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

noncomputable def subtract_computes : PolyComputes (fun xs =>
    normalize (subtract (extractPrefix xs) (discardPrefix xs))) :=
  (subtractReverse_computes.comp trim_computes).comp reverse_computes

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

noncomputable def le_computes : PolyComputes (fun xs=>
    [decide (value (extractPrefix xs)≤value (discardPrefix xs))]) := by
  have hh := subtract_computes.comp isEmpty_computes
  simpa only [Function.comp_def,normalize_eq_bits,value_subtract,bits_eq_nil,
    Nat.sub_eq_zero_iff_le] using hh

end BinarySubtraction
end
open Turing Turing.TM2 StateTransition

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

noncomputable def digits_computes : PolyComputes digits :=
  tail_computes.comp extractPrefix_computes
noncomputable def divisor_computes : PolyComputes divisor :=
  (tail_computes.comp discardPrefix_computes).comp extractPrefix_computes
noncomputable def quotient_computes : PolyComputes quotient :=
  ((tail_computes.comp discardPrefix_computes).comp discardPrefix_computes).comp extractPrefix_computes
noncomputable def remainder_computes : PolyComputes remainder :=
  ((tail_computes.comp discardPrefix_computes).comp discardPrefix_computes).comp discardPrefix_computes

noncomputable def doubled_computes : PolyComputes doubled := by
  exact (digits_computes.comp head_computes).append remainder_computes
noncomputable def nextBit_computes : PolyComputes (fun x=>[nextBit x]) := by
  have hh := (divisor_computes.pair doubled_computes).comp le_computes
  simpa only [Function.comp_def,pairBits,extractPrefix_pair,discardPrefix_pair,nextBit] using hh
noncomputable def reduced_computes : PolyComputes reduced := by
  have hh := (doubled_computes.pair divisor_computes).comp subtract_computes
  simp only [Function.comp_def,pairBits,extractPrefix_pair,discardPrefix_pair] at hh
  exact nextBit_computes.cond hh doubled_computes

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

noncomputable def setupWords_computes : PolyComputes setupWords :=
  pack_computes true (extractPrefix_computes.comp reverse_computes) discardPrefix_computes
    (const_computes []) (const_computes [])

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

noncomputable def first_computes : PolyComputes first := tail_computes.comp extractPrefix_computes
noncomputable def second_computes : PolyComputes second := tail_computes.comp discardPrefix_computes

end BinaryGCD
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_ProcessOutputs
attribute [-simp] _root_.OAI.MetricKMedianRecovery.BitMachine.BinaryRational.decode_pair _root_.OAI.MetricKMedianRecovery.BitMachine.BinaryRational.numerator_encode _root_.OAI.MetricKMedianRecovery.BitMachine.Signed.natAbs_signed _root_.OAI.MetricKMedianRecovery.BitMachine.Signed.sign_encode _root_.OAI.MetricKMedianRecovery.BitMachine.discardPrefix_pairBits _root_.OAI.MetricKMedianRecovery.BitMachine.extractPrefix_pairBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine

open WordOperations BinaryArithmetic
namespace NatOps

noncomputable def sub {f g : List Bool → List Bool} (hf : PolyComputes f) (hg : PolyComputes g) :
    PolyComputes (fun x=>(value (f x)-value (g x)).bits) := by
  have hh := (hf.pair hg).comp BinarySubtraction.subtract_computes
  simpa only [Function.comp_def,pairBits,extractPrefix_pair,discardPrefix_pair,
    normalize_eq_bits,BinarySubtraction.value_subtract] using hh

noncomputable def le {f g : List Bool → List Bool} (hf : PolyComputes f) (hg : PolyComputes g) :
    PolyComputes (fun x=>[decide (value (f x)≤value (g x))]) := by
  have hh := (hf.pair hg).comp BinarySubtraction.le_computes
  simpa only [Function.comp_def,pairBits,extractPrefix_pair,discardPrefix_pair] using hh

end NatOps
namespace Signed

noncomputable def sign_computes : PolyComputes (fun x=>[sign x]) := head_computes

noncomputable def neg_computes : PolyComputes (fun x=>encode (-decode x)) := by
  have hm := tail_computes.comp normalize_computes
  have ha := pack_computes (const_computes [false]) hm
  have hb := pack_computes (const_computes [true]) hm
  have hh := sign_computes.cond ha hb
  have he : (fun x=>if sign x then pack false (normalize x.tail) else pack true (normalize x.tail)) =
      (fun x=>encode (-decode x)) := by
    funext x
    cases h : sign x <;> simp only [h,Bool.false_eq_true,ite_false, if_false,ite_true, if_true,normalize_eq_bits,pack_bits,signed,decode,mag,neg_neg]
  rw [← he]
  exact hh

noncomputable def add_computes : PolyComputes (fun x=>
    encode (decode (extractPrefix x)+decode (discardPrefix x))) := by
  let l := extractPrefix_computes
  let r := discardPrefix_computes
  let sl := l.comp sign_computes
  let sr := r.comp sign_computes
  let al := l.comp tail_computes
  let ar := r.comp tail_computes
  have hs := NatOps.add al ar
  have hab := NatOps.sub al ar
  have hba := NatOps.sub ar al
  have hle := NatOps.le al ar
  have hdiff := hle.cond (pack_computes sr hba) (pack_computes sl hab)
  have hsum := pack_computes sl hs
  have ha := sr.cond hsum hdiff
  have hb := sr.cond hdiff hsum
  have hh := sl.cond ha hb
  have he (x : List Bool) :
      encode (decode (extractPrefix x)+decode (discardPrefix x)) =
      if sign (extractPrefix x) then
        if sign (discardPrefix x) then pack (sign (extractPrefix x)) (mag (extractPrefix x)+mag (discardPrefix x)).bits
        else if mag (extractPrefix x)≤ mag (discardPrefix x) then
          pack (sign (discardPrefix x)) (mag (discardPrefix x)-mag (extractPrefix x)).bits
        else pack (sign (extractPrefix x)) (mag (extractPrefix x)-mag (discardPrefix x)).bits
      else if sign (discardPrefix x) then
        if mag (extractPrefix x)≤ mag (discardPrefix x) then
          pack (sign (discardPrefix x)) (mag (discardPrefix x)-mag (extractPrefix x)).bits
        else pack (sign (extractPrefix x)) (mag (extractPrefix x)-mag (discardPrefix x)).bits
      else pack (sign (extractPrefix x)) (mag (extractPrefix x)+mag (discardPrefix x)).bits := by
    change encode (signed (sign (extractPrefix x)) _ + signed (sign (discardPrefix x)) _)=_
    rw [signed_add]
    cases hl : sign (extractPrefix x) <;> cases hr : sign (discardPrefix x) <;>
      simp only [Bool.false_eq_true,Bool.true_eq_false,ite_false, if_false,ite_true, if_true,pack_bits] <;>
      (try split_ifs) <;> rfl
  simp_rw [he]
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  dsimp [mag,Function.comp_def]
  simp only [decide_eq_true_eq]
  rfl

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
namespace Signed

noncomputable def neg {f : List Bool → List Bool} (hf : PolyComputes f) :
    PolyComputes (fun x=>encode (-decode (f x))) := hf.comp neg_computes

end Signed
namespace BinaryRational

noncomputable def numerator_computes : PolyComputes numerator := extractPrefix_computes
noncomputable def denominator_computes : PolyComputes denominator := discardPrefix_computes

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

noncomputable def negWords_computes : PolyComputes negWords :=
  (Signed.neg numerator_computes).pair denominator_computes
noncomputable def rawInv_computes : PolyComputes rawInv := by
  have hs := numerator_computes.comp Signed.sign_computes
  have hd := denominator_computes.comp BinaryArithmetic.normalize_computes
  have hn := (numerator_computes.comp tail_computes).comp BinaryArithmetic.normalize_computes
  have hh := (Signed.pack_computes hs hd).pair hn
  unfold rawInv Signed.mag
  simpa only [Function.comp_def,normalize_eq_bits] using hh

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

namespace ReverseMap

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
noncomputable def loop_computes {f : List Bool → List Bool} (hf : PolyComputes f) :
    PolyComputes (fun x=>(next f)^[rank x] x) := by
  let P := hf.lengthPolynomial
  apply (step_computes hf).whileLoop rank (Polynomial.X+1)
    ((Polynomial.X+1)*(2*(P.comp (3*Polynomial.X+1))+2)+6*Polynomial.X+3)
  · intro x
    have h := (projection_bounds x).1
    simp only [Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one]
    unfold rank; split_ifs <;> omega
  · intro x j hj
    have h := (iterate_bounds hf x j).2.2.2.1
    obtain ⟨hc,hd,ho⟩ := projection_bounds x
    have hr : rank x ≤ x.length+1 := by unfold rank; split_ifs <;> omega
    have hm := polynomial_monotone P (show 2*(data x).length+1+(counter x).length ≤ 3*x.length+1 by omega)
    dsimp only at hm
    have hg : growth P x ≤ 2*P.eval (3*x.length+1)+2 := by unfold growth; omega
    have hjg := Nat.mul_le_mul (hj.trans hr) hg
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,
      Polynomial.eval_one,Polynomial.eval_comp]
    change ((next f)^[j] x).length ≤ _
    change _ ≤ x.length+2*(counter x).length+2*(data x).length+(output x).length+j*growth P x+3 at h
    omega
  · exact stop hf

noncomputable def run_computes {f : List Bool → List Bool} (hf : PolyComputes f) : PolyComputes (run f) :=
  ((pack_computes true discardPrefix_computes extractPrefix_computes (const_computes [])).comp
    (loop_computes hf)).comp output_computes
end ReverseMap

noncomputable def reverse_computes : PolyComputes reverse :=
  ((const_computes []).pair id_computes).comp (ReverseMap.run_computes discardPrefix_computes)
noncomputable def mapWith_computes {f : List Bool → List Bool} (hf : PolyComputes f) : PolyComputes (mapWith f) :=
  (ReverseMap.run_computes hf).comp reverse_computes

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

noncomputable def step_computes : PolyComputes step := by
  have hd := NatOps.sub extractPrefix_computes (const_computes [true])
  have hp := hd.pair (discardPrefix_computes.comp WordList.tail_computes)
  have hh := (NatOps.zero extractPrefix_computes).cond id_computes hp
  unfold step
  simpa [value,Function.comp_def] using hh
noncomputable def run_computes : PolyComputes run := by
  have hi := BoundedIteration.polynomialRun_computes step_computes Polynomial.X (4*Polynomial.X+1)
  have hh := (hi.comp discardPrefix_computes).comp WordList.head_computes
  have he (x : List Bool) : BoundedIteration.polynomialRun step Polynomial.X (4*Polynomial.X+1) x=
      step^[x.length] x := by
    have ht := BoundedIteration.polynomialRun_eq step Polynomial.X (4*Polynomial.X+1) x (by
      intro j _
      have hb := (iterate_bounds x j).2.2
      obtain ⟨hf,hr⟩ := ProductBits.projections_length x
      simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,
        Polynomial.eval_one]
      omega)
    simpa only [Polynomial.eval_X] using ht
  change PolyComputes (fun x=>WordList.head (discardPrefix (step^[x.length] x)))
  simpa only [Function.comp_def,he] using hh
end WordList.Lookup
end
open WordOperations
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

noncomputable def addOp_computes : PolyComputes addOp := discardPrefix_computes.comp Signed.add_computes
noncomputable def sumWords_computes : PolyComputes sumWords :=
  (WordList.Fold.pack_computes id_computes (const_computes []) (const_computes (Signed.encode 0))).comp
    (WordList.Fold.run_computes addOp_computes (4*Polynomial.X+4))
end IntegerArray
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

noncomputable def run_computes : PolyComputes run := by
  have hi := Fold.pack_computes id_computes (const_computes [])
    (const_computes (pairBits (Nat.bits 0,encode [])))
  have hf := hi.comp (Fold.run_computes op_computes (20*(Polynomial.X+1)^2))
  exact (hf.comp discardPrefix_computes).comp reverse_computes
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
noncomputable def inc_computes : PolyComputes inc := by
  change PolyComputes (fun x=>(value x+1).bits)
  have hh := NatOps.add id_computes (const_computes (1:ℕ).bits)
  simpa only [inc,Function.comp_def,id_eq,value_bits] using hh
noncomputable def lengthBits_computes : PolyComputes lengthBits :=
  (id_computes.pair (cap.computes.pair (const_computes (0:ℕ).bits))).comp
    (BoundedIteration.run_computes inc_computes)
end UnaryResources
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

noncomputable def context_computes : PolyComputes context := extractPrefix_computes
noncomputable def item_computes : PolyComputes item := discardPrefix_computes.comp extractPrefix_computes
noncomputable def accum_computes : PolyComputes accum := discardPrefix_computes.comp discardPrefix_computes

end WordList.Find
end
open WordOperations BinaryArithmetic RationalLinearFeasibility
namespace BinaryRow
open RationalMatrix

noncomputable def coeff_computes : PolyComputes coeff := discardPrefix_computes.comp extractPrefix_computes
end BinaryRow
namespace BinaryEllipsoidAdvance
open Ellipsoid RationalMatrix
open scoped Matrix

noncomputable def dim_computes : PolyComputes dim := extractPrefix_computes
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

noncomputable def indices_computes : PolyComputes indices := dummy_computes.comp Indices.run_computes
noncomputable def ctx_computes : PolyComputes ctx := extractPrefix_computes.comp extractPrefix_computes
noncomputable def row_computes : PolyComputes row := extractPrefix_computes.comp discardPrefix_computes
noncomputable def col_computes : PolyComputes col := discardPrefix_computes

noncomputable def entryWords_computes : PolyComputes entryWords := by
  unfold entryWords
  have hh := (NatOps.le row_computes col_computes).cond
    ((NatOps.le col_computes row_computes).cond (ctx_computes.comp discardPrefix_computes)
      (const_computes (BinaryRational.encode 0))) (const_computes (BinaryRational.encode 0))
  simpa only [entryWords,Function.comp_def,decide_eq_true_eq] using hh
noncomputable def rowInput_computes : PolyComputes rowInput :=
  id_computes.pair ((extractPrefix_computes.comp extractPrefix_computes).comp indices_computes)
noncomputable def rowWords_computes : PolyComputes rowWords :=
  rowInput_computes.comp (mapWith_computes entryWords_computes)
noncomputable def runInput_computes : PolyComputes runInput :=
  id_computes.pair (extractPrefix_computes.comp indices_computes)
noncomputable def run_computes : PolyComputes run := runInput_computes.comp (mapWith_computes rowWords_computes)
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
noncomputable def mulOp_computes : PolyComputes mulOp :=
  NatOps.mul (discardPrefix_computes.comp extractPrefix_computes) (discardPrefix_computes.comp discardPrefix_computes)
noncomputable def productWords_computes : PolyComputes productWords :=
  (Fold.pack_computes id_computes (const_computes []) (const_computes (1:ℕ).bits)).comp
    (Fold.run_computes mulOp_computes (4*Polynomial.X+4))
noncomputable def exponentiate_computes : PolyComputes exponentiate := repeatWords_computes.comp productWords_computes
noncomputable def nextOp_computes : PolyComputes nextOp := discardPrefix_computes.comp UnaryResources.inc_computes
noncomputable def factorialWords_computes : PolyComputes factorialWords := by
  unfold factorialWords
  simpa only [Function.comp_def] using
    (PolyComputes.comp (f:=fun input=>pairBits ([],BinaryEllipsoidInitial.indices input))
      (g:=productWords ∘ mapWith nextOp)
      ((const_computes []).pair BinaryEllipsoidInitial.indices_computes)
      (PolyComputes.comp (f:=mapWith nextOp) (g:=productWords)
        (mapWith_computes nextOp_computes) productWords_computes))
noncomputable def unaryLog_computes : PolyComputes unaryLog := by
  unfold unaryLog
  have hh := (NatOps.zero id_computes).cond (const_computes [true])
    (UnaryResources.copy_computes BinaryArithmetic.normalize_computes (const_computes [true]))
  simpa only [id_eq,decide_eq_true_eq] using hh
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

noncomputable def nword_computes : PolyComputes nword := extractPrefix_computes
noncomputable def rest₁_computes : PolyComputes rest₁ := discardPrefix_computes
noncomputable def mword_computes : PolyComputes mword := rest₁_computes.comp extractPrefix_computes
noncomputable def rest₂_computes : PolyComputes rest₂ := rest₁_computes.comp discardPrefix_computes
noncomputable def bound_computes : PolyComputes bound := rest₂_computes.comp extractPrefix_computes
noncomputable def rest₃_computes : PolyComputes rest₃ := rest₂_computes.comp discardPrefix_computes
noncomputable def height_computes : PolyComputes height := rest₃_computes.comp extractPrefix_computes
noncomputable def rows_computes : PolyComputes rows := rest₃_computes.comp discardPrefix_computes
noncomputable def dim_computes : PolyComputes dim := nword_computes.comp lengthBits_computes
noncomputable def count_computes : PolyComputes count := mword_computes.comp lengthBits_computes
noncomputable def nextDim_computes : PolyComputes nextDim := nword_computes.append (const_computes [true])
noncomputable def rowFactor_computes : PolyComputes rowFactor := by
  unfold rowFactor
  have hh := NatOps.add (NatOps.add count_computes (NatOps.mul (const_computes (2:ℕ).bits) dim_computes))
    (NatOps.mul (const_computes (2:ℕ).bits) (NatOps.add dim_computes (const_computes (1:ℕ).bits)))
  simpa only [value_bits] using hh
noncomputable def base_computes : PolyComputes base := by
  unfold base
  have hh := NatOps.mul rowFactor_computes (NatOps.mul height_computes height_computes)
  simpa only [value_bits] using hh
noncomputable def power_computes : PolyComputes power := (nextDim_computes.pair base_computes).comp exponentiate_computes
noncomputable def factorial_computes : PolyComputes factorial := nextDim_computes.comp factorialWords_computes
noncomputable def gap_computes : PolyComputes gap := NatOps.mul factorial_computes power_computes
noncomputable def doubledGap_computes : PolyComputes doubledGap := by
  unfold doubledGap
  have hh := NatOps.mul (const_computes (2:ℕ).bits) gap_computes
  simpa only [value_bits] using hh
noncomputable def precisionArg_computes : PolyComputes precisionArg := NatOps.mul doubledGap_computes height_computes
noncomputable def precision_computes : PolyComputes precision := precisionArg_computes.comp unaryLog_computes
noncomputable def radius_computes : PolyComputes radius := by
  unfold radius
  have hh := NatOps.mul dim_computes (NatOps.add bound_computes (const_computes (1:ℕ).bits))
  simpa only [value_bits] using hh
noncomputable def radiusPrecision_computes : PolyComputes radiusPrecision := radius_computes.comp unaryLog_computes
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

noncomputable def boundOp_computes : PolyComputes boundOp := discardPrefix_computes.pair extractPrefix_computes
noncomputable def boxShape_computes (s : Bool) : PolyComputes (boxShape s) := by
  unfold boxShape
  simpa only [Function.comp_def] using
    (PolyComputes.comp
      (f:=fun input=>pairBits (nword input,BinaryRational.encode (if s then 1 else -1)))
      (g:=BinaryEllipsoidInitial.run)
      (nword_computes.pair (const_computes (BinaryRational.encode (if s then 1 else -1))))
      BinaryEllipsoidInitial.run_computes)
noncomputable def boxWords_computes (s : Bool) : PolyComputes (boxWords s) := by
  unfold boxWords
  simpa only [Function.comp_def] using
    (PolyComputes.comp
      (f:=fun input=>pairBits (BinaryRational.encode (value (bound input):ℚ),boxShape s input))
      (g:=mapWith boundOp)
      ((RatOps.nat bound_computes).pair (boxShape_computes s))
      (mapWith_computes boundOp_computes))
noncomputable def boundedWords_computes : PolyComputes boundedWords :=
  (rows_computes.append (boxWords_computes true)).append (boxWords_computes false)
end BinaryDecision
end
open WordOperations BinaryArithmetic
namespace NaturalArray
open WordList

noncomputable def signedOp_computes : PolyComputes signedOp := Signed.cast_computes discardPrefix_computes
noncomputable def sumWords_computes : PolyComputes sumWords := by
  unfold sumWords
  simpa only [Function.comp_def] using
    (PolyComputes.comp (f:=mapWith signedOp ∘ (fun input=>pairBits ([],input)))
      (g:=List.tail ∘ IntegerArray.sumWords)
      (PolyComputes.comp (f:=fun input=>pairBits ([],input)) (g:=mapWith signedOp)
        ((const_computes []).pair id_computes) (mapWith_computes signedOp_computes))
      (PolyComputes.comp (f:=IntegerArray.sumWords) (g:=List.tail)
        IntegerArray.sumWords_computes WordOperations.tail_computes))
end NaturalArray
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

noncomputable def nword_computes : PolyComputes nword := extractPrefix_computes
noncomputable def rest₁_computes : PolyComputes rest₁ := discardPrefix_computes
noncomputable def mword_computes : PolyComputes mword := rest₁_computes.comp extractPrefix_computes
noncomputable def rest₂_computes : PolyComputes rest₂ := rest₁_computes.comp discardPrefix_computes
noncomputable def bound_computes : PolyComputes bound := rest₂_computes.comp extractPrefix_computes
noncomputable def rows_computes : PolyComputes rows := rest₂_computes.comp discardPrefix_computes
noncomputable def numAbs_computes : PolyComputes numAbs := extractPrefix_computes.comp WordOperations.tail_computes
noncomputable def numAbsOp_computes : PolyComputes numAbsOp := discardPrefix_computes.comp numAbs_computes
noncomputable def coeffAbs_computes : PolyComputes coeffAbs := by
  unfold coeffAbs
  simpa only [Function.comp_def] using
    (PolyComputes.comp (f:=fun input=>pairBits ([],extractPrefix input)) (g:=mapWith numAbsOp)
      ((const_computes []).pair extractPrefix_computes) (mapWith_computes numAbsOp_computes))
noncomputable def coeffSum_computes : PolyComputes coeffSum := coeffAbs_computes.comp NaturalArray.sumWords_computes
noncomputable def rowHeight_computes : PolyComputes rowHeight :=
  NatOps.add (discardPrefix_computes.comp numAbs_computes) coeffSum_computes
noncomputable def rowHeightOp_computes : PolyComputes rowHeightOp := discardPrefix_computes.comp rowHeight_computes
noncomputable def rowHeights_computes : PolyComputes rowHeights := by
  unfold rowHeights
  simpa only [Function.comp_def] using
    (PolyComputes.comp (f:=fun input=>pairBits ([],rows input)) (g:=mapWith rowHeightOp)
      ((const_computes []).pair rows_computes) (mapWith_computes rowHeightOp_computes))
noncomputable def heightSum_computes : PolyComputes heightSum := rowHeights_computes.comp NaturalArray.sumWords_computes
noncomputable def height_computes : PolyComputes height := by
  unfold height
  have hh := NatOps.add (NatOps.add bound_computes (const_computes (1:ℕ).bits)) heightSum_computes
  simpa only [value_bits] using hh
noncomputable def padRow_computes : PolyComputes padRow :=
  (extractPrefix_computes.append (const_computes (WordList.encode [BinaryRational.encode 0,BinaryRational.encode 0]))).pair
    discardPrefix_computes
noncomputable def padRowOp_computes : PolyComputes padRowOp := discardPrefix_computes.comp padRow_computes
noncomputable def paddedRows_computes : PolyComputes paddedRows := by
  unfold paddedRows
  simpa only [Function.comp_def] using
    (PolyComputes.comp (f:=fun input=>pairBits ([],rows input)) (g:=mapWith padRowOp)
      ((const_computes []).pair rows_computes) (mapWith_computes padRowOp_computes))
noncomputable def prepared_computes : PolyComputes prepared :=
  (nword_computes.append (const_computes [true,true])).pair
    (mword_computes.pair (bound_computes.pair (height_computes.pair paddedRows_computes)))
end BinaryBoundedDecision
namespace BinaryRationalDecision
open WordOperations BinaryArithmetic RationalLinearFeasibility Ellipsoid
open WordList

noncomputable def first_computes : PolyComputes first := extractPrefix_computes
noncomputable def rest₁_computes : PolyComputes rest₁ := discardPrefix_computes
noncomputable def rest₂_computes : PolyComputes rest₂ := rest₁_computes.comp discardPrefix_computes
noncomputable def bound_computes : PolyComputes bound := rest₂_computes.comp extractPrefix_computes
noncomputable def rows_computes : PolyComputes rows := rest₂_computes.comp discardPrefix_computes
end BinaryRationalDecision

open WordOperations
namespace WordList
namespace Count
noncomputable def op_computes : PolyComputes op := Fold.accum_computes.comp (prefix_computes true)
noncomputable def run_computes : PolyComputes run :=
  (Fold.pack_computes id_computes (const_computes []) (const_computes [])).comp
    (Fold.run_computes op_computes (4*Polynomial.X+4))
end Count
end WordList
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
noncomputable def negEntry_computes : PolyComputes negEntry := discardPrefix_computes.comp BinaryRational.negWords_computes
noncomputable def reverse_computes : PolyComputes reverse := by
  unfold reverse
  simpa only [Function.comp_def] using
    (PolyComputes.pair (f:=mapWith negEntry ∘ (fun input=>pairBits ([],extractPrefix input)))
      (g:=BinaryRational.negWords ∘ discardPrefix)
      (PolyComputes.comp (f:=fun input=>pairBits ([],extractPrefix input)) (g:=mapWith negEntry)
        ((const_computes []).pair extractPrefix_computes) (mapWith_computes negEntry_computes))
      (discardPrefix_computes.comp BinaryRational.negWords_computes))
noncomputable def reverseOp_computes : PolyComputes reverseOp := discardPrefix_computes.comp reverse_computes
noncomputable def reverseRows_computes : PolyComputes reverseRows := by
  unfold reverseRows
  simpa only [Function.comp_def] using
    (PolyComputes.comp (f:=fun input=>pairBits ([],input)) (g:=mapWith reverseOp)
      ((const_computes []).pair id_computes) (mapWith_computes reverseOp_computes))
noncomputable def proposed_computes : PolyComputes proposed := cons_computes Find.item_computes Find.accum_computes
noncomputable def faceWords_computes : PolyComputes faceWords := by
  unfold faceWords
  simpa only [Function.comp_def] using
    (PolyComputes.append
      (f:=fun input=>(BinaryRationalDecision.rows ∘ Find.context) input++proposed input)
      (g:=reverseRows ∘ proposed)
      ((Find.context_computes.comp BinaryRationalDecision.rows_computes).append proposed_computes)
      (PolyComputes.comp (f:=proposed) (g:=reverseRows) proposed_computes reverseRows_computes))
noncomputable def decisionInput_computes : PolyComputes decisionInput :=
  (Find.context_computes.comp BinaryRationalDecision.first_computes).pair
    ((faceWords_computes.comp Count.run_computes).pair
      ((Find.context_computes.comp BinaryRationalDecision.bound_computes).pair faceWords_computes))
end BinaryFace
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
noncomputable def coeffs_computes : PolyComputes coeffs := by
  unfold coeffs
  simpa only [Function.comp_def] using
    (PolyComputes.comp (f:=fun input=>pairBits ([],input)) (g:=mapWith BinaryRow.coeff)
      ((const_computes []).pair id_computes) (mapWith_computes BinaryRow.coeff_computes))
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

noncomputable def field_computes (k : ℕ) : PolyComputes (field k) :=
  ((const_computes k.bits).pair id_computes).comp Lookup.run_computes
noncomputable def itemField_computes (k : ℕ) : PolyComputes (itemField k) :=
  extractPrefix_computes.comp (field_computes k)
end BinaryOpeningPayment
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
open WordOperations BinaryArithmetic
namespace BinaryOpeningEnumeration
open WordList EffectiveOpenability RationalOpenability BinaryOpeningPayment
noncomputable def clients_computes : PolyComputes clients := (field_computes 7).comp BinaryEllipsoidInitial.indices_computes
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

namespace MetricKMedianRecovery.BitMachine.BinaryPhaseFirst
open WordOperations BinaryArithmetic WordList EffectiveOpenability RationalOpenability
open BinaryOpeningPayment

noncomputable def query_computes : PolyComputes query := by
  exact cons_computes (itemField_computes 0) (cons_computes (itemField_computes 1)
    (cons_computes (itemField_computes 2) (cons_computes (itemField_computes 3)
    (cons_computes (itemField_computes 4) (cons_computes (itemField_computes 5)
    (cons_computes discardPrefix_computes (cons_computes (itemField_computes 7)
    (cons_computes (itemField_computes 8) (const_computes [])))))))))
end MetricKMedianRecovery.BitMachine.BinaryPhaseFirst

end OAI
end


