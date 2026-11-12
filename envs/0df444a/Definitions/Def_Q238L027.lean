-- Prove2me | Definitions.Def_Q238L027
-- name    : Q238L027
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T11:27:43.311165+00:00
-- url     : https://prove2.me/theorems/4e6f073f-9092-4d6a-b9cb-da0ac0c90d9b
-- title:
--   Definitions bundle Q238L027 of the split of OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 127 declarations of OpenAI's Lean: 127 definitions. The definitions and types are `OAI.MetricKMedianRecovery.BitMachine.BinaryBoundedDecision.bound_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBoundedDecision.coeffAbs_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBoundedDecision.coeffSum_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBoundedDecision.heightSum_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBoundedDecision.height_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBoundedDecision.mword_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBoundedDecision.numAbsOp_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBoundedDecision.numAbs_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBoundedDecision.nword_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBoundedDecision.padRowOp_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBoundedDecision.padRow_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBoundedDecision.paddedRows_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBoundedDecision.prepared_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBoundedDecision.rowHeightOp_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBoundedDecision.rowHeight_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBoundedDecision.rowHeights_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.base_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.boundOp_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.bound_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.boundedWords_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.boxShape_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.boxWords_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.count_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.dim_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.doubledGap_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.factorial_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.gap_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.height_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.mword_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.nextDim_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.nword_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.power_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.precisionArg_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.precision_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.radiusPrecision_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.radius_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.rowFactor_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDivision.digits_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDivision.divisor_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDivision.quotient_computes` and 87 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedianRecovery_Branching_CopyComputes`, `KMedianRecovery_Encoding_Encode`, `KMedianRecovery_Encoding_Encode3`, `KMedianRecovery_Encoding_OptionEncode`, `KMedianRecovery_Encoding_Words`, `KMedianRecovery_Recovery_BoundOp`, `KMedianRecovery_Recovery_BoundedDecision`, `KMedianRecovery_Recovery_Computes`, `KMedianRecovery_Recovery_Copies`, `KMedianRecovery_Recovery_DigitBit`, `KMedianRecovery_Recovery_FaceSelection`, `KMedianRecovery_Recovery_LeftNum`, `KMedianRecovery_Recovery_LengthPolynomial`, `KMedianRecovery_Recovery_MulComputes`, `KMedianRecovery_Recovery_NumAbs`, `KMedianRecovery_Recovery_Op`, `KMedianRecovery_Recovery_Op2`, `KMedianRecovery_Recovery_Pack`, `KMedianRecovery_Recovery_Pack2`, `KMedianRecovery_Recovery_Pack3`, `KMedianRecovery_Recovery_Pack7`, `KMedianRecovery_Recovery_Pack9`, `KMedianRecovery_Recovery_ProcessOutputs`, `KMedianRecovery_Recovery_Rectangular`, `KMedianRecovery_Recovery_RowInput`, `KMedianRecovery_Recovery_Step`, `KMedianRecovery_Recovery_Step2`, `KMedianRecovery_Recovery_Values`.
--
--   **Imports.** It imports the published bundle `Def_KMedianRecovery`; the bundles `Q238L022` and `Q238L023` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q238L032`, `Q238L033`, `Q238L034` and `Q238L035`; the statements `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseFirst.bids_context_s238r` and `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseFirst.eligible_context_s238r`; the proofs of `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseFirst.bids_context_s238r` and `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseFirst.eligible_context_s238r`.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_KMedianRecovery
import Definitions.Def_Q238L022
import Definitions.Def_Q238L023

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

noncomputable def first_computes : PolyComputes first := tail_computes.comp extractPrefix_computes

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

noncomputable def le {f g : List Bool → List Bool} (hf : PolyComputes f) (hg : PolyComputes g) :
    PolyComputes (fun x=>[decide (value (f x)≤value (g x))]) := by
  have hh := (hf.pair hg).comp BinarySubtraction.le_computes
  simpa only [Function.comp_def,pairBits,extractPrefix_pair,discardPrefix_pair] using hh

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
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Pack3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace UnaryTake

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

namespace WordList

noncomputable def head_computes : PolyComputes head := _root_.OAI.MetricKMedianRecovery.BitMachine.WordOperations.tail_computes.comp extractPrefix_computes
noncomputable def tail_computes : PolyComputes tail :=
  WordOperations.tail_computes.comp discardPrefix_computes

namespace ReverseMap

noncomputable def step_computes {f : List Bool → List Bool} (hf : PolyComputes f) : PolyComputes (step f) := by
  have hn := (data_computes.pair (counter_computes.comp head_computes)).comp hf
  have ht := pack_computes true (counter_computes.comp tail_computes) data_computes
    (cons_computes hn output_computes)
  have hh := (counter_computes.comp isEmpty_computes).cond
    (pack_computes false (const_computes []) data_computes output_computes) ht
  unfold step
  simpa only [Function.comp_def,decide_eq_true_eq] using hh

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
namespace WordList
namespace Fold

noncomputable def items_computes : PolyComputes items := extractPrefix_computes
noncomputable def context_computes : PolyComputes context := discardPrefix_computes.comp extractPrefix_computes
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

noncomputable def op_computes : PolyComputes op := by
  let a : PolyComputes (fun x=>discardPrefix (discardPrefix x)) := discardPrefix_computes.comp discardPrefix_computes
  let l := a.comp extractPrefix_computes
  let r := a.comp discardPrefix_computes
  have hi := NatOps.add l (const_computes [true])
  have hh := hi.pair (cons_computes l r)
  unfold op
  simpa only [Function.comp_def,value,Bool.toNat_true,Nat.mul_zero,Nat.add_zero] using hh
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
noncomputable def copy_computes {f g : List Bool → List Bool} (hf : PolyComputes f) (hg : PolyComputes g) :
    PolyComputes (fun x=>RepeatedAppend.copies (f x).length (g x)) := by
  have hh := (hf.pair hg).comp RepeatedAppend.run_computes
  simpa only [Function.comp_def,RepeatedAppend.run_pair] using hh
noncomputable def lengthBits_computes : PolyComputes lengthBits :=
  (id_computes.pair (cap.computes.pair (const_computes (0:ℕ).bits))).comp
    (BoundedIteration.run_computes inc_computes)
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
end RatOps
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
end WordList.Find
end
open WordOperations BinaryArithmetic RationalLinearFeasibility
namespace BinaryRow
open RationalMatrix

noncomputable def coeff_computes : PolyComputes coeff := discardPrefix_computes.comp extractPrefix_computes
end BinaryRow
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
noncomputable def indices_computes : PolyComputes indices := dummy_computes.comp Indices.run_computes
noncomputable def ctx_computes : PolyComputes ctx := extractPrefix_computes.comp extractPrefix_computes
noncomputable def row_computes : PolyComputes row := extractPrefix_computes.comp discardPrefix_computes
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
noncomputable def mword_computes : PolyComputes mword := rest₁_computes.comp extractPrefix_computes
noncomputable def bound_computes : PolyComputes bound := rest₂_computes.comp extractPrefix_computes
noncomputable def height_computes : PolyComputes height := rest₃_computes.comp extractPrefix_computes
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
noncomputable def mword_computes : PolyComputes mword := rest₁_computes.comp extractPrefix_computes
noncomputable def bound_computes : PolyComputes bound := rest₂_computes.comp extractPrefix_computes
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
noncomputable def bound_computes : PolyComputes bound := rest₂_computes.comp extractPrefix_computes
end BinaryRationalDecision

open WordOperations
namespace WordList
namespace Count
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
open WordList BinaryOpeningPayment
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

namespace MetricKMedianRecovery.BitMachine.BinaryRawOpening
open WordOperations BinaryArithmetic WordList RationalLinearFeasibility
open BinaryOpeningPayment BinaryOpeningEnumeration

noncomputable def run : List Bool → List Bool := BinaryExactSolve.run ∘ prepared
end MetricKMedianRecovery.BitMachine.BinaryRawOpening

namespace MetricKMedianRecovery.BitMachine.BinaryPhaseFirst
open WordOperations BinaryArithmetic WordList
open BinaryOpeningPayment

noncomputable def query_computes : PolyComputes query := by
  exact cons_computes (itemField_computes 0) (cons_computes (itemField_computes 1)
    (cons_computes (itemField_computes 2) (cons_computes (itemField_computes 3)
    (cons_computes (itemField_computes 4) (cons_computes (itemField_computes 5)
    (cons_computes discardPrefix_computes (cons_computes (itemField_computes 7)
    (cons_computes (itemField_computes 8) (const_computes [])))))))))

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


