-- Prove2me | Definitions.Def_Q238K032
-- name    : Q238K032
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T23:28:14.897373+00:00
-- url     : https://prove2.me/theorems/d3b5eedf-5245-4f8f-9a5c-eddc4670fbf5
-- title:
--   Definitions bundle Q238K032 of the split of OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 147 declarations of OpenAI's Lean: 147 definitions. The definitions and types are `OAI.MetricKMedianRecovery.BitMachine.BinaryBoundedDecision.run_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryClearRow.boundWords_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryClearRow.coeffWords_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryClearRow.denOp_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryClearRow.denominator_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryClearRow.denominators_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryClearRow.scalar_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.epsilon_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.prepared_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.relaxedOp_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.relaxedWords_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.run_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.solved_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDivision.divide_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDivision.loop_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDivision.rawDivide_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDivision.step_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDivision.withDivision_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidAdvance.cutInput_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidAdvance.direction_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidAdvance.found_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidAdvance.nextState_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidAdvance.normWords_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidAdvance.run_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidAdvance.updated_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidAdvance.zeroDirection_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidCut.centerInput_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidCut.centerWords_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidCut.coefA_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidCut.coefB_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidCut.coefCenter_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidCut.coefInflate_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidCut.cutInput_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidCut.cutWords_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidCut.differenceInput_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidCut.difference_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidCut.gridInput_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidCut.haWords_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidCut.inflateInput_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidCut.inflateWords_computes` and 107 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedianRecovery_Encoding_DivNatWords`, `KMedianRecovery_Encoding_Encode2`, `KMedianRecovery_Encoding_OptionEncode`, `KMedianRecovery_Encoding_Words`, `KMedianRecovery_Recovery_BoundOp`, `KMedianRecovery_Recovery_BoundedDecision`, `KMedianRecovery_Recovery_DigitBit`, `KMedianRecovery_Recovery_GetRow2`, `KMedianRecovery_Recovery_LeftNum`, `KMedianRecovery_Recovery_MulComputes`, `KMedianRecovery_Recovery_Next`, `KMedianRecovery_Recovery_NumAbs`, `KMedianRecovery_Recovery_Op`, `KMedianRecovery_Recovery_Pack`, `KMedianRecovery_Recovery_Pack2`, `KMedianRecovery_Recovery_Pack5`, `KMedianRecovery_Recovery_Pack6`, `KMedianRecovery_Recovery_Pack7`, `KMedianRecovery_Recovery_Pack8`, `KMedianRecovery_Recovery_Pack9`, `KMedianRecovery_Recovery_ProcessOutputs`.
--
--   **Imports.** It imports the published bundle `Def_KMedianRefinedRecovery`; the bundles `Q238K028` and `Q238K029` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q238K036`, `Q238K037` and `Q238K038`; the statements `OAI_MetricKMedianRecovery_BitMachine_BinaryBranchProgram_rows_pack_s238` and `OAI_MetricKMedianRecovery_BitMachine_BinaryRationalSort_bottom_pack_s238`; the proofs of `OAI_MetricKMedianRecovery_BitMachine_BinaryBranchProgram_rows_pack_s238` and `OAI_MetricKMedianRecovery_BitMachine_BinaryRationalSort_bottom_pack_s238`.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_KMedianRefinedRecovery
import Definitions.Def_Q238K028
import Definitions.Def_Q238K029

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

noncomputable def step_computes : PolyComputes step := by
  have ht := pack_computes true (digits_computes.comp tail_computes) divisor_computes
    (nextBit_computes.append quotient_computes) reduced_computes
  have hf := pack_computes false (const_computes []) divisor_computes quotient_computes remainder_computes
  have hh := (digits_computes.comp isEmpty_computes).cond hf ht
  change PolyComputes (fun xs=>if digits xs=[] then _ else _)
  simpa only [Function.comp_def,decide_eq_true_eq,List.singleton_append] using hh

noncomputable def loop_computes : PolyComputes (fun x=>next^[rank x] x) := by
  apply step_computes.whileLoop rank (Polynomial.X+1) (20*(Polynomial.X+1)^2)
  · intro x
    simpa only [Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one] using rank_bound x
  · intro x j hj
    have hh := (iterate_bounds x j).2.2.1
    have hq := rank_bound x
    obtain ⟨hd,hy,hb,hr⟩ := projection_bounds x
    simp only [Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_pow,
      Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one]
    change (next^[j] x).length ≤ _
    simp only [mass] at hh
    have hm : j*((divisor x).length+2) ≤ (x.length+1)*(x.length+2) :=
      Nat.mul_le_mul (hj.trans hq) (by omega)
    nlinarith
  · exact stop

end BinaryDivision
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_DigitBit
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open Turing
namespace BinaryDivision
open BinaryArithmetic BinarySubtraction WordOperations

noncomputable def withDivision_computes : PolyComputes withDivision := by
  have hh := setupWords_computes.comp loop_computes
  unfold withDivision
  simpa only [Function.comp_def] using hh

noncomputable def rawDivide_computes : PolyComputes rawDivide := by
  have hq := quotient_computes.comp normalize_computes
  have hr := remainder_computes.comp normalize_computes
  have hh := withDivision_computes.comp (hq.pair hr)
  unfold rawDivide
  simpa only [Function.comp_def] using hh

noncomputable def divide_computes : PolyComputes divide := by
  have hz := discardPrefix_computes.comp zeroTest_computes
  have hf := (const_computes []).pair (extractPrefix_computes.comp normalize_computes)
  have hh := hz.cond hf rawDivide_computes
  change PolyComputes (fun x=>if value (discardPrefix x)=0 then _ else _)
  simpa only [Function.comp_def,decide_eq_true_eq] using hh

end BinaryDivision
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Pack2
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open Turing
namespace BinaryGCD
open BinaryArithmetic BinarySubtraction WordOperations

noncomputable def mod_computes {f g : List Bool → List Bool}
    (hf : PolyComputes f) (hg : PolyComputes g) :
    PolyComputes (fun x=>(value (f x)%value (g x)).bits) := by
  have hh := ((hf.pair hg).comp BinaryDivision.divide_computes).comp discardPrefix_computes
  simp only [Function.comp_def,BinaryDivision.divide_pair] at hh
  simpa only [pairBits,discardPrefix_pair] using hh

noncomputable def firstRem_computes : PolyComputes firstRem := mod_computes first_computes second_computes
noncomputable def secondRem_computes : PolyComputes secondRem := by
  have hh := mod_computes second_computes firstRem_computes
  unfold secondRem
  simpa only [firstRem,value_bits] using hh

noncomputable def step_computes : PolyComputes step := by
  have ha := pack_computes false (first_computes.comp BinaryDivision.normalize_computes) (const_computes [])
  have hb := pack_computes false (second_computes.comp BinaryDivision.normalize_computes) (const_computes [])
  have hc := pack_computes true firstRem_computes secondRem_computes
  have hz := firstRem_computes.comp BinaryDivision.zeroTest_computes
  have hc' := hz.cond hb hc
  have hz' := second_computes.comp BinaryDivision.zeroTest_computes
  have hh := hz'.cond ha hc'
  change PolyComputes (fun x=>if value (second x)=0 then _ else if value (first x)%value (second x)=0 then _ else _)
  simpa only [Function.comp_def,firstRem,value_bits,decide_eq_true_eq] using hh

noncomputable def loop_computes : PolyComputes (fun x=>next^[rank x] x) := by
  apply step_computes.whileLoop rank (2*Polynomial.X+1) (5*Polynomial.X+2)
  · intro x
    simpa only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,Polynomial.eval_one] using rank_bound x
  · intro x j _
    have hh := (iterate_bounds x j).2.2
    have hm := measure_bound x
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X]
    change (next^[j] x).length ≤ _
    apply hh.trans
    apply max_le <;> omega
  · exact stop

noncomputable def gcdWords_computes : PolyComputes gcdWords := by
  have hi := pack_computes true extractPrefix_computes discardPrefix_computes
  have hl := hi.comp loop_computes
  have ht := first_computes.comp BinaryDivision.normalize_computes
  have hh := hl.comp ht
  unfold gcdWords
  simpa only [Function.comp_def] using hh

end BinaryGCD
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

open WordOperations BinaryArithmetic
namespace NatOps

noncomputable def div {f g : List Bool → List Bool} (hf : PolyComputes f) (hg : PolyComputes g) :
    PolyComputes (fun x=>(value (f x)/value (g x)).bits) := by
  have hh := ((hf.pair hg).comp BinaryDivision.divide_computes).comp extractPrefix_computes
  simp only [Function.comp_def,BinaryDivision.divide_pair] at hh
  simpa only [pairBits,extractPrefix_pair] using hh

noncomputable def mod {f g : List Bool → List Bool} (hf : PolyComputes f) (hg : PolyComputes g) :
    PolyComputes (fun x=>(value (f x)%value (g x)).bits) := BinaryGCD.mod_computes hf hg

noncomputable def gcd {f g : List Bool → List Bool} (hf : PolyComputes f) (hg : PolyComputes g) :
    PolyComputes (fun x=>(Nat.gcd (value (f x)) (value (g x))).bits) := by
  have hh := (hf.pair hg).comp BinaryGCD.gcdWords_computes
  simpa only [Function.comp_def,BinaryGCD.gcdWords_pair] using hh

end NatOps
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_MulComputes
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace Signed

noncomputable def mul_computes : PolyComputes (fun x=>
    encode (decode (extractPrefix x)*decode (discardPrefix x))) := by
  let l := extractPrefix_computes
  let r := discardPrefix_computes
  let sl := l.comp sign_computes
  let sr := r.comp sign_computes
  let al := l.comp tail_computes
  let ar := r.comp tail_computes
  have hm := NatOps.mul al ar
  have hp := pack_computes (const_computes [false]) hm
  have hn := pack_computes (const_computes [true]) hm
  have hh := sl.cond (sr.cond hp hn) (sr.cond hn hp)
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  dsimp only [Function.comp_def]
  cases hl : sign (extractPrefix x) <;> cases hr : sign (discardPrefix x) <;>
    simp only [decode,hl,hr,Bool.false_eq_true,ite_false, if_false,ite_true, if_true,pack_bits,signed,mag,
      Int.natCast_mul,neg_mul,mul_neg,neg_neg]

noncomputable def le_computes : PolyComputes (fun x=>
    [decide (decode (extractPrefix x)≤decode (discardPrefix x))]) := by
  let l := extractPrefix_computes
  let r := discardPrefix_computes
  let sl := l.comp sign_computes
  let sr := r.comp sign_computes
  let al := l.comp tail_computes
  let ar := r.comp tail_computes
  have hl := NatOps.le al ar
  have hr := NatOps.le ar al
  have hz := NatOps.zero (NatOps.add al ar)
  have hh := sl.cond (sr.cond hr (const_computes [true])) (sr.cond hz hl)
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  dsimp only [Function.comp_def]
  cases h1 : sign (extractPrefix x) <;> cases h2 : sign (discardPrefix x) <;>
    simp only [decode,h1,h2,Bool.false_eq_true,ite_false, if_false,ite_true, if_true,mag,value_bits]
  all_goals congr 1; simp only [decide_eq_decide,decide_eq_true_eq]; omega

noncomputable def add {f g : List Bool → List Bool} (hf : PolyComputes f) (hg : PolyComputes g) :
    PolyComputes (fun x=>encode (decode (f x)+decode (g x))) := by
  have hh := (hf.pair hg).comp add_computes
  simpa only [Function.comp_def,pairBits,extractPrefix_pair,discardPrefix_pair] using hh

noncomputable def mul {f g : List Bool → List Bool} (hf : PolyComputes f) (hg : PolyComputes g) :
    PolyComputes (fun x=>encode (decode (f x)*decode (g x))) := by
  have hh := (hf.pair hg).comp mul_computes
  simpa only [Function.comp_def,pairBits,extractPrefix_pair,discardPrefix_pair] using hh

noncomputable def le {f g : List Bool → List Bool} (hf : PolyComputes f) (hg : PolyComputes g) :
    PolyComputes (fun x=>[decide (decode (f x)≤decode (g x))]) := by
  have hh := (hf.pair hg).comp le_computes
  simpa only [Function.comp_def,pairBits,extractPrefix_pair,discardPrefix_pair] using hh

end Signed
namespace BinaryRational

noncomputable def divisor_computes : PolyComputes divisor := by
  unfold divisor Signed.mag
  exact NatOps.gcd (numerator_computes.comp tail_computes) denominator_computes

noncomputable def reduceNonzero_computes : PolyComputes reduceNonzero := by
  have hn := NatOps.div (numerator_computes.comp tail_computes) divisor_computes
  have hd := NatOps.div denominator_computes divisor_computes
  have hs := numerator_computes.comp Signed.sign_computes
  unfold reduceNonzero Signed.mag
  exact (Signed.pack_computes hs hn).pair hd

noncomputable def reduce_computes : PolyComputes reduce := by
  have hz := NatOps.zero denominator_computes
  have hh := hz.cond (const_computes (encode 0)) reduceNonzero_computes
  unfold reduce
  simpa only [decide_eq_true_eq] using hh

noncomputable def normalize_computes : PolyComputes (fun x=>encode (decode x)) := by
  have he : reduce=(fun x=>encode (decode x)) := funext reduce_correct
  rw [← he]
  exact reduce_computes

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

noncomputable def leftNum_computes : PolyComputes leftNum := extractPrefix_computes.comp numerator_computes
noncomputable def rightNum_computes : PolyComputes rightNum := discardPrefix_computes.comp numerator_computes
noncomputable def leftDen_computes : PolyComputes leftDen := extractPrefix_computes.comp denominator_computes
noncomputable def rightDen_computes : PolyComputes rightDen := discardPrefix_computes.comp denominator_computes

noncomputable def rawMul_computes : PolyComputes rawMul :=
  (Signed.mul leftNum_computes rightNum_computes).pair (NatOps.mul leftDen_computes rightDen_computes)
noncomputable def rawAdd_computes : PolyComputes rawAdd := by
  have hl := Signed.mul leftNum_computes (Signed.cast_computes rightDen_computes)
  have hr := Signed.mul rightNum_computes (Signed.cast_computes leftDen_computes)
  have hn := Signed.add hl hr
  have hd := NatOps.mul leftDen_computes rightDen_computes
  have hh := hn.pair hd
  unfold rawAdd
  simpa only [Signed.encode_decode] using hh

noncomputable def addWords_computes : PolyComputes addWords := rawAdd_computes.comp reduce_computes
noncomputable def mulWords_computes : PolyComputes mulWords := rawMul_computes.comp reduce_computes

noncomputable def leWords_computes : PolyComputes leWords := by
  have hl := Signed.mul leftNum_computes (Signed.cast_computes rightDen_computes)
  have hr := Signed.mul rightNum_computes (Signed.cast_computes leftDen_computes)
  have hh := Signed.le hl hr
  unfold leWords
  simpa only [Signed.encode_decode] using hh
noncomputable def invWords_computes : PolyComputes invWords := rawInv_computes.comp reduce_computes

end BinaryRational
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_DivNatWords
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace Signed

noncomputable def divNatWords_computes : PolyComputes divNatWords := by
  have hm := extractPrefix_computes.comp tail_computes
  have hq := NatOps.div hm discardPrefix_computes
  have hq1 := NatOps.add hq (const_computes (Nat.bits 1))
  have hz := NatOps.zero (NatOps.mod hm discardPrefix_computes)
  have hneg := hz.cond (pack_computes (const_computes [true]) hq)
    (pack_computes (const_computes [true]) hq1)
  have hs := extractPrefix_computes.comp sign_computes
  have hsign := hs.cond hneg (pack_computes (const_computes [false]) hq)
  have hd := NatOps.zero discardPrefix_computes
  have hh := hd.cond (const_computes (encode 0)) hsign
  unfold divNatWords mag
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  simp only [Function.comp_def,value_bits,decide_eq_true_eq]

end Signed
namespace BinaryRational

noncomputable def floorWords_computes : PolyComputes floorWords := Signed.divNatWords_computes

end BinaryRational
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

section
open WordOperations
namespace WordList
namespace Zip

noncomputable def run_computes : PolyComputes run := by
  have ha : PolyComputes (fun x=>pairBits (discardPrefix x,[])) := discardPrefix_computes.pair (const_computes [])
  have hi := Fold.pack_computes extractPrefix_computes (const_computes []) ha
  have hf := hi.comp (Fold.run_computes op_computes (4*Polynomial.X+4))
  exact (hf.comp discardPrefix_computes).comp reverse_computes
end Zip
end WordList
end
open WordOperations BinaryArithmetic
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
open RationalHeight
noncomputable def addOp_computes : PolyComputes addOp := discardPrefix_computes.comp BinaryRational.addWords_computes
noncomputable def sumWords_computes : PolyComputes sumWords := by
  with_unfolding_all exact sumInput_computes.comp (WordList.Fold.run_computes addOp_computes (20*(Polynomial.X+1)^2))
noncomputable def mulOp_computes : PolyComputes mulOp := discardPrefix_computes.comp BinaryRational.mulWords_computes
noncomputable def dotWords_computes : PolyComputes dotWords := by
  with_unfolding_all exact (IntegerArray.prefixEmpty_computes.comp (WordList.mapWith_computes mulOp_computes)).comp sumWords_computes
noncomputable def dotListsWords_computes : PolyComputes dotListsWords := by
  with_unfolding_all exact WordList.Zip.run_computes.comp dotWords_computes
end RationalArray
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

noncomputable def getRow_computes : PolyComputes getRow := swapWords_computes.comp Lookup.run_computes
noncomputable def entryInput_computes : PolyComputes entryInput :=
  discardPrefix_computes.pair (extractPrefix_computes.comp getRow_computes)
noncomputable def getEntry_computes : PolyComputes getEntry := entryInput_computes.comp Lookup.run_computes

end RationalMatrix
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

noncomputable def middle_computes : PolyComputes middle := by
  have hh := NatOps.div (NatOps.add low_computes high_computes) (const_computes (Nat.bits 2))
  change PolyComputes (fun x => ((value (low x)+value (high x))/2).bits)
  simpa only [value_bits] using hh

noncomputable def leftCase_computes : PolyComputes leftCase := extractPrefix_computes.pair
  (middle_computes.pair high_computes)
noncomputable def rightCase_computes : PolyComputes rightCase := extractPrefix_computes.pair
  (low_computes.pair middle_computes)
noncomputable def step_computes : PolyComputes step := by
  have hh := (NatOps.le (NatOps.mul middle_computes middle_computes) extractPrefix_computes).cond
    leftCase_computes rightCase_computes
  unfold step
  simpa only [value_bits,decide_eq_true_eq] using hh
noncomputable def run_computes : PolyComputes run :=
  (startWords_computes.comp (BoundedIteration.polynomialRun_computes step_computes
    (Polynomial.X+1) (10*(Polynomial.X+1)))).comp low_computes
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

noncomputable def upper_computes : PolyComputes upper := by
  have hh := NatOps.add (radicand_computes.comp BinarySqrt.run_computes) (const_computes (Nat.bits 1))
  change PolyComputes (fun x => (value (BinarySqrt.run (radicand x))+1).bits)
  simpa only [value_bits,Function.comp_apply] using hh

noncomputable def rawWords_computes : PolyComputes rawWords :=
  (Signed.cast_computes upper_computes).pair denom_computes
noncomputable def run_computes : PolyComputes run := rawWords_computes.comp BinaryRational.reduce_computes
end BinaryEllipsoidRoot
open WordOperations BinaryArithmetic
open scoped Matrix
namespace WordList
noncomputable def pointwise_computes {f : List Bool → List Bool} (hf : PolyComputes f) :
    PolyComputes (pointwise f) := by
  unfold pointwise
  simpa only [Function.comp_def] using
    (PolyComputes.comp (f := fun input => pairBits ([], Zip.run input))
      (g := mapWith (f ∘ discardPrefix))
      (PolyComputes.comp (f := Zip.run) (g := fun input => pairBits ([], input))
        Zip.run_computes IntegerArray.prefixEmpty_computes)
      (mapWith_computes (f := f ∘ discardPrefix)
        (PolyComputes.comp (f := discardPrefix) (g := f) discardPrefix_computes hf)))
end WordList
namespace BinaryRational

noncomputable def subInput_computes : PolyComputes subInput :=
  extractPrefix_computes.pair (discardPrefix_computes.comp negWords_computes)
noncomputable def subWords_computes : PolyComputes subWords := subInput_computes.comp addWords_computes
noncomputable def secondInverse_computes : PolyComputes secondInverse :=
  PolyComputes.comp (f:=discardPrefix) (g:=invWords) discardPrefix_computes invWords_computes
noncomputable def divInput_computes : PolyComputes divInput :=
  extractPrefix_computes.pair secondInverse_computes
noncomputable def divWords_computes : PolyComputes divWords := divInput_computes.comp mulWords_computes
end BinaryRational
namespace RationalMatrix
open WordList
noncomputable def vectorSub_computes : PolyComputes vectorSub := pointwise_computes BinaryRational.subWords_computes
noncomputable def vectorScale_computes : PolyComputes vectorScale := mapWith_computes BinaryRational.mulWords_computes
noncomputable def matrixSub_computes : PolyComputes matrixSub := pointwise_computes vectorSub_computes
noncomputable def matrixScale_computes : PolyComputes matrixScale := mapWith_computes vectorScale_computes
noncomputable def outerRow_computes : PolyComputes outerRow := swapWords_computes.comp vectorScale_computes
noncomputable def outer_computes : PolyComputes outer := swapWords_computes.comp (mapWith_computes outerRow_computes)
noncomputable def dotRow_computes : PolyComputes dotRow := swapWords_computes.comp RationalArray.dotListsWords_computes
noncomputable def mulVec_computes : PolyComputes mulVec := swapWords_computes.comp (mapWith_computes dotRow_computes)
noncomputable def quadInput_computes : PolyComputes quadInput := discardPrefix_computes.pair mulVec_computes
noncomputable def quad_computes : PolyComputes quad := quadInput_computes.comp RationalArray.dotListsWords_computes
end RationalMatrix
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_Words
attribute [-instance] _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace RatOps
open BinaryRational
noncomputable def ofWords {f : List Bool → List Bool} (hf : PolyComputes f) :
    PolyComputes (fun x=>encode (decode (f x))) := by
  have hh := hf.comp BinaryRational.normalize_computes
  simpa only [Function.comp_def] using hh
noncomputable def add {f g : List Bool → ℚ}
    (hf : PolyComputes (fun x=>encode (f x))) (hg : PolyComputes (fun x=>encode (g x))) :
    PolyComputes (fun x=>encode (f x+g x)) := by
  have hh := (hf.pair hg).comp addWords_computes
  simpa only [Function.comp_def,addWords_pair] using hh
noncomputable def mul {f g : List Bool → ℚ}
    (hf : PolyComputes (fun x=>encode (f x))) (hg : PolyComputes (fun x=>encode (g x))) :
    PolyComputes (fun x=>encode (f x*g x)) := by
  have hh := (hf.pair hg).comp mulWords_computes
  simpa only [Function.comp_def,mulWords_pair] using hh
noncomputable def sub {f g : List Bool → ℚ}
    (hf : PolyComputes (fun x=>encode (f x))) (hg : PolyComputes (fun x=>encode (g x))) :
    PolyComputes (fun x=>encode (f x-g x)) := by
  have hh := (hf.pair hg).comp subWords_computes
  simpa only [Function.comp_def,subWords_pair] using hh
noncomputable def div {f g : List Bool → ℚ}
    (hf : PolyComputes (fun x=>encode (f x))) (hg : PolyComputes (fun x=>encode (g x))) :
    PolyComputes (fun x=>encode (f x/g x)) := by
  have hh := (hf.pair hg).comp divWords_computes
  simpa only [Function.comp_def,divWords_pair] using hh
noncomputable def floor {f : List Bool → ℚ} (hf : PolyComputes (fun x=>encode (f x))) :
    PolyComputes (fun x=>encode ((⌊f x⌋:ℤ):ℚ)) := by
  have hi : PolyComputes (fun x=>Signed.encode (⌊f x⌋:ℤ)) := by
    have hh := hf.comp floorWords_computes
    simpa only [Function.comp_def,floorWords_encode] using hh
  have hh := hi.comp castIntWords_computes
  simpa only [Function.comp_def,castIntWords_encode] using hh
noncomputable def root {f : List Bool → ℚ} {d : List Bool → ℕ}
    (hf : PolyComputes (fun x=>encode (f x))) (hd : PolyComputes (fun x=>(d x).bits)) :
    PolyComputes (fun x=>encode (Ellipsoid.rationalRootUpper (d x) (f x))) := by
  have hh := (hf.pair hd).comp BinaryEllipsoidRoot.run_computes
  simpa only [Function.comp_def,BinaryEllipsoidRoot.run_encode] using hh
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

noncomputable def haWords_computes : PolyComputes haWords := haInput_computes.comp mulVec_computes
noncomputable def quadWords_computes : PolyComputes quadWords := haInput_computes.comp quad_computes
noncomputable def qvalue_computes : PolyComputes (fun x=>BinaryRational.encode (qvalue x)) := RatOps.ofWords quadWords_computes

noncomputable def coefA_computes : PolyComputes coefA := by
  have hn := RatOps.mul dimension_computes dimension_computes
  have hh := RatOps.div hn (RatOps.sub hn (RatOps.const 1))
  change PolyComputes (fun x=>BinaryRational.encode (dimension x^2/(dimension x^2-1)))
  simpa only [pow_two] using hh
noncomputable def coefB_computes : PolyComputes coefB :=
  RatOps.div (RatOps.const 2) (RatOps.mul (RatOps.add dimension_computes (RatOps.const 1)) qvalue_computes)
noncomputable def coefInflate_computes : PolyComputes coefInflate := by
  have hn := RatOps.mul dimension_computes dimension_computes
  have hh := RatOps.div (RatOps.const 1) (RatOps.sub (RatOps.const 1)
    (RatOps.div (RatOps.const 1) (RatOps.mul (RatOps.const 8) hn)))
  change PolyComputes (fun x=>BinaryRational.encode (1/(1-1/(8*dimension x^2))))
  simpa only [pow_two] using hh

noncomputable def root_computes : PolyComputes
    (fun x=>BinaryRational.encode (Ellipsoid.rationalRootUpper (rootPrecision x) (qvalue x))) :=
  RatOps.root qvalue_computes rootPrecision_computes
noncomputable def coefCenter_computes : PolyComputes coefCenter :=
  RatOps.div (RatOps.const 1) (RatOps.mul (RatOps.add dimension_computes (RatOps.const 1)) root_computes)

noncomputable def scaledHaInput_computes : PolyComputes scaledHaInput := coefCenter_computes.pair haWords_computes
noncomputable def scaledHa_computes : PolyComputes scaledHa := scaledHaInput_computes.comp vectorScale_computes
noncomputable def centerInput_computes : PolyComputes centerInput := center_computes.pair scaledHa_computes
noncomputable def centerWords_computes : PolyComputes centerWords := centerInput_computes.comp vectorSub_computes
noncomputable def outerInput_computes : PolyComputes outerInput := haWords_computes.pair haWords_computes
noncomputable def outerWords_computes : PolyComputes outerWords := outerInput_computes.comp outer_computes
noncomputable def scaledOuterInput_computes : PolyComputes scaledOuterInput := coefB_computes.pair outerWords_computes
noncomputable def scaledOuter_computes : PolyComputes scaledOuter := scaledOuterInput_computes.comp matrixScale_computes
noncomputable def differenceInput_computes : PolyComputes differenceInput := shape_computes.pair scaledOuter_computes
noncomputable def difference_computes : PolyComputes difference := differenceInput_computes.comp matrixSub_computes
noncomputable def cutInput_computes : PolyComputes cutInput := coefA_computes.pair difference_computes
noncomputable def cutWords_computes : PolyComputes cutWords := cutInput_computes.comp matrixScale_computes
noncomputable def inflateInput_computes : PolyComputes inflateInput := coefInflate_computes.pair cutWords_computes
noncomputable def inflateWords_computes : PolyComputes inflateWords := inflateInput_computes.comp matrixScale_computes
end BinaryEllipsoidCut
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Pack6
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
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

noncomputable def entry_computes : PolyComputes entry := entryInput_computes.comp getEntry_computes
noncomputable def qvalue_computes : PolyComputes (fun x=>BinaryRational.encode (qvalue x)) := RatOps.ofWords entry_computes
noncomputable def floorValue_computes : PolyComputes (fun x=>BinaryRational.encode (floorValue x)) :=
  RatOps.div (RatOps.floor (RatOps.mul scale_computes qvalue_computes)) scale_computes
noncomputable def diagonal_computes : PolyComputes (fun x=>BinaryRational.encode (diagonal x)) :=
  RatOps.div dimension_computes scale_computes
noncomputable def entryWords_computes : PolyComputes entryWords := by
  have hh := (NatOps.le row_computes col_computes).cond
    ((NatOps.le col_computes row_computes).cond (RatOps.add floorValue_computes diagonal_computes)
      floorValue_computes) floorValue_computes
  unfold entryWords
  simpa only [decide_eq_true_eq] using hh
noncomputable def rowInput_computes : PolyComputes rowInput :=
  id_computes.pair ((extractPrefix_computes.comp shape_computes).comp Indices.run_computes)
noncomputable def rowWords_computes : PolyComputes rowWords := rowInput_computes.comp (mapWith_computes entryWords_computes)
noncomputable def runInput_computes : PolyComputes runInput :=
  id_computes.pair (shape_computes.comp Indices.run_computes)
noncomputable def run_computes : PolyComputes run := runInput_computes.comp (mapWith_computes rowWords_computes)
end BinaryEllipsoidGrid
namespace BinaryEllipsoidCut
noncomputable def gridInput_computes : PolyComputes gridInput := dim_computes.pair (precision_computes.pair inflateWords_computes)
noncomputable def shapeWords_computes : PolyComputes shapeWords := gridInput_computes.comp BinaryEllipsoidGrid.run_computes
end BinaryEllipsoidCut
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_OptionEncode
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine

section
open WordOperations
namespace WordList.Find

noncomputable def operation_computes {p : List Bool → Bool} (hp : PolyComputes (fun x=>[p x])) :
    PolyComputes (operation p) := by
  have hc := (context_computes.pair item_computes).comp hp
  have hi := item_computes.comp (prefix_computes true)
  have h₁ := hc.cond hi (const_computes [])
  have h₂ := (accum_computes.comp isEmpty_computes).cond h₁ accum_computes
  unfold operation
  simpa only [Function.comp_def,decide_eq_true_eq] using h₂

noncomputable def run_computes {p : List Bool → Bool} (hp : PolyComputes (fun x=>[p x])) :
    PolyComputes (run p) :=
  (Fold.pack_computes discardPrefix_computes extractPrefix_computes (const_computes [])).comp
    (Fold.run_computes (operation_computes hp) (3*Polynomial.X+3))

end WordList.Find
end
open WordOperations BinaryArithmetic RationalLinearFeasibility
namespace BinaryRow
open RationalMatrix

noncomputable def dotInput_computes : PolyComputes dotInput := coeff_computes.pair extractPrefix_computes
noncomputable def dot_computes : PolyComputes dot := dotInput_computes.comp RationalArray.dotListsWords_computes
noncomputable def good_computes : PolyComputes (fun x=>[good x]) := by
  have hh := ((RatOps.ofWords dot_computes).pair (RatOps.ofWords bound_computes)).comp BinaryRational.leWords_computes
  simpa only [good,Function.comp_def,BinaryRational.leWords_pair] using hh
noncomputable def bad_computes : PolyComputes (fun x=>[bad x]) := by
  have hh := good_computes.cond (const_computes [false]) (const_computes [true])
  change PolyComputes (fun x=>[!good x])
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  cases good x <;> rfl
noncomputable def run_computes : PolyComputes run := WordList.Find.run_computes bad_computes
end BinaryRow
namespace BinaryEllipsoidAdvance
open Ellipsoid RationalMatrix
open scoped Matrix

noncomputable def found_computes : PolyComputes found := (center_computes.pair rows_computes).comp BinaryRow.run_computes
noncomputable def direction_computes : PolyComputes direction :=
  (found_computes.comp tail_computes).comp extractPrefix_computes
noncomputable def normWords_computes : PolyComputes normWords :=
  (direction_computes.pair direction_computes).comp RationalArray.dotListsWords_computes
noncomputable def zeroDirection_computes : PolyComputes (fun x=>[zeroDirection x]) := by
  have hh := ((RatOps.ofWords normWords_computes).pair (RatOps.const 0)).comp BinaryRational.leWords_computes
  simpa only [zeroDirection,Function.comp_def,BinaryRational.leWords_pair] using hh
noncomputable def cutInput_computes : PolyComputes cutInput :=
  dim_computes.pair (shape_computes.pair (direction_computes.pair (center_computes.pair precision_computes)))
noncomputable def updated_computes : PolyComputes updated := by
  unfold updated
  simpa only [Function.comp_def] using
    (cutInput_computes.comp BinaryEllipsoidCut.shapeWords_computes).pair
      (cutInput_computes.comp BinaryEllipsoidCut.centerWords_computes)
noncomputable def nextState_computes : PolyComputes nextState := by
  have hh := (found_computes.comp isEmpty_computes).cond stored_computes
    (zeroDirection_computes.cond stored_computes updated_computes)
  unfold nextState
  simpa only [Function.comp_def,decide_eq_true_eq] using hh
noncomputable def run_computes : PolyComputes run :=
  dim_computes.pair (precision_computes.pair (rows_computes.pair nextState_computes))
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

open WordOperations BinaryArithmetic RationalLinearFeasibility Ellipsoid RationalHeight
namespace BinaryEllipsoidIteration
open RationalMatrix BinaryEllipsoidAdvance

noncomputable def run_computes : PolyComputes run :=
  prepared_computes.comp (BoundedIteration.run_computes BinaryEllipsoidAdvance.run_computes)
end BinaryEllipsoidIteration
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

noncomputable def dimBits_computes : PolyComputes dimBits := nword_computes.comp lengthBits_computes
noncomputable def cubeWords_computes : PolyComputes cubeWords := by
  unfold cubeWords
  have hh := NatOps.mul (NatOps.mul dimBits_computes dimBits_computes) dimBits_computes
  simpa only [value_bits] using hh
noncomputable def gridWords_computes : PolyComputes gridWords := by
  unfold gridWords
  have hh := NatOps.mul (NatOps.mul (const_computes (16:ℕ).bits) cubeWords_computes) powerWords_computes
  simpa only [value_bits] using hh
noncomputable def radiusSquare_computes : PolyComputes radiusSquare :=
  RatOps.mul (RatOps.nat radius_computes) (RatOps.nat radius_computes)
noncomputable def shapeWords_computes : PolyComputes shapeWords := by
  unfold shapeWords
  simpa only [Function.comp_def] using
    (nword_computes.pair radiusSquare_computes).comp BinaryEllipsoidInitial.run_computes
noncomputable def advanceInput_computes : PolyComputes advanceInput :=
  dimBits_computes.pair (gridWords_computes.pair (rows_computes.pair (shapeWords_computes.pair centerWords_computes)))
noncomputable def prepared_computes : PolyComputes prepared :=
  budgetWord_computes.pair (radius_computes.pair advanceInput_computes)
noncomputable def iterated_computes : PolyComputes iterated := prepared_computes.comp BinaryEllipsoidIteration.run_computes
noncomputable def result_computes : PolyComputes result := by
  have hh := (BinaryEllipsoidAdvance.found_computes.comp isEmpty_computes).cond
    (BinaryEllipsoidAdvance.center_computes.comp (prefix_computes true)) (const_computes [])
  unfold result
  simpa only [Function.comp_def,decide_eq_true_eq] using hh
noncomputable def run_computes : PolyComputes run := iterated_computes.comp result_computes
end BinaryWeakSolve
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

noncomputable def epsilon_computes : PolyComputes epsilon := RatOps.div (RatOps.const 1) (RatOps.nat doubledGap_computes)
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

noncomputable def relaxedOp_computes : PolyComputes relaxedOp :=
  (discardPrefix_computes.comp extractPrefix_computes).pair
    (RatOps.add (RatOps.ofWords (discardPrefix_computes.comp discardPrefix_computes))
      (RatOps.ofWords extractPrefix_computes))
noncomputable def relaxedWords_computes : PolyComputes relaxedWords := by
  unfold relaxedWords
  simpa only [Function.comp_def] using
    (PolyComputes.comp (f:=fun input=>pairBits (epsilon input,boundedWords input))
      (g:=mapWith relaxedOp) (epsilon_computes.pair boundedWords_computes)
      (mapWith_computes relaxedOp_computes))
noncomputable def prepared_computes : PolyComputes prepared :=
  nword_computes.pair (precision_computes.pair (radiusPrecision_computes.pair (radius_computes.pair relaxedWords_computes)))
noncomputable def solved_computes : PolyComputes solved := prepared_computes.comp BinaryWeakSolve.run_computes
noncomputable def run_computes : PolyComputes run := by
  have hh := (solved_computes.comp isEmpty_computes).cond (const_computes [false]) (const_computes [true])
  unfold run
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  by_cases h : solved x=[] <;> simp [h]
end BinaryDecision
end
open WordOperations BinaryArithmetic
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

noncomputable def run_computes : PolyComputes run := prepared_computes.comp BinaryDecision.run_computes
end BinaryBoundedDecision
namespace BinaryClearRow
open WordOperations BinaryArithmetic RationalLinearFeasibility Ellipsoid PolytopeCertificate
open WordList RationalMatrix

noncomputable def denOp_computes : PolyComputes denOp := discardPrefix_computes.comp BinaryRational.denominator_computes
noncomputable def denominators_computes : PolyComputes denominators := by
  unfold denominators
  simpa only [Function.comp_def] using
    (PolyComputes.comp (f:=fun input=>pairBits ([],entries input)) (g:=mapWith denOp)
      ((const_computes []).pair entries_computes) (mapWith_computes denOp_computes))
noncomputable def denominator_computes : PolyComputes denominator := denominators_computes.comp NaturalArray.productWords_computes

noncomputable def scalar_computes : PolyComputes scalar := RatOps.nat denominator_computes
noncomputable def coeffWords_computes : PolyComputes coeffWords := by
  unfold coeffWords
  simpa only [Function.comp_def] using
    (PolyComputes.comp (f:=fun input=>pairBits (scalar input,extractPrefix input))
      (g:=mapWith BinaryRational.mulWords)
      (scalar_computes.pair extractPrefix_computes) (mapWith_computes BinaryRational.mulWords_computes))
noncomputable def boundWords_computes : PolyComputes boundWords :=
  RatOps.mul (RatOps.nat denominator_computes) (RatOps.ofWords discardPrefix_computes)
end BinaryClearRow

open WordOperations
end MetricKMedianRecovery.BitMachine

end OAI
end


