-- Prove2me | Definitions.Def_Q238K009
-- name    : Q238K009
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T23:13:32.011543+00:00
-- url     : https://prove2.me/theorems/2f013b9a-8155-4711-87a5-779aa0b1f0ed
-- title:
--   Definitions bundle Q238K009 of the split of OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 94 declarations of OpenAI's Lean: 56 definitions and 38 theorems. The definitions and types are `OAI.MetricKMedianRecovery.BitMachine.BinaryActions.delete`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDelete.cf`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDelete.rest`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDelete.sf`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDivision.digitBit`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDivision.digitRem`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDivision.digits`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDivision.divide`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDivision.divisor`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDivision.doubled`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDivision.mass`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDivision.next`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDivision.nextBit`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDivision.process`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDivision.quotient`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDivision.rank`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDivision.rawDivide`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDivision.reduced`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDivision.remainder`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDivision.setupWords`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDivision.step`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDivision.withDivision`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidRoot.den`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidRoot.denom`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidRoot.numAbs`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidRoot.precision`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidRoot.radicand`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidRoot.rawWords`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidRoot.upper`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteInsert.new`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteInsert.old`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGCD.Good`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGCD.rank`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGCD.secondRem`, `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseCount.cf`, `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseUpdate.allFacilities`, `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseUpdate.context`, `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseUpdate.ctxField`, `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseUpdate.newBudget`, `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseUpdate.newFacility` and 16 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedianRecovery_Encoding_DivNatWords`, `KMedianRecovery_Encoding_NatWords`, `KMedianRecovery_Encoding_StateBits`, `KMedianRecovery_Machines_ActionMachine`, `KMedianRecovery_Machines_DeleteFold`, `KMedianRecovery_Recovery_DigitBit`, `KMedianRecovery_Recovery_FilterItem`, `KMedianRecovery_Recovery_FinishPhase`, `KMedianRecovery_Recovery_LeftNum`, `KMedianRecovery_Recovery_Next`, `KMedianRecovery_Recovery_NumAbs`, `KMedianRecovery_Recovery_Pack`, `KMedianRecovery_Recovery_Pack2`, `KMedianRecovery_Recovery_ProcessOutputs`, `KMedianRecovery_Recovery_RawSlices`.
--
--   **Imports.** It imports the published bundle `Def_KMedianRefinedRecovery`; the bundles `Q238K000`, `Q238K001` and `Q238K002` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q238K019` and `Q238K021`; the proof of `OAI.MetricKMedianRecovery.BitMachine.RationalMatrix.determinantWords_encode_s238`.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_KMedianRefinedRecovery
import Definitions.Def_Q238K000
import Definitions.Def_Q238K001
import Definitions.Def_Q238K002

section
-- module Solutions.Q238_KM.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
@[simp] theorem fin5_lit_0_2 : ((0 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_0_3 : ((0 : Fin 5) = 3) ↔ False := by decide
@[simp] theorem fin5_lit_0_4 : ((0 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_1_2 : ((1 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_1_3 : ((1 : Fin 5) = 3) ↔ False := by decide
@[simp] theorem fin5_lit_1_4 : ((1 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_2_3 : ((2 : Fin 5) = 3) ↔ False := by decide
@[simp] theorem fin5_lit_2_4 : ((2 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_3_4 : ((3 : Fin 5) = 4) ↔ False := by decide
end OAICompat434

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
open BinaryArithmetic BinarySubtraction

def digits (x : List Bool) := extractPrefix x.tail
def divisor (x : List Bool) := extractPrefix (discardPrefix x.tail)
def quotient (x : List Bool) := extractPrefix (discardPrefix (discardPrefix x.tail))
def remainder (x : List Bool) := discardPrefix (discardPrefix (discardPrefix x.tail))

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

lemma length_pack (a : Bool) (d y q r : List Bool) :
    (pack a d y q r).length=2*d.length+2*y.length+2*q.length+r.length+4 := by
  simp only [pack,List.length_cons,pairBits_length]
  omega

def doubled (x : List Bool) : List Bool := (digits x).head?.getD false :: remainder x
def nextBit (x : List Bool) : Bool := decide (value (divisor x) ≤ value (doubled x))
def reduced (x : List Bool) : List Bool :=
  if nextBit x then normalize (subtract (doubled x) (divisor x)) else doubled x

def step (x : List Bool) : List Bool :=
  if digits x=[] then pack false [] (divisor x) (quotient x) (remainder x)
  else pack true (digits x).tail (divisor x) (nextBit x::quotient x) (reduced x)

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

def next := While.next step

def rank (x : List Bool) : ℕ := if x.head?=some true then (digits x).length+1 else 0

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
open BinaryArithmetic BinarySubtraction

def digitBit (b : Bool) (y r : List Bool) : Bool := decide (value y ≤ value (b::r))
def digitRem (b : Bool) (y r : List Bool) : List Bool :=
  if digitBit b y r then BinaryArithmetic.normalize (subtract (b::r) y) else b::r

def process : List Bool → List Bool → List Bool → List Bool → List Bool × List Bool
  | [],_,q,r => (q,r)
  | b::ds,y,q,r => process ds y (digitBit b y r::q) (digitRem b y r)

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

def setupWords (x : List Bool) : List Bool :=
  pack true (extractPrefix x).reverse (discardPrefix x) [] []

def withDivision (x : List Bool) : List Bool := next^[rank (setupWords x)] (setupWords x)

def rawDivide (x : List Bool) : List Bool :=
  pairBits (normalize (quotient (withDivision x)),normalize (remainder (withDivision x)))

def divide (x : List Bool) : List Bool :=
  if value (discardPrefix x)=0 then pairBits ([],normalize (extractPrefix x)) else rawDivide x

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
open BinaryArithmetic BinarySubtraction

def secondRem (x : List Bool) : List Bool :=
  (value (second x)%(value (first x)%value (second x))).bits

def rank (x : List Bool) : ℕ := if x.head?=some true then measure x+1 else 0
def Good (x : List Bool) : Prop := x.head?=some true ∨ value (second x)=0

@[simp] lemma rank_true (a b : List Bool) : rank (pack true a b)=measure (pack true a b)+1 := rfl
@[simp] lemma rank_false (a b : List Bool) : rank (pack false a b)=0 := rfl

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

open BinaryArithmetic
namespace Signed

lemma encode_mag (z : ℤ) : mag (encode z)=z.natAbs := by
  simp only [mag,encode,List.tail_cons,value_bits]

end Signed
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
open BinaryArithmetic
namespace BinaryRational

lemma negWords_encode (x : ℚ) : negWords (encode x)=encode (-x) := by
  simp only [negWords,numerator_encode,denominator_encode,Signed.encode_decode]
  simp only [encode,Rat.num_neg_eq_neg_num,Rat.den_neg_eq_den]

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
open BinaryArithmetic
namespace Signed

lemma signed_ediv_nat (s : Bool) (n d : ℕ) : signed s n/(d:ℤ)=
    if d=0 then 0 else if s then
      if n%d=0 then signed true (n/d) else signed true (n/d+1)
    else signed false (n/d) := by
  by_cases hd : d=0
  · simp only [hd,Int.natCast_zero,Int.ediv_zero,ite_true, if_true]
  · have hp : (0:ℤ)<d := by exact_mod_cast Nat.pos_of_ne_zero hd
    cases s with
    | false => simp only [ite_eq_right hd,Bool.false_eq_true,ite_false, if_false,signed,Int.natCast_ediv]
    | true =>
      simp only [ite_eq_right hd,ite_true, if_true,signed,Int.neg_ediv,Int.natCast_ediv,
        Int.natCast_dvd_natCast,Nat.dvd_iff_mod_eq_zero,Int.sign_eq_one_of_pos hp]
      split_ifs <;> omega

end Signed
namespace BinaryRational

def castIntWords (x : List Bool) : List Bool := pairBits (x,Nat.bits 1)
lemma castIntWords_encode (z : ℤ) : castIntWords (Signed.encode z)=encode (z:ℚ) := by
  simp only [castIntWords,encode,Rat.num_intCast,Rat.den_intCast]

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
open BinaryArithmetic
namespace Signed
noncomputable def natWords (x : List Bool) : List Bool := if sign x then [] else normalize x.tail
end Signed
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
open BinaryArithmetic
namespace BinarySqrt

def pack (n l u : ℕ) : List Bool := pairBits (n.bits,pairBits (l.bits,u.bits))
def low (x : List Bool) : List Bool := extractPrefix (discardPrefix x)
def high (x : List Bool) : List Bool := discardPrefix (discardPrefix x)

def middle (x : List Bool) : List Bool := ((value (low x)+value (high x))/2).bits

def leftCase (x : List Bool) : List Bool := pairBits (extractPrefix x,pairBits (middle x,high x))
def rightCase (x : List Bool) : List Bool := pairBits (extractPrefix x,pairBits (low x,middle x))
def step (x : List Bool) : List Bool :=
  if value (middle x)*value (middle x)≤value (extractPrefix x) then leftCase x else rightCase x
lemma step_pack (n l u : ℕ) : step (pack n l u)=pack n (next n (l,u)).1 (next n (l,u)).2 := by
  simp only [step,middle,low,high,pack,extractPrefix_pairBits,discardPrefix_pairBits,value_bits,
    leftCase,rightCase,next]
  split_ifs <;> rfl
lemma iterate_pack (n t : ℕ) : step^[t] (pack n 0 (n+1))=
    pack n (interval n t).1 (interval n t).2 := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply',ih,step_pack]; rfl
lemma length_pack (n l u : ℕ) : (pack n l u).length=2*n.size+2*l.size+u.size+2 := by
  simp only [pack,pairBits_length,Nat.size_eq_bits_len]
  omega
lemma iterate_length (n t : ℕ) : (step^[t] (pack n 0 (n+1))).length≤5*n.size+5 := by
  rw [iterate_pack,length_pack]
  have hh := interval_bracket n t
  have hu : (interval n t).2.size≤n.size+1 := by
    have h := Nat.size_le_size (hh.2.2.2.trans (Nat.lt_size_self n))
    simpa only [Nat.size_pow] using h
  have hl := Nat.size_le_size hh.1.le
  omega

def startWords (x : List Bool) : List Bool := pairBits (x,pairBits ([],(value x+1).bits))
lemma startWords_bits (n : ℕ) : startWords n.bits=pack n 0 (n+1) := by
  simp only [startWords,value_bits,pack]
  rfl

noncomputable def run (x : List Bool) : List Bool :=
  low (BoundedIteration.polynomialRun step (Polynomial.X+1) (10*(Polynomial.X+1)) (startWords x))
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
open BinaryArithmetic
namespace BinaryEllipsoidRoot

def numAbs (x : List Bool) : List Bool := (extractPrefix (extractPrefix x)).tail
def den (x : List Bool) : List Bool := discardPrefix (extractPrefix x)
def precision (x : List Bool) : List Bool := discardPrefix x

def radicand (x : List Bool) : List Bool :=
  (value (numAbs x)*value (den x)*(value (precision x)*value (precision x))).bits
noncomputable def upper (x : List Bool) : List Bool := (value (BinarySqrt.run (radicand x))+1).bits

def denom (x : List Bool) : List Bool := (value (den x)*value (precision x)).bits
noncomputable def rawWords (x : List Bool) : List Bool :=
  pairBits (Signed.encode (value (upper x):ℤ),denom x)
end BinaryEllipsoidRoot
open BinaryArithmetic
open scoped Matrix
namespace BinaryRational

def natWords (x : List Bool) : List Bool := castIntWords (Signed.encode (value x:ℤ))
end BinaryRational
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
open BinaryArithmetic
namespace WordList
noncomputable def filterItem (p : List Bool → Bool) (x : List Bool) : List Bool :=
  if p x then encode [discardPrefix x] else []
end WordList
namespace BinaryFiniteInsert
open WordList BinaryPhaseFirst

def old : List Bool → List Bool := extractPrefix ∘ extractPrefix
def new : List Bool → List Bool := discardPrefix ∘ extractPrefix
end BinaryFiniteInsert
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_StateBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryPhaseUpdate
open BinaryArithmetic WordList
open BinaryOpeningPayment

def context : List Bool → List Bool := extractPrefix ∘ extractPrefix
def oldBudget : List Bool → List Bool := discardPrefix ∘ extractPrefix
def newFacility : List Bool → List Bool := extractPrefix ∘ discardPrefix
def newBudget : List Bool → List Bool := discardPrefix ∘ discardPrefix
def ctxField (k : ℕ) : List Bool → List Bool := field k ∘ context
noncomputable def allFacilities : List Bool → List Bool := Indices.run ∘ field 0
end MetricKMedianRecovery.BitMachine.BinaryPhaseUpdate

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
open BinaryArithmetic WordList BinaryPhaseUpdate BinaryOpeningPayment
attribute [local irreducible] WordList.Indices.run WordList.Lookup.run
  WordList.Fold.run
noncomputable def cf (k : ℕ) : List Bool → List Bool := field k ∘ extractPrefix
end MetricKMedianRecovery.BitMachine.BinaryPhaseCount

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
open BinaryArithmetic
def step (x : List Bool) : List Bool :=
  if value (extractPrefix x)=0 then x
  else pairBits ((value (extractPrefix x)-1).bits,List.tail (discardPrefix x))
lemma rest_step (x : List Bool) : (discardPrefix (step x)).length ≤ (discardPrefix x).length := by
  unfold step; split_ifs
  · exact le_rfl
  · rw [discardPrefix_pairBits]; exact by simp only [List.length_tail]; omega
def run (x : List Bool) : List Bool := discardPrefix (step^[x.length] x)
end MetricKMedianRecovery.BitMachine.RawDrop

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_ActionMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryActions
open WordList BinaryArithmetic
open BinaryOpeningPayment (field )
open RationalSampling
variable {n : ℕ}
noncomputable def delete (x : List Bool) : List Bool := encode [(1:ℕ).bits,discardPrefix x,[]]
end MetricKMedianRecovery.BitMachine.BinaryActions

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
open WordList RationalLeaves
open BinaryOpeningPayment (field )

def cf (n : ℕ) (x : List Bool) : List Bool := field n (extractPrefix x)
def sf (n : ℕ) (x : List Bool) : List Bool := field n (discardPrefix (discardPrefix x))
noncomputable def rest (x : List Bool) : List Bool := WordList.tail (sf 0 x)
end MetricKMedianRecovery.BitMachine.BinaryDelete

end OAI
end


