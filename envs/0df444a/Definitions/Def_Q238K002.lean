-- Prove2me | Definitions.Def_Q238K002
-- name    : Q238K002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T23:10:57.105934+00:00
-- url     : https://prove2.me/theorems/b6a3ee27-8bc5-4469-b6d0-b942dffa1c97
-- title:
--   Definitions bundle Q238K002 of the split of OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 150 declarations of OpenAI's Lean: 105 definitions, 4 inductive types or structures and 41 theorems. The definitions and types are `OAI.MetricKMedianRecovery.BitMachine.BinaryArithmetic.add`, `OAI.MetricKMedianRecovery.BitMachine.BinaryArithmetic.carryBit`, `OAI.MetricKMedianRecovery.BitMachine.BinaryArithmetic.mulFrom`, `OAI.MetricKMedianRecovery.BitMachine.BinaryArithmetic.normalize`, `OAI.MetricKMedianRecovery.BitMachine.BinaryArithmetic.sumBit`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueLoop.capPoly`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchCheck.Ready`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchContext.balls`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.objective`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.rationalScore`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.drawn`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.elements`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletion.capped`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletion.savingQ`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletion.surrogateQ`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDelete.capacityPoly`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDivision.evalMSB`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDivision.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidIteration.centerPoly`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidIteration.incrementPoly`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidIteration.quadPoly`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidIteration.shapePoly`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidIteration.storagePoly`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidIteration.vectorPoly`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFinSet.values`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRationalSort.bottomValues`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRationalSort.indexSet`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRationalSort.ranking`, `OAI.MetricKMedianRecovery.BitMachine.BinarySqrt.Bracket`, `OAI.MetricKMedianRecovery.BitMachine.BinarySqrt.interval`, `OAI.MetricKMedianRecovery.BitMachine.BinarySqrt.next`, `OAI.MetricKMedianRecovery.BitMachine.BinarySubtraction.borrowBit`, `OAI.MetricKMedianRecovery.BitMachine.BinarySubtraction.difference`, `OAI.MetricKMedianRecovery.BitMachine.BinarySubtraction.subtract`, `OAI.MetricKMedianRecovery.BitMachine.Signed.signed`, `OAI.MetricKMedianRecovery.BlueDP.Atom`, `OAI.MetricKMedianRecovery.BlueDP.Candidate`, `OAI.MetricKMedianRecovery.BlueDP.Table`, `OAI.MetricKMedianRecovery.BlueDP.states`, `OAI.MetricKMedianRecovery.BlueDP.value` and 69 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedianRecovery_Branching_BlueChoice`, `KMedianRecovery_Branching_BlueDPValue`, `KMedianRecovery_Branching_BlueTable`, `KMedianRecovery_Branching_BlueTableSize`, `KMedianRecovery_Branching_BranchContext`, `KMedianRecovery_Branching_BranchObjective`, `KMedianRecovery_Branching_BranchPhysical`, `KMedianRecovery_Branching_BranchWeights`, `KMedianRecovery_Branching_CategoricalChoice`, `KMedianRecovery_Branching_CategoricalResources`, `KMedianRecovery_Branching_CategoricalRule`, `KMedianRecovery_Branching_CategoricalTable`, `KMedianRecovery_Branching_CompletionFillMath`, `KMedianRecovery_Branching_CompletionRealizeMath`, `KMedianRecovery_Branching_CopyGround`, `KMedianRecovery_Branching_RationalBranch`, `KMedianRecovery_Branching_RationalSurrogate`, `KMedianRecovery_Encoding_FinSets`, `KMedianRecovery_Encoding_PushWord`, `KMedianRecovery_Encoding_RationalBottomIndices`, `KMedianRecovery_Encoding_RationalCap`, `KMedianRecovery_Encoding_RationalLeaves`, `KMedianRecovery_Encoding_RationalMenus`, `KMedianRecovery_Encoding_RationalSort`, `KMedianRecovery_Encoding_UniformBits`, `KMedianRecovery_Geometry_MetricArrays`, `KMedianRecovery_Machines_DeleteSize`, `KMedianRecovery_Recovery_Advance`, `KMedianRecovery_Recovery_Average`, `KMedianRecovery_Recovery_BorrowBit`, `KMedianRecovery_Recovery_BottomMath`, `KMedianRecovery_Recovery_BoundRow`, `KMedianRecovery_Recovery_DigitBit`, `KMedianRecovery_Recovery_DyadicGrid`, `KMedianRecovery_Recovery_GridFloor`, `KMedianRecovery_Recovery_InitialState2`, `KMedianRecovery_Recovery_LeftNum`, `KMedianRecovery_Recovery_Mul`, `KMedianRecovery_Recovery_MulComputes`, `KMedianRecovery_Recovery_Next`, `KMedianRecovery_Recovery_Normalize`, `KMedianRecovery_Recovery_Op`, `KMedianRecovery_Recovery_OrderedMaximum`, `KMedianRecovery_Recovery_Pack`, `KMedianRecovery_Recovery_Pack2`, `KMedianRecovery_Recovery_Pack7`, `KMedianRecovery_Recovery_PhasesBounded`, `KMedianRecovery_Recovery_ProcessOutputs`, `KMedianRecovery_Recovery_RealVector`, `KMedianRecovery_Recovery_Row`, `KMedianRecovery_Recovery_Score`, `KMedianRecovery_Recovery_SetFunction`, `KMedianRecovery_Recovery_State2`, `KMedianRecovery_Recovery_Step`, `KMedianRecovery_Recovery_StepThen`, `KMedianRecovery_Recovery_Table`, `KMedianRecovery_Recovery_TableValue`, `KMedianRecovery_Recovery_Value`, `KMedianRecovery_Sampling_RationalSampling`.
--
--   **Imports.** It imports the published bundle `Def_KMedianRefinedRecovery`.
--
--   **Imported by** (directly, in this split): the bundles `Q238K007`, `Q238K008`, `Q238K009`, `Q238K010`, `Q238K011`, `Q238K012`, `Q238K013`, `Q238K014`, `Q238K015` and `Q238K016`; the statements `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionFair.realize_le_surrogate_s238`, `OAI.MetricKMedianRecovery.Ellipsoid.rationalRootUpper_bounds_s238`, `OAI.MetricKMedianRecovery.FiniteSampling.average_le_threshold_add_failure_s238` and `OAI.MetricKMedianRecovery.FiniteSampling.probability_prefix_s238`; the proofs of `OAI.MetricKMedianRecovery.Ellipsoid.rationalRootUpper_bounds_s238`, `OAI.MetricKMedianRecovery.FiniteSampling.average_le_threshold_add_failure_s238` and `OAI.MetricKMedianRecovery.FiniteSampling.probability_prefix_s238`.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_KMedianRefinedRecovery

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Row
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalLinearFeasibility

structure Row (n : ℕ) where
  coeff : Fin n → ℚ
  bound : ℚ

end MetricKMedianRecovery.RationalLinearFeasibility

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_StepThen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open Turing Turing.TM2 StateTransition

lemma unit_update {α : Type} (f : Unit → α) (a : α) :
    Function.update f () a = fun _ => a := by
  funext u
  cases u
  simp only [Function.update_self]

end MetricKMedianRecovery.BitMachine

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

def sumBit (c x y : Bool) : Bool := xor (xor c x) y
def carryBit (c x y : Bool) : Bool := (c && x) || (c && y) || (x && y)

lemma fullAdder (c x y : Bool) :
    (sumBit c x y).toNat+2*(carryBit c x y).toNat=c.toNat+x.toNat+y.toNat := by
  cases c <;> cases x <;> cases y <;> rfl

def add : Bool → List Bool → List Bool → List Bool
  | c,[],[] => if c then [true] else []
  | c,x::xs,[] => sumBit c x false :: add (carryBit c x false) xs []
  | c,[],y::ys => sumBit c false y :: add (carryBit c false y) [] ys
  | c,x::xs,y::ys => sumBit c x y :: add (carryBit c x y) xs ys
termination_by _ xs ys => xs.length+ys.length

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

def normalize (xs : List Bool) : List Bool :=
  (xs.reverse.dropWhile (fun b => !b)).reverse

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

def mulFrom : List Bool → List Bool → List Bool → List Bool
  | [],_,acc => acc
  | b::bs,ys,acc => mulFrom bs ys (if b then add false ys (false::acc) else false::acc)

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

def borrowBit (c x y : Bool) : Bool := ((!x) && (c || y)) || (c && y)

lemma fullSubtractor (c x y : Bool) :
    (sumBit c x y).toNat+y.toNat+c.toNat=x.toNat+2*(borrowBit c x y).toNat := by
  cases c <;> cases x <;> cases y <;> rfl

def difference : Bool → List Bool → List Bool → List Bool × Bool
  | c,[],[] => ([],c)
  | c,x::xs,[] => let r := difference (borrowBit c x false) xs []
    (sumBit c x false::r.1,r.2)
  | c,[],y::ys => let r := difference (borrowBit c false y) [] ys
    (sumBit c false y::r.1,r.2)
  | c,x::xs,y::ys => let r := difference (borrowBit c x y) xs ys
    (sumBit c x y::r.1,r.2)
termination_by _ xs ys => xs.length+ys.length

lemma difference_length (c : Bool) (xs ys : List Bool) :
    (difference c xs ys).1.length=max xs.length ys.length := by
  induction xs generalizing c ys with
  | nil =>
    induction ys generalizing c with
    | nil => simp only [difference,List.length_nil,Nat.max_self]
    | cons y ys ih => simp only [difference,List.length_cons,ih,List.length_nil,Nat.zero_max]
  | cons x xs ih =>
    cases ys with
    | nil => simp only [difference,List.length_cons,ih,List.length_nil,Nat.max_zero]
    | cons y ys => simp only [difference,List.length_cons,ih,max_add_add_right]

def subtract (xs ys : List Bool) : List Bool :=
  let r := difference false xs ys
  if r.2 then [] else r.1

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

lemma fold_orElse (xs : List Bool) (q : Option Bool) :
    xs.foldl (fun q b=>q.orElse (fun _=>some b)) q=q.orElse (fun _=>xs.head?) := by
  induction xs generalizing q with
  | nil => simp
  | cons b xs ih =>
    rw [List.foldl_cons,ih]
    cases q <;> simp

lemma fold_empty (xs : List Bool) (q : Bool) :
    xs.foldl (fun _ _=>false) q=if xs=[] then q else false := by
  induction xs generalizing q with
  | nil => simp
  | cons b xs ih => simp [ih]

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

def pack (active : Bool) (digits divisor quotient remainder : List Bool) : List Bool :=
  active :: pairBits (digits, pairBits (divisor, pairBits (quotient,remainder)))

lemma normalize_length (x : List Bool) : (normalize x).length ≤ x.length := by
  simpa only [BinaryArithmetic.normalize,List.length_reverse] using List.length_dropWhile_le (fun b:Bool=>!b) x.reverse
lemma subtract_length (x y : List Bool) : (subtract x y).length ≤ max x.length y.length := by
  dsimp only [subtract]
  split_ifs
  · simp
  · exact (difference_length false x y).le

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

def evalMSB : List Bool → ℕ → ℕ
  | [],n => n
  | b::bs,n => evalMSB bs (2*n+b.toNat)

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

lemma modulus_twice_lt (a b : ℕ) (_ha : 0<a) (hb : 0<b) (hle : b ≤ a) : 2*(a%b)<a := by
  have hm := Nat.mod_lt a hb
  by_cases h : 2*b ≤ a
  · omega
  · have hd : a/b=1 := Nat.div_eq_of_lt_le (by simpa using hle) (by omega)
    have he := Nat.mod_add_div a b
    rw [hd,Nat.mul_one] at he
    omega

lemma size_drop_of_twice_lt (r a : ℕ) (h : 2*r<a) : r.size<a.size := by
  have ha : 0<a.size := Nat.size_pos.mpr (by omega)
  obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ha)
  have he := Nat.lt_size_self a
  rw [hk,pow_succ] at he
  have hr : r<2^k := by omega
  have hs := Nat.size_le.mpr hr
  omega

lemma second_mod_size_drop (a b : ℕ) (hb : 0<b) (hr : 0<a%b) :
    (a%b).size+(b%(a%b)).size<a.size+b.size := by
  have h1 := Nat.size_le_size (Nat.mod_le a b)
  have h2 := size_drop_of_twice_lt (b%(a%b)) b
    (modulus_twice_lt b (a%b) hb hr (Nat.le_of_lt (Nat.mod_lt a hb)))
  omega

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

def signed (s : Bool) (n : ℕ) : ℤ := if s then -(n:ℤ) else (n:ℤ)

lemma signed_add (s t : Bool) (a b : ℕ) :
    signed s a+signed t b =
    if s=t then signed s (a+b)
    else if a≤b then signed t (b-a) else signed s (a-b) := by
  cases s <;> cases t <;> simp only [signed,Bool.false_eq_true,ite_false, if_false,ite_true, if_true,Bool.true_eq_false] <;>
    (try split_ifs) <;> omega

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
open BinaryArithmetic
namespace Signed

@[simp] lemma natAbs_signed (s : Bool) (n : ℕ) : (signed s n).natAbs=n := by
  cases s <;> simp [signed]
lemma signed_div_nat (s : Bool) (n d : ℕ) (hd : d∣n) :
    signed s (n/d)=signed s n/(d:ℤ) := by
  cases s <;> simp only [signed,Bool.false_eq_true,ite_false, if_false,ite_true, if_true,Int.natCast_ediv]
  rw [Int.neg_ediv_of_dvd (by exact_mod_cast hd)]

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

lemma signed_sign (z : ℤ) (d : ℕ) (hz : z≠0) :
    Signed.signed (decide (z<0)) d=z.sign*(d:ℤ) := by
  by_cases h : z<0
  · simp only [h,decide_true,Signed.signed,ite_true, if_true,Int.sign_eq_neg_one_of_neg h,neg_one_mul]
  · have hp : 0<z := by omega
    simp only [h,decide_false,Signed.signed,Bool.false_eq_true,ite_false, if_false,Int.sign_eq_one_of_pos hp,one_mul]

end BinaryRational
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
namespace BoundedIteration

lemma clamp_iterate_eq (f : List Bool → List Bool) (d n : ℕ) (s : List Bool)
    (h : ∀ j, j ≤ n → (f^[j] s).length ≤ d) :
    (fun s=>(f s).take d)^[n] s=f^[n] s := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply',ih (fun j hj=>h j (by omega))]
    simpa only [Function.iterate_succ_apply'] using List.take_of_length_le (by simpa only [Function.iterate_succ_apply'] using h (n+1) le_rfl)

end BoundedIteration
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

open BinaryArithmetic
namespace WordList
namespace Indices

lemma bits_length_le (n : ℕ) : n.bits.length ≤ n := by
  rw [Nat.size_eq_bits_len]
  exact Nat.size_le.mpr Nat.lt_two_pow_self
end Indices
end WordList
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_GridFloor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Ellipsoid

def sqrtUpperFraction (p q D : ℕ) : ℚ :=
  ((Nat.sqrt (p*q*D^2)+1 : ℕ):ℚ)/((q*D:ℕ):ℚ)

end MetricKMedianRecovery.Ellipsoid

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_RealVector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Ellipsoid

section
open Matrix
open scoped Matrix
variable {V : Type*} [Fintype V] [DecidableEq V]

def rationalRootUpper (D : ℕ) (q : ℚ) : ℚ := sqrtUpperFraction q.num.natAbs q.den D

end

open Matrix
open scoped Matrix

end MetricKMedianRecovery.Ellipsoid

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

def next (n : ℕ) (s : ℕ×ℕ) : ℕ×ℕ :=
  let m := (s.1+s.2)/2
  if m*m≤n then (m,s.2) else (s.1,m)
def interval (n : ℕ) : ℕ → ℕ×ℕ
  | 0 => (0,n+1)
  | t+1 => next n (interval n t)
def Bracket (n : ℕ) (s : ℕ×ℕ) : Prop :=
  s.1 < s.2 ∧ s.1*s.1≤n ∧ n < s.2*s.2 ∧ s.2≤n+1
lemma initial_bracket (n : ℕ) : Bracket n (0,n+1) := by
  simp only [Bracket]
  constructor
  · omega
  constructor
  · omega
  constructor
  · nlinarith
  · exact le_rfl
lemma next_bracket {n : ℕ} {s : ℕ×ℕ} (h : Bracket n s) : Bracket n (next n s) := by
  obtain ⟨l,u⟩ := s
  let m := (l+u)/2
  have hl : l ≤ m := by dsimp [m]; dsimp [Bracket] at h; omega
  have hu : m<u := by dsimp [m]; dsimp [Bracket] at h; omega
  change Bracket n (if m*m≤n then (m,u) else (l,m))
  split_ifs with hm
  · exact ⟨hu,hm,h.2.2.1,h.2.2.2⟩
  · have hlm : l < m := by nlinarith [h.2.1]
    exact ⟨hlm,h.2.1,Nat.lt_of_not_ge hm,hu.le.trans h.2.2.2⟩
lemma interval_bracket (n t : ℕ) : Bracket n (interval n t) := by
  induction t with
  | zero => exact initial_bracket n
  | succ t ih => exact next_bracket ih
lemma next_width {n : ℕ} {s : ℕ×ℕ} (h : s.1 < s.2) :
    (next n s).2-(next n s).1-1≤(s.2-s.1-1)/2 := by
  obtain ⟨l,u⟩ := s
  dsimp only at h
  dsimp only [next]
  split_ifs <;> dsimp only <;> omega
lemma interval_width (n t : ℕ) : (interval n t).2-(interval n t).1-1≤n/2^t := by
  induction t with
  | zero => simp [interval]
  | succ t ih =>
    have hh := next_width (n:=n) (interval_bracket n t).1
    calc
      _ ≤ ((interval n t).2-(interval n t).1-1)/2 := hh
      _ ≤ (n/2^t)/2 := Nat.div_le_div_right ih
      _ = n/2^(t+1) := by rw [Nat.div_div_eq_div_mul,pow_succ]
lemma interval_correct (n t : ℕ) (ht : n.size≤t) : (interval n t).1=Nat.sqrt n := by
  have hb := interval_bracket n t
  have hw := interval_width n t
  have hn : n<2^t := Nat.size_le.mp ht
  rw [Nat.div_eq_of_lt hn] at hw
  have hl := Nat.le_sqrt.mpr hb.2.1
  have hu := Nat.sqrt_lt.mpr hb.2.2.1
  omega

end BinarySqrt
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

open BinaryArithmetic RationalLinearFeasibility Ellipsoid
namespace BinaryEllipsoidIteration

noncomputable def shapePoly : Polynomial ℕ := Polynomial.X+2*Polynomial.X+(4+3*Polynomial.X+2*(Polynomial.X+1))
noncomputable def vectorPoly : Polynomial ℕ := Polynomial.X*(shapePoly+Polynomial.X+1)
noncomputable def quadPoly : Polynomial ℕ := Polynomial.X*(Polynomial.X+vectorPoly+1)
noncomputable def incrementPoly : Polynomial ℕ := Polynomial.X+1+(2*quadPoly+2*(5+Polynomial.X)+1)+vectorPoly
noncomputable def centerPoly : Polynomial ℕ := Polynomial.X*(incrementPoly+1)
noncomputable def storagePoly : Polynomial ℕ :=
  10*(Polynomial.X+1)+2*Polynomial.X*(2*(Polynomial.X*(6*shapePoly+14))+2)+Polynomial.X*(6*centerPoly+14)
end BinaryEllipsoidIteration
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_BoundRow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Ellipsoid
open Matrix RationalLinearFeasibility
open scoped BigOperators

def integerRow {n : ℕ} (a : Fin n → ℤ) (b : ℤ) : Row n := ⟨fun j => a j,b⟩

end MetricKMedianRecovery.Ellipsoid

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BlueChoice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BlueDP
variable {A : Type*}
abbrev Candidate (A : Type*) := Option (ℚ×A)
def value : Candidate A→WithTop ℝ
  | none=>⊤
  | some (q,_)=>((q:ℝ):WithTop ℝ)
end MetricKMedianRecovery.BlueDP

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BlueDPValue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BlueDP
variable {L R Y : Type*} [LinearOrder L] [LinearOrder R] [LinearOrder Y]
abbrev Atom (L R Y : Type*) := L×R×Y

end MetricKMedianRecovery.BlueDP

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_PhasesBounded
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.LeafMetric
variable {V C : Type*} [PseudoMetricSpace V]

def parent (root : C → V) : V ⊕ C → V := Sum.elim id root

def height (u : C → ℝ) : V ⊕ C → ℝ := Sum.elim (fun _ => 0) u

noncomputable def leafDist (root : C → V) (u : C → ℝ) (x y : V ⊕ C) : ℝ := by
  classical
  exact if x = y then 0 else height u x+dist (parent root x) (parent root y)+height u y

omit [PseudoMetricSpace V] in
lemma height_nonneg (u : C → ℝ) (hu : ∀ c, 0 ≤ u c) (x : V ⊕ C) : 0 ≤ height u x := by
  cases x with
  | inl => exact le_rfl
  | inr c => exact hu c

lemma leafDist_self (root : C → V) (u : C → ℝ) (x : V ⊕ C) : leafDist root u x x = 0 := by
  simp [leafDist]
lemma leafDist_nonneg (root : C → V) (u : C → ℝ) (hu : ∀ c, 0 ≤ u c) (x y : V ⊕ C) :
    0 ≤ leafDist root u x y := by
  unfold leafDist
  split_ifs
  · exact le_rfl
  · exact add_nonneg (add_nonneg (height_nonneg u hu x) dist_nonneg) (height_nonneg u hu y)

end MetricKMedianRecovery.LeafMetric

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_RationalLeaves
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalLeaves
variable {V : Type*} [PseudoMetricSpace V]

abbrev Label (V : Type*) := V ⊕ (ℕ × V × ℚ)

def root (c : ℕ × V × ℚ) : V := c.2.1
def height (c : ℕ × V × ℚ) : ℝ := (max c.2.2 0:ℚ)

end MetricKMedianRecovery.RationalLeaves

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
open WordList BinaryArithmetic

def ranking {r : ℕ} (v : Fin r→ℚ) (i : Fin r) : ℚ ×ₗ ℕ := toLex (v i,i.val)
end MetricKMedianRecovery.BitMachine.BinaryRationalSort

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_BottomMath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Completion

variable {α : Type*} [LinearOrder α]
def bottomSet (U : Finset α) (k : ℕ) : Finset α := ((U.sort (·≤·)).take k).toFinset
end MetricKMedianRecovery.Completion

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CompletionFillMath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Completion.Canonical
variable {E V : Type*} [DecidableEq E] [DecidableEq V] {a : ℕ}
def pick (part : E→Fin a) (o : Fin a→E) (xs : List E) (j : Fin a) : E :=
  ((xs.filter (fun e=>part e=j)).head?).getD (o j)
def filled (part : E→Fin a) (o : Fin a→E) (loc : E→V) (xs : List E) : Finset V :=
  Finset.univ.image (loc ∘ pick part o xs)
end MetricKMedianRecovery.Completion.Canonical
namespace MetricKMedianRecovery.Completion.Canonical
variable {V : Type*} [LinearOrder V]
def pad (F U : Finset V) (n : ℕ) : Finset V := U∪bottomSet (F\U) (n-U.card)
end MetricKMedianRecovery.Completion.Canonical

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Score
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Completion

variable {E R : Type*} [Fintype R]

noncomputable def score (baseline : ℝ) (offer : E → ℝ) (X : Finset E) : ℝ :=
  X.fold max baseline offer

@[simp] lemma score_empty (baseline : ℝ) (offer : E → ℝ) :
    score baseline offer ∅ = baseline := rfl

noncomputable def topSum (q : ℕ) (v : R → ℝ) : ℝ :=
  (Finset.univ.powersetCard (min q (Fintype.card R))).sup'
    (Finset.powersetCard_nonempty.mpr (by simp)) (fun S => ∑ s ∈ S, v s)

noncomputable def bottomSum (q : ℕ) (v : R → ℝ) : ℝ := -topSum q (fun r => -v r)

noncomputable def cappedCost (baseline : ℝ) (distance : E → ℝ) (X : Finset E) : ℝ :=
  X.fold min baseline distance

@[simp] lemma cappedCost_empty (baseline : ℝ) (distance : E → ℝ) :
    cappedCost baseline distance ∅ = baseline := rfl

variable {P : Type*} [Fintype P]

noncomputable def surrogate (K : ℝ) (q : ℕ)
    (base : P → ℝ) (distance : P → E → ℝ)
    (weight redBase : R → ℝ) (redDistance : R → E → ℝ) (X : Finset E) : ℝ :=
  K + ∑ p, cappedCost (base p) (distance p) X +
    bottomSum q (fun r => weight r * cappedCost (redBase r) (redDistance r) X)

end MetricKMedianRecovery.Completion

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_FinSets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryFinSet
open WordList
variable {n : ℕ}
def values (S : Finset (Fin n)) : Finset ℕ := S.image Fin.val
end MetricKMedianRecovery.BitMachine.BinaryFinSet

namespace MetricKMedianRecovery.BitMachine.BinaryRationalSort
open WordList BinaryArithmetic
def bottomValues {r : ℕ} (v : Fin r→ℚ) (k : ℕ) : List ℚ :=
  (((Finset.univ.image (ranking v)).sort (·≤·)).take k).map (fun p=>(ofLex p).1)
end MetricKMedianRecovery.BitMachine.BinaryRationalSort

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BlueTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BlueDP
variable {L A : Type*} [LinearOrder L]
abbrev Table (L A : Type*) := List (Finset L × Candidate (List A))
def states (U : Finset L) : List (Finset L) := (U.sort (·≤·)).sublists.map List.toFinset
end MetricKMedianRecovery.BlueDP

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_State2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Sampling

structure State (V : Type*) where
  deleted : Finset V
  leaves : List (V × ℝ)

variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V]
abbrev Tag (V : Type*) := V ⊕ₗ ℕ

def realTag (v : V) : Tag V := toLex (Sum.inl v)
def leafTag (j : ℕ) : Tag V := toLex (Sum.inr j)

noncomputable def tags (S : Finset V) (s : State V) : Finset (Tag V) :=
  (S \ s.deleted).image realTag ∪ (Finset.range (s.leaves.length+1)).image leafTag

omit [PseudoMetricSpace V] in
lemma tags_nonempty (S : Finset V) (s : State V) : (tags S s).Nonempty := by
  refine ⟨leafTag 0,?_⟩
  exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨0,by simp, rfl⟩)

end MetricKMedianRecovery.Sampling

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_RationalSampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalSampling
open Sampling
variable {n : ℕ}
structure State (n : ℕ) where
  deleted : Finset (Fin n)
  leaves : List (Fin n×ℚ)
def State.real (s : State n) : Sampling.State (Fin n) :=
  ⟨s.deleted,s.leaves.map (fun z=>(z.1,(z.2:ℝ)))⟩
def tagId (t : Tag (Fin n)) : ℕ := match ofLex t with
  | .inl v=>v.val
  | .inr j=>n+j
def tagDistance (δ : Fin n→Fin n→ℚ) (Δ : ℚ) (s : State n) (w : Fin n) (t : Tag (Fin n)) : ℚ :=
  match ofLex t with
  | .inl v=>δ w v
  | .inr 0=>Δ
  | .inr (j+1)=>match s.leaves[j]? with
    | some z=>δ w z.1+z.2
    | none=>Δ
section Metric
variable [PseudoMetricSpace (Fin n)] (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
def key (Δ : ℚ) (s : State n) (w : Fin n) (t : Tag (Fin n)) : ℚ ×ₗ ℕ :=
  toLex (tagDistance δ Δ s w t,tagId t)
noncomputable def keys (S : Finset (Fin n)) (Δ : ℚ) (s : State n) (w : Fin n) : Finset (ℚ ×ₗ ℕ) :=
  (Sampling.tags S s.real).image (key δ Δ s w)
omit [PseudoMetricSpace (Fin n)] in
lemma keys_nonempty (S : Finset (Fin n)) (Δ : ℚ) (s : State n) (w : Fin n) :
    (keys δ S Δ s w).Nonempty := (Sampling.tags_nonempty S s.real).image _
end Metric
end MetricKMedianRecovery.RationalSampling

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_RationalMenus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalSampling
open Sampling BitMachine
variable {n : ℕ}
noncomputable def chosenKey (δ : Fin n→Fin n→ℚ) (S : Finset (Fin n)) (Δ : ℚ) (s : State n) (w : Fin n) : ℚ×ₗℕ :=
  (keys δ S Δ s w).min' (keys_nonempty δ S Δ s w)
noncomputable def reference (δ : Fin n→Fin n→ℚ) (S : Finset (Fin n)) (Δ : ℚ) (s : State n) (w : Fin n) : ℚ :=
  (ofLex (chosenKey δ S Δ s w)).1
noncomputable def chosenId (δ : Fin n→Fin n→ℚ) (S : Finset (Fin n)) (Δ : ℚ) (s : State n) (w : Fin n) : ℕ :=
  (ofLex (chosenKey δ S Δ s w)).2
end MetricKMedianRecovery.RationalSampling

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_RationalBottomIndices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRationalSort
open WordList BinaryArithmetic
noncomputable def indexSet {r : ℕ} (v : Fin r→ℚ) (k : ℕ) : Finset (Fin r) :=
  Finset.univ.filter (fun i=>ranking v i∈Completion.bottomSet (Finset.univ.image (ranking v)) k)
end MetricKMedianRecovery.BitMachine.BinaryRationalSort

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Average
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery
namespace FiniteSampling

open scoped BigOperators

noncomputable def average {Ω : Type*} [Fintype Ω] (X : Ω → ℝ) : ℝ :=
  𝔼 ω, X ω

noncomputable def probability {Ω : Type*} [Fintype Ω] (P : Ω → Prop) : ℝ := by
  classical
  exact average (fun ω => if P ω then 1 else 0)

noncomputable def sampleMean {Ω : Type*} (L : ℕ) (X : Ω → ℝ) (s : Fin L → Ω) : ℝ :=
  (∑ i, X (s i)) / L

section Average
variable {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]

lemma average_congr {X Y : Ω → ℝ} (h : ∀ ω, X ω = Y ω) : average X = average Y :=
  Finset.expect_congr rfl (fun ω _ => h ω)

@[simp] lemma average_const [Nonempty Ω] (c : ℝ) : average (fun _ : Ω => c) = c :=
  Fintype.expect_const c

lemma average_add (X Y : Ω → ℝ) :
    average (fun ω => X ω + Y ω) = average X + average Y :=
  Finset.expect_add_distrib _ _ _

lemma average_mul_const (X : Ω → ℝ) (c : ℝ) :
    average (fun ω => X ω * c) = average X * c :=
  (Finset.expect_mul _ _ _).symm

lemma average_sum {ι : Type*} (s : Finset ι) (X : ι → Ω → ℝ) :
    average (fun ω => ∑ i ∈ s, X i ω) = ∑ i ∈ s, average (X i) :=
  Finset.expect_sum_comm _ _ _

end Average

end FiniteSampling
end MetricKMedianRecovery

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_SetFunction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery
namespace Categorical

variable {E : Type*} [Fintype E] [DecidableEq E]

abbrev SetFunction (E : Type*) := Finset E → ℝ

noncomputable def marginal (g : SetFunction E) (e : E) (S : Finset E) : ℝ :=
  g (insert e S) - g S

noncomputable def operator (w : E → ℝ) (g : SetFunction E) (S : Finset E) : ℝ :=
  (1 - ∑ e, w e) * g S + ∑ e, w e * g (insert e S)

end Categorical
end MetricKMedianRecovery

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Table
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery
namespace Categorical

open FiniteSampling
variable {E Ω : Type*} [Fintype E] [DecidableEq E] [Fintype Ω] [Nonempty Ω]

abbrev Table (Ω E : Type*) := Ω → Option E

noncomputable def tableWeights (r : Table Ω E) (e : E) : ℝ :=
  probability (fun ω => r ω = some e)

omit [Nonempty Ω] in
lemma average_option (r : Table Ω E) (v : Option E → ℝ) :
    average (fun ω => v (r ω)) = probability (fun ω => r ω = none) * v none +
      ∑ e, tableWeights r e * v (some e) := by
  classical
  unfold tableWeights probability
  simp_rw [← average_mul_const]
  rw [← average_sum, ← average_add]
  apply average_congr
  intro ω
  by_cases hn : r ω = none
  · simp [hn]
  · have hex : ∃ e, r ω = some e := by
      cases h : r ω with
      | none => exact (hn h).elim
      | some e => exact ⟨e,rfl⟩
    obtain ⟨e,he⟩ := hex
    simp [he]

lemma tableWeights_total (r : Table Ω E) :
    probability (fun ω => r ω = none) + ∑ e, tableWeights r e = 1 := by
  have h := average_option r (fun _ => 1)
  simpa only [average_const, mul_one] using h.symm

lemma table_operator (r : Table Ω E) (g : SetFunction E) (S : Finset E) :
    operator (tableWeights r) g S = average (fun ω =>
      match r ω with | none => g S | some e => g (insert e S)) := by
  rw [average_option r (fun o => match o with | none => g S | some e => g (insert e S))]
  have ht := tableWeights_total r
  dsimp only
  unfold operator
  rw [show 1 - ∑ e, tableWeights r e = probability (fun ω => r ω = none) by linarith]

def put (o : Option E) (S : Finset E) : Finset E :=
  match o with | none => S | some e => insert e S

def draw : (a : ℕ) → (Fin a → Table Ω E) → (Fin a → Ω) → Finset E → Finset E
  | 0, _, _, S => S
  | a+1, r, seed, S => put (r 0 (seed 0)) (draw a (Fin.tail r) (Fin.tail seed) S)

end Categorical
end MetricKMedianRecovery

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Advance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Categorical

open FiniteSampling

def advance {E Ω : Type*} [DecidableEq Ω] {a : ℕ}
    (r : Fin a → Table Ω E) (ω : Ω) (c : Fin a → E) : Fin a → Table Ω E :=
  fun j => Function.update (r j) ω (some (c j))

end MetricKMedianRecovery.Categorical

namespace MetricKMedianRecovery.FiniteSampling

def adaptiveRun {S Ω : Type*} (f : S → Ω → S) :
    (n : ℕ) → S → (Fin n → Ω) → S
  | 0, s, _ => s
  | n+1, s, seed => adaptiveRun f n (f s (seed 0)) (Fin.tail seed)

end MetricKMedianRecovery.FiniteSampling

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_TableValue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Categorical
open FiniteSampling

section GreedyStep
variable {E : Type*} [Fintype E] [DecidableEq E] {a T L : ℕ}

abbrev GreedyState (E : Type*) (a T : ℕ) := ℕ × (Fin a → Table (Fin T) E)
abbrev OracleSeed (E : Type*) (a T L : ℕ) := E → Fin L → Fin a → Fin T

noncomputable def marginalSample (part : E → Fin a) (g : SetFunction E)
    (r : Fin a → Table (Fin T) E) (e : E) (seed : Fin a → Fin T) : ℝ :=
  marginal g e (draw a (Function.update r (part e) (fun _ => none)) seed ∅)

noncomputable def scores (part : E → Fin a) (g : SetFunction E)
    (r : Fin a → Table (Fin T) E) (seed : OracleSeed E a T L) (e : E) : ℝ :=
  sampleMean L (marginalSample part g r e) (seed e)

end GreedyStep
end MetricKMedianRecovery.Categorical

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_InitialState2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Categorical
open FiniteSampling

def initialState (E : Type*) (a T : ℕ) : GreedyState E a T :=
  (0, fun _ _ => none)

end MetricKMedianRecovery.Categorical

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_UniformBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Categorical
open FiniteSampling

def uniformBits : (b : ℕ) → (Fin b → Bool) ≃ Fin (2^b)
  | 0 => (Equiv.ofUnique (Fin 0 → Bool) (Fin 1)).trans (finCongr (by simp))
  | b+1 => (Fin.consEquiv (fun _ : Fin (b+1) => Bool)).symm |>.trans
      ((Equiv.prodCongr finTwoEquiv.symm (uniformBits b)).trans
        (finProdFinEquiv.trans (finCongr (by simp [Nat.pow_succ, Nat.mul_comm]))))

abbrev BinaryOracleIndex (E : Type*) (a b L : ℕ) :=
  ((Fin (2^b) × E × Fin L × Fin a) ⊕ Fin a) × Fin b

def binarySeedEquiv (E : Type*) (a b L : ℕ) :
    (BinaryOracleIndex E a b L → Bool) ≃
      (Fin (2^b) → OracleSeed E a (2^b) L) × (Fin a → Fin (2^b)) where
  toFun bits := (fun t e l j => uniformBits b (fun i => bits (.inl (t,e,l,j),i)),
    fun j => uniformBits b (fun i => bits (.inr j,i)))
  invFun s := fun idx => match idx.1 with
    | .inl (t,e,l,j) => (uniformBits b).symm (s.1 t e l j) idx.2
    | .inr j => (uniformBits b).symm (s.2 j) idx.2
  left_inv bits := by
    funext idx
    rcases idx with ⟨idx,i⟩
    rcases idx with ⟨t,e,l,j⟩ | j <;> simp
  right_inv s := by
    apply Prod.ext
    · funext t e l j
      exact (uniformBits b).apply_symm_apply _
    · funext j
      exact (uniformBits b).apply_symm_apply _

end MetricKMedianRecovery.Categorical

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BranchWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalSampling
variable {n : ℕ}
noncomputable def assignmentWeight (δ : Fin n→Fin n→ℚ) (D S : Finset (Fin n)) (Δ : ℚ) (s : State n) (u : Fin n) : ℚ :=
  (D.filter (fun p=>chosenId δ S Δ s p=u.val)).card
end MetricKMedianRecovery.RationalSampling

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BlueTableSize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBlueLoop
open WordList
variable {n m : ℕ} {R : Type*} [LinearOrder R]
noncomputable def capPoly : Polynomial ℕ := 1000*(Polynomial.X+1)^4
end MetricKMedianRecovery.BitMachine.BinaryBlueLoop

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CopyGround
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Completion.CopyGround
variable {n a : ℕ}
def part : Fin (a*n)→Fin a := Fin.divNat
noncomputable def location (H : Fin a→Finset (Fin n)) (hH : ∀ i,(H i).Nonempty) (e : Fin (a*n)) : Fin n :=
  if e.modNat ∈ H e.divNat then e.modNat else (H e.divNat).min' (hH e.divNat)
end MetricKMedianRecovery.Completion.CopyGround

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BranchContext
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBranchContext
open WordList
variable {n m : ℕ}
def balls (δ : Fin n→Fin n→ℚ) (F : Finset (Fin n)) (s : RationalSampling.State n) : Fin s.leaves.length→Finset (Fin n) :=
  fun i=>F.filter (fun f=>δ s.leaves[i.val].1 f ≤ s.leaves[i.val].2)
end MetricKMedianRecovery.BitMachine.BinaryBranchContext

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CategoricalRule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Categorical.Selected
open FiniteSampling
structure Rule {E : Type*} {a : ℕ} (part : E→Fin a) where
  choose : (E→ℝ)→Fin a→E
  spec : ∀ score j,part (choose score j)=j ∧ ∀ e,part e=j→score e ≤ score (choose score j)
variable {E : Type*} [Fintype E] [DecidableEq E] {a T L : ℕ}
noncomputable def greedyStep (part : E → Fin a) (rule : Rule part)
    (g : SetFunction E) (s : GreedyState E a T) (seed : OracleSeed E a T L) :
    GreedyState E a T :=
  if h : s.1 < T then
    (s.1+1, advance s.2 ⟨s.1,h⟩ (rule.choose (scores part g s.2 seed)))
  else s

noncomputable def greedyRun (part : E → Fin a) (rule : Rule part)
    (g : SetFunction E) (seed : Fin T → OracleSeed E a T L) : GreedyState E a T :=
  adaptiveRun (greedyStep part rule g) T (initialState E a T) seed

end MetricKMedianRecovery.Categorical.Selected

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CategoricalResources
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Categorical.Explicit
open FiniteSampling

def exponent (a : ℕ) : ℕ := 2*(a+1).size+10
def steps (a : ℕ) : ℕ := 2^exponent a
def samples (q a : ℕ) : ℕ := 1000000000*steps a*(q+1)*(a+1)^2
attribute [local irreducible] steps exponent

attribute [local irreducible] samples
end MetricKMedianRecovery.Categorical.Explicit

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CategoricalTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCategorical
open WordList BinaryArithmetic
variable {E : Type*} {a T : ℕ}
def drawn (r : Fin a→Fin T→Option E) (s : Fin a→Fin T) : List E :=
  (List.ofFn (fun j=>(r j (s j)).toList)).flatten
end MetricKMedianRecovery.BitMachine.BinaryCategorical

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_OrderedMaximum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.OrderedMaximum
variable {E β : Type*} [LinearOrder β]
def run (score : E→β) (s : E) : List E→E
  | []=>s
  | a::as=>run score (if score s < score a then a else s) as
def ofList (score : E→β) (as : List E) (h : as≠[]) : E := run score (as.head h) as.tail
end MetricKMedianRecovery.OrderedMaximum

namespace MetricKMedianRecovery.Categorical.Selected
variable {E : Type*} [DecidableEq E] {a : ℕ}
def bag (es : List E) (part : E→Fin a) (j : Fin a) : List E := es.filter (fun e=>part e=j)
omit [DecidableEq E] in
lemma bag_ne_nil (es : List E) (he : ∀ e,e∈es) (part : E→Fin a)
    (hp : Function.Surjective part) (j : Fin a) : bag es part j≠[] := by
  obtain ⟨e,hem⟩:=hp j
  intro hn
  have hm : e∈bag es part j:=List.mem_filter.mpr ⟨he e,by simpa using hem⟩
  rw [hn] at hm
  exact List.not_mem_nil hm
end MetricKMedianRecovery.Categorical.Selected

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CategoricalChoice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCategorical
open WordList BinaryArithmetic
variable {q a T L : ℕ}
def elements (q : ℕ) : List (Fin q) := List.ofFn id
lemma mem_elements (e : Fin q) : e∈elements q := by simp [elements]
end MetricKMedianRecovery.BitMachine.BinaryCategorical

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CompletionRealizeMath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Completion.Canonical
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V]
def realize {E R B : Type*} [Fintype B] {a : ℕ} (F S Q : Finset V)
    (part : E→Fin a) (o : Fin a→E) (loc : E→V)
    (redLoc : R→V) (blueLoc blueDest : B→V) (xs : List E) (T : Finset R) : Finset V :=
  pad F ((S \ (Q∪T.image redLoc∪Finset.univ.image blueLoc)) ∪
    (filled part o loc xs∪Finset.univ.image blueDest)) S.card

end MetricKMedianRecovery.Completion.Canonical

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_RationalCap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCompletion
open WordList BinaryArithmetic

def capped {E : Type*} (base : ℚ) (distance : E→ℚ) (S : Finset E) : ℚ := S.fold min base distance
end MetricKMedianRecovery.BitMachine.BinaryCompletion

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_MetricArrays
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.SortedIndex
variable {α : Type*} [LinearOrder α]
def enum (S : Finset α) : Fin S.card→α := S.orderEmbOfFin rfl
end MetricKMedianRecovery.SortedIndex

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_RationalSurrogate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCompletion
open WordList BinaryArithmetic
variable {q p r : ℕ}

def surrogateQ (k : ℕ) (base : Fin p→ℚ) (distance : Fin p→Fin q→ℚ)
    (weight redBase : Fin r→ℚ) (redDistance : Fin r→Fin q→ℚ) (S : Finset (Fin q)) : ℚ :=
  (∑ i,capped (base i) (distance i) S)+
    (BinaryRationalSort.bottomValues (fun i=>weight i*capped (redBase i) (redDistance i) S) k).sum

def savingQ (k : ℕ) (base : Fin p→ℚ) (distance : Fin p→Fin q→ℚ)
    (weight redBase : Fin r→ℚ) (redDistance : Fin r→Fin q→ℚ) (S : Finset (Fin q)) : ℚ :=
  surrogateQ k base distance weight redBase redDistance ∅-surrogateQ k base distance weight redBase redDistance S
end MetricKMedianRecovery.BitMachine.BinaryCompletion

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BranchPhysical
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBranchCheck
open WordList BinaryArithmetic BinaryBranchContext
variable {n m : ℕ}
def Ready (δ : Fin n→Fin n→ℚ) (F S : Finset (Fin n)) (s : RationalSampling.State n)
    (colors : Fin n→Fin 3) (q c m : ℕ) : Prop :=
  s.deleted⊆S ∧ (∀ i,(balls δ F s i).Nonempty) ∧ (∀ z∈s.leaves,0≤z.2) ∧
    q≤((S\s.deleted).filter (fun i=>colors i=1)).card ∧ s.leaves.length+c≤ s.deleted.card+q+m
end MetricKMedianRecovery.BitMachine.BinaryBranchCheck

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_RationalBranch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBranchProgram
open Completion Categorical FiniteSampling BinaryBranchContext
variable {n m : ℕ}
noncomputable def objective (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℚ) (s : RationalSampling.State n)
    (colors : Fin n→Fin 3) (hH : ∀ i,(balls δ F s i).Nonempty) (sel dest : Fin m→Fin n) (k : ℕ)
    (X : Finset (Fin (s.leaves.length*n))) : ℝ :=
  let red:=(S\s.deleted).filter (fun i=>colors i=1)
  let green:=(S\s.deleted).filter (fun i=>colors i=0)
  let loc:=CopyGround.location (balls δ F s) hH
  surrogate (∑ j,(RationalSampling.assignmentWeight δ D S Δ s (sel j)*δ (sel j) (dest j):ℚ)) k
    (fun i=>(RationalSampling.reference δ S Δ s (SortedIndex.enum D i):ℝ))
    (fun i e=>(δ (SortedIndex.enum D i) (loc e):ℝ))
    (fun i=>(RationalSampling.assignmentWeight δ D S Δ s (SortedIndex.enum red i):ℝ))
    (fun i=>(RationalSampling.reference δ green Δ ⟨∅,s.leaves⟩ (SortedIndex.enum red i):ℝ))
    (fun i e=>(δ (SortedIndex.enum red i) (loc e):ℝ)) X
end MetricKMedianRecovery.BitMachine.BinaryBranchProgram

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BranchObjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBranchProgram
open Completion Categorical FiniteSampling BinaryBranchContext Sampling
variable {n m : ℕ} [PseudoMetricSpace (Fin n)]
noncomputable def rationalScore (δ : Fin n→Fin n→ℚ) (D S : Finset (Fin n)) (Δ : ℚ)
    (s : RationalSampling.State n) (u v : Fin n) : ℚ :=
  RationalSampling.assignmentWeight δ D S Δ s u*δ u v
end MetricKMedianRecovery.BitMachine.BinaryBranchProgram

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_DeleteSize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryDelete
open WordList RationalLeaves

noncomputable def capacityPoly : Polynomial ℕ :=
  let X : Polynomial ℕ:=Polynomial.X
  2*(X*(2*X+2)+(X+X*X)*(2*X+2)+(2*X)*(2*((3*X+1+X*X)*(2*X+2))+2))+6

end MetricKMedianRecovery.BitMachine.BinaryDelete

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_DyadicGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.DyadicGrid
abbrev State := ℕ × ℕ × ℕ
def start : State := (0,1,1)
end MetricKMedianRecovery.DyadicGrid

end OAI
end


