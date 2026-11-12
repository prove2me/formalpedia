-- Prove2me | Definitions.Def_Q238L017
-- name    : Q238L017
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T11:23:36.213284+00:00
-- url     : https://prove2.me/theorems/7e204506-743f-4c12-aaee-c6a9c5cbfbfb
-- title:
--   Definitions bundle Q238L017 of the split of OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 164 declarations of OpenAI's Lean: 141 definitions and 23 theorems. The definitions and types are `OAI.MetricKMedianRecovery.BitMachine.BinaryActions.delete`, `OAI.MetricKMedianRecovery.BitMachine.BinaryAdvance.deletionInput`, `OAI.MetricKMedianRecovery.BitMachine.BinaryAdvance.firstVertex`, `OAI.MetricKMedianRecovery.BitMachine.BinaryAdvance.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBisection.context`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBisection.fuel`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBisection.input`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBisection.logWord`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBisection.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBisection.predWords`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBisection.width`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBisection.widthCeil`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueBlocks.itemCall`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueBlocks.labelsEnc`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueCell.atomEnc`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueCell.ctx`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueCell.ctxPack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueCell.whole`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueChoice.encode`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueChoice.run`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueChoice.score`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueChoice.select`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueChoice.step`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueCollect.invalid`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueCollect.payloadOp`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueCollect.scoreOp`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueCollect.scores`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueItem.atomEnc`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueItem.op`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueItem.price`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueItem.record`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueItem.records`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueItem.response`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueItem.run`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueItem.sourceL`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueItem.sourceR`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueItem.sourceRow`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueItem.targetL`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueItem.targetY`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueLookup.encode` and 101 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedianRecovery_Branching_BlueBlocksMachine`, `KMedianRecovery_Branching_BlueChoice`, `KMedianRecovery_Branching_BlueItem`, `KMedianRecovery_Branching_BlueLookup`, `KMedianRecovery_Branching_BlueMerge`, `KMedianRecovery_Branching_BlueNextTable`, `KMedianRecovery_Branching_BlueProgram`, `KMedianRecovery_Branching_BlueTable`, `KMedianRecovery_Branching_BlueTableSize`, `KMedianRecovery_Branching_CopyComputes`, `KMedianRecovery_Encoding_Encode2`, `KMedianRecovery_Encoding_FinSets`, `KMedianRecovery_Encoding_LabelLookup`, `KMedianRecovery_Encoding_LabelMember`, `KMedianRecovery_Encoding_LabelOrder`, `KMedianRecovery_Encoding_NatWords`, `KMedianRecovery_Encoding_RationalSort`, `KMedianRecovery_Encoding_StateBits`, `KMedianRecovery_Encoding_WordExtras`, `KMedianRecovery_Encoding_WordSubsets`, `KMedianRecovery_Machines_ActionMachine`, `KMedianRecovery_Machines_BisectionMachine`, `KMedianRecovery_Machines_CappedFold`, `KMedianRecovery_Machines_DeleteFold`, `KMedianRecovery_Machines_DeleteSize`, `KMedianRecovery_Machines_FiniteMachine`, `KMedianRecovery_Machines_GridMachine`, `KMedianRecovery_Recovery_DigitBit`, `KMedianRecovery_Recovery_FilterItem`, `KMedianRecovery_Recovery_FinishPhase`, `KMedianRecovery_Recovery_FiniteContext`, `KMedianRecovery_Recovery_LeftNum`, `KMedianRecovery_Recovery_Next`, `KMedianRecovery_Recovery_NumAbs`, `KMedianRecovery_Recovery_Pack2`, `KMedianRecovery_Recovery_ProcessOutputs`, `KMedianRecovery_Recovery_RawSlices`, `KMedianRecovery_Recovery_SortMath`, `KMedianRecovery_Sampling_SamplingReference`, `KMedianRecovery_Sampling_SamplingStateMachine`.
--
--   **Imports.** It imports the published bundle `Def_KMedianRecovery`; the bundles `Q238L006`, `Q238L007` and `Q238L008` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q238L023`, `Q238L024`, `Q238L025` and `Q238L026`; the statements `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueSize.tableRun_best_bound_s238r` and `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueSize.table_length_s238r`.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_KMedianRecovery
import Definitions.Def_Q238L006
import Definitions.Def_Q238L007
import Definitions.Def_Q238L008

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

def Good (x : List Bool) : Prop := x.head?=some true ∨ value (second x)=0

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
open WordOperations BinaryArithmetic
namespace BinaryRational

lemma negWords_encode (x : ℚ) : negWords (encode x)=encode (-x) := by
  simp only [negWords,numerator_encode,denominator_encode,Signed.encode_decode]
  simp only [encode,Rat.num_neg_eq_neg_num,Rat.den_neg_eq_den]

end BinaryRational
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
lemma inc_iter (j : ℕ) : inc^[j] (0:ℕ).bits=j.bits := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply',ih]; simp only [inc,value_bits]
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
open WordOperations BinaryArithmetic
namespace RationalArray
def encode (xs : List ℚ) : List Bool := WordList.encode (xs.map BinaryRational.encode)
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
open WordOperations BinaryArithmetic
open scoped Matrix
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_CappedFold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.WordList.CappedFold
open WordOperations
noncomputable def run (f : List Bool → List Bool) (x : List Bool) : List Bool :=
  Fold.accum (BoundedIteration.run (Fold.step f)
    (pairBits (Count.run (Fold.items (discardPrefix x)),
      pairBits (RepeatedAppend.copies 4 x,discardPrefix x))))
end MetricKMedianRecovery.BitMachine.WordList.CappedFold

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BlueChoice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBlueChoice
open WordOperations WordList BinaryArithmetic
variable {A : Type*}
def encode (enc : A→List Bool) : BlueDP.Candidate A→List Bool
  | none=>[]
  | some (q,a)=>WordList.encode [pairBits (BinaryRational.encode q,enc a)]
noncomputable def score (x : List Bool) : List Bool := extractPrefix (head x)
noncomputable def run (x : List Bool) : List Bool :=
  if extractPrefix x=[] then discardPrefix x else
  if discardPrefix x=[] then extractPrefix x else
  if BinaryRational.decode (score (extractPrefix x))≤BinaryRational.decode (score (discardPrefix x))
    then extractPrefix x else discardPrefix x

noncomputable def step (x : List Bool) : List Bool := run (pairBits (Fold.accum x,Find.item x))
noncomputable def select (x : List Bool) : List Bool := CappedFold.run step (pairBits (x,Fold.pack x [] []))

end MetricKMedianRecovery.BitMachine.BinaryBlueChoice

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BlueMerge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBlueMerge
open WordOperations WordList
variable {A : Type*}
def listEnc (enc : A→List Bool) (xs : List A) : List Bool := WordList.encode (xs.map enc)
noncomputable def payload (x : List Bool) : List Bool := discardPrefix (head x)
noncomputable def sum (x : List Bool) : List Bool := BinaryRational.encode
  (BinaryRational.decode (BinaryBlueChoice.score (extractPrefix x))+
    BinaryRational.decode (BinaryBlueChoice.score (discardPrefix x)))
noncomputable def output (x : List Bool) : List Bool := WordList.encode
  [pairBits (sum x,payload (extractPrefix x)++payload (discardPrefix x))]
noncomputable def run (x : List Bool) : List Bool :=
  if extractPrefix x=[] then [] else if discardPrefix x=[] then [] else output x
end MetricKMedianRecovery.BitMachine.BinaryBlueMerge

namespace MetricKMedianRecovery.BitMachine.BinaryBlueCollect
open WordOperations WordList
variable {A : Type*}
noncomputable def invalid (x : List Bool) : Bool := decide (discardPrefix x=[])
noncomputable def scoreOp (x : List Bool) : List Bool := BinaryBlueChoice.score (discardPrefix x)
noncomputable def scores (x : List Bool) : List Bool := mapWith scoreOp (pairBits ([],x))
attribute [local irreducible] mapWith
noncomputable def payloadOp (x : List Bool) : List Bool := BinaryBlueMerge.payload (discardPrefix x)
end MetricKMedianRecovery.BitMachine.BinaryBlueCollect

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
open WordOperations BinaryArithmetic WordList
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
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_SortMath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations
namespace WordList.Sort

def reverseTest (p : List Bool → Bool) (x : List Bool) : Bool :=
  p (pairBits (discardPrefix x,extractPrefix x))
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

def encode {m : ℕ} (x : Label (Fin m)) : List Bool :=
  pairBits ((level x).bits,pairBits ((parent x).val.bits,BinaryRational.encode (rationalHeight x)))
def levelWords : List Bool → List Bool := extractPrefix
def parentWords : List Bool → List Bool := extractPrefix ∘ discardPrefix
def heightWords : List Bool → List Bool := discardPrefix ∘ discardPrefix

@[simp] lemma levelWords_encode {m : ℕ} (x : Label (Fin m)) : levelWords (encode x)=(level x).bits := by
  simp only [levelWords,encode,extractPrefix_pairBits]
@[simp] lemma parentWords_encode {m : ℕ} (x : Label (Fin m)) : parentWords (encode x)=(parent x).val.bits := by
  simp only [parentWords,encode,Function.comp_apply,extractPrefix_pairBits,discardPrefix_pairBits]
@[simp] lemma heightWords_encode {m : ℕ} (x : Label (Fin m)) : heightWords (encode x)=BinaryRational.encode (rationalHeight x) := by
  simp only [heightWords,encode,Function.comp_apply,discardPrefix_pairBits]

def lt (x : List Bool) : Bool :=
  decide (value (levelWords (extractPrefix x))<value (levelWords (discardPrefix x))) ||
    (decide (value (levelWords (extractPrefix x))=value (levelWords (discardPrefix x))) &&
      (decide (value (parentWords (extractPrefix x))<value (parentWords (discardPrefix x))) ||
        (decide (value (parentWords (extractPrefix x))=value (parentWords (discardPrefix x))) &&
          decide (BinaryRational.decode (heightWords (extractPrefix x))<BinaryRational.decode (heightWords (discardPrefix x))))))

def table : List Bool → List Bool := extractPrefix ∘ extractPrefix
def label : List Bool → List Bool := discardPrefix ∘ extractPrefix
def col : List Bool → List Bool := discardPrefix
end MetricKMedianRecovery.BitMachine.BinaryLabel

namespace MetricKMedianRecovery.BitMachine.BinaryLabelMatrix
open WordOperations WordList RationalLeaves
attribute [local irreducible] mapWith

def table : List Bool → List Bool := extractPrefix ∘ extractPrefix ∘ extractPrefix
def item : List Bool → List Bool := discardPrefix ∘ extractPrefix
def col : List Bool → List Bool := discardPrefix
end MetricKMedianRecovery.BitMachine.BinaryLabelMatrix

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_LabelMember
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryLabel
open WordOperations BinaryArithmetic WordList RationalLeaves

def eq (x : List Bool) : Bool :=
  decide (value (levelWords (extractPrefix x))=value (levelWords (discardPrefix x))) &&
    (decide (value (parentWords (extractPrefix x))=value (parentWords (discardPrefix x))) &&
      decide (BinaryRational.decode (heightWords (extractPrefix x))=BinaryRational.decode (heightWords (discardPrefix x))))

end MetricKMedianRecovery.BitMachine.BinaryLabel

namespace MetricKMedianRecovery.BitMachine.BinaryLabelSelect
open Classical
open WordOperations BinaryArithmetic WordList RationalLeaves

def alphabet : List Bool → List Bool := extractPrefix ∘ extractPrefix
def target : List Bool → List Bool := discardPrefix ∘ extractPrefix
def index : List Bool → List Bool := discardPrefix
end MetricKMedianRecovery.BitMachine.BinaryLabelSelect

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_LabelLookup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryLabelLookup
open WordOperations WordList RationalLeaves
noncomputable def item (x : List Bool) : List Bool := Lookup.run (pairBits (discardPrefix x,extractPrefix x))
noncomputable def run : List Bool → List Bool := mapWith item
end MetricKMedianRecovery.BitMachine.BinaryLabelLookup

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
attribute [local irreducible] WordList.Indices.run WordList.Lookup.run
  WordList.Fold.run
noncomputable def cf (k : ℕ) : List Bool → List Bool := field k ∘ extractPrefix
noncomputable def contextAt (x : List Bool) : List Bool := encode
  [cf 0 x,cf 1 x,cf 2 x,discardPrefix x,cf 4 x,cf 5 x,cf 6 x,cf 7 x,cf 8 x]
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

def labels {m : ℕ} (xs : List (Label (Fin m))) : List Bool := encode (xs.map BinaryLabel.encode)
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
noncomputable def replaceOpen (x : List Bool) : List Bool :=
  encode [field 0 (extractPrefix x),field 1 (extractPrefix x),field 2 (extractPrefix x),discardPrefix x,
    field 4 (extractPrefix x),field 5 (extractPrefix x),field 6 (extractPrefix x),field 7 (extractPrefix x)]
end MetricKMedianRecovery.BitMachine.BinaryFiniteContext

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_WordExtras
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace WordEq
lemma value_length_injective {xs ys : List Bool} (hl : xs.length=ys.length) (hv : value xs=value ys) : xs=ys := by
  induction xs generalizing ys with
  | nil=>exact (List.eq_nil_of_length_eq_zero hl.symm).symm
  | cons b xs ih=>
    cases ys with
    | nil=>simp only [List.length_cons,List.length_nil] at hl; omega
    | cons c ys=>
      have ht : xs.length=ys.length := by simpa only [List.length_cons,Nat.add_left_inj] using hl
      have hbc : b=c := by
        cases b <;> cases c <;> simp only [value,Bool.toNat_false,Bool.toNat_true] at hv ⊢ <;> omega
      subst c
      congr 1
      apply ih ht
      simp only [value] at hv
      omega
noncomputable def eq (x : List Bool) : Bool := decide (extractPrefix x=discardPrefix x)
end WordEq
end MetricKMedianRecovery.BitMachine

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

def lt (x : List Bool) : Bool :=
  decide (BinaryRational.decode (extractPrefix (extractPrefix x))<BinaryRational.decode (extractPrefix (discardPrefix x))) ||
  (decide (BinaryRational.decode (extractPrefix (extractPrefix x))=BinaryRational.decode (extractPrefix (discardPrefix x))) &&
    decide (value (discardPrefix (extractPrefix x))<value (discardPrefix (discardPrefix x))))
end MetricKMedianRecovery.BitMachine.BinaryRationalSort

namespace MetricKMedianRecovery.BitMachine.BinaryNatSet
open WordOperations WordList BinaryArithmetic
abbrev pack (xs : List ℕ) := WordList.encode (xs.map Nat.bits)
abbrev encode (S : Finset ℕ) := pack (S.sort (·≤·))
def lt (x : List Bool) : Bool := decide (value (extractPrefix x)<value (discardPrefix x))
end MetricKMedianRecovery.BitMachine.BinaryNatSet

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
def step (x : List Bool) : List Bool :=
  if value (extractPrefix x)=0 then x
  else pairBits ((value (extractPrefix x)-1).bits,List.tail (discardPrefix x))
lemma decrement_length (x : List Bool) : (value x-1).bits.length ≤ x.length := by
  rw [Nat.size_eq_bits_len]
  apply Nat.size_le_size (Nat.sub_le _ _) |>.trans
  simpa only [normalize_eq_bits,Nat.size_eq_bits_len] using BinaryDivision.normalize_length x
lemma first_step (x : List Bool) : (extractPrefix (step x)).length ≤ (extractPrefix x).length := by
  unfold step; split_ifs
  · exact le_rfl
  · rw [extractPrefix_pairBits]; exact decrement_length _
lemma rest_step (x : List Bool) : (discardPrefix (step x)).length ≤ (discardPrefix x).length := by
  unfold step; split_ifs
  · exact le_rfl
  · rw [discardPrefix_pairBits]; exact by simp only [List.length_tail]; omega
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

def run (x : List Bool) : List Bool := discardPrefix (step^[x.length] x)
end MetricKMedianRecovery.BitMachine.RawDrop

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
open WordOperations WordList
variable {n : ℕ}
def encode (S : Finset (Fin n)) : List Bool := BinaryNatSet.encode (values S)
end MetricKMedianRecovery.BitMachine.BinaryFinSet

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_SamplingReference
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySamplingReference
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field )
attribute [local irreducible] WordList.mapWith
variable {n l : ℕ}
noncomputable def original (x : List Bool) : List Bool :=
  pairBits (Lookup.run (pairBits (discardPrefix x,extractPrefix x)),discardPrefix x)
noncomputable def originals (x : List Bool) : List Bool := mapWith original (pairBits (field 4 x,field 2 x))
noncomputable def leaf (x : List Bool) : List Bool :=
  pairBits (BinaryRational.encode
    (BinaryRational.decode (Lookup.run (pairBits (extractPrefix (discardPrefix (discardPrefix x)),discardPrefix (extractPrefix x))))+
      BinaryRational.decode (discardPrefix (discardPrefix (discardPrefix x)))),
    (value (extractPrefix (extractPrefix x))+value (extractPrefix (discardPrefix x))+1).bits)
end MetricKMedianRecovery.BitMachine.BinarySamplingReference

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_SamplingStateMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySamplingState
open WordOperations WordList BinaryArithmetic RationalSampling
open BinaryOpeningPayment (field )
variable {n : ℕ}
noncomputable def referenceInput (x : List Bool) : List Bool := extractPrefix x++WordList.encode [discardPrefix x]
end MetricKMedianRecovery.BitMachine.BinarySamplingState

namespace MetricKMedianRecovery.BitMachine.BinarySamplingOracle
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field )
variable {n : ℕ}
noncomputable def row (x : List Bool) : List Bool := Lookup.run (pairBits (discardPrefix x,field 0 (extractPrefix x)))
end MetricKMedianRecovery.BitMachine.BinarySamplingOracle

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BlueItem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBlueItem
open WordOperations WordList
variable {L R : Type*} [LinearOrder R] [LinearOrder L] {n : ℕ}
def atomEnc (el : L→List Bool) (er : R→List Bool) (a : BlueDP.Atom L R (Fin n)) : List Bool :=
  pairBits (el a.1,pairBits (er a.2.1,a.2.2.val.bits))
def record (el : L→List Bool) (er : R→List Bool) (label : R→L) (q : R→Fin n→ℚ) (r : R) : List Bool :=
  pairBits (er r,pairBits (el (label r),RationalArray.encode (List.ofFn (q r))))
def records (el : L→List Bool) (er : R→List Bool) (B : Finset R) (label : R→L) (q : R→Fin n→ℚ) : List Bool :=
  WordList.encode ((B.sort (·≤·)).map (record el er label q))
def targetL (x : List Bool) : List Bool := extractPrefix (extractPrefix x)
def targetY (x : List Bool) : List Bool := discardPrefix (extractPrefix x)
def sourceR (x : List Bool) : List Bool := extractPrefix (discardPrefix x)
def sourceL (x : List Bool) : List Bool := extractPrefix (discardPrefix (discardPrefix x))
def sourceRow (x : List Bool) : List Bool := discardPrefix (discardPrefix (discardPrefix x))
noncomputable def price (x : List Bool) : List Bool := Lookup.run (pairBits (targetY x,sourceRow x))
noncomputable def response (x : List Bool) : List Bool := WordList.encode [pairBits (price x,
  WordList.encode [pairBits (targetL x,pairBits (sourceR x,targetY x))])]
noncomputable def op (x : List Bool) : List Bool := if WordEq.eq (pairBits (sourceL x,targetL x)) then response x else []
noncomputable def run (x : List Bool) : List Bool := BinaryBlueChoice.select (mapWith op x)
end MetricKMedianRecovery.BitMachine.BinaryBlueItem

namespace MetricKMedianRecovery.BitMachine.BinaryBlueRecords
open WordOperations WordList
open BinaryOpeningPayment (field )
variable {n m : ℕ}
noncomputable def oracleInput (x : List Bool) : List Bool := pairBits (field 0 (extractPrefix x),discardPrefix x)
end MetricKMedianRecovery.BitMachine.BinaryBlueRecords

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BlueBlocksMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBlueBlocks
open WordOperations WordList
variable {L R : Type*} [LinearOrder L] [LinearOrder R] {n : ℕ}
def labelsEnc (el : L→List Bool) (U : Finset L) : List Bool := WordList.encode ((U.sort (·≤·)).map el)
noncomputable def itemCall (x : List Bool) : List Bool := BinaryBlueItem.run
  (pairBits (pairBits (discardPrefix x,discardPrefix (extractPrefix x)),extractPrefix (extractPrefix x)))
end MetricKMedianRecovery.BitMachine.BinaryBlueBlocks

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_WordSubsets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.WordList.Subsets
open WordOperations
variable {A : Type*}
noncomputable def addLast (x : List Bool) : List Bool := discardPrefix x++encode [extractPrefix x]
noncomputable def added (x : List Bool) : List Bool := mapWith addLast (pairBits (Find.item x,Fold.accum x))
noncomputable def op (x : List Bool) : List Bool := Fold.accum x++added x
end MetricKMedianRecovery.BitMachine.WordList.Subsets

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BlueTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBlueStates
open WordOperations WordList
variable {n : ℕ}
noncomputable def nonemptyKey (x : List Bool) : Bool := !decide (discardPrefix x=[])
end MetricKMedianRecovery.BitMachine.BinaryBlueStates

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BlueLookup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBlueLookup
open WordOperations WordList
variable {L A : Type*} [LinearOrder L]
def encode (key : Finset L→List Bool) (enc : A→List Bool) (T : BlueDP.Table L A) : List Bool :=
  WordList.encode (T.map (fun z=>pairBits (key z.1,BinaryBlueChoice.encode (BinaryBlueMerge.listEnc enc) z.2)))
noncomputable def matchKey (x : List Bool) : Bool := WordEq.eq (pairBits (extractPrefix x,extractPrefix (discardPrefix x)))
end MetricKMedianRecovery.BitMachine.BinaryBlueLookup

namespace MetricKMedianRecovery.BitMachine.BinaryBlueCell
open WordOperations WordList
open BinaryOpeningPayment (field )
variable {n m : ℕ} {R : Type*} [LinearOrder R]
abbrev atomEnc (er : R→List Bool) := BinaryBlueItem.atomEnc (fun i : Fin m=>i.val.bits) er (n:=n)
def ctxPack (er : R→List Bool) (B : Finset R) (F : Finset (Fin n)) (label : R→Fin m) (q : R→Fin n→ℚ)
    (U : Finset (Fin m)) (T : BlueDP.Table (Fin m) (BlueDP.Atom (Fin m) R (Fin n))) : List Bool :=
  encode [BinaryBlueItem.records (fun i=>i.val.bits) er B label q,BinaryFinSet.encode F,
    encode ((BlueDP.states U).map BinaryFinSet.encode),BinaryBlueLookup.encode BinaryFinSet.encode (atomEnc er) T]
noncomputable def ctx (x : List Bool) : List Bool := extractPrefix (extractPrefix x)
noncomputable def whole (x : List Bool) : List Bool := discardPrefix (extractPrefix x)
end MetricKMedianRecovery.BitMachine.BinaryBlueCell

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BlueNextTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBlueTable
open WordOperations WordList
open BinaryOpeningPayment (field )
variable {n m : ℕ} {R : Type*} [LinearOrder R]
noncomputable def initRow (x : List Bool) : List Bool := pairBits (discardPrefix x,
  if discardPrefix x=[] then BinaryBlueChoice.encode id (some (0,[])) else [])
noncomputable def initial (x : List Bool) : List Bool := mapWith initRow (pairBits ([],x))
end MetricKMedianRecovery.BitMachine.BinaryBlueTable

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
open WordOperations WordList
open BinaryOpeningPayment (field )
variable {n m : ℕ} {R : Type*} [LinearOrder R]
noncomputable def oldTable (x : List Bool) : List Bool := extractPrefix (discardPrefix x)
noncomputable def oldBest (x : List Bool) : List Bool := discardPrefix (discardPrefix x)
noncomputable def initial (x : List Bool) : List Bool := pairBits (x,pairBits (BinaryBlueTable.initial (field 2 x),[]))
end MetricKMedianRecovery.BitMachine.BinaryBlueLoop

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BlueProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBlueOutput
open WordOperations WordList
open BinaryOpeningPayment (field )
variable {m n r : ℕ}
abbrev atomEnc := BinaryBlueCell.atomEnc (fun i : Fin r=>i.val.bits) (m:=m) (n:=n)
end MetricKMedianRecovery.BitMachine.BinaryBlueOutput

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
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field )
open RationalSampling
variable {n : ℕ}
noncomputable def delete (x : List Bool) : List Bool := encode [(1:ℕ).bits,discardPrefix x,[]]
end MetricKMedianRecovery.BitMachine.BinaryActions

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_GridMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryGrid
open WordOperations WordList BinaryArithmetic DyadicGrid
open BinaryOpeningPayment (field )
def cf (n : ℕ) : List Bool → List Bool := field n ∘ extractPrefix
def gf (n : ℕ) : List Bool → List Bool := field n ∘ discardPrefix
def num : List Bool → List Bool := extractPrefix ∘ discardPrefix
def den : List Bool → List Bool := discardPrefix ∘ discardPrefix
noncomputable def pointWords (x : List Bool) : List Bool := BinaryRational.encode
  (BinaryRational.decode (cf 2 x)+(BinaryRational.decode (cf 3 x)-BinaryRational.decode (cf 2 x))*
    (value (num x):ℚ)/(value (den x):ℚ))
noncomputable def doubled (n : ℕ) (x : List Bool) : List Bool := (2*value (gf n x)).bits
noncomputable def summed (x : List Bool) : List Bool := (value (gf 0 x)+value (gf 1 x)).bits
noncomputable def midpoint (x : List Bool) : List Bool := pointWords (pairBits (extractPrefix x,pairBits (summed x,doubled 2 x)))
noncomputable def queryInput (x : List Bool) : List Bool := pairBits (cf 0 x,midpoint x)
noncomputable def chooseLeft (query : List Bool→List Bool) (x : List Bool) : Bool :=
  decide (value (cf 1 x)≤value (query (queryInput x)))
noncomputable def upLeft (x : List Bool) : List Bool := encode [summed x,doubled 1 x,doubled 2 x]
noncomputable def upRight (x : List Bool) : List Bool := encode [doubled 0 x,summed x,doubled 2 x]
noncomputable def step (query : List Bool→List Bool) (x : List Bool) : List Bool :=
  pairBits (extractPrefix x,if chooseLeft query x then upLeft x else upRight x)
def stateBits (ctx : List Bool) (g : State) : List Bool := pairBits (ctx,encode [g.1.bits,g.2.1.bits,g.2.2.bits])
noncomputable def initial (x : List Bool) : List Bool := stateBits (discardPrefix x) start
noncomputable def endpoint (n : ℕ) (x : List Bool) : List Bool := pointWords (pairBits (extractPrefix x,pairBits (gf n x,gf 2 x)))
noncomputable def finish (x : List Bool) : List Bool := pairBits (endpoint 0 x,endpoint 1 x)
end MetricKMedianRecovery.BitMachine.BinaryGrid

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_BisectionMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBisection
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field )
noncomputable def predWords (x : List Bool) : List Bool := (value x-1).bits
noncomputable def logWord (x : List Bool) : List Bool := RepeatedAppend.copies (predWords x).length [true]
noncomputable def width (x : List Bool) : ℚ := BinaryRational.decode (field 4 x)-BinaryRational.decode (field 3 x)
noncomputable def widthCeil (x : List Bool) : List Bool := (Nat.ceil (width x)).bits
noncomputable def fuel (x : List Bool) : List Bool := field 0 x++logWord (widthCeil x)
noncomputable def context (x : List Bool) : List Bool := encode [field 1 x,field 2 x,field 3 x,field 4 x]
noncomputable def input (x : List Bool) : List Bool := pairBits (fuel x,context x)
def pack (N : ℕ) (ctx : List Bool) (k : ℕ) (a b : ℚ) : List Bool :=
  encode [List.replicate N true,ctx,k.bits,BinaryRational.encode a,BinaryRational.encode b]
end MetricKMedianRecovery.BitMachine.BinaryBisection

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

def cf (n : ℕ) (x : List Bool) : List Bool := field n (extractPrefix x)
def sf (n : ℕ) (x : List Bool) : List Bool := field n (discardPrefix (discardPrefix x))
noncomputable def rest (x : List Bool) : List Bool := WordList.tail (sf 0 x)
noncomputable def retained (x : List Bool) : List Bool := cf 1 x++rest x++WordList.cons (cf 2 x) (sf 1 x)
end MetricKMedianRecovery.BitMachine.BinaryDelete

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_DeleteSize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryAdvance
open WordOperations WordList RationalLeaves
open BinaryFiniteContext (labels )
open BinaryOpeningPayment (field )

def pack {m : ℕ} (base : List Bool) (C U : List (Label (Fin m))) (i ci : Label (Fin m)) : List Bool :=
  encode [base,labels C,labels U,BinaryLabel.encode i,BinaryLabel.encode ci]
noncomputable def deletionInput (x : List Bool) : List Bool :=
  Fold.pack (field 2 x) (encode [field 0 x,field 1 x,field 4 x]) (encode [field 2 x,[],[]])
noncomputable def firstVertex (x : List Bool) : List Bool := field 1 x++field 2 x++WordList.cons (field 4 x) []
end MetricKMedianRecovery.BitMachine.BinaryAdvance

end OAI
end


