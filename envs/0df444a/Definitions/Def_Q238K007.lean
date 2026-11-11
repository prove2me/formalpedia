-- Prove2me | Definitions.Def_Q238K007
-- name    : Q238K007
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T23:12:52.252097+00:00
-- url     : https://prove2.me/theorems/ce9622db-6f20-40de-925f-4bf52b763a8c
-- title:
--   Definitions bundle Q238K007 of the split of OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 115 declarations of OpenAI's Lean: 85 definitions and 30 theorems. The definitions and types are `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.bound`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.boundOp`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.boundedWords`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.boxShape`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.boxWords`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.relaxedOp`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.rows`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidAdvance.center`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidAdvance.cutInput`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidAdvance.dim`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidAdvance.direction`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidAdvance.found`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidAdvance.precision`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidAdvance.rest`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidAdvance.rest₂`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidAdvance.rows`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidAdvance.shape`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidAdvance.stored`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidCut.center`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidCut.centerInput`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidCut.coefCenter`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidCut.dim`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidCut.dimension`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidCut.direction`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidCut.haInput`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidCut.haWords`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidCut.quadWords`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidCut.qvalue`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidCut.rest`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidCut.rest₂`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidCut.rest₃`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidCut.rootPrecision`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidCut.scaledHa`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidCut.scaledHaInput`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidCut.shape`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidInitial.col`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidInitial.ctx`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidInitial.entryWords`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidInitial.row`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidInitial.rowInput` and 45 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedianRecovery_Encoding_Encode2`, `KMedianRecovery_Encoding_Encode3`, `KMedianRecovery_Encoding_OptionEncode`, `KMedianRecovery_Encoding_PushWord`, `KMedianRecovery_Machines_Program2`, `KMedianRecovery_Recovery_BoundOp`, `KMedianRecovery_Recovery_Computes`, `KMedianRecovery_Recovery_Copies`, `KMedianRecovery_Recovery_LeftNum`, `KMedianRecovery_Recovery_MulComputes`, `KMedianRecovery_Recovery_NumAbs`, `KMedianRecovery_Recovery_Op`, `KMedianRecovery_Recovery_Pack3`, `KMedianRecovery_Recovery_Pack5`, `KMedianRecovery_Recovery_Pack7`, `KMedianRecovery_Recovery_Pack9`, `KMedianRecovery_Recovery_ProcessOutputs`, `KMedianRecovery_Recovery_StepThen`.
--
--   **Imports.** It imports the published bundle `Def_KMedianRefinedRecovery`; the bundles `Q238K000`, `Q238K001` and `Q238K002` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q238K017`, `Q238K018`, `Q238K019`, `Q238K020` and `Q238K021`; the proofs of `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidInitial.indices_replicate_s238` and `OAI.MetricKMedianRecovery.BitMachine.WordList.flatMapWith_typed_s238`.
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
@[simp] theorem fin5_lit_2_0 : ((2 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_2_1 : ((2 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_3_0 : ((3 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_3_1 : ((3 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_3_2 : ((3 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_4_0 : ((4 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_4_1 : ((4 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_4_2 : ((4 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_4_3 : ((4 : Fin 5) = 3) ↔ False := by decide
end OAICompat434

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

@[simp] lemma twoStacks_false (xs ys : List Bool) : twoStacks xs ys false = xs := rfl
@[simp] lemma twoStacks_true (xs ys : List Bool) : twoStacks xs ys true = ys := rfl

lemma twoStacks_update_false (xs ys zs : List Bool) :
    Function.update (twoStacks xs ys) false zs = twoStacks zs ys := by
  funext b
  cases b <;> rfl

lemma twoStacks_update_true (xs ys zs : List Bool) :
    Function.update (twoStacks xs ys) true zs = twoStacks xs zs := by
  funext b
  cases b <;> rfl

lemma twoStacks_pure_false (xs : List Bool) :
    Function.update (fun _ : Bool => []) false xs = twoStacks xs [] := by
  funext b
  cases b <;> rfl

lemma twoStacks_pure_true (xs : List Bool) :
    Function.update (fun _ : Bool => []) true xs = twoStacks [] xs := by
  funext b
  cases b <;> rfl

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
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_PushWord
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open Turing Turing.TM2 StateTransition

lemma pushWord_step {K L S : Type} [DecidableEq K] (k : K) (bs : List Bool)
    (c : TM2.Stmt (fun _ : K=>Bool) L S) (v : S) (s : Stacks K) :
    TM2.stepAux (pushWord k bs c) v s=TM2.stepAux c v (Function.update s k (bs++s k)) := by
  induction bs generalizing c with
  | nil => simp only [pushWord,List.nil_append,Function.update_eq_self]
  | cons b bs ih =>
    rw [pushWord,ih]
    simp only [TM2.stepAux,Function.update_self,Function.update_idem,List.cons_append]

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

open Turing Turing.TM2 StateTransition
namespace WordSelection

def choose (xs : List Bool) : List Bool :=
  if xs.head?=some true then extractPrefix xs.tail else discardPrefix xs.tail

end WordSelection

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

def pack (s : Bool) (x : List Bool) : List Bool :=
  if value x=0 then [false] else s::normalize x

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
namespace BinaryRational

def divisor (x : List Bool) : List Bool :=
  (Nat.gcd (Signed.mag (numerator x)) (value (denominator x))).bits

def reduceNonzero (x : List Bool) : List Bool :=
  pairBits (Signed.pack (Signed.sign (numerator x))
    (Signed.mag (numerator x)/value (divisor x)).bits,
    (value (denominator x)/value (divisor x)).bits)

def reduce (x : List Bool) : List Bool :=
  if value (denominator x)=0 then encode 0 else reduceNonzero x

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
open BinaryArithmetic
namespace BinaryRational

def leftNum (x : List Bool) : List Bool := numerator (extractPrefix x)
def rightNum (x : List Bool) : List Bool := numerator (discardPrefix x)
def leftDen (x : List Bool) : List Bool := denominator (extractPrefix x)
def rightDen (x : List Bool) : List Bool := denominator (discardPrefix x)

def rawMul (x : List Bool) : List Bool :=
  pairBits (Signed.encode (Signed.decode (leftNum x)*Signed.decode (rightNum x)),
    (value (leftDen x)*value (rightDen x)).bits)
def rawAdd (x : List Bool) : List Bool :=
  pairBits (Signed.encode (Signed.decode (leftNum x)*(value (rightDen x):ℤ)+
    Signed.decode (rightNum x)*(value (leftDen x):ℤ)),
    (value (leftDen x)*value (rightDen x)).bits)

def addWords : List Bool → List Bool := reduce ∘ rawAdd
def mulWords : List Bool → List Bool := reduce ∘ rawMul

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
open BinaryArithmetic
namespace UnaryTake

lemma length_pack (a : Bool) (c d o : List Bool) :
    (pack a c d o).length=2*c.length+2*d.length+o.length+3 := by
  simp only [pack,List.length_cons,pairBits_length]; omega

end UnaryTake
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
namespace RepeatedAppend

lemma length_copies (n : ℕ) (d : List Bool) : (copies n d).length=n*d.length := by
  induction n with
  | zero => simp only [copies,List.length_nil,Nat.zero_mul]
  | succ n ih => simp only [copies,List.length_append,ih,Nat.add_mul,Nat.one_mul]

def step (x : List Bool) : List Bool :=
  if counter x=[] then pack false [] (data x) (output x)
  else pack true (counter x).tail (data x) (data x++output x)

def next := While.next step
lemma data_next (x : List Bool) : data (next x)=data x := by
  unfold next While.next; split_ifs
  · unfold step; split_ifs <;> simp only [data_pack]
  · rfl
lemma counter_next (x : List Bool) : (counter (next x)).length ≤ (counter x).length := by
  unfold next While.next; split_ifs
  · unfold step; split_ifs <;> simp only [counter_pack,List.length_nil,List.length_tail] <;> omega
  · exact le_rfl
lemma output_next (x : List Bool) : (output (next x)).length ≤ (output x).length+(data x).length := by
  unfold next While.next; split_ifs
  · unfold step; split_ifs <;> simp only [output_pack,List.length_append] <;> omega
  · omega
lemma length_next (x : List Bool) :
    (next x).length ≤ max x.length
      (2*(counter (next x)).length+2*(data (next x)).length+(output (next x)).length+3) := by
  unfold next While.next; split_ifs
  · unfold step; split_ifs <;> simp only [length_pack,counter_pack,data_pack,output_pack] <;> omega
  · exact Nat.le_max_left _ _
lemma rank_next (x : List Bool) : rank (next x) ≤ rank x-1 := by
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
lemma iterate_bounds (x : List Bool) (j : ℕ) :
    (counter (next^[j] x)).length ≤ (counter x).length ∧ data (next^[j] x)=data x ∧
    (output (next^[j] x)).length ≤ (output x).length+j*(data x).length ∧
    (next^[j] x).length ≤ x.length+2*(counter x).length+2*(data x).length+(output x).length+
      j*(data x).length+3 ∧ rank (next^[j] x) ≤ rank x-j := by
  induction j with
  | zero => simp only [Function.iterate_zero_apply,Nat.sub_zero,Nat.le_refl,Nat.zero_mul,
      Nat.add_zero,true_and,and_true]; omega
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    have hc := counter_next (next^[j] x)
    have hd := data_next (next^[j] x)
    have ho := output_next (next^[j] x)
    have hl := length_next (next^[j] x)
    have hr := rank_next (next^[j] x)
    rw [ih.2.1] at hd ho
    refine ⟨hc.trans ih.1,hd,?_,?_,?_⟩
    · nlinarith [ih.2.2.1]
    · apply hl.trans; apply max_le
      · nlinarith [ih.2.2.2.1]
      · rw [hd]; nlinarith [ih.1,ih.2.2.1]
    · omega
lemma stop (x : List Bool) : (next^[rank x] x).head?≠some true := by
  have hh := (iterate_bounds x (rank x)).2.2.2.2
  simp only [Nat.sub_self,Nat.le_zero] at hh
  intro hp
  change (if (next^[rank x] x).head?=some true then _ else 0)=0 at hh
  rw [ite_eq_left hp] at hh; omega
lemma next_nil (d o : List Bool) : next (pack true [] d o)=pack false [] d o := by
  simp only [next,While.next,head_pack,ite_true, if_true,step,counter_pack,data_pack,output_pack]
lemma next_cons (b : Bool) (c d o : List Bool) :
    next (pack true (b::c) d o)=pack true c d (d++o) := by
  simp only [next,While.next,head_pack,ite_true, if_true,step,counter_pack,reduceCtorEq,ite_false, if_false,
    data_pack,output_pack,List.tail_cons]
lemma loop_spec (c d o : List Bool) : next^[c.length+1] (pack true c d o)=
    pack false [] d (copies c.length d++o) := by
  induction c generalizing o with
  | nil => simp only [List.length_nil,Nat.zero_add,Function.iterate_one,next_nil,copies,List.nil_append]
  | cons b c ih => rw [List.length_cons,Function.iterate_succ_apply,next_cons,ih,copies,List.append_assoc]

def run (x : List Bool) : List Bool := copies (extractPrefix x).length (discardPrefix x)
lemma run_pair (c d : List Bool) : run (pairBits (c,d))=copies c.length d := by
  simp only [run,extractPrefix_pairBits,discardPrefix_pairBits]

end RepeatedAppend

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
namespace WordList
namespace Zip

def op (x : List Bool) : List Bool :=
  let a := discardPrefix (discardPrefix x)
  let ys := extractPrefix a
  let os := discardPrefix a
  if ys=[] then a else pairBits (WordList.tail ys,cons (pairBits (extractPrefix (discardPrefix x),head ys)) os)

noncomputable def run (x : List Bool) : List Bool := reverse (discardPrefix
  (Fold.run op (4*Polynomial.X+4) (Fold.pack (extractPrefix x) [] (pairBits (discardPrefix x,[])))))
end Zip
end WordList
end
open BinaryArithmetic
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
namespace RationalArray
noncomputable def addOp : List Bool → List Bool := BinaryRational.addWords ∘ discardPrefix
noncomputable def sumInput (x : List Bool) : List Bool :=
  WordList.Fold.pack x [] (BinaryRational.encode 0)
noncomputable def sumWords : List Bool → List Bool :=
  (WordList.Fold.run addOp (20*(Polynomial.X+1)^2)) ∘ sumInput

noncomputable def mulOp : List Bool → List Bool := BinaryRational.mulWords ∘ discardPrefix
noncomputable def dotWords : List Bool → List Bool :=
  sumWords ∘ ((WordList.mapWith mulOp) ∘ (fun x=>pairBits ([],x)))
noncomputable def dotListsWords : List Bool → List Bool := dotWords ∘ WordList.Zip.run
end RationalArray
attribute [irreducible] RationalArray.sumWords RationalArray.dotWords RationalArray.dotListsWords
namespace RationalMatrix
open WordList

def swapWords (x : List Bool) : List Bool := pairBits (discardPrefix x,extractPrefix x)
end RationalMatrix
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
open BinaryArithmetic
open scoped Matrix
namespace BinaryRational

def subInput (x : List Bool) : List Bool := pairBits (extractPrefix x,negWords (discardPrefix x))
def subWords : List Bool → List Bool := addWords ∘ subInput
end BinaryRational
namespace RationalMatrix
open WordList
noncomputable def vectorScale : List Bool → List Bool := mapWith BinaryRational.mulWords
noncomputable def dotRow : List Bool → List Bool := RationalArray.dotListsWords ∘ swapWords
noncomputable def mulVec : List Bool → List Bool := (mapWith dotRow) ∘ swapWords
noncomputable def quadInput (x : List Bool) : List Bool := pairBits (discardPrefix x,mulVec x)
noncomputable def quad : List Bool → List Bool := RationalArray.dotListsWords ∘ quadInput
end RationalMatrix
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
open BinaryArithmetic
open scoped Matrix
namespace BinaryEllipsoidCut
open RationalMatrix

def dim : List Bool → List Bool := extractPrefix
def rest : List Bool → List Bool := discardPrefix
def shape : List Bool → List Bool := extractPrefix ∘ rest
def rest₂ : List Bool → List Bool := discardPrefix ∘ rest
def direction : List Bool → List Bool := extractPrefix ∘ rest₂
def rest₃ : List Bool → List Bool := discardPrefix ∘ rest₂
def center : List Bool → List Bool := extractPrefix ∘ rest₃

def haInput (x : List Bool) : List Bool := pairBits (shape x,direction x)
noncomputable def haWords : List Bool → List Bool := mulVec ∘ haInput
noncomputable def quadWords : List Bool → List Bool := quad ∘ haInput

def dimension (x : List Bool) : ℚ := value (dim x)
noncomputable def qvalue (x : List Bool) : ℚ := BinaryRational.decode (quadWords x)

def rootPrecision (x : List Bool) : ℕ := 32*value (dim x)
noncomputable def coefCenter (x : List Bool) : List Bool :=
  BinaryRational.encode (1/((dimension x+1)*Ellipsoid.rationalRootUpper (rootPrecision x) (qvalue x)))

noncomputable def scaledHaInput (x : List Bool) : List Bool := pairBits (coefCenter x,haWords x)
noncomputable def scaledHa : List Bool → List Bool := vectorScale ∘ scaledHaInput
noncomputable def centerInput (x : List Bool) : List Bool := pairBits (center x,scaledHa x)
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
namespace WordList.Find

def operation (p : List Bool → Bool) (x : List Bool) : List Bool :=
  if accum x=[] then if p (pairBits (context x,item x)) then true::item x else [] else accum x

noncomputable def run (p : List Bool → Bool) : List Bool → List Bool :=
  Fold.run (operation p) (3*Polynomial.X+3) ∘
    (fun x=>Fold.pack (discardPrefix x) (extractPrefix x) [])
end WordList.Find
end
open BinaryArithmetic RationalLinearFeasibility
namespace BinaryRow
open RationalMatrix

def bound : List Bool → List Bool := discardPrefix ∘ discardPrefix
def dotInput (x : List Bool) : List Bool := pairBits (coeff x,extractPrefix x)
noncomputable def dot : List Bool → List Bool := RationalArray.dotListsWords ∘ dotInput
noncomputable def good (x : List Bool) : Bool := decide (BinaryRational.decode (dot x)≤BinaryRational.decode (bound x))
noncomputable def bad (x : List Bool) : Bool := !good x
noncomputable def run : List Bool → List Bool := WordList.Find.run bad
end BinaryRow
namespace BinaryEllipsoidAdvance
open Ellipsoid RationalMatrix
open scoped Matrix

def dim : List Bool → List Bool := extractPrefix
def rest : List Bool → List Bool := discardPrefix
def precision : List Bool → List Bool := extractPrefix ∘ rest
def rest₂ : List Bool → List Bool := discardPrefix ∘ rest
def rows : List Bool → List Bool := extractPrefix ∘ rest₂
def stored : List Bool → List Bool := discardPrefix ∘ rest₂
def shape : List Bool → List Bool := extractPrefix ∘ stored
def center : List Bool → List Bool := discardPrefix ∘ stored
noncomputable def found (x : List Bool) : List Bool := BinaryRow.run (pairBits (center x,rows x))
noncomputable def direction (x : List Bool) : List Bool := extractPrefix (found x).tail

noncomputable def cutInput (x : List Bool) : List Bool :=
  pairBits (dim x,pairBits (shape x,pairBits (direction x,pairBits (center x,precision x))))
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
open BinaryArithmetic RationalLinearFeasibility Ellipsoid
namespace BinaryEllipsoidInitial
open RationalMatrix WordList

def ctx : List Bool → List Bool := extractPrefix ∘ extractPrefix
def row : List Bool → List Bool := discardPrefix ∘ extractPrefix
def col : List Bool → List Bool := discardPrefix

def entryWords (x : List Bool) : List Bool :=
  if value (row x)≤value (col x) then
    if value (col x)≤value (row x) then discardPrefix (ctx x) else BinaryRational.encode 0
  else BinaryRational.encode 0

noncomputable def rowInput (x : List Bool) : List Bool :=
  pairBits (x,indices (extractPrefix (extractPrefix x)))
noncomputable def rowWords : List Bool → List Bool := mapWith entryWords ∘ rowInput

noncomputable def runInput (x : List Bool) : List Bool := pairBits (x,indices (extractPrefix x))
noncomputable def run : List Bool → List Bool := mapWith rowWords ∘ runInput
end BinaryEllipsoidInitial
end
open BinaryArithmetic RationalLinearFeasibility Ellipsoid
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
open BinaryArithmetic
namespace NaturalArray
open WordList

noncomputable def exponentiate (x : List Bool) : List Bool := productWords (repeatWords x)
noncomputable def unaryLog (x : List Bool) : List Bool :=
  if value x=0 then [true] else RepeatedAppend.copies (BinaryArithmetic.normalize x).length [true]
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
open BinaryArithmetic RationalLinearFeasibility Ellipsoid
namespace BinaryDecision
open UnaryResources NaturalArray

def bound : List Bool → List Bool := extractPrefix ∘ rest₂
def rows : List Bool → List Bool := discardPrefix ∘ rest₃
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
open BinaryArithmetic RationalLinearFeasibility Ellipsoid
namespace BinaryDecision
open WordList RationalMatrix

def boundOp (x : List Bool) : List Bool := pairBits (discardPrefix x,extractPrefix x)
noncomputable def boxShape (s : Bool) (x : List Bool) : List Bool :=
  BinaryEllipsoidInitial.run (pairBits (nword x,BinaryRational.encode (if s then 1 else -1)))
noncomputable def boxWords (s : Bool) (x : List Bool) : List Bool :=
  mapWith boundOp (pairBits (BinaryRational.encode (value (bound x):ℚ),boxShape s x))
noncomputable def boundedWords (x : List Bool) : List Bool := rows x++boxWords true x++boxWords false x

def relaxedOp (x : List Bool) : List Bool :=
  pairBits (extractPrefix (discardPrefix x),BinaryRational.encode
    (BinaryRational.decode (discardPrefix (discardPrefix x))+BinaryRational.decode (extractPrefix x)))
end BinaryDecision
end
open BinaryArithmetic
end MetricKMedianRecovery.BitMachine

end OAI
end


