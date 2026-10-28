-- Prove2me | Definitions.Def_OAIQ035K001
-- name    : OAIQ035K001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T07:53:12.808203+00:00
-- url     : https://prove2.me/theorems/64523bb9-09be-4732-80ab-9d13a8b9e4ea
-- title:
--   Definitions bundle OAIQ035K001 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 119 declarations of OpenAI's Lean: 55 definitions, 3 inductive types or structures, 2 instances and 59 theorems. The definitions and types are `OAI.MetricKMedian.Binary.Automatic.Coding`, `OAI.MetricKMedian.Binary.Automatic.enc`, `OAI.MetricKMedian.Binary.BoundedRun`, `OAI.MetricKMedian.Binary.DivisionLoop.S`, `OAI.MetricKMedian.Binary.DivisionLoop.body`, `OAI.MetricKMedian.Binary.DivisionLoop.eval`, `OAI.MetricKMedian.Binary.DivisionLoop.next`, `OAI.MetricKMedian.Binary.DivisionLoop.potential`, `OAI.MetricKMedian.Binary.DivisionLoop.qstep`, `OAI.MetricKMedian.Binary.DivisionLoop.result`, `OAI.MetricKMedian.Binary.DivisionLoop.rstep`, `OAI.MetricKMedian.Binary.GCDLoop.S`, `OAI.MetricKMedian.Binary.GCDLoop.body`, `OAI.MetricKMedian.Binary.GCDLoop.next`, `OAI.MetricKMedian.Binary.GCDLoop.potential`, `OAI.MetricKMedian.Binary.GCDLoop.result`, `OAI.MetricKMedian.Binary.HasHeight`, `OAI.MetricKMedian.Binary.ListAlgorithms.indexStep`, `OAI.MetricKMedian.Binary.ListFindIdx.body`, `OAI.MetricKMedian.Binary.ListFindIdx.result`, `OAI.MetricKMedian.Binary.ListFold.body`, `OAI.MetricKMedian.Binary.ListFold.result`, `OAI.MetricKMedian.Binary.ListReverse.body`, `OAI.MetricKMedian.Binary.ListReverse.result`, `OAI.MetricKMedian.Binary.ListSplit.body`, `OAI.MetricKMedian.Binary.ListSplit.result`, `OAI.MetricKMedian.Binary.ListZip.body`, `OAI.MetricKMedian.Binary.ListZip.result`, `OAI.MetricKMedian.Binary.MultiplicationLoop.S`, `OAI.MetricKMedian.Binary.MultiplicationLoop.body`, `OAI.MetricKMedian.Binary.MultiplicationLoop.next`, `OAI.MetricKMedian.Binary.MultiplicationLoop.potential`, `OAI.MetricKMedian.Binary.MultiplicationLoop.result`, `OAI.MetricKMedian.Binary.ParallelTransducer`, `OAI.MetricKMedian.Binary.ParallelTransducer.Label`, `OAI.MetricKMedian.Binary.ParallelTransducer.run`, `OAI.MetricKMedian.Binary.ParallelTransducer.width`, `OAI.MetricKMedian.Binary.Ratio.normalized`, `OAI.MetricKMedian.Binary.Ratio.parts`, `OAI.MetricKMedian.Binary.ReverseLoop.S` and 18 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics/KMedian, in whole or in part: `KMedian_Binary_BinaryAutomatic`, `KMedian_Binary_BinaryDivision`, `KMedian_Binary_BinaryGCD`, `KMedian_Binary_BinaryInteger`, `KMedian_Binary_BinaryListContext`, `KMedian_Binary_BinaryListFold`, `KMedian_Binary_BinaryListIndex`, `KMedian_Binary_BinaryListIndices`, `KMedian_Binary_BinaryListMap`, `KMedian_Binary_BinaryListSelection`, `KMedian_Binary_BinaryListZip`, `KMedian_Binary_BinaryLists`, `KMedian_Binary_BinaryMultiplication`, `KMedian_Binary_BinaryNatural`, `KMedian_Binary_BinaryRational`, `KMedian_Binary_BinaryRationalFold`, `KMedian_Binary_BinaryRationalHeight`, `KMedian_Binary_BinarySubtraction`, `KMedian_Binary_BinaryWords`, `KMedian_Binary_BooleanLoop`, `KMedian_Binary_BooleanParallelTransducer`, `KMedian_Binary_BooleanPolynomial`, `KMedian_Binary_BooleanProducts`, `KMedian_Binary_BooleanReverse`, `KMedian_Compression_CircuitBitBound`, `KMedian_Compression_RationalOperationHeight`, `KMedian_Process_RoundingListOperations`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ035K013`, `OAIQ035K014`, `OAIQ035K015`, `OAIQ035K016`, `OAIQ035K017`, `OAIQ035K018`, `OAIQ035K019`, `OAIQ035K020`, `OAIQ035K021`, `OAIQ035K022`, `OAIQ035K023`, `OAIQ035K024`, `OAIQ035K025`, `OAIQ035K026`, `OAIQ035K038` and `OAIQ035K062`; the proofs of `OAI.MetricKMedian.CountStatistic.variance_bound` and `OAI.MetricKMedian.Preparation.support_repaired_cost`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/KMedian at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ035_KM.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Binary_BooleanPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                         
section
namespace MetricKMedian.Binary
open Turing Polynomial

 theorem polynomial_eval_mono (p : Polynomial ℕ) {a b : ℕ} (h : a ≤ b) :
    p.eval a ≤ p.eval b := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [Polynomial.eval_add] using Nat.add_le_add hp hq
  | monomial n x =>
      simpa only [Polynomial.eval_monomial] using Nat.mul_le_mul_left x (Nat.pow_le_pow_left h n)

end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Binary_BooleanLoop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                   
section
namespace MetricKMedian.Binary
open Turing Function Polynomial

def encodeLoop {α β : Type} (ea : α → List Bool) (eb : β → List Bool) : β ⊕ α → List Bool
  | .inl b => false::eb b
  | .inr a => true::ea a

inductive BoundedRun {α β : Type} (ea : α → List Bool) (f : α → β ⊕ α) (S : ℕ) :
    ℕ → α → β → Prop
  | stop {a b} : (ea a).length ≤ S → f a=.inl b → BoundedRun ea f S 1 a b
  | step {a a' b n} : (ea a).length ≤ S → f a=.inr a' →
      BoundedRun ea f S n a' b → BoundedRun ea f S (n+1) a b

end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Binary_BooleanParallelTransducer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                 
section
namespace MetricKMedian.Binary
open Turing Function Polynomial Finset

structure ParallelTransducer where
  Q : Type
  [finiteQ : Fintype Q]
  initial : Q
  next : Q → Bool → Q × (List Bool × List Bool)
  finish : Q → List Bool × List Bool
attribute [instance] ParallelTransducer.finiteQ

namespace ParallelTransducer
variable (T : ParallelTransducer)

def run : T.Q → List Bool → List Bool × List Bool
  | q, [] => T.finish q
  | q, b::xs =>
    let v := T.next q b
    let z := run v.1 xs
    (v.2.1++z.1,v.2.2++z.2)

def width : ℕ := max (univ.sup (fun q => (T.finish q).1.length+(T.finish q).2.length))
  (univ.sup (fun x : T.Q × Bool => (T.next x.1 x.2).2.1.length+(T.next x.1 x.2).2.2.length))

 theorem finish_length (q : T.Q) : (T.finish q).1.length+(T.finish q).2.length≤T.width :=
  (le_sup (f:=fun q => (T.finish q).1.length+(T.finish q).2.length) (mem_univ q)).trans (Nat.le_max_left _ _)

 theorem next_length (q : T.Q) (b : Bool) :
    (T.next q b).2.1.length+(T.next q b).2.2.length≤T.width :=
  (le_sup (f:=fun x : T.Q × Bool => (T.next x.1 x.2).2.1.length+(T.next x.1 x.2).2.2.length)
    (mem_univ (q,b))).trans (Nat.le_max_right _ _)

 theorem run_length (q : T.Q) (xs : List Bool) :
    (T.run q xs).1.length+(T.run q xs).2.length≤T.width*(xs.length+1) := by
  induction xs generalizing q with
  | nil => simpa only [run,List.length_nil,zero_add,mul_one] using T.finish_length q
  | cons b xs ih =>
      have hn := T.next_length q b
      have ht := ih (T.next q b).1
      simp only [run,List.length_append,List.length_cons]
      rw [show xs.length+1+1=(xs.length+1)+1 by rfl,Nat.mul_add,mul_one]
      omega

abbrev Label := T.Q ⊕ Bool

end ParallelTransducer
end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Binary_BooleanProducts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                       
section
namespace MetricKMedian.Binary
open Turing Function Polynomial

namespace WordTransducer

def duplicate : ParallelTransducer where
  Q := Unit
  initial := ()
  next _ b := ((),([true,b],[b]))
  finish _ := ([false],[])

def exchange : ParallelTransducer where
  Q := Option Bool
  initial := none
  next q b := match q with
    | none => (some (!b),([],[]))
    | some false => (none,([],[b]))
    | some true => (some true,([true,b],[]))
  finish _ := ([false],[])

end WordTransducer

end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Binary_BooleanReverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                      
section
namespace MetricKMedian.Binary
open Function Polynomial

namespace ReverseLoop
abbrev S := List Bool × List Bool

def body (s : S) : List Bool ⊕ S :=
  if s.1.isEmpty then .inl s.2 else .inr (s.1.tail,s.1.head?.getD false::s.2)

def result (s : S) : List Bool := s.1.reverse++s.2

end ReverseLoop

end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Binary_BinaryWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                   
section
namespace MetricKMedian.Binary
open Function Polynomial

namespace Word

def value : List Bool → ℕ
  | [] => 0
  | b::bs => b.toNat+2*value bs

@[simp] theorem value_nil : value []=0 := rfl
@[simp] theorem value_cons (b : Bool) (xs : List Bool) : value (b::xs)=b.toNat+2*value xs := rfl

 theorem value_bits (n : ℕ) : value n.bits=n := by
  induction n using Nat.binaryRec' with
  | zero => rfl
  | bit b n hn ih => rw [Nat.bits_append_bit n b hn,value_cons,ih,Nat.bit_val]; omega

 theorem value_zero (xs : List Bool) : value xs=0 ↔ ∀ b∈xs,b=false := by
  induction xs with
  | nil => simp
  | cons b xs ih => simp only [value_cons,Nat.add_eq_zero_iff,Nat.mul_eq_zero,OfNat.ofNat_ne_zero,false_or,Bool.toNat_eq_zero,ih,List.forall_mem_cons]

 theorem bits_value (xs : List Bool) (h : xs.getLast?≠some false) : (value xs).bits=xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
      by_cases he : xs=[]
      · subst xs
        cases b
        · exact False.elim (h rfl)
        · rfl
      · have ht : xs.getLast?≠some false := by
          intro hh
          apply h
          simp only [List.getLast?_cons,hh,Option.getD_some]
        rw [value_cons,show b.toNat+2*value xs=Nat.bit b (value xs) by rw [Nat.bit_val]; omega]
        rw [Nat.bits_append_bit,ih ht]
        intro hzero
        exfalso
        have hh := value_zero xs |>.mp hzero
        have hl := List.getLast_mem he
        have hb := hh _ hl
        apply ht
        rw [List.getLast?_eq_some_getLast he,hb]

 theorem value_append (xs ys : List Bool) : value (xs++ys)=value xs+2^xs.length*value ys := by
  induction xs with
  | nil => simp
  | cons b xs ih => simp only [List.cons_append,value_cons,ih,List.length_cons,pow_succ]; ring

 theorem value_reverse_drop (xs : List Bool) : value (xs.dropWhile Bool.not).reverse=value xs.reverse := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
      cases b
      · simp only [List.dropWhile_cons,Bool.not_false,ite_true,List.reverse_cons,value_append,
          value_cons,value_nil,Bool.toNat_false,Nat.mul_zero,Nat.add_zero,zero_add]
        exact ih
      · simp

 theorem drop_head (xs : List Bool) : (xs.dropWhile Bool.not).head?≠some false := by
  induction xs with
  | nil => simp
  | cons b xs ih => cases b <;> simp_all

 def normalize (xs : List Bool) : List Bool := (xs.reverse.dropWhile Bool.not).reverse

 theorem normalize_eq_bits (xs : List Bool) : normalize xs=(value xs).bits := by
  have hv : value (normalize xs)=value xs := by
    simpa only [normalize,List.reverse_reverse] using value_reverse_drop xs.reverse
  rw [← hv,bits_value]
  simp only [normalize,List.getLast?_reverse]
  exact drop_head _

end Word

end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Binary_BinaryLists
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                   
section
namespace MetricKMedian.Binary
open Function Polynomial

namespace ListReverse
variable {α : Type} (ea : α → List Bool) (a0 : α)
 def body (s : List α × List α) : List α ⊕ (List α × List α) :=
  if s.1.isEmpty then .inl s.2 else .inr (s.1.tail,s.1.head?.getD a0::s.2)
 def result (s : List α × List α) : List α := s.1.reverse++s.2

end ListReverse

end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Binary_BinaryListFold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                      
section
namespace MetricKMedian.Binary
open Function Polynomial

namespace ListFold
variable {α β : Type} (ea : α → List Bool) (eb : β → List Bool) (a0 : α)
variable (op : β × α → β)
 def body (s : List α × β) : β ⊕ (List α × β) :=
  if s.1.isEmpty then .inl s.2 else .inr (s.1.tail,op (s.2,s.1.head?.getD a0))
 def result (s : List α × β) : β := s.1.foldl (fun b a => op (b,a)) s.2

end ListFold

end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Binary_BinaryNatural
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                     
section
namespace MetricKMedian.Binary
open Function Polynomial

namespace Word
 theorem normalize_length (xs : List Bool) : (normalize xs).length≤xs.length := by
  simpa only [normalize,List.length_reverse] using List.length_dropWhile_le Bool.not xs.reverse

 theorem bits_value_length (xs : List Bool) : (value xs).bits.length≤xs.length := by
  rw [← normalize_eq_bits]
  exact normalize_length xs
end Word

namespace NatBinary
 theorem zero_iff (n : ℕ) : n.bits=[] ↔ n=0 := by
  constructor
  · intro h
    have hv := Word.value_bits n
    rw [h,Word.value_nil] at hv
    exact hv.symm
  · rintro rfl; rfl

 theorem bit_length (b : Bool) (n : ℕ) : (Nat.bit b n).bits.length≤n.bits.length+1 := by
  have h := Word.bits_value_length (b::n.bits)
  simpa only [Word.value_cons,Word.value_bits,Nat.bit_val,Nat.add_comm,List.length_cons] using h

 theorem half_length (n : ℕ) : n.div2.bits.length=n.bits.length-1 := by
  rw [Nat.div2_bits_eq_tail,List.length_tail]

 theorem add_length (a b : ℕ) : (a+b).bits.length≤ max a.bits.length b.bits.length+1 := by
  simp only [Nat.size_eq_bits_len]
  apply Nat.size_le.mpr
  have ha := (Nat.lt_size_self a).trans_le (Nat.pow_le_pow_right (by decide : 1≤2) (le_max_left a.size b.size))
  have hb := (Nat.lt_size_self b).trans_le (Nat.pow_le_pow_right (by decide : 1≤2) (le_max_right a.size b.size))
  rw [pow_succ]
  omega

 theorem length_mono {a b : ℕ} (h : a≤b) : a.bits.length≤b.bits.length := by
  simpa only [Nat.size_eq_bits_len] using Nat.size_le_size h

 theorem half_lt_length {n : ℕ} (hn : n≠0) : n.div2.bits.length<n.bits.length := by
  rw [half_length]
  have hh : n.bits≠[] := fun h => hn ((zero_iff n).mp h)
  have hl : 0<n.bits.length := List.length_pos_iff.mpr hh
  omega
end NatBinary

end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Binary_BinaryListMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                     
section
namespace MetricKMedian.Binary
open Function Polynomial

namespace ListAlgorithms
variable {α β : Type}
 theorem pushMap (f : α → β) (as : List α) (bs : List β) :
    as.foldl (fun bs a => f a::bs) bs=(as.map f).reverse++bs := by
  induction as generalizing bs with
  | nil => rfl
  | cons a as ih =>
      rw [List.foldl_cons,ih,List.map_cons,List.reverse_cons,List.append_assoc,List.singleton_append]

 theorem pushFilter (f : α → Bool) (as bs : List α) :
    as.foldl (fun bs a => if f a then a::bs else bs) bs=(as.filter f).reverse++bs := by
  induction as generalizing bs with
  | nil => rfl
  | cons a as ih =>
      simp only [List.foldl_cons,List.filter_cons]
      cases f a <;> simp only [Bool.false_eq_true,ite_false,ite_true,ih,List.reverse_cons,List.append_assoc,List.singleton_append]

 theorem count (as : List α) (n : ℕ) : as.foldl (fun n _ => n+1) n=n+as.length := by
  induction as generalizing n with
  | nil => rfl
  | cons a as ih => simp only [List.foldl_cons,ih,List.length_cons]; omega

 theorem all (p : α → Bool) (as : List α) (b : Bool) :
    as.foldl (fun b a => b && p a) b=(b && as.all p) := by
  induction as generalizing b with
  | nil => simp
  | cons a as ih => simp only [List.foldl_cons,ih,List.all_cons,Bool.and_assoc]

 theorem any (p : α → Bool) (as : List α) (b : Bool) :
    as.foldl (fun b a => b || p a) b=(b || as.any p) := by
  induction as generalizing b with
  | nil => simp
  | cons a as ih => simp only [List.foldl_cons,ih,List.any_cons,Bool.or_assoc]
end ListAlgorithms

end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Binary_BinaryListContext
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                         
section
namespace MetricKMedian.Binary
open Function Polynomial
namespace ListAlgorithms
variable {α β γ : Type}
 theorem pushMapWith (f : γ × α → β) (as : List α) (c : γ) (bs : List β) :
    as.foldl (fun x a => (x.1,f (x.1,a)::x.2)) (c,bs)=(c,(as.map (fun a => f (c,a))).reverse++bs) := by
  induction as generalizing bs with
  | nil => rfl
  | cons a as ih =>
      simpa only [List.foldl_cons,List.map_cons,List.reverse_cons,List.append_assoc,List.singleton_append] using ih (f (c,a)::bs)
 theorem pushMapWith_pair (f : γ × α → β) (as : List α) (x : γ × List β) :
    as.foldl (fun x a => (x.1,f (x.1,a)::x.2)) x=(x.1,(as.map (fun a => f (x.1,a))).reverse++x.2) := by
  cases x
  exact pushMapWith _ _ _ _
 theorem filterMapPair (p : γ × α → Bool) (c : γ) (as : List α) :
    (((as.map (fun a => (c,a))).filter p).map Prod.snd)=as.filter (fun a => p (c,a)) := by
  induction as with
  | nil => rfl
  | cons a as ih =>
      simp only [List.map_cons,List.filter_cons]
      split <;> simp_all only [List.map_cons]
end ListAlgorithms

end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Binary_BinarySubtraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                         
section
namespace MetricKMedian.Binary
open Function Polynomial

namespace Word
 def borrowBit (a b c : Bool) : Bool := ((!a) && b) || ((!a) && c) || (b && c)

 theorem value_lt (xs : List Bool) : value xs<2^xs.length := by
  induction xs with
  | nil => decide
  | cons b xs ih =>
      have hb : b.toNat≤1 := by cases b <;> decide
      simp only [value_cons,List.length_cons,pow_succ]
      omega

end Word

end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Binary_BinaryListIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                       
section
namespace MetricKMedian.Binary
open Function Polynomial
namespace ListSplit
variable {α : Type} (ea : α → List Bool) (a0 : α)
def body (x : List α × (ℕ × List α)) : (List α × List α) ⊕ (List α × (ℕ × List α)) :=
  if x.1.isEmpty || decide (x.2.1=0) then .inl (x.2.2.reverse,x.1)
  else .inr (x.1.tail,(x.2.1-1,x.1.head?.getD a0::x.2.2))
def result (x : List α × (ℕ × List α)) : List α × List α := (x.2.2.reverse++x.1.take x.2.1,x.1.drop x.2.1)
end ListSplit

end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Binary_BinaryDivision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                      
section
namespace MetricKMedian.Binary
open Function Polynomial

namespace DivisionLoop
 def qstep (b : Bool) (d q r : ℕ) : ℕ := Nat.bit (!decide (Nat.bit b r<d)) q
 def rstep (b : Bool) (d r : ℕ) : ℕ := if Nat.bit b r<d then Nat.bit b r else Nat.bit b r-d

 theorem step_total (b : Bool) (d q r : ℕ) :
    qstep b d q r*d+rstep b d r=2*(q*d+r)+b.toNat := by
  by_cases ht : Nat.bit b r<d
  · rw [qstep,rstep,ite_eq_left ht,decide_eq_true ht]
    simp only [Bool.not_true,Nat.bit_val,Bool.toNat_false]
    ring
  · have hd : d≤Nat.bit b r := by omega
    have he := Nat.sub_add_cancel hd
    rw [qstep,rstep,ite_eq_right ht,decide_eq_false ht]
    simp only [Bool.not_false,Nat.bit_val,Bool.toNat_true] at *
    nlinarith

 theorem step_remainder (b : Bool) (d r : ℕ) (_ : 0<d) (hr : r<d) : rstep b d r<d := by
  have hb : b.toNat≤1 := by cases b <;> decide
  unfold rstep
  split_ifs with ht
  · exact ht
  · simp only [Nat.bit_val] at *
    omega

 def eval : List Bool → ℕ → ℕ → ℕ → ℕ × ℕ
  | [],_,q,r => (q,r)
  | b::xs,d,q,r => eval xs d (qstep b d q r) (rstep b d r)

 theorem eval_spec (xs : List Bool) (d q r : ℕ) (hd : 0<d) (hr : r<d) :
    (eval xs d q r).2<d ∧
      (eval xs d q r).1*d+(eval xs d q r).2=2^xs.length*(q*d+r)+Word.value xs.reverse := by
  induction xs generalizing q r with
  | nil => exact ⟨hr,by simp [eval]⟩
  | cons b xs ih =>
      obtain ⟨hrem,heq⟩ := ih (qstep b d q r) (rstep b d r) (step_remainder b d r hd hr)
      refine ⟨hrem,?_⟩
      change (eval xs d (qstep b d q r) (rstep b d r)).1*d+
        (eval xs d (qstep b d q r) (rstep b d r)).2=_
      rw [heq,step_total]
      simp only [List.length_cons,List.reverse_cons,Word.value_append,Word.value_cons,Word.value_nil,
        Nat.mul_zero,Nat.add_zero,List.length_reverse,pow_succ]
      ring

abbrev S := List Bool × (ℕ × (ℕ × ℕ))
 def next (s : S) : S :=
  (s.1.tail,(s.2.1,(qstep (s.1.head?.getD false) s.2.1 s.2.2.1 s.2.2.2,
    rstep (s.1.head?.getD false) s.2.1 s.2.2.2)))
 def body (s : S) : (ℕ × ℕ) ⊕ S := if s.1.isEmpty then .inl s.2.2 else .inr (next s)
 def result (s : S) : ℕ × ℕ := eval s.1 s.2.1 s.2.2.1 s.2.2.2
 def potential (s : S) : ℕ := s.1.length+max s.2.2.1.bits.length s.2.2.2.bits.length

 theorem next_potential (s : S) (h : s.1.isEmpty=false) : potential (next s)≤potential s := by
  have hx : s.1.tail.length < s.1.length := by
    cases hh : s.1 with
    | nil => simp only [hh,List.isEmpty_nil] at h; contradiction
    | cons b xs => simp only [List.tail_cons,List.length_cons]; omega
  have hq := NatBinary.bit_length (!decide (Nat.bit (s.1.head?.getD false) s.2.2.2 < s.2.1)) s.2.2.1
  have hr := NatBinary.bit_length (s.1.head?.getD false) s.2.2.2
  have hrle : rstep (s.1.head?.getD false) s.2.1 s.2.2.2≤Nat.bit (s.1.head?.getD false) s.2.2.2 := by
    unfold rstep
    split_ifs <;> omega
  have hrl := (NatBinary.length_mono hrle).trans hr
  simp only [potential,next,qstep]
  omega

end DivisionLoop

end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Binary_BinaryGCD
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                 
section
namespace MetricKMedian.Binary
open Function Polynomial

namespace NatBinary
 theorem mod_length_lt {a b : ℕ} (hb : 0 < b) (hba : b ≤ a) : (a%b).bits.length < a.bits.length := by
  have ha : 0 < a := hb.trans_le hba
  by_cases hz : a%b=0
  · rw [hz,Nat.zero_bits,List.length_nil]
    apply List.length_pos_iff.mpr
    intro h
    have := (zero_iff a).mp h
    omega
  · have hr := Nat.mod_lt a hb
    have he := Nat.mod_add_div a b
    have hq : 1 ≤ a/b := (Nat.le_div_iff_mul_le hb).mpr (by simpa only [one_mul] using hba)
    have hm : b ≤ b*(a/b) := by nlinarith
    have hsmall : 2*(a%b) < a := by omega
    have hlen := length_mono hsmall.le
    have hbit : (2*(a%b)).bits.length=(a%b).bits.length+1 := by
      have hn : Nat.bit false (a%b) ≠ 0 := by
        simp only [Nat.bit_val,Bool.toNat_false,Nat.add_zero]
        omega
      simpa only [Nat.size_eq_bits_len,Nat.bit_val,Bool.toNat_false,Nat.add_zero,Nat.succ_eq_add_one]
        using Nat.size_bit hn
    omega
end NatBinary

namespace GCDLoop
abbrev S := ℕ × ℕ
 def next (s : S) : S := (s.2,s.1%s.2)
 def body (s : S) : ℕ ⊕ S := if s.2=0 then .inl s.1 else .inr (next s)
 def result (s : S) : ℕ := s.1.gcd s.2
 def potential (s : S) : ℕ := s.1.bits.length+s.2.bits.length

 theorem next_result (s : S) : result (next s)=result s := by
  simp only [result,next]
  calc s.2.gcd (s.1%s.2)=(s.1%s.2).gcd s.2 := Nat.gcd_comm _ _
    _=s.2.gcd s.1 := (Nat.gcd_rec _ _).symm
    _=s.1.gcd s.2 := Nat.gcd_comm _ _

 theorem next_potential (s : S) : potential (next s) ≤ potential s := by
  have hm := NatBinary.length_mono (Nat.mod_le s.1 s.2)
  simp only [potential,next]
  omega

 theorem next_potential_lt (s : S) (ho : s.2 ≤ s.1) (hb : s.2 ≠ 0) : potential (next s) < potential s := by
  have h := NatBinary.mod_length_lt (Nat.pos_of_ne_zero hb) ho
  simp only [potential,next]
  omega

end GCDLoop

end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Binary_BinaryMultiplication
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.Binary
open Function Polynomial

namespace MultiplicationLoop
abbrev S := ℕ × (ℕ × ℕ)
 def next (s : S) : S := (s.1.div2,(Nat.bit false s.2.1,if s.1.bodd then s.2.2+s.2.1 else s.2.2))
 def body (s : S) : ℕ ⊕ S := if s.1=0 then .inl s.2.2 else .inr (next s)
 def result (s : S) : ℕ := s.1*s.2.1+s.2.2
 def potential (s : S) : ℕ := s.1.bits.length+max s.2.1.bits.length s.2.2.bits.length

 theorem next_potential (s : S) (h : s.1≠0) : potential (next s)≤potential s := by
  have hx := NatBinary.half_lt_length h
  have hy := NatBinary.bit_length false s.2.1
  have ha := NatBinary.add_length s.2.2 s.2.1
  simp only [potential,next]
  cases s.1.bodd <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> omega

 theorem next_result (s : S) : result (next s)=result s := by
  have h := Nat.bodd_add_div2 s.1
  simp only [result,next,Nat.bit_val,Bool.toNat_false,Nat.add_zero]
  cases he : s.1.bodd
  · simp only [he,Bool.toNat_false,zero_add] at h
    simp only [Bool.false_eq_true,ite_false]
    nlinarith only [congrArg (fun n => n*s.2.1) h]
  · simp only [he,Bool.toNat_true] at h
    simp only [ite_true]
    nlinarith only [congrArg (fun n => n*s.2.1) h]

end MultiplicationLoop

end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Binary_BinaryInteger
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                     
section
namespace MetricKMedian.Binary
open Function Polynomial

namespace Signed
 def value (s : Bool) (n : ℕ) : ℤ := if s then -(n:ℤ) else n
 def sign (z : ℤ) : Bool := decide (z < 0)
 def parts (z : ℤ) : Bool × ℕ := (sign z,z.natAbs)

 theorem abs_value (s : Bool) (n : ℕ) : (value s n).natAbs=n := by cases s <;> simp [value]
 theorem sign_value (s : Bool) (n : ℕ) : sign (value s n)=(s && !decide (n=0)) := by
  cases s <;> by_cases hn : n=0
  all_goals simp only [value,sign,Bool.false_eq_true,ite_false,ite_true]
  all_goals simp [hn, Nat.pos_of_ne_zero]

 theorem value_parts (z : ℤ) : value (sign z) z.natAbs=z := by
  unfold value sign
  split_ifs with h
  · exact (Int.eq_neg_natAbs_of_nonpos (le_of_lt (of_decide_eq_true h))).symm
  · exact Int.natAbs_of_nonneg (by simpa using h)

 theorem value_neg (s : Bool) (n : ℕ) : value (!s) n= -value s n := by
  cases s <;> simp [value]

 theorem value_mul (s t : Bool) (n m : ℕ) : value (xor s t) (n*m)=value s n*value t m := by
  cases s <;> cases t <;> simp [value]

 def add (s t : Bool) (n m : ℕ) : ℤ :=
  if s=t then value s (n+m) else if n < m then value t (m-n) else value s (n-m)

 theorem value_add (s t : Bool) (n m : ℕ) : add s t n m=value s n+value t m := by
  cases s <;> cases t <;> by_cases h : n < m <;> simp [add,value,h] <;> omega

 theorem value_div (s : Bool) (n d : ℕ) (h : d∣n) : value s (n/d)=value s n/(d:ℤ) := by
  have hd : (d:ℤ)∣(n:ℤ) := Int.natCast_dvd_natCast.mpr h
  cases s <;> simp only [value,Bool.false_eq_true,ite_false,ite_true,Int.neg_ediv_of_dvd hd,Int.ofNat_ediv_ofNat]
end Signed

end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Binary_BinaryRational
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                      
section
namespace MetricKMedian.Binary
open Function Polynomial

namespace Ratio
 def parts (q : ℚ) : ℤ × ℕ := (q.num,q.den)
 def normalized (x : ℤ × ℕ) : ℤ × ℕ :=
  if x.2=0 then (0,1) else
    (Signed.value (Signed.sign x.1) (x.1.natAbs / x.2.gcd x.1.natAbs),x.2 / x.2.gcd x.1.natAbs)
 theorem normalized_eq (x : ℤ × ℕ) : normalized x=parts (mkRat x.1 x.2) := by
  simp only [normalized,parts,Rat.num_mkRat,Rat.den_mkRat]
  split_ifs with h
  · rfl
  · rw [Signed.value_div _ _ _ (Nat.gcd_dvd_right _ _),Signed.value_parts]

 theorem inv_eq (q : ℚ) : q⁻¹=mkRat (Signed.value (Signed.sign q.num) q.den) q.num.natAbs := by
  rw [Rat.mkRat_eq_div]
  calc
    q⁻¹ = ((q.num:ℚ)/q.den)⁻¹ := congrArg Inv.inv q.num_div_den.symm
    _ = (q.den:ℚ)/q.num := inv_div _ _
    _ = _ := by
      have hnum := Signed.value_parts q.num
      unfold Signed.value at hnum ⊢
      split_ifs with hn
      · rw [ite_eq_left hn] at hnum
        have haZ : (q.num.natAbs:ℤ) = -q.num := by omega
        have ha : (q.num.natAbs:ℚ) = -(q.num:ℚ) := by simpa only [Int.cast_natCast,Int.cast_neg] using congrArg (fun z : ℤ => (z:ℚ)) haZ
        rw [Int.cast_neg,Int.cast_natCast,ha,neg_div_neg_eq]
      · rw [ite_eq_right hn] at hnum
        have ha : (q.num.natAbs:ℚ) = (q.num:ℚ) := by simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z:ℚ)) hnum
        rw [Int.cast_natCast,ha]
end Ratio

end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Compression_CircuitBitBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.Gaussian
open Finset

theorem ratio_num_den_bound (a b : ℤ) (hb : b ≠ 0) (H : ℤ)
    (ha : |a| ≤ H) (hbH : |b| ≤ H) :
    |((a:ℚ)/(b:ℚ)).num| ≤ H ∧ (((a:ℚ)/(b:ℚ)).den:ℤ) ≤ H := by
  let q := (a:ℚ)/(b:ℚ)
  obtain ⟨c,hcA,hcB⟩ := Rat.num_den_mk hb (q := q) (by exact (Rat.divInt_eq_div a b).symm)
  have hc : c ≠ 0 := by intro hz; rw [hz,zero_mul] at hcB; exact hb hcB
  have hc1 : (1:ℤ) ≤ |c| := by
    have ha := abs_pos.mpr hc
    omega
  have hnum : |q.num| ≤ |a| := by
    rw [hcA,abs_mul]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hc1 (abs_nonneg q.num)
  have hden : (q.den:ℤ) ≤ |b| := by
    rw [hcB,abs_mul,abs_of_nonneg (by positivity : (0:ℤ) ≤ q.den)]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hc1 (Int.natCast_nonneg q.den)
  exact ⟨hnum.trans ha,hden.trans hbH⟩

end MetricKMedian.Gaussian

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Compression_RationalOperationHeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                               
section
namespace MetricKMedian.Binary
open Finset

def HasHeight (q : ℚ) (L : ℕ) : Prop := |q.num| ≤ (2:ℤ)^L ∧ (q.den:ℤ) ≤ (2:ℤ)^L

namespace HasHeight
variable {q r : ℚ} {L M : ℕ}

 theorem mono (h : HasHeight q L) (hLM : L≤M) : HasHeight q M :=
  ⟨h.1.trans (pow_le_pow_right₀ (by norm_num) hLM),h.2.trans (pow_le_pow_right₀ (by norm_num) hLM)⟩

 theorem mul (hq : HasHeight q L) (hr : HasHeight r M) : HasHeight (q*r) (L+M) := by
  have hdq : (q.den:ℤ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  have hdr : (r.den:ℤ) ≠ 0 := by exact_mod_cast r.den_ne_zero
  have hh := Gaussian.ratio_num_den_bound (q.num*r.num) ((q.den:ℤ)*r.den) (mul_ne_zero hdq hdr)
    ((2:ℤ)^(L+M)) (by
      rw [abs_mul,pow_add]
      exact mul_le_mul hq.1 hr.1 (abs_nonneg _) (by positivity)) (by
      rw [abs_mul,abs_of_nonneg (Int.natCast_nonneg _),abs_of_nonneg (Int.natCast_nonneg _),pow_add]
      exact mul_le_mul hq.2 hr.2 (by positivity) (by positivity))
  have he : ((q.num*r.num:ℤ):ℚ)/(((q.den:ℤ)*r.den:ℤ):ℚ)=q*r := by
    push_cast
    rw [mul_div_mul_comm,Rat.num_div_den,Rat.num_div_den]
  rwa [he] at hh

end HasHeight
end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Binary_BinaryRationalHeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.Binary
open Polynomial
namespace NatBinary
 theorem length_le_height {n L : ℕ} (h : n ≤ 2^L) : n.bits.length ≤ L+1 := by
  rw [Nat.size_eq_bits_len]
  apply Nat.size_le.mpr
  have hp : 0<2^L := pow_pos (by decide) _
  rw [pow_succ]
  omega
 theorem le_two_pow_length (n : ℕ) : n ≤ 2^n.bits.length := by
  simpa only [Nat.size_eq_bits_len] using (Nat.lt_size_self n).le
end NatBinary

end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Binary_BinaryListIndices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                         
section
namespace MetricKMedian.Binary
open Function Polynomial
namespace ListAlgorithms
variable {α : Type}
def indexStep (x : (ℕ × List ℕ) × α) : ℕ × List ℕ := (x.1.1+1,x.1.1::x.1.2)
 theorem pushIndices (xs : List α) (n : ℕ) (bs : List ℕ) :
    xs.foldl (fun b a => indexStep (b,a)) (n,bs)=
      (n+xs.length,(List.range' n xs.length).reverse++bs) := by
  induction xs generalizing n bs with
  | nil => simp
  | cons a xs ih =>
      change xs.foldl (fun b a => indexStep (b,a)) (n+1,n::bs)=_
      rw [ih]
      simp only [List.length_cons,List.range'_succ,List.reverse_cons,List.append_assoc,List.singleton_append]
      congr 1
      omega

end ListAlgorithms
end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Binary_BinaryListZip
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                     
section
namespace MetricKMedian.Binary
open Function Polynomial
namespace ListZip
variable {α β : Type} (ea : α → List Bool) (eb : β → List Bool) (a0 : α) (b0 : β)
def body (x : (List α × List β) × List (α × β)) : List (α × β) ⊕ ((List α × List β) × List (α × β)) :=
  if x.1.1.isEmpty || x.1.2.isEmpty then .inl x.2.reverse
  else .inr ((x.1.1.tail,x.1.2.tail),(x.1.1.head?.getD a0,x.1.2.head?.getD b0)::x.2)
def result (x : (List α × List β) × List (α × β)) : List (α × β) := x.2.reverse++x.1.1.zip x.1.2
end ListZip
end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Binary_BinaryListSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.Binary
open Function Polynomial
namespace ListFindIdx
variable {α : Type} (ea : α → List Bool) (a0 : α) (p : α → Bool)
def body (x : List α × ℕ) : ℕ ⊕ (List α × ℕ) :=
  if x.1.isEmpty || p (x.1.head?.getD a0) then .inl x.2 else .inr (x.1.tail,x.2+1)
def result (x : List α × ℕ) : ℕ := x.2+x.1.findIdx p
end ListFindIdx
end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Binary_BinaryAutomatic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                       
section
namespace MetricKMedian.Binary.Automatic
open Function
class Coding (α : Type) where
  encode : α → List Bool
abbrev enc {α : Type} [Coding α] : α → List Bool := Coding.encode
instance instCodingNat : Coding ℕ := ⟨Nat.bits⟩
instance instCodingUnit : Coding Unit := ⟨fun _ => []⟩
end MetricKMedian.Binary.Automatic
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Binary_BinaryRationalFold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.Binary
open Function Polynomial
namespace ListAlgorithms
 theorem foldAdd (as : List ℚ) (b : ℚ) : as.foldl (·+·) b=b+as.sum := by
  induction as generalizing b with
  | nil => simp
  | cons a as ih => simp only [List.foldl_cons,ih,List.sum_cons,add_assoc]
 theorem foldMul (as : List ℚ) (b : ℚ) : as.foldl (·*·) b=b*as.prod := by
  induction as generalizing b with
  | nil => simp
  | cons a as ih => simp only [List.foldl_cons,ih,List.prod_cons,mul_assoc]
end ListAlgorithms
end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_RoundingListOperations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                              
section
namespace MetricKMedian.RoundingList
open Binary Binary.Automatic Finset
abbrev Row := List ℚ

def frac (q : ℚ) : Bool := decide (0<q) && decide (q<1)
def indices (p : Row) : List ℕ := List.range p.length
def fractional (p : Row) : List ℕ := (indices p).filter (fun i => frac (p[i]?.getD 0))
def first (p : Row) : ℕ := (indices p).findIdx (fun i => frac (p[i]?.getD 0))
def active (p : Row) : Bool := decide (1<(fractional p).length)

end MetricKMedian.RoundingList
end

end OAI
end


