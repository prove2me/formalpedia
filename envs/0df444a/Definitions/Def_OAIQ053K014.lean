-- Prove2me | Definitions.Def_OAIQ053K014
-- name    : OAIQ053K014
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T05:55:03.709994+00:00
-- url     : https://prove2.me/theorems/0987e03c-d602-4aef-9d5b-14310ce8705e
-- title:
--   Definitions bundle OAIQ053K014 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 90 declarations of OpenAI's Lean: 39 definitions, 5 instances and 46 theorems. The definitions and types are `OAI.MetricKMedian.Binary.AdditionLoop.result`, `OAI.MetricKMedian.Binary.Automatic.Poly`, `OAI.MetricKMedian.Binary.Automatic.Poly.program`, `OAI.MetricKMedian.Binary.DivisionLoop.edqr`, `OAI.MetricKMedian.Binary.DivisionLoop.enc`, `OAI.MetricKMedian.Binary.DivisionLoop.eqr`, `OAI.MetricKMedian.Binary.GCDLoop.enc`, `OAI.MetricKMedian.Binary.ListFindIdx.enc`, `OAI.MetricKMedian.Binary.ListFold.enc`, `OAI.MetricKMedian.Binary.ListReverse.enc`, `OAI.MetricKMedian.Binary.ListSplit.enc`, `OAI.MetricKMedian.Binary.ListSplit.out`, `OAI.MetricKMedian.Binary.ListZip.enc`, `OAI.MetricKMedian.Binary.MultiplicationLoop.enc`, `OAI.MetricKMedian.Binary.MultiplicationLoop.ey`, `OAI.MetricKMedian.Binary.PolyProgram.boolEq`, `OAI.MetricKMedian.Binary.PolyProgram.boolNot`, `OAI.MetricKMedian.Binary.PolyProgram.boolOr`, `OAI.MetricKMedian.Binary.PolyProgram.boolXor`, `OAI.MetricKMedian.Binary.PolyProgram.dropFalse`, `OAI.MetricKMedian.Binary.PolyProgram.intAbs`, `OAI.MetricKMedian.Binary.PolyProgram.natHalf`, `OAI.MetricKMedian.Binary.PolyProgram.ratDen`, `OAI.MetricKMedian.Binary.PolyProgram.recode`, `OAI.MetricKMedian.Binary.PolyProgram.signedParts`, `OAI.MetricKMedian.Binary.PolyProgram.snd`, `OAI.MetricKMedian.Binary.PolyProgram.tail`, `OAI.MetricKMedian.Binary.Ratio.encode`, `OAI.MetricKMedian.Binary.Signed.encode`, `OAI.MetricKMedian.Binary.SubtractionLoop.body`, `OAI.MetricKMedian.Binary.SubtractionLoop.finish`, `OAI.MetricKMedian.Binary.SubtractionLoop.next`, `OAI.MetricKMedian.Binary.SubtractionLoop.result`, `OAI.MetricKMedian.Binary.Word.add`, `OAI.MetricKMedian.Binary.Word.sub`, `OAI.MetricKMedian.Binary.WordTransducer.dropFalse`, `OAI.MetricKMedian.Binary.WordTransducer.tail`, `OAI.MetricKMedian.Binary.encodeList`, `OAI.MetricKMedian.SparseGraph.ListOperation.Table`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedian_Binary_BinaryAddition`, `KMedian_Binary_BinaryAutomatic`, `KMedian_Binary_BinaryDivision`, `KMedian_Binary_BinaryGCD`, `KMedian_Binary_BinaryInteger`, `KMedian_Binary_BinaryListFold`, `KMedian_Binary_BinaryListIndex`, `KMedian_Binary_BinaryListSelection`, `KMedian_Binary_BinaryListZip`, `KMedian_Binary_BinaryLists`, `KMedian_Binary_BinaryMultiplication`, `KMedian_Binary_BinaryNatural`, `KMedian_Binary_BinaryRational`, `KMedian_Binary_BinaryRationalHeight`, `KMedian_Binary_BinarySubtraction`, `KMedian_Binary_BinaryWords`, `KMedian_Binary_BooleanEncoding`, `KMedian_Binary_BooleanFinite`, `KMedian_Binary_BooleanListPrimitives`, `KMedian_Binary_BooleanRecode`, `KMedian_Geometry_GraphListOperations`.
--
--   **Imports.** It imports the bundles `OAIQ053K000` and `OAIQ053K001` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ053K028`, `OAIQ053K029`, `OAIQ053K030`, `OAIQ053K032`, `OAIQ053K033` and `OAIQ053K034`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ053K000
import Definitions.Def_OAIQ053K001

section
-- module Solutions.OAIQ053_KM.KMedian_Binary_BooleanEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                       
section
namespace MetricKMedian.Binary
open Turing Function Polynomial

namespace PolyProgram

 noncomputable def snd {α β : Type} (ea : α → List Bool) (eb : β → List Bool) :
    PolyProgram (encodePair ea eb) eb Prod.snd :=
  (WordTransducer.projecting true).program.of_word (fun _ => by
    simpa only [encodePair,ite_true,WordTransducer.projecting] using WordTransducer.projecting_pair true _ _)

end PolyProgram
end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Binary_BooleanListPrimitives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section
namespace MetricKMedian.Binary
open Turing Function Polynomial

namespace WordTransducer

def tail : Transducer where
  Q := Bool
  initial := true
  next q b := (false,if q then [] else [b])
  finish _ := []

 theorem tail_run_false (xs : List Bool) : tail.run false xs=xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih => change b::tail.run false xs=b::xs; rw [ih]

 theorem tail_run (xs : List Bool) : tail.run true xs=xs.tail := by
  cases xs with
  | nil => rfl
  | cons b xs => exact tail_run_false xs

end WordTransducer

namespace PolyProgram
variable {α β : Type} {ea : α → List Bool} {eb : β → List Bool}

noncomputable def tail : PolyProgram id id List.tail :=
  WordTransducer.tail.program.of_word (fun xs => by
    simpa only [WordTransducer.tail,id_eq] using WordTransducer.tail_run xs)

end PolyProgram
end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Binary_BinaryWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                   
section
namespace MetricKMedian.Binary
open Function Polynomial

namespace WordTransducer

def dropFalse : Transducer where
  Q := Bool
  initial := false
  next q b := (q || b,if q || b then [b] else [])
  finish _ := []

 theorem dropFalse_true (xs : List Bool) : dropFalse.run true xs=xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih => change b::dropFalse.run true xs=b::xs; rw [ih]

 theorem dropFalse_run (xs : List Bool) : dropFalse.run false xs=xs.dropWhile Bool.not := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
      cases b
      · exact ih
      · exact congrArg (List.cons true) (dropFalse_true xs)

end WordTransducer

namespace PolyProgram

noncomputable def dropFalse : PolyProgram id id (List.dropWhile Bool.not) :=
  WordTransducer.dropFalse.program.of_word (fun xs => by
    simpa only [WordTransducer.dropFalse,id_eq] using WordTransducer.dropFalse_run xs)

end PolyProgram
end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Binary_BooleanFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                     
section
namespace MetricKMedian.Binary
open Function Finset

namespace PolyProgram

noncomputable def boolNot : PolyProgram encodeBool encodeBool Bool.not :=
  boolFunction _ _ _ encodeBool_injective
noncomputable def boolOr : PolyProgram (encodePair encodeBool encodeBool) encodeBool (fun x => x.1 || x.2) :=
  boolFunction _ _ _ (encodePair_injective encodeBool_injective encodeBool_injective)

end PolyProgram
end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Binary_BooleanRecode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                     
section
namespace MetricKMedian.Binary.PolyProgram
variable {α β α' β' : Type} {ea : α → List Bool} {eb : β → List Bool}
variable {ea' : α' → List Bool} {eb' : β' → List Bool} {f : α → β} {f' : α' → β'}

def recode (P : PolyProgram ea eb f) (i : α' → α)
    (hi : ∀ a, ea (i a)=ea' a) (ho : ∀ a, eb (f (i a))=eb' (f' a)) :
    PolyProgram ea' eb' f' where
  machine := P.machine
  time := P.time
  outputs a := by
    have h := P.outputs (i a)
    rwa [hi,ho] at h

end MetricKMedian.Binary.PolyProgram
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Binary_BinaryAddition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                      
section
namespace MetricKMedian.Binary
open Function Polynomial

namespace Word

 theorem fullAdder (a b c : Bool) :
    (sumBit a b c).toNat+2*(carryBit a b c).toNat=a.toNat+b.toNat+c.toNat := by
  cases a <;> cases b <;> cases c <;> decide

 def add : List Bool → List Bool → Bool → List Bool
  | [],[],c => if c then [true] else []
  | a::xs,ys,c => sumBit a (ys.head?.getD false) c :: add xs ys.tail (carryBit a (ys.head?.getD false) c)
  | [],b::ys,c => sumBit false b c :: add [] ys (carryBit false b c)
termination_by xs ys _ => xs.length+ys.length

 theorem add_step (xs ys : List Bool) (c : Bool) (h : (xs.isEmpty && ys.isEmpty)=false) :
    add xs ys c=sumBit (xs.head?.getD false) (ys.head?.getD false) c ::
      add xs.tail ys.tail (carryBit (xs.head?.getD false) (ys.head?.getD false) c) := by
  cases xs <;> cases ys <;> simp_all only [List.isEmpty_nil,List.isEmpty_cons,Bool.true_and,Bool.false_and,
    Bool.true_eq_false,List.head?_cons,List.head?_nil,Option.getD_some,Option.getD_none,
    List.tail_nil,List.tail_cons,add]

 theorem value_add (xs ys : List Bool) (c : Bool) : value (add xs ys c)=value xs+value ys+c.toNat := by
  induction xs generalizing ys c with
  | nil =>
      induction ys generalizing c with
      | nil => cases c <;> simp [add,value]
      | cons b ys ih =>
          rw [add,value_cons,ih]
          have h := fullAdder false b c
          simp only [value_nil,value_cons,Bool.toNat_false] at *
          omega
  | cons a xs ih =>
      rw [add,value_cons,ih]
      have h := fullAdder a (ys.head?.getD false) c
      cases ys with
      | nil => simp only [List.head?_nil,Option.getD_none,List.tail_nil,value_nil,value_cons,Bool.toNat_false] at *; omega
      | cons b ys => simp only [List.head?_cons,Option.getD_some,List.tail_cons,value_cons] at *; omega

end Word

namespace AdditionLoop
 def result (s : S) : List Bool := s.2.2.2.reverse++Word.add s.1 s.2.1 s.2.2.1

 theorem shorten (s : S) (h : empty s=false) :
    s.1.tail.length+s.2.1.tail.length < s.1.length+s.2.1.length := by
  rcases s with ⟨xs,ys,c,acc⟩
  cases xs <;> cases ys <;> simp_all [empty]
  omega

 theorem next_result (s : S) (h : empty s=false) : result (next s)=result s := by
  simp only [result]
  rw [Word.add_step s.1 s.2.1 s.2.2.1 h]
  simp only [next,List.reverse_cons,List.append_assoc,List.singleton_append]

 theorem next_size (s : S) (h : empty s=false) : (enc (next s)).length≤(enc s).length := by
  have hs := shorten s h
  simp only [enc_length,next,List.length_cons]
  omega

 theorem run (L : ℕ) : ∀ (s : S) (S : ℕ), s.1.length+s.2.1.length=L → (enc s).length≤S →
    ∃ n≤L+1, BoundedRun enc body S n s (result s) := by
  induction L using Nat.strong_induction_on with
  | h L ih =>
      intro s S hL hs
      cases he : empty s with
      | true =>
          refine ⟨1,by omega,BoundedRun.stop hs ?_⟩
          rcases s with ⟨xs,ys,c,acc⟩
          have hz : xs=[] ∧ ys=[] := by simpa only [empty,Bool.and_eq_true,List.isEmpty_iff] using he
          rcases hz with ⟨rfl,rfl⟩
          cases c <;> simp [body,empty,finish,result,Word.add]
      | false =>
          have hl : (next s).1.length+(next s).2.1.length<L := by simpa only [next,hL] using shorten s he
          obtain ⟨n,hn,hr⟩ := ih _ hl (next s) S rfl ((next_size s he).trans hs)
          refine ⟨n+1,by omega,?_⟩
          rw [next_result s he] at hr
          exact BoundedRun.step hs (by simp only [body,he,Bool.false_eq_true,ite_false]) hr

end AdditionLoop

end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Binary_BinaryLists
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                   
section
namespace MetricKMedian.Binary
open Function Polynomial

 def encodeList {α : Type} (ea : α → List Bool) : List α → List Bool
  | [] => []
  | a::as => quote (ea a)++encodeList ea as

namespace EncodedList
variable {α : Type} (ea : α → List Bool)
 theorem nil : encodeList ea []=[] := rfl
 theorem cons_length (a : α) (as : List α) : (encodeList ea (a::as)).length=2*(ea a).length+1+(encodeList ea as).length := by
  simp only [encodeList,List.length_append,quote_length]
 theorem length_le (as : List α) : as.length ≤ (encodeList ea as).length := by
  induction as with
  | nil => rfl
  | cons a as ih => simp only [cons_length,List.length_cons]; omega
 theorem isEmpty (as : List α) : (encodeList ea as).isEmpty=as.isEmpty := by
  cases as with
  | nil => rfl
  | cons a as =>
      have h := cons_length ea a as
      apply List.isEmpty_eq_false_iff.mpr
      intro hz
      simp only [hz,List.length_nil] at h
      omega
 theorem append (as bs : List α) : encodeList ea (as++bs)=encodeList ea as++encodeList ea bs := by
  induction as with
  | nil => rfl
  | cons a as ih => simp only [List.cons_append,encodeList,ih,List.append_assoc]
 theorem reverse_length (as : List α) : (encodeList ea as.reverse).length=(encodeList ea as).length := by
  induction as with
  | nil => rfl
  | cons a as ih =>
      simp only [List.reverse_cons,append,List.length_append,cons_length,nil,List.length_nil,ih]
      omega
 theorem member_length (as : List α) (a : α) (h : a∈as) : (ea a).length ≤ (encodeList ea as).length := by
  induction as with
  | nil => simp at h
  | cons b as ih =>
      simp only [List.mem_cons] at h
      rcases h with rfl|h
      · rw [cons_length]; omega
      · have hh := ih h
        rw [cons_length]; omega
 theorem length_bound (as : List α) (L : ℕ) (h : ∀ a∈as, (ea a).length ≤ L) :
    (encodeList ea as).length ≤ as.length*(2*L+1) := by
  induction as with
  | nil => simp only [nil,List.length_nil,zero_mul,le_refl]
  | cons a as ih =>
      have ha := h a (by simp)
      have hh := ih (fun a ha => h a (by simp [ha]))
      rw [cons_length,List.length_cons]
      nlinarith
end EncodedList

namespace ListReverse
variable {α : Type} (ea : α → List Bool) (a0 : α)
abbrev enc : List α × List α → List Bool := encodePair (encodeList ea) (encodeList ea)

 theorem run (as bs : List α) (S : ℕ) (h : 2*(encodeList ea as).length+1+(encodeList ea bs).length ≤ S) :
    BoundedRun (enc ea) (body a0) S (as.length+1) (as,bs) (as.reverse++bs) := by
  induction as generalizing bs with
  | nil =>
      apply BoundedRun.stop
      · simpa only [enc,encodePair_length] using h
      · rfl
  | cons a as ih =>
      have hs : 2*(encodeList ea as).length+1+(encodeList ea (a::bs)).length ≤ S := by
        simp only [EncodedList.cons_length] at h ⊢
        omega
      have hr := BoundedRun.step (ea:=enc ea) (f:=body a0)
        (a:=(a::as,bs)) (a':=(as,a::bs))
        (by simpa only [enc,encodePair_length] using h) rfl (ih (a::bs) hs)
      simpa only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append] using hr

end ListReverse

end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Binary_BinaryListFold
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
abbrev enc : List α × β → List Bool := encodePair (encodeList ea) eb

 theorem run (as : List α) (b : β) (S : ℕ)
    (h : ∀ pre suf, as=pre++suf → (enc ea eb (suf,pre.foldl (fun b a => op (b,a)) b)).length ≤ S) :
    BoundedRun (enc ea eb) (body a0 op) S (as.length+1) (as,b) (result op (as,b)) := by
  induction as generalizing b with
  | nil =>
      apply BoundedRun.stop
      · exact h [] [] rfl
      · rfl
  | cons a as ih =>
      have hs : ∀ pre suf, as=pre++suf →
          (enc ea eb (suf,pre.foldl (fun b a => op (b,a)) (op (b,a)))).length ≤ S := by
        intro pre suf he
        exact h (a::pre) suf (by simp only [List.cons_append,he])
      exact BoundedRun.step (h [] (a::as) rfl) rfl (ih (op (b,a)) hs)

 theorem linear_height (C : ℕ)
    (hop : ∀ b a, (eb (op (b,a))).length ≤ (eb b).length+C*(2*(ea a).length+1))
    (as : List α) (b : β) :
    (eb (as.foldl (fun b a => op (b,a)) b)).length ≤ (eb b).length+C*(encodeList ea as).length := by
  induction as generalizing b with
  | nil => simp only [List.foldl_nil,EncodedList.nil,List.length_nil,mul_zero,add_zero,le_refl]
  | cons a as ih =>
      have hh := ih (op (b,a))
      have ha := hop b a
      simp only [List.foldl_cons,EncodedList.cons_length]
      nlinarith

end ListFold

end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Binary_BinaryNatural
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                     
section
namespace MetricKMedian.Binary
open Function Polynomial

namespace PolyProgram

noncomputable def natHalf : PolyProgram Nat.bits Nat.bits Nat.div2 :=
  tail.recode Nat.bits (fun _ => rfl) (fun n => (Nat.div2_bits_eq_tail n).symm)

end PolyProgram
end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Binary_BinarySubtraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                         
section
namespace MetricKMedian.Binary
open Function Polynomial

namespace Word
 theorem fullSubtract (a b c : Bool) :
    a.toNat+2*(borrowBit a b c).toNat=b.toNat+c.toNat+(sumBit a b c).toNat := by
  cases a <;> cases b <;> cases c <;> decide

 def sub : List Bool → List Bool → Bool → Bool × List Bool
  | [],[],c => (c,[])
  | a::xs,ys,c =>
      let t := sub xs ys.tail (borrowBit a (ys.head?.getD false) c)
      (t.1,sumBit a (ys.head?.getD false) c::t.2)
  | [],b::ys,c =>
      let t := sub [] ys (borrowBit false b c)
      (t.1,sumBit false b c::t.2)
termination_by xs ys _ => xs.length+ys.length

 theorem sub_step (xs ys : List Bool) (c : Bool) (h : (xs.isEmpty && ys.isEmpty)=false) :
    sub xs ys c=
      let t := sub xs.tail ys.tail (borrowBit (xs.head?.getD false) (ys.head?.getD false) c)
      (t.1,sumBit (xs.head?.getD false) (ys.head?.getD false) c::t.2) := by
  cases xs <;> cases ys <;> simp_all [sub]

 theorem value_sub (xs ys : List Bool) (c : Bool) :
    value (sub xs ys c).2+value ys+c.toNat=
      value xs+2^(sub xs ys c).2.length*(sub xs ys c).1.toNat := by
  induction xs generalizing ys c with
  | nil =>
      induction ys generalizing c with
      | nil => simp [sub,value]
      | cons b ys ih =>
          rw [sub]
          simp only [value_cons,value_nil,List.length_cons,pow_succ]
          have h := ih (borrowBit false b c)
          have hb := fullSubtract false b c
          simp only [value_nil,Bool.toNat_false] at h hb
          nlinarith
  | cons a xs ih =>
      rw [sub]
      simp only [value_cons,List.length_cons,pow_succ]
      have h := ih ys.tail (borrowBit a (ys.head?.getD false) c)
      have hb := fullSubtract a (ys.head?.getD false) c
      cases ys with
      | nil =>
          simp only [value_nil,List.head?_nil,Option.getD_none,List.tail_nil,Bool.toNat_false] at *
          nlinarith
      | cons b ys =>
          simp only [value_cons,List.head?_cons,Option.getD_some,List.tail_cons] at *
          nlinarith

 theorem sub_borrow (xs ys : List Bool) : (sub xs ys false).1=decide (value xs<value ys) := by
  have h := value_sub xs ys false
  have hl := value_lt (sub xs ys false).2
  cases he : (sub xs ys false).1
  · simp only [he,Bool.toNat_false,Nat.mul_zero,Nat.add_zero] at h
    have hn : ¬ value xs<value ys := by omega
    simp only [decide_eq_false hn]
  · simp only [he,Bool.toNat_true,Bool.toNat_false,Nat.mul_one,Nat.add_zero] at h
    have hn : value xs<value ys := by omega
    simp only [decide_eq_true hn]

 theorem sub_clamp (xs ys : List Bool) :
    value (if (sub xs ys false).1 then [] else (sub xs ys false).2)=value xs-value ys := by
  have h := value_sub xs ys false
  cases he : (sub xs ys false).1
  · simp only [he,Bool.toNat_false,Nat.mul_zero,Nat.add_zero] at h
    simp only [Bool.false_eq_true,ite_false]
    omega
  · have hl := sub_borrow xs ys
    rw [he] at hl
    have hn : value xs<value ys := of_decide_eq_true hl.symm
    simp only [ite_true,value_nil]
    omega
end Word

namespace SubtractionLoop
open AdditionLoop (S ec ey enc enc_length)
 def next (s : S) : S :=
  (s.1.tail,(s.2.1.tail,(Word.borrowBit (s.1.head?.getD false) (s.2.1.head?.getD false) s.2.2.1,
    Word.sumBit (s.1.head?.getD false) (s.2.1.head?.getD false) s.2.2.1 :: s.2.2.2)))
 def finish (s : S) : Bool × List Bool := (s.2.2.1,s.2.2.2.reverse)
 def body (s : S) : (Bool × List Bool) ⊕ S := if AdditionLoop.empty s then .inl (finish s) else .inr (next s)
 def result (s : S) : Bool × List Bool :=
  let t := Word.sub s.1 s.2.1 s.2.2.1
  (t.1,s.2.2.2.reverse++t.2)

 theorem next_result (s : S) (h : AdditionLoop.empty s=false) : result (next s)=result s := by
  simp only [result]
  rw [Word.sub_step s.1 s.2.1 s.2.2.1 h]
  simp only [next,List.reverse_cons,List.append_assoc,List.singleton_append]

 theorem next_size (s : S) (h : AdditionLoop.empty s=false) : (enc (next s)).length≤(enc s).length := by
  have hs := AdditionLoop.shorten s h
  simp only [enc_length,next,List.length_cons]
  omega

 theorem run (L : ℕ) : ∀ (s : S) (S : ℕ), s.1.length+s.2.1.length=L → (enc s).length≤S →
    ∃ n≤L+1, BoundedRun enc body S n s (result s) := by
  induction L using Nat.strong_induction_on with
  | h L ih =>
      intro s S hL hs
      cases he : AdditionLoop.empty s with
      | true =>
          refine ⟨1,by omega,BoundedRun.stop hs ?_⟩
          rcases s with ⟨xs,ys,c,acc⟩
          have hz : xs=[] ∧ ys=[] := by simpa only [AdditionLoop.empty,Bool.and_eq_true,List.isEmpty_iff] using he
          rcases hz with ⟨rfl,rfl⟩
          simp [body,AdditionLoop.empty,finish,result,Word.sub]
      | false =>
          have hl : (next s).1.length+(next s).2.1.length<L := by simpa only [next,hL] using AdditionLoop.shorten s he
          obtain ⟨n,hn,hr⟩ := ih _ hl (next s) S rfl ((next_size s he).trans hs)
          refine ⟨n+1,by omega,?_⟩
          rw [next_result s he] at hr
          exact BoundedRun.step hs (by simp only [body,he,Bool.false_eq_true,ite_false]) hr

end SubtractionLoop

end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Binary_BinaryListIndex
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
abbrev enc : List α × (ℕ × List α) → List Bool := encodePair (encodeList ea) (encodePair Nat.bits (encodeList ea))
abbrev out : List α × List α → List Bool := encodePair (encodeList ea) (encodeList ea)

 theorem run (as bs : List α) (n S : ℕ) (hsize : (enc ea (as,(n,bs))).length ≤ S) :
    ∃ t ≤ as.length+1, BoundedRun (enc ea) (body a0) S t (as,(n,bs)) (result (as,(n,bs))) := by
  induction as generalizing n bs with
  | nil =>
      refine ⟨1,by simp,BoundedRun.stop hsize ?_⟩
      simp only [body,result,List.isEmpty_nil,Bool.true_or,List.take_nil,List.drop_nil,List.append_nil]
      rfl
  | cons a as ih =>
      cases n with
      | zero =>
          refine ⟨1,by simp,BoundedRun.stop hsize ?_⟩
          simp only [body,result,List.isEmpty_cons,decide_true,Bool.false_or,List.take_zero,List.drop_zero,List.append_nil]
          rfl
      | succ n =>
          have hn := NatBinary.length_mono (Nat.le_succ n)
          change n.bits.length ≤ (n+1).bits.length at hn
          have hs : (enc ea (as,(n,a::bs))).length ≤ S := by
            simp only [enc,encodePair_length,EncodedList.cons_length] at hsize ⊢
            omega
          obtain ⟨t,ht,hr⟩ := ih (a::bs) n hs
          refine ⟨t+1,by simpa only [List.length_cons] using Nat.succ_le_succ ht,?_⟩
          have hb : body a0 (a::as,(n+1,bs))=.inr (as,(n,a::bs)) := by simp [body]
          have he : result (as,(n,a::bs))=result (a::as,(n+1,bs)) := by
            simp only [result,List.reverse_cons,List.take_succ_cons,List.drop_succ_cons,List.append_assoc,List.singleton_append]
          rw [← he]
          exact BoundedRun.step hsize hb hr

end ListSplit

end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Binary_BinaryDivision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                      
section
namespace MetricKMedian.Binary
open Function Polynomial

namespace DivisionLoop
abbrev eqr : ℕ × ℕ → List Bool := encodePair Nat.bits Nat.bits
abbrev edqr : ℕ × (ℕ × ℕ) → List Bool := encodePair Nat.bits eqr
abbrev enc : S → List Bool := encodePair id edqr

 theorem enc_length (s : S) :
    (enc s).length=2*s.1.length+2*s.2.1.bits.length+2*s.2.2.1.bits.length+s.2.2.2.bits.length+3 := by
  simp only [enc,edqr,eqr,encodePair_length,id_eq]
  omega

 theorem total_le_length (s : S) : potential s+s.2.1.bits.length≤(enc s).length := by
  simp only [potential,enc_length]
  omega

 theorem length_le_total (s : S) : (enc s).length≤3*(potential s+s.2.1.bits.length)+3 := by
  simp only [potential,enc_length]
  omega

 theorem run (xs : List Bool) (d q r S : ℕ) (hs : 3*(potential (xs,d,q,r)+d.bits.length)+3≤S) :
    BoundedRun enc body S (xs.length+1) (xs,d,q,r) (result (xs,d,q,r)) := by
  induction xs generalizing q r with
  | nil =>
      exact BoundedRun.stop ((length_le_total ([],d,q,r)).trans hs) rfl
  | cons b xs ih =>
      let s : DivisionLoop.S := (b::xs,d,q,r)
      have hp := next_potential s rfl
      change 3*(potential s+d.bits.length)+3≤S at hs
      have hnext : 3*(potential (next s)+d.bits.length)+3≤S := by omega
      have hr := ih (qstep b d q r) (rstep b d r) hnext
      have hh : result (xs,d,qstep b d q r,rstep b d r)=result s := rfl
      rw [hh] at hr
      exact BoundedRun.step ((length_le_total s).trans hs) rfl hr

end DivisionLoop

end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Binary_BinaryGCD
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                 
section
namespace MetricKMedian.Binary
open Function Polynomial

namespace GCDLoop
abbrev enc : S → List Bool := encodePair Nat.bits Nat.bits

 theorem enc_length (s : S) : (enc s).length=2*s.1.bits.length+1+s.2.bits.length := by
  exact encodePair_length _ _ _
 theorem length_le_potential (s : S) : (enc s).length ≤ 2*potential s+1 := by
  simp only [enc_length,potential]; omega
 theorem potential_le_length (s : S) : potential s ≤ (enc s).length := by
  simp only [enc_length,potential]; omega

 theorem run_ordered (L : ℕ) : ∀ (s : S) (S : ℕ), potential s=L →
    s.2 ≤ s.1 → 2*L+1 ≤ S → ∃ n ≤ L+1, BoundedRun enc body S n s (result s) := by
  induction L using Nat.strong_induction_on with
  | h L ih =>
      intro s S hL ho hs
      have hsize : (enc s).length ≤ S := (length_le_potential s).trans (by omega)
      by_cases hz : s.2=0
      · refine ⟨1,by omega,BoundedRun.stop hsize ?_⟩
        simp only [body,hz,ite_true,result,Nat.gcd_zero_right]
      · have hpot : potential (next s) < L := by simpa only [hL] using next_potential_lt s ho hz
        have horder : (next s).2 ≤ (next s).1 := (Nat.mod_lt s.1 (Nat.pos_of_ne_zero hz)).le
        obtain ⟨n,hn,hr⟩ := ih _ hpot (next s) S rfl horder (by omega)
        refine ⟨n+1,by omega,?_⟩
        rw [next_result] at hr
        exact BoundedRun.step hsize (by simp only [body,hz,ite_false]) hr

 theorem run (s : S) (S : ℕ) (hs : 2*potential s+1 ≤ S) :
    ∃ n ≤ potential s+2, BoundedRun enc body S n s (result s) := by
  by_cases ho : s.2 ≤ s.1
  · obtain ⟨n,hn,hr⟩ := run_ordered (potential s) s S rfl ho hs
    exact ⟨n,by omega,hr⟩
  · have hb : s.2 ≠ 0 := by omega
    have hn := next_potential s
    have horder : (next s).2 ≤ (next s).1 := (Nat.mod_lt s.1 (Nat.pos_of_ne_zero hb)).le
    obtain ⟨n,hbound,hr⟩ := run_ordered (potential (next s)) (next s) S rfl horder (by omega)
    refine ⟨n+1,by omega,?_⟩
    rw [next_result] at hr
    exact BoundedRun.step ((length_le_potential s).trans hs)
      (by simp only [body,hb,ite_false]) hr

end GCDLoop

end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Binary_BinaryMultiplication
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.Binary
open Function Polynomial

namespace MultiplicationLoop
abbrev ey : ℕ × ℕ → List Bool := encodePair Nat.bits Nat.bits
abbrev enc : S → List Bool := encodePair Nat.bits ey

 theorem enc_length (s : S) : (enc s).length=2*s.1.bits.length+2*s.2.1.bits.length+s.2.2.bits.length+2 := by
  simp only [enc,ey,encodePair_length]
  omega

 theorem potential_le_length (s : S) : potential s≤(enc s).length := by
  simp only [potential,enc_length]
  omega

 theorem length_le_potential (s : S) : (enc s).length≤3*potential s+2 := by
  simp only [potential,enc_length]
  omega

 theorem run (L : ℕ) : ∀ (s : S) (S : ℕ), s.1.bits.length=L → 3*potential s+2≤S →
    ∃ n≤L+1, BoundedRun enc body S n s (result s) := by
  induction L using Nat.strong_induction_on with
  | h L ih =>
      intro s S hL hs
      have hsize := (length_le_potential s).trans hs
      by_cases hz : s.1=0
      · refine ⟨1,by omega,BoundedRun.stop hsize ?_⟩
        simp only [body,hz,ite_true,result,zero_mul,zero_add]
      · have hl : (next s).1.bits.length<L := by simpa only [next,hL] using NatBinary.half_lt_length hz
        have hb : 3*potential (next s)+2≤S := by have := next_potential s hz; omega
        obtain ⟨n,hn,hr⟩ := ih _ hl (next s) S rfl hb
        refine ⟨n+1,by omega,?_⟩
        rw [next_result] at hr
        exact BoundedRun.step hsize (by simp only [body,hz,ite_false]) hr

end MultiplicationLoop

end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Binary_BinaryInteger
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                     
section
namespace MetricKMedian.Binary
open Function Polynomial

namespace Signed
 def encode (z : ℤ) : List Bool := encodePair encodeBool Nat.bits (parts z)

end Signed

namespace PolyProgram
abbrev signedParts : Bool × ℕ → List Bool := encodePair encodeBool Nat.bits

noncomputable def intAbs : PolyProgram Signed.encode Nat.bits Int.natAbs :=
  (snd encodeBool Nat.bits).recode Signed.parts (fun _ => rfl) (fun _ => rfl)

noncomputable def boolXor : PolyProgram (encodePair encodeBool encodeBool) encodeBool (fun x => xor x.1 x.2) :=
  boolFunction _ _ _ (encodePair_injective encodeBool_injective encodeBool_injective)
noncomputable def boolEq : PolyProgram (encodePair encodeBool encodeBool) encodeBool (fun x => decide (x.1=x.2)) :=
  boolFunction _ _ _ (encodePair_injective encodeBool_injective encodeBool_injective)

end PolyProgram
end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Binary_BinaryRational
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                      
section
namespace MetricKMedian.Binary
open Function Polynomial

namespace Ratio
 def encode (q : ℚ) : List Bool := encodePair Signed.encode Nat.bits (parts q)
end Ratio

namespace PolyProgram
noncomputable def ratDen : PolyProgram Ratio.encode Nat.bits Rat.den :=
  (snd Signed.encode Nat.bits).recode Ratio.parts (fun _ => rfl) (fun _ => rfl)
end PolyProgram
end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Binary_BinaryRationalHeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.Binary
open Polynomial

namespace Signed
 theorem encode_length (z : ℤ) : (encode z).length=3+z.natAbs.bits.length := by
  simp only [encode,parts,encodePair_length,encodeBool,List.length_singleton]

end Signed
end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Binary_BinaryListZip
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
abbrev enc : (List α × List β) × List (α × β) → List Bool :=
  encodePair (encodePair (encodeList ea) (encodeList eb)) (encodeList (encodePair ea eb))
end ListZip
end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Binary_BinaryListSelection
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
abbrev enc : List α × ℕ → List Bool := encodePair (encodeList ea) Nat.bits
end ListFindIdx
end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Binary_BinaryAutomatic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                       
section
namespace MetricKMedian.Binary.Automatic
open PolyProgram Function
instance instCodingInt : Coding ℤ := ⟨Signed.encode⟩
instance instCodingRat : Coding ℚ := ⟨Ratio.encode⟩
instance instCodingBool : Coding Bool := ⟨encodeBool⟩
instance instCodingProd {α β : Type} [Coding α] [Coding β] : Coding (α × β) := ⟨encodePair enc enc⟩
instance instCodingList {α : Type} [Coding α] : Coding (List α) := ⟨encodeList enc⟩

@[fun_prop] def Poly {α β : Type} [Coding α] [Coding β] (f : α → β) : Prop :=
  Nonempty (PolyProgram enc enc f)

namespace Poly
variable {α β γ : Type} [Coding α] [Coding β] [Coding γ]
noncomputable def program {f : α → β} (h : Poly f) : PolyProgram enc enc f := Classical.choice h

theorem of_program {f : α → β} (p : PolyProgram enc enc f) : Poly f := ⟨p⟩

end Poly
end MetricKMedian.Binary.Automatic
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Geometry_GraphListOperations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.SparseGraph.ListOperation
open Binary Binary.Automatic Binary.Automatic.Poly
abbrev Table := List Row
end MetricKMedian.SparseGraph.ListOperation
end

end OAI
end


