-- Prove2me | Definitions.Def_OAIQ035K014
-- name    : OAIQ035K014
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T07:54:47.834426+00:00
-- url     : https://prove2.me/theorems/b5843151-d6c0-4ff8-92f5-8bdb4a4835d4
-- title:
--   Definitions bundle OAIQ035K014 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 104 declarations of OpenAI's Lean: 52 definitions, 4 instances and 48 theorems. The definitions and types are `OAI.MetricKMedian.Binary.AdditionLoop.result`, `OAI.MetricKMedian.Binary.Automatic.Poly`, `OAI.MetricKMedian.Binary.Automatic.Poly.program`, `OAI.MetricKMedian.Binary.DivisionLoop.edqr`, `OAI.MetricKMedian.Binary.DivisionLoop.enc`, `OAI.MetricKMedian.Binary.DivisionLoop.eqr`, `OAI.MetricKMedian.Binary.GCDLoop.enc`, `OAI.MetricKMedian.Binary.ListFold.enc`, `OAI.MetricKMedian.Binary.ListReverse.enc`, `OAI.MetricKMedian.Binary.MultiplicationLoop.enc`, `OAI.MetricKMedian.Binary.MultiplicationLoop.ey`, `OAI.MetricKMedian.Binary.PolyProgram.boolEq`, `OAI.MetricKMedian.Binary.PolyProgram.boolNot`, `OAI.MetricKMedian.Binary.PolyProgram.boolXor`, `OAI.MetricKMedian.Binary.PolyProgram.dropFalse`, `OAI.MetricKMedian.Binary.PolyProgram.fst`, `OAI.MetricKMedian.Binary.PolyProgram.head`, `OAI.MetricKMedian.Binary.PolyProgram.identity`, `OAI.MetricKMedian.Binary.PolyProgram.injectLeft`, `OAI.MetricKMedian.Binary.PolyProgram.injectRight`, `OAI.MetricKMedian.Binary.PolyProgram.intAbs`, `OAI.MetricKMedian.Binary.PolyProgram.intSign`, `OAI.MetricKMedian.Binary.PolyProgram.isEmpty`, `OAI.MetricKMedian.Binary.PolyProgram.listCons`, `OAI.MetricKMedian.Binary.PolyProgram.listIsEmpty`, `OAI.MetricKMedian.Binary.PolyProgram.natHalf`, `OAI.MetricKMedian.Binary.PolyProgram.natOdd`, `OAI.MetricKMedian.Binary.PolyProgram.natZero`, `OAI.MetricKMedian.Binary.PolyProgram.passTime`, `OAI.MetricKMedian.Binary.PolyProgram.prependWord`, `OAI.MetricKMedian.Binary.PolyProgram.recode`, `OAI.MetricKMedian.Binary.PolyProgram.select`, `OAI.MetricKMedian.Binary.PolyProgram.signedParts`, `OAI.MetricKMedian.Binary.PolyProgram.snd`, `OAI.MetricKMedian.Binary.PolyProgram.tail`, `OAI.MetricKMedian.Binary.Ratio.encode`, `OAI.MetricKMedian.Binary.ReverseLoop.enc`, `OAI.MetricKMedian.Binary.Signed.encode`, `OAI.MetricKMedian.Binary.SubtractionLoop.body`, `OAI.MetricKMedian.Binary.SubtractionLoop.finish` and 12 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics/KMedian, in whole or in part: `KMedian_Binary_BinaryAddition`, `KMedian_Binary_BinaryAutomatic`, `KMedian_Binary_BinaryDivision`, `KMedian_Binary_BinaryGCD`, `KMedian_Binary_BinaryInteger`, `KMedian_Binary_BinaryListFold`, `KMedian_Binary_BinaryLists`, `KMedian_Binary_BinaryMultiplication`, `KMedian_Binary_BinaryNatural`, `KMedian_Binary_BinaryRational`, `KMedian_Binary_BinarySubtraction`, `KMedian_Binary_BinaryWords`, `KMedian_Binary_BooleanEncoding`, `KMedian_Binary_BooleanFinite`, `KMedian_Binary_BooleanListPrimitives`, `KMedian_Binary_BooleanLoop`, `KMedian_Binary_BooleanProducts`, `KMedian_Binary_BooleanRecode`, `KMedian_Binary_BooleanReverse`.
--
--   **Imports.** It imports the bundles `OAIQ035K000` and `OAIQ035K001` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ035K027`, `OAIQ035K028`, `OAIQ035K029`, `OAIQ035K030`, `OAIQ035K031`, `OAIQ035K032`, `OAIQ035K034`, `OAIQ035K038` and `OAIQ035K062`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/KMedian at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ035K000
import Definitions.Def_OAIQ035K001

section
-- module Solutions.OAIQ035_KM.KMedian_Binary_BooleanEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                       
section
namespace MetricKMedian.Binary
open Turing Function Polynomial

namespace PolyProgram

 noncomputable def fst {α β : Type} (ea : α → List Bool) (eb : β → List Bool) :
    PolyProgram (encodePair ea eb) ea Prod.fst :=
  (WordTransducer.projecting false).program.of_word (fun _ => by
    simpa only [encodePair,Bool.false_eq_true,ite_false,WordTransducer.projecting] using WordTransducer.projecting_pair false _ _)

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
-- module Solutions.OAIQ035_KM.KMedian_Binary_BooleanLoop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                   
section
namespace MetricKMedian.Binary
open Turing Function Polynomial

namespace PolyProgram
variable {α β γ : Type} {ea : α → List Bool} {eb : β → List Bool}
variable {f : α → β ⊕ α}

noncomputable def passTime (P : PolyProgram ea (encodeLoop ea eb) f) (S : ℕ) : ℕ :=
  P.time.eval S+2*P.sizeBound.eval S+3

end PolyProgram
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

def identity : Transducer where
  Q := Unit
  initial := ()
  next _ b := ((),[b])
  finish _ := []

 theorem identity_run (xs : List Bool) : identity.run () xs=xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih => change b::identity.run () xs=b::xs; rw [ih]

end WordTransducer

namespace PolyProgram
variable {α β γ δ : Type}
variable {ea : α → List Bool} {eb : β → List Bool} {ec : γ → List Bool} {ed : δ → List Bool}
variable {f : α → β} {g : γ → δ}

noncomputable def identity (ea : α → List Bool) : PolyProgram ea ea _root_.id :=
  WordTransducer.identity.program.of_word (fun a => by
    simpa only [WordTransducer.identity,id_eq] using WordTransducer.identity_run (ea a))

end PolyProgram
end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Binary_BooleanListPrimitives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section
namespace MetricKMedian.Binary
open Turing Function Polynomial

namespace WordTransducer

def emptyTest : Transducer where
  Q := Bool
  initial := true
  next _ _ := (false,[])
  finish b := [b]

 theorem emptyTest_run (q : Bool) (xs : List Bool) :
    emptyTest.run q xs=[q && xs.isEmpty] := by
  induction xs generalizing q with
  | nil => cases q <;> rfl
  | cons b xs ih =>
      change emptyTest.run false xs=_
      rw [ih]
      simp

def head : Transducer where
  Q := Option Bool
  initial := none
  next q b := (q.or (some b),[])
  finish q := [q.getD false]

 theorem head_run (q : Option Bool) (xs : List Bool) :
    head.run q xs=[(q.or xs.head?).getD false] := by
  induction xs generalizing q with
  | nil => cases q <;> rfl
  | cons b xs ih =>
      change head.run (q.or (some b)) xs=_
      rw [ih]
      cases q <;> rfl

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

def prependWord (p : List Bool) : Transducer where
  Q := Bool
  initial := true
  next q b := (false,if q then p++[b] else [b])
  finish q := if q then p else []

 theorem prefix_done (p xs : List Bool) : (prependWord p).run false xs=xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih => change b::(prependWord p).run false xs=b::xs; rw [ih]

 theorem prefix_run (p xs : List Bool) : (prependWord p).run true xs=p++xs := by
  cases xs with
  | nil => exact (List.append_nil p).symm
  | cons b xs =>
      change (p++[b])++(prependWord p).run false xs=p++b::xs
      rw [prefix_done,List.append_assoc,List.singleton_append]

def select : Transducer where
  Q := Fin 2 ⊕ (Bool × Option (Option Bool))
  initial := .inl 0
  next q b := match q with
    | .inl k => if k=0 then (.inl 1,[]) else (.inr (b,none),[])
    | .inr (keep,none) => (.inr (keep,some none),[])
    | .inr (keep,some none) => (.inr (keep,some (some (!b))),[])
    | .inr (keep,some (some false)) => (.inr (keep,some none),if keep then [] else [b])
    | .inr (keep,some (some true)) => (.inr (keep,some (some true)),if keep then [b] else [])
  finish _ := []

 theorem select_done (keep : Bool) (xs : List Bool) :
    select.run (.inr (keep,some (some true))) xs=if keep then xs else [] := by
  induction xs with
  | nil => cases keep <;> rfl
  | cons b xs ih =>
      change (if keep then [b] else [])++select.run (.inr (keep,some (some true))) xs=_
      rw [ih]
      cases keep <;> simp

 theorem select_pair (keep : Bool) (xs ys : List Bool) :
    select.run (.inr (keep,some none)) (quote xs++ys)=if keep then ys else xs := by
  induction xs with
  | nil => exact select_done keep ys
  | cons b xs ih =>
      change (if keep then [] else [b])++select.run (.inr (keep,some none)) (quote xs++ys)=_
      rw [ih]
      cases keep <;> simp

 theorem select_run (keep : Bool) (xs ys : List Bool) :
    select.run (.inl 0) (quote [keep]++quote xs++ys)=if keep then ys else xs := by
  exact select_pair keep xs ys

end WordTransducer

namespace PolyProgram
variable {α β : Type} {ea : α → List Bool} {eb : β → List Bool}

noncomputable def isEmpty : PolyProgram id encodeBool List.isEmpty :=
  WordTransducer.emptyTest.program.of_word (fun xs => by
    simpa only [WordTransducer.emptyTest,Bool.true_and,encodeBool,id_eq] using WordTransducer.emptyTest_run true xs)

noncomputable def head : PolyProgram id encodeBool (fun xs => xs.head?.getD false) :=
  WordTransducer.head.program.of_word (fun xs => by
    simpa only [WordTransducer.head,Option.or,encodeBool,id_eq] using WordTransducer.head_run none xs)

noncomputable def tail : PolyProgram id id List.tail :=
  WordTransducer.tail.program.of_word (fun xs => by
    simpa only [WordTransducer.tail,id_eq] using WordTransducer.tail_run xs)

noncomputable def prependWord (p : List Bool) : PolyProgram id id (fun xs => p++xs) :=
  (WordTransducer.prependWord p).program.of_word (fun xs => by
    simpa only [WordTransducer.prependWord,id_eq] using WordTransducer.prefix_run p xs)

noncomputable def injectLeft (ea : α → List Bool) (eb : β → List Bool) :
    PolyProgram eb (encodeLoop ea eb) Sum.inl :=
  (prependWord [false]).of_word (fun _ => rfl)

noncomputable def injectRight (ea : α → List Bool) (eb : β → List Bool) :
    PolyProgram ea (encodeLoop ea eb) Sum.inr :=
  (prependWord [true]).of_word (fun _ => rfl)

noncomputable def select (eb : β → List Bool) :
    PolyProgram (encodePair encodeBool (encodePair eb eb)) eb
      (fun x => if x.1 then x.2.2 else x.2.1) :=
  WordTransducer.select.program.of_word (fun x => by
    simpa only [WordTransducer.select,encodePair,encodeBool,List.append_assoc,apply_ite] using
      WordTransducer.select_run x.1 (eb x.2.1) (eb x.2.2))

end PolyProgram
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
abbrev enc : S → List Bool := encodePair id id

 theorem run (xs ys : List Bool) (S : ℕ) (h : 2*xs.length+1+ys.length≤S) :
    BoundedRun enc body S (xs.length+1) (xs,ys) (xs.reverse++ys) := by
  induction xs generalizing ys with
  | nil =>
      apply BoundedRun.stop
      · simpa only [enc,encodePair_length,id_eq,List.length_nil,zero_mul,zero_add] using h
      · rfl
  | cons b xs ih =>
      have hs : 2*xs.length+1+(b::ys).length≤S := by simp only [List.length_cons] at h ⊢; omega
      have hr := BoundedRun.step (ea:=enc) (f:=body)
        (a:=(b::xs,ys)) (a':=(xs,b::ys))
        (by simpa only [enc,encodePair_length,id_eq] using h) rfl (ih (b::ys) hs)
      simpa only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append] using hr

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
-- module Solutions.OAIQ035_KM.KMedian_Binary_BooleanFinite
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

end PolyProgram
end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Binary_BooleanRecode
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
-- module Solutions.OAIQ035_KM.KMedian_Binary_BinaryAddition
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
-- module Solutions.OAIQ035_KM.KMedian_Binary_BinaryLists
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

namespace PolyProgram
variable {α : Type} (ea : α → List Bool) (a0 : α)
noncomputable def listIsEmpty : PolyProgram (encodeList ea) encodeBool List.isEmpty :=
  isEmpty.recode (encodeList ea) (fun _ => rfl) (fun as => by rw [EncodedList.isEmpty])

noncomputable def listCons : PolyProgram (encodePair ea (encodeList ea)) (encodeList ea) (fun x => x.1::x.2) :=
  (identity id).recode (encodePair ea (encodeList ea)) (fun _ => rfl) (fun _ => rfl)
end PolyProgram

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

namespace PolyProgram

noncomputable def natHalf : PolyProgram Nat.bits Nat.bits Nat.div2 :=
  tail.recode Nat.bits (fun _ => rfl) (fun n => (Nat.div2_bits_eq_tail n).symm)

noncomputable def natOdd : PolyProgram Nat.bits encodeBool Nat.bodd :=
  head.recode Nat.bits (fun _ => rfl) (fun n => by
    rw [Nat.bodd_eq_bits_head]
    cases n.bits <;> rfl)

noncomputable def natZero : PolyProgram Nat.bits encodeBool (fun n => decide (n=0)) :=
  isEmpty.recode Nat.bits (fun _ => rfl) (fun n => by
    congr 1
    cases h : n.bits.isEmpty
    · have hn : n≠0 := by intro hn; subst n; contradiction
      exact (decide_eq_false hn).symm
    · have hn : n=0 := (NatBinary.zero_iff n).mp (List.isEmpty_iff.mp h)
      exact (decide_eq_true hn).symm)
end PolyProgram
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

namespace GCDLoop
abbrev enc : S → List Bool := encodePair Nat.bits Nat.bits

 theorem enc_length (s : S) : (enc s).length=2*s.1.bits.length+1+s.2.bits.length := by
  exact encodePair_length _ _ _
 theorem length_le_potential (s : S) : (enc s).length ≤ 2*potential s+1 := by
  simp only [enc_length,potential]; omega
 theorem potential_le_length (s : S) : potential s ≤ (enc s).length := by
  simp only [enc_length,potential]; omega

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
 def encode (z : ℤ) : List Bool := encodePair encodeBool Nat.bits (parts z)

end Signed

namespace PolyProgram
abbrev signedParts : Bool × ℕ → List Bool := encodePair encodeBool Nat.bits

noncomputable def intSign : PolyProgram Signed.encode encodeBool Signed.sign :=
  (fst encodeBool Nat.bits).recode Signed.parts (fun _ => rfl) (fun _ => rfl)
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
 def encode (q : ℚ) : List Bool := encodePair Signed.encode Nat.bits (parts q)
end Ratio

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
open PolyProgram Function
instance instCodingRat : Coding ℚ := ⟨Ratio.encode⟩
instance instCodingBool : Coding Bool := ⟨encodeBool⟩
instance instCodingProd {α β : Type} [Coding α] [Coding β] : Coding (α × β) := ⟨encodePair enc enc⟩
instance instCodingList {α : Type} [Coding α] : Coding (List α) := ⟨encodeList enc⟩

@[fun_prop] def Poly {α β : Type} [Coding α] [Coding β] (f : α → β) : Prop :=
  Nonempty (PolyProgram enc enc f)

namespace Poly
variable {α β γ : Type} [Coding α] [Coding β] [Coding γ]
noncomputable def program {f : α → β} (h : Poly f) : PolyProgram enc enc f := Classical.choice h

@[fun_prop] theorem identity : Poly (id : α → α) := ⟨PolyProgram.identity enc⟩

end Poly
end MetricKMedian.Binary.Automatic
end

end OAI
end


