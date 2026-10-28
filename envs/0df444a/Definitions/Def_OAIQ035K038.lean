-- Prove2me | Definitions.Def_OAIQ035K038
-- name    : OAIQ035K038
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T08:01:47.582034+00:00
-- url     : https://prove2.me/theorems/b657f5af-ee1d-4585-a07b-a1afa4a0534f
-- title:
--   Definitions bundle OAIQ035K038 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 77 declarations of OpenAI's Lean: 47 definitions and 30 theorems. The definitions and types are `OAI.MetricKMedian.Binary.DivisionLoop.loop`, `OAI.MetricKMedian.Binary.DivisionLoop.program`, `OAI.MetricKMedian.Binary.GCDLoop.loop`, `OAI.MetricKMedian.Binary.GCDLoop.program`, `OAI.MetricKMedian.Binary.ListFold.linearLoop`, `OAI.MetricKMedian.Binary.ListSplit.loop`, `OAI.MetricKMedian.Binary.ListSplit.program`, `OAI.MetricKMedian.Binary.ListZip.loop`, `OAI.MetricKMedian.Binary.ListZip.program`, `OAI.MetricKMedian.Binary.MultiplicationLoop.loop`, `OAI.MetricKMedian.Binary.PolyProgram.intLT`, `OAI.MetricKMedian.Binary.PolyProgram.intMul`, `OAI.MetricKMedian.Binary.PolyProgram.intNeg`, `OAI.MetricKMedian.Binary.PolyProgram.intSub`, `OAI.MetricKMedian.Binary.PolyProgram.listAppend`, `OAI.MetricKMedian.Binary.PolyProgram.listDrop`, `OAI.MetricKMedian.Binary.PolyProgram.listFilter`, `OAI.MetricKMedian.Binary.PolyProgram.listFilterWith`, `OAI.MetricKMedian.Binary.PolyProgram.listFoldLinear`, `OAI.MetricKMedian.Binary.PolyProgram.listGetD`, `OAI.MetricKMedian.Binary.PolyProgram.listIndices`, `OAI.MetricKMedian.Binary.PolyProgram.listLength`, `OAI.MetricKMedian.Binary.PolyProgram.listMap`, `OAI.MetricKMedian.Binary.PolyProgram.listSplitAt`, `OAI.MetricKMedian.Binary.PolyProgram.listZip`, `OAI.MetricKMedian.Binary.PolyProgram.mkRational`, `OAI.MetricKMedian.Binary.PolyProgram.natDiv`, `OAI.MetricKMedian.Binary.PolyProgram.natDivMod`, `OAI.MetricKMedian.Binary.PolyProgram.natEQ`, `OAI.MetricKMedian.Binary.PolyProgram.natGcd`, `OAI.MetricKMedian.Binary.PolyProgram.natLE`, `OAI.MetricKMedian.Binary.PolyProgram.natMod`, `OAI.MetricKMedian.Binary.PolyProgram.natMul`, `OAI.MetricKMedian.Binary.PolyProgram.ratAdd`, `OAI.MetricKMedian.Binary.PolyProgram.ratDiv`, `OAI.MetricKMedian.Binary.PolyProgram.ratEQ`, `OAI.MetricKMedian.Binary.PolyProgram.ratInv`, `OAI.MetricKMedian.Binary.PolyProgram.ratLE`, `OAI.MetricKMedian.Binary.PolyProgram.ratLT`, `OAI.MetricKMedian.Binary.PolyProgram.ratMul` and 7 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics/KMedian, in whole or in part: `KMedian_Binary_BinaryAutomatic`, `KMedian_Binary_BinaryDivision`, `KMedian_Binary_BinaryGCD`, `KMedian_Binary_BinaryInteger`, `KMedian_Binary_BinaryListContext`, `KMedian_Binary_BinaryListFold`, `KMedian_Binary_BinaryListIndex`, `KMedian_Binary_BinaryListIndices`, `KMedian_Binary_BinaryListMap`, `KMedian_Binary_BinaryListZip`, `KMedian_Binary_BinaryLists`, `KMedian_Binary_BinaryMultiplication`, `KMedian_Binary_BinaryPredicates`, `KMedian_Binary_BinaryRational`, `KMedian_Optimization_LPListFacts`, `KMedian_Sparse_SparseListTrim`.
--
--   **Imports.** It imports the bundles `OAIQ035K027`, `OAIQ035K028`, `OAIQ035K000`, `OAIQ035K001`, `OAIQ035K002`, `OAIQ035K005`, `OAIQ035K014`, `OAIQ035K015` and `OAIQ035K017` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ035K046`, `OAIQ035K047`, `OAIQ035K048`, `OAIQ035K049` and `OAIQ035K062`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/KMedian at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ035K027
import Definitions.Def_OAIQ035K028
import Definitions.Def_OAIQ035K000
import Definitions.Def_OAIQ035K001
import Definitions.Def_OAIQ035K002
import Definitions.Def_OAIQ035K005
import Definitions.Def_OAIQ035K014
import Definitions.Def_OAIQ035K015
import Definitions.Def_OAIQ035K017

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

namespace PolyProgram
variable {α : Type} (ea : α → List Bool) (a0 : α)
noncomputable def listAppend : PolyProgram (encodePair (encodeList ea) (encodeList ea)) (encodeList ea) (fun x => x.1++x.2) :=
  (((listReverse ea a0).thread (encodeList ea)).comp (ListReverse.loop ea a0)).congr _
    (fun _ => by simp only [Function.comp_apply,ListReverse.result,List.reverse_reverse])
end PolyProgram
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

noncomputable def linearLoop (P : PolyProgram (encodePair eb ea) eb op) (C : ℕ)
    (hop : ∀ b a, (eb (op (b,a))).length ≤ (eb b).length+C*(2*(ea a).length+1)) :
    PolyProgram (enc ea eb) eb (result op) :=
  loop ea eb a0 op P ((Polynomial.C C+1)*X) (fun as b pre suf he => by
    have hh := linear_height ea eb op C hop pre b
    have hp : (encodeList ea pre).length ≤ (encodeList ea as).length := by
      rw [he,EncodedList.append,List.length_append]; omega
    simp only [eval_mul,eval_add,eval_C,eval_one,eval_X,enc,encodePair_length]
    nlinarith)
end ListFold

namespace PolyProgram
variable {α β : Type} {ea : α → List Bool} {eb : β → List Bool} {op : β × α → β}
noncomputable def listFoldLinear (P : PolyProgram (encodePair eb ea) eb op) (a0 : α) (C : ℕ)
    (hop : ∀ b a, (eb (op (b,a))).length ≤ (eb b).length+C*(2*(ea a).length+1)) :
    PolyProgram (encodePair (encodeList ea) eb) eb (fun x => x.1.foldl (fun b a => op (b,a)) x.2) :=
  ListFold.linearLoop ea eb a0 op P C hop
end PolyProgram
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

namespace PolyProgram
variable {α β : Type} {ea : α → List Bool} {eb : β → List Bool} {f : α → β}
noncomputable def listMap (P : PolyProgram ea eb f) (a0 : α) :
    PolyProgram (encodeList ea) (encodeList eb) (List.map f) := by
  let step : PolyProgram (encodePair (encodeList eb) ea) (encodeList eb) (fun x => f x.2::x.1) :=
    (((P.second (encodeList eb)).comp (exchange (encodeList eb) eb)).comp (listCons eb)).congr _ (fun _ => rfl)
  let fold := step.listFold a0 (X*(2*P.sizeBound+1)+X) (by
    intro as bs pre suf he
    simp only [ListAlgorithms.pushMap,EncodedList.append,List.length_append,EncodedList.reverse_length]
    let L := (encodePair (encodeList ea) (encodeList eb) (as,bs)).length
    have hpre : (encodeList ea pre).length ≤ (encodeList ea as).length := by
      rw [he,EncodedList.append,List.length_append]; omega
    have hlen : pre.length ≤ L := by
      have hp := EncodedList.length_le ea pre
      simp only [L,encodePair_length]; omega
    have hbs : (encodeList eb bs).length ≤ L := by simp only [L,encodePair_length]; omega
    have hh := EncodedList.length_bound eb (pre.map f) (P.sizeBound.eval L) (by
      intro b hb
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hb
      apply (P.length_bound a).trans
      apply polynomial_eval_mono
      have hmem := EncodedList.member_length ea pre a ha
      simp only [L,encodePair_length]; omega)
    simp only [List.length_map] at hh
    simp only [eval_add,eval_mul,eval_X,eval_ofNat,eval_one]
    change _ ≤ L*(2*P.sizeBound.eval L+1)+L
    nlinarith)
  let start := (identity (encodeList ea)).fanout (constant (encodeList ea) (encodeList eb) [])
  exact ((start.comp fold).comp (listReverse eb (f a0))).congr _ (fun as => by
    simp only [Function.comp_apply,id_eq,ListAlgorithms.pushMap,List.append_nil,List.reverse_reverse])

noncomputable def listFilter {p : α → Bool} (P : PolyProgram ea encodeBool p) (a0 : α) :
    PolyProgram (encodeList ea) (encodeList ea) (List.filter p) := by
  let first := fst (encodeList ea) ea
  let test := (snd (encodeList ea) ea).comp P
  let push := (exchange (encodeList ea) ea).comp (listCons ea)
  let step : PolyProgram (encodePair (encodeList ea) ea) (encodeList ea) (fun x => if p x.2 then x.2::x.1 else x.1) :=
    (ite test first push).congr _ (fun _ => rfl)
  let fold := step.listFoldLinear a0 1 (by
    intro bs a
    simp only [one_mul]
    split_ifs
    · rw [EncodedList.cons_length]; omega
    · omega)
  exact ((((identity (encodeList ea)).fanout (constant (encodeList ea) (encodeList ea) [])).comp fold).comp (listReverse ea a0)).congr _
    (fun as => by simp only [Function.comp_apply,id_eq,ListAlgorithms.pushFilter,List.append_nil,List.reverse_reverse])

noncomputable def listLength (ea : α → List Bool) (a0 : α) :
    PolyProgram (encodeList ea) Nat.bits List.length := by
  let step : PolyProgram (encodePair Nat.bits ea) Nat.bits (fun x : ℕ × α => x.1+1) :=
    (((fst Nat.bits ea).fanout (constant (encodePair Nat.bits ea) Nat.bits 1)).comp natAdd).congr _ (fun _ => rfl)
  let fold := step.listFoldLinear a0 2 (by
    intro n a
    have h := NatBinary.add_length n 1
    have hone : (1:ℕ).bits.length=1 := rfl
    rw [hone] at h
    dsimp only
    omega)
  exact (((identity (encodeList ea)).fanout (constant (encodeList ea) Nat.bits 0)).comp fold).congr _
    (fun as => by simpa only [Function.comp_apply,id_eq,Nat.zero_add] using ListAlgorithms.count as 0)

end PolyProgram
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

namespace PolyProgram
variable {α β γ : Type} {ea : α → List Bool} {eb : β → List Bool} {ec : γ → List Bool}

noncomputable def listFilterWith {p : γ × α → Bool}
    (P : PolyProgram (encodePair ec ea) encodeBool p) (a0 : α) (c0 : γ) :
    PolyProgram (encodePair ec (encodeList ea)) (encodeList ea) (fun x => x.2.filter (fun a => p (x.1,a))) := by
  let attach := (identity (encodePair ec ea)).listMapWith a0 (c0,a0)
  let filt := listFilter P (c0,a0)
  let drop := (snd ec ea).listMap (c0,a0)
  exact ((attach.comp filt).comp drop).congr _ (fun x => by
    simp only [Function.comp_apply,id_eq,ListAlgorithms.filterMapPair])
end PolyProgram
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
noncomputable def program : PolyProgram (enc ea) (encodeLoop (enc ea) (out ea)) (body a0) := by
  let ls := PolyProgram.fst (encodeList ea) (encodePair Nat.bits (encodeList ea))
  let ns := PolyProgram.snd (encodeList ea) (encodePair Nat.bits (encodeList ea))
  let n := ns.comp (PolyProgram.fst Nat.bits (encodeList ea))
  let bs := ns.comp (PolyProgram.snd Nat.bits (encodeList ea))
  let zero := (((ls.comp (PolyProgram.listIsEmpty ea)).fanout (n.comp PolyProgram.natZero)).comp PolyProgram.boolOr)
  let done := (((bs.comp (PolyProgram.listReverse ea a0)).fanout ls).comp (PolyProgram.injectLeft (enc ea) (out ea)))
  let pred := ((n.fanout (PolyProgram.constant (enc ea) Nat.bits 1)).comp PolyProgram.natSub)
  let push := (((ls.comp (PolyProgram.listHead ea a0)).fanout bs).comp (PolyProgram.listCons ea))
  let cont := (((ls.comp (PolyProgram.listTail ea a0)).fanout (pred.fanout push)).comp (PolyProgram.injectRight (enc ea) (out ea)))
  exact (PolyProgram.ite zero cont done).congr _ (fun _ => rfl)

noncomputable def loop : PolyProgram (enc ea) (out ea) result :=
  (program ea a0).loop result (X+1) X (fun x => by
    obtain ⟨t,ht,hr⟩ := run ea a0 x.1 x.2.2 x.2.1 (enc ea x).length le_rfl
    refine ⟨t,?_,?_⟩
    · have hh := EncodedList.length_le ea x.1
      simp only [eval_add,eval_X,eval_one,enc,encodePair_length]
      omega
    · simpa only [eval_X] using hr)
end ListSplit

namespace PolyProgram
variable {α : Type} (ea : α → List Bool) (a0 : α)
noncomputable def listSplitAt : PolyProgram (encodePair (encodeList ea) Nat.bits)
    (encodePair (encodeList ea) (encodeList ea)) (fun x : List α × ℕ => (x.1.take x.2,x.1.drop x.2)) := by
  let ls := fst (encodeList ea) Nat.bits
  let n := snd (encodeList ea) Nat.bits
  let start := ls.fanout (n.fanout (constant (encodePair (encodeList ea) Nat.bits) (encodeList ea) []))
  exact (start.comp (ListSplit.loop ea a0)).congr _ (fun x => by simp only [Function.comp_apply,ListSplit.result,List.reverse_nil,List.nil_append])
noncomputable def listDrop : PolyProgram (encodePair (encodeList ea) Nat.bits)
    (encodeList ea) (fun x : List α × ℕ => x.1.drop x.2) :=
  ((listSplitAt ea a0).comp (snd (encodeList ea) (encodeList ea))).congr _ (fun _ => rfl)
noncomputable def listGetD : PolyProgram (encodePair (encodeList ea) Nat.bits)
    ea (fun x : List α × ℕ => x.1[x.2]?.getD a0) := by
  exact ((listDrop ea a0).comp (listHead ea a0)).congr _ (fun x => by
    simp only [Function.comp_apply,List.head?_drop])
end PolyProgram
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

noncomputable def program : PolyProgram enc (encodeLoop enc eqr) body := by
  let px := PolyProgram.fst id edqr
  let pdqr := PolyProgram.snd id edqr
  let pd := pdqr.comp (PolyProgram.fst Nat.bits eqr)
  let pqr := pdqr.comp (PolyProgram.snd Nat.bits eqr)
  let pq := pqr.comp (PolyProgram.fst Nat.bits Nat.bits)
  let pr := pqr.comp (PolyProgram.snd Nat.bits Nat.bits)
  let pb := px.comp PolyProgram.head
  let pt := (pb.fanout pr).comp PolyProgram.natBit
  let plt := (pt.fanout pd).comp PolyProgram.natLT
  let nq := ((plt.comp PolyProgram.boolNot).fanout pq).comp PolyProgram.natBit
  let nr := PolyProgram.ite plt ((pt.fanout pd).comp PolyProgram.natSub) pt
  let pn := (px.comp PolyProgram.tail).fanout (pd.fanout (nq.fanout nr))
  exact (PolyProgram.ite (px.comp PolyProgram.isEmpty)
    (pn.comp (PolyProgram.injectRight enc eqr))
    (pqr.comp (PolyProgram.injectLeft enc eqr))).congr _ (fun s => by
      simp only [Function.comp_apply,body,next,qstep,rstep,decide_eq_true_eq])

noncomputable def loop : PolyProgram enc eqr result :=
  program.loop result (X+1) (3*X+3) (fun s => by
    refine ⟨s.1.length+1,?_,?_⟩
    · simp only [Polynomial.eval_add,eval_X,eval_one,enc_length]; omega
    · have hs := total_le_length s
      simpa only [Polynomial.eval_add,eval_mul,eval_ofNat,eval_X] using
        run s.1 s.2.1 s.2.2.1 s.2.2.2 (3*(enc s).length+3) (by
          change 3*(potential s+s.2.1.bits.length)+3≤3*(enc s).length+3
          omega))
end DivisionLoop

namespace PolyProgram
noncomputable def natDivMod : PolyProgram (encodePair Nat.bits Nat.bits) (encodePair Nat.bits Nat.bits)
    (fun x : ℕ × ℕ => (x.1/x.2,x.1%x.2)) := by
  let ex : ℕ × ℕ → List Bool := encodePair Nat.bits Nat.bits
  let px := fst Nat.bits Nat.bits
  let pd := snd Nat.bits Nat.bits
  let rev : PolyProgram Nat.bits id (fun n => n.bits.reverse) := reverse.recode Nat.bits (fun _ => rfl) (fun _ => rfl)
  let init := (px.comp rev).fanout (pd.fanout (constant ex DivisionLoop.eqr (0,0)))
  let normal := init.comp DivisionLoop.loop
  let zeroCase := (constant ex Nat.bits 0).fanout px
  refine (ite (pd.comp natZero) normal zeroCase).congr _ ?_
  intro x
  change (if decide (x.2=0) then (0,x.1) else DivisionLoop.eval x.1.bits.reverse x.2 0 0)=_
  by_cases hd : x.2=0
  · simp only [hd,decide_true,ite_true,Nat.div_zero,Nat.mod_zero]
  · simp only [decide_eq_false hd,Bool.false_eq_true,ite_false]
    obtain ⟨hr,he⟩ := DivisionLoop.eval_spec x.1.bits.reverse x.2 0 0 (Nat.pos_of_ne_zero hd) (Nat.pos_of_ne_zero hd)
    simp only [zero_mul,zero_add,mul_zero,zero_add,List.reverse_reverse,Word.value_bits] at he
    have hp : x.1/x.2=(DivisionLoop.eval x.1.bits.reverse x.2 0 0).1 ∧
        x.1%x.2=(DivisionLoop.eval x.1.bits.reverse x.2 0 0).2 :=
      (Nat.div_mod_unique (Nat.pos_of_ne_zero hd)).mpr ⟨by
        simpa only [Nat.mul_comm,Nat.add_comm] using he,hr⟩
    exact Prod.ext hp.1.symm hp.2.symm

noncomputable def natDiv : PolyProgram (encodePair Nat.bits Nat.bits) Nat.bits (fun x : ℕ × ℕ => x.1/x.2) :=
  (natDivMod.comp (fst Nat.bits Nat.bits)).congr _ (fun _ => rfl)
noncomputable def natMod : PolyProgram (encodePair Nat.bits Nat.bits) Nat.bits (fun x : ℕ × ℕ => x.1%x.2) :=
  (natDivMod.comp (snd Nat.bits Nat.bits)).congr _ (fun _ => rfl)
end PolyProgram
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

noncomputable def program : PolyProgram enc (encodeLoop enc Nat.bits) body := by
  let px := PolyProgram.fst Nat.bits Nat.bits
  let py := PolyProgram.snd Nat.bits Nat.bits
  let pn := py.fanout PolyProgram.natMod
  exact (PolyProgram.ite (py.comp PolyProgram.natZero)
    (pn.comp (PolyProgram.injectRight enc Nat.bits))
    (px.comp (PolyProgram.injectLeft enc Nat.bits))).congr _ (fun _ => by
      simp only [Function.comp_apply,body,next,decide_eq_true_eq])

noncomputable def loop : PolyProgram enc Nat.bits result :=
  program.loop result (X+2) (2*X+1) (fun s => by
    have hs := potential_le_length s
    obtain ⟨n,hn,hr⟩ := run s (2*(enc s).length+1) (by omega)
    refine ⟨n,?_,?_⟩
    · simp only [eval_add,eval_X,eval_ofNat]; omega
    · simpa only [eval_add,eval_mul,eval_ofNat,eval_one,eval_X] using hr)
end GCDLoop

namespace PolyProgram
noncomputable def natGcd : PolyProgram (encodePair Nat.bits Nat.bits) Nat.bits (fun x : ℕ × ℕ => x.1.gcd x.2) :=
  GCDLoop.loop
end PolyProgram
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

noncomputable def loop : PolyProgram enc Nat.bits result :=
  program.loop result (X+1) (3*X+2) (fun s => by
    obtain ⟨n,hn,hr⟩ := run s.1.bits.length s (3*(enc s).length+2) rfl (by
      have := potential_le_length s; omega)
    refine ⟨n,?_,?_⟩
    · simp only [eval_add,eval_X,eval_one,enc_length]; omega
    · simpa only [eval_add,eval_mul,eval_ofNat,eval_X] using hr)
end MultiplicationLoop

namespace PolyProgram
noncomputable def natMul : PolyProgram (encodePair Nat.bits Nat.bits) Nat.bits (fun x : ℕ × ℕ => x.1*x.2) := by
  let ex : ℕ × ℕ → List Bool := encodePair Nat.bits Nat.bits
  let init := (fst Nat.bits Nat.bits).fanout ((snd Nat.bits Nat.bits).fanout (constant ex Nat.bits 0))
  exact (init.comp MultiplicationLoop.loop).congr _ (fun x => by
    simp only [Function.comp_apply,MultiplicationLoop.result,Nat.add_zero])
end PolyProgram
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

namespace PolyProgram

noncomputable def intNeg : PolyProgram Signed.encode Signed.encode Neg.neg :=
  (((intSign.comp boolNot).fanout intAbs).comp intFromParts).congr _ (fun z => by
    simp only [Function.comp_apply,Signed.value_neg,Signed.value_parts])

noncomputable def intMul : PolyProgram (encodePair Signed.encode Signed.encode) Signed.encode (fun x : ℤ × ℤ => x.1*x.2) := by
  let px := fst Signed.encode Signed.encode
  let py := snd Signed.encode Signed.encode
  let s := ((px.comp intSign).fanout (py.comp intSign)).comp boolXor
  let n := ((px.comp intAbs).fanout (py.comp intAbs)).comp natMul
  exact ((s.fanout n).comp intFromParts).congr _ (fun x => by
    simp only [Function.comp_apply,Signed.value_mul,Signed.value_parts])

noncomputable def intSub : PolyProgram (encodePair Signed.encode Signed.encode) Signed.encode (fun x : ℤ × ℤ => x.1-x.2) :=
  ((intNeg.second Signed.encode).comp intAdd).congr _ (fun x => (sub_eq_add_neg x.1 x.2).symm)
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

namespace PolyProgram
noncomputable def intLT : PolyProgram (encodePair Signed.encode Signed.encode) encodeBool (fun x : ℤ × ℤ => decide (x.1 < x.2)) :=
  (intSub.comp intSign).congr _ (fun _ => by simp only [Function.comp_apply,Signed.sign,sub_neg])

noncomputable def mkRational : PolyProgram (encodePair Signed.encode Nat.bits) Ratio.encode (fun x => mkRat x.1 x.2) := by
  let pn := fst Signed.encode Nat.bits
  let pd := snd Signed.encode Nat.bits
  let pa := pn.comp intAbs
  let pg := (pd.fanout pa).comp natGcd
  let nm := (((pn.comp intSign).fanout ((pa.fanout pg).comp natDiv)).comp intFromParts)
  let dm := (pd.fanout pg).comp natDiv
  let normal := ite (pd.comp natZero) (nm.fanout dm)
    (constant (encodePair Signed.encode Nat.bits) (encodePair Signed.encode Nat.bits) (0,1))
  refine normal.recode id (fun _ => rfl) ?_
  intro x
  simp only [Function.comp_apply,id_eq,decide_eq_true_eq]
  change encodePair Signed.encode Nat.bits (Ratio.normalized x)=Ratio.encode (mkRat x.1 x.2)
  rw [Ratio.normalized_eq]
  rfl

noncomputable def ratNeg : PolyProgram Ratio.encode Ratio.encode Neg.neg := by
  refine (((ratNum.comp intNeg).fanout ratDen)).recode id (fun _ => rfl) ?_
  intro q
  simp only [Function.comp_apply,id_eq,Ratio.encode,Ratio.parts,Rat.num_neg_eq_neg_num,Rat.den_neg_eq_den]
noncomputable def ratOfInt : PolyProgram Signed.encode Ratio.encode Int.cast :=
  (((identity Signed.encode).fanout (constant Signed.encode Nat.bits 1)).comp mkRational).congr _ (fun z => by simp [Rat.mkRat_eq_div])
noncomputable def ratOfNat : PolyProgram Nat.bits Ratio.encode Nat.cast :=
  (intOfNat.comp ratOfInt).congr _ (fun n => by simp)
noncomputable def ratMul : PolyProgram (encodePair Ratio.encode Ratio.encode) Ratio.encode (fun x : ℚ × ℚ => x.1*x.2) := by
  let px := fst Ratio.encode Ratio.encode
  let py := snd Ratio.encode Ratio.encode
  let pn := ((px.comp ratNum).fanout (py.comp ratNum)).comp intMul
  let pd := ((px.comp ratDen).fanout (py.comp ratDen)).comp natMul
  exact ((pn.fanout pd).comp mkRational).congr _ (fun x => (Rat.mul_def' x.1 x.2).symm)
noncomputable def ratAdd : PolyProgram (encodePair Ratio.encode Ratio.encode) Ratio.encode (fun x : ℚ × ℚ => x.1+x.2) := by
  let px := fst Ratio.encode Ratio.encode
  let py := snd Ratio.encode Ratio.encode
  let pnx := ((px.comp ratNum).fanout ((py.comp ratDen).comp intOfNat)).comp intMul
  let pny := ((py.comp ratNum).fanout ((px.comp ratDen).comp intOfNat)).comp intMul
  let pn := (pnx.fanout pny).comp intAdd
  let pd := ((px.comp ratDen).fanout (py.comp ratDen)).comp natMul
  exact ((pn.fanout pd).comp mkRational).congr _ (fun x => (Rat.add_def' x.1 x.2).symm)
noncomputable def ratSub : PolyProgram (encodePair Ratio.encode Ratio.encode) Ratio.encode (fun x : ℚ × ℚ => x.1-x.2) :=
  ((ratNeg.second Ratio.encode).comp ratAdd).congr _ (fun x => (sub_eq_add_neg x.1 x.2).symm)
noncomputable def ratInv : PolyProgram Ratio.encode Ratio.encode Inv.inv :=
  (((((ratNum.comp intSign).fanout ratDen).comp intFromParts).fanout (ratNum.comp intAbs)).comp mkRational).congr _ (fun q => (Ratio.inv_eq q).symm)
noncomputable def ratDiv : PolyProgram (encodePair Ratio.encode Ratio.encode) Ratio.encode (fun x : ℚ × ℚ => x.1/x.2) :=
  ((ratInv.second Ratio.encode).comp ratMul).congr _ (fun x => (div_eq_mul_inv x.1 x.2).symm)
noncomputable def ratLT : PolyProgram (encodePair Ratio.encode Ratio.encode) encodeBool (fun x : ℚ × ℚ => decide (x.1 < x.2)) := by
  let px := fst Ratio.encode Ratio.encode
  let py := snd Ratio.encode Ratio.encode
  let lhs := ((px.comp ratNum).fanout ((py.comp ratDen).comp intOfNat)).comp intMul
  let rhs := ((py.comp ratNum).fanout ((px.comp ratDen).comp intOfNat)).comp intMul
  refine ((lhs.fanout rhs).comp intLT).congr _ ?_
  intro x
  simp only [Function.comp_apply]
  simp only [← Rat.lt_iff]
end PolyProgram
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
namespace PolyProgram
variable {α : Type} (ea : α → List Bool) (a0 : α)
noncomputable def listIndices : PolyProgram (encodeList ea) (encodeList Nat.bits) (fun xs : List α => List.range xs.length) := by
  let eb := encodePair Nat.bits (encodeList Nat.bits)
  let acc := fst eb ea
  let n := acc.comp (fst Nat.bits (encodeList Nat.bits))
  let bs := acc.comp (snd Nat.bits (encodeList Nat.bits))
  let inc := (n.fanout (constant (encodePair eb ea) Nat.bits 1)).comp natAdd
  let push := (n.fanout bs).comp (listCons Nat.bits)
  let step : PolyProgram (encodePair eb ea) eb ListAlgorithms.indexStep :=
    (inc.fanout push).congr _ (fun _ => rfl)
  let fold := step.listFold a0 (10*(X+1)^2) (by
    intro xs x pre suf he
    simpa only [eval_mul,eval_ofNat,eval_pow,eval_add,eval_X,eval_one] using ListAlgorithms.index_partial_size ea xs x pre suf he)
  let start := (identity (encodeList ea)).fanout (constant (encodeList ea) eb (0,[]))
  exact ((((start.comp fold).comp (snd Nat.bits (encodeList Nat.bits))).comp (listReverse Nat.bits 0))).congr _ (fun xs => by
    simp only [Function.comp_apply,id_eq,ListAlgorithms.pushIndices,List.append_nil,List.reverse_reverse,← List.range_eq_range'])
end PolyProgram
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
noncomputable def program : PolyProgram (enc ea eb) (encodeLoop (enc ea eb) (encodeList (encodePair ea eb))) (body a0 b0) := by
  let pair := PolyProgram.fst (encodePair (encodeList ea) (encodeList eb)) (encodeList (encodePair ea eb))
  let as := pair.comp (PolyProgram.fst (encodeList ea) (encodeList eb))
  let bs := pair.comp (PolyProgram.snd (encodeList ea) (encodeList eb))
  let cs := PolyProgram.snd (encodePair (encodeList ea) (encodeList eb)) (encodeList (encodePair ea eb))
  let test := (((as.comp (PolyProgram.listIsEmpty ea)).fanout (bs.comp (PolyProgram.listIsEmpty eb))).comp PolyProgram.boolOr)
  let done := ((cs.comp (PolyProgram.listReverse (encodePair ea eb) (a0,b0))).comp (PolyProgram.injectLeft (enc ea eb) (encodeList (encodePair ea eb))))
  let heads := (as.comp (PolyProgram.listHead ea a0)).fanout (bs.comp (PolyProgram.listHead eb b0))
  let tails := (as.comp (PolyProgram.listTail ea a0)).fanout (bs.comp (PolyProgram.listTail eb b0))
  let push := ((heads.fanout cs).comp (PolyProgram.listCons (encodePair ea eb)))
  let cont := ((tails.fanout push).comp (PolyProgram.injectRight (enc ea eb) (encodeList (encodePair ea eb))))
  exact (PolyProgram.ite test cont done).congr _ (fun _ => rfl)

noncomputable def loop : PolyProgram (enc ea eb) (encodeList (encodePair ea eb)) result :=
  (program ea eb a0 b0).loop result (X+1) X (fun x => by
    obtain ⟨t,ht,hr⟩ := run ea eb a0 b0 x.1.1 x.1.2 x.2 (enc ea eb x).length le_rfl
    refine ⟨t,?_,?_⟩
    · have hh := EncodedList.length_le ea x.1.1
      simp only [eval_add,eval_X,eval_one,enc,encodePair_length]
      omega
    · simpa only [eval_X] using hr)
end ListZip
namespace PolyProgram
variable {α β γ : Type} (ea : α → List Bool) (eb : β → List Bool) (a0 : α) (b0 : β)
noncomputable def listZip : PolyProgram (encodePair (encodeList ea) (encodeList eb))
    (encodeList (encodePair ea eb)) (fun x : List α × List β => x.1.zip x.2) := by
  let start := (identity (encodePair (encodeList ea) (encodeList eb))).fanout
    (constant (encodePair (encodeList ea) (encodeList eb)) (encodeList (encodePair ea eb)) [])
  exact (start.comp (ListZip.loop ea eb a0 b0)).congr _ (fun _ => by simp only [Function.comp_apply,id_eq,ListZip.result,List.reverse_nil,List.nil_append])
end PolyProgram
end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Binary_BinaryPredicates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                        
section
namespace MetricKMedian.Binary.PolyProgram
noncomputable def natLE : PolyProgram (encodePair Nat.bits Nat.bits) encodeBool (fun x : ℕ × ℕ => decide (x.1≤x.2)) :=
  (((exchange Nat.bits Nat.bits).comp natLT).comp boolNot).congr _ (fun x => by
    by_cases h : x.1≤x.2
    · simp [Function.comp_def,h,not_lt.mpr h]
    · simp [Function.comp_def,h,lt_of_not_ge h])
noncomputable def natEQ : PolyProgram (encodePair Nat.bits Nat.bits) encodeBool (fun x : ℕ × ℕ => decide (x.1=x.2)) :=
  ((natLE.fanout ((exchange Nat.bits Nat.bits).comp natLE)).comp boolAnd).congr _ (fun x => by
    by_cases h₁ : x.1≤x.2 <;> by_cases h₂ : x.2≤x.1 <;> simp [Function.comp_apply,Prod.swap,h₁,h₂,le_antisymm_iff])
noncomputable def ratEQ : PolyProgram (encodePair Ratio.encode Ratio.encode) encodeBool (fun x : ℚ × ℚ => decide (x.1=x.2)) :=
  (ratSub.comp ratZero).congr _ (fun q => by simp only [Function.comp_apply,sub_eq_zero])
noncomputable def ratLE : PolyProgram (encodePair Ratio.encode Ratio.encode) encodeBool (fun x : ℚ × ℚ => decide (x.1≤x.2)) :=
  (((exchange Ratio.encode Ratio.encode).comp ratLT).comp boolNot).congr _ (fun x => by
    by_cases h : x.1≤x.2
    · simp [Function.comp_def,h,not_lt.mpr h]
    · simp [Function.comp_def,h,lt_of_not_ge h])
end MetricKMedian.Binary.PolyProgram
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Optimization_LPListFacts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                   
section
namespace MetricKMedian.LPBinary
open Finset

namespace Program
open Binary Binary.PolyProgram
noncomputable def ratMax : PolyProgram (encodePair Ratio.encode Ratio.encode) Ratio.encode (fun x : ℚ × ℚ => max x.1 x.2) :=
  (ite ratLE (fst Ratio.encode Ratio.encode) (snd Ratio.encode Ratio.encode)).congr _ (fun x => by
    by_cases h : x.1≤x.2
    · simp [h]
    · simp [h,max_eq_left (le_of_not_ge h)])
noncomputable def ratMin : PolyProgram (encodePair Ratio.encode Ratio.encode) Ratio.encode (fun x : ℚ × ℚ => min x.1 x.2) :=
  (ite ratLE (snd Ratio.encode Ratio.encode) (fst Ratio.encode Ratio.encode)).congr _ (fun x => by
    by_cases h : x.1≤x.2
    · simp [h]
    · simp [h,min_eq_right (le_of_not_ge h)])
end Program
end MetricKMedian.LPBinary
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

namespace Poly
variable {α β γ : Type} [Coding α] [Coding β] [Coding γ]

@[fun_prop] theorem rat_add : Poly (fun x : ℚ × ℚ => x.1+x.2) := ⟨ratAdd⟩
@[fun_prop] theorem rat_sub : Poly (fun x : ℚ × ℚ => x.1-x.2) := ⟨ratSub⟩
@[fun_prop] theorem rat_mul : Poly (fun x : ℚ × ℚ => x.1*x.2) := ⟨ratMul⟩
@[fun_prop] theorem rat_div : Poly (fun x : ℚ × ℚ => x.1/x.2) := ⟨ratDiv⟩
@[fun_prop] theorem rat_lt : Poly (fun x : ℚ × ℚ => decide (x.1<x.2)) := ⟨ratLT⟩
@[fun_prop] theorem rat_le : Poly (fun x : ℚ × ℚ => decide (x.1≤x.2)) := ⟨ratLE⟩
@[fun_prop] theorem rat_eq : Poly (fun x : ℚ × ℚ => decide (x.1=x.2)) := ⟨ratEQ⟩
@[fun_prop] theorem rat_min : Poly (fun x : ℚ × ℚ => min x.1 x.2) := ⟨LPBinary.Program.ratMin⟩
@[fun_prop] theorem rat_max : Poly (fun x : ℚ × ℚ => max x.1 x.2) := ⟨LPBinary.Program.ratMax⟩
@[fun_prop] theorem nat_add : Poly (fun x : ℕ × ℕ => x.1+x.2) := ⟨natAdd⟩
@[fun_prop] theorem nat_sub : Poly (fun x : ℕ × ℕ => x.1-x.2) := ⟨natSub⟩
@[fun_prop] theorem nat_mul : Poly (fun x : ℕ × ℕ => x.1*x.2) := ⟨natMul⟩
@[fun_prop] theorem nat_lt : Poly (fun x : ℕ × ℕ => decide (x.1<x.2)) := ⟨natLT⟩
@[fun_prop] theorem nat_le : Poly (fun x : ℕ × ℕ => decide (x.1≤x.2)) := ⟨natLE⟩
@[fun_prop] theorem nat_eq : Poly (fun x : ℕ × ℕ => decide (x.1=x.2)) := ⟨natEQ⟩
@[fun_prop] theorem bool_and : Poly (fun x : Bool × Bool => x.1 && x.2) := ⟨boolAnd⟩
@[fun_prop] theorem bool_or : Poly (fun x : Bool × Bool => x.1 || x.2) := ⟨boolOr⟩
@[fun_prop] theorem rat_neg : Poly (fun x : ℚ => -x) := ⟨ratNeg⟩
@[fun_prop] theorem bool_not : Poly (fun x : Bool => !x) := ⟨boolNot⟩
@[fun_prop] theorem rat_ofNat : Poly (fun x : ℕ => (x:ℚ)) := ⟨ratOfNat⟩
@[fun_prop] theorem rat_ofInt : Poly (fun x : ℤ => (x:ℚ)) := ⟨ratOfInt⟩

@[fun_prop] theorem list_length [Inhabited α] : Poly (List.length : List α → ℕ) := ⟨listLength enc default⟩
@[fun_prop] theorem list_indices [Inhabited α] : Poly (fun xs : List α => List.range xs.length) := ⟨listIndices enc default⟩
@[fun_prop] theorem list_getD (a0 : α) : Poly (fun x : List α × ℕ => x.1[x.2]?.getD a0) := ⟨listGetD enc a0⟩
@[fun_prop] theorem list_head (a0 : α) : Poly (fun xs : List α => xs.head?.getD a0) := ⟨listHead enc a0⟩
@[fun_prop] theorem list_tail [Inhabited α] : Poly (List.tail : List α → List α) := ⟨listTail enc default⟩
@[fun_prop] theorem list_empty : Poly (List.isEmpty : List α → Bool) := ⟨listIsEmpty enc⟩
@[fun_prop] theorem list_append [Inhabited α] : Poly (fun x : List α × List α => x.1++x.2) := ⟨listAppend enc default⟩
@[fun_prop] theorem list_cons : Poly (fun x : α × List α => x.1::x.2) := ⟨listCons enc⟩
@[fun_prop] theorem list_zip [Inhabited α] [Inhabited β] : Poly (fun x : List α × List β => x.1.zip x.2) := ⟨listZip enc enc default default⟩

end Poly
end MetricKMedian.Binary.Automatic
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseListTrim
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                      
section
namespace MetricKMedian.SparseIntegerLaw.BinarySparse
open Binary Binary.PolyProgram Function Finset
variable {α : Type}

def raw (μ : SparseIntegerLaw α) : Data α :=
  ((μ.law.denominator,List.ofFn μ.law.numerator),μ.states.toList)
end MetricKMedian.SparseIntegerLaw.BinarySparse
end

end OAI
end


