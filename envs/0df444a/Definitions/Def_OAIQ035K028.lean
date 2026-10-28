-- Prove2me | Definitions.Def_OAIQ035K028
-- name    : OAIQ035K028
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T07:58:45.52402+00:00
-- url     : https://prove2.me/theorems/7767eb71-5d18-4944-9795-2c8080b2c2fd
-- title:
--   Definitions bundle OAIQ035K028 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 42 declarations of OpenAI's Lean: 18 definitions and 24 theorems. The definitions and types are `OAI.MetricKMedian.Binary.BooleanLists.packProgram`, `OAI.MetricKMedian.Binary.BooleanLists.unpackProgram`, `OAI.MetricKMedian.Binary.IntegerList.em`, `OAI.MetricKMedian.Binary.IntegerList.er`, `OAI.MetricKMedian.Binary.Iteration.enc`, `OAI.MetricKMedian.Binary.ListFindIdx.enc`, `OAI.MetricKMedian.Binary.ListSplit.enc`, `OAI.MetricKMedian.Binary.ListSplit.out`, `OAI.MetricKMedian.Binary.ListZip.enc`, `OAI.MetricKMedian.Binary.PolyProgram.natAsList`, `OAI.MetricKMedian.Binary.PolyProgram.ratDen`, `OAI.MetricKMedian.Binary.PolyProgram.ratNonzero`, `OAI.MetricKMedian.Binary.PolyProgram.ratNum`, `OAI.MetricKMedian.Binary.PolyProgram.ratZero`, `OAI.MetricKMedian.Binary.PolyProgram.sumTag`, `OAI.MetricKMedian.Binary.PolyProgram.wordAsList`, `OAI.MetricKMedian.CopyState.roundAlive`, `OAI.MetricKMedian.LPBinary.er`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics/KMedian, in whole or in part: `KMedian_Binary_BinaryAutomatic`, `KMedian_Binary_BinaryBooleanLists`, `KMedian_Binary_BinaryDivision`, `KMedian_Binary_BinaryGCD`, `KMedian_Binary_BinaryIntegerHeight`, `KMedian_Binary_BinaryIterations`, `KMedian_Binary_BinaryListExtras`, `KMedian_Binary_BinaryListFold`, `KMedian_Binary_BinaryListIndex`, `KMedian_Binary_BinaryListIndices`, `KMedian_Binary_BinaryListSelection`, `KMedian_Binary_BinaryListZip`, `KMedian_Binary_BinaryPredicates`, `KMedian_Binary_BinaryRational`, `KMedian_Binary_BinaryRationalFold`, `KMedian_Binary_BinaryRationalHeight`, `KMedian_Binary_BooleanSum`, `KMedian_Compression_IntegerListProgram`, `KMedian_Optimization_LPListFacts`, `KMedian_Process_PhysicalRound`, `KMedian_Sparse_SparseTable`.
--
--   **Imports.** It imports the bundles `OAIQ035K013`, `OAIQ035K014` and `OAIQ035K015` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ035K038`, `OAIQ035K039`, `OAIQ035K040`, `OAIQ035K041`, `OAIQ035K043` and `OAIQ035K044`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/KMedian at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ035K013
import Definitions.Def_OAIQ035K014
import Definitions.Def_OAIQ035K015

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
-- module Solutions.OAIQ035_KM.KMedian_Binary_BinaryListExtras
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                        
section
namespace MetricKMedian.Binary
open Function Polynomial
namespace WordTransducer

theorem listBits_run (xs : List Bool) : listBits.run () xs=encodeList encodeBool xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
      change [true,b,false]++listBits.run () xs=quote [b]++encodeList encodeBool xs
      rw [ih]
      rfl
end WordTransducer
namespace PolyProgram
variable {α β γ : Type} {ea : α → List Bool} {eb : β → List Bool} {ec : γ → List Bool}
noncomputable def wordAsList : PolyProgram id (encodeList encodeBool) id :=
  WordTransducer.listBits.program.of_word (fun xs => WordTransducer.listBits_run xs)
noncomputable def natAsList : PolyProgram Nat.bits (encodeList encodeBool) Nat.bits :=
  wordAsList.recode Nat.bits (fun _ => rfl) (fun _ => rfl)
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

noncomputable def ratNum : PolyProgram Ratio.encode Signed.encode Rat.num :=
  (fst Signed.encode Nat.bits).recode Ratio.parts (fun _ => rfl) (fun _ => rfl)
noncomputable def ratDen : PolyProgram Ratio.encode Nat.bits Rat.den :=
  (snd Signed.encode Nat.bits).recode Ratio.parts (fun _ => rfl) (fun _ => rfl)
end PolyProgram
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

namespace Signed
 theorem encode_length (z : ℤ) : (encode z).length=3+z.natAbs.bits.length := by
  simp only [encode,parts,encodePair_length,encodeBool,List.length_singleton]

end Signed
namespace Ratio
 theorem encode_length (q : ℚ) : (encode q).length=7+2*q.num.natAbs.bits.length+q.den.bits.length := by
  simp only [encode,parts,encodePair_length,Signed.encode_length]
  omega
 theorem height_length (q : ℚ) : HasHeight q (encode q).length := by
  have hn := NatBinary.le_two_pow_length q.num.natAbs
  have hd := NatBinary.le_two_pow_length q.den
  have hlen := encode_length q
  have hnb : q.num.natAbs.bits.length ≤ (encode q).length := by omega
  have hdb : q.den.bits.length ≤ (encode q).length := by omega
  have hN := hn.trans (Nat.pow_le_pow_right (by decide : 1≤2) hnb)
  have hD := hd.trans (Nat.pow_le_pow_right (by decide : 1≤2) hdb)
  constructor
  · simpa only [Nat.cast_pow,Nat.cast_ofNat,Int.natCast_natAbs] using (Nat.cast_le (α:=ℤ)).mpr hN
  · simpa only [Nat.cast_pow,Nat.cast_ofNat] using (Nat.cast_le (α:=ℤ)).mpr hD
 theorem length_height {q : ℚ} {L : ℕ} (h : HasHeight q L) : (encode q).length ≤ 3*L+10 := by
  have hN : q.num.natAbs ≤ 2^L := (Nat.cast_le (α:=ℤ)).mp (by
    simpa only [Nat.cast_pow,Nat.cast_ofNat,Int.natCast_natAbs] using h.1)
  have hD : q.den ≤ 2^L := (Nat.cast_le (α:=ℤ)).mp (by
    simpa only [Nat.cast_pow,Nat.cast_ofNat] using h.2)
  have hnb := NatBinary.length_le_height hN
  have hdb := NatBinary.length_le_height hD
  rw [encode_length]
  omega
end Ratio
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
 theorem index_partial_size (ea : α → List Bool) (xs : List α) (x : ℕ × List ℕ) (pre suf : List α)
    (he : xs=pre++suf) :
    (encodePair Nat.bits (encodeList Nat.bits) (pre.foldl (fun b a => indexStep (b,a)) x)).length ≤
      10*((encodePair (encodeList ea) (encodePair Nat.bits (encodeList Nat.bits)) (xs,x)).length+1)^2 := by
  let L := (encodePair (encodeList ea) (encodePair Nat.bits (encodeList Nat.bits)) (xs,x)).length
  have hp : pre.length ≤ L := by
    have hp : (encodeList ea pre).length ≤ (encodeList ea xs).length := by rw [he,EncodedList.append,List.length_append]; omega
    have hh := EncodedList.length_le ea pre
    simp only [L,encodePair_length]; omega
  have hn : x.1.bits.length ≤ L := by simp only [L,encodePair_length]; omega
  have hb : (encodeList Nat.bits x.2).length ≤ L := by simp only [L,encodePair_length]; omega
  have hl : pre.length.bits.length ≤ pre.length+1 := NatBinary.length_le_height (Nat.lt_two_pow_self.le)
  have hc := NatBinary.add_length x.1 pre.length
  have hi : ∀ q∈List.range' x.1 pre.length, q.bits.length ≤ 2*L+2 := by
    intro q hq
    have hq' : q ≤ x.1+pre.length := (List.mem_range'_1.mp hq).2.le
    have hh := (NatBinary.length_mono hq').trans hc
    omega
  have hr := EncodedList.length_bound Nat.bits (List.range' x.1 pre.length) (2*L+2) hi
  simp only [List.length_range'] at hr
  have hcount : (x.1+pre.length).bits.length ≤ 2*L+2 := by omega
  have hr' : (encodeList Nat.bits (List.range' x.1 pre.length)).length ≤ L*(4*L+5) := by
    calc
      _ ≤ pre.length*(2*(2*L+2)+1) := hr
      _ ≤ L*(2*(2*L+2)+1) := Nat.mul_le_mul_right _ hp
      _ = L*(4*L+5) := by ring
  change (encodePair Nat.bits (encodeList Nat.bits) (pre.foldl (fun b a => indexStep (b,a)) (x.1,x.2))).length ≤ _
  rw [pushIndices]
  simp only [encodePair_length,EncodedList.append,List.length_append,EncodedList.reverse_length]
  simp only [L,encodePair_length] at hcount hr' hb
  nlinarith

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
abbrev enc : (List α × List β) × List (α × β) → List Bool :=
  encodePair (encodePair (encodeList ea) (encodeList eb)) (encodeList (encodePair ea eb))

 theorem run (as : List α) (bs : List β) (cs : List (α × β)) (S : ℕ)
    (hsize : (enc ea eb ((as,bs),cs)).length ≤ S) :
    ∃ t ≤ as.length+1, BoundedRun (enc ea eb) (body a0 b0) S t ((as,bs),cs) (result ((as,bs),cs)) := by
  induction as generalizing bs cs with
  | nil =>
      refine ⟨1,by simp,BoundedRun.stop hsize ?_⟩
      simp [body,result]
  | cons a as ih =>
      cases bs with
      | nil =>
          refine ⟨1,by simp,BoundedRun.stop hsize ?_⟩
          simp [body,result]
      | cons b bs =>
          have hs : (enc ea eb ((as,bs),(a,b)::cs)).length ≤ S := by
            simp only [enc,encodePair_length,EncodedList.cons_length] at hsize ⊢
            omega
          obtain ⟨t,ht,hr⟩ := ih bs ((a,b)::cs) hs
          refine ⟨t+1,by simpa only [List.length_cons] using Nat.succ_le_succ ht,?_⟩
          have he : result ((as,bs),(a,b)::cs)=result ((a::as,b::bs),cs) := by
            simp only [result,List.reverse_cons,List.zip_cons_cons,List.append_assoc,List.singleton_append]
          rw [← he]
          exact BoundedRun.step hsize (by simp [body]) hr

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
abbrev enc : List α × ℕ → List Bool := encodePair (encodeList ea) Nat.bits
 theorem run (as : List α) (n S : ℕ) (hsize : (enc ea (as,n)).length ≤ S) :
    ∃ t ≤ as.length+1, BoundedRun (enc ea) (body a0 p) S t (as,n) (result p (as,n)) := by
  induction as generalizing n with
  | nil =>
      refine ⟨1,by simp,BoundedRun.stop hsize ?_⟩
      simp [body,result]
  | cons a as ih =>
      cases hp : p a with
      | true =>
          refine ⟨1,by simp,BoundedRun.stop hsize ?_⟩
          simp [body,result,hp,List.findIdx_cons]
      | false =>
          have hn := NatBinary.add_length n 1
          have hs : (enc ea (as,n+1)).length ≤ S := by
            have hone : (1:ℕ).bits.length=1 := rfl
            rw [hone] at hn
            simp only [enc,encodePair_length,EncodedList.cons_length] at hsize ⊢
            omega
          obtain ⟨t,ht,hr⟩ := ih (n+1) hs
          refine ⟨t+1,by simpa only [List.length_cons] using Nat.succ_le_succ ht,?_⟩
          have he : result p (as,n+1)=result p (a::as,n) := by simp [result,List.findIdx_cons,hp,Nat.add_comm,Nat.add_left_comm]
          rw [← he]
          exact BoundedRun.step hsize (by simp [body,hp]) hr
end ListFindIdx
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
noncomputable def ratZero : PolyProgram Ratio.encode encodeBool (fun q => decide (q=0)) :=
  ((ratNum.comp intAbs).comp natZero).congr _ (fun q => by
    simp only [Function.comp_apply,Int.natAbs_eq_zero,Rat.num_eq_zero])
noncomputable def ratNonzero : PolyProgram Ratio.encode encodeBool (fun q => decide (q≠0)) :=
  (ratZero.comp boolNot).congr _ (fun q => by simp)
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
abbrev er := Binary.encodeList Binary.Ratio.encode
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

theorem of_program {f : α → β} (p : PolyProgram enc enc f) : Poly f := ⟨p⟩

end Poly
end MetricKMedian.Binary.Automatic
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Binary_BinaryBooleanLists
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.Binary
namespace BooleanLists
 theorem pack_run (xs : List Bool) : pack.run () xs=encodeList encodeBool xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih => simpa only [Transducer.run,pack,encodeList,encodeBool,quote,List.append_assoc,List.nil_append] using congrArg (fun ys => [true,b,false]++ys) ih
 theorem unpack_run (xs : List Bool) : unpack.run .start (encodeList encodeBool xs)=xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih => simpa only [encodeList,encodeBool,quote,List.cons_append,List.nil_append,Transducer.run,unpack,List.append_assoc,List.singleton_append] using congrArg (List.cons b) ih
noncomputable def packProgram : PolyProgram id (encodeList encodeBool) (id : List Bool → List Bool) :=
  pack.program.recode id (fun _ => rfl) (fun xs => pack_run xs)
noncomputable def unpackProgram : PolyProgram (encodeList encodeBool) id (id : List Bool → List Bool) :=
  unpack.program.recode (encodeList encodeBool) (fun _ => rfl) (fun xs => unpack_run xs)
 theorem length (xs : List Bool) : (encodeList encodeBool xs).length=3*xs.length := by
  induction xs with
  | nil => rfl
  | cons b xs ih => simp only [EncodedList.cons_length,encodeBool,List.length_cons,List.length_nil,ih]; omega
end BooleanLists
end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Binary_BinaryIntegerHeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.Binary.Signed
 theorem height_length (z : ℤ) : |z| ≤ (2:ℤ)^(encode z).length := by
  have h := NatBinary.le_two_pow_length z.natAbs
  have hl : z.natAbs.bits.length≤(encode z).length := by rw [encode_length]; omega
  have hh := h.trans (Nat.pow_le_pow_right (by decide : 1≤2) hl)
  simpa only [Nat.cast_pow,Nat.cast_ofNat,Int.natCast_natAbs] using (Nat.cast_le (α:=ℤ)).mpr hh
 theorem length_height {z : ℤ} {L : ℕ} (h : |z|≤(2:ℤ)^L) : (encode z).length≤L+4 := by
  have hN : z.natAbs≤2^L := (Nat.cast_le (α:=ℤ)).mp (by simpa only [Nat.cast_pow,Nat.cast_ofNat,Int.natCast_natAbs] using h)
  have hnb := NatBinary.length_le_height hN
  rw [encode_length]
  omega
end MetricKMedian.Binary.Signed
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Binary_BinaryIterations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                        
section
namespace MetricKMedian.Binary
open Function Polynomial
namespace Iteration
open PolyProgram
variable {α : Type}
def enc (ea : α → List Bool) := encodePair Nat.bits (encodePair ea (encodeList ea))

theorem state_size (ea : α → List Bool) (N A n : ℕ) (a : α) (bs : List α)
    (hn : n+bs.length≤N) (ha : (ea a).length≤A) (hb : ∀ b∈bs, (ea b).length≤A) :
    (enc ea (n,(a,bs))).length ≤ bound N A := by
  have hnl : n.bits.length≤N+1 := (NatBinary.length_le_height (Nat.lt_two_pow_self.le)).trans (by omega)
  have hbl := EncodedList.length_bound ea bs A hb
  have hbn : bs.length*(2*A+1) ≤ N*(2*A+1) := Nat.mul_le_mul_right _ (by omega)
  simp only [enc,encodePair_length,bound]
  omega

theorem run (ea : α → List Bool) (f : α → α) (N A n : ℕ) (a : α) (bs : List α)
    (hn : n+bs.length≤N)
    (ha : ∀ i≤n, (ea (f^[i] a)).length≤A)
    (hb : ∀ b∈bs, (ea b).length≤A) :
    BoundedRun (enc ea) (body f) (bound N A) (n+1) (n,(a,bs))
      (bs.reverse++iterates f a n) := by
  induction n generalizing a bs with
  | zero =>
      have has : (ea a).length≤A := by simpa using ha 0 (Nat.zero_le _)
      refine BoundedRun.stop (state_size ea N A 0 a bs hn has hb) ?_
      simp [body,iterates]
  | succ n ih =>
      have has : (ea a).length≤A := by simpa using ha 0 (Nat.zero_le _)
      have hs := state_size ea N A (n+1) a bs hn has hb
      have hh := ih (f a) (a::bs) (by simp only [List.length_cons]; omega)
        (fun i hi => by simpa only [Function.iterate_succ_apply] using ha (i+1) (by omega))
        (by intro b hm; rcases List.mem_cons.mp hm with rfl|hm; exact has; exact hb b hm)
      have he : (a::bs).reverse++iterates f (f a) n=bs.reverse++iterates f a (n+1) := by
        simp only [List.reverse_cons,iterates,List.append_assoc,List.singleton_append]
      rw [he] at hh
      exact BoundedRun.step hs (by simp [body]) hh
end Iteration

end MetricKMedian.Binary
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
namespace HasHeight
 theorem foldAdd (as : List ℚ) (b : ℚ) (L : ℕ) (hb : HasHeight b L) :
    HasHeight (as.foldl (·+·) b) (L+(encodeList Ratio.encode as).length) := by
  induction as generalizing b L with
  | nil => simpa only [List.foldl_nil,EncodedList.nil,List.length_nil,add_zero] using hb
  | cons a as ih =>
      have hh := ih (b+a) (L+(Ratio.encode a).length+1) (hb.add (Ratio.height_length a))
      simp only [List.foldl_cons,EncodedList.cons_length]
      exact hh.mono (by omega)
 theorem foldMul (as : List ℚ) (b : ℚ) (L : ℕ) (hb : HasHeight b L) :
    HasHeight (as.foldl (·*·) b) (L+(encodeList Ratio.encode as).length) := by
  induction as generalizing b L with
  | nil => simpa only [List.foldl_nil,EncodedList.nil,List.length_nil,add_zero] using hb
  | cons a as ih =>
      have hh := ih (b*a) (L+(Ratio.encode a).length) (hb.mul (Ratio.height_length a))
      simp only [List.foldl_cons,EncodedList.cons_length]
      exact hh.mono (by omega)
end HasHeight
end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Binary_BooleanSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                  
section
namespace MetricKMedian.Binary
open Function
namespace PolyProgram
variable {α β γ : Type} (ea : α → List Bool) (eb : β → List Bool)
noncomputable def sumTag : PolyProgram (encodeLoop eb ea) encodeBool Sum.isRight :=
  head.recode (encodeLoop eb ea) (fun _ => rfl) (fun x => by cases x <;> rfl)
end PolyProgram
end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Compression_IntegerListProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.Binary
open PolyProgram Function
namespace IntegerList
abbrev er := encodeList Signed.encode
abbrev em := encodeList er

end IntegerList
end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_PhysicalRound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.CopyState
open Finset PhysicalPotential FixedBatch
variable {F : Type*} [DecidableEq F] [Fintype F] {Δ : ℕ}

noncomputable def roundAlive (A S : Finset (Copy (F := F) Δ)) (G : A → Finset A)
    (H : Finset A) (Z : Finset (HeavyAction (graphActions G) H)) (x g : ℝ) (d : F → ℝ) :
    Finset (Copy (F := F) Δ) :=
  (nextAliveAt (heavyActions (graphActions G) H) (Analytic.coefficient x (mass g S))
    (fun i => d i.val.1) (localSet A S \ forcedAlive A S H) Z).image Subtype.val

end MetricKMedian.CopyState
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                   
section
namespace MetricKMedian.Binary
 theorem encodeList_map {α β : Type} (e : β → List Bool) (f : α → β) (xs : List α) :
    encodeList e (xs.map f)=encodeList (e ∘ f) xs := by
  induction xs with
  | nil => rfl
  | cons a as ih => simp only [List.map_cons,encodeList,ih,Function.comp_def]
end MetricKMedian.Binary

end

end OAI
end


