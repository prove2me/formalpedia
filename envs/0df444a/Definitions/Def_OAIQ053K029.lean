-- Prove2me | Definitions.Def_OAIQ053K029
-- name    : OAIQ053K029
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T05:59:15.150599+00:00
-- url     : https://prove2.me/theorems/62f8f62f-a132-43ce-87ae-fc43c1e42c1a
-- title:
--   Definitions bundle OAIQ053K029 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 39 declarations of OpenAI's Lean: 21 definitions and 18 theorems. The definitions and types are `OAI.MetricKMedian.Binary.BooleanLists.packProgram`, `OAI.MetricKMedian.Binary.BooleanLists.unpackProgram`, `OAI.MetricKMedian.Binary.IntegerList.em`, `OAI.MetricKMedian.Binary.IntegerList.er`, `OAI.MetricKMedian.Binary.Iteration.enc`, `OAI.MetricKMedian.Binary.PolyProgram.checkedProgram`, `OAI.MetricKMedian.Binary.PolyProgram.dependentIf`, `OAI.MetricKMedian.Binary.PolyProgram.dependentIfTotal`, `OAI.MetricKMedian.Binary.PolyProgram.natAsList`, `OAI.MetricKMedian.Binary.PolyProgram.sumElim`, `OAI.MetricKMedian.Binary.PolyProgram.sumLeft`, `OAI.MetricKMedian.Binary.PolyProgram.sumRight`, `OAI.MetricKMedian.Binary.PolyProgram.sumTag`, `OAI.MetricKMedian.Binary.PolyProgram.wordAsList`, `OAI.MetricKMedian.Complexity.FiniteComposition.PolyProgram.ofStock`, `OAI.MetricKMedian.Complexity.FiniteComposition.PolyProgram.withInput`, `OAI.MetricKMedian.FixedBatch.RationalParameters.radius`, `OAI.MetricKMedian.IntegerLaw.ListPivot.er`, `OAI.MetricKMedian.LPBinary.Nearest.ee`, `OAI.MetricKMedian.LPBinary.Nearest.ees`, `OAI.MetricKMedian.LPBinary.er`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedian_Binary_BinaryBooleanLists`, `KMedian_Binary_BinaryGuard`, `KMedian_Binary_BinaryGuardTotal`, `KMedian_Binary_BinaryIntegerHeight`, `KMedian_Binary_BinaryIterations`, `KMedian_Binary_BinaryListExtras`, `KMedian_Binary_BinaryListIndices`, `KMedian_Binary_BinaryListSelection`, `KMedian_Binary_BinaryListZip`, `KMedian_Binary_BinaryRationalFold`, `KMedian_Binary_BinaryRationalHeight`, `KMedian_Binary_BooleanSum`, `KMedian_Compression_IntegerListProgram`, `KMedian_Geometry_RationalGridRound`, `KMedian_Hardness_Composition`, `KMedian_Hardness_Threads`, `KMedian_Optimization_LPListFacts`, `KMedian_Programs_NearestListProgram`, `KMedian_Programs_PivotListProgram`, `KMedian_Sparse_SparseTable`.
--
--   **Imports.** It imports the bundles `OAIQ053K013`, `OAIQ053K014`, `OAIQ053K015` and `OAIQ053K016` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ053K038`, `OAIQ053K039`, `OAIQ053K040`, `OAIQ053K041` and `OAIQ053K042`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ053K013
import Definitions.Def_OAIQ053K014
import Definitions.Def_OAIQ053K015
import Definitions.Def_OAIQ053K016

section
-- module Solutions.OAIQ053_KM.KMedian_Binary_BinaryBooleanLists
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
-- module Solutions.OAIQ053_KM.KMedian_Binary_BinaryGuard
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                   
section
namespace MetricKMedian.Binary.PolyProgram
variable {α β : Type} {ea : α → List Bool} {eb : β → List Bool}

noncomputable def checkedProgram (p : α → Prop) [DecidablePred p]
    (P : PolyProgram ea encodeBool (fun a => decide (p a))) (a0 : {a // p a}) :
    PolyProgram ea (fun a : {a // p a} => ea a.val) (checked p a0) := by
  let raw : PolyProgram ea id ea := (identity ea).recode id (fun _ => rfl) (fun _ => rfl)
  let q := ite P (constant ea id (ea a0.val)) raw
  exact q.recode id (fun _ => rfl) (fun a => by
    by_cases h : p a
    · simp [checked,h]
    · simp [checked,h])

noncomputable def dependentIf (p : α → Prop) [DecidablePred p]
    (P : PolyProgram ea encodeBool (fun a => decide (p a)))
    (f : (a : α) → ¬p a → β) (g : (a : α) → p a → β)
    (F : PolyProgram (fun a : {a // ¬p a} => ea a.val) eb (fun a => f a.val a.property))
    (G : PolyProgram (fun a : {a // p a} => ea a.val) eb (fun a => g a.val a.property))
    (a0 : {a // ¬p a}) (a1 : {a // p a}) :
    PolyProgram ea eb (fun a => if h : p a then g a h else f a h) := by
  let notP := (P.comp boolNot).congr (fun a => decide (¬p a)) (fun a => by simp [Function.comp_apply])
  let FF := (checkedProgram (fun a => ¬p a) notP a0).comp F
  let GG := (checkedProgram p P a1).comp G
  exact (ite P FF GG).congr _ (fun a => by
    by_cases h : p a
    · simp [Function.comp_apply,checked,h]
    · simp [Function.comp_apply,checked,h])
end MetricKMedian.Binary.PolyProgram
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Binary_BinaryGuardTotal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                        
section
namespace MetricKMedian.Binary.PolyProgram
variable {α β : Type} {ea : α → List Bool} {eb : β → List Bool}
noncomputable def dependentIfTotal (p : α → Prop) [DecidablePred p]
    (P : PolyProgram ea encodeBool (fun a => decide (p a)))
    (f : (a : α) → ¬p a → β) (g : (a : α) → p a → β)
    (F : PolyProgram (fun a : {a // ¬p a} => ea a.val) eb (fun a => f a.val a.property))
    (G : PolyProgram (fun a : {a // p a} => ea a.val) eb (fun a => g a.val a.property)) :
    PolyProgram ea eb (fun a => if h : p a then g a h else f a h) := by
  classical
  by_cases h0 : Nonempty {a // ¬p a}
  · by_cases h1 : Nonempty {a // p a}
    · exact dependentIf p P f g F G h0.some h1.some
    · have h : ∀a, ¬p a := fun a ha => h1 ⟨⟨a,ha⟩⟩
      exact F.recode (fun a => ⟨a,h a⟩) (fun _ => rfl) (fun a => by simp only [dite_eq_right (h a)])
  · have h : ∀a, p a := fun a => by by_contra ha; exact h0 ⟨⟨a,ha⟩⟩
    exact G.recode (fun a => ⟨a,h a⟩) (fun _ => rfl) (fun a => by simp only [dite_eq_left (h a)])
end MetricKMedian.Binary.PolyProgram
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
-- module Solutions.OAIQ053_KM.KMedian_Binary_BinaryIntegerHeight
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
-- module Solutions.OAIQ053_KM.KMedian_Binary_BinaryIterations
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction
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
-- module Solutions.OAIQ053_KM.KMedian_Binary_BinaryListExtras
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
-- module Solutions.OAIQ053_KM.KMedian_Binary_BinaryListIndices
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
-- module Solutions.OAIQ053_KM.KMedian_Binary_BinaryListSelection
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction
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
-- module Solutions.OAIQ053_KM.KMedian_Binary_BinaryListZip
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction
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
-- module Solutions.OAIQ053_KM.KMedian_Binary_BinaryRationalFold
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
-- module Solutions.OAIQ053_KM.KMedian_Binary_BooleanSum
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction
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
noncomputable def sumLeft (a0 : α) : PolyProgram (encodeLoop eb ea) ea (fun x => x.elim id (fun _ => a0)) := by
  let raw := tail.recode (encodeLoop eb ea) (fun _ => rfl) (fun _ => rfl)
  let deflt := constant (encodeLoop eb ea) id (ea a0)
  refine (ite (sumTag ea eb) raw deflt).recode id (fun _ => rfl) ?_
  intro x
  cases x <;> rfl
noncomputable def sumRight (b0 : β) : PolyProgram (encodeLoop eb ea) eb (fun x => x.elim (fun _ => b0) id) := by
  let raw := tail.recode (encodeLoop eb ea) (fun _ => rfl) (fun _ => rfl)
  let deflt := constant (encodeLoop eb ea) id (eb b0)
  refine (ite (sumTag ea eb) deflt raw).recode id (fun _ => rfl) ?_
  intro x
  cases x <;> rfl
noncomputable def sumElim {ec : γ → List Bool} {f : α → γ} {g : β → γ}
    (F : PolyProgram ea ec f) (G : PolyProgram eb ec g) (a0 : α) (b0 : β) :
    PolyProgram (encodeLoop eb ea) ec (Sum.elim f g) :=
  (ite (sumTag ea eb) ((sumLeft ea eb a0).comp F) ((sumRight ea eb b0).comp G)).congr _
    (fun x => by cases x <;> rfl)
end PolyProgram
end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Compression_IntegerListProgram
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
-- module Solutions.OAIQ053_KM.KMedian_Geometry_RationalGridRound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                         
section
namespace MetricKMedian.FixedBatch.RationalParameters
open Finset PhysicalPotential CopyState RationalPhysicalKernel Completion.Rational
open Preparation.RationalNearest
variable {τ : ℝ} (q : RationalParameters τ)
variable {F X : Type} [LinearOrder F] [PseudoMetricSpace X] {j : ℕ}

attribute [local instance] OAI.MetricKMedian.FixedBatch.RationalParameters.rationalGridRoundCopyOrder
theorem nearest_nonempty (d : Fin j → F → ℚ) (A : Finset (Copy (F := F) q.Δ))
    (hA : q.Δ ≤ A.card) (c : Fin j) : (q.nearest d A c).Nonempty := by
  apply card_pos.mp
  change 0 < (takeNearest (fun a : Copy (F := F) q.Δ => d c a.1) q.Δ A).card
  rw [(takeNearest_spec (fun a : Copy (F := F) q.Δ => d c a.1) q.Δ A hA).2.1]
  exact q.Δpos

def radius (d : Fin j → F → ℚ) (A : Finset (Copy (F := F) q.Δ))
    (hA : q.Δ ≤ A.card) (c : Fin j) : ℚ :=
  ((q.nearest d A c).image (fun a => d c a.1)).max' ((q.nearest_nonempty d A hA c).image _)

end MetricKMedian.FixedBatch.RationalParameters
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Optimization_LPListFacts
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
-- module Solutions.OAIQ053_KM.KMedian_Programs_NearestListProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.LPBinary
open Binary Binary.PolyProgram Function Finset

namespace Nearest
abbrev ee := encodePair Nat.bits (encodePair Ratio.encode Ratio.encode)
abbrev ees := encodeList ee

end Nearest
end MetricKMedian.LPBinary
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_PivotListProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                        
section
namespace MetricKMedian.IntegerLaw.ListPivot
open Binary Binary.PolyProgram Function Finset
abbrev er := Binary.IntegerList.er

end MetricKMedian.IntegerLaw.ListPivot
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseTable
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

section
-- module Solutions.OAIQ053_KM.KMedian_Hardness_Composition
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPInherited

namespace MetricKMedian.Complexity.FiniteComposition
open Turing Function Finset Polynomial
open Binary (Trace)

attribute [instance] Machine.decK Machine.finK Machine.finΓ Machine.finLabel Machine.finState

namespace PolyProgram
variable {α β γ : Type} {ea : α → List Bool} {eb : β → List Bool} {ec : γ → List Bool}
variable {f : α → β} {g : β → γ}

noncomputable def ofStock (p : TM2ComputableInPolyTime ea eb f)
    (h : ∀ k : p.tm.K, Finite (p.tm.Γ k)) : PolyProgram ea eb f where
  machine := stockMachine p h
  time := p.time
  outputs a := by
    let ht := p.outputsFun a
    refine ⟨ht.steps, ht.steps_le_m, ?_⟩
    rw [← Machine.init_eq, ← Machine.halt_eq]
    exact Trace.of_iterate ht.evals_in_steps

end PolyProgram

end MetricKMedian.Complexity.FiniteComposition

end Inline_PCPInherited

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Hardness_Threads
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPInherited

namespace MetricKMedian.Complexity.FiniteComposition
open Turing Function Polynomial
open Binary (Trace quote quote_length polynomial_eval_mono)

namespace PolyProgram
variable {α β γ : Type} {ea : α → List Bool} {eb : β → List Bool} {ec : γ → List Bool} {f : α → β}

noncomputable def withInput (P : PolyProgram ea eb f) :
    PolyProgram ea (Binary.encodePair eb ea) (fun a => (f a,a)) :=
  let d := Binary.PolyProgram.duplicate ea
  ((ofStock d.stock d.finite_work).comp (P.thread ea)).congr _ (fun _ => rfl)

end PolyProgram
end MetricKMedian.Complexity.FiniteComposition

end Inline_PCPInherited

end OAI
end


