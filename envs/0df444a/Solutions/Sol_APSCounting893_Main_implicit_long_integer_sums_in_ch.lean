-- Prove2me | solution 1 for APSCounting893.Main.implicit_long_integer_sums_in_ch
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T22:03:15.216463+00:00
-- url     : https://prove2.me/submissions/ab08e9f9-45ea-43c1-877e-12e268843d23

import Definitions.Def_APSCounting893_Main_BinaryOracleArithmetic
import Definitions.Def_APSCounting893_Main_CountingHierarchy
import Definitions.Def_APSCounting893_Main_ImplicitCountingArithmetic
import Definitions.Def_APSCounting893_Main_LongSumCarryMachine
import Definitions.Def_APSCounting893_Main_OracleProofPrimitives
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_BitString
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Nat_Binary
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Nat_BinaryDiv
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Decoder_Nat
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Frame_Basic
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Length
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Nat_Words
import Mathlib
import Theorems.Thm_APSCounting893_Main_bounded_majority_oracle_pp
import Theorems.Thm_APSCounting893_Main_bounded_quantification_oracle_pp
import Theorems.Thm_APSCounting893_Main_native_long_sum_carry_query
import Theorems.Thm_APSCounting893_Main_native_polynomial_oracle_preimage
import Theorems.Thm_APSCounting893_Main_short_natural_graph_from_bits
import Theorems.Thm_APSCounting893_Main_stack_program_polynomial_simulation
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

section Component_0
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

def fastUnaryPrefix (w : Word) : Option (ℕ × Word):=
  let n:=w.idxOf false
  if n<w.length then some (n,w.drop (n+1)) else none

lemma fastUnaryPrefix_eq_readUnary (w : Word) : fastUnaryPrefix w=readUnary w := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    cases b with
    | false => simp [fastUnaryPrefix,readUnary]
    | true =>
      unfold fastUnaryPrefix at ih ⊢
      simp only [List.idxOf_cons_ne w (show (true:Bool)≠false by decide),List.length_cons]
      rw [readUnary,←ih]
      by_cases h : w.idxOf false<w.length
      · simp [h,List.drop_succ_cons]
      · simp [h,List.drop_succ_cons]

lemma native_fastUnaryPrefix :
    Turing.MultiTapeTM.ComputableTidilyInPolyTime fastUnaryPrefix Turing.MultiTapeTM.encBits
      (Turing.MultiTapeTM.encOption (Turing.MultiTapeTM.encPair Turing.MultiTapeTM.encUnary Turing.MultiTapeTM.encBits)) := by
  open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime in
  have hlist := bitsToList
  open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime in
  have hidx : ComputableTidilyInPolyTime (fun w : Word=>w.idxOf false) encBits encUnary :=
    (idxOf encBool).comp (hlist.prod (const false))
  open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime in
  have hlen : ComputableTidilyInPolyTime (fun w : Word=>w.length) encBits encUnary:=length_bits
  open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime in
  have hnext := unary_add.comp (hidx.prod (const 1))
  open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime in
  have hrest := bitsDropWithInput (id' (encIn:=encBits)) hnext
  open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime in
  have hguard := binary_lt' (unary_to_binary.comp hidx) (unary_to_binary.comp hlen)
  open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime in
  have hsome := (optionSome (encPair encUnary encBits)).comp (hidx.prod hrest)
  open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime in
  exact hguard.ite_decide hsome (const none)

end APSCounting893.Main
end Component_0

section Component_1
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime

lemma apsCanonicalBits_append_singleton (w : Word) (b : Bool) : canonicalBits (w++[b])=b := by
  induction w with
  | nil => rfl
  | cons a w ih => cases w with
    | nil => rfl
    | cons c w => exact ih

lemma apsCanonicalBits_reverse_getD (w : Word) : canonicalBits w=w.reverse.getD 0 true := by
  induction w using List.reverseRecOn with
  | nil => rfl
  | append_singleton w b ih => simp [apsCanonicalBits_append_singleton]

lemma native_apsCanonicalBits : ComputableTidilyInPolyTime canonicalBits encBits encBool := by
  have hh:=bitsGetDWithInput bitsReverse (const 0) true
  apply hh.of_enc_eq
  intro w
  rw [apsCanonicalBits_reverse_getD]


def fastBinaryPayload (p : ℕ × Word) : Option (ℕ × Word):=
  if p.1≤p.2.length then
    if canonicalBits (p.2.take p.1) then some (ofBits (p.2.take p.1),p.2.drop p.1) else none
  else none

lemma native_fastBinaryPayload : ComputableTidilyInPolyTime fastBinaryPayload
    (encPair encUnary encBits) (encOption (encPair encNat encBits)) := by
  have hn:=fst encUnary encBits
  have hw:=snd encUnary encBits
  have hlength:=length_bits.comp hw
  have hguard:=binary_le' (unary_to_binary.comp hn) (unary_to_binary.comp hlength)
  have htake:=bitsTakeWithInput hw hn
  have hdrop:=bitsDropWithInput hw hn
  have hvalue:=bitsToNat.comp htake
  have hcanon:=native_apsCanonicalBits.comp htake
  have hsome:=(optionSome (encPair encNat encBits)).comp (hvalue.prod hdrop)
  have hinner:=hcanon.cond hsome (const none)
  exact hguard.ite_decide hinner (const none)

lemma fastBinaryPayload_eq (p : ℕ × Word) : fastBinaryPayload p=
    if p.1≤p.2.length then
      if canonicalBits (p.2.take p.1) then some (bitsValue (p.2.take p.1),p.2.drop p.1) else none
    else none := rfl

end APSCounting893.Main
end Component_1

section Component_2
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime

lemma native_decodeNat : ComputableTidilyInPolyTime decodeNat encBits
    (encOption (encPair encNat encBits)) := by
  have hbody:=native_fastBinaryPayload.comp (snd encBits (encPair encUnary encBits))
  have hh:=optionElimWithInput (body:=fun (_ : Word) (p : ℕ × Word)=>fastBinaryPayload p)
    native_fastUnaryPrefix (const (none : Option (ℕ × Word))) hbody
  apply hh.of_enc_eq
  intro w
  rw [fastUnaryPrefix_eq_readUnary]
  unfold decodeNat
  cases hp : readUnary w with
  | none => rfl
  | some p =>
    simp only [Option.elim_some,fastBinaryPayload_eq]
    rfl

end APSCounting893.Main
end Component_2

section Component_3
set_option autoImplicit false
set_option maxHeartbeats 4000000

section CodecPart_0

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma unaryPrefix_append_injective (a b : ℕ) (u v : Word)
    (h : List.replicate a true ++ false :: u = List.replicate b true ++ false :: v) :
    a = b ∧ u = v := by
  induction a generalizing b with
  | zero =>
      cases b with
      | zero => simpa using h
      | succ b => simp [List.replicate_succ] at h
  | succ a ih =>
      cases b with
      | zero => simp [List.replicate_succ] at h
      | succ b =>
          simp only [List.replicate_succ, List.cons_append, List.cons.injEq, true_and] at h
          obtain ⟨hab, huv⟩ := ih b h
          exact ⟨congrArg Nat.succ hab, huv⟩

lemma nat_bits_fold (n : ℕ) : n.bits.foldr Nat.bit 0 = n := by
  induction n using Nat.binaryRec' with
  | zero => rfl
  | bit b n hn ih => simp only [Nat.bits_append_bit n b hn, List.foldr_cons, ih]

lemma encodeNat_append_injective (a b : ℕ) (u v : Word)
    (h : encodeNat a ++ u = encodeNat b ++ v) : a = b ∧ u = v := by
  have hh : List.replicate a.bits.length true ++ false :: (a.bits ++ u) =
      List.replicate b.bits.length true ++ false :: (b.bits ++ v) := by
    simpa only [encodeNat, List.append_assoc, List.singleton_append, List.cons_append, List.nil_append] using h
  obtain ⟨hlen, hsuffix⟩ := unaryPrefix_append_injective _ _ _ _ hh
  have hbits : a.bits = b.bits := by
    have ht := congrArg (List.take a.bits.length) hsuffix
    rw [List.take_left] at ht
    rwa [hlen, List.take_left] at ht
  have hab : a = b := by
    have ht := congrArg (List.foldr Nat.bit 0) hbits
    simpa only [nat_bits_fold] using ht
  subst b
  exact ⟨rfl, List.append_cancel_left hsuffix⟩

lemma encodeNatList_append_injective (l l' : List ℕ) (u v : Word)
    (h : encodeList encodeNat l ++ u = encodeList encodeNat l' ++ v) : l = l' ∧ u = v := by
  have hh : encodeNat l.length ++ (l.flatMap encodeNat ++ u) =
      encodeNat l'.length ++ (l'.flatMap encodeNat ++ v) := by simpa only [encodeList, List.append_assoc] using h
  obtain ⟨hlen, hsuffix⟩ := encodeNat_append_injective _ _ _ _ hh
  clear h hh
  induction l generalizing l' with
  | nil =>
      have hl' : l' = [] := List.length_eq_zero_iff.mp hlen.symm
      subst l'
      exact ⟨rfl, hsuffix⟩
  | cons a l ih =>
      cases l' with
      | nil => simp at hlen
      | cons b l' =>
          have hh : encodeNat a ++ (l.flatMap encodeNat ++ u) =
              encodeNat b ++ (l'.flatMap encodeNat ++ v) := by
            simpa only [List.flatMap_cons, List.append_assoc] using hsuffix
          obtain ⟨hab, hs⟩ := encodeNat_append_injective _ _ _ _ hh
          obtain ⟨hll, huv⟩ := ih l' (Nat.succ.inj hlen) hs
          exact ⟨congrArg₂ List.cons hab hll, huv⟩

lemma coefficientPart_append_injective (p p' : CoefficientPart) (u v : Word)
    (h : p.encode ++ u = p'.encode ++ v) : p = p' ∧ u = v := by
  cases p <;> cases p' <;> simp_all [CoefficientPart.encode]

lemma coefficientQuery_injective {k : ℕ}
    (x x' : Word) (e e' : Fin (k + 1) →₀ ℕ) (part part' : CoefficientPart) (q q' : ℕ)
    (h : coefficientQuery x e part q = coefficientQuery x' e' part' q') :
    x = x' ∧ e = e' ∧ part = part' ∧ q = q' := by
  have hh := encodeNat_append_injective x.length x'.length
    (x ++ encodeList encodeNat (List.ofFn (fun i => e i)) ++ part.encode ++ encodeNat q)
    (x' ++ encodeList encodeNat (List.ofFn (fun i => e' i)) ++ part'.encode ++ encodeNat q')
    (by simpa only [coefficientQuery, List.append_assoc] using h)
  have hx : x = x' := by
    have ht := congrArg (List.take x.length) hh.2
    simp only [List.append_assoc] at ht
    rw [List.take_left] at ht
    rwa [hh.1, List.take_left] at ht
  subst x'
  have hs := List.append_cancel_left (show
    x ++ (encodeList encodeNat (List.ofFn (fun i => e i)) ++ part.encode ++ encodeNat q) =
    x ++ (encodeList encodeNat (List.ofFn (fun i => e' i)) ++ part'.encode ++ encodeNat q') from
      by simpa only [List.append_assoc] using hh.2)
  obtain ⟨helist, hs⟩ := encodeNatList_append_injective _ _
    (part.encode ++ encodeNat q) (part'.encode ++ encodeNat q')
    (by simpa only [List.append_assoc] using hs)
  have he : e = e' := by
    apply Finsupp.ext
    intro i
    exact congrFun (List.ofFn_injective helist) i
  obtain ⟨hpart, hq⟩ := coefficientPart_append_injective _ _ _ _ hs
  have hq' : q = q' := (encodeNat_append_injective q q' [] [] (by simpa using hq)).1
  exact ⟨rfl, he, hpart, hq'⟩

lemma coefficientBitLanguage_query_iff {k : ℕ} (rho : CoefficientRepresentation k)
    (x : Word) (e : Fin (k + 1) →₀ ℕ) (part : CoefficientPart) (q : ℕ) :
    CoefficientBitLanguage rho (coefficientQuery x e part q) ↔ representationBit (rho x e) part q = true := by
  constructor
  · rintro ⟨x', e', part', q', h, hb⟩
    obtain ⟨hx, he, hp, hq⟩ := coefficientQuery_injective _ _ _ _ _ _ _ _ h
    subst x'; subst e'; subst part'; subst q'
    exact hb
  · intro h
    exact ⟨x, e, part, q, rfl, h⟩

end APSCounting893.Main
end CodecPart_0

section CodecPart_1

set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace APSCounting893.Main

def incrementBits : Word → Word
  | [] => [true]
  | false :: w => true :: w
  | true :: w => false :: incrementBits w

lemma incrementBits_length_le (w : Word) : (incrementBits w).length ≤ w.length + 1 := by
  induction w with
  | nil => rfl
  | cons b w ih => cases b <;> simp [incrementBits] <;> omega

lemma incrementBits_nat_bits (n : ℕ) : incrementBits n.bits = (n + 1).bits := by
  induction n using Nat.binaryRec' with
  | zero => rfl
  | bit b n hn ih =>
      cases b with
      | false =>
          rw [Nat.bits_append_bit n false hn]
          have heq : Nat.bit false n + 1 = Nat.bit true n := by simp [Nat.bit_val]
          rw [heq, Nat.bits_append_bit n true (by intro; rfl)]
          rfl
      | true =>
          rw [Nat.bits_append_bit n true hn]
          change false :: incrementBits n.bits = _
          rw [ih]
          have heq : Nat.bit true n + 1 = Nat.bit false (n + 1) := by simp [Nat.bit_val]; omega
          rw [heq, Nat.bits_append_bit (n + 1) false (by intro h; omega)]

lemma incrementBits_ne_nil (w : Word) : incrementBits w ≠ [] := by
  cases w with
  | nil => decide
  | cons b w => cases b <;> simp [incrementBits]

lemma canonicalBits_tail (b : Bool) (w : Word) (h : canonicalBits (b :: w) = true) :
    canonicalBits w = true := by
  cases w <;> simpa [canonicalBits] using h

lemma bitsValue_pos_of_canonical {w : Word} (h : canonicalBits w = true) (hne : w ≠ []) :
    0 < bitsValue w := by
  induction w with
  | nil => exact (hne rfl).elim
  | cons b w ih =>
      cases w with
      | nil =>
          have hb : b = true := h
          subst b
          decide
      | cons c w =>
          have ht : 0 < bitsValue (c :: w) := ih (canonicalBits_tail b _ h) (by simp)
          cases b <;> simp only [bitsValue, List.foldr_cons, Nat.bit_val] at ht ⊢ <;> omega

lemma bitsValue_bits_of_canonical (w : Word) (h : canonicalBits w = true) :
    (bitsValue w).bits = w := by
  induction w with
  | nil => rfl
  | cons b w ih =>
      have hw := canonicalBits_tail b w h
      change (Nat.bit b (bitsValue w)).bits = b :: w
      rw [Nat.bits_append_bit (bitsValue w) b]
      · rw [ih hw]
      · intro hn
        by_cases hz : w = []
        · subst w
          exact h
        · exact ((bitsValue_pos_of_canonical hw hz).ne' hn).elim

lemma canonicalBits_nat_bits (n : ℕ) : canonicalBits n.bits = true := by
  induction n using Nat.binaryRec' with
  | zero => rfl
  | bit b n hn ih =>
      rw [Nat.bits_append_bit n b hn]
      by_cases hz : n = 0
      · subst n
        exact hn rfl
      · have hnil : n.bits ≠ [] := by
          intro heq
          have hv := nat_bits_fold n
          rw [heq] at hv
          exact hz hv.symm
        cases hw : n.bits with
        | nil => exact (hnil hw).elim
        | cons c w => simpa [canonicalBits, hw] using ih

lemma canonicalBits_append_singleton (w : Word) (b : Bool) : canonicalBits (w ++ [b]) = b := by
  induction w with
  | nil => rfl
  | cons a w ih =>
      cases w with
      | nil => rfl
      | cons c w => exact ih

lemma canonicalBits_eq_reverse_headD (w : Word) : canonicalBits w = w.reverse.headD true := by
  induction w using List.reverseRecOn with
  | nil => rfl
  | append_singleton w b ih => simp [canonicalBits_append_singleton]

lemma nat_bits_reverse_head (n : ℕ) : n.bits.reverse.headD true = true := by
  rw [← canonicalBits_eq_reverse_headD, canonicalBits_nat_bits]

end APSCounting893.Main
end CodecPart_1

section CodecPart_2

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
namespace APSCounting893.Main

lemma readUnary_code (k : ℕ) (rest : Word) :
    readUnary (List.replicate k true ++ false :: rest) = some (k, rest) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [List.replicate_succ, List.cons_append, readUnary, ih, Option.map_some]

lemma readUnary_inverse (w : Word) (k : ℕ) (rest : Word) (h : readUnary w = some (k, rest)) :
    w = List.replicate k true ++ false :: rest := by
  induction w generalizing k rest with
  | nil => simp [readUnary] at h
  | cons b w ih =>
      cases b with
      | false =>
          have heq : (0, w) = (k, rest) := by simpa [readUnary] using h
          cases heq
          rfl
      | true =>
          cases hw : readUnary w with
          | none => simp [readUnary, hw] at h
          | some p =>
              have heq : (p.1 + 1, p.2) = (k, rest) := by simpa [readUnary, hw] using h
              obtain ⟨hk, hr⟩ := Prod.mk.inj heq
              subst k
              rw [← hr, ih p.1 p.2 hw]
              simp [List.replicate_succ]

lemma decodeNat_code (n : ℕ) (rest : Word) : decodeNat (encodeNat n ++ rest) = some (n, rest) := by
  have hw : encodeNat n ++ rest = List.replicate n.bits.length true ++ false :: (n.bits ++ rest) := by
    simp [encodeNat, List.append_assoc]
  rw [hw]
  simp [decodeNat, readUnary_code, List.take_left, canonicalBits_nat_bits, bitsValue, nat_bits_fold]

lemma decodeNat_inverse (w : Word) (n : ℕ) (rest : Word) (h : decodeNat w = some (n, rest)) :
    w = encodeNat n ++ rest := by
  cases hu : readUnary w with
  | none => simp [decodeNat, hu] at h
  | some p =>
      have hw := readUnary_inverse w p.1 p.2 hu
      by_cases hlen : p.1 ≤ p.2.length
      · by_cases hc : canonicalBits (p.2.take p.1) = true
        · have heq : (bitsValue (p.2.take p.1), p.2.drop p.1) = (n, rest) := by
            simpa [decodeNat, hu, hlen, hc] using h
          obtain ⟨hn, hr⟩ := Prod.mk.inj heq
          have hb : n.bits = p.2.take p.1 := by rw [← hn]; exact bitsValue_bits_of_canonical _ hc
          have hk : n.bits.length = p.1 := by rw [hb, List.length_take, Nat.min_eq_left hlen]
          rw [hw]
          simp only [encodeNat, hk]
          rw [hb, ← hr]
          simp [List.append_assoc]
        · simp [decodeNat, hu, hlen, hc] at h
      · simp [decodeNat, hu, hlen] at h

lemma readUnary_none_iff (w : Word) : readUnary w = none ↔ w = List.replicate w.length true := by
  induction w with
  | nil => simp [readUnary]
  | cons b w ih =>
      cases b with
      | false => simp [readUnary, List.replicate_succ]
      | true => simpa [readUnary, List.replicate_succ] using ih

lemma readUnary_length (w : Word) (k : ℕ) (rest : Word) (h : readUnary w = some (k, rest)) :
    w.length = k + 1 + rest.length := by
  rw [readUnary_inverse w k rest h]
  simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

end APSCounting893.Main
end CodecPart_2
end Component_3

section Component_4
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace APSCounting893.Main
open Cslib.BitString
open Turing.MultiTapeTM

lemma ofBits_eq_lsbValue (w : Word) : ofBits w=lsbValue w := by
  exact (lsbValue_eq_foldr_bit w).symm

lemma words_below_threshold_ncard (s t : ℕ) (ht : t ≤ 2^s) :
    Set.ncard {w : Word | w.length=s ∧ ofBits w<t}=t := by
  have he : {w : Word | w.length=s ∧ ofBits w<t}=
      lowBits s '' {n : ℕ | n<t} := by
    ext w
    constructor
    · rintro ⟨hlen,hval⟩
      refine ⟨ofBits w,hval,?_⟩
      rw [ofBits_eq_lsbValue,←hlen,lowBits_lsbValue]
    · rintro ⟨n,hn,rfl⟩
      refine ⟨length_lowBits _ _,?_⟩
      rw [ofBits_eq_lsbValue,lsbValue_lowBits (hn.trans_le ht)]
      exact hn
  have hi : Set.InjOn (lowBits s) {n : ℕ | n<t} := by
    intro n hn m hm he
    have hv := congrArg lsbValue he
    simpa only [lsbValue_lowBits (hn.trans_le ht),lsbValue_lowBits (hm.trans_le ht)] using hv
  rw [he,hi.ncard_image]
  have hr : {n : ℕ | n<t}=(Finset.range t : Set ℕ) := by ext n;simp
  rw [hr]
  simp

lemma words_fixed_length_ncard (s : ℕ) : Set.ncard {w : Word | w.length=s}=2^s := by
  have he : {w : Word | w.length=s}={w : Word | w.length=s ∧ ofBits w<2^s} := by
    ext w
    constructor
    · intro h
      have hlen : w.length=s := h
      exact ⟨h,by simpa only [hlen,ofBits] using Nat.foldr_bit_lt w⟩
    · exact And.left
  rw [he,words_below_threshold_ncard s (2^s) le_rfl]

lemma words_at_least_threshold_ncard (s t : ℕ) :
    Set.ncard {w : Word | w.length=s ∧ t≤ofBits w}=2^s-t := by
  classical
  let U : Set Word := {w | w.length=s}
  let V : Set Word := {w | w.length=s ∧ ofBits w<t}
  have hu : U.Finite := by
    apply Set.finite_of_ncard_ne_zero
    apply Nat.ne_of_gt
    rw [show U={w : Word | w.length=s} by rfl,words_fixed_length_ncard]
    positivity
  have hv : V ⊆ U := fun _ h => h.1
  have he : {w : Word | w.length=s ∧ t≤ofBits w}=U\V := by ext w;simp [U,V];omega
  rw [he,Set.ncard_sdiff hv (hu.subset hv),show U={w : Word | w.length=s} by rfl,words_fixed_length_ncard]
  by_cases ht : t≤2^s
  · rw [show V={w : Word | w.length=s ∧ ofBits w<t} by rfl,words_below_threshold_ncard s t ht]
  · have hV : V=U := by
      ext w
      constructor
      · exact fun h => h.1
      · intro h;refine ⟨h,?_⟩
        have hlen : w.length=s := h
        have hb : ofBits w<2^s := by simpa only [hlen,ofBits] using Nat.foldr_bit_lt w
        omega
    rw [hV,show U={w : Word | w.length=s} by rfl,words_fixed_length_ncard]
    omega

end APSCounting893.Main
end Component_4

section Component_5
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace APSCounting893.Main
open Turing.MultiTapeTM

lemma naturalBitQuery_correct (F : Word → ℕ) (x : Word) (q : ℕ) :
    NaturalBitLanguage F (naturalBitQuery x q) ↔ (F x).testBit q=true := by
  constructor
  · rintro ⟨y,r,he,hbit⟩
    have hframe := Turing.MultiTapeTM.frame_append_inj he
    have hy : x=y := hframe.1
    have hq : q=r := (encodeNat_append_injective q r [] [] (by simpa only [List.append_nil] using hframe.2)).1
    simpa only [hy,hq] using hbit
  · intro h;exact ⟨x,q,rfl,h⟩

end APSCounting893.Main
end Component_5

section Component_6
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.constructorNameAsVariable false
namespace APSCounting893.Main
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime Cslib.BitString
lemma native_parseNaturalBitQuery : ComputableTidilyInPolyTime parseNaturalBitQuery encBits
    (encOption (encPair encBits encNat)) := by
  have hdecode := native_decodeNat.comp ComputableTidilyInPolyTime.dropFrame
  have hs := fst encBits (encPair encNat encBits)
  have hqr := snd encBits (encPair encNat encBits)
  have htail := decide_eq' hqr.snd' (const [])
  have hcode := bitsAppend ((bitsFrame encBits).comp (ComputableTidilyInPolyTime.unframe.comp hs))
    (ComputableTidilyInPolyTime.dropFrame.comp hs)
  have hguard := decide_and htail (decide_eq' hs hcode)
  have hresult := (optionSome (encPair encBits encNat)).comp
    ((ComputableTidilyInPolyTime.unframe.comp hs).prod hqr.fst')
  have hbody := ite_decide hguard hresult (const (none : Option (Word × ℕ)))
  have hh := optionElimWithInput
    (body:=fun (z : Word) (qr : ℕ × Word) =>
      if qr.2=[] ∧ z=Turing.MultiTapeTM.frame (Turing.MultiTapeTM.unframe z)++Turing.MultiTapeTM.dropFrame z
        then some (Turing.MultiTapeTM.unframe z,qr.1) else none)
    hdecode (const (none : Option (Word × ℕ))) hbody
  apply hh.of_enc_eq
  intro z
  unfold parseNaturalBitQuery
  dsimp only [Function.comp_apply]
  cases decodeNat (Turing.MultiTapeTM.dropFrame z) <;> rfl

lemma parseNaturalBitQuery_code (x : Word) (q : ℕ) :
    parseNaturalBitQuery (naturalBitQuery x q)=some (x,q) := by
  simp only [parseNaturalBitQuery,naturalBitQuery,unframe_frame_append,dropFrame_frame_append]
  have hd : decodeNat (encodeNat q)=some (q,[]) := by simpa only [List.append_nil] using decodeNat_code q []
  rw [hd]
  simp

lemma parseNaturalBitQuery_inverse (z x : Word) (q : ℕ)
    (hp : parseNaturalBitQuery z=some (x,q)) : z=naturalBitQuery x q := by
  unfold parseNaturalBitQuery at hp
  cases hd : decodeNat (Turing.MultiTapeTM.dropFrame z) with
  | none => simp only [hd,Option.bind_none] at hp;cases hp
  | some qr =>
    simp only [hd,Option.bind_some] at hp
    by_cases h : qr.2=[] ∧ z=Turing.MultiTapeTM.frame (Turing.MultiTapeTM.unframe z)++Turing.MultiTapeTM.dropFrame z
    · rw [if_pos h] at hp
      have heq : (Turing.MultiTapeTM.unframe z,qr.1)=(x,q) := Option.some.inj hp
      have hx : Turing.MultiTapeTM.unframe z=x := congrArg Prod.fst heq
      have hq : qr.1=q := congrArg Prod.snd heq
      have ht := decodeNat_inverse _ _ _ hd
      rw [h.1,List.append_nil] at ht
      unfold naturalBitQuery
      calc
        z=Turing.MultiTapeTM.frame (Turing.MultiTapeTM.unframe z)++Turing.MultiTapeTM.dropFrame z := h.2
        _=Turing.MultiTapeTM.frame x++encodeNat q := by rw [hx,ht,hq]
    · rw [if_neg h] at hp
      cases hp
end APSCounting893.Main
end Component_6

section Component_7
set_option autoImplicit false
namespace APSCounting893.Main
lemma native_longSumMatrixQuery (a b : ℕ) :
    Turing.MultiTapeTM.ComputableTidilyInPolyTime (longSumMatrixQuery a b)
      Turing.MultiTapeTM.encBits Turing.MultiTapeTM.encBits :=
  native_long_sum_carry_query a b
end APSCounting893.Main
end Component_7

section Component_8

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
namespace APSCounting893.Main

noncomputable def haltMachine (b : Bool) : OracleMachine where
  states := 1
  alphabet := 0
  tapes := 4
  inputTape := 0
  randomTape := 1
  queryTape := 2
  outputTape := 3
  distinctTapes := by decide
  initial := 0
  transition := fun _ _ => .halt b

lemma haltMachine_answer_one (b : Bool) (A : Language) (x w : Word) :
    (machineRun (haltMachine b) A x w 1).answer = some b := rfl

lemma constant_inOracleP (A : Language) (b : Bool) : InOracleP A (fun _ => b = true) := by
  refine ⟨haltMachine b, 1, 0, ?_⟩
  intro x
  exact ⟨b, haltMachine_answer_one b A x [], Iff.rfl⟩

lemma constant_inOraclePP (A : Language) (b : Bool) : InOraclePP A (fun _ => b = true) := by
  refine ⟨haltMachine b, 1, 0, 0, 0, ?_, ?_⟩
  · intro x w hw
    rw [show polyBound 1 0 x.length = 1 by simp [polyBound], haltMachine_answer_one]
    rfl
  · intro x
    simp only [polyBound, pow_zero, mul_one, zero_mul, pow_zero, haltMachine_answer_one]
    cases b <;> simp

lemma constant_inCountingHierarchy (b : Bool) : InCountingHierarchy (fun _ => b = true) := by
  exact ⟨0, constant_inOracleP (fun _ => False) b⟩

lemma constant_atCHLevel (j : ℕ) (b : Bool) : AtCHLevel j (fun _ => b = true) := by
  induction j with
  | zero => exact constant_inOracleP _ b
  | succ j ih => exact ⟨fun _ => b = true, ih, constant_inOraclePP _ b⟩

lemma machineStep_halted (M : OracleMachine) (A : Language) (cfg : MachineConfig M)
    (h : cfg.answer.isSome) : machineStep M A cfg = cfg := by
  simp only [machineStep, if_pos h]

lemma machineRun_succ (M : OracleMachine) (A : Language) (x w : Word) (t : ℕ) :
    machineRun M A x w (t + 1) = machineStep M A (machineRun M A x w t) := by
  exact Function.iterate_succ_apply' _ _ _

lemma machineRun_halted_persistent (M : OracleMachine) (A : Language) (x w : Word)
    (t s : ℕ) (h : (machineRun M A x w t).answer.isSome) :
    machineRun M A x w (t + s) = machineRun M A x w t := by
  induction s with
  | zero => simp
  | succ s ih =>
      rw [Nat.add_succ]
      rw [machineRun_succ]
      rw [ih, machineStep_halted M A _ h]

end APSCounting893.Main
end Component_8

section Component_9

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

noncomputable def negateMachine (M : OracleMachine) : OracleMachine :=
  { M with transition := fun q symbols => match M.transition q symbols with
    | .step q write move => .step q write move
    | .query yes no => .query yes no
    | .halt b => .halt (!b) }

def negateConfig (M : OracleMachine) (cfg : MachineConfig M) : MachineConfig (negateMachine M) where
  state := cfg.state
  tapes := cfg.tapes
  answer := cfg.answer.map Bool.not

lemma negateMachine_step (M : OracleMachine) (A : Language) (cfg : MachineConfig M) :
    machineStep (negateMachine M) A (negateConfig M cfg) = negateConfig M (machineStep M A cfg) := by
  classical
  rcases cfg with ⟨q, tapes, answer⟩
  cases answer with
  | some b => rfl
  | none =>
      cases h : M.transition q (fun j => (tapes j).read (tapes j).head) with
      | step q' write move => simp [machineStep, negateMachine, negateConfig, h]
      | query yes no => simp [machineStep, negateMachine, negateConfig, h]
      | halt b => simp [machineStep, negateMachine, negateConfig, h]

lemma negateMachine_initial (M : OracleMachine) (x w : Word) :
    initialConfig (negateMachine M) x w = negateConfig M (initialConfig M x w) := rfl

lemma negateMachine_run (M : OracleMachine) (A : Language) (x w : Word) (t : ℕ) :
    machineRun (negateMachine M) A x w t = negateConfig M (machineRun M A x w t) := by
  induction t with
  | zero => exact negateMachine_initial M x w
  | succ t ih =>
      rw [machineRun_succ, machineRun_succ, ih, negateMachine_step]

lemma InOracleP.compl {A L : Language} (hL : InOracleP A L) : InOracleP A (fun x => ¬ L x) := by
  obtain ⟨M, c, d, hM⟩ := hL
  refine ⟨negateMachine M, c, d, ?_⟩
  intro x
  obtain ⟨b, hb, hbx⟩ := hM x
  refine ⟨!b, ?_, ?_⟩
  · rw [negateMachine_run]
    change (machineRun M A x [] (polyBound c d x.length)).answer.map Bool.not = some (!b)
    rw [hb]
    rfl
  · cases b <;> simp_all

lemma InOracleP.inOraclePP {A L : Language} (hL : InOracleP A L) : InOraclePP A L := by
  obtain ⟨M, c, d, hM⟩ := hL
  refine ⟨M, c, d, 0, 0, ?_, ?_⟩
  · intro x w hw
    have hw0 : w = [] := List.length_eq_zero_iff.mp (by simpa [polyBound] using hw)
    subst w
    obtain ⟨b, hb, _⟩ := hM x
    rw [hb]
    rfl
  · intro x
    obtain ⟨b, hb, hbx⟩ := hM x
    have hset : {w : Word | w.length = polyBound 0 0 x.length ∧
        (machineRun M A x w (polyBound c d x.length)).answer = some true} =
        if b then {[]} else ∅ := by
      ext w
      simp only [polyBound, zero_mul, List.length_eq_zero_iff, Set.mem_setOf_eq]
      by_cases hw : w = []
      · subst w
        dsimp [polyBound] at hb
        cases b <;> simp [hb]
      · simp [hw]
    rw [hset]
    cases b <;> simp_all [polyBound]

end APSCounting893.Main
end Component_9

section Component_10
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

def taggedOracle (A : Language) : Language
  | false::false::rest => A rest
  | false::true::rest => ¬ A rest
  | true::b::_ => b=true
  | _ => False

def taggedOracleProgram : StackProgram (Fin 7) 0 where
  initial:=0
  transition:=fun q =>
    if q=0 then .pop 0 1 2 6
    else if q=1 then .pop 0 3 4 6
    else if q=2 then .pop 0 6 5 6
    else if q=3 then .query 0 5 6
    else if q=4 then .query 0 6 5
    else .halt (decide (q=5))

lemma taggedOracleProgram_answer (A : Language) (x : Word) :
    (taggedOracleProgram.run A x [] 4).answer=
      some (@decide (taggedOracle A x) (Classical.propDecidable _)) := by
  classical
  cases x with
  | nil => simp [taggedOracle,taggedOracleProgram,StackProgram.run,StackProgram.step,
      StackProgram.initialConfig,Function.iterate_succ_apply']
  | cons b rest =>
    cases b with
    | false =>
      cases rest with
      | nil => simp [taggedOracle,taggedOracleProgram,StackProgram.run,StackProgram.step,
          StackProgram.initialConfig,Function.iterate_succ_apply']
      | cons mode rest =>
        cases mode <;> by_cases ha : A rest <;>
          simp [taggedOracle,taggedOracleProgram,StackProgram.run,StackProgram.step,
            StackProgram.initialConfig,Function.iterate_succ_apply',ha]
    | true =>
      cases rest with
      | nil => simp [taggedOracle,taggedOracleProgram,StackProgram.run,StackProgram.step,
          StackProgram.initialConfig,Function.iterate_succ_apply']
      | cons b rest => cases b <;>
          simp [taggedOracle,taggedOracleProgram,StackProgram.run,StackProgram.step,
            StackProgram.initialConfig,Function.iterate_succ_apply']

lemma taggedOracle_inOracleP (A : Language) : InOracleP A (taggedOracle A) := by
  apply stack_program_polynomial_simulation taggedOracleProgram A (taggedOracle A) 4 0
  intro x
  refine ⟨@decide (taggedOracle A x) (Classical.propDecidable _),?_,by simp⟩
  simpa only [polyBound,pow_zero,mul_one] using taggedOracleProgram_answer A x

lemma AtCHLevel.tagged {j : ℕ} {A : Language} (hA : AtCHLevel j A) :
    AtCHLevel (j+1) (taggedOracle A) := ⟨A,hA,(taggedOracle_inOracleP A).inOraclePP⟩

end APSCounting893.Main
end Component_10

section Component_11
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace APSCounting893.Main

lemma AtCHLevel.native_tagged_preimage {j : ℕ} {A : Language} (hA : AtCHLevel j A)
    (f : Word → Word)
    (hf : Turing.MultiTapeTM.ComputableInPolyTime f Turing.MultiTapeTM.encBits Turing.MultiTapeTM.encBits) :
    AtCHLevel (j+2) (fun x => taggedOracle A (f x)) := by
  exact ⟨taggedOracle A,hA.tagged,(native_polynomial_oracle_preimage f hf (taggedOracle A)).inOraclePP⟩

lemma AtCHLevel.native_tagged_majority {j : ℕ} {A : Language} (hA : AtCHLevel j A)
    (f : Word → Word)
    (hf : Turing.MultiTapeTM.ComputableInPolyTime f Turing.MultiTapeTM.encBits Turing.MultiTapeTM.encBits)
    (a b : ℕ) :
    AtCHLevel (j+3) (fun x => 2^polyBound a b x.length <
      2*Set.ncard {w : Word | w.length=polyBound a b x.length ∧ taggedOracle A (f (pairWord x w))}) := by
  exact ⟨fun z => taggedOracle A (f z),hA.native_tagged_preimage f hf,
    bounded_majority_oracle_pp _ a b⟩

end APSCounting893.Main
end Component_11

section Component_12
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace APSCounting893.Main
attribute [local irreducible] longSumMatrixQuery carryMatrixQuery

def longSumCarryLanguage (F : Word → ℕ) (a b : ℕ) : Language := fun root =>
  ∃ outer : Word,outer.length=polyBound (4*(2*a+3)) (b+1) root.length ∧
    ∀ univ : Word,univ.length=polyBound (2*a+3) (b+1) (pairWord root outer).length →
      ∃ inner : Word,inner.length=polyBound (5*(2*a+3)) (b+1) (pairWord (pairWord root outer) univ).length ∧
        ∀ sel : Word,sel.length=3 →
          taggedOracle (NaturalGraphLanguage F)
            (longSumMatrixQuery a b (pairWord (pairWord (pairWord (pairWord root outer) univ) inner) sel))

lemma AtCHLevel.bounded_exists {j : ℕ} {A : Language} (hA : AtCHLevel j A)
    (a b : ℕ) (ha : 0 < a) :
    AtCHLevel (j+1) (fun x => ∃ y : Word,y.length=polyBound a b x.length ∧ A (pairWord x y)) :=
  ⟨A,hA,(bounded_quantification_oracle_pp A a b ha).1⟩

lemma AtCHLevel.bounded_forall {j : ℕ} {A : Language} (hA : AtCHLevel j A)
    (a b : ℕ) (ha : 0 < a) :
    AtCHLevel (j+1) (fun x => ∀ y : Word,y.length=polyBound a b x.length → A (pairWord x y)) :=
  ⟨A,hA,(bounded_quantification_oracle_pp A a b ha).2⟩

lemma AtCHLevel.long_sum_carry_language {F : Word → ℕ} {j : ℕ}
    (hF : AtCHLevel j (NaturalGraphLanguage F)) (a b : ℕ) :
    AtCHLevel (j+6) (longSumCarryLanguage F a b) := by
  have h0 := hF.native_tagged_preimage (longSumMatrixQuery a b) (native_longSumMatrixQuery a b).computableInPolyTime
  have h1 := h0.bounded_forall 3 0 (by decide)
  have h2 := h1.bounded_exists (5*(2*a+3)) (b+1) (by positivity)
  have h3 := h2.bounded_forall (2*a+3) (b+1) (by positivity)
  have h4 := h3.bounded_exists (4*(2*a+3)) (b+1) (by positivity)
  unfold longSumCarryLanguage
  simpa [Nat.add_assoc,polyBound] using h4

end APSCounting893.Main
end Component_12

section Component_13
set_option autoImplicit false
namespace APSCounting893.Main
lemma unframe_pairWord (x y : Word) : Turing.MultiTapeTM.unframe (pairWord x y)=x :=
  Turing.MultiTapeTM.unframe_frame_append x y
lemma dropFrame_pairWord (x y : Word) : Turing.MultiTapeTM.dropFrame (pairWord x y)=y :=
  Turing.MultiTapeTM.dropFrame_frame_append x y
end APSCounting893.Main
end Component_13

section Component_14
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.constructorNameAsVariable false
namespace APSCounting893.Main
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime Cslib.BitString
lemma carryGraphWord_semantics (F : Word → ℕ) (x : Word) (index : ℕ) (candidate : Word) :
    taggedOracle (NaturalGraphLanguage F) (carryGraphWord x index candidate) ↔
      F (Turing.MultiTapeTM.frame x++index.bits)=ofBits candidate := by
  simp [carryGraphWord,taggedOracle,NaturalGraphLanguage,List.append_assoc,unframe_frame_append,dropFrame_frame_append]
end APSCounting893.Main
end Component_14

section Component_15

end Component_15

section Component_16
set_option autoImplicit false
set_option maxHeartbeats 2200000
namespace APSCounting893.Main
open Turing.MultiTapeTM

def CarryMatrixGraphs (F : Word → ℕ) (a b : ℕ) (p : CarryMatrixInput) : Prop :=
  F (Turing.MultiTapeTM.frame p.x++(carryMatrixIndex a b p).bits)=ofBits p.current ∧
  F (Turing.MultiTapeTM.frame p.x++(carryMatrixIndex a b p-1).bits)=ofBits p.previous ∧
  F (Turing.MultiTapeTM.frame p.x++(carryMatrixGenIndex p).bits)=ofBits p.gen ∧
  F (Turing.MultiTapeTM.frame p.x++(carryMatrixGenIndex p-1).bits)=ofBits p.genPrevious ∧
  F (Turing.MultiTapeTM.frame p.x++(carryMatrixPropIndex p).bits)=ofBits p.prop ∧
  F (Turing.MultiTapeTM.frame p.x++(carryMatrixPropIndex p-1).bits)=ofBits p.propPrevious

lemma carryMatrixQuery_all (F : Word → ℕ) (a b : ℕ) (p : CarryMatrixInput) :
    (∀ i : Fin 8,taggedOracle (NaturalGraphLanguage F) (carryMatrixQuery a b (p,i.val))) ↔
      carryMatrixGuard a b p=true ∧ CarryMatrixGraphs F a b p := by
  cases hg : carryMatrixGuard a b p with
  | false => simp [carryMatrixQuery,hg,taggedOracle]
  | true =>
    simp only [Fin.forall_fin_succ, carryMatrixQuery, hg, Bool.true_eq, if_true]
    simp [carryGraphWord_semantics, CarryMatrixGraphs, taggedOracle, carryGraphWord, NaturalGraphLanguage, List.append_assoc, unframe_frame_append, dropFrame_frame_append]

end APSCounting893.Main
end Component_16

section Component_17
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace APSCounting893.Main
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime

lemma native_binary_bit_read : ComputableTidilyInPolyTime
    (fun x : ℕ × ℕ => x.1.testBit x.2) (encPair encNat encNat) encBool := by
  have hs := Turing.MultiTapeTM.ComputableInPolyTime.binary_shiftRight.tidy
  have hm := binary_mod' hs (const 2)
  have hh := decide_eq' hm (const 1)
  apply hh.of_enc_eq
  intro x
  simp only [Nat.testBit_eq_decide_div_mod_eq,Nat.shiftRight_eq_div_pow,Function.comp_apply]

end APSCounting893.Main
end Component_17

section Component_18
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace APSCounting893.Main

lemma AtCHLevel.native_tagged_exists {j : ℕ} {A : Language} (hA : AtCHLevel j A)
    (f : Word → Word)
    (hf : Turing.MultiTapeTM.ComputableInPolyTime f Turing.MultiTapeTM.encBits Turing.MultiTapeTM.encBits)
    (a b : ℕ) (ha : 0 < a) :
    AtCHLevel (j+3) (fun x => ∃ w : Word,w.length=polyBound a b x.length ∧
      taggedOracle A (f (pairWord x w))) := by
  have hp := hA.native_tagged_preimage f hf
  exact ⟨_,hp,(bounded_quantification_oracle_pp _ a b ha).1⟩

lemma AtCHLevel.native_tagged_forall {j : ℕ} {A : Language} (hA : AtCHLevel j A)
    (f : Word → Word)
    (hf : Turing.MultiTapeTM.ComputableInPolyTime f Turing.MultiTapeTM.encBits Turing.MultiTapeTM.encBits)
    (a b : ℕ) (ha : 0 < a) :
    AtCHLevel (j+3) (fun x => ∀ w : Word,w.length=polyBound a b x.length →
      taggedOracle A (f (pairWord x w))) := by
  have hp := hA.native_tagged_preimage f hf
  exact ⟨_,hp,(bounded_quantification_oracle_pp _ a b ha).2⟩

end APSCounting893.Main
end Component_18

section Component_19
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime

lemma native_graph_encodeNat : ComputableTidilyInPolyTime encodeNat encNat encBits := by
  have hbits := natBits
  have hprefix := (bitsReplicate true).comp (length_bits.comp hbits)
  have hh := bitsAppend hprefix (bitsAppend (const [false]) hbits)
  apply hh.of_enc_eq
  intro n
  simp [encodeNat,Function.comp_def,List.append_assoc]

def naturalGraphQuery (z : Word) : Word :=
  let whole := Turing.MultiTapeTM.unframe z
  let x := Turing.MultiTapeTM.unframe whole
  let v := ofBits (Turing.MultiTapeTM.dropFrame whole)
  let q := ofBits (Turing.MultiTapeTM.dropFrame z)
  [false,!(v.testBit q)]++naturalBitQuery x q

lemma native_naturalGraphQuery : ComputableTidilyInPolyTime naturalGraphQuery encBits encBits := by
  have hwhole := ComputableTidilyInPolyTime.unframe
  have hx := ComputableTidilyInPolyTime.unframe.comp hwhole
  have hv := bitsToNat.comp (ComputableTidilyInPolyTime.dropFrame.comp hwhole)
  have hq := bitsToNat.comp ComputableTidilyInPolyTime.dropFrame
  have hb := native_binary_bit_read.comp (hv.prod hq)
  have hmode := bool_not.comp hb
  have hquery := bitsAppend ((bitsFrame encBits).comp hx) (native_graph_encodeNat.comp hq)
  have hh := bitsCons (const false) (bitsCons hmode hquery)
  exact hh.of_enc_eq (fun z => rfl)

lemma naturalGraphQuery_semantics (F : Word → ℕ) (z w : Word) :
    taggedOracle (NaturalBitLanguage F) (naturalGraphQuery (pairWord z w)) ↔
      (F (Turing.MultiTapeTM.unframe z)).testBit (ofBits w)=
        (ofBits (Turing.MultiTapeTM.dropFrame z)).testBit (ofBits w) := by
  have he : pairWord z w=Turing.MultiTapeTM.frame z++w := rfl
  rw [he]
  simp only [naturalGraphQuery,unframe_frame_append,dropFrame_frame_append]
  cases hf : (F (Turing.MultiTapeTM.unframe z)).testBit (ofBits w) <;>
    cases hv : (ofBits (Turing.MultiTapeTM.dropFrame z)).testBit (ofBits w) <;>
    simp [taggedOracle,naturalBitQuery_correct,hf,hv]

end APSCounting893.Main
end Component_19

section Component_20
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime

def mappedNaturalBitQuery (phi : Word × ℕ → Option (Word × ℕ)) (z : Word) : Word :=
  (parseNaturalBitQuery z).elim [true,false] fun u =>
    (phi u).elim [true,false] fun v => [false,false]++naturalBitQuery v.1 v.2

lemma native_mappedNaturalBitQuery (phi : Word × ℕ → Option (Word × ℕ))
    (hphi : ComputableTidilyInPolyTime phi (encPair encBits encNat)
      (encOption (encPair encBits encNat))) :
    ComputableTidilyInPolyTime (mappedNaturalBitQuery phi) encBits encBits := by
  let encI := encPair encBits encNat
  have hv := snd encI encI
  have htarget := bitsAppend (const [false,false]) (bitsAppend
    ((bitsFrame encBits).comp hv.fst') (native_graph_encodeNat.comp hv.snd'))
  have hinner := optionElimWithInput
    (body:=fun (_ : Word × ℕ) (v : Word × ℕ) => [false,false]++naturalBitQuery v.1 v.2)
    hphi (const [true,false]) htarget
  have hbody := hinner.comp (snd encBits encI)
  exact optionElimWithInput
    (body:=fun (_ : Word) (u : Word × ℕ) => (phi u).elim [true,false]
      (fun v => [false,false]++naturalBitQuery v.1 v.2))
    native_parseNaturalBitQuery (const [true,false]) hbody

lemma mappedNaturalBitQuery_correct (F G : Word → ℕ)
    (phi : Word × ℕ → Option (Word × ℕ))
    (hbits : ∀ x q,(G x).testBit q=(phi (x,q)).elim false (fun v => (F v.1).testBit v.2))
    (z : Word) :
    NaturalBitLanguage G z ↔ taggedOracle (NaturalBitLanguage F) (mappedNaturalBitQuery phi z) := by
  have hi (u : Word × ℕ) :
      taggedOracle (NaturalBitLanguage F)
        ((phi u).elim [true,false] (fun v => [false,false]++naturalBitQuery v.1 v.2)) ↔
          (G u.1).testBit u.2=true := by
    rw [hbits]
    cases hm : phi u with
    | none => simp [taggedOracle]
    | some v => simp only [Option.elim_some,List.cons_append,List.nil_append,taggedOracle,naturalBitQuery_correct]
  unfold mappedNaturalBitQuery
  cases hp : parseNaturalBitQuery z with
  | none =>
    simp only [Option.elim_none,taggedOracle,Bool.false_eq_true,iff_false]
    rintro ⟨x,q,hz,hbit⟩
    rw [hz,parseNaturalBitQuery_code] at hp
    cases hp
  | some u =>
    simp only [Option.elim_some]
    rw [hi u]
    have hz := parseNaturalBitQuery_inverse z u.1 u.2 hp
    rw [hz,naturalBitQuery_correct]

lemma AtCHLevel.natural_bit_map {F G : Word → ℕ} {j : ℕ}
    (hF : AtCHLevel j (NaturalBitLanguage F)) (phi : Word × ℕ → Option (Word × ℕ))
    (hphi : ComputableTidilyInPolyTime phi (encPair encBits encNat)
      (encOption (encPair encBits encNat)))
    (hbits : ∀ x q,(G x).testBit q=(phi (x,q)).elim false (fun v => (F v.1).testBit v.2)) :
    AtCHLevel (j+2) (NaturalBitLanguage G) := by
  have hh := hF.native_tagged_preimage (mappedNaturalBitQuery phi)
    (native_mappedNaturalBitQuery phi hphi).computableInPolyTime
  have he : (fun z => taggedOracle (NaturalBitLanguage F) (mappedNaturalBitQuery phi z))=
      NaturalBitLanguage G := by
    funext z
    exact propext (mappedNaturalBitQuery_correct F G phi hbits z).symm
  rw [he] at hh
  exact hh

end APSCounting893.Main
end Component_20

section Component_21
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime

def naturalLessQuery (z : Word) : Word :=
  let whole := Turing.MultiTapeTM.unframe z
  let witnessWord := Turing.MultiTapeTM.dropFrame z
  if ofBits (Turing.MultiTapeTM.dropFrame whole)<ofBits witnessWord then
    [false,false]++Turing.MultiTapeTM.frame (Turing.MultiTapeTM.unframe whole)++witnessWord
  else [true,false]

lemma native_naturalLessQuery : ComputableTidilyInPolyTime naturalLessQuery encBits encBits := by
  have hwhole := ComputableTidilyInPolyTime.unframe
  have hw := ComputableTidilyInPolyTime.dropFrame
  have ht := bitsToNat.comp (ComputableTidilyInPolyTime.dropFrame.comp hwhole)
  have hv := bitsToNat.comp hw
  have hcmp := binary_lt' ht hv
  have hdomain := ComputableTidilyInPolyTime.unframe.comp hwhole
  have hyes := bitsAppend (const [false,false]) (bitsAppend ((bitsFrame encBits).comp hdomain) hw)
  have hh := ite_decide hcmp hyes (const [true,false])
  exact hh.of_enc_eq (fun z => rfl)

lemma naturalLessQuery_semantics (F : Word → ℕ) (z w : Word) :
    taggedOracle (NaturalGraphLanguage F) (naturalLessQuery (pairWord z w)) ↔
      ofBits (Turing.MultiTapeTM.dropFrame z)<ofBits w ∧
        F (Turing.MultiTapeTM.unframe z)=ofBits w := by
  have he : pairWord z w=Turing.MultiTapeTM.frame z++w := rfl
  rw [he]
  simp only [naturalLessQuery,unframe_frame_append,dropFrame_frame_append]
  by_cases h : ofBits (Turing.MultiTapeTM.dropFrame z)<ofBits w
  · simp [h,taggedOracle,NaturalGraphLanguage,unframe_frame_append,dropFrame_frame_append,List.append_assoc]
  · simp [h,taggedOracle]

end APSCounting893.Main
end Component_21

section Component_22
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.constructorNameAsVariable false
namespace APSCounting893.Main
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime Cslib.BitString
lemma native_polyBound_unary (a b : ℕ) : ComputableTidilyInPolyTime
    (polyBound a b) encUnary encUnary := by
  have hi := id' (encIn:=encUnary)
  have hplus := unary_add.comp (hi.prod (const 1))
  have hp := (unary_pow b).comp hplus
  have hh := unary_mul.comp ((const a).prod hp)
  exact hh.of_enc_eq (fun n => rfl)

def smallSumQuery (a b c d : ℕ) (z : Word) : Word :=
  let countInput := Turing.MultiTapeTM.unframe z
  let x := Turing.MultiTapeTM.unframe countInput
  let w := Turing.MultiTapeTM.dropFrame z
  let r := polyBound a b x.length
  let s := polyBound c d x.length
  if r+s≤w.length ∧ (w.drop (r+s)).all (!·)=true then
    [false,false]++Turing.MultiTapeTM.frame (Turing.MultiTapeTM.frame x++w.take r)++
      (w.drop r).take s
  else [true,false]
end APSCounting893.Main
end Component_22

section Component_23
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime

def naturalBlockWidth (a b : ℕ) (z : Word) : ℕ :=
  polyBound a b (Turing.MultiTapeTM.unframe (Turing.MultiTapeTM.unframe z)).length+1

def naturalBlockSource (z : Word) : Word :=
  Turing.MultiTapeTM.frame (Turing.MultiTapeTM.unframe (Turing.MultiTapeTM.unframe z))++
    Turing.MultiTapeTM.dropFrame z

def naturalBlockIndex (z : Word) : ℕ :=
  ofBits (Turing.MultiTapeTM.dropFrame (Turing.MultiTapeTM.unframe z))

def naturalBitBlock (F : Word → ℕ) (a b : ℕ) (z : Word) : ℕ :=
  (F (naturalBlockSource z) >>> (naturalBlockWidth a b z*naturalBlockIndex z))%
    2^naturalBlockWidth a b z

def naturalBlockBitMap (a b : ℕ) (p : Word × ℕ) : Option (Word × ℕ) :=
  if p.2<naturalBlockWidth a b p.1 then
    some (naturalBlockSource p.1,naturalBlockWidth a b p.1*naturalBlockIndex p.1+p.2)
  else none

lemma native_naturalBlockBitMap (a b : ℕ) : ComputableTidilyInPolyTime
    (naturalBlockBitMap a b) (encPair encBits encNat) (encOption (encPair encBits encNat)) := by
  have hi := id' (encIn:=encPair encBits encNat)
  have hz := hi.fst'
  have hq := hi.snd'
  have hdomain := ComputableTidilyInPolyTime.unframe.comp (ComputableTidilyInPolyTime.unframe.comp hz)
  have hindex := bitsToNat.comp (ComputableTidilyInPolyTime.dropFrame.comp (ComputableTidilyInPolyTime.unframe.comp hz))
  have hr := (native_polyBound_unary a b).comp (length_bits.comp hdomain)
  have hwidth := binary_add' (unary_to_binary.comp hr) (const 1)
  have hsource := bitsAppend ((bitsFrame encBits).comp hdomain) (ComputableTidilyInPolyTime.dropFrame.comp hz)
  have hposition := binary_add' (binary_mul' hwidth hindex) hq
  have hsome := (optionSome (encPair encBits encNat)).comp (hsource.prod hposition)
  have hh := ite_decide (binary_lt' hq hwidth) hsome (const (none : Option (Word × ℕ)))
  exact hh.of_enc_eq (fun p => rfl)

lemma naturalBitBlock_bit (F : Word → ℕ) (a b : ℕ) (z : Word) (q : ℕ) :
    (naturalBitBlock F a b z).testBit q=
      (naturalBlockBitMap a b (z,q)).elim false (fun v => (F v.1).testBit v.2) := by
  unfold naturalBitBlock naturalBlockBitMap
  rw [Nat.testBit_mod_two_pow,Nat.testBit_shiftRight]
  by_cases h : q<naturalBlockWidth a b z <;> simp only [h,decide_true,decide_false,
    Bool.true_and,Bool.false_and,if_true,if_false,Option.elim_some,Option.elim_none]

lemma naturalBitBlock_length_bound (F : Word → ℕ) (a b : ℕ) (z : Word) :
    (naturalBitBlock F a b z).bits.length≤polyBound (a+1) (b+1) z.length := by
  have hsize : (naturalBitBlock F a b z).bits.length≤naturalBlockWidth a b z := by
    rw [Nat.size_eq_bits_len]
    apply Nat.size_le.mpr
    exact Nat.mod_lt _ (by positivity)
  apply hsize.trans
  have h1 := length_unframe_add_dropFrame_le z
  have h2 := length_unframe_add_dropFrame_le (Turing.MultiTapeTM.unframe z)
  have hp : ((Turing.MultiTapeTM.unframe (Turing.MultiTapeTM.unframe z)).length+1)^b≤
      (z.length+1)^(b+1) :=
    (Nat.pow_le_pow_left (by omega) b).trans (Nat.pow_le_pow_right (by omega) (Nat.le_succ b))
  have hU : 1≤(z.length+1)^(b+1) := Nat.one_le_pow _ _ (by omega)
  unfold naturalBlockWidth polyBound
  nlinarith [Nat.mul_le_mul_left a hp]

lemma AtCHLevel.natural_bit_blocks {F : Word → ℕ} {j : ℕ}
    (hF : AtCHLevel j (NaturalBitLanguage F)) (a b : ℕ) :
    AtCHLevel (j+5) (NaturalGraphLanguage (naturalBitBlock F a b)) := by
  have hb := hF.natural_bit_map (naturalBlockBitMap a b) (native_naturalBlockBitMap a b)
    (naturalBitBlock_bit F a b)
  have hg := short_natural_graph_from_bits (naturalBitBlock F a b) (j+2) (a+1) (b+1)
    (naturalBitBlock_length_bound F a b) hb
  simpa only [Nat.add_assoc] using hg

end APSCounting893.Main
end Component_23

section Component_24
set_option autoImplicit false
namespace APSCounting893.Main

noncomputable def indexedNaturalSumWithWidth (F : Word → ℕ) (width : Word → ℕ) (x : Word) : ℕ :=
  ∑ i : Fin (2^width x),F (Turing.MultiTapeTM.frame x++Cslib.BitString.lowBits (width x) i.val)

end APSCounting893.Main
end Component_24

section Component_25
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime

def variableSumQuery (rho sigma : Word → ℕ) (z : Word) : Word :=
  let x := Turing.MultiTapeTM.unframe (Turing.MultiTapeTM.unframe z)
  let w := Turing.MultiTapeTM.dropFrame z
  if rho x+sigma x≤w.length ∧ (w.drop (rho x+sigma x)).all (!·)=true then
    [false,false]++Turing.MultiTapeTM.frame (Turing.MultiTapeTM.frame x++w.take (rho x))++
      (w.drop (rho x)).take (sigma x)
  else [true,false]

lemma native_variableSumQuery (rho sigma : Word → ℕ)
    (hrho : ComputableTidilyInPolyTime rho encBits encUnary)
    (hsigma : ComputableTidilyInPolyTime sigma encBits encUnary) :
    ComputableTidilyInPolyTime (variableSumQuery rho sigma) encBits encBits := by
  have hx := ComputableTidilyInPolyTime.unframe.comp ComputableTidilyInPolyTime.unframe
  have hw := ComputableTidilyInPolyTime.dropFrame
  have hr := hrho.comp hx
  have hs := hsigma.comp hx
  have htotal := unary_add.comp (hr.prod hs)
  have hlengthok := unary_le' htotal (length_bits.comp hw)
  have hpad := bitsDropWithInput hw htotal
  have hbitsok := allWithEncoding (encA:=encBool) (encL:=encBits)
    (bool_not.comp (snd encBits encBool)) (id' (encIn:=encBits)) hpad
  have hguard := decide_and hlengthok (decide_eq' hbitsok (const true))
  have hindex := bitsTakeWithInput hw hr
  have hvalue := bitsTakeWithInput (bitsDropWithInput hw hr) hs
  have hterm := bitsAppend ((bitsFrame encBits).comp hx) hindex
  have hquery := bitsAppend (const [false,false]) (bitsAppend ((bitsFrame encBits).comp hterm) hvalue)
  have hh := ite_decide hguard hquery (const [true,false])
  exact hh.of_enc_eq (fun z => rfl)

lemma variableSumQuery_semantics (F : Word → ℕ) (rho sigma : Word → ℕ) (z w : Word) :
    let x := Turing.MultiTapeTM.unframe z
    taggedOracle (NaturalLessLanguage F) (variableSumQuery rho sigma (pairWord z w)) ↔
      rho x+sigma x≤w.length ∧ (w.drop (rho x+sigma x)).all (!·)=true ∧
      ofBits ((w.drop (rho x)).take (sigma x))<F (Turing.MultiTapeTM.frame x++w.take (rho x)) := by
  have he : pairWord z w=Turing.MultiTapeTM.frame z++w := rfl
  dsimp only
  rw [he]
  simp only [variableSumQuery,unframe_frame_append,dropFrame_frame_append]
  split_ifs with h
  · simp [h,taggedOracle,NaturalLessLanguage,unframe_frame_append,dropFrame_frame_append,List.append_assoc]
  · simp only [taggedOracle,Bool.false_eq_true,false_iff]
    rintro ⟨hL,hpad,_⟩
    exact h ⟨hL,hpad⟩

end APSCounting893.Main
end Component_25

section Component_26
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace APSCounting893.Main

def zeroPadWord (k : ℕ) (w : Word) : Word := w++List.replicate k false

lemma zeroPadWord_injective (k : ℕ) : Function.Injective (zeroPadWord k) := by
  intro u v h
  exact List.append_cancel_right h

lemma zero_padded_set_ncard (G : Set Word) (k : ℕ) :
    ((zeroPadWord k) '' G).ncard=G.ncard := (zeroPadWord_injective k).injOn.ncard_image

lemma zero_padded_set_characterization (G : Set Word) (r N : ℕ)
    (hG : G ⊆ {w : Word | w.length=r}) (hN : r≤N) :
    zeroPadWord (N-r) '' G = {w : Word | w.length=N ∧ w.take r ∈ G ∧
      w.drop r=List.replicate (N-r) false} := by
  ext w
  constructor
  · rintro ⟨u,hu,rfl⟩
    have hlen : u.length=r := hG hu
    refine ⟨?_,?_,?_⟩
    · simp only [zeroPadWord,List.length_append,List.length_replicate,hlen];omega
    · unfold zeroPadWord
      have he : (u++List.replicate (N-r) false).take r=u := by simpa only [hlen] using (show (u++List.replicate (N-r) false).take u.length=u from List.take_left)
      rw [he];exact hu
    · unfold zeroPadWord
      simpa only [hlen] using (show (u++List.replicate (N-r) false).drop u.length=List.replicate (N-r) false from List.drop_left)
  · rintro ⟨hlen,hmem,htail⟩
    refine ⟨w.take r,hmem,?_⟩
    unfold zeroPadWord
    rw [←htail,List.take_append_drop]

end APSCounting893.Main
end Component_26

section Component_27
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace APSCounting893.Main
open Turing.MultiTapeTM Cslib.BitString

noncomputable def fixedWordEquivFin (s : ℕ) : {w : Word // w.length=s} ≃ Fin (2^s) where
  toFun:=fun w => ⟨ofBits w.1,by simpa only [←w.2,ofBits] using Nat.foldr_bit_lt w.1⟩
  invFun:=fun i => ⟨lowBits s i.val,length_lowBits _ _⟩
  left_inv:=by
    intro w;apply Subtype.ext
    change lowBits s (ofBits w.1)=w.1
    simpa only [w.2,ofBits_eq_lsbValue] using lowBits_lsbValue w.1
  right_inv:=by
    intro i;apply Fin.ext
    change ofBits (lowBits s i.val)=i.val
    simpa only [ofBits_eq_lsbValue] using lsbValue_lowBits i.isLt

noncomputable def splitFixedWords (r s : ℕ) :
    {w : Word // w.length=r+s} ≃ {u : Word // u.length=r} × {v : Word // v.length=s} where
  toFun:=fun w => (⟨w.1.take r,by simp only [List.length_take,w.2];omega⟩,
    ⟨w.1.drop r,by simp only [List.length_drop,w.2];omega⟩)
  invFun:=fun p => ⟨p.1.1++p.2.1,by simp only [List.length_append,p.1.2,p.2.2]⟩
  left_inv:=by intro w;apply Subtype.ext;exact List.take_append_drop _ _
  right_inv:=by
    intro p
    apply Prod.ext <;> apply Subtype.ext
    · change (p.1.1++p.2.1).take r=p.1.1
      have h : (p.1.1++p.2.1).take p.1.1.length=p.1.1 := List.take_left
      simpa only [p.1.2] using h
    · change (p.1.1++p.2.1).drop r=p.2.1
      have h : (p.1.1++p.2.1).drop p.1.1.length=p.2.1 := List.drop_left
      simpa only [p.1.2] using h

end APSCounting893.Main
end Component_27

section Component_28
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace APSCounting893.Main

lemma weighted_counting_card {ι : Type} [Fintype ι] (B : ℕ) (v : ι → ℕ)
    (hv : ∀ i,v i≤B) :
    Fintype.card {z : ι × Fin B // z.2.val<v z.1}=∑ i,v i := by
  classical
  let e : {z : ι × Fin B // z.2.val<v z.1} ≃ (Σ i,Fin (v i)) :=
    { toFun:=fun z => ⟨z.1.1,⟨z.1.2.val,z.2⟩⟩
      invFun:=fun z => ⟨(z.1,⟨z.2.val,z.2.isLt.trans_le (hv z.1)⟩),z.2.isLt⟩
      left_inv:=by intro z;cases z; rfl
      right_inv:=by intro z;cases z;rfl }
  rw [Fintype.card_congr e,Fintype.card_sigma]
  simp

end APSCounting893.Main
end Component_28

section Component_29
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace APSCounting893.Main
open Turing.MultiTapeTM Cslib.BitString

noncomputable def wordPairFinEquiv (r s : ℕ) :
    {w : Word // w.length=r+s} ≃ Fin (2^r) × Fin (2^s) :=
  (splitFixedWords r s).trans ((fixedWordEquivFin r).prodCongr (fixedWordEquivFin s))

lemma weighted_word_counting (r s : ℕ) (v : Word → ℕ)
    (hv : ∀ w : Word,w.length=r → v w≤2^s) :
    Set.ncard {w : Word | w.length=r+s ∧ ofBits (w.drop r)<v (w.take r)}=
      ∑ i : Fin (2^r),v (lowBits r i.val) := by
  classical
  let code : Fin (2^r) × Fin (2^s) → Word := fun z => lowBits r z.1.val++lowBits s z.2.val
  let S : Set (Fin (2^r) × Fin (2^s)) := {z | z.2.val<v (lowBits r z.1.val)}
  have hinj : Function.Injective code := by
    intro z z' he
    apply (wordPairFinEquiv r s).symm.injective
    apply Subtype.ext
    exact he
  have himage : {w : Word | w.length=r+s ∧ ofBits (w.drop r)<v (w.take r)}=code '' S := by
    ext w
    constructor
    · rintro ⟨hlen,hlt⟩
      let z := wordPairFinEquiv r s ⟨w,hlen⟩
      have hback : code z=w := congrArg Subtype.val ((wordPairFinEquiv r s).symm_apply_apply ⟨w,hlen⟩)
      have ht : (code z).take r=lowBits r z.1.val := by
        have hh : (lowBits r z.1.val++lowBits s z.2.val).take (lowBits r z.1.val).length=lowBits r z.1.val := List.take_left
        simpa only [length_lowBits] using hh
      have hd : (code z).drop r=lowBits s z.2.val := by
        have hh : (lowBits r z.1.val++lowBits s z.2.val).drop (lowBits r z.1.val).length=lowBits s z.2.val := List.drop_left
        simpa only [length_lowBits] using hh
      refine ⟨z,?_,hback⟩
      change z.2.val<v (lowBits r z.1.val)
      rw [←hback,hd,ofBits_eq_lsbValue,lsbValue_lowBits z.2.isLt,ht] at hlt
      exact hlt
    · rintro ⟨z,hz,rfl⟩
      refine ⟨by simp [code],?_⟩
      have ht : (code z).take r=lowBits r z.1.val := by
        have hh : (lowBits r z.1.val++lowBits s z.2.val).take (lowBits r z.1.val).length=lowBits r z.1.val := List.take_left
        simpa only [length_lowBits] using hh
      have hd : (code z).drop r=lowBits s z.2.val := by
        have hh : (lowBits r z.1.val++lowBits s z.2.val).drop (lowBits r z.1.val).length=lowBits s z.2.val := List.drop_left
        simpa only [length_lowBits] using hh
      rw [hd,ofBits_eq_lsbValue,lsbValue_lowBits z.2.isLt,ht]
      exact hz
  rw [himage,hinj.injOn.ncard_image]
  change Nat.card {z : Fin (2^r) × Fin (2^s) // z.2.val<v (lowBits r z.1.val)}=_
  rw [Nat.card_eq_fintype_card]
  exact weighted_counting_card (2^s) (fun i : Fin (2^r) => v (lowBits r i.val))
    (fun i => hv _ (length_lowBits _ _))

end APSCounting893.Main
end Component_29

section Component_30
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace APSCounting893.Main
open Turing.MultiTapeTM Cslib.BitString

lemma all_false_eq_replicate (w : Word) :
    w.all (!·)=true ↔ w=List.replicate w.length false := by
  induction w with
  | nil => simp
  | cons bit w ih => cases bit <;> simp [List.replicate_succ,ih]

lemma smallSumQuery_semantics (F : Word → ℕ) (a b c d : ℕ) (z w : Word) :
    let x := Turing.MultiTapeTM.unframe z
    let r := polyBound a b x.length
    let s := polyBound c d x.length
    taggedOracle (NaturalLessLanguage F) (smallSumQuery a b c d (pairWord z w)) ↔
      r+s≤w.length ∧ (w.drop (r+s)).all (!·)=true ∧
      ofBits ((w.drop r).take s)<F (Turing.MultiTapeTM.frame x++w.take r) := by
  have he : pairWord z w=Turing.MultiTapeTM.frame z++w := rfl
  dsimp only
  rw [he]
  simp only [smallSumQuery,unframe_frame_append,dropFrame_frame_append]
  split_ifs with h
  · simp [h,taggedOracle,NaturalLessLanguage,unframe_frame_append,dropFrame_frame_append,List.append_assoc]
  · simp only [taggedOracle,Bool.false_eq_true,false_iff]
    rintro ⟨hL,hpad,_⟩
    exact h ⟨hL,hpad⟩

lemma smallSum_word_clock (a b c d : ℕ) (z : Word) :
    polyBound a b (Turing.MultiTapeTM.unframe z).length+
      polyBound c d (Turing.MultiTapeTM.unframe z).length+1≤
      polyBound (a+c+2) (max b d+1) z.length := by
  let U := (z.length+1)^(max b d+1)
  have hU : 1≤U := Nat.one_le_pow _ _ (by omega)
  have hlen := length_unframe_add_dropFrame_le z
  have hr : polyBound a b (Turing.MultiTapeTM.unframe z).length≤a*U :=
    Nat.mul_le_mul_left a ((Nat.pow_le_pow_left (by omega) b).trans
      (Nat.pow_le_pow_right (by omega) (by omega : b ≤ max b d+1)))
  have hs : polyBound c d (Turing.MultiTapeTM.unframe z).length≤c*U :=
    Nat.mul_le_mul_left c ((Nat.pow_le_pow_left (by omega) d).trans
      (Nat.pow_le_pow_right (by omega) (by omega : d ≤ max b d+1)))
  change _≤(a+c+2)*U
  nlinarith

end APSCounting893.Main
end Component_30

section Component_31
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace APSCounting893.Main
open Turing.MultiTapeTM Cslib.BitString

lemma weighted_zero_padded_word_count (r s N : ℕ) (v : Word → ℕ)
    (hN : r+s≤N) (hv : ∀ w : Word,w.length=r → v w≤2^s) :
    Set.ncard {w : Word | w.length=N ∧ (w.drop (r+s)).all (!·)=true ∧
      ofBits ((w.drop r).take s)<v (w.take r)}=
        ∑ i : Fin (2^r),v (lowBits r i.val) := by
  classical
  let G : Set Word := {u | u.length=r+s ∧ ofBits (u.drop r)<v (u.take r)}
  have hg : G ⊆ {u : Word | u.length=r+s} := fun _ h => h.1
  have hpref (w : Word) (hlen : w.length=N) :
      w.take (r+s) ∈ G ↔ ofBits ((w.drop r).take s)<v (w.take r) := by
    change ((w.take (r+s)).length=r+s ∧
      ofBits ((w.take (r+s)).drop r)<v ((w.take (r+s)).take r)) ↔ _
    simp only [List.length_take,hlen,Nat.min_eq_left hN,List.drop_take,
      Nat.add_sub_cancel_left,List.take_take,Nat.min_eq_left (show r≤r+s by omega),true_and]
  have he : zeroPadWord (N-(r+s)) '' G={w : Word | w.length=N ∧
      (w.drop (r+s)).all (!·)=true ∧ ofBits ((w.drop r).take s)<v (w.take r)} := by
    rw [zero_padded_set_characterization G (r+s) N hg hN]
    ext w
    by_cases hlen : w.length=N
    · simp only [Set.mem_setOf_eq,hlen,true_and,hpref w hlen,all_false_eq_replicate,List.length_drop,hlen]
      exact and_comm
    · simp only [Set.mem_setOf_eq,hlen,false_and]
  rw [←he,zero_padded_set_ncard]
  exact weighted_word_counting r s v hv

lemma smallSum_count_identity (F : Word → ℕ) (a b c d : ℕ) (z : Word) (N : ℕ)
    (hN : polyBound a b (Turing.MultiTapeTM.unframe z).length+
      polyBound c d (Turing.MultiTapeTM.unframe z).length≤N)
    (hF : ∀ i : Word,i.length=polyBound a b (Turing.MultiTapeTM.unframe z).length →
      F (Turing.MultiTapeTM.frame (Turing.MultiTapeTM.unframe z)++i)≤
        2^polyBound c d (Turing.MultiTapeTM.unframe z).length) :
    Set.ncard {w : Word | w.length=N ∧
      taggedOracle (NaturalLessLanguage F) (smallSumQuery a b c d (pairWord z w))}=
      indexedNaturalSum F a b (Turing.MultiTapeTM.unframe z) := by
  have he : {w : Word | w.length=N ∧
      taggedOracle (NaturalLessLanguage F) (smallSumQuery a b c d (pairWord z w))}=
      {w : Word | w.length=N ∧
        (w.drop (polyBound a b (Turing.MultiTapeTM.unframe z).length+
          polyBound c d (Turing.MultiTapeTM.unframe z).length)).all (!·)=true ∧
        ofBits ((w.drop (polyBound a b (Turing.MultiTapeTM.unframe z).length)).take
          (polyBound c d (Turing.MultiTapeTM.unframe z).length))<
          F (Turing.MultiTapeTM.frame (Turing.MultiTapeTM.unframe z)++
            w.take (polyBound a b (Turing.MultiTapeTM.unframe z).length))} := by
    ext w
    simp only [Set.mem_setOf_eq,smallSumQuery_semantics]
    by_cases hlen : w.length=N
    · simp only [hlen,hN,true_and]
    · simp only [hlen,false_and]
  rw [he]
  exact weighted_zero_padded_word_count _ _ N _ hN hF

end APSCounting893.Main
end Component_31

section Component_32
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace APSCounting893.Main
open Turing.MultiTapeTM

lemma variableSum_count_identity (F : Word → ℕ) (rho sigma : Word → ℕ) (z : Word) (N : ℕ)
    (hN : rho (Turing.MultiTapeTM.unframe z)+sigma (Turing.MultiTapeTM.unframe z)≤N)
    (hF : ∀ i : Word,i.length=rho (Turing.MultiTapeTM.unframe z) →
      F (Turing.MultiTapeTM.frame (Turing.MultiTapeTM.unframe z)++i)≤
        2^sigma (Turing.MultiTapeTM.unframe z)) :
    Set.ncard {w : Word | w.length=N ∧
      taggedOracle (NaturalLessLanguage F) (variableSumQuery rho sigma (pairWord z w))}=
      indexedNaturalSumWithWidth F rho (Turing.MultiTapeTM.unframe z) := by
  have he : {w : Word | w.length=N ∧
      taggedOracle (NaturalLessLanguage F) (variableSumQuery rho sigma (pairWord z w))}=
      {w : Word | w.length=N ∧
        (w.drop (rho (Turing.MultiTapeTM.unframe z)+sigma (Turing.MultiTapeTM.unframe z))).all (!·)=true ∧
        ofBits ((w.drop (rho (Turing.MultiTapeTM.unframe z))).take (sigma (Turing.MultiTapeTM.unframe z)))<
          F (Turing.MultiTapeTM.frame (Turing.MultiTapeTM.unframe z)++w.take (rho (Turing.MultiTapeTM.unframe z)))} := by
    ext w
    simp only [Set.mem_ofPred_eq,variableSumQuery_semantics]
    by_cases hlen : w.length=N
    · simp only [hlen,hN,true_and]
    · simp only [hlen,false_and]
  rw [he]
  exact weighted_zero_padded_word_count _ _ N _ hN hF

end APSCounting893.Main
end Component_32

section Component_33
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime

def countThresholdQuery (z : Word) : Word :=
  let x := Turing.MultiTapeTM.unframe z
  let w := Turing.MultiTapeTM.dropFrame z
  if w.headD false then [true,decide (ofBits (Turing.MultiTapeTM.dropFrame x) ≤ ofBits w.tail)]
  else [false,false]++Turing.MultiTapeTM.frame x++w.tail

lemma native_countThresholdQuery : ComputableTidilyInPolyTime countThresholdQuery encBits encBits := by
  have hx := ComputableTidilyInPolyTime.unframe
  have hw := ComputableTidilyInPolyTime.dropFrame
  have ht := bitsToNat.comp (ComputableTidilyInPolyTime.dropFrame.comp hx)
  have hr := bitsToNat.comp (bitsTail.comp hw)
  have hcmp := binary_le' ht hr
  have hyes := bitsCons (const true) (bitsCons hcmp (const []))
  have hno := bitsAppend (const [false,false]) (bitsAppend ((bitsFrame encBits).comp hx) (bitsTail.comp hw))
  have hhead := (headD (encA:=encBool) (encL:=encBits) false).comp hw
  have hh := ComputableTidilyInPolyTime.cond hhead hyes hno
  exact hh.of_enc_eq (fun z => rfl)

end APSCounting893.Main
end Component_33

section Component_34
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace APSCounting893.Main
open Turing.MultiTapeTM

def thresholdPaddedSeeds (G : Set Word) (s t : ℕ) : Set Word :=
  (List.cons false) '' G ∪ (List.cons true) '' {w : Word | w.length=s ∧ t≤ofBits w}

lemma thresholdPaddedSeeds_ncard (G : Set Word) (s t : ℕ)
    (hG : G ⊆ {w : Word | w.length=s}) :
    (thresholdPaddedSeeds G s t).ncard=G.ncard+(2^s-t) := by
  classical
  have hu : Set.Finite {w : Word | w.length=s} := Set.finite_of_ncard_pos (by
    rw [words_fixed_length_ncard];positivity)
  have hg := hu.subset hG
  have hh := hu.subset (show {w : Word | w.length=s ∧ t≤ofBits w} ⊆ {w : Word | w.length=s} from fun _ h => h.1)
  have hd : Disjoint ((List.cons false) '' G)
      ((List.cons true) '' {w : Word | w.length=s ∧ t≤ofBits w}) := by
    apply Set.disjoint_left.mpr
    rintro w ⟨u,hu,rfl⟩ ⟨v,hv,he⟩
    simp at he
  have hi (b : Bool) : Function.Injective (List.cons b : Word → Word) := by
    intro u v he;exact List.cons.inj he |>.2
  rw [thresholdPaddedSeeds,Set.ncard_union_eq hd (hg.image _) (hh.image _),
    (hi false).injOn.ncard_image,(hi true).injOn.ncard_image,words_at_least_threshold_ncard]

lemma thresholdPaddedSeeds_majority (G : Set Word) (s t : ℕ)
    (hG : G ⊆ {w : Word | w.length=s}) :
    2^(s+1)<2*(thresholdPaddedSeeds G s t).ncard ↔ t<G.ncard := by
  rw [thresholdPaddedSeeds_ncard G s t hG,pow_succ]
  have hcard : G.ncard≤2^s := by
    rw [←words_fixed_length_ncard s]
    exact Set.ncard_le_ncard hG (Set.finite_of_ncard_pos (by rw [words_fixed_length_ncard];positivity))
  omega

end APSCounting893.Main
end Component_34

section Component_35
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main
open Turing.MultiTapeTM

lemma countThresholdQuery_semantics (A : Language) (x : Word) (b : Bool) (w : Word) :
    taggedOracle A (countThresholdQuery (pairWord x (b::w))) ↔
      if b then ofBits (Turing.MultiTapeTM.dropFrame x) ≤ ofBits w else A (pairWord x w) := by
  have he : pairWord x (b::w)=Turing.MultiTapeTM.frame x++(b::w) := rfl
  rw [he]
  simp only [countThresholdQuery,unframe_frame_append,dropFrame_frame_append,List.headD_cons,List.tail_cons]
  cases b <;> simp [taggedOracle,pairWord,Turing.MultiTapeTM.frame,List.append_assoc]

lemma countThresholdQuery_seed_set (A : Language) (x : Word) (s : ℕ) :
    {w : Word | w.length=s+1 ∧ taggedOracle A (countThresholdQuery (pairWord x w))}=
      thresholdPaddedSeeds {w : Word | w.length=s ∧ A (pairWord x w)}
        s (ofBits (Turing.MultiTapeTM.dropFrame x)) := by
  ext w
  cases w with
  | nil => simp [thresholdPaddedSeeds]
  | cons b w =>
    simp only [Set.mem_ofPred_eq]
    rw [countThresholdQuery_semantics]
    cases b <;> simp [thresholdPaddedSeeds,List.cons.injEq]

lemma countThresholdQuery_majority_iff (A : Language) (x : Word) (p : ℕ) (hp : 0 < p) :
    (2^p<2*Set.ncard {w : Word | w.length=p ∧ taggedOracle A (countThresholdQuery (pairWord x w))}) ↔
      ofBits (Turing.MultiTapeTM.dropFrame x)<Set.ncard {w : Word | w.length+1=p ∧ A (pairWord x w)} := by
  obtain ⟨s,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne'
  rw [countThresholdQuery_seed_set,thresholdPaddedSeeds_majority _ _ _ (fun _ h => h.1)]
  simp

lemma AtCHLevel.count_threshold {A : Language} {j : ℕ} (hA : AtCHLevel j A)
    (a b : ℕ) (ha : 0 < a) :
    AtCHLevel (j+3) (fun x => ofBits (Turing.MultiTapeTM.dropFrame x)<
      Set.ncard {w : Word | w.length+1=polyBound a b x.length ∧ A (pairWord x w)}) := by
  have hm := hA.native_tagged_majority countThresholdQuery native_countThresholdQuery.computableInPolyTime a b
  have he : (fun x => 2^polyBound a b x.length<2*Set.ncard {w : Word |
      w.length=polyBound a b x.length ∧ taggedOracle A (countThresholdQuery (pairWord x w))})=
      (fun x => ofBits (Turing.MultiTapeTM.dropFrame x)<
        Set.ncard {w : Word | w.length+1=polyBound a b x.length ∧ A (pairWord x w)}) := by
    funext x
    apply propext
    exact countThresholdQuery_majority_iff A x _ (Nat.mul_pos ha (by positivity))
  rw [he] at hm
  exact hm

end APSCounting893.Main
end Component_35

section Component_36
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime

def graphFromLessQuery (z : Word) : Word :=
  let whole := Turing.MultiTapeTM.unframe z
  let v := ofBits (Turing.MultiTapeTM.dropFrame whole)
  if (Turing.MultiTapeTM.dropFrame z).headD false then [false,true]++whole
  else if v=0 then [true,true]
  else [false,false]++Turing.MultiTapeTM.frame (Turing.MultiTapeTM.unframe whole)++(v-1).bits

lemma native_graphFromLessQuery : ComputableTidilyInPolyTime graphFromLessQuery encBits encBits := by
  have hwhole := ComputableTidilyInPolyTime.unframe
  have hv := bitsToNat.comp (ComputableTidilyInPolyTime.dropFrame.comp hwhole)
  have hhead := (headD (encA:=encBool) (encL:=encBits) false).comp ComputableTidilyInPolyTime.dropFrame
  have hupper := bitsAppend (const [false,true]) hwhole
  have hlowerWord := bitsAppend ((bitsFrame encBits).comp (ComputableTidilyInPolyTime.unframe.comp hwhole))
    (natBits.comp (binary_sub' hv (const 1)))
  have hlower := ite_decide (decide_eq' hv (const 0)) (const [true,true])
    (bitsAppend (const [false,false]) hlowerWord)
  have hh := hhead.cond hupper hlower
  exact hh.of_enc_eq (fun z => rfl)

lemma graphFromLessQuery_semantics (F : Word → ℕ) (z : Word) (b : Bool) :
    taggedOracle (NaturalLessLanguage F) (graphFromLessQuery (pairWord z [b])) ↔
      if b then ¬ ofBits (Turing.MultiTapeTM.dropFrame z)<F (Turing.MultiTapeTM.unframe z)
      else ofBits (Turing.MultiTapeTM.dropFrame z)=0 ∨
        ofBits (Turing.MultiTapeTM.dropFrame z)-1<F (Turing.MultiTapeTM.unframe z) := by
  have he : pairWord z [b]=Turing.MultiTapeTM.frame z++[b] := rfl
  rw [he]
  simp only [graphFromLessQuery,unframe_frame_append,dropFrame_frame_append,List.headD_cons]
  cases b with
  | true => simp [taggedOracle,NaturalLessLanguage]
  | false =>
    by_cases hv : ofBits (Turing.MultiTapeTM.dropFrame z)=0
    · simp [hv,taggedOracle]
    · have hbits (n : ℕ) : ofBits n.bits=n := Nat.foldr_bit_bits n
      simp [hv,taggedOracle,NaturalLessLanguage,unframe_frame_append,dropFrame_frame_append,
        hbits,List.append_assoc]

lemma forall_one_bit_word (P : Word → Prop) :
    (∀ w : Word,w.length=1 → P w) ↔ P [false] ∧ P [true] := by
  constructor
  · intro h;exact ⟨h [false] rfl,h [true] rfl⟩
  · rintro ⟨hf,ht⟩ w hw
    cases w with
    | nil => simp at hw
    | cons b w =>
      have hnil : w=[] := List.length_eq_zero_iff.mp (by simpa using hw)
      subst w
      cases b <;> assumption

lemma AtCHLevel.graph_from_less {F : Word → ℕ} {j : ℕ}
    (hless : AtCHLevel j (NaturalLessLanguage F)) :
    AtCHLevel (j+3) (NaturalGraphLanguage F) := by
  have hh := hless.native_tagged_forall graphFromLessQuery
    native_graphFromLessQuery.computableInPolyTime 1 0 (by decide)
  have he : (fun z => ∀ w : Word,w.length=polyBound 1 0 z.length →
      taggedOracle (NaturalLessLanguage F) (graphFromLessQuery (pairWord z w)))=NaturalGraphLanguage F := by
    funext z
    apply propext
    simp only [polyBound,pow_zero,mul_one,forall_one_bit_word,graphFromLessQuery_semantics,
      Bool.false_eq_true,ite_false,ite_true]
    change (ofBits (Turing.MultiTapeTM.dropFrame z)=0 ∨
      ofBits (Turing.MultiTapeTM.dropFrame z)-1<F (Turing.MultiTapeTM.unframe z)) ∧
      ¬ ofBits (Turing.MultiTapeTM.dropFrame z)<F (Turing.MultiTapeTM.unframe z) ↔
      F (Turing.MultiTapeTM.unframe z)=ofBits (Turing.MultiTapeTM.dropFrame z)
    omega
  rw [he] at hh
  exact hh

end APSCounting893.Main
end Component_36

section Component_37
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace APSCounting893.Main
open Turing.MultiTapeTM

lemma variable_sum_less_in_ch (F : Word → ℕ) (j a b c d : ℕ)
    (rho sigma : Word → ℕ)
    (hrho : ComputableTidilyInPolyTime rho encBits encUnary)
    (hsigma : ComputableTidilyInPolyTime sigma encBits encUnary)
    (hr : ∀ x,rho x≤polyBound a b x.length) (hs : ∀ x,sigma x≤polyBound c d x.length)
    (hless : AtCHLevel j (NaturalLessLanguage F))
    (hF : ∀ x i : Word,i.length=rho x →
      F (Turing.MultiTapeTM.frame x++i)≤2^sigma x) :
    AtCHLevel (j+5) (NaturalLessLanguage (indexedNaturalSumWithWidth F rho)) := by
  have hpre := hless.native_tagged_preimage (variableSumQuery rho sigma)
    (native_variableSumQuery rho sigma hrho hsigma).computableInPolyTime
  have hcount := hpre.count_threshold (a+c+2) (max b d+1) (by omega)
  have he : (fun z => ofBits (Turing.MultiTapeTM.dropFrame z)<
      Set.ncard {w : Word | w.length+1=polyBound (a+c+2) (max b d+1) z.length ∧
        taggedOracle (NaturalLessLanguage F) (variableSumQuery rho sigma (pairWord z w))})=
      NaturalLessLanguage (indexedNaturalSumWithWidth F rho) := by
    funext z
    apply propext
    let Q := polyBound (a+c+2) (max b d+1) z.length
    have hQ : 0<Q := by dsimp [Q,polyBound];positivity
    have hc := smallSum_word_clock a b c d z
    have hN : rho (Turing.MultiTapeTM.unframe z)+sigma (Turing.MultiTapeTM.unframe z)≤Q-1 := by
      have h1 := hr (Turing.MultiTapeTM.unframe z)
      have h2 := hs (Turing.MultiTapeTM.unframe z)
      dsimp [Q]
      omega
    have hset : {w : Word | w.length+1=Q ∧
        taggedOracle (NaturalLessLanguage F) (variableSumQuery rho sigma (pairWord z w))}=
        {w : Word | w.length=Q-1 ∧
          taggedOracle (NaturalLessLanguage F) (variableSumQuery rho sigma (pairWord z w))} := by
      ext w
      have hl : w.length+1=Q ↔ w.length=Q-1 := by omega
      simp only [Set.mem_ofPred_eq,hl]
    change ofBits (Turing.MultiTapeTM.dropFrame z)<Set.ncard {w : Word |
      w.length+1=Q ∧ taggedOracle (NaturalLessLanguage F) (variableSumQuery rho sigma (pairWord z w))} ↔ _
    rw [hset,variableSum_count_identity F rho sigma z (Q-1) hN (hF _)]
    rfl
  rw [he] at hcount
  simpa only [Nat.add_assoc] using hcount

lemma variable_sum_graph_in_ch (F : Word → ℕ) (j a b c d : ℕ)
    (rho sigma : Word → ℕ)
    (hrho : ComputableTidilyInPolyTime rho encBits encUnary)
    (hsigma : ComputableTidilyInPolyTime sigma encBits encUnary)
    (hr : ∀ x,rho x≤polyBound a b x.length) (hs : ∀ x,sigma x≤polyBound c d x.length)
    (hless : AtCHLevel j (NaturalLessLanguage F))
    (hF : ∀ x i : Word,i.length=rho x →
      F (Turing.MultiTapeTM.frame x++i)≤2^sigma x) :
    AtCHLevel (j+8) (NaturalGraphLanguage (indexedNaturalSumWithWidth F rho)) := by
  simpa only [Nat.add_assoc] using
    (variable_sum_less_in_ch F j a b c d rho sigma hrho hsigma hr hs hless hF).graph_from_less

end APSCounting893.Main
end Component_37

section Component_38
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace APSCounting893.Main
open Turing.MultiTapeTM

lemma naturals_equal_iff_bounded_word_bits (a b p : ℕ)
    (ha : a.bits.length ≤ p) (hb : b.bits.length ≤ p) :
    a=b ↔ ∀ w : Word,w.length=p → a.testBit (ofBits w)=b.testBit (ofBits w) := by
  constructor
  · intro h;rw [h];simp
  · intro h
    apply Nat.eq_of_testBit_eq
    intro q
    by_cases hq : q<2^p
    · have hw := h (Cslib.BitString.lowBits p q) (Cslib.BitString.length_lowBits _ _)
      simpa only [ofBits_eq_lsbValue,Cslib.BitString.lsbValue_lowBits hq] using hw
    · have hpq : p≤q := by
        have hpp : p≤2^p := Nat.lt_two_pow_self.le
        omega
      have haa : a<2^q := (Nat.size_le.mp (by simpa only [Nat.size_eq_bits_len] using ha.trans hpq))
      have hbb : b<2^q := (Nat.size_le.mp (by simpa only [Nat.size_eq_bits_len] using hb.trans hpq))
      rw [Nat.testBit_eq_false_of_lt haa,Nat.testBit_eq_false_of_lt hbb]

lemma graph_bit_clock_bounds (F : Word → ℕ) (a b : ℕ)
    (hF : ∀ x,(F x).bits.length≤polyBound a b x.length) (z : Word) :
    (F (Turing.MultiTapeTM.unframe z)).bits.length≤polyBound (a+1) (b+1) z.length ∧
      (ofBits (Turing.MultiTapeTM.dropFrame z)).bits.length≤polyBound (a+1) (b+1) z.length := by
  have hlen := length_unframe_add_dropFrame_le z
  have hword := Nat.foldr_bit_lt (Turing.MultiTapeTM.dropFrame z)
  have hv : (ofBits (Turing.MultiTapeTM.dropFrame z)).bits.length≤(Turing.MultiTapeTM.dropFrame z).length := by
    rw [Nat.size_eq_bits_len]
    exact Nat.size_le.mpr hword
  have hp : z.length+1≤(z.length+1)^(b+1) := by
    simpa only [pow_one] using Nat.pow_le_pow_right (n:=z.length+1) (by omega) (show 1≤b+1 by omega)
  have hpow : ((Turing.MultiTapeTM.unframe z).length+1)^b≤(z.length+1)^(b+1) :=
    (Nat.pow_le_pow_left (by omega) b).trans (Nat.pow_le_pow_right (by omega) (Nat.le_succ b))
  constructor
  · apply (hF _).trans
    change a*((Turing.MultiTapeTM.unframe z).length+1)^b≤(a+1)*(z.length+1)^(b+1)
    exact Nat.mul_le_mul (Nat.le_succ a) hpow
  · apply hv.trans
    change _≤(a+1)*(z.length+1)^(b+1)
    nlinarith

end APSCounting893.Main
end Component_38

section Component_39
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace APSCounting893.Main
open Turing.MultiTapeTM Cslib.BitString

lemma natural_short_less_in_ch (F : Word → ℕ) (j a b : ℕ)
    (hF : ∀ x,(F x).bits.length≤polyBound a b x.length)
    (hgraph : AtCHLevel j (NaturalGraphLanguage F)) :
    AtCHLevel (j+3) (NaturalLessLanguage F) := by
  have hh := hgraph.native_tagged_exists naturalLessQuery
    native_naturalLessQuery.computableInPolyTime (a+1) (b+1) (by omega)
  have he : (fun z => ∃ w : Word,w.length=polyBound (a+1) (b+1) z.length ∧
      taggedOracle (NaturalGraphLanguage F) (naturalLessQuery (pairWord z w)))=NaturalLessLanguage F := by
    funext z
    apply propext
    change (∃ w : Word,w.length=polyBound (a+1) (b+1) z.length ∧
      taggedOracle (NaturalGraphLanguage F) (naturalLessQuery (pairWord z w))) ↔
      ofBits (Turing.MultiTapeTM.dropFrame z)<F (Turing.MultiTapeTM.unframe z)
    simp only [naturalLessQuery_semantics]
    constructor
    · rintro ⟨w,hlen,hlt,heq⟩
      simpa only [heq] using hlt
    · intro h
      have hb := (graph_bit_clock_bounds F a b hF z).1
      have hp : F (Turing.MultiTapeTM.unframe z)<2^polyBound (a+1) (b+1) z.length :=
        Nat.size_le.mp (by simpa only [Nat.size_eq_bits_len] using hb)
      refine ⟨lowBits _ (F (Turing.MultiTapeTM.unframe z)),length_lowBits _ _,?_,?_⟩
      · simpa only [ofBits_eq_lsbValue,lsbValue_lowBits hp] using h
      · simp only [ofBits_eq_lsbValue,lsbValue_lowBits hp]
  rw [he] at hh
  exact hh

end APSCounting893.Main
end Component_39

section Component_40
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime

def blockIndexWidth (a b : ℕ) (y : Word) : ℕ :=
  polyBound a b (Turing.MultiTapeTM.unframe y).length

def blockValueWidth (a b : ℕ) (y : Word) : ℕ := blockIndexWidth a b y+1

noncomputable def naturalBlockSum (F : Word → ℕ) (a b : ℕ) : Word → ℕ :=
  indexedNaturalSumWithWidth (naturalBitBlock F a b) (blockIndexWidth a b)

lemma native_blockIndexWidth (a b : ℕ) : ComputableTidilyInPolyTime
    (blockIndexWidth a b) encBits encUnary :=
  (native_polyBound_unary a b).comp (length_bits.comp ComputableTidilyInPolyTime.unframe)

lemma native_blockValueWidth (a b : ℕ) : ComputableTidilyInPolyTime
    (blockValueWidth a b) encBits encUnary :=
  unary_add.comp ((native_blockIndexWidth a b).prod (const 1))

lemma blockIndexWidth_bound (a b : ℕ) (y : Word) :
    blockIndexWidth a b y≤polyBound a b y.length := by
  have hlen := length_unframe_add_dropFrame_le y
  exact Nat.mul_le_mul_left a (Nat.pow_le_pow_left (by omega) b)

lemma blockValueWidth_bound (a b : ℕ) (y : Word) :
    blockValueWidth a b y≤polyBound (a+1) (b+1) y.length := by
  have hlen := length_unframe_add_dropFrame_le y
  have hp : ((Turing.MultiTapeTM.unframe y).length+1)^b≤(y.length+1)^(b+1) :=
    (Nat.pow_le_pow_left (by omega) b).trans (Nat.pow_le_pow_right (by omega) (Nat.le_succ b))
  have hU : 1≤(y.length+1)^(b+1) := Nat.one_le_pow _ _ (by omega)
  unfold blockValueWidth blockIndexWidth polyBound
  nlinarith [Nat.mul_le_mul_left a hp]

lemma naturalBitBlock_value_bound (F : Word → ℕ) (a b : ℕ) (y i : Word) :
    naturalBitBlock F a b (Turing.MultiTapeTM.frame y++i)≤2^blockValueWidth a b y := by
  unfold naturalBitBlock naturalBlockWidth blockValueWidth blockIndexWidth
  rw [unframe_frame_append]
  exact (Nat.mod_lt _ (by positivity)).le

lemma AtCHLevel.natural_block_sums {F : Word → ℕ} {j : ℕ}
    (hF : AtCHLevel j (NaturalBitLanguage F)) (a b : ℕ) :
    AtCHLevel (j+16) (NaturalGraphLanguage (naturalBlockSum F a b)) := by
  have hgraph := hF.natural_bit_blocks a b
  have hless := natural_short_less_in_ch (naturalBitBlock F a b) (j+5) (a+1) (b+1)
    (naturalBitBlock_length_bound F a b) hgraph
  have hs := variable_sum_graph_in_ch (naturalBitBlock F a b) (j+8) a b (a+1) (b+1)
    (blockIndexWidth a b) (blockValueWidth a b) (native_blockIndexWidth a b) (native_blockValueWidth a b)
    (blockIndexWidth_bound a b) (blockValueWidth_bound a b) hless
    (fun y i _ => naturalBitBlock_value_bound F a b y i)
  simpa only [Nat.add_assoc,naturalBlockSum] using hs

lemma indexedNaturalSumWithWidth_at (F : Word → ℕ) (rho : Word → ℕ) (x : Word)
    (n : ℕ) (hn : rho x=n) :
    indexedNaturalSumWithWidth F rho x=
      ∑ i : Fin (2^n),F (Turing.MultiTapeTM.frame x++Cslib.BitString.lowBits n i.val) := by
  subst n
  rfl

lemma naturalBlockSum_eq (F : Word → ℕ) (a b : ℕ) (x : Word) (k : ℕ) :
    naturalBlockSum F a b (Turing.MultiTapeTM.frame x++k.bits)=
      ∑ i : Fin (2^polyBound a b x.length),
        (F (Turing.MultiTapeTM.frame x++Cslib.BitString.lowBits (polyBound a b x.length) i.val)/
          (2^(polyBound a b x.length+1))^k)%2^(polyBound a b x.length+1) := by
  have hr : blockIndexWidth a b (Turing.MultiTapeTM.frame x++k.bits)=polyBound a b x.length := by
    simp only [blockIndexWidth,unframe_frame_append]
  unfold naturalBlockSum
  rw [indexedNaturalSumWithWidth_at _ _ _ _ hr]
  apply Finset.sum_congr rfl
  intro i _
  simp only [naturalBitBlock,naturalBlockWidth,naturalBlockSource,naturalBlockIndex,
    unframe_frame_append,dropFrame_frame_append,ofBits,Nat.foldr_bit_bits,
    Nat.shiftRight_eq_div_pow,pow_mul]


end APSCounting893.Main
end Component_40

section Component_41
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.constructorNameAsVariable false
namespace APSCounting893.Main
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime Cslib.BitString
lemma encodeFixedNatFields_length (W : ℕ) (values : List ℕ) :
    (encodeFixedNatFields W values).length=values.length*W := by
  induction values with
  | nil => simp [encodeFixedNatFields]
  | cons v vs ih =>
    simp only [encodeFixedNatFields,List.flatMap_cons,List.length_append,length_lowBits,List.length_cons,Nat.add_mul,one_mul] at *
    omega

lemma readWordField_zero (W v : ℕ) (rest : Word) :
    readWordField W 0 (lowBits W v++rest)=lowBits W v := by
  unfold readWordField
  simp only [Nat.zero_mul,List.drop_zero]
  simpa only [length_lowBits] using
    (show (lowBits W v++rest).take (lowBits W v).length=lowBits W v from List.take_left)

lemma readWordField_successor (W v i : ℕ) (rest : Word) :
    readWordField W (i+1) (lowBits W v++rest)=readWordField W i rest := by
  unfold readWordField
  rw [Nat.add_mul,one_mul,Nat.add_comm (i*W),←List.drop_drop]
  have hd : (lowBits W v++rest).drop W=rest := by
    simpa only [length_lowBits] using
      (show (lowBits W v++rest).drop (lowBits W v).length=rest from List.drop_left)
  rw [hd]

lemma readWordField_encode (W : ℕ) (values : List ℕ) (rest : Word) (i : ℕ) (hi : i<values.length) :
    readWordField W i (encodeFixedNatFields W values++rest)=lowBits W values[i] := by
  induction values generalizing i with
  | nil => simp at hi
  | cons v vs ih =>
    cases i with
    | zero => simpa only [encodeFixedNatFields,List.flatMap_cons,List.append_assoc,List.getElem_cons_zero] using
        readWordField_zero W v (encodeFixedNatFields W vs++rest)
    | succ i =>
      simp only [encodeFixedNatFields,List.flatMap_cons,List.append_assoc,List.getElem_cons_succ]
      rw [readWordField_successor]
      exact ih i (by simpa only [List.length_cons,Nat.succ_lt_succ_iff] using hi)

lemma readNatField_encode (W : ℕ) (values : List ℕ) (rest : Word) (i : ℕ) (hi : i<values.length)
    (hv : values[i]<2^W) :
    readNatField W i (encodeFixedNatFields W values++rest)=values[i] := by
  unfold readNatField
  rw [readWordField_encode W values rest i hi,ofBits_eq_lsbValue,lsbValue_lowBits hv]

lemma readNatField_lt (W i : ℕ) (w : Word) : readNatField W i w<2^W := by
  have hlen : (readWordField W i w).length≤W := by simp [readWordField]
  have hbits := Nat.foldr_bit_lt (readWordField W i w)
  exact hbits.trans_le (Nat.pow_le_pow_right (by decide) hlen)
end APSCounting893.Main
end Component_41

section Component_42
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace APSCounting893.Main

def blockCarry (B : ℕ) (s : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | k+1 => (s k+blockCarry B s k)/B

def blockCarryBase (B : ℕ) (s : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | k+1 => s k/B

def blockCarryExtra (B : ℕ) (s : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | k+1 => if B ≤ s k%B+blockCarryBase B s k+blockCarryExtra B s k then 1 else 0

lemma blockCarry_lt (B : ℕ) (hB : 0 < B) (s : ℕ → ℕ)
    (hs : ∀ k,s k ≤ B*(B-1)) (k : ℕ) : blockCarry B s k < B := by
  induction k with
  | zero => exact hB
  | succ k ih =>
    simp only [blockCarry]
    apply (Nat.div_lt_iff_lt_mul hB).mpr
    have hb : B-1+1=B := Nat.sub_add_cancel hB
    nlinarith [hs k]

lemma blockCarry_eq_base_add_extra (B : ℕ) (hB : 0 < B) (s : ℕ → ℕ)
    (hs : ∀ k,s k ≤ B*(B-1)) (k : ℕ) :
    blockCarry B s k=blockCarryBase B s k+blockCarryExtra B s k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hc := blockCarry_lt B hB s hs k
    change (s k+blockCarry B s k)/B = s k/B+
      if B ≤ s k%B+blockCarryBase B s k+blockCarryExtra B s k then 1 else 0
    rw [Nat.add_div hB,Nat.div_eq_of_lt hc,Nat.mod_eq_of_lt hc,Nat.add_zero,ih]
    simp only [Nat.add_assoc]

lemma blockCarryExtra_zero_or_one (B : ℕ) (s : ℕ → ℕ) (k : ℕ) :
    blockCarryExtra B s k=0 ∨ blockCarryExtra B s k=1 := by
  cases k with
  | zero => exact Or.inl rfl
  | succ k => simp only [blockCarryExtra];split_ifs <;> simp

lemma blockCarryExtra_step (B : ℕ) (s : ℕ → ℕ) (k : ℕ) :
    blockCarryExtra B s (k+1)=1 ↔
      B ≤ s k%B+blockCarryBase B s k ∨
        (s k%B+blockCarryBase B s k+1=B ∧ blockCarryExtra B s k=1) := by
  have he := blockCarryExtra_zero_or_one B s k
  simp only [blockCarryExtra,ite_eq_left_iff,zero_ne_one,imp_false,not_not]
  rcases he with h|h <;> rw [h] <;> omega

lemma blockCarryExtra_generate_propagate (B : ℕ) (s : ℕ → ℕ) (k : ℕ) :
    blockCarryExtra B s (k+1)=1 ↔
      ∃ j ≤ k,B ≤ s j%B+blockCarryBase B s j ∧
        ∀ l,j < l → l ≤ k → s l%B+blockCarryBase B s l+1=B := by
  induction k with
  | zero =>
    rw [blockCarryExtra_step]
    simp only [blockCarryExtra,zero_ne_one,and_false,or_false,Nat.le_zero]
    constructor
    · intro h;exact ⟨0,rfl,h,by intro l hl hl';omega⟩
    · rintro ⟨j,rfl,h,_⟩;exact h
  | succ k ih =>
    rw [blockCarryExtra_step,ih]
    constructor
    · rintro (h|⟨hp,j,hj,hg,hprop⟩)
      · exact ⟨k+1,le_rfl,h,by intro l hl hl';omega⟩
      · refine ⟨j,by omega,hg,?_⟩
        intro l hlt hle
        by_cases hl : l=k+1
        · simpa only [hl] using hp
        · exact hprop l hlt (by omega)
    · rintro ⟨j,hj,hg,hprop⟩
      by_cases he : j=k+1
      · exact Or.inl (by simpa only [he] using hg)
      · refine Or.inr ⟨hprop (k+1) (by omega) le_rfl,j,by omega,hg,?_⟩
        intro l hl hle
        exact hprop l hl (by omega)

end APSCounting893.Main
end Component_42

section Component_43
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace APSCounting893.Main

def carryGenerate (B : ℕ) (s : ℕ → ℕ) (j : ℕ) : Prop :=
  B ≤ s j%B+blockCarryBase B s j

def carryPropagate (B : ℕ) (s : ℕ → ℕ) (j : ℕ) : Prop :=
  s j%B+blockCarryBase B s j+1=B

lemma carry_one_witness (B : ℕ) (s : ℕ → ℕ) (k : ℕ) :
    blockCarryExtra B s k=1 ↔ ∃ J<k,carryGenerate B s J ∧
      ∀ U,J<U → U<k → carryPropagate B s U := by
  cases k with
  | zero => simp [blockCarryExtra]
  | succ k =>
    simpa only [Nat.lt_succ_iff,carryGenerate,carryPropagate] using
      blockCarryExtra_generate_propagate B s k

lemma carry_zero_counterwitness (B : ℕ) (s : ℕ → ℕ) (k : ℕ) :
    blockCarryExtra B s k=0 ↔
      ∀ U,U<k → ¬carryGenerate B s U ∨
        ∃ L,U<L ∧ L<k ∧ ¬carryPropagate B s L := by
  classical
  constructor
  · intro hz U hU
    by_cases hg : carryGenerate B s U
    · right
      by_contra hn
      push_neg at hn
      have hp : ∀ L,U<L → L<k → carryPropagate B s L := by
        intro L hUL hL
        exact hn L hUL hL
      have ho := (carry_one_witness B s k).mpr ⟨U,hU,hg,hp⟩
      omega
    · exact Or.inl hg
  · intro h
    rcases blockCarryExtra_zero_or_one B s k with hz|ho
    · exact hz
    · obtain ⟨J,hJ,hg,hp⟩ := (carry_one_witness B s k).mp ho
      rcases h J hJ with hng|⟨L,hJL,hL,hbad⟩
      · exact (hng hg).elim
      · exact (hbad (hp L hJL hL)).elim

open Classical in
lemma bounded_carry_certificate (B : ℕ) (s : ℕ → ℕ) (k K : ℕ)
    (hK : 1<K) (hk : k<K) (P : ℕ → Prop) :
    P (blockCarryExtra B s k) ↔
      ∃ c J,c<K ∧ J<K ∧ c≤1 ∧ P c ∧ (c=1 → J<k) ∧
        ∀ U,U<K → ∃ L,L<K ∧
          (if c=1 then carryGenerate B s J ∧
              (J<U → U<k → carryPropagate B s U)
            else U<k → ¬carryGenerate B s U ∨
              (U<L ∧ L<k ∧ ¬carryPropagate B s L)) := by
  constructor
  · intro hP
    rcases blockCarryExtra_zero_or_one B s k with hz|ho
    · refine ⟨0,0,by omega,by omega,by omega,by simpa only [hz] using hP,by omega,?_⟩
      intro U hUK
      by_cases hU : U<k
      · rcases (carry_zero_counterwitness B s k).mp hz U hU with hng|⟨L,hUL,hL,hbad⟩
        · refine ⟨0,by omega,?_⟩
          simp only [zero_ne_one,ite_false]
          exact fun _ => Or.inl hng
        · refine ⟨L,by omega,?_⟩
          simp only [zero_ne_one,ite_false]
          exact fun _ => Or.inr ⟨hUL,hL,hbad⟩
      · refine ⟨0,by omega,?_⟩
        simp only [zero_ne_one,ite_false]
        exact fun h => (hU h).elim
    · obtain ⟨J,hJ,hg,hp⟩ := (carry_one_witness B s k).mp ho
      refine ⟨1,J,by omega,by omega,by omega,by simpa only [ho] using hP,by intro _;exact hJ,?_⟩
      intro U hUK
      exact ⟨0,by omega,by simpa only [ite_true] using And.intro hg (hp U)⟩
  · rintro ⟨c,J,hcK,hJK,hc,hPc,hJ,hforall⟩
    have hc01 : c=0 ∨ c=1 := by omega
    rcases hc01 with rfl|rfl
    · have hz : blockCarryExtra B s k=0 := by
        apply (carry_zero_counterwitness B s k).mpr
        intro U hU
        obtain ⟨L,hL,hmat⟩ := hforall U (by omega)
        simp only [zero_ne_one,ite_false] at hmat
        rcases hmat hU with hng|hbad
        · exact Or.inl hng
        · exact Or.inr ⟨L,hbad⟩
      simpa only [hz] using hPc
    · have hJk := hJ rfl
      have hg : carryGenerate B s J := by
        obtain ⟨L,hL,hmat⟩ := hforall 0 (by omega)
        exact (by simpa only [ite_true] using hmat : carryGenerate B s J ∧
          (J<0 → 0<k → carryPropagate B s 0)).1
      have hp : ∀ U,J<U → U<k → carryPropagate B s U := by
        intro U hJU hU
        obtain ⟨L,hL,hmat⟩ := hforall U (by omega)
        simp only [ite_true] at hmat
        exact hmat.2 hJU hU
      have ho := (carry_one_witness B s k).mpr ⟨J,hJk,hg,hp⟩
      simpa only [ho] using hPc

end APSCounting893.Main
end Component_43

section Component_44
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace APSCounting893.Main

lemma remainder_power_successor (B k v : ℕ) :
    v%(B^(k+1))=v%(B^k)+B^k*((v/B^k)%B) := by
  rw [pow_succ,Nat.mod_mul]

lemma sum_remainder_power_successor {ι : Type} [Fintype ι] (B k : ℕ) (v : ι → ℕ) :
    (∑ i,v i%(B^(k+1)))=(∑ i,v i%(B^k))+B^k*(∑ i,(v i/B^k)%B) := by
  simp only [remainder_power_successor,Finset.sum_add_distrib,Finset.mul_sum]

lemma blockCarry_eq_sum_remainders {ι : Type} [Fintype ι] (B : ℕ) (hB : 0 < B)
    (v : ι → ℕ) (k : ℕ) :
    blockCarry B (fun j => ∑ i,(v i/B^j)%B) k = (∑ i,v i%B^k)/B^k := by
  induction k with
  | zero => simp only [blockCarry,pow_zero,Nat.mod_one,Finset.sum_const_zero,Nat.zero_div]
  | succ k ih =>
    have hpow : 0 < B^k := by positivity
    rw [blockCarry,ih,sum_remainder_power_successor,pow_succ,←Nat.div_div_eq_div_mul,
      Nat.add_mul_div_left _ _ hpow]
    congr 1
    omega

lemma sum_block_digit {ι : Type} [Fintype ι] (B : ℕ) (hB : 0 < B)
    (v : ι → ℕ) (k : ℕ) :
    ((∑ i,v i)/B^k)%B =
      ((∑ i,(v i/B^k)%B)+blockCarry B (fun j => ∑ i,(v i/B^j)%B) k)%B := by
  rw [blockCarry_eq_sum_remainders B hB v k]
  have hpow : 0 < B^k := by positivity
  have he : (∑ i,v i)=(∑ i,v i%B^k)+B^k*(∑ i,v i/B^k) := by
    rw [Finset.mul_sum,←Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => (Nat.mod_add_div (v i) (B^k)).symm)
  rw [he,Nat.add_mul_div_left _ _ hpow,Nat.add_mod]
  rw [Finset.sum_nat_mod,←Nat.add_mod]
  congr 1
  omega

lemma blockSums_bound {ι : Type} [Fintype ι] (B : ℕ) (hB : 0 < B)
    (hN : Fintype.card ι ≤ B) (v : ι → ℕ) (k : ℕ) :
    (∑ i,(v i/B^k)%B) ≤ B*(B-1) := by
  have hh : (∑ i,(v i/B^k)%B) ≤ Fintype.card ι*(B-1) := by
    simpa using Finset.sum_le_sum (s:=Finset.univ)
      (show ∀ i ∈ (Finset.univ : Finset ι),(v i/B^k)%B ≤ B-1 from fun i _ => by
        have := Nat.mod_lt (v i/B^k) hB
        omega)
  exact hh.trans (Nat.mul_le_mul_right (B-1) hN)

end APSCounting893.Main
end Component_44

section Component_45
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace APSCounting893.Main

lemma testBit_via_binary_block (S W q : ℕ) (hW : 0 < W) :
    S.testBit q=((S/(2^W)^(q/W))%2^W).testBit (q%W) := by
  have hq : q%W<W := Nat.mod_lt q hW
  rw [Nat.testBit_mod_two_pow]
  simp only [hq,decide_true,Bool.true_and]
  rw [←pow_mul,Nat.testBit_div_two_pow,Nat.mod_add_div]

open Classical in
lemma sum_bit_bounded_carry_certificate {ι : Type} [Fintype ι] (v : ι → ℕ)
    (W q K : ℕ) (hW : 0 < W) (hN : Fintype.card ι≤2^W)
    (hK : 1<K) (hk : q/W<K) :
    let B := 2^W
    let s := fun j => ∑ i,(v i/B^j)%B
    let k := q/W
    (∑ i,v i).testBit q=true ↔
      ∃ c J,c<K ∧ J<K ∧ c≤1 ∧
        ((s k+blockCarryBase B s k+c)%B).testBit (q%W)=true ∧
        (c=1 → J<k) ∧
        ∀ U,U<K → ∃ L,L<K ∧
          (if c=1 then carryGenerate B s J ∧
              (J<U → U<k → carryPropagate B s U)
            else U<k → ¬carryGenerate B s U ∨
              (U<L ∧ L<k ∧ ¬carryPropagate B s L)) := by
  let B := 2^W
  let s := fun j => ∑ i,(v i/B^j)%B
  let k := q/W
  have hB : 0<B := by dsimp [B];positivity
  have hs : ∀ j,s j≤B*(B-1) := fun j => blockSums_bound B hB hN v j
  have hd := sum_block_digit B hB v k
  change ((∑ i,v i)/B^k)%B=(s k+blockCarry B s k)%B at hd
  have hb := blockCarry_eq_base_add_extra B hB s hs k
  rw [testBit_via_binary_block _ W q hW]
  change (((∑ i,v i)/B^k)%B).testBit (q%W)=true ↔ _
  rw [hd,hb]
  simp only [Nat.add_assoc]
  simpa only [Nat.add_assoc] using bounded_carry_certificate B s k K hK hk
    (fun c => ((s k+blockCarryBase B s k+c)%B).testBit (q%W)=true)

end APSCounting893.Main
end Component_45

section Component_46
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.constructorNameAsVariable false
namespace APSCounting893.Main
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime Cslib.BitString
lemma longSumFieldWidth_pos (a b : ℕ) (z : Word) : 0 < longSumFieldWidth a b z := by
  unfold longSumFieldWidth polyBound
  positivity

lemma longSumFieldWidth_bounds (a b : ℕ) (z x : Word) (hlen : x.length ≤ z.length) :
    2*polyBound a b x.length+1 ≤ longSumFieldWidth a b z ∧
    z.length+1 ≤ longSumFieldWidth a b z := by
  have hm : (x.length+1)^b ≤ (z.length+1)^(b+1) :=
    (Nat.pow_le_pow_left (by omega) b).trans (Nat.pow_le_pow_right (by omega) (Nat.le_succ b))
  have hpow : z.length+1 ≤ (z.length+1)^(b+1) := by
    simpa using Nat.pow_le_pow_right (by omega : 1 ≤ z.length+1) (by omega : 1 ≤ b+1)
  have hone : 1 ≤ (z.length+1)^(b+1) := Nat.one_le_pow _ _ (by omega)
  unfold longSumFieldWidth polyBound
  constructor <;> nlinarith [Nat.mul_le_mul_left (2*a) hm]

lemma naturalBlockSum_uniform_bound (F : Word → ℕ) (a b : ℕ) (x : Word) (k : ℕ) :
    naturalBlockSum F a b (Turing.MultiTapeTM.frame x++k.bits) <
      2^(2*polyBound a b x.length+1) := by
  rw [naturalBlockSum_eq]
  let r := polyBound a b x.length
  have hs : (∑ i : Fin (2^r),
      (F (Turing.MultiTapeTM.frame x++lowBits r i.val)/(2^(r+1))^k)%2^(r+1)) <
        (2^r)*2^(r+1) := by
    calc
      _ < ∑ _i : Fin (2^r), 2^(r+1) := by
        apply Finset.sum_lt_sum
        · intro i hi; exact (Nat.mod_lt _ (by positivity)).le
        · exact ⟨⟨0,by positivity⟩, Finset.mem_univ _, Nat.mod_lt _ (by positivity)⟩
      _ = _ := by simp
  simpa only [←pow_add, Nat.add_assoc, two_mul] using hs

lemma exists_word_fields (W L : ℕ) (values : List ℕ)
    (hL : values.length*W ≤ L) (hv : ∀ v ∈ values,v < 2^W) :
    ∃ w : Word,w.length=L ∧
      ∀ i (hi : i < values.length), readNatField W i w=values[i] := by
  refine ⟨encodeFixedNatFields W values++List.replicate (L-values.length*W) false,?_,?_⟩
  · simp only [List.length_append,encodeFixedNatFields_length,List.length_replicate]
    omega
  · intro i hi
    exact readNatField_encode W values _ i hi (hv _ (List.getElem_mem hi))
end APSCounting893.Main
end Component_46

section Component_47
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace APSCounting893.Main
open Turing.MultiTapeTM

lemma naturalBitQuery_lengths (x : Word) (q : ℕ) :
    x.length ≤ (naturalBitQuery x q).length ∧
    q < 2^((naturalBitQuery x q).length+1) := by
  have hx := length_unframe_add_dropFrame_le (naturalBitQuery x q)
  simp only [naturalBitQuery,unframe_frame_append,dropFrame_frame_append] at hx
  have hq : q < 2^q.bits.length := by
    simpa only [Nat.foldr_bit_bits] using Nat.foldr_bit_lt q.bits
  have hlen : q.bits.length ≤ (naturalBitQuery x q).length+1 := by
    simp only [naturalBitQuery,encodeNat,List.length_append,List.length_replicate,List.length_cons,List.length_nil]
    omega
  exact ⟨by simpa only [naturalBitQuery] using (show x.length ≤ (Turing.MultiTapeTM.frame x++encodeNat q).length from by omega),hq.trans_le (Nat.pow_le_pow_right (by decide) hlen)⟩

lemma longSumQuery_bounds (a b : ℕ) (x : Word) (q : ℕ) :
    let W := longSumFieldWidth a b (naturalBitQuery x q)
    1 < 2^W ∧ q/(polyBound a b x.length+1) < 2^W ∧
      ∀ F : Word → ℕ,∀ i : ℕ,naturalBlockSum F a b (Turing.MultiTapeTM.frame x++i.bits) < 2^W := by
  let z := naturalBitQuery x q
  have hz := naturalBitQuery_lengths x q
  have hW := longSumFieldWidth_bounds a b z x hz.1
  have hpos := longSumFieldWidth_pos a b z
  change 1 < 2^(longSumFieldWidth a b z) ∧ q/(polyBound a b x.length+1) < 2^(longSumFieldWidth a b z) ∧ _
  refine ⟨?_,?_,?_⟩
  · exact Nat.one_lt_pow (by omega : longSumFieldWidth a b z ≠ 0) (by decide : 1 < (2 : ℕ))
  · exact (Nat.div_le_self _ _).trans_lt (hz.2.trans_le (Nat.pow_le_pow_right (by decide) hW.2))
  · intro F i
    exact (naturalBlockSum_uniform_bound F a b x i).trans_le (Nat.pow_le_pow_right (by decide) hW.1)

lemma blockCarryBase_eq_if (B : ℕ) (s : ℕ → ℕ) (i : ℕ) :
    blockCarryBase B s i=if i=0 then 0 else s (i-1)/B := by
  cases i <;> simp [blockCarryBase]

end APSCounting893.Main
end Component_47

section Component_48
set_option autoImplicit false
set_option maxHeartbeats 2200000
namespace APSCounting893.Main
open Turing.MultiTapeTM

def CarryNumericalMatrix (B : ℕ) (s : ℕ → ℕ) (k pos c J U L : ℕ) : Prop :=
  c ≤ 1 ∧ ((s k+blockCarryBase B s k+c)%B).testBit pos=true ∧
    (c=1 → J < k) ∧
      (if c=1 then carryGenerate B s J ∧ (J < U → U < k → carryPropagate B s U)
       else U < k → ¬carryGenerate B s U ∨ (U < L ∧ L < k ∧ ¬carryPropagate B s L))

lemma carryMatrixGuard_specification (F : Word → ℕ) (a b : ℕ) (p : CarryMatrixInput)
    (hg : CarryMatrixGraphs F a b p) :
    carryMatrixGuard a b p=true ↔
      CarryNumericalMatrix (carryMatrixBase a b p)
        (fun i => F (Turing.MultiTapeTM.frame p.x++i.bits))
        (carryMatrixIndex a b p) (carryMatrixPosition a b p)
        p.carry p.generator p.universal p.counter := by
  rcases hg with ⟨h0,h1,h2,h3,h4,h5⟩
  unfold carryMatrixGuard carryMatrixOutput carryMatrixGeneration carryMatrixPropagation
    carryOutputTest carryGenerateTest carryPropagateTest
  rw [←h0,←h1,←h2,←h3,←h4,←h5]
  unfold CarryNumericalMatrix carryGenerate carryPropagate carryBaseValue
  simp only [blockCarryBase_eq_if]
  by_cases hc : p.carry=1
  · simp [hc,carryMatrixGenIndex,carryMatrixPropIndex,and_assoc] <;> omega
  · simp [hc,carryMatrixGenIndex,carryMatrixPropIndex,and_assoc] <;> omega

end APSCounting893.Main
end Component_48

section Component_49
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option linter.constructorNameAsVariable false
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main
attribute [local irreducible] longSumMatrixQuery carryMatrixQuery
open Turing.MultiTapeTM Cslib.BitString

def longSumPackedData (a b : ℕ) (root outer univ inner x : Word) (q : ℕ) : CarryMatrixInput :=
  let W := longSumFieldWidth a b root
  (x,q,readNatField W 0 outer,readNatField W 1 outer,readNatField W 0 univ,
    readNatField W 0 inner,readWordField W 2 outer,readWordField W 3 outer,
    readWordField W 1 inner,readWordField W 2 inner,readWordField W 3 inner,readWordField W 4 inner)

lemma longSumMatrixQuery_packed (a b : ℕ) (root outer univ inner sel x : Word) (q : ℕ)
    (hr : parseNaturalBitQuery root=some (x,q)) :
    longSumMatrixQuery a b (pairWord (pairWord (pairWord (pairWord root outer) univ) inner) sel)=
      carryMatrixQuery a b (longSumPackedData a b root outer univ inner x q,ofBits sel) := by
  simp only [longSumMatrixQuery,longSumRoot,longSumMatrixData,longSumOuter,longSumUniversal,
    longSumInner,longSumSelector,unframe_pairWord,dropFrame_pairWord,hr,longSumPackedData]

lemma longSumMatrixQuery_selectors (F : Word → ℕ) (a b : ℕ) (root outer univ inner x : Word)
    (q : ℕ) (hr : parseNaturalBitQuery root=some (x,q)) :
    (∀ sel : Word,sel.length=3 →
      taggedOracle (NaturalGraphLanguage F)
        (longSumMatrixQuery a b (pairWord (pairWord (pairWord (pairWord root outer) univ) inner) sel))) ↔
    let p := longSumPackedData a b root outer univ inner x q
    carryMatrixGuard a b p=true ∧ CarryMatrixGraphs F a b p := by
  rw [←carryMatrixQuery_all]
  constructor
  · intro h i
    have hi : ofBits (lowBits 3 i.val)=i.val := by
      rw [ofBits_eq_lsbValue,lsbValue_lowBits (by simpa using i.isLt)]
    have hh : taggedOracle (NaturalGraphLanguage F)
        (longSumMatrixQuery a b (pairWord (pairWord (pairWord (pairWord root outer) univ) inner) (lowBits 3 i.val))) :=
      h (lowBits 3 i.val) (length_lowBits _ _)
    rwa [longSumMatrixQuery_packed a b root outer univ inner _ x q hr,hi] at hh
  · intro h sel hlen
    have hb : ofBits sel<8 := by
      have hh := Nat.foldr_bit_lt sel
      simpa only [ofBits,hlen,show (2 : ℕ)^3=8 by decide] using hh
    rw [longSumMatrixQuery_packed a b root outer univ inner sel x q hr]
    exact h ⟨ofBits sel,hb⟩

end APSCounting893.Main
end Component_49

section Component_50
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace APSCounting893.Main
open Turing.MultiTapeTM

lemma longSumPackedGuard_spec (F : Word → ℕ) (a b : ℕ) (root outer univ inner x : Word) (q : ℕ)
    (hg : CarryMatrixGraphs F a b (longSumPackedData a b root outer univ inner x q)) :
    carryMatrixGuard a b (longSumPackedData a b root outer univ inner x q)=true ↔
      let W := longSumFieldWidth a b root
      CarryNumericalMatrix (2^(polyBound a b x.length+1))
        (fun i => F (Turing.MultiTapeTM.frame x++i.bits))
        (q/(polyBound a b x.length+1)) (q%(polyBound a b x.length+1))
        (readNatField W 0 outer) (readNatField W 1 outer)
        (readNatField W 0 univ) (readNatField W 0 inner) := by
  exact carryMatrixGuard_specification F a b _ hg

lemma longSumPackedGraphs_spec (F : Word → ℕ) (a b : ℕ) (root outer univ inner x : Word) (q : ℕ) :
    let W := longSumFieldWidth a b root
    let s := fun i => F (Turing.MultiTapeTM.frame x++i.bits)
    let k := q/(polyBound a b x.length+1)
    let g := if readNatField W 0 outer=1 then readNatField W 1 outer else readNatField W 0 univ
    let p := if readNatField W 0 outer=1 then readNatField W 0 univ else readNatField W 0 inner
    CarryMatrixGraphs F a b (longSumPackedData a b root outer univ inner x q) ↔
      s k=readNatField W 2 outer ∧ s (k-1)=readNatField W 3 outer ∧
      s g=readNatField W 1 inner ∧ s (g-1)=readNatField W 2 inner ∧
      s p=readNatField W 3 inner ∧ s (p-1)=readNatField W 4 inner := by
  rfl

end APSCounting893.Main
end Component_50

section Component_51
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.constructorNameAsVariable false
namespace APSCounting893.Main
open Turing.MultiTapeTM Cslib.BitString

def LongSumWordCertificate (F : Word → ℕ) (a b : ℕ) (root x : Word) (q : ℕ)
    (lo : ℕ) (lu : Word → ℕ) (li : Word → Word → ℕ) : Prop :=
  ∃ outer : Word,outer.length=lo ∧
    ∀ univ : Word,univ.length=lu outer →
      ∃ inner : Word,inner.length=li outer univ ∧
        let p := longSumPackedData a b root outer univ inner x q
        carryMatrixGuard a b p=true ∧ CarryMatrixGraphs F a b p

lemma longSumWordCertificate_iff (F : Word → ℕ) (a b : ℕ) (root x : Word) (q lo : ℕ)
    (lu : Word → ℕ) (li : Word → Word → ℕ)
    (ho : 4*longSumFieldWidth a b root ≤ lo)
    (hu : ∀ o,longSumFieldWidth a b root ≤ lu o)
    (hi : ∀ o u,5*longSumFieldWidth a b root ≤ li o u)
    (hK : 1 < 2^longSumFieldWidth a b root)
    (hk : q/(polyBound a b x.length+1) < 2^longSumFieldWidth a b root)
    (hF : ∀ i : ℕ,F (Turing.MultiTapeTM.frame x++i.bits) < 2^longSumFieldWidth a b root) :
    LongSumWordCertificate F a b root x q lo lu li ↔
      let W := longSumFieldWidth a b root
      let B := 2^(polyBound a b x.length+1)
      let s := fun i : ℕ => F (Turing.MultiTapeTM.frame x++i.bits)
      let k := q/(polyBound a b x.length+1)
      ∃ c J,c < 2^W ∧ J < 2^W ∧
        ∀ U,U < 2^W → ∃ L,L < 2^W ∧
          CarryNumericalMatrix B s k (q%(polyBound a b x.length+1)) c J U L := by
  let W := longSumFieldWidth a b root
  let K := 2^W
  let s := fun i : ℕ => F (Turing.MultiTapeTM.frame x++i.bits)
  let k := q/(polyBound a b x.length+1)
  constructor
  · rintro ⟨o,holen,hall⟩
    let c := readNatField W 0 o
    let J := readNatField W 1 o
    refine ⟨c,J,readNatField_lt W 0 o,readNatField_lt W 1 o,?_⟩
    intro U hU
    obtain ⟨u,hlen,hfields⟩ := exists_word_fields W (lu o) [U] (by simpa using hu o)
      (by simpa using hU)
    obtain ⟨inn,hilen,hmat⟩ := hall u hlen
    refine ⟨readNatField W 0 inn,readNatField_lt W 0 inn,?_⟩
    have hnum := (longSumPackedGuard_spec F a b root o u inn x q hmat.2).mp hmat.1
    have huf : readNatField W 0 u=U := by simpa using hfields 0 (by simp)
    change CarryNumericalMatrix _ _ _ _ c J (readNatField W 0 u) (readNatField W 0 inn) at hnum
    rw [huf] at hnum
    exact hnum
  · rintro ⟨c,J,hc,hJ,hall⟩
    obtain ⟨o,holen,hof⟩ := exists_word_fields W lo [c,J,s k,s (k-1)] (by simpa using ho)
      (by simp only [List.mem_cons,List.not_mem_nil,or_false];intro v hv;rcases hv with rfl|rfl|rfl|rfl;exact hc;exact hJ;exact hF _;exact hF _)
    refine ⟨o,holen,?_⟩
    intro u hulen
    let U := readNatField W 0 u
    obtain ⟨L,hL,hnum⟩ := hall U (readNatField_lt W 0 u)
    let g := if c=1 then J else U
    let p := if c=1 then U else L
    obtain ⟨inn,hilen,hif⟩ := exists_word_fields W (li o u) [L,s g,s (g-1),s p,s (p-1)] (by simpa using hi o u)
      (by simp only [List.mem_cons,List.not_mem_nil,or_false];intro v hv;rcases hv with rfl|rfl|rfl|rfl|rfl;exact hL;exact hF _;exact hF _;exact hF _;exact hF _)
    have ho0 : readNatField W 0 o=c := by simpa using hof 0 (by simp)
    have ho1 : readNatField W 1 o=J := by simpa using hof 1 (by simp)
    have ho2 : readNatField W 2 o=s k := by simpa using hof 2 (by simp)
    have ho3 : readNatField W 3 o=s (k-1) := by simpa using hof 3 (by simp)
    have hi0 : readNatField W 0 inn=L := by simpa using hif 0 (by simp)
    have hi1 : readNatField W 1 inn=s g := by simpa using hif 1 (by simp)
    have hi2 : readNatField W 2 inn=s (g-1) := by simpa using hif 2 (by simp)
    have hi3 : readNatField W 3 inn=s p := by simpa using hif 3 (by simp)
    have hi4 : readNatField W 4 inn=s (p-1) := by simpa using hif 4 (by simp)
    have hgraphs : CarryMatrixGraphs F a b (longSumPackedData a b root o u inn x q) := by
      have hgs := longSumPackedGraphs_spec F a b root o u inn x q
      dsimp only at hgs
      rw [hgs]
      change s k=readNatField W 2 o ∧ s (k-1)=readNatField W 3 o ∧
        s (if readNatField W 0 o=1 then readNatField W 1 o else U)=readNatField W 1 inn ∧
        s ((if readNatField W 0 o=1 then readNatField W 1 o else U)-1)=readNatField W 2 inn ∧
        s (if readNatField W 0 o=1 then U else readNatField W 0 inn)=readNatField W 3 inn ∧
        s ((if readNatField W 0 o=1 then U else readNatField W 0 inn)-1)=readNatField W 4 inn
      simp only [ho0,ho1,ho2,ho3,hi0,hi1,hi2,hi3,hi4,g,p]
      exact ⟨trivial,trivial,trivial,trivial,trivial,trivial⟩
    refine ⟨inn,hilen,?_,hgraphs⟩
    apply (longSumPackedGuard_spec F a b root o u inn x q hgraphs).mpr
    change CarryNumericalMatrix _ _ _ _ (readNatField W 0 o) (readNatField W 1 o) U (readNatField W 0 inn)
    rw [ho0,ho1,hi0]
    exact hnum

end APSCounting893.Main
end Component_51

section Component_52
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace APSCounting893.Main

open Classical in
lemma sum_bit_numerical_prefix {ι : Type} [Fintype ι] (v : ι → ℕ)
    (W q K : ℕ) (hW : 0 < W) (hN : Fintype.card ι ≤ 2^W)
    (hK : 1 < K) (hk : q/W < K) :
    let B := 2^W
    let s := fun j => ∑ i,(v i/B^j)%B
    let k := q/W
    (∑ i,v i).testBit q=true ↔
      ∃ c J,c < K ∧ J < K ∧
        ∀ U,U < K → ∃ L,L < K ∧ CarryNumericalMatrix B s k (q%W) c J U L := by
  have hcert := sum_bit_bounded_carry_certificate v W q K hW hN hK hk
  dsimp only at hcert ⊢
  rw [hcert]
  constructor
  · rintro ⟨c,J,hc,hJ,hcone,hout,hJk,hall⟩
    refine ⟨c,J,hc,hJ,?_⟩
    intro U hU
    obtain ⟨L,hL,hmat⟩ := hall U hU
    exact ⟨L,hL,hcone,hout,hJk,hmat⟩
  · rintro ⟨c,J,hc,hJ,hall⟩
    obtain ⟨L,hL,hhead⟩ := hall 0 (by omega)
    refine ⟨c,J,hc,hJ,hhead.1,hhead.2.1,hhead.2.2.1,?_⟩
    intro U hU
    obtain ⟨L,hL,hmat⟩ := hall U hU
    exact ⟨L,hL,hmat.2.2.2⟩

end APSCounting893.Main
end Component_52

section Component_53
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.constructorNameAsVariable false
namespace APSCounting893.Main
attribute [local irreducible] longSumMatrixQuery carryMatrixQuery
open Turing.MultiTapeTM Cslib.BitString

lemma pairWord_length_left (x w : Word) : x.length ≤ (pairWord x w).length := by
  change x.length ≤ (Turing.MultiTapeTM.frame x++w).length
  simp only [List.length_append,length_frame]
  omega

lemma longSumCarryLanguage_certificate (F : Word → ℕ) (a b : ℕ) (root x : Word) (q : ℕ)
    (hr : parseNaturalBitQuery root=some (x,q)) :
    longSumCarryLanguage F a b root ↔
      LongSumWordCertificate F a b root x q
        (polyBound (4*(2*a+3)) (b+1) root.length)
        (fun o => polyBound (2*a+3) (b+1) (pairWord root o).length)
        (fun o u => polyBound (5*(2*a+3)) (b+1) (pairWord (pairWord root o) u).length) := by
  unfold longSumCarryLanguage LongSumWordCertificate
  apply exists_congr
  intro o
  apply and_congr_right
  intro ho
  apply forall_congr'
  intro u
  apply imp_congr_right
  intro hu
  apply exists_congr
  intro inn
  apply and_congr_right
  intro hi
  exact longSumMatrixQuery_selectors F a b root o u inn x q hr

lemma longSumCarryLanguage_code (F : Word → ℕ) (a b : ℕ) (x : Word) (q : ℕ) :
    longSumCarryLanguage (naturalBlockSum F a b) a b (naturalBitQuery x q) ↔
      (indexedNaturalSum F a b x).testBit q=true := by
  let root := naturalBitQuery x q
  let W := longSumFieldWidth a b root
  let G := naturalBlockSum F a b
  rw [longSumCarryLanguage_certificate G a b root x q (parseNaturalBitQuery_code x q)]
  have ho : 4*W ≤ polyBound (4*(2*a+3)) (b+1) root.length := by
    simp [W,longSumFieldWidth,polyBound,Nat.mul_assoc]
  have hu : ∀ o,W ≤ polyBound (2*a+3) (b+1) (pairWord root o).length := by
    intro o
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by have h := pairWord_length_left root o;omega) (b+1))
  have hi : ∀ o u,5*W ≤ polyBound (5*(2*a+3)) (b+1) (pairWord (pairWord root o) u).length := by
    intro o u
    have hh := (pairWord_length_left root o).trans (pairWord_length_left (pairWord root o) u)
    have hp := Nat.mul_le_mul_left (5*(2*a+3)) (Nat.pow_le_pow_left (by omega : root.length+1 ≤ (pairWord (pairWord root o) u).length+1) (b+1))
    simpa only [W,longSumFieldWidth,polyBound,←Nat.mul_assoc] using hp
  have hb := longSumQuery_bounds a b x q
  dsimp only at hb
  rw [longSumWordCertificate_iff G a b root x q _ _ _ ho hu hi hb.1 hb.2.1 (hb.2.2 F)]
  let r := polyBound a b x.length
  let v := fun i : Fin (2^r) => F (Turing.MultiTapeTM.frame x++lowBits r i.val)
  have hn := sum_bit_numerical_prefix v (r+1) q (2^W) (by omega)
    (by simp only [Fintype.card_fin];exact Nat.pow_le_pow_right (by decide) (Nat.le_succ r)) hb.1 hb.2.1
  dsimp only at hn ⊢
  have hs : (fun k => ∑ i : Fin (2^r),(v i/(2^(r+1))^k)%2^(r+1))=
      (fun k => G (Turing.MultiTapeTM.frame x++k.bits)) := by
    funext k
    exact (naturalBlockSum_eq F a b x k).symm
  rw [hs] at hn
  exact hn.symm

end APSCounting893.Main
end Component_53

section Component_54
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.constructorNameAsVariable false
namespace APSCounting893.Main
attribute [local irreducible] longSumMatrixQuery carryMatrixQuery
open Turing.MultiTapeTM

lemma longSumCarryLanguage_invalid (F : Word → ℕ) (a b : ℕ) (root : Word)
    (hp : parseNaturalBitQuery root=none) : ¬longSumCarryLanguage F a b root := by
  rintro ⟨o,ho,hall⟩
  let u := List.replicate (polyBound (2*a+3) (b+1) (pairWord root o).length) false
  obtain ⟨inn,hi,hsel⟩ := hall u (by simp [u])
  have hh : taggedOracle (NaturalGraphLanguage F)
      (longSumMatrixQuery a b (pairWord (pairWord (pairWord (pairWord root o) u) inn) (List.replicate 3 false))) :=
    hsel (List.replicate 3 false) (by simp)
  simp only [longSumMatrixQuery,longSumRoot,unframe_pairWord,hp,taggedOracle] at hh
  cases hh

lemma naturalBitLanguage_invalid (F : Word → ℕ) (root : Word)
    (hp : parseNaturalBitQuery root=none) : ¬NaturalBitLanguage F root := by
  rintro ⟨x,q,rfl,hbit⟩
  rw [parseNaturalBitQuery_code] at hp
  cases hp

end APSCounting893.Main
end Component_54

section Component_55
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.constructorNameAsVariable false
namespace APSCounting893.Main

lemma longSumCarryLanguage_eq (F : Word → ℕ) (a b : ℕ) :
    longSumCarryLanguage (naturalBlockSum F a b) a b=NaturalBitLanguage (indexedNaturalSum F a b) := by
  funext root
  apply propext
  cases hp : parseNaturalBitQuery root with
  | none =>
    exact iff_of_false (longSumCarryLanguage_invalid _ a b root hp) (naturalBitLanguage_invalid _ root hp)
  | some xq =>
    have hr := parseNaturalBitQuery_inverse root xq.1 xq.2 hp
    rw [hr,longSumCarryLanguage_code,naturalBitQuery_correct]

lemma implicit_long_integer_sums_in_ch_proof (F : Word → ℕ) (j a b : ℕ)
    (hF : AtCHLevel j (NaturalBitLanguage F)) :
    AtCHLevel (j+22) (NaturalBitLanguage (indexedNaturalSum F a b)) := by
  have hG := hF.natural_block_sums a b
  have hcarry := hG.long_sum_carry_language a b
  rw [longSumCarryLanguage_eq] at hcarry
  simpa only [Nat.add_assoc] using hcarry

end APSCounting893.Main
end Component_55

open APSCounting893.Main
theorem solution (F : Word → ℕ) (j a b : ℕ)
    (hF : AtCHLevel j (NaturalBitLanguage F)) :
    AtCHLevel (j+22) (NaturalBitLanguage (indexedNaturalSum F a b)) := by
  exact implicit_long_integer_sums_in_ch_proof F j a b hF
