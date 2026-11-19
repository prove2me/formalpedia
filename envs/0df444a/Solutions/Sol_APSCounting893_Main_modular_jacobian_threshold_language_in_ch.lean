-- Prove2me | solution 1 for APSCounting893.Main.modular_jacobian_threshold_language_in_ch
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T19:26:52.363936+00:00
-- url     : https://prove2.me/submissions/dab7b9e5-196f-4d77-8cdf-49e66778f0a9

import Definitions.Def_APSCounting893_Main_ModularJacobianComputation
import Definitions.Def_APSCounting893_Main_ModularJacobianData
import Definitions.Def_APSCounting893_Main_OracleProofPrimitives
import Definitions.Def_APSCounting893_Main_SampledResultant
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_BitString
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Iteration
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Nat_Binary
import Mathlib
import Theorems.Thm_APSCounting893_Main_bounded_quantification_oracle_pp
import Theorems.Thm_APSCounting893_Main_native_modular_jacobian_verification
import Theorems.Thm_APSCounting893_Main_native_polynomial_simulation
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
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime

lemma native_decodeSignedNat : ComputableTidilyInPolyTime decodeSignedNat encBits
    (encOption (encPair (encPair encBool encNat) encBits)) := by
  have htail:=bitsDropWithInput (id' (encIn:=encBits)) (const 1)
  have hvalue:=native_decodeNat.comp htail
  have hword:=fst encBits (encPair encNat encBits)
  have hparsed:=snd encBits (encPair encNat encBits)
  have hsign:=bitsGetDWithInput hword (const 0) false
  have hnumber:=(fst encNat encBits).comp hparsed
  have hrest:=(snd encNat encBits).comp hparsed
  have hbody:=(optionSome (encPair (encPair encBool encNat) encBits)).comp ((hsign.prod hnumber).prod hrest)
  have hh:=optionElimWithInput (body:=fun (w : Word) (p : ℕ × Word)=>some ((w.getD 0 false,p.1),p.2))
    hvalue (const (none : Option ((Bool × ℕ) × Word))) hbody
  apply hh.of_enc_eq
  intro w
  unfold decodeSignedNat
  dsimp only [Function.comp_apply]
  cases decodeNat (w.drop 1) <;> rfl

lemma decodeSignedNat_encodeInt (z : ℤ) (rest : Word) :
    decodeSignedNat (encodeInt z++rest)=some ((decide (z<0),z.natAbs),rest) := by
  simp [decodeSignedNat,encodeInt,decodeNat_code]

end APSCounting893.Main
end Component_4

section Component_5
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime

lemma native_decoderBind {α β : Type} (encA : α ↪ Word) (encB : β ↪ Word)
    (da : Word → Option (α × Word)) (db : α → Word → Option (β × Word))
    (ha : ComputableTidilyInPolyTime da encBits (encOption (encPair encA encBits)))
    (hb : ComputableTidilyInPolyTime (fun p : α × Word=>db p.1 p.2)
      (encPair encA encBits) (encOption (encPair encB encBits))) :
    ComputableTidilyInPolyTime (decoderBind da db) encBits (encOption (encPair encB encBits)) := by
  have hbody:=hb.comp (snd encBits (encPair encA encBits))
  exact optionElimWithInput (body:=fun (_ : Word) (p : α × Word)=>db p.1 p.2)
    ha (const (none : Option (β × Word))) hbody


lemma native_decoderPair {α β : Type} (encA : α ↪ Word) (encB : β ↪ Word)
    (da : Word → Option (α × Word)) (db : Word → Option (β × Word))
    (ha : ComputableTidilyInPolyTime da encBits (encOption (encPair encA encBits)))
    (hb : ComputableTidilyInPolyTime db encBits (encOption (encPair encB encBits))) :
    ComputableTidilyInPolyTime (decoderPair da db) encBits (encOption (encPair (encPair encA encB) encBits)) := by
  have hvalue:=hb.comp (snd encA encBits)
  have hsaved:=fst (encPair encA encBits) (encPair encB encBits)
  have hparsed:=snd (encPair encA encBits) (encPair encB encBits)
  have hleft:=(fst encA encBits).comp hsaved
  have hright:=(fst encB encBits).comp hparsed
  have hrest:=(snd encB encBits).comp hparsed
  have hsome:=(optionSome (encPair (encPair encA encB) encBits)).comp ((hleft.prod hright).prod hrest)
  have hinner:=optionElimWithInput
    (body:=fun (saved : α × Word) (p : β × Word)=>some ((saved.1,p.1),p.2))
    hvalue (const (none : Option ((α × β) × Word))) hsome
  exact native_decoderBind encA (encPair encA encB) da _ ha hinner

lemma decoderPair_success {α β : Type} (da : Word → Option (α × Word))
    (db : Word → Option (β × Word)) (w rest rest' : Word) (a : α) (b : β)
    (ha : da w=some (a,rest)) (hb : db rest=some (b,rest')) :
    decoderPair da db w=some ((a,b),rest') := by
  simp [decoderPair,decoderBind,ha,hb]

end APSCounting893.Main
end Component_5

section Component_6
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime

lemma native_decodeRawRational : ComputableTidilyInPolyTime decodeRawRational encBits
    (encOption (encPair (encPair (encPair encBool encNat) encNat) encBits)) :=
  native_decoderPair (encPair encBool encNat) encNat decodeSignedNat decodeNat native_decodeSignedNat native_decodeNat

lemma decodeRawRational_encodeRat (q : ℚ) (rest : Word) :
    decodeRawRational (encodeRat q++rest)=some (((decide (q.num<0),q.num.natAbs),q.den),rest) := by
  apply decoderPair_success decodeSignedNat decodeNat _ (encodeNat q.den++rest) rest _ _
  · simpa [encodeRat,List.append_assoc] using decodeSignedNat_encodeInt q.num (encodeNat q.den++rest)
  · exact decodeNat_code q.den rest

end APSCounting893.Main
end Component_6

section Component_7
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime

lemma native_decoderManyStep {α : Type} (encA : α ↪ Word)
    (da : Word → Option (α × Word))
    (ha : ComputableTidilyInPolyTime da encBits (encOption (encPair encA encBits))) :
    ComputableTidilyInPolyTime
      (fun p : (ℕ × Word) × ManyState α => decoderManyStep da p.1 p.2)
      (encPair (encPair encNat encBits) (encOption (encPair (encList encA) encBits)))
      (encOption (encPair (encList encA) encBits)) := by
  let encI := encPair encNat encBits
  let encS := encPair (encList encA) encBits
  have hi := (fst (encPair encI (encOption encS)) encS).fst'
  have hs := snd (encPair encI (encOption encS)) encS
  have hacc := hs.fst'
  have hcursor := hs.snd'
  have hcount := hi.fst'
  have hlimit := length_bits.comp hi.snd'
  have hparse := ha.comp (bitsTakeWithInput hcursor hlimit)
  have hsaved := fst (encPair (encPair encI (encOption encS)) encS) (encPair encA encBits)
  have hparsed := snd (encPair (encPair encI (encOption encS)) encS) (encPair encA encBits)
  have hnewacc := cons' hparsed.fst' (hacc.comp hsaved)
  have hnew := (optionSome encS).comp (hnewacc.prod hparsed.snd')
  have hbody := optionElimWithInput
    (body := fun (saved : ((ℕ × Word) × ManyState α) × (List α × Word))
      (p : α × Word) => some (p.1 :: saved.2.1,p.2))
    hparse (const (none : ManyState α)) hnew
  have hguard := decide_eq' (unary_to_binary.comp ((length_list encA).comp hacc)) hcount
  have hkeep := (optionSome encS).comp hs
  have hinner := hguard.ite_decide hkeep hbody
  exact optionElimWithInput
    (body := fun (p : (ℕ × Word) × ManyState α) (s : List α × Word) =>
      if s.1.length = p.1.1 then some s
      else (da (s.2.take p.1.2.length)).elim none fun q => some (q.1 :: s.1,q.2))
    (snd encI (encOption encS)) (const (none : ManyState α)) hinner

end APSCounting893.Main
end Component_7

section Component_8
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace APSCounting893.Main
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime

lemma decoderManyStep_growth {α : Type} (encA : α ↪ Word)
    (da : Word → Option (α × Word)) (c d : ℕ)
    (hsize : ∀ w, (encOption (encPair encA encBits) (da w)).length ≤ c*(w.length+1)^d)
    (input : ℕ × Word) (state : ManyState α) :
    (encOption (encPair (encList encA) encBits) (decoderManyStep da input state)).length ≤
      (encOption (encPair (encList encA) encBits) state).length +
        2*c*(input.2.length+1)^d := by
  cases state with
  | none => simp [decoderManyStep]
  | some s =>
    unfold decoderManyStep
    simp only [Option.elim_some]
    split
    · omega
    · have h := hsize (s.2.take input.2.length)
      have hlen : (s.2.take input.2.length).length+1 ≤ input.2.length+1 := by
        simp only [List.length_take]; omega
      have hp : c*((s.2.take input.2.length).length+1)^d ≤ c*(input.2.length+1)^d :=
        Nat.mul_le_mul_left c (Nat.pow_le_pow_left hlen d)
      cases hd : da (s.2.take input.2.length) with
      | none => simp
      | some p =>
        rw [hd] at h
        simp only [Option.elim_some,encOption_some,List.length_cons,length_encPair,
          encList_cons,List.length_append,length_frame,encBits_apply] at h ⊢
        simp only [Nat.mul_assoc] at *
        omega

lemma native_decoderManyLoop {α : Type} (encA : α ↪ Word)
    (da : Word → Option (α × Word))
    (ha : ComputableTidilyInPolyTime da encBits (encOption (encPair encA encBits))) :
    ComputableTidilyInPolyTime (decoderManyLoop da) (encPair encNat encBits)
      (encOption (encPair (encList encA) encBits)) := by
  obtain ⟨c,d,hsize⟩ := ha.polyBounded_length.exists_le
  let encI := encPair encNat encBits
  let encS := encPair (encList encA) encBits
  have hcount := length_bits.comp (snd encNat encBits)
  have hinit := (optionSome encS).comp ((const ([] : List α)).prod (snd encNat encBits))
  apply iterateWithInput_of_bounded_growth hcount hinit (native_decoderManyStep encA da ha)
  refine ⟨PolyBounded.of_forall_le (2*c) d ?_,decoderManyStep_growth encA da c d ?_⟩
  · intro input
    have hlen := length_le_encPair_right encNat encBits input
    simp only [encBits_apply] at hlen
    exact Nat.mul_le_mul_left (2*c) (Nat.pow_le_pow_left (Nat.add_le_add_right hlen 1) d)
  · simpa only [encBits_apply] using hsize

end APSCounting893.Main
end Component_8

section Component_9
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime

lemma native_decoderMany {α : Type} (encA : α ↪ Word)
    (da : Word → Option (α × Word))
    (ha : ComputableTidilyInPolyTime da encBits (encOption (encPair encA encBits))) :
    ComputableTidilyInPolyTime (decoderMany da) (encPair encNat encBits)
      (encOption (encPair (encList encA) encBits)) := by
  let encI := encPair encNat encBits
  let encS := encPair (encList encA) encBits
  have hi := fst encI encS
  have hs := snd encI encS
  have hguard := decide_eq' (unary_to_binary.comp ((length_list encA).comp hs.fst')) hi.fst'
  have hreverse := (listReverse encA).comp hs.fst'
  have hsome := (optionSome encS).comp (hreverse.prod hs.snd')
  have hbody := hguard.ite_decide hsome (const (none : ManyState α))
  exact optionElimWithInput
    (body := fun (p : ℕ × Word) (s : List α × Word) =>
      if s.1.length = p.1 then some (s.1.reverse,s.2) else none)
    (native_decoderManyLoop encA da ha) (const (none : ManyState α)) hbody

lemma native_decoderMap {α β : Type} (encA : α ↪ Word) (encB : β ↪ Word)
    (f : α → β) (da : Word → Option (α × Word))
    (ha : ComputableTidilyInPolyTime da encBits (encOption (encPair encA encBits)))
    (hf : ComputableTidilyInPolyTime f encA encB) :
    ComputableTidilyInPolyTime (decoderMap f da) encBits (encOption (encPair encB encBits)) := by
  have hp := snd encBits (encPair encA encBits)
  have hbody := (optionSome (encPair encB encBits)).comp ((hf.comp hp.fst').prod hp.snd')
  have hh := optionElimWithInput
    (body := fun (_ : Word) (p : α × Word) => some (f p.1,p.2))
    ha (const (none : Option (β × Word))) hbody
  apply hh.of_enc_eq
  intro w
  unfold decoderMap
  cases da w <;> rfl

end APSCounting893.Main
end Component_9

section Component_10
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime

lemma native_decoderWith {α β γ : Type} (encA : α ↪ Word) (encB : β ↪ Word)
    (encC : γ ↪ Word) (da : Word → Option (β × Word)) (f : α → β → γ)
    (ha : ComputableTidilyInPolyTime da encBits (encOption (encPair encB encBits)))
    (hf : ComputableTidilyInPolyTime (fun p : α × β => f p.1 p.2) (encPair encA encB) encC) :
    ComputableTidilyInPolyTime (decoderWith da f) (encPair encA encBits)
      (encOption (encPair encC encBits)) := by
  have hparse := ha.comp (snd encA encBits)
  have hs := fst (encPair encA encBits) (encPair encB encBits)
  have hp := snd (encPair encA encBits) (encPair encB encBits)
  have hv := hf.comp (hs.fst'.prod hp.fst')
  have hsome := (optionSome (encPair encC encBits)).comp (hv.prod hp.snd')
  have hh := optionElimWithInput
    (body := fun (saved : α × Word) (q : β × Word) => some (f saved.1 q.1,q.2))
    hparse (const (none : Option (γ × Word))) hsome
  apply hh.of_enc_eq
  intro p
  unfold decoderWith
  dsimp only [Function.comp_apply]
  cases da p.2 <;> rfl

lemma native_decoderList {α : Type} (encA : α ↪ Word) (da : Word → Option (α × Word))
    (ha : ComputableTidilyInPolyTime da encBits (encOption (encPair encA encBits))) :
    ComputableTidilyInPolyTime (decoderList da) encBits
      (encOption (encPair (encList encA) encBits)) :=
  native_decoderBind encNat (encList encA) decodeNat _ native_decodeNat (native_decoderMany encA da ha)

end APSCounting893.Main
end Component_10

section Component_11
set_option autoImplicit false
namespace APSCounting893.Main
open Turing.MultiTapeTM

end APSCounting893.Main
end Component_11

section Component_12
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime

lemma native_rawVariable : ComputableTidilyInPolyTime rawVariable encNat encRawGate := by
  exact (const 0).prod ((id' (encIn:=encNat)).prod ((const 0).prod (const false)))

lemma native_rawConstant : ComputableTidilyInPolyTime rawConstant
    (encPair (encPair encBool encNat) encNat) encRawGate := by
  have hi := id' (encIn:=encPair (encPair encBool encNat) encNat)
  exact (const 1).prod (hi.fst'.snd'.prod (hi.snd'.prod hi.fst'.fst'))

lemma native_rawOperation : ComputableTidilyInPolyTime
    (fun p : ℕ × (ℕ × ℕ) => rawOperation p.1 p.2)
    (encPair encNat (encPair encNat encNat)) encRawGate := by
  have hi := id' (encIn:=encPair encNat (encPair encNat encNat))
  exact hi.fst'.prod (hi.snd'.fst'.prod (hi.snd'.snd'.prod (const false)))

lemma native_decodeRawConstantBody : ComputableTidilyInPolyTime decodeRawConstantBody
    (encPair encNat encBits) (encOption (encPair encRawGate encBits)) := by
  have hn := fst encNat encBits
  have hw := snd encNat encBits
  have hzero := decide_eq' hn (const 0)
  have hone := decide_eq' hn (const 1)
  have hz := (optionSome (encPair encRawGate encBits)).comp
    ((const (rawConstant ((false,0),1))).prod hw)
  have hr := (native_decoderMap _ _ rawConstant decodeRawRational
    native_decodeRawRational native_rawConstant).comp hw
  exact hzero.ite_decide hz (hone.ite_decide hr (const none))

lemma native_decodeRawConstant : ComputableTidilyInPolyTime decodeRawConstant encBits
    (encOption (encPair encRawGate encBits)) :=
  native_decoderBind encNat encRawGate decodeNat _ native_decodeNat native_decodeRawConstantBody

lemma native_decodeRawGateBody : ComputableTidilyInPolyTime decodeRawGateBody
    (encPair encNat encBits) (encOption (encPair encRawGate encBits)) := by
  have hn := fst encNat encBits
  have hw := snd encNat encBits
  have hzero := decide_eq' hn (const 0)
  have hone := decide_eq' hn (const 1)
  have hsmall := binary_le' hn (const 5)
  have hv := (native_decoderMap encNat encRawGate rawVariable decodeNat
    native_decodeNat native_rawVariable).comp hw
  have hc := native_decodeRawConstant.comp hw
  have hop := native_decoderWith encNat (encPair encNat encNat) encRawGate
    (decoderPair decodeNat decodeNat) rawOperation
    (native_decoderPair encNat encNat decodeNat decodeNat native_decodeNat native_decodeNat)
    native_rawOperation
  exact hzero.ite_decide hv (hone.ite_decide hc (hsmall.ite_decide hop (const none)))

lemma native_decodeRawGate : ComputableTidilyInPolyTime decodeRawGate encBits
    (encOption (encPair encRawGate encBits)) :=
  native_decoderBind encNat encRawGate decodeNat _ native_decodeNat native_decodeRawGateBody

lemma native_decodeRawCircuit : ComputableTidilyInPolyTime decodeRawCircuit encBits
    (encOption (encPair encRawCircuit encBits)) :=
  native_decoderPair encNat (encPair (encList encRawGate) (encList encNat)) decodeNat _
    native_decodeNat
    (native_decoderPair (encList encRawGate) (encList encNat) _ _
      (native_decoderList encRawGate decodeRawGate native_decodeRawGate)
      (native_decoderList encNat decodeNat native_decodeNat))

end APSCounting893.Main
end Component_12

section Component_13
set_option autoImplicit false
set_option maxHeartbeats 2200000
namespace APSCounting893.Main

lemma decoderManyStep_idle {α : Type} (da : Word → Option (α × Word)) (input : ℕ × Word)
    (acc : List α) (rest : Word) (h : acc.length = input.1) :
    decoderManyStep da input (some (acc,rest)) = some (acc,rest) := by
  simp [decoderManyStep,h]

lemma decoderManyStep_steps {α : Type} (da : Word → Option (α × Word))
    (encode : α → Word)
    (hparse : ∀ a rest, da (encode a ++ rest) = some (a,rest))
    (hpos : ∀ a, 0 < (encode a).length)
    (xs acc : List α) (rest : Word) (limit : Word)
    (hlen : (xs.flatMap encode ++ rest).length ≤ limit.length) :
    (decoderManyStep da (acc.length+xs.length,limit))^[xs.length]
      (some (acc,xs.flatMap encode ++ rest)) = some (xs.reverse ++ acc,rest) := by
  induction xs generalizing acc with
  | nil => simp
  | cons a xs ih =>
    rw [List.length_cons,Function.iterate_succ_apply]
    have hne : acc.length ≠ acc.length+(a::xs).length := by simp
    have htake : ((a::xs).flatMap encode ++ rest).take limit.length =
        (a::xs).flatMap encode ++ rest := List.take_of_length_le hlen
    have hstep : decoderManyStep da (acc.length+(a::xs).length,limit)
        (some (acc,(a::xs).flatMap encode ++ rest)) =
        some (a::acc,xs.flatMap encode ++ rest) := by
      simp only [decoderManyStep,Option.elim_some,if_neg hne]
      rw [htake]
      simp [List.flatMap_cons,List.append_assoc,hparse]
    have hstep' := hstep
    simp only [List.length_cons] at hstep'
    rw [hstep']
    have hlen' : (xs.flatMap encode ++ rest).length ≤ limit.length := by
      simp only [List.flatMap_cons,List.length_append] at hlen ⊢
      omega
    have heq : acc.length+(xs.length+1)=(a::acc).length+xs.length := by simp; omega
    simp only [heq]
    rw [ih (a::acc) hlen']
    simp [List.reverse_cons,List.append_assoc]

lemma decoderMany_code {α : Type} (da : Word → Option (α × Word)) (encode : α → Word)
    (hparse : ∀ a rest, da (encode a ++ rest) = some (a,rest))
    (hpos : ∀ a, 0 < (encode a).length) (xs : List α) (rest : Word) :
    decoderMany da (xs.length,xs.flatMap encode ++ rest) = some (xs,rest) := by
  let w := xs.flatMap encode ++ rest
  have hxlen : xs.length ≤ w.length := by
    have hh : ∀ ys : List α, ys.length ≤ (ys.flatMap encode).length := by
      intro ys
      induction ys with
      | nil => simp
      | cons a ys ih =>
        have := hpos a
        simp only [List.length_cons,List.flatMap_cons,List.length_append]
        omega
    have := hh xs
    simp only [w,List.length_append]
    omega
  have hsteps := decoderManyStep_steps da encode hparse hpos xs [] rest w le_rfl
  simp only [List.length_nil,Nat.zero_add,List.append_nil] at hsteps
  have hidle := decoderManyStep_idle da (xs.length,w) xs.reverse rest (by simp)
  have hloop : decoderManyLoop da (xs.length,w)=some (xs.reverse,rest) := by
    unfold decoderManyLoop
    rw [show w.length=(w.length-xs.length)+xs.length by omega,Function.iterate_add_apply,hsteps]
    exact Function.iterate_fixed hidle _
  simp [decoderMany,w,hloop]

end APSCounting893.Main
end Component_13

section Component_14
set_option autoImplicit false
set_option maxHeartbeats 2200000
namespace APSCounting893.Main

lemma decodeRawConstant_empty (rest : Word) :
    decodeRawConstant (encodeList encodeRat [] ++ rest) =
      some (rawConstant ((false,0),1),rest) := by
  simp [decodeRawConstant,decoderBind,encodeList,decodeNat_code,decodeRawConstantBody]

lemma decodeRawConstant_singleton (q : ℚ) (rest : Word) :
    decodeRawConstant (encodeList encodeRat [q] ++ rest) =
      some (rawConstant ((decide (q.num<0),q.num.natAbs),q.den),rest) := by
  simp [decodeRawConstant,decoderBind,encodeList,List.append_assoc,decodeNat_code,
    decodeRawConstantBody,decoderMap,decodeRawRational_encodeRat]

lemma decodeRawGate_code {n : ℕ} (g : ArithmeticGate n)
    (hvalid : match g with | .constant cs => cs.length ≤ 1 | _ => True)
    (rest : Word) :
    decodeRawGate (g.encode ++ rest) = some (g.raw,rest) := by
  cases g with
  | «variable» i =>
    simp [ArithmeticGate.encode,ArithmeticGate.raw,decodeRawGate,decoderBind,
      List.append_assoc,decodeNat_code,decodeRawGateBody,decoderMap]
  | constant cs =>
    have hc : cs=[] ∨ ∃ q, cs=[q] := by
      cases cs with
      | nil => exact Or.inl rfl
      | cons q cs =>
        cases cs with
        | nil => exact Or.inr ⟨q,rfl⟩
        | cons q' cs => simp at hvalid
    rcases hc with rfl | ⟨q,rfl⟩
    · simp [ArithmeticGate.encode,ArithmeticGate.raw,decodeRawGate,decoderBind,
        List.append_assoc,decodeNat_code,decodeRawGateBody,decodeRawConstant_empty]
    · simp [ArithmeticGate.encode,ArithmeticGate.raw,decodeRawGate,decoderBind,
        List.append_assoc,decodeNat_code,decodeRawGateBody,decodeRawConstant_singleton]
  | add a b | sub a b | mul a b | div a b =>
    simp [ArithmeticGate.encode,ArithmeticGate.raw,decodeRawGate,decoderBind,
      List.append_assoc,decodeNat_code,decodeRawGateBody,decoderWith,decoderPair]

lemma arithmeticGate_encode_pos {n : ℕ} (g : ArithmeticGate n) : 0 < g.encode.length := by
  have h (k : ℕ) : 0 < (encodeNat k).length := by
    simp [encodeNat]
  cases g <;> simp only [ArithmeticGate.encode,List.length_append] <;> have := h 0 <;>
    simp only [encodeNat,List.length_append,List.length_replicate,List.length_cons,List.length_nil] <;> omega

end APSCounting893.Main
end Component_14

section Component_15
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace APSCounting893.Main

lemma decoderManyStep_mapped_steps {α β : Type} (da : Word → Option (α × Word))
    (encode : β → Word) (value : β → α)
    (xs : List β)
    (hparse : ∀ a ∈ xs, ∀ rest, da (encode a ++ rest) = some (value a,rest))
    (hpos : ∀ a ∈ xs, 0 < (encode a).length) (acc : List α) (rest : Word) (limit : Word)
    (hlen : (xs.flatMap encode ++ rest).length ≤ limit.length) :
    (decoderManyStep da (acc.length+xs.length,limit))^[xs.length]
      (some (acc,xs.flatMap encode ++ rest)) = some (xs.reverse.map value ++ acc,rest) := by
  induction xs generalizing acc with
  | nil => simp
  | cons a xs ih =>
    rw [List.length_cons,Function.iterate_succ_apply]
    have hne : acc.length ≠ acc.length+(a::xs).length := by simp
    have htake : ((a::xs).flatMap encode ++ rest).take limit.length =
        (a::xs).flatMap encode ++ rest := List.take_of_length_le hlen
    have hstep : decoderManyStep da (acc.length+(a::xs).length,limit)
        (some (acc,(a::xs).flatMap encode ++ rest)) =
        some (value a::acc,xs.flatMap encode ++ rest) := by
      simp only [decoderManyStep,Option.elim_some,if_neg hne]
      rw [htake]
      simp [List.flatMap_cons,List.append_assoc,hparse a (by simp)]
    have hstep' := hstep
    simp only [List.length_cons] at hstep'
    rw [hstep']
    have hlen' : (xs.flatMap encode ++ rest).length ≤ limit.length := by
      simp only [List.flatMap_cons,List.length_append] at hlen ⊢
      omega
    have heq : acc.length+(xs.length+1)=(value a::acc).length+xs.length := by simp; omega
    simp only [heq]
    rw [ih (fun b hb => hparse b (by simp [hb])) (fun b hb => hpos b (by simp [hb])) (value a::acc) hlen']
    simp [List.reverse_cons,List.append_assoc]


lemma decoderMany_mapped_code {α β : Type} (da : Word → Option (α × Word))
    (encode : β → Word) (value : β → α) (xs : List β)
    (hparse : ∀ a ∈ xs, ∀ rest, da (encode a ++ rest) = some (value a,rest))
    (hpos : ∀ a ∈ xs, 0 < (encode a).length) (rest : Word) :
    decoderMany da (xs.length,xs.flatMap encode ++ rest) = some (xs.map value,rest) := by
  let w := xs.flatMap encode ++ rest
  have hh : ∀ (ys : List β), (∀ a ∈ ys, 0 < (encode a).length) →
      ys.length ≤ (ys.flatMap encode).length := by
    intro ys hy
    induction ys with
    | nil => simp
    | cons a ys ih =>
      have ha := hy a (by simp)
      have hi := ih (fun b hb => hy b (by simp [hb]))
      simp only [List.length_cons,List.flatMap_cons,List.length_append]
      omega
  have hxlen : xs.length ≤ w.length := by
    have := hh xs hpos
    simp only [w,List.length_append]
    omega
  have hsteps := decoderManyStep_mapped_steps da encode value xs hparse hpos [] rest w le_rfl
  simp only [List.length_nil,Nat.zero_add,List.append_nil] at hsteps
  have hidle := decoderManyStep_idle da (xs.length,w) (xs.reverse.map value) rest (by simp)
  have hloop : decoderManyLoop da (xs.length,w)=some (xs.reverse.map value,rest) := by
    unfold decoderManyLoop
    rw [show w.length=(w.length-xs.length)+xs.length by omega,Function.iterate_add_apply,hsteps]
    exact Function.iterate_fixed hidle _
  simp [decoderMany,w,hloop,List.map_reverse]

lemma decoderList_mapped_code {α β : Type} (da : Word → Option (α × Word))
    (encode : β → Word) (value : β → α) (xs : List β)
    (hparse : ∀ a ∈ xs, ∀ rest, da (encode a ++ rest) = some (value a,rest))
    (hpos : ∀ a ∈ xs, 0 < (encode a).length) (rest : Word) :
    decoderList da (encodeList encode xs ++ rest) = some (xs.map value,rest) := by
  simp only [decoderList,decoderBind,encodeList,List.append_assoc,decodeNat_code,Option.elim_some]
  exact decoderMany_mapped_code da encode value xs hparse hpos rest

end APSCounting893.Main
end Component_15

section Component_16
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace APSCounting893.Main

lemma decodeRawCircuit_code {n : ℕ} (C : ArithmeticCircuit n)
    (hvalid : ValidCircuit .rational C) (rest : Word) :
    decodeRawCircuit (C.encode ++ rest) = some (C.raw,rest) := by
  have hgate : ∀ g ∈ C.gates, ∀ rest, decodeRawGate (g.encode++rest)=some (g.raw,rest) := by
    intro g hg rest
    apply decodeRawGate_code
    have hh := hvalid.1 g hg
    cases g with
    | constant cs => exact hh.1
    | «variable» i | add a b | sub a b | mul a b | div a b => trivial
  have hgs : ∀ rest, decoderList decodeRawGate (encodeList ArithmeticGate.encode C.gates++rest)=
      some (C.gates.map ArithmeticGate.raw,rest) := by
    intro rest
    exact decoderList_mapped_code decodeRawGate ArithmeticGate.encode ArithmeticGate.raw C.gates
      hgate (fun g _ => arithmeticGate_encode_pos g) rest
  have hos : ∀ rest, decoderList decodeNat (encodeList encodeNat C.outputs++rest)=
      some (C.outputs,rest) := by
    intro rest
    simpa using decoderList_mapped_code decodeNat encodeNat id C.outputs
      (fun a _ rest => decodeNat_code a rest)
      (fun a _ => by simp [encodeNat]) rest
  unfold decodeRawCircuit ArithmeticCircuit.encode ArithmeticCircuit.raw
  apply decoderPair_success decodeNat _ _
    (encodeList ArithmeticGate.encode C.gates ++ encodeList encodeNat C.outputs ++ rest) rest n (C.gates.map ArithmeticGate.raw,C.outputs)
  · simp [List.append_assoc,decodeNat_code]
  · apply decoderPair_success (decoderList decodeRawGate) (decoderList decodeNat) _
      (encodeList encodeNat C.outputs++rest) rest
      (C.gates.map ArithmeticGate.raw) C.outputs
    · simpa [List.append_assoc] using hgs (encodeList encodeNat C.outputs++rest)
    · exact hos rest

end APSCounting893.Main
end Component_16

section Component_17
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime

lemma native_encodeNat : ComputableTidilyInPolyTime encodeNat encNat encBits := by
  have hbits := natBits
  have hprefix := (bitsReplicate true).comp (length_bits.comp hbits)
  have hh := bitsAppend hprefix (bitsAppend (const [false]) hbits)
  apply hh.of_enc_eq
  intro n
  simp [encodeNat,Function.comp_def,List.append_assoc]

lemma native_encodeList {α : Type} (encA : α ↪ Word) (f : α → Word)
    (hf : ComputableTidilyInPolyTime f encA encBits) :
    ComputableTidilyInPolyTime (encodeList f) (encList encA) encBits := by
  have hcount := native_encodeNat.comp (unary_to_binary.comp (length_list encA))
  have hwords := map hf
  have hflat := bitsFlatten hwords
  have hh := bitsAppend hcount hflat
  apply hh.of_enc_eq
  intro xs
  simp only [encodeList,Function.comp_def,List.flatMap_def]

def encodeRawSigned (z : Bool × ℕ) : Word := z.1::encodeNat z.2

lemma native_encodeRawSigned : ComputableTidilyInPolyTime encodeRawSigned
    (encPair encBool encNat) encBits := by
  have hi := id' (encIn:=encPair encBool encNat)
  exact bitsCons hi.fst' (native_encodeNat.comp hi.snd')

def encodeRawAssignment (a : RawAssignment) : Word :=
  encodeList (fun e => encodeNat e.1++encodeRawSigned e.2) a

lemma native_encodeRawAssignment : ComputableTidilyInPolyTime encodeRawAssignment
    encRawAssignment encBits := by
  have hi := id' (encIn:=encPair encNat (encPair encBool encNat))
  exact native_encodeList _ _ (bitsAppend (native_encodeNat.comp hi.fst')
    (native_encodeRawSigned.comp hi.snd'))

lemma decodeSignedNat_raw_code (z : Bool × ℕ) (rest : Word) :
    decodeSignedNat (encodeRawSigned z++rest)=some (z,rest) := by
  rcases z with ⟨b,a⟩
  simp [decodeSignedNat,encodeRawSigned,decodeNat_code]

end APSCounting893.Main
end Component_17

section Component_18
set_option autoImplicit false
namespace APSCounting893.Main
open Turing.MultiTapeTM

abbrev RawModularWitness := ℕ × (List ℕ × (List ℕ × (RawAssignment × List ℕ)))
def encRawModularWitness : RawModularWitness ↪ Word :=
  encPair encNat (encPair (encList encNat) (encPair (encList encNat)
    (encPair encRawAssignment (encList encNat))))

def decodeRawAssignment : Word → Option (RawAssignment × Word) :=
  decoderList (decoderPair decodeNat decodeSignedNat)

def decodeRawModularWitness : Word → Option (RawModularWitness × Word) :=
  decoderPair decodeNat (decoderPair (decoderList decodeNat)
    (decoderPair (decoderList decodeNat) (decoderPair decodeRawAssignment (decoderList decodeNat))))

def encodeRawModularWitness (w : RawModularWitness) : Word :=
  encodeNat w.1++encodeList encodeNat w.2.1++encodeList encodeNat w.2.2.1++
    encodeRawAssignment w.2.2.2.1++encodeList encodeNat w.2.2.2.2

def natListDistinct (xs : List ℕ) : Bool := xs.all fun x => decide (xs.count x ≤ 1)

def rawModularWitnessHeader (length : ℕ) (circuit : RawCircuit) (k : ℕ)
    (w : RawModularWitness) : Bool :=
  decide (k ≤ length ∧ w.2.1.length=k ∧ w.2.2.1.length=k ∧ 2 ≤ w.1 ∧
    w.1.bits.length ≤ 128*(length+1)+8 ∧
    (encodeRawAssignment w.2.2.2.1).length ≤ polyBound 32 2 length ∧
    w.2.2.2.2.length=k*k) &&
  natListDistinct w.2.1 && natListDistinct w.2.2.1 &&
  w.2.1.all (fun o => decide (o<circuit.2.2.length)) &&
  w.2.2.1.all (fun v => decide (v<circuit.1 ∧ v.bits.length ≤ length)) &&
  w.2.2.2.1.all (fun a => decide (a.1<circuit.1 ∧ (a.2.1=true → 0<a.2.2)))

def rawModularWitnessCheck (length : ℕ) (circuit : RawCircuit) (k : ℕ)
    (w : RawModularWitness) : Bool :=
  rawModularWitnessHeader length circuit k w &&
    residueMatrixInverseTest (w.1,(circuit,(w.2.2.2.1,(w.2.1,w.2.2.1)))) w.2.2.2.2

def modularThresholdVerifier (z : Word) : Bool :=
  (decodeRawCircuit (unframe (unframe z))).elim false fun cr =>
    (decodeNat (dropFrame (unframe z))).elim false fun kr =>
      (decodeRawModularWitness (dropFrame z)).elim false fun wr =>
        rawModularWitnessCheck (unframe (unframe z)).length cr.1 kr.1 wr.1

end APSCounting893.Main
end Component_18

section Component_19
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime

lemma native_decodeRawAssignment : ComputableTidilyInPolyTime decodeRawAssignment encBits
    (encOption (encPair encRawAssignment encBits)) :=
  native_decoderList (encPair encNat (encPair encBool encNat)) _
    (native_decoderPair encNat (encPair encBool encNat) decodeNat decodeSignedNat
      native_decodeNat native_decodeSignedNat)

lemma native_decodeRawModularWitness : ComputableTidilyInPolyTime decodeRawModularWitness encBits
    (encOption (encPair encRawModularWitness encBits)) :=
  native_decoderPair encNat _ decodeNat _ native_decodeNat
    (native_decoderPair (encList encNat) _ _ _ (native_decoderList encNat decodeNat native_decodeNat)
      (native_decoderPair (encList encNat) _ _ _ (native_decoderList encNat decodeNat native_decodeNat)
        (native_decoderPair encRawAssignment (encList encNat) _ _ native_decodeRawAssignment
          (native_decoderList encNat decodeNat native_decodeNat))))

lemma native_natListDistinct : ComputableTidilyInPolyTime natListDistinct (encList encNat) encBool := by
  have hi := fst (encList encNat) encNat
  have hx := snd (encList encNat) encNat
  have hcount := countWithInput hi hx
  have htest := binary_le' (unary_to_binary.comp hcount) (const 1)
  exact allWithInput (test:=fun (xs : List ℕ) (x : ℕ) => decide (xs.count x ≤ 1)) id' htest

lemma natListDistinct_iff (xs : List ℕ) : natListDistinct xs=true ↔ xs.Nodup := by
  simp only [natListDistinct,List.all_eq_true,decide_eq_true_eq,List.nodup_iff_count_le_one]
  constructor
  · intro h x
    by_cases hx : x ∈ xs
    · exact h x hx
    · simp [List.count_eq_zero.mpr hx]
  · intro h x _
    exact h x

end APSCounting893.Main
end Component_19

section Component_20
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime

abbrev WitnessHeaderInput := ℕ × (RawCircuit × (ℕ × RawModularWitness))
def encWitnessHeaderInput : WitnessHeaderInput ↪ Word :=
  encPair encNat (encPair encRawCircuit (encPair encNat encRawModularWitness))

lemma native_rawModularWitnessHeader : ComputableTidilyInPolyTime
    (fun q : WitnessHeaderInput => rawModularWitnessHeader q.1 q.2.1 q.2.2.1 q.2.2.2)
    encWitnessHeaderInput encBool := by
  have hi := id' (encIn:=encWitnessHeaderInput)
  have hL := hi.fst'
  have hc := hi.snd'.fst'
  have hk := hi.snd'.snd'.fst'
  have hw := hi.snd'.snd'.snd'
  have hp := hw.fst'
  have ho := hw.snd'.fst'
  have hv := hw.snd'.snd'.fst'
  have ha := hw.snd'.snd'.snd'.fst'
  have hb := hw.snd'.snd'.snd'.snd'
  have hol := unary_to_binary.comp ((length_list encNat).comp ho)
  have hvl := unary_to_binary.comp ((length_list encNat).comp hv)
  have hbl := unary_to_binary.comp ((length_list encNat).comp hb)
  have hpb := unary_to_binary.comp (length_bits.comp (natBits.comp hp))
  have hal := unary_to_binary.comp (length_bits.comp (native_encodeRawAssignment.comp ha))
  have hplus := binary_add' hL (const 1)
  have hprimeBound := binary_add' (binary_mul' (const 128) hplus) (const 8)
  have hpointBound := binary_mul' (const 32) (binary_mul' hplus hplus)
  have h1 := binary_le' hk hL
  have h2 := decide_eq' hol hk
  have h3 := decide_eq' hvl hk
  have h4 := binary_le' (const 2) hp
  have h5 := binary_le' hpb hprimeBound
  have h6 := binary_le' hal hpointBound
  have h7 := decide_eq' hbl (binary_mul' hk hk)
  have hprefix := decide_and h1 (decide_and h2 (decide_and h3
    (decide_and h4 (decide_and h5 (decide_and h6 h7)))))
  have hdo := native_natListDistinct.comp ho
  have hdv := native_natListDistinct.comp hv
  have hs := fst encWitnessHeaderInput encNat
  have hx := snd encWitnessHeaderInput encNat
  have houtputs := unary_to_binary.comp ((length_list encNat).comp (hc.snd'.snd'.comp hs))
  have hovalid := allWithInput (test:=fun (q : WitnessHeaderInput) (o : ℕ) =>
      decide (o<q.2.1.2.2.length)) ho (binary_lt' hx houtputs)
  have hvbound := binary_lt' hx (hc.fst'.comp hs)
  have hvbits := binary_le' (unary_to_binary.comp (length_bits.comp (natBits.comp hx))) (hL.comp hs)
  have hvvalid := allWithInput
    (test:=fun (q : WitnessHeaderInput) (v : ℕ) => decide (v<q.2.1.1 ∧ v.bits.length ≤ q.1))
    hv (decide_and hvbound hvbits)
  let encE := encPair encNat (encPair encBool encNat)
  have hsave := fst encWitnessHeaderInput encE
  have he := snd encWitnessHeaderInput encE
  have haindex := binary_lt' he.fst' (hc.fst'.comp hsave)
  have hapos := binary_lt' (const 0) he.snd'.snd'
  have hacond := he.snd'.fst'.cond hapos (const true)
  have hacanonical : ComputableTidilyInPolyTime
      (fun q : WitnessHeaderInput × (ℕ × (Bool × ℕ)) =>
        decide (q.2.2.1=true → 0<q.2.2.2))
      (encPair encWitnessHeaderInput encE) encBool := by
    apply hacond.of_enc_eq
    intro q
    cases q.2.2.1 <;> simp
  have havalid := allWithInput
    (test:=fun (q : WitnessHeaderInput) (a : ℕ × (Bool × ℕ)) =>
      decide (a.1<q.2.1.1 ∧ (a.2.1=true → 0<a.2.2)))
    ha (decide_and haindex hacanonical)
  have hh := bool_and' (bool_and' (bool_and' (bool_and' (bool_and' hprefix hdo) hdv) hovalid) hvvalid) havalid
  apply hh.of_enc_eq
  intro q
  simp only [rawModularWitnessHeader,polyBound,pow_two,Function.comp_apply]

end APSCounting893.Main
end Component_20

section Component_21
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime

lemma native_rawModularWitnessCheck : ComputableTidilyInPolyTime
    (fun q : WitnessHeaderInput => rawModularWitnessCheck q.1 q.2.1 q.2.2.1 q.2.2.2)
    encWitnessHeaderInput encBool := by
  have hi := id' (encIn:=encWitnessHeaderInput)
  have hc := hi.snd'.fst'
  have hw := hi.snd'.snd'.snd'
  have hp := hw.fst'
  have ho := hw.snd'.fst'
  have hv := hw.snd'.snd'.fst'
  have ha := hw.snd'.snd'.snd'.fst'
  have hb := hw.snd'.snd'.snd'.snd'
  have hm := native_modular_jacobian_verification.1.tidy
  have htest := hm.comp ((hp.prod (hc.prod (ha.prod (ho.prod hv)))).prod hb)
  exact bool_and' native_rawModularWitnessHeader htest

def thresholdWitnessStage (q : (Word × RawCircuit) × ℕ) : Bool :=
  (decodeRawModularWitness (dropFrame q.1.1)).elim false fun wr =>
    rawModularWitnessCheck (unframe (unframe q.1.1)).length q.1.2 q.2 wr.1

lemma native_thresholdWitnessStage : ComputableTidilyInPolyTime thresholdWitnessStage
    (encPair (encPair encBits encRawCircuit) encNat) encBool := by
  let encI := encPair (encPair encBits encRawCircuit) encNat
  have hi := id' (encIn:=encI)
  have hdecode := native_decodeRawModularWitness.comp (dropFrame.comp hi.fst'.fst')
  have hs := fst encI (encPair encRawModularWitness encBits)
  have hw := snd encI (encPair encRawModularWitness encBits)
  have hL := unary_to_binary.comp (length_bits.comp (unframe.comp (unframe.comp hs.fst'.fst')))
  have hbody := native_rawModularWitnessCheck.comp
    (hL.prod (hs.fst'.snd'.prod (hs.snd'.prod hw.fst')))
  exact optionElimWithInput
    (body:=fun (q : (Word × RawCircuit) × ℕ) (wr : RawModularWitness × Word) =>
      rawModularWitnessCheck (unframe (unframe q.1.1)).length q.1.2 q.2 wr.1)
    hdecode (const false) hbody

def thresholdKStage (q : Word × RawCircuit) : Bool :=
  (decodeNat (dropFrame (unframe q.1))).elim false fun kr => thresholdWitnessStage (q,kr.1)

lemma native_thresholdKStage : ComputableTidilyInPolyTime thresholdKStage
    (encPair encBits encRawCircuit) encBool := by
  let encI := encPair encBits encRawCircuit
  have hi := id' (encIn:=encI)
  have hk := native_decodeNat.comp (dropFrame.comp (unframe.comp hi.fst'))
  have hs := fst encI (encPair encNat encBits)
  have hp := snd encI (encPair encNat encBits)
  have hbody := native_thresholdWitnessStage.comp (hs.prod hp.fst')
  exact optionElimWithInput
    (body:=fun (q : Word × RawCircuit) (kr : ℕ × Word) => thresholdWitnessStage (q,kr.1))
    hk (const false) hbody

lemma native_modularThresholdVerifier : ComputableTidilyInPolyTime modularThresholdVerifier encBits encBool := by
  have hc := native_decodeRawCircuit.comp (unframe.comp unframe)
  have hz := fst encBits (encPair encRawCircuit encBits)
  have hp := snd encBits (encPair encRawCircuit encBits)
  have hbody := native_thresholdKStage.comp (hz.prod hp.fst')
  exact optionElimWithInput
    (body:=fun (z : Word) (cr : RawCircuit × Word) => thresholdKStage (z,cr.1))
    hc (const false) hbody

end APSCounting893.Main
end Component_21

section Component_22
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma decodeNatList_code (xs : List ℕ) (rest : Word) :
    decoderList decodeNat (encodeList encodeNat xs++rest)=some (xs,rest) := by
  simpa using decoderList_mapped_code decodeNat encodeNat id xs
    (fun a _ rest => decodeNat_code a rest) (fun a _ => by simp [encodeNat]) rest

lemma decodeRawAssignment_code (xs : RawAssignment) (rest : Word) :
    decodeRawAssignment (encodeRawAssignment xs++rest)=some (xs,rest) := by
  have hparse (a : ℕ × (Bool × ℕ)) (rest : Word) :
      decoderPair decodeNat decodeSignedNat ((encodeNat a.1++encodeRawSigned a.2)++rest)=some (a,rest) := by
    apply decoderPair_success decodeNat decodeSignedNat _ (encodeRawSigned a.2++rest) rest a.1 a.2
    · simp [List.append_assoc,decodeNat_code]
    · exact decodeSignedNat_raw_code a.2 rest
  unfold decodeRawAssignment encodeRawAssignment
  simpa using decoderList_mapped_code (decoderPair decodeNat decodeSignedNat)
    (fun a : ℕ × (Bool × ℕ) => encodeNat a.1++encodeRawSigned a.2) id xs
    (fun a _ rest => hparse a rest)
    (fun a _ => by simp [encodeNat,encodeRawSigned]) rest

lemma decodeRawModularWitness_code (w : RawModularWitness) (rest : Word) :
    decodeRawModularWitness (encodeRawModularWitness w++rest)=some (w,rest) := by
  simp [decodeRawModularWitness,encodeRawModularWitness,decoderPair,decoderBind,
    List.append_assoc,decodeNat_code,decodeNatList_code,decodeRawAssignment_code]

lemma pairWord_eq_frame (x y : Word) : pairWord x y=Turing.MultiTapeTM.frame x++y := by
  rfl

lemma encodeRawAssignment_of {n : ℕ} (a : List (Fin n × ℤ)) :
    encodeRawAssignment (rawAssignmentOf a)=encodeSparseAssignment a := by
  simp [encodeRawAssignment,rawAssignmentOf,encodeSparseAssignment,encodeList,encodeRawSigned,
    encodeInt,List.flatMap_map,Function.comp_def]

end APSCounting893.Main
end Component_22

section Component_23
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace APSCounting893.Main

lemma rawModularWitnessHeader_iff (length : ℕ) (circuit : RawCircuit) (k : ℕ)
    (w : RawModularWitness) : rawModularWitnessHeader length circuit k w=true ↔
    k ≤ length ∧ w.2.1.length=k ∧ w.2.2.1.length=k ∧ 2 ≤ w.1 ∧
    w.1.bits.length ≤ 128*(length+1)+8 ∧
    (encodeRawAssignment w.2.2.2.1).length ≤ polyBound 32 2 length ∧
    w.2.2.2.2.length=k*k ∧ w.2.1.Nodup ∧ w.2.2.1.Nodup ∧
    (∀ o ∈ w.2.1,o<circuit.2.2.length) ∧
    (∀ v ∈ w.2.2.1,v<circuit.1 ∧ v.bits.length ≤ length) ∧
    (∀ a ∈ w.2.2.2.1,a.1<circuit.1 ∧ (a.2.1=true → 0<a.2.2)) := by
  simp only [rawModularWitnessHeader,Bool.and_eq_true,decide_eq_true_eq,
    List.all_eq_true,natListDistinct_iff]
  tauto

end APSCounting893.Main
end Component_23

section Component_24
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

def finiteFunctionOfList (m k : ℕ) (xs : List ℕ) (hlen : xs.length=k)
    (hbound : ∀ x ∈ xs,x < m) : Fin k → Fin m :=
  fun i => ⟨xs[i.val]'(by omega),hbound _ (List.getElem_mem _)⟩

lemma finiteFunctionOfList_values (m k : ℕ) (xs : List ℕ) (hlen : xs.length=k)
    (hbound : ∀ x ∈ xs,x < m) :
    List.ofFn (fun i => (finiteFunctionOfList m k xs hlen hbound i).val)=xs := by
  apply List.ext_getElem
  · simp [hlen]
  · intro i hi hj
    simp [finiteFunctionOfList]

lemma finiteFunctionOfList_injective (m k : ℕ) (xs : List ℕ) (hlen : xs.length=k)
    (hbound : ∀ x ∈ xs,x < m) (hdup : xs.Nodup) :
    Function.Injective (finiteFunctionOfList m k xs hlen hbound) := by
  intro i j hij
  have hv := congrArg Fin.val hij
  change xs[i.val]'(by omega)=xs[j.val]'(by omega) at hv
  apply Fin.ext
  exact (hdup.getElem_inj_iff).mp hv

def signedValue (a : Bool × ℕ) : ℤ := if a.1 then -(a.2 : ℤ) else (a.2 : ℤ)

lemma signedValue_canonical (a : Bool × ℕ) (ha : a.1=true → 0 < a.2) :
    (decide (signedValue a < 0),(signedValue a).natAbs)=a := by
  rcases a with ⟨sign,value⟩
  cases sign
  · simp [signedValue]
  · have hv : 0 < value := ha rfl
    simp [signedValue,hv]

def finiteAssignmentOfList (n : ℕ) (a : RawAssignment) (hbound : ∀ e ∈ a,e.1 < n) :
    List (Fin n × ℤ) :=
  a.attach.map (fun e => (⟨e.val.1,hbound e.val e.property⟩,signedValue e.val.2))

lemma finiteAssignmentOfList_raw (n : ℕ) (a : RawAssignment) (hbound : ∀ e ∈ a,e.1 < n)
    (hcanonical : ∀ e ∈ a,e.2.1=true → 0<e.2.2) :
    rawAssignmentOf (finiteAssignmentOfList n a hbound)=a := by
  unfold rawAssignmentOf finiteAssignmentOfList
  simp only [List.map_map,Function.comp_apply]
  trans a.attach.map Subtype.val
  · apply List.map_congr_left
    intro e _
    change (e.val.1,(decide (signedValue e.val.2<0),(signedValue e.val.2).natAbs))=e.val
    rw [signedValue_canonical e.val.2 (hcanonical e.val e.property)]
  · exact List.attach_map_subtype_val _

end APSCounting893.Main
end Component_24

section Component_25
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

abbrev NumericFraction (R : Type) := R × R

def numericFractionMap {R S : Type} [CommRing R] [CommRing S] (h : R →+* S)
    (p : NumericFraction R) : NumericFraction S := (h p.1,h p.2)

def numericFractionGate {R : Type} [CommRing R] {n : ℕ} (x : Fin n → R)
    (prior : List (NumericFraction R)) : ArithmeticGate n → Option (NumericFraction R)
  | .variable i => some (x i,1)
  | .constant cs => let q:=cs.headD 0;some ((q.num : R),(q.den : R))
  | .add a b => do
      let p←prior[a]?;let q←prior[b]?;return (p.1*q.2+q.1*p.2,p.2*q.2)
  | .sub a b => do
      let p←prior[a]?;let q←prior[b]?;return (p.1*q.2-q.1*p.2,p.2*q.2)
  | .mul a b => do
      let p←prior[a]?;let q←prior[b]?;return (p.1*q.1,p.2*q.2)
  | .div a b => do
      let p←prior[a]?;let q←prior[b]?;return (p.1*q.2,p.2*q.1)

def numericCircuitValues {R : Type} [CommRing R] {n : ℕ} (x : Fin n → R)
    (C : ArithmeticCircuit n) : Option (List (NumericFraction R)) :=
  C.gates.foldl (fun acc g=>do
    let prior←acc
    let value←numericFractionGate x prior g
    return prior++[value]) (some [])

lemma numericFractionGate_integer_map {R : Type} [CommRing R] {n : ℕ} (x : Fin n → R)
    (prior : List (IntegerPolynomialPair n)) (g : ArithmeticGate n) :
    numericFractionGate x (prior.map (numericFractionMap (MvPolynomial.eval₂Hom (Int.castRingHom R) x))) g=
      (integerGateValue prior g).map (numericFractionMap (MvPolynomial.eval₂Hom (Int.castRingHom R) x)) := by
  cases g with
  | «variable» i => simp [numericFractionGate,integerGateValue,numericFractionMap]
  | constant cs => simp [numericFractionGate,integerGateValue,numericFractionMap]
  | add a b | sub a b | mul a b | div a b =>
    cases ha : prior[a]? <;> cases hb : prior[b]? <;>
      simp [numericFractionGate,integerGateValue,ha,hb,List.getElem?_map,
        numericFractionMap,IntegerPolynomialPair.add,IntegerPolynomialPair.sub,IntegerPolynomialPair.mul,IntegerPolynomialPair.div]

lemma numericCircuitValues_integer_map {R : Type} [CommRing R] {n : ℕ} (x : Fin n → R)
    (C : ArithmeticCircuit n) :
    numericCircuitValues x C=(integerCircuitValues C).map
      (List.map (numericFractionMap (MvPolynomial.eval₂Hom (Int.castRingHom R) x))) := by
  let f:=numericFractionMap (MvPolynomial.eval₂Hom (Int.castRingHom R) x)
  have hh (gs : List (ArithmeticGate n)) (acc : Option (List (IntegerPolynomialPair n))) :
      gs.foldl (fun acc g=>do
        let prior←acc
        let value←numericFractionGate x prior g
        return prior++[value]) (acc.map (List.map f))=
      (gs.foldl (fun acc g=>do
        let prior←acc
        let value←integerGateValue prior g
        return prior++[value]) acc).map (List.map f) := by
    induction gs generalizing acc with
    | nil => rfl
    | cons g gs ih =>
      simp only [List.foldl_cons]
      have heq : (do
          let prior←acc.map (List.map f)
          let value←numericFractionGate x prior g
          pure (prior++[value]))=
          (do
            let prior←acc
            let value←integerGateValue prior g
            pure (prior++[value])).map (List.map f) := by
        cases acc with
        | none => rfl
        | some prior =>
          change (numericFractionGate x (prior.map f) g).bind (fun value=>some (prior.map f++[value]))=
            ((integerGateValue prior g).bind (fun value=>some (prior++[value]))).map (List.map f)
          dsimp only [f]
          rw [numericFractionGate_integer_map]
          cases integerGateValue prior g <;> simp [List.map_append,f]
      rw [heq,ih]
  exact hh C.gates (some [])

end APSCounting893.Main
end Component_25

section Component_26
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

noncomputable def polynomialJetEvaluation {R : Type} [CommRing R] {n : ℕ}
    (x : Fin n → R) (j : Fin n) : MvPolynomial (Fin n) ℤ →+* DualNumber R where
  toFun p := ((MvPolynomial.eval₂ (Int.castRingHom R) x p,
    MvPolynomial.eval₂ (Int.castRingHom R) x (MvPolynomial.pderiv j p)) : DualNumber R)
  map_zero' := by ext <;> simp
  map_one' := by ext <;> simp
  map_add' p q := by
    apply TrivSqZeroExt.ext
    · change MvPolynomial.eval₂ (Int.castRingHom R) x (p+q)=_
      simp only [TrivSqZeroExt.fst_add,TrivSqZeroExt.fst_mul,TrivSqZeroExt.fst_mk,MvPolynomial.eval₂_add,MvPolynomial.eval₂_mul]
    · change MvPolynomial.eval₂ (Int.castRingHom R) x (MvPolynomial.pderiv j (p+q))=_
      simp only [TrivSqZeroExt.snd_add,TrivSqZeroExt.snd_mk,map_add,MvPolynomial.eval₂_add]
  map_mul' p q := by
    apply TrivSqZeroExt.ext
    · change MvPolynomial.eval₂ (Int.castRingHom R) x (p*q)=_
      simp only [TrivSqZeroExt.fst_add,TrivSqZeroExt.fst_mul,TrivSqZeroExt.fst_mk,MvPolynomial.eval₂_add,MvPolynomial.eval₂_mul]
    · change MvPolynomial.eval₂ (Int.castRingHom R) x (MvPolynomial.pderiv j (p*q))=_
      simp [MvPolynomial.pderiv_mul,DualNumber.snd_mul]
      <;> ring

@[simp] lemma polynomialJetEvaluation_fst {R : Type} [CommRing R] {n : ℕ}
    (x : Fin n → R) (j : Fin n) (p : MvPolynomial (Fin n) ℤ) :
    (polynomialJetEvaluation x j p).fst=MvPolynomial.eval₂ (Int.castRingHom R) x p := rfl

@[simp] lemma polynomialJetEvaluation_snd {R : Type} [CommRing R] {n : ℕ}
    (x : Fin n → R) (j : Fin n) (p : MvPolynomial (Fin n) ℤ) :
    (polynomialJetEvaluation x j p).snd=MvPolynomial.eval₂ (Int.castRingHom R) x (MvPolynomial.pderiv j p) := rfl

@[simp] lemma polynomialJetEvaluation_C {R : Type} [CommRing R] {n : ℕ}
    (x : Fin n → R) (j : Fin n) (z : ℤ) :
    polynomialJetEvaluation x j (MvPolynomial.C z)=((z:R),0) := by
  ext <;> simp

@[simp] lemma polynomialJetEvaluation_X {R : Type} [CommRing R] {n : ℕ}
    (x : Fin n → R) (j i : Fin n) :
    polynomialJetEvaluation x j (MvPolynomial.X i)=(x i,if i=j then 1 else 0) := by
  ext <;> simp
  by_cases hi : i=j
  · subst i;simp
  · simp [Pi.single_apply,Ne.symm hi,hi]

end APSCounting893.Main
end Component_26

section Component_27
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

def numericCircuitOutput {R : Type} [CommRing R] {n : ℕ} (x : Fin n → R)
    (C : ArithmeticCircuit n) (j : Fin C.outputs.length) : NumericFraction R :=
  (((numericCircuitValues x C).getD [])[C.outputs[j]]?).getD (0,1)

lemma numericCircuitOutput_integer_map {R : Type} [CommRing R] {n : ℕ} (x : Fin n → R)
    (C : ArithmeticCircuit n) (j : Fin C.outputs.length) :
    numericCircuitOutput x C j=numericFractionMap (MvPolynomial.eval₂Hom (Int.castRingHom R) x) (integerCircuitOutput C j) := by
  unfold numericCircuitOutput integerCircuitOutput
  rw [numericCircuitValues_integer_map]
  cases hvals : integerCircuitValues C with
  | none => simp [numericFractionMap]
  | some vals =>
    simp only [Option.map_some,Option.getD_some,List.getElem?_map]
    cases vals[C.outputs[j]]? <;> simp [numericFractionMap]

lemma polynomialJetEvaluation_eq_eval₂Hom {R : Type} [CommRing R] {n : ℕ}
    (x : Fin n → R) (j : Fin n) :
    polynomialJetEvaluation x j=MvPolynomial.eval₂Hom (Int.castRingHom (DualNumber R))
      (fun i=>(x i,if i=j then 1 else 0)) := by
  apply MvPolynomial.ringHom_ext
  · intro z
    simp [MvPolynomial.eval₂Hom_C]
  · intro i
    simp only [polynomialJetEvaluation_X,MvPolynomial.eval₂Hom_X']

lemma numericCircuitOutput_jet {R : Type} [CommRing R] {n : ℕ}
    (x : Fin n → R) (v : Fin n) (C : ArithmeticCircuit n) (j : Fin C.outputs.length) :
    numericCircuitOutput (R:=DualNumber R) (fun i=>(x i,if i=v then 1 else 0) : Fin n → DualNumber R) C j=
      numericFractionMap (polynomialJetEvaluation x v) (integerCircuitOutput C j) := by
  rw [numericCircuitOutput_integer_map (R:=DualNumber R),polynomialJetEvaluation_eq_eval₂Hom]

end APSCounting893.Main
end Component_27

section Component_28
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

def numericDerivativePair {R : Type} [CommRing R] (p : NumericFraction (DualNumber R)) : NumericFraction R :=
  (p.1.snd*p.2.fst-p.1.fst*p.2.snd,p.2.fst^2)

def numericJacobianPairs {R : Type} [CommRing R] {n k : ℕ} (x : Fin n → R) (C : ArithmeticCircuit n)
    (o : Fin k → Fin C.outputs.length) (v : Fin k → Fin n) : Matrix (Fin k) (Fin k) (NumericFraction R) :=
  fun i j=>numericDerivativePair (numericCircuitOutput (R:=DualNumber R)
    (fun l=>(x l,if l=v j then 1 else 0) : Fin n → DualNumber R) C (o i))

def numericClearedMatrix {R : Type} [CommRing R] {k : ℕ} (M : Matrix (Fin k) (Fin k) (NumericFraction R)) :
    Matrix (Fin k) (Fin k) R := fun i j=>(M i j).1*∏ l ∈ Finset.univ.erase j,(M i l).2

lemma numericJacobianPairs_integer_map {R : Type} [CommRing R] {n k : ℕ} (x : Fin n → R)
    (C : ArithmeticCircuit n) (o : Fin k → Fin C.outputs.length) (v : Fin k → Fin n) (i j : Fin k) :
    numericJacobianPairs x C o v i j=
      numericFractionMap (MvPolynomial.eval₂Hom (Int.castRingHom R) x) (circuitJacobianIntegerPairs C o v i j) := by
  unfold numericJacobianPairs
  rw [numericCircuitOutput_jet]
  apply Prod.ext <;> simp [numericDerivativePair,numericFractionMap,circuitJacobianIntegerPairs,
    IntegerPolynomialPair.derivative]

lemma numericClearedMatrix_integer_map {R : Type} [CommRing R] {n k : ℕ} (x : Fin n → R)
    (C : ArithmeticCircuit n) (o : Fin k → Fin C.outputs.length) (v : Fin k → Fin n) :
    numericClearedMatrix (numericJacobianPairs x C o v)=
      (clearedIntegerMatrix (circuitJacobianIntegerPairs C o v)).map (MvPolynomial.eval₂Hom (Int.castRingHom R) x) := by
  funext i j
  simp only [numericClearedMatrix,numericJacobianPairs_integer_map,numericFractionMap,
    Matrix.map_apply,clearedIntegerMatrix,map_mul,map_prod]

lemma numericJacobianDeterminant_integer_map {R : Type} [CommRing R] {n k : ℕ} (x : Fin n → R)
    (C : ArithmeticCircuit n) (o : Fin k → Fin C.outputs.length) (v : Fin k → Fin n) :
    (numericClearedMatrix (numericJacobianPairs x C o v)).det=
      MvPolynomial.eval₂ (Int.castRingHom R) x (circuitJacobianIntegerMinor C o v) := by
  rw [numericClearedMatrix_integer_map]
  exact (RingHom.map_det (MvPolynomial.eval₂Hom (Int.castRingHom R) x) _).symm

lemma matrix_right_inverse_det_ne_zero {R : Type} [CommRing R] [Nontrivial R] {k : ℕ}
    (M B : Matrix (Fin k) (Fin k) R) (h : M*B=1) : M.det≠0 := by
  have hh:=congrArg Matrix.det h
  rw [Matrix.det_mul,Matrix.det_one] at hh
  intro hz
  rw [hz,zero_mul] at hh
  exact zero_ne_one hh

lemma matrix_right_inverse_iff_det_ne_zero {R : Type} [Field R] {k : ℕ}
    (M : Matrix (Fin k) (Fin k) R) : (∃ B,M*B=1) ↔ M.det≠0 := by
  constructor
  · rintro ⟨B,hB⟩;exact matrix_right_inverse_det_ne_zero M B hB
  · intro h;exact ⟨M⁻¹,Matrix.mul_nonsing_inv M (isUnit_iff_ne_zero.mpr h)⟩

end APSCounting893.Main
end Component_28

section Component_29
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma polynomial_integer_eval_cast {R : Type} [CommRing R] {n : ℕ} (a : Fin n → ℤ)
    (p : MvPolynomial (Fin n) ℤ) :
    MvPolynomial.eval₂ (Int.castRingHom R) (fun i=>(a i:R)) p=(MvPolynomial.eval a p:R) := by
  simpa [Function.comp_def,MvPolynomial.eval₂_id] using
    (MvPolynomial.eval₂_comp_left (Int.castRingHom R) (RingHom.id ℤ) a p).symm

lemma numericJacobian_right_inverse_sound {n k p : ℕ} (hp : 2≤p) (C : ArithmeticCircuit n)
    (o : Fin k → Fin C.outputs.length) (v : Fin k → Fin n) (a : List (Fin n × ℤ))
    (B : Matrix (Fin k) (Fin k) (ZMod p))
    (hB : numericClearedMatrix (numericJacobianPairs (fun i=>(sparseAssignmentPoint a i:ZMod p)) C o v)*B=1) :
    circuitJacobianIntegerMinor C o v≠0 := by
  letI : Fact (1<p):=⟨by omega⟩
  have hdet:=matrix_right_inverse_det_ne_zero _ B hB
  rw [numericJacobianDeterminant_integer_map,polynomial_integer_eval_cast] at hdet
  intro hz
  apply hdet
  simp [hz]

lemma numericJacobian_right_inverse_complete {n k p : ℕ} (hp : p.Prime) (C : ArithmeticCircuit n)
    (o : Fin k → Fin C.outputs.length) (v : Fin k → Fin n) (a : List (Fin n × ℤ))
    (hne : (MvPolynomial.eval (sparseAssignmentPoint a) (circuitJacobianIntegerMinor C o v):ZMod p)≠0) :
    ∃ B : Matrix (Fin k) (Fin k) (ZMod p),
      numericClearedMatrix (numericJacobianPairs (fun i=>(sparseAssignmentPoint a i:ZMod p)) C o v)*B=1 := by
  letI : Fact p.Prime:=⟨hp⟩
  apply (matrix_right_inverse_iff_det_ne_zero _).mpr
  rwa [numericJacobianDeterminant_integer_map,polynomial_integer_eval_cast]

lemma numericJacobian_prime_divisor_certificate {n k p : ℕ} (hp : 2≤p) (C : ArithmeticCircuit n)
    (o : Fin k → Fin C.outputs.length) (v : Fin k → Fin n) (a : List (Fin n × ℤ))
    (B : Matrix (Fin k) (Fin k) (ZMod p))
    (hB : numericClearedMatrix (numericJacobianPairs (fun i=>(sparseAssignmentPoint a i:ZMod p)) C o v)*B=1) :
    ∃ q : ℕ,q.Prime ∧ q≤p ∧
      (MvPolynomial.eval (sparseAssignmentPoint a) (circuitJacobianIntegerMinor C o v):ZMod q)≠0 := by
  obtain ⟨q,hq,hqp⟩:=Nat.exists_prime_and_dvd (show p≠1 by omega)
  letI : Fact q.Prime:=⟨hq⟩
  have hh:=congrArg Matrix.det hB
  rw [Matrix.det_mul,Matrix.det_one,numericJacobianDeterminant_integer_map,polynomial_integer_eval_cast] at hh
  have hmap:=congrArg (ZMod.castHom hqp (ZMod q)) hh
  simp only [map_mul,map_intCast,map_one] at hmap
  refine ⟨q,hq,Nat.le_of_dvd (by omega) hqp,?_⟩
  intro hz
  rw [hz,zero_mul] at hmap
  exact zero_ne_one hmap

end APSCounting893.Main
end Component_29

section Component_30
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

def matrixEntryList {R : Type} {k : ℕ} (B : Matrix (Fin k) (Fin k) R) : List R :=
  (List.finRange k).flatMap (fun i=>(List.finRange k).map (B i))

def encodeModularMatrix {p k : ℕ} (B : Matrix (Fin k) (Fin k) (ZMod p)) : Word :=
  encodeList encodeNat (matrixEntryList B |>.map ZMod.val)

lemma matrixEntryList_length {R : Type} {k : ℕ} (B : Matrix (Fin k) (Fin k) R) :
    (matrixEntryList B).length=k*k := by
  simp [matrixEntryList,List.length_flatMap]

lemma flatMap_word_length_le {α : Type} (xs : List α) (f : α → Word) (M : ℕ)
    (h : ∀ x ∈ xs,(f x).length≤M) : (xs.flatMap f).length≤xs.length*M := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx:=h x (by simp)
    have ht:=ih (fun y hy=>h y (by simp [hy]))
    simp only [List.flatMap_cons,List.length_append,List.length_cons]
    nlinarith

lemma encodeModularMatrix_length {p k : ℕ} (hp : 2≤p) (B : Matrix (Fin k) (Fin k) (ZMod p)) :
    (encodeModularMatrix B).length ≤ 2*(k*k).bits.length+1+k*k*(2*p.bits.length+1) := by
  letI : NeZero p:=⟨by omega⟩
  have hbit (z : ZMod p) : z.val.bits.length≤p.bits.length := by
    simpa only [Nat.size_eq_bits_len] using Nat.size_le_size (ZMod.val_lt z).le
  have hh:=flatMap_word_length_le ((matrixEntryList B).map ZMod.val) encodeNat (2*p.bits.length+1)
    (by
      intro a ha
      obtain ⟨z,hz,rfl⟩:=List.mem_map.mp ha
      have hzbits:=hbit z
      simp only [encodeNat,List.length_append,List.length_replicate,List.length_cons,List.length_nil]
      omega)
  unfold encodeModularMatrix encodeList
  simp only [List.length_append,List.length_map,matrixEntryList_length]
  calc
    (encodeNat (k*k)).length+(((matrixEntryList B).map ZMod.val).flatMap encodeNat).length ≤
        (encodeNat (k*k)).length+k*k*(2*p.bits.length+1) := by
      have hlen : ((matrixEntryList B).map ZMod.val).length=k*k := by simp [matrixEntryList_length]
      rw [hlen] at hh
      omega
    _ = _ := by simp [encodeNat];omega

end APSCounting893.Main
end Component_30

section Component_31
set_option autoImplicit false
set_option maxHeartbeats 500000
namespace APSCounting893.Main

lemma encodeNat_length_pos (n : ℕ) : 0<(encodeNat n).length := by
  simp [encodeNat]

lemma arithmeticGate_encode_length_pos {n : ℕ} (g : ArithmeticGate n) : 0<g.encode.length := by
  cases g <;> simp [ArithmeticGate.encode,encodeNat]

lemma gates_length_le_flatMap_encode {n : ℕ} (gs : List (ArithmeticGate n)) :
    gs.length≤(gs.flatMap ArithmeticGate.encode).length := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    have hg:=arithmeticGate_encode_length_pos g
    simp only [List.length_cons,List.flatMap_cons,List.length_append]
    omega

lemma circuit_gates_length_le_encode {n : ℕ} (C : ArithmeticCircuit n) : C.gates.length≤C.encode.length := by
  have hh:=gates_length_le_flatMap_encode C.gates
  simp only [ArithmeticCircuit.encode,encodeList,List.length_append]
  omega

lemma output_count_le_encode {n : ℕ} (C : ArithmeticCircuit n) : C.outputs.length≤C.encode.length := by
  have hh : C.outputs.length≤(C.outputs.flatMap encodeNat).length := by
    induction C.outputs with
    | nil => rfl
    | cons o os ih =>
      have ho:=encodeNat_length_pos o
      simp only [List.length_cons,List.flatMap_cons,List.length_append]
      omega
  simp only [ArithmeticCircuit.encode,encodeList,List.length_append]
  omega

lemma ReducedCircuit.dimension_le_encode (I : ReducedCircuit) : I.n+1≤I.C.encode.length := by
  rw [←I.outputCount]
  exact output_count_le_encode I.C

end APSCounting893.Main
end Component_31

section Component_32
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

noncomputable def ModularInverseCertificate {n : ℕ} (C : ArithmeticCircuit n) (k : ℕ) : Prop :=
  ∃ (o : Fin k → Fin C.outputs.length) (v : Fin k → Fin n),
    Function.Injective o ∧ Function.Injective v ∧
    (∀ j,(v j).val.bits.length≤C.encode.length) ∧
    ∃ p : ℕ,2≤p ∧ p.bits.length≤128*(C.encode.length+1)+8 ∧
      ∃ a : List (Fin n × ℤ),(encodeSparseAssignment a).length≤polyBound 32 2 C.encode.length ∧
        ∃ B : Matrix (Fin k) (Fin k) (ZMod p),
          numericClearedMatrix (numericJacobianPairs (fun i=>(sparseAssignmentPoint a i:ZMod p)) C o v)*B=1

lemma modularInverseCertificate_iff {n : ℕ} (C : ArithmeticCircuit n)
    (k : ℕ) : ModularInverseCertificate C k ↔ ModularJacobianCertificate C k := by
  constructor
  · rintro ⟨o,v,ho,hv,hvbits,p,hp,hpbits,a,habits,B,hB⟩
    obtain ⟨q,hq,hqp,hqne⟩:=numericJacobian_prime_divisor_certificate hp C o v a B hB
    refine ⟨o,v,ho,hv,hvbits,q,hq,?_,a,habits,hqne⟩
    have hqb : q.bits.length≤p.bits.length := by simpa only [Nat.size_eq_bits_len] using Nat.size_le_size hqp
    exact hqb.trans hpbits
  · rintro ⟨o,v,ho,hv,hvbits,p,hp,hpbits,a,habits,hne⟩
    exact ⟨o,v,ho,hv,hvbits,p,hp.two_le,hpbits,a,habits,numericJacobian_right_inverse_complete hp C o v a hne⟩

end APSCounting893.Main
end Component_32

section Component_33
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma rawModularWitnessCheck_sound {n : ℕ} (C : ArithmeticCircuit n) (k : ℕ)
    (w : RawModularWitness) (hcheck : rawModularWitnessCheck C.encode.length C.raw k w=true) :
    ModularJacobianCertificate C k := by
  have hh : rawModularWitnessHeader C.encode.length C.raw k w=true ∧
      residueMatrixInverseTest (w.1,(C.raw,(w.2.2.2.1,(w.2.1,w.2.2.1)))) w.2.2.2.2=true := by
    simpa only [rawModularWitnessCheck,Bool.and_eq_true] using hcheck
  rcases (rawModularWitnessHeader_iff C.encode.length C.raw k w).mp hh.1 with
    ⟨hkL,holen,hvlen,hp,hpbits,habits,hblen,hodup,hvdup,ho,hv,ha⟩
  have hobound : ∀ x ∈ w.2.1,x < C.outputs.length := ho
  have hvbound : ∀ x ∈ w.2.2.1,x < n := fun x hx => (hv x hx).1
  let o := finiteFunctionOfList C.outputs.length k w.2.1 holen hobound
  let v := finiteFunctionOfList n k w.2.2.1 hvlen hvbound
  have hovals : List.ofFn (fun i => (o i).val)=w.2.1 :=
    finiteFunctionOfList_values _ _ _ holen hobound
  have hvvals : List.ofFn (fun j => (v j).val)=w.2.2.1 :=
    finiteFunctionOfList_values _ _ _ hvlen hvbound
  have habound : ∀ e ∈ w.2.2.2.1,e.1 < n := fun e he => (ha e he).1
  let a := finiteAssignmentOfList n w.2.2.2.1 habound
  have havals : rawAssignmentOf a=w.2.2.2.1 :=
    finiteAssignmentOfList_raw n _ habound (fun e he => (ha e he).2)
  have hmat : residueMatrixInverseTest
      (w.1,(C.raw,(rawAssignmentOf a,(List.ofFn (fun i => (o i).val),List.ofFn (fun j => (v j).val)))))
      w.2.2.2.2=true := by
    simpa only [havals,hovals,hvvals] using hh.2
  have hB := (native_modular_jacobian_verification.2 n k w.1 hp C a o v w.2.2.2.2).mp hmat
  rw [←numericClearedMatrix_integer_map] at hB
  apply (modularInverseCertificate_iff C k).mp
  refine ⟨o,v,finiteFunctionOfList_injective _ _ _ holen hobound hodup,
    finiteFunctionOfList_injective _ _ _ hvlen hvbound hvdup,?_,w.1,hp,hpbits,a,?_,_,hB⟩
  · intro j
    have hmem : (v j).val ∈ w.2.2.1 := by rw [←hvvals];simp
    exact (hv _ hmem).2
  · rw [←encodeRawAssignment_of,havals]
    exact habits

end APSCounting893.Main
end Component_33

section Component_34
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main
open Turing.MultiTapeTM

lemma modularThresholdVerifier_on_input {n : ℕ} (C : ArithmeticCircuit n)
    (hvalid : ValidCircuit .rational C) (k : ℕ) (w : Word) :
    modularThresholdVerifier (pairWord (pairWord C.encode (encodeNat k)) w)=
      (decodeRawModularWitness w).elim false
        (fun wr => rawModularWitnessCheck C.encode.length C.raw k wr.1) := by
  simp only [modularThresholdVerifier,pairWord_eq_frame,unframe_frame_append,dropFrame_frame_append]
  have hc := decodeRawCircuit_code C hvalid []
  have hk := decodeNat_code k []
  simp only [List.append_nil] at hc hk
  rw [hc,hk]
  rfl

lemma modularThresholdVerifier_sound {n : ℕ} (C : ArithmeticCircuit n)
    (hvalid : ValidCircuit .rational C) (k : ℕ) (w : Word)
    (h : modularThresholdVerifier (pairWord (pairWord C.encode (encodeNat k)) w)=true) :
    ModularJacobianCertificate C k := by
  rw [modularThresholdVerifier_on_input C hvalid k w] at h
  cases hd : decodeRawModularWitness w with
  | none => simp [hd] at h
  | some wr =>
    simp only [hd,Option.elim_some] at h
    exact rawModularWitnessCheck_sound C k wr.1 h

end APSCounting893.Main
end Component_34

section Component_35
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

def inverseResidueList {p k : ℕ} (B : Matrix (Fin k) (Fin k) (ZMod p)) : List ℕ :=
  List.ofFn (fun t : Fin (k*k) =>
    (B (finProdFinEquiv.symm t).1 (finProdFinEquiv.symm t).2).val)

lemma inverseResidueList_length {p k : ℕ} (B : Matrix (Fin k) (Fin k) (ZMod p)) :
    (inverseResidueList B).length=k*k := by simp [inverseResidueList]

lemma inverseResidueList_getD {p k : ℕ} (B : Matrix (Fin k) (Fin k) (ZMod p)) (i j : Fin k) :
    (inverseResidueList B).getD (i.val*k+j.val) 0=(B i j).val := by
  have hlt : i.val*k+j.val < k*k := by nlinarith [i.isLt,j.isLt]
  have heq : (⟨i.val*k+j.val,hlt⟩ : Fin (k*k))=finProdFinEquiv (i,j) := by
    apply Fin.ext
    simp [finProdFinEquiv,Nat.mul_comm,Nat.add_comm]
  simp only [inverseResidueList,List.getD_eq_getElem?_getD,List.getElem?_ofFn,dif_pos hlt,Option.getD_some]
  rw [heq]
  simp

end APSCounting893.Main
end Component_35

section Component_36
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma encodeNatList_length_bound (xs : List ℕ) (b : ℕ)
    (hbits : ∀ x ∈ xs,x.bits.length ≤ b) :
    (encodeList encodeNat xs).length ≤ 2*xs.length.bits.length+1+xs.length*(2*b+1) := by
  have hf := flatMap_word_length_le xs encodeNat (2*b+1) (fun x hx => by
    have hb:=hbits x hx
    simp only [encodeNat,List.length_append,List.length_replicate,List.length_cons,List.length_nil]
    omega)
  simp only [encodeList,List.length_append,encodeNat,List.length_replicate,List.length_cons,List.length_nil]
  omega

lemma inverseResidueList_bits {p k : ℕ} (hp : 2 ≤ p) (B : Matrix (Fin k) (Fin k) (ZMod p)) :
    ∀ x ∈ inverseResidueList B,x.bits.length ≤ p.bits.length := by
  letI : NeZero p := ⟨by omega⟩
  intro x hx
  obtain ⟨t,rfl⟩ := List.mem_ofFn.mp hx
  simpa only [Nat.size_eq_bits_len] using Nat.size_le_size
    (ZMod.val_lt (B (finProdFinEquiv.symm t).1 (finProdFinEquiv.symm t).2)).le

lemma bits_length_le_self (r : ℕ) : r.bits.length ≤ r := by
  simpa only [Nat.size_eq_bits_len] using (Nat.size_le.mpr (Nat.lt_two_pow_self (n:=r)))

lemma inverseResidueList_encoded_bound {p k : ℕ} (hp : 2 ≤ p)
    (B : Matrix (Fin k) (Fin k) (ZMod p)) :
    (encodeList encodeNat (inverseResidueList B)).length ≤
      2*(k*k).bits.length+1+k*k*(2*p.bits.length+1) := by
  simpa only [inverseResidueList_length] using
    encodeNatList_length_bound (inverseResidueList B) p.bits.length (inverseResidueList_bits hp B)

end APSCounting893.Main
end Component_36

section Component_37
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

def modularWitnessOf {n k m : ℕ} (p : ℕ) (a : List (Fin n × ℤ))
    (o : Fin k → Fin m) (v : Fin k → Fin n) (B : Matrix (Fin k) (Fin k) (ZMod p)) : RawModularWitness :=
  (p,(List.ofFn (fun i => (o i).val),(List.ofFn (fun j => (v j).val),
    (rawAssignmentOf a,inverseResidueList B))))

lemma rawModularWitnessCheck_complete {n k : ℕ} (C : ArithmeticCircuit n)
    (p : ℕ) (hp : 2 ≤ p) (hpbits : p.bits.length ≤ 128*(C.encode.length+1)+8)
    (a : List (Fin n × ℤ)) (habits : (encodeSparseAssignment a).length ≤ polyBound 32 2 C.encode.length)
    (o : Fin k → Fin C.outputs.length) (v : Fin k → Fin n)
    (ho : Function.Injective o) (hv : Function.Injective v)
    (hvbits : ∀ j,(v j).val.bits.length ≤ C.encode.length)
    (B : Matrix (Fin k) (Fin k) (ZMod p))
    (hB : numericClearedMatrix (numericJacobianPairs (fun l => (sparseAssignmentPoint a l : ZMod p)) C o v)*B=1) :
    rawModularWitnessCheck C.encode.length C.raw k (modularWitnessOf p a o v B)=true := by
  have hk : k ≤ C.encode.length := by
    have hcard := Fintype.card_le_of_injective o ho
    simp only [Fintype.card_fin] at hcard
    exact hcard.trans (output_count_le_encode C)
  have hoval : Function.Injective (fun i => (o i).val) := fun i j hij => ho (Fin.ext hij)
  have hvval : Function.Injective (fun j => (v j).val) := fun i j hij => hv (Fin.ext hij)
  have hheader : rawModularWitnessHeader C.encode.length C.raw k (modularWitnessOf p a o v B)=true := by
    apply (rawModularWitnessHeader_iff _ _ _ _).mpr
    refine ⟨hk,by simp [modularWitnessOf],by simp [modularWitnessOf],hp,hpbits,?_,
      inverseResidueList_length B,?_,?_,?_,?_,?_⟩
    · simpa [modularWitnessOf,encodeRawAssignment_of] using habits
    · exact List.nodup_ofFn.mpr hoval
    · exact List.nodup_ofFn.mpr hvval
    · intro out hout
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hout
      exact (o i).isLt
    · intro var hvar
      obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hvar
      exact ⟨(v j).isLt,hvbits j⟩
    · intro e he
      obtain ⟨entry,hentry,rfl⟩ := List.mem_map.mp he
      refine ⟨entry.1.isLt,?_⟩
      intro hneg
      have hn : entry.2<0 := of_decide_eq_true hneg
      exact Int.natAbs_pos.mpr (by omega)
  let Blist : Matrix (Fin k) (Fin k) (ZMod p) :=
    Matrix.of (fun i j => ((inverseResidueList B).getD (i.val*k+j.val) 0 : ZMod p))
  have hlist : Blist=B := by
    letI : NeZero p := ⟨by omega⟩
    apply Matrix.ext
    intro i j
    change (((inverseResidueList B).getD (i.val*k+j.val) 0 : ℕ) : ZMod p)=B i j
    rw [inverseResidueList_getD]
    exact ZMod.natCast_zmod_val _
  have hnumeric : numericClearedMatrix (numericJacobianPairs (fun l => (sparseAssignmentPoint a l : ZMod p)) C o v)*
      Blist=1 := by rw [hlist];exact hB
  have hcheck := (native_modular_jacobian_verification.2 n k p hp C a o v (inverseResidueList B)).mpr
    (by rw [←numericClearedMatrix_integer_map];exact hnumeric)
  unfold rawModularWitnessCheck
  apply Bool.and_eq_true_iff.mpr
  refine ⟨hheader,?_⟩
  simpa only [modularWitnessOf] using hcheck

end APSCounting893.Main
end Component_37

section Component_38
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma natList_encoded_quadratic (L k : ℕ) (xs : List ℕ) (hlen : xs.length=k)
    (hk : k ≤ L) (hb : ∀ x ∈ xs,x.bits.length ≤ L) :
    (encodeList encodeNat xs).length ≤ 6*(L+1)^2 := by
  have h := encodeNatList_length_bound xs L hb
  have hbits := bits_length_le_self k
  rw [hlen] at h
  have hmul := Nat.mul_le_mul_right (2*L+1) hk
  nlinarith

lemma modularWitnessOf_length {n k : ℕ} (C : ArithmeticCircuit n) (p : ℕ)
    (hp : 2 ≤ p) (hpbits : p.bits.length ≤ 128*(C.encode.length+1)+8)
    (a : List (Fin n × ℤ)) (habits : (encodeSparseAssignment a).length ≤ polyBound 32 2 C.encode.length)
    (o : Fin k → Fin C.outputs.length) (v : Fin k → Fin n)
    (ho : Function.Injective o) (hvbits : ∀ j,(v j).val.bits.length ≤ C.encode.length)
    (B : Matrix (Fin k) (Fin k) (ZMod p)) :
    (encodeRawModularWitness (modularWitnessOf p a o v B)).length ≤ polyBound 2048 4 C.encode.length := by
  let L := C.encode.length
  let T := L+1
  have hT : 1 ≤ T := by omega
  have hk : k ≤ L := by
    have hcard := Fintype.card_le_of_injective o ho
    simp only [Fintype.card_fin] at hcard
    exact hcard.trans (output_count_le_encode C)
  have hO := natList_encoded_quadratic L k (List.ofFn (fun i => (o i).val))
    (by simp) hk (by
      intro x hx
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
      exact (bits_length_le_self (o i).val).trans ((o i).isLt.le.trans (output_count_le_encode C)))
  have hV := natList_encoded_quadratic L k (List.ofFn (fun j => (v j).val))
    (by simp) hk (by intro x hx;obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hx;exact hvbits j)
  have hA : (encodeRawAssignment (rawAssignmentOf a)).length ≤ 32*T^2 := by
    simpa only [encodeRawAssignment_of,polyBound] using habits
  have hpb : p.bits.length ≤ 136*T := by dsimp [T,L];omega
  have hP : (encodeNat p).length ≤ 274*T := by
    simp only [encodeNat,List.length_append,List.length_replicate,List.length_cons,List.length_nil]
    omega
  have hB := inverseResidueList_encoded_bound hp B
  have hkk : k*k ≤ T^2 := by dsimp [T];nlinarith
  have hkkbits := bits_length_le_self (k*k)
  have hmul := Nat.mul_le_mul hkk (show 2*p.bits.length+1 ≤ 272*T+1 by omega)
  have hB' : (encodeList encodeNat (inverseResidueList B)).length ≤ 3*T^2+1+272*T^3 := by
    nlinarith
  have h1 : T ≤ T^4 := by simpa only [pow_one] using Nat.pow_le_pow_right hT (show 1 ≤ 4 by decide)
  have h2 : T^2 ≤ T^4 := Nat.pow_le_pow_right hT (by decide)
  have h3 : T^3 ≤ T^4 := Nat.pow_le_pow_right hT (by decide)
  change (encodeNat p++encodeList encodeNat (List.ofFn (fun i => (o i).val))++
    encodeList encodeNat (List.ofFn (fun j => (v j).val))++encodeRawAssignment (rawAssignmentOf a)++
    encodeList encodeNat (inverseResidueList B)).length ≤ 2048*T^4
  simp only [List.length_append]
  change (encodeNat p).length+_+_+_+_ ≤ _
  change (encodeList encodeNat (List.ofFn (fun i => (o i).val))).length ≤ 6*T^2 at hO
  change (encodeList encodeNat (List.ofFn (fun j => (v j).val))).length ≤ 6*T^2 at hV
  nlinarith

end APSCounting893.Main
end Component_38

section Component_39
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma modularThresholdVerifier_complete {n : ℕ} (C : ArithmeticCircuit n)
    (hvalid : ValidCircuit .rational C) (k N : ℕ)
    (hN : polyBound 2048 4 C.encode.length ≤ N) (hcert : ModularJacobianCertificate C k) :
    ∃ w : Word,w.length=N ∧
      modularThresholdVerifier (pairWord (pairWord C.encode (encodeNat k)) w)=true := by
  rcases (modularInverseCertificate_iff C k).mpr hcert with
    ⟨o,v,ho,hv,hvbits,p,hp,hpbits,a,habits,B,hB⟩
  let witness := modularWitnessOf p a o v B
  let witnessWord := encodeRawModularWitness witness
  have hcheck := rawModularWitnessCheck_complete C p hp hpbits a habits o v ho hv hvbits B hB
  have hsize : witnessWord.length ≤ N :=
    (modularWitnessOf_length C p hp hpbits a habits o v ho hvbits B).trans hN
  let padding : Word := List.replicate (N-witnessWord.length) false
  refine ⟨witnessWord++padding,?_,?_⟩
  · simp only [List.length_append,padding,List.length_replicate]
    omega
  · rw [modularThresholdVerifier_on_input C hvalid k]
    change (decodeRawModularWitness (encodeRawModularWitness witness++padding)).elim false _=true
    rw [decodeRawModularWitness_code]
    exact hcheck

lemma pairWord_left_length_le (x y : Word) : x.length ≤ (pairWord x y).length := by
  simp [pairWord_eq_frame]
  omega

lemma threshold_certificate_equivalence {n : ℕ} (C : ArithmeticCircuit n)
    (hvalid : ValidCircuit .rational C) (k : ℕ) :
    (∃ w : Word,w.length=polyBound 2048 4 (pairWord C.encode (encodeNat k)).length ∧
      modularThresholdVerifier (pairWord (pairWord C.encode (encodeNat k)) w)=true) ↔
      ModularJacobianCertificate C k := by
  constructor
  · rintro ⟨w,_,hw⟩
    exact modularThresholdVerifier_sound C hvalid k w hw
  · intro hc
    apply modularThresholdVerifier_complete C hvalid k _ ?_ hc
    unfold polyBound
    exact Nat.mul_le_mul_left 2048 (Nat.pow_le_pow_left
      (Nat.add_le_add_right (pairWord_left_length_le C.encode (encodeNat k)) 1) 4)

end APSCounting893.Main
end Component_39

section Component_40
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma modular_threshold_language_in_ch_proof :
    ∃ A : Language,InCountingHierarchy A ∧
      ∀ (n : ℕ) (C : ArithmeticCircuit n),ValidCircuit .rational C →
        ∀ k : ℕ,A (pairWord C.encode (encodeNat k)) ↔ ModularJacobianCertificate C k := by
  let R : Language := fun z => modularThresholdVerifier z=true
  have hR : AtCHLevel 0 R := native_polynomial_simulation.2 modularThresholdVerifier
    native_modularThresholdVerifier.computableInPolyTime (fun _ => False)
  let A : Language := fun x => ∃ w : Word,w.length=polyBound 2048 4 x.length ∧ R (pairWord x w)
  refine ⟨A,⟨1,R,hR,?_⟩,?_⟩
  · exact (bounded_quantification_oracle_pp R 2048 4 (by decide)).1
  · intro n C hvalid k
    exact threshold_certificate_equivalence C hvalid k

end APSCounting893.Main
end Component_40

open APSCounting893.Main
theorem solution :
    ∃ A : Language,InCountingHierarchy A ∧
      ∀ (n : ℕ) (C : ArithmeticCircuit n),ValidCircuit .rational C →
        ∀ k : ℕ,A (pairWord C.encode (encodeNat k)) ↔ ModularJacobianCertificate C k := by
  exact modular_threshold_language_in_ch_proof

