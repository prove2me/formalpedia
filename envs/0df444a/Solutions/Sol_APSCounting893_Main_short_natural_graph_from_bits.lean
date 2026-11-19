-- Prove2me | solution 1 for APSCounting893.Main.short_natural_graph_from_bits
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T20:48:13.473567+00:00
-- url     : https://prove2.me/submissions/18fd94ba-f9ad-46ad-bf81-b83a18dee276

import Definitions.Def_APSCounting893_Main_BinaryOracleArithmetic
import Definitions.Def_APSCounting893_Main_CountingHierarchy
import Definitions.Def_APSCounting893_Main_OracleProofPrimitives
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_BitString
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Nat_BinaryDiv
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Length
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Nat_Words
import Theorems.Thm_APSCounting893_Main_bounded_majority_oracle_pp
import Theorems.Thm_APSCounting893_Main_bounded_quantification_oracle_pp
import Theorems.Thm_APSCounting893_Main_native_polynomial_oracle_preimage
import Theorems.Thm_APSCounting893_Main_stack_program_polynomial_simulation
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

section Component_0
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
end Component_0

section Component_1
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
end Component_1

section Component_2
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
end Component_2

section Component_3
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
end Component_3

section Component_4

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
end Component_4

section Component_5

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
end Component_5

section Component_6
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
end Component_6

section Component_7
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
end Component_7

section Component_8
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
end Component_8

section Component_9
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
end Component_9

section Component_10
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
end Component_10

section Component_11
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace APSCounting893.Main

lemma natural_short_graph_in_ch (F : Word → ℕ) (j a b : ℕ)
    (hF : ∀ x,(F x).bits.length≤polyBound a b x.length)
    (hbits : AtCHLevel j (NaturalBitLanguage F)) :
    AtCHLevel (j+3) (NaturalGraphLanguage F) := by
  have hh := hbits.native_tagged_forall naturalGraphQuery
    native_naturalGraphQuery.computableInPolyTime (a+1) (b+1) (by omega)
  have he : (fun z => ∀ w : Word,w.length=polyBound (a+1) (b+1) z.length →
      taggedOracle (NaturalBitLanguage F) (naturalGraphQuery (pairWord z w)))=NaturalGraphLanguage F := by
    funext z
    apply propext
    change (∀ w : Word,w.length=polyBound (a+1) (b+1) z.length →
      taggedOracle (NaturalBitLanguage F) (naturalGraphQuery (pairWord z w))) ↔
      F (Turing.MultiTapeTM.unframe z)=Turing.MultiTapeTM.ofBits (Turing.MultiTapeTM.dropFrame z)
    simp only [naturalGraphQuery_semantics]
    obtain ⟨ha,hb⟩ := graph_bit_clock_bounds F a b hF z
    exact (naturals_equal_iff_bounded_word_bits _ _ _ ha hb).symm
  rw [he] at hh
  exact hh

end APSCounting893.Main
end Component_11

open APSCounting893.Main
theorem solution
    (F : Word → ℕ) (j a b : ℕ)
    (hF : ∀ x,(F x).bits.length ≤ polyBound a b x.length)
    (hbits : AtCHLevel j (NaturalBitLanguage F)) :
    AtCHLevel (j+3) (NaturalGraphLanguage F) := by
  exact natural_short_graph_in_ch F j a b hF hbits
