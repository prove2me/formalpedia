-- Prove2me | solution 1 for APSCounting893.Main.implicit_short_integer_sums_in_ch
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T21:05:11.313931+00:00
-- url     : https://prove2.me/submissions/c5ba176d-2396-452c-90d7-03bb3c62566c

import Definitions.Def_APSCounting893_Main_BinaryOracleArithmetic
import Definitions.Def_APSCounting893_Main_CountingHierarchy
import Definitions.Def_APSCounting893_Main_ImplicitCountingArithmetic
import Definitions.Def_APSCounting893_Main_OracleProofPrimitives
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_BitString
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Nat
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Nat_Binary
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Decoder_Nat
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Length
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Nat_Words
import Mathlib
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
end Component_3

section Component_4

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
end Component_4

section Component_5
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
end Component_5

section Component_6
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
end Component_6

section Component_7
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
end Component_7

section Component_8
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
end Component_8

section Component_9
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime

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

lemma native_smallSumQuery (a b c d : ℕ) : ComputableTidilyInPolyTime
    (smallSumQuery a b c d) encBits encBits := by
  have hx := ComputableTidilyInPolyTime.unframe.comp ComputableTidilyInPolyTime.unframe
  have hw := ComputableTidilyInPolyTime.dropFrame
  have hn := length_bits.comp hx
  have hr := (native_polyBound_unary a b).comp hn
  have hs := (native_polyBound_unary c d).comp hn
  have htotal := unary_add.comp (hr.prod hs)
  have hlength := length_bits.comp hw
  have hlengthok := unary_le' htotal hlength
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

end APSCounting893.Main
end Component_9

section Component_10
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
end Component_10

section Component_11
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
end Component_11

section Component_12
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
end Component_12

section Component_13
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
end Component_13

section Component_14
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
end Component_14

section Component_15
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
end Component_15

section Component_16
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
end Component_16

section Component_17
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
end Component_17

section Component_18
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
end Component_18

section Component_19
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
end Component_19

section Component_20
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace APSCounting893.Main
open Turing.MultiTapeTM

lemma small_sum_less_in_ch (F : Word → ℕ) (j a b c d : ℕ)
    (hless : AtCHLevel j (NaturalLessLanguage F))
    (hF : ∀ x i : Word,i.length=polyBound a b x.length →
      F (Turing.MultiTapeTM.frame x++i)≤2^polyBound c d x.length) :
    AtCHLevel (j+5) (NaturalLessLanguage (indexedNaturalSum F a b)) := by
  have hpre := hless.native_tagged_preimage (smallSumQuery a b c d)
    (native_smallSumQuery a b c d).computableInPolyTime
  have hcount := hpre.count_threshold (a+c+2) (max b d+1) (by omega)
  have he : (fun z => ofBits (Turing.MultiTapeTM.dropFrame z)<
      Set.ncard {w : Word | w.length+1=polyBound (a+c+2) (max b d+1) z.length ∧
        taggedOracle (NaturalLessLanguage F) (smallSumQuery a b c d (pairWord z w))})=
      NaturalLessLanguage (indexedNaturalSum F a b) := by
    funext z
    apply propext
    let Q := polyBound (a+c+2) (max b d+1) z.length
    have hQ : 0<Q := by dsimp [Q,polyBound];positivity
    have hc := smallSum_word_clock a b c d z
    have hN : polyBound a b (Turing.MultiTapeTM.unframe z).length+
        polyBound c d (Turing.MultiTapeTM.unframe z).length≤Q-1 := by dsimp [Q];omega
    have hs : {w : Word | w.length+1=Q ∧
        taggedOracle (NaturalLessLanguage F) (smallSumQuery a b c d (pairWord z w))}=
        {w : Word | w.length=Q-1 ∧
          taggedOracle (NaturalLessLanguage F) (smallSumQuery a b c d (pairWord z w))} := by
      ext w
      have hl : w.length+1=Q ↔ w.length=Q-1 := by omega
      simp only [Set.mem_ofPred_eq,hl]
    change ofBits (Turing.MultiTapeTM.dropFrame z)<Set.ncard {w : Word |
      w.length+1=Q ∧ taggedOracle (NaturalLessLanguage F) (smallSumQuery a b c d (pairWord z w))} ↔ _
    rw [hs,smallSum_count_identity F a b c d z (Q-1) hN (hF _)]
    rfl
  rw [he] at hcount
  simpa only [Nat.add_assoc] using hcount

lemma small_sum_graph_in_ch (F : Word → ℕ) (j a b c d : ℕ)
    (hless : AtCHLevel j (NaturalLessLanguage F))
    (hF : ∀ x i : Word,i.length=polyBound a b x.length →
      F (Turing.MultiTapeTM.frame x++i)≤2^polyBound c d x.length) :
    AtCHLevel (j+8) (NaturalGraphLanguage (indexedNaturalSum F a b)) := by
  simpa only [Nat.add_assoc] using (small_sum_less_in_ch F j a b c d hless hF).graph_from_less

end APSCounting893.Main
end Component_20

section Component_21
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main
open Turing.MultiTapeTM Cslib.BitString

lemma indexedNaturalSum_bits_bound (F : Word → ℕ) (a b c d : ℕ)
    (hF : ∀ x i : Word,i.length=polyBound a b x.length →
      F (Turing.MultiTapeTM.frame x++i)≤2^polyBound c d x.length) (x : Word) :
    (indexedNaturalSum F a b x).bits.length≤polyBound (a+c+1) (max b d) x.length := by
  let r := polyBound a b x.length
  let s := polyBound c d x.length
  have hsum : indexedNaturalSum F a b x≤2^(r+s) := by
    unfold indexedNaturalSum
    rw [pow_add]
    dsimp only [r,s]
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id] using
      Finset.sum_le_sum (s:=Finset.univ) (fun (i : Fin (2^polyBound a b x.length)) _ =>
        hF x (lowBits (polyBound a b x.length) i.val) (length_lowBits _ _))
  have hbits : (indexedNaturalSum F a b x).bits.length≤r+s+1 := by
    have hh := Nat.size_le_size hsum
    simpa only [Nat.size_eq_bits_len,Nat.size_pow] using hh
  apply hbits.trans
  let U := (x.length+1)^(max b d)
  have hU : 1≤U := Nat.one_le_pow _ _ (by omega)
  have hr : r≤a*U := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (le_max_left _ _))
  have hs : s≤c*U := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (le_max_right _ _))
  change r+s+1≤(a+c+1)*U
  nlinarith

lemma indexed_term_uniform_value_bound (F : Word → ℕ) (a b e f : ℕ)
    (hF : ∀ y,(F y).bits.length≤polyBound e f y.length) (x i : Word)
    (hi : i.length=polyBound a b x.length) :
    F (Turing.MultiTapeTM.frame x++i)<
      2^polyBound (e*(a+4)^f+1) ((b+1)*f) x.length := by
  have hx : 1≤(x.length+1)^(b+1) := Nat.one_le_pow _ _ (by omega)
  have hxl : x.length+1≤(x.length+1)^(b+1) := by
    simpa only [pow_one] using Nat.pow_le_pow_right (n:=x.length+1) (by omega) (show 1≤b+1 by omega)
  have hp : polyBound a b x.length≤a*(x.length+1)^(b+1) :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (Nat.le_succ b))
  have hlen : (Turing.MultiTapeTM.frame x++i).length+1≤(a+4)*(x.length+1)^(b+1) := by
    simp only [List.length_append,length_frame,hi]
    nlinarith
  have hbound : polyBound e f (Turing.MultiTapeTM.frame x++i).length≤
      polyBound (e*(a+4)^f+1) ((b+1)*f) x.length := by
    apply (Nat.mul_le_mul_left e (Nat.pow_le_pow_left hlen f)).trans
    simp only [mul_pow,←pow_mul,polyBound]
    nlinarith [Nat.zero_le ((x.length+1)^((b+1)*f))]
  apply Nat.size_le.mp
  simpa only [Nat.size_eq_bits_len] using (hF _).trans hbound

end APSCounting893.Main
end Component_21

section Component_22
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
end Component_22

section Component_23
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
end Component_23

section Component_24
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace APSCounting893.Main

lemma implicit_short_integer_sums_in_ch_proof (F : Word → ℕ) (j a b e f : ℕ)
    (hF : ∀ x,(F x).bits.length≤polyBound e f x.length)
    (hgraph : AtCHLevel j (NaturalGraphLanguage F)) :
    AtCHLevel (j+11) (NaturalGraphLanguage (indexedNaturalSum F a b)) ∧
      ∀ x,(indexedNaturalSum F a b x).bits.length≤
        polyBound (a+e*(a+4)^f+2) (max b ((b+1)*f)) x.length := by
  have hless := natural_short_less_in_ch F j e f hF hgraph
  have hterm : ∀ x i : Word,i.length=polyBound a b x.length →
      F (Turing.MultiTapeTM.frame x++i)≤2^polyBound (e*(a+4)^f+1) ((b+1)*f) x.length :=
    fun x i hi => (indexed_term_uniform_value_bound F a b e f hF x i hi).le
  have hsum := small_sum_graph_in_ch F (j+3) a b (e*(a+4)^f+1) ((b+1)*f) hless hterm
  constructor
  · simpa only [Nat.add_assoc] using hsum
  · intro x
    simpa only [Nat.add_assoc] using indexedNaturalSum_bits_bound F a b (e*(a+4)^f+1) ((b+1)*f) hterm x

end APSCounting893.Main
end Component_24

open APSCounting893.Main
theorem solution
    (F : Word → ℕ) (j a b e f : ℕ)
    (hF : ∀ x,(F x).bits.length ≤ polyBound e f x.length)
    (hgraph : AtCHLevel j (NaturalGraphLanguage F)) :
    AtCHLevel (j+11) (NaturalGraphLanguage (indexedNaturalSum F a b)) ∧
      ∀ x,(indexedNaturalSum F a b x).bits.length ≤
        polyBound (a+e*(a+4)^f+2) (max b ((b+1)*f)) x.length := by
  exact implicit_short_integer_sums_in_ch_proof F j a b e f hF hgraph
