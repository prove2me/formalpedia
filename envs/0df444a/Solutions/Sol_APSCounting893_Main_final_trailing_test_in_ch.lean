-- Prove2me | solution 1 for APSCounting893.Main.final_trailing_test_in_ch
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T07:18:32.379569+00:00
-- url     : https://prove2.me/submissions/44029de0-a89c-42ae-9e03-385e10eed866

import Definitions.Def_APSCounting893_Main_CoefficientLanguages
import Definitions.Def_APSCounting893_Main_CountingHierarchy
import Definitions.Def_APSCounting893_Main_OracleProofPrimitives
import Theorems.Thm_APSCounting893_Main_bounded_quantification_oracle_pp
import Theorems.Thm_APSCounting893_Main_trailing_verifier_in_oracleP
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

section Component_0

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
end Component_0

section Component_1

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
end Component_1

section Component_2

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
end Component_2

section Component_3
set_option autoImplicit false
namespace APSCounting893.Main
lemma pairWord_length (x y : Word) : (pairWord x y).length = 2 * x.length + 1 + y.length := by
  simp [pairWord, List.length_flatMap, List.sum_replicate, Nat.mul_comm, Nat.add_assoc, Nat.add_comm]


end APSCounting893.Main
end Component_3

section Component_4
set_option autoImplicit false
namespace APSCounting893.Main
lemma decodePair_pairWord (x y : Word) : decodePair (pairWord x y) = some (x, y) := by
  induction x with
  | nil => rfl
  | cons b x ih =>
      change (decodePair (pairWord x y)).map _ = _
      rw [ih]
      rfl

lemma decodePair_inverse (v x y : Word) (h : decodePair v = some (x, y)) : v = pairWord x y := by
  induction v using List.twoStepInduction generalizing x y with
  | nil => simp [decodePair] at h
  | singleton b =>
      cases b with
      | false =>
          have heq : ([], []) = (x, y) := by simpa [decodePair] using h
          cases heq
          rfl
      | true => simp [decodePair] at h
  | cons_cons b c v ih _ =>
      cases b with
      | false =>
          have heq : ([], c :: v) = (x, y) := by simpa [decodePair] using h
          cases heq
          rfl
      | true =>
          cases hv : decodePair v with
          | none => simp [decodePair, hv] at h
          | some p =>
              have heq : (c :: p.1, p.2) = (x, y) := by simpa [decodePair, hv] using h
              cases heq
              rw [ih p.1 p.2 hv]
              rfl


end APSCounting893.Main
end Component_4

section Component_5

set_option autoImplicit false
open MvPolynomial
namespace APSCounting893.Main

lemma coefficientIn_zero {K : Type} [CommRing K] {n : ℕ} (v : Fin n) (k : ℕ) :
    coefficientIn v k (0 : MvPolynomial (Fin n) K) = 0 := by
  simp [coefficientIn]

lemma coefficientIn_monomial {K : Type} [CommRing K] {n : ℕ}
    (v : Fin n) (k : ℕ) (e : Fin n →₀ ℕ) (a : K) :
    coefficientIn v k (monomial e a) =
      if e v = k then monomial (e - Finsupp.single v k) a else 0 := by
  classical
  by_cases ha : a = 0
  · simp [ha, coefficientIn_zero]
  · simp [coefficientIn, support_monomial, ha]

lemma coefficientIn_add {K : Type} [CommRing K] {n : ℕ}
    (v : Fin n) (k : ℕ) (p q : MvPolynomial (Fin n) K) :
    coefficientIn v k (p + q) = coefficientIn v k p + coefficientIn v k q := by
  classical
  change Finsupp.sum (AddMonoidAlgebra.coeff (p + q))
    (fun e a => if e v = k then monomial (e - Finsupp.single v k) a else 0) =
    Finsupp.sum (AddMonoidAlgebra.coeff p)
      (fun e a => if e v = k then monomial (e - Finsupp.single v k) a else 0) +
    Finsupp.sum (AddMonoidAlgebra.coeff q)
      (fun e a => if e v = k then monomial (e - Finsupp.single v k) a else 0)
  rw [AddMonoidAlgebra.coeff_add]
  apply Finsupp.sum_add_index
  · intro e; split_ifs <;> simp
  · intro e a b; split_ifs <;> simp

lemma coefficientIn_sum {K : Type} [CommRing K] {n : ℕ} {ι : Type}
    (v : Fin n) (k : ℕ) (s : Finset ι) (p : ι → MvPolynomial (Fin n) K) :
    coefficientIn v k (∑ i ∈ s, p i) = ∑ i ∈ s, coefficientIn v k (p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [coefficientIn_zero]
  | @insert i s hi ih => simp [hi, coefficientIn_add, ih]

lemma coefficientIn_coeff {K : Type} [CommRing K] {n : ℕ}
    (v : Fin n) (k : ℕ) (p : MvPolynomial (Fin n) K) (e : Fin n →₀ ℕ) :
    (coefficientIn v k p).coeff e =
      if e v = 0 then p.coeff (e + Finsupp.single v k) else 0 := by
  classical
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq =>
    rw [coefficientIn_add, coeff_add, hp, hq, coeff_add]
    split_ifs <;> simp
  | monomial d a =>
    rw [coefficientIn_monomial]
    by_cases hd : d v = k
    · rw [if_pos hd]
      by_cases he : e v = 0
      · rw [if_pos he, coeff_monomial, coeff_monomial]
        have hle : Finsupp.single v k ≤ d := Finsupp.single_le_iff.mpr hd.ge
        have hi : d - Finsupp.single v k = e ↔ d = e + Finsupp.single v k := by
          constructor
          · intro h; rw [← h, tsub_add_cancel_of_le hle]
          · intro h; simp [h]
        simp only [hi]
      · rw [if_neg he, coeff_monomial]
        have hi : d - Finsupp.single v k ≠ e := by
          intro h
          have := congrArg (fun f : Fin n →₀ ℕ => f v) h
          simp [Finsupp.tsub_apply, hd] at this
          exact he this.symm
        simp [hi]
    · rw [if_neg hd, coeff_zero]
      split_ifs with he
      · rw [coeff_monomial]
        have hi : d ≠ e + Finsupp.single v k := by
          intro h; apply hd
          simpa [he] using congrArg (fun f : Fin n →₀ ℕ => f v) h
        simp [hi]
      · rfl

lemma coefficientIn_ne_zero_iff {K : Type} [CommRing K] {n : ℕ}
    (v : Fin n) (k : ℕ) (p : MvPolynomial (Fin n) K) :
    coefficientIn v k p ≠ 0 ↔ ∃ e ∈ p.support, e v = k := by
  classical
  constructor
  · intro h
    obtain ⟨e, he⟩ := exists_coeff_ne_zero h
    rw [coefficientIn_coeff] at he
    split_ifs at he with hv
    · refine ⟨e + Finsupp.single v k, mem_support_iff.mpr he, ?_⟩
      simp [hv]
    · exact (he rfl).elim
  · rintro ⟨e, he, hv⟩ h
    have ha : (e - Finsupp.single v k) v = 0 := by simp [Finsupp.tsub_apply, hv]
    have hb : e - Finsupp.single v k + Finsupp.single v k = e :=
      tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr hv.ge)
    have := congrArg (coeff (e - Finsupp.single v k)) h
    simpa [coefficientIn_coeff, ha, hb, mem_support_iff.mp he] using this

lemma trailingCoefficient_ne_zero {K : Type} [CommRing K] {n : ℕ}
    (v : Fin n) (p : MvPolynomial (Fin n) K) (hp : p ≠ 0) :
    trailingCoefficient v p ≠ 0 := by
  classical
  have hs : p.support.Nonempty := support_nonempty.mpr hp
  rw [trailingCoefficient, dif_pos hs, coefficientIn_ne_zero_iff]
  exact Finset.mem_image.mp (Finset.min'_mem _ (hs.image _))

lemma coefficientIn_totalDegree_le {K : Type} [CommRing K] {n : ℕ}
    (v : Fin n) (k : ℕ) (p : MvPolynomial (Fin n) K) :
    (coefficientIn v k p).totalDegree ≤ p.totalDegree := by
  classical
  unfold totalDegree
  apply Finset.sup_le
  intro e he
  have hc := mem_support_iff.mp he
  rw [coefficientIn_coeff] at hc
  split_ifs at hc with hv
  · have hd := le_totalDegree (mem_support_iff.mpr hc)
    have hadd : (e + Finsupp.single v k).sum (fun _ a => a) =
        e.sum (fun _ a => a) + k := by
      simp [Finsupp.sum_add_index']
    rw [hadd] at hd
    exact (Nat.le_add_right _ _).trans hd
  · exact (hc rfl).elim

lemma trailingCoefficient_totalDegree_le {K : Type} [CommRing K] {n : ℕ}
    (v : Fin n) (p : MvPolynomial (Fin n) K) :
    (trailingCoefficient v p).totalDegree ≤ p.totalDegree := by
  classical
  unfold trailingCoefficient
  split_ifs
  · exact coefficientIn_totalDegree_le ..
  · simp

lemma trailingCoefficient_eq_of_min {K : Type} [CommRing K] {n : ℕ}
    (v : Fin n) (p : MvPolynomial (Fin n) K) (k : ℕ)
    (hk : coefficientIn v k p ≠ 0)
    (hmin : ∀ j < k, coefficientIn v j p = 0) :
    trailingCoefficient v p = coefficientIn v k p := by
  classical
  obtain ⟨e, he, hv⟩ := (coefficientIn_ne_zero_iff v k p).mp hk
  have hs : p.support.Nonempty := ⟨e, he⟩
  rw [trailingCoefficient, dif_pos hs]
  congr 1
  apply le_antisymm
  · apply Finset.min'_le
    exact Finset.mem_image.mpr ⟨e, he, hv⟩
  · by_contra h
    have hlt := Nat.lt_of_not_ge h
    obtain ⟨d, hd, heq⟩ := Finset.mem_image.mp (Finset.min'_mem _ (hs.image (fun e => e v)))
    have hz := hmin _ hlt
    exact ((coefficientIn_ne_zero_iff v _ p).mpr ⟨d, hd, heq⟩) hz

lemma coefficientIn_map {K L : Type} [CommRing K] [CommRing L] {n : ℕ}
    (f : K →+* L) (v : Fin n) (k : ℕ) (p : MvPolynomial (Fin n) K) :
    coefficientIn v k (MvPolynomial.map f p) =
      MvPolynomial.map f (coefficientIn v k p) := by
  classical
  ext e
  simp only [coefficientIn_coeff, coeff_map]
  split_ifs <;> simp

lemma trailingCoefficient_map {K L : Type} [CommRing K] [CommRing L] {n : ℕ}
    (f : K →+* L) (v : Fin n) (p : MvPolynomial (Fin n) K)
    (hp : MvPolynomial.map f (trailingCoefficient v p) ≠ 0) :
    trailingCoefficient v (MvPolynomial.map f p) =
      MvPolynomial.map f (trailingCoefficient v p) := by
  classical
  have hs : p.support.Nonempty := by
    by_contra h
    simp [trailingCoefficient, h] at hp
  let k := (p.support.image (fun e => e v)).min' (hs.image _)
  have htc : trailingCoefficient v p = coefficientIn v k p := by
    simp [trailingCoefficient, hs, k]
  rw [htc] at hp ⊢
  rw [← coefficientIn_map] at hp ⊢
  apply trailingCoefficient_eq_of_min v _ k hp
  intro j hj
  rw [coefficientIn_map]
  have hz : coefficientIn v j p = 0 := by
    by_contra h
    obtain ⟨e, he, hv⟩ := (coefficientIn_ne_zero_iff v j p).mp h
    have hkj : k ≤ j := Finset.min'_le _ _ (Finset.mem_image.mpr ⟨e, he, hv⟩)
    omega
  simp [hz]

lemma specializeParameters_monomial {K : Type} [Field K] [Algebra ℚ K]
    {s k : ℕ} (theta : Fin s → K) (e : Fin (s + (k + 1)) →₀ ℕ) (a : ℚ) :
    specializeParameters theta (monomial e a) =
      monomial (Finsupp.equivFunOnFinite.symm (fun i : Fin (k + 1) => e (i.natAdd s)))
        (algebraMap ℚ K a * ∏ i : Fin s, theta i ^ e (i.castAdd (k + 1))) := by
  classical
  simp only [specializeParameters, eval₂Hom_monomial, RingHom.coe_comp, Function.comp_apply,
    Finsupp.prod_pow]
  rw [Fin.prod_univ_add]
  simp only [Fin.addCases_left, Fin.addCases_right]
  rw [monomial_eq]
  simp only [Finsupp.prod_pow, Finsupp.equivFunOnFinite_symm_apply_apply]
  simp [map_mul, map_prod, map_pow, mul_assoc]

lemma specializeParameters_coefficientIn {K : Type} [Field K] [Algebra ℚ K]
    {s k : ℕ} (theta : Fin s → K) (v : Fin (k + 1)) (j : ℕ)
    (p : MvPolynomial (Fin (s + (k + 1))) ℚ) :
    specializeParameters theta (coefficientIn (v.natAdd s) j p) =
      coefficientIn v j (specializeParameters theta p) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq =>
    simp only [coefficientIn_add, specializeParameters, map_add] at hp hq ⊢
    rw [hp, hq]
  | monomial e a =>
    rw [coefficientIn_monomial, specializeParameters_monomial, coefficientIn_monomial]
    simp only [Finsupp.equivFunOnFinite_symm_apply_apply]
    split_ifs with he
    · rw [specializeParameters_monomial]
      have haux : Finsupp.equivFunOnFinite.symm
          (fun i : Fin (k + 1) => (e - Finsupp.single (v.natAdd s) j) (i.natAdd s)) =
          Finsupp.equivFunOnFinite.symm (fun i : Fin (k + 1) => e (i.natAdd s)) -
            Finsupp.single v j := by
        ext i
        simp [Finsupp.tsub_apply, Finsupp.single_apply, eq_comm]
      rw [haux]
      congr 2
      apply Finset.prod_congr rfl
      intro i _
      have hn : i.castAdd (k + 1) ≠ v.natAdd s := by
        intro h
        have hval := congrArg Fin.val h
        simp at hval
        omega
      simp [Finsupp.tsub_apply, Finsupp.single_apply, hn, Ne.symm hn]
    · simp [specializeParameters]

lemma totalDegree_eval₂_linear {K L : Type} [CommRing K] [CommRing L] {n m : ℕ}
    (f : K →+* L) (g : Fin n → MvPolynomial (Fin m) L)
    (hg : ∀ i, (g i).totalDegree ≤ 1) (p : MvPolynomial (Fin n) K) :
    (eval₂Hom (MvPolynomial.C.comp f) g p).totalDegree ≤ p.totalDegree := by
  classical
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  apply totalDegree_finsetSum_le
  intro e he
  rw [eval₂Hom_monomial]
  apply (totalDegree_mul _ _).trans
  simp only [RingHom.coe_comp, Function.comp_apply, totalDegree_C, zero_add]
  rw [Finsupp.prod_pow]
  apply (totalDegree_finsetProd _ _).trans
  apply le_trans (Finset.sum_le_sum (fun i _ =>
    (totalDegree_pow _ _).trans (Nat.mul_le_mul_left _ (hg i))))
  simpa [Finsupp.sum_fintype] using (le_totalDegree he)

lemma specializeParameters_trailingCoefficient {K : Type} [Field K] [Algebra ℚ K]
    {s k : ℕ} (theta : Fin s → K) (v : Fin (k + 1))
    (p : MvPolynomial (Fin (s + (k + 1))) ℚ)
    (hp : specializeParameters theta (trailingCoefficient (v.natAdd s) p) ≠ 0) :
    specializeParameters theta (trailingCoefficient (v.natAdd s) p) =
      trailingCoefficient v (specializeParameters theta p) := by
  classical
  have hs : p.support.Nonempty := by
    by_contra h
    simp [trailingCoefficient, h, specializeParameters] at hp
  let j := (p.support.image (fun e => e (v.natAdd s))).min' (hs.image _)
  have htc : trailingCoefficient (v.natAdd s) p = coefficientIn (v.natAdd s) j p := by
    simp [trailingCoefficient, hs, j]
  rw [htc, specializeParameters_coefficientIn] at hp ⊢
  symm
  apply trailingCoefficient_eq_of_min v _ j hp
  intro i hi
  rw [← specializeParameters_coefficientIn]
  have hz : coefficientIn (v.natAdd s) i p = 0 := by
    by_contra h
    obtain ⟨e, he, hv⟩ := (coefficientIn_ne_zero_iff (v.natAdd s) i p).mp h
    have hji : j ≤ i := Finset.min'_le _ _ (Finset.mem_image.mpr ⟨e, he, hv⟩)
    omega
  simp [hz, specializeParameters]

lemma specialization_nonzero_witness {s k : ℕ}
    (p : MvPolynomial (Fin (s + (k + 1))) ℚ) (hp : p ≠ 0) :
    ∃ A : MvPolynomial (Fin s) ℚ,
      A ≠ 0 ∧ A.totalDegree ≤ p.totalDegree ∧
      ∀ (K : Type) [Field K] [Algebra ℚ K] (theta : Fin s → K),
        eval₂ (algebraMap ℚ K) theta A ≠ 0 → specializeParameters theta p ≠ 0 := by
  classical
  obtain ⟨x, hx⟩ : ∃ x : Fin (s + (k + 1)) → ℚ, eval x p ≠ 0 := by
    by_contra h
    push_neg at h
    apply hp
    apply MvPolynomial.funext
    intro x
    simpa using h x
  let z : Fin (k + 1) → ℚ := fun i => x (i.natAdd s)
  let freeze : MvPolynomial (Fin (s + (k + 1))) ℚ →+* MvPolynomial (Fin s) ℚ :=
    eval₂Hom C (Fin.addCases X (fun i => C (z i)))
  have commute (K : Type) [Field K] [Algebra ℚ K] (theta : Fin s → K) :
      (eval₂Hom (algebraMap ℚ K) theta).comp freeze =
        (eval₂Hom (RingHom.id K) (fun i => algebraMap ℚ K (z i))).comp
          (eval₂Hom (C.comp (algebraMap ℚ K)) (Fin.addCases (fun i => C (theta i)) X)) := by
    apply MvPolynomial.ringHom_ext
    · intro a; simp [freeze]
    · intro i
      refine Fin.addCases ?_ ?_ i
      · intro j; simp [freeze]
      · intro j; simp [freeze]
  refine ⟨freeze p, ?_, ?_, ?_⟩
  · intro h
    have hcomp : (eval₂Hom (RingHom.id ℚ) (fun i => x (i.castAdd (k + 1)))).comp freeze =
        eval₂Hom (RingHom.id ℚ) x := by
      apply MvPolynomial.ringHom_ext
      · intro a; simp [freeze]
      · intro i
        refine Fin.addCases ?_ ?_ i
        · intro j; simp [freeze]
        · intro j; simp [freeze, z]
    apply hx
    change (eval₂Hom (RingHom.id ℚ) x) p = 0
    rw [← hcomp, RingHom.comp_apply, h, map_zero]
  · apply totalDegree_eval₂_linear (RingHom.id ℚ)
    intro i
    refine Fin.addCases ?_ ?_ i
    · intro j; simp
    · intro j; simp
  · intro K _ _ theta hA hz
    apply hA
    change (eval₂Hom (algebraMap ℚ K) theta) (freeze p) = 0
    rw [← RingHom.comp_apply, commute K theta, RingHom.comp_apply]
    change (eval₂Hom (RingHom.id K) (fun i => algebraMap ℚ K (z i)))
      (specializeParameters theta p) = 0
    rw [hz, map_zero]

lemma nestedTrailing_specialization_aux {s k : ℕ}
    (order : List (Fin (k + 1)))
    (p : MvPolynomial (Fin (s + (k + 1))) ℚ) (hp : p ≠ 0) :
    ∃ A : Fin order.length → MvPolynomial (Fin s) ℚ,
      (∀ i, A i ≠ 0 ∧ (A i).totalDegree ≤ p.totalDegree) ∧
      ∀ (K : Type) [Field K] [Algebra ℚ K] (theta : Fin s → K),
        (∀ i, eval₂ (algebraMap ℚ K) theta (A i) ≠ 0) →
        specializeParameters theta (nestedTrailing (order.map (Fin.natAdd s)) p) =
          nestedTrailing order (specializeParameters theta p) := by
  classical
  induction order generalizing p with
  | nil =>
    refine ⟨Fin.elim0, ?_, ?_⟩
    · exact fun i => Fin.elim0 i
    · intro K _ _ theta h
      rfl
  | cons v order ih =>
    let q := trailingCoefficient (v.natAdd s) p
    have hq : q ≠ 0 := trailingCoefficient_ne_zero _ _ hp
    obtain ⟨a, ha, had, haw⟩ := specialization_nonzero_witness q hq
    obtain ⟨B, hB, hBw⟩ := ih q hq
    refine ⟨Fin.cons a B, ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using And.intro ha (had.trans (trailingCoefficient_totalDegree_le _ _))
      · simpa using And.intro (hB j).1
          ((hB j).2.trans (trailingCoefficient_totalDegree_le _ _))
    · intro K _ _ theta hA
      have hqa : specializeParameters theta q ≠ 0 := haw K theta (by simpa using hA 0)
      have htc := specializeParameters_trailingCoefficient theta v p hqa
      have htail : ∀ i, eval₂ (algebraMap ℚ K) theta (B i) ≠ 0 := by
        intro i; simpa using hA i.succ
      have hrec := hBw K theta htail
      change specializeParameters theta (nestedTrailing (order.map (Fin.natAdd s)) q) =
        nestedTrailing order (trailingCoefficient v (specializeParameters theta p))
      rw [← htc]
      exact hrec

end APSCounting893.Main
end Component_5

section Component_6

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

noncomputable def nestedCoefficient {K : Type} [CommRing K] {n : ℕ}
    (order : List (Fin n)) (a : Fin n →₀ ℕ) (p : MvPolynomial (Fin n) K) :=
  order.foldl (fun q v => coefficientIn v (a v) q) p

lemma coefficientIn_support_shift {K : Type} [CommRing K] {n : ℕ}
    (p : MvPolynomial (Fin n) K) (v : Fin n) (j : ℕ) (e : Fin n →₀ ℕ) :
    e ∈ (coefficientIn v j p).support ↔
      e v = 0 ∧ e + Finsupp.single v j ∈ p.support := by
  classical
  simp only [mem_support_iff, coefficientIn_coeff]
  split_ifs with h
  · simp [h]
  · simp [h]

lemma nestedTrailing_eq_of_lex_min {K : Type} [CommRing K] {n : ℕ}
    (order : List (Fin n)) (horder : order.Nodup) (a : Fin n →₀ ℕ)
    (p : MvPolynomial (Fin n) K)
    (ha : ∃ e ∈ p.support, ∀ v ∈ order, e v = a v)
    (hmin : ∀ e ∈ p.support, ¬ List.Lex (· < ·) (order.map (fun v => e v))
      (order.map (fun v => a v))) :
    nestedTrailing order p = nestedCoefficient order a p := by
  classical
  induction order generalizing p with
  | nil => rfl
  | cons v order ih =>
      obtain ⟨hv, horder⟩ := List.nodup_cons.mp horder
      obtain ⟨e, he, hea⟩ := ha
      have hev : e v = a v := hea v (by simp)
      have hnonzero : coefficientIn v (a v) p ≠ 0 :=
        (coefficientIn_ne_zero_iff ..).mpr ⟨e, he, hev⟩
      have htc : trailingCoefficient v p = coefficientIn v (a v) p := by
        apply trailingCoefficient_eq_of_min v p (a v) hnonzero
        intro j hj
        by_contra hn
        obtain ⟨d, hd, hdv⟩ := (coefficientIn_ne_zero_iff ..).mp hn
        exact hmin d hd (by simpa only [List.map_cons] using
          (List.Lex.rel (hdv ▸ hj) : List.Lex (· < ·) (d v :: order.map (fun w => d w))
            (a v :: order.map (fun w => a w))))
      change nestedTrailing order (trailingCoefficient v p) =
        nestedCoefficient order a (coefficientIn v (a v) p)
      rw [htc]
      apply ih horder
      · refine ⟨e - Finsupp.single v (a v), ?_, ?_⟩
        · rw [coefficientIn_support_shift]
          constructor
          · simp [Finsupp.tsub_apply, hev]
          · rwa [tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr hev.ge)]
        · intro w hw
          have hwv : w ≠ v := by intro h; subst w; exact hv hw
          simpa [Finsupp.tsub_apply, hwv] using hea w (by simp [hw])
      · intro d hd hlex
        obtain ⟨hdv, hdp⟩ := (coefficientIn_support_shift p v (a v) d).mp hd
        apply hmin (d + Finsupp.single v (a v)) hdp
        have htail : order.map (fun w => (d + Finsupp.single v (a v)) w) =
            order.map (fun w => d w) := by
          apply List.map_congr_left
          intro w hw
          have hwv : w ≠ v := by intro h; subst w; exact hv hw
          simp [hwv]
        simp only [List.map_cons]
        rw [htail]
        simpa only [Finsupp.add_apply, Finsupp.single_eq_same, hdv, zero_add] using (List.Lex.cons hlex : List.Lex (· < ·)
            (a v :: order.map (fun w => d w)) (a v :: order.map (fun w => a w)))

lemma orderExponent_apply_not_mem {n : ℕ} (order : List (Fin n)) (a : Fin n →₀ ℕ)
    (v : Fin n) (hv : v ∉ order) : orderExponent order a v = 0 := by
  classical
  induction order with
  | nil => simp [orderExponent]
  | cons w order ih =>
      have hvw : v ≠ w := by intro h; subst v; exact hv (by simp)
      have hv' : v ∉ order := by intro h; exact hv (List.mem_cons_of_mem w h)
      simp [orderExponent, Finsupp.single_apply, hvw, hvw.symm,
        show ((order.map (fun w => Finsupp.single w (a w))).sum) v = 0 from ih hv']

lemma nestedCoefficient_coeff {K : Type} [CommRing K] {n : ℕ}
    (order : List (Fin n)) (horder : order.Nodup) (a e : Fin n →₀ ℕ)
    (p : MvPolynomial (Fin n) K) :
    (nestedCoefficient order a p).coeff e =
      if ∀ v ∈ order, e v = 0 then p.coeff (e + orderExponent order a) else 0 := by
  classical
  induction order generalizing p with
  | nil => simp [nestedCoefficient, orderExponent]
  | cons v order ih =>
      obtain ⟨hv, hn⟩ := List.nodup_cons.mp horder
      change (nestedCoefficient order a (coefficientIn v (a v) p)).coeff e = _
      rw [ih hn, coefficientIn_coeff]
      have hv0 := orderExponent_apply_not_mem order a v hv
      by_cases he : ∀ w ∈ order, e w = 0
      · rw [if_pos he]
        simp only [Finsupp.add_apply, hv0, add_zero]
        by_cases hev : e v = 0
        · rw [if_pos hev, if_pos (by
            intro w hw
            obtain rfl | hw := List.mem_cons.mp hw
            · exact hev
            · exact he w hw)]
          congr 1
          simp [orderExponent, add_assoc, add_left_comm, add_comm]
        · rw [if_neg hev, if_neg (by simp [hev])]
      · rw [if_neg he, if_neg (by
          intro hall
          apply he
          intro w hw
          exact hall w (List.mem_cons_of_mem v hw))]

lemma eval_zero_nestedCoefficient {K : Type} [CommRing K] {n : ℕ}
    (order : List (Fin n)) (horder : order.Nodup) (a : Fin n →₀ ℕ)
    (p : MvPolynomial (Fin n) K) :
    MvPolynomial.eval (fun _ => (0 : K)) (nestedCoefficient order a p) =
      p.coeff (orderExponent order a) := by
  rw [MvPolynomial.eval_zero']
  change (nestedCoefficient order a p).coeff 0 = _
  rw [nestedCoefficient_coeff order horder]
  simp

lemma eval_zero_nestedTrailing_of_lex_min {K : Type} [CommRing K] {n : ℕ}
    (order : List (Fin n)) (horder : order.Nodup) (a : Fin n →₀ ℕ)
    (p : MvPolynomial (Fin n) K) (ha : a ∈ p.support)
    (hmin : ∀ e ∈ p.support, ¬ List.Lex (· < ·) (order.map (fun v => e v))
      (order.map (fun v => a v))) :
    MvPolynomial.eval (fun _ => (0 : K)) (nestedTrailing order p) =
      p.coeff (orderExponent order a) := by
  rw [nestedTrailing_eq_of_lex_min order horder a p ⟨a, ha, by simp⟩ hmin,
    eval_zero_nestedCoefficient order horder]

lemma exists_support_lex_min {K : Type} [CommRing K] {n : ℕ}
    (order : List (Fin n)) (p : MvPolynomial (Fin n) K) (hp : p ≠ 0) :
    ∃ a ∈ p.support, ∀ e ∈ p.support,
      ¬ List.Lex (· < ·) (order.map (fun v => e v)) (order.map (fun v => a v)) := by
  classical
  let s := p.support.image (fun a => order.map (fun v => a v))
  have hs : s.Nonempty := (support_nonempty.mpr hp).image _
  obtain ⟨a, ha, hma⟩ := Finset.mem_image.mp (Finset.min'_mem s hs)
  refine ⟨a, ha, ?_⟩
  intro e he hlt
  have hle := Finset.min'_le s (order.map (fun v => e v)) (Finset.mem_image.mpr ⟨e, he, rfl⟩)
  rw [← hma] at hle
  exact (not_lt_of_ge hle) hlt

lemma support_exponents_le_totalDegree {K : Type} [CommRing K] {n : ℕ}
    (p : MvPolynomial (Fin n) K) (a : Fin n →₀ ℕ) (ha : a ∈ p.support) (v : Fin n) :
    a v ≤ p.totalDegree :=
  (MvPolynomial.monomial_le_degreeOf v ha).trans (MvPolynomial.degreeOf_le_totalDegree p v)

lemma trailing_zero_iff_bounded_coefficients {K : Type} [CommRing K] {n : ℕ}
    (order : List (Fin n)) (horder : order.Nodup) (p : MvPolynomial (Fin n) K)
    (hp : p ≠ 0) (D : ℕ) (hD : p.totalDegree ≤ D) :
    MvPolynomial.eval (fun _ => (0 : K)) (nestedTrailing order p) = 0 ↔
      ∃ a : Fin n →₀ ℕ, (∀ v, a v ≤ D) ∧ p.coeff a ≠ 0 ∧
        (∀ e : Fin n →₀ ℕ, (∀ v, e v ≤ D) →
          List.Lex (· < ·) (order.map (fun v => e v)) (order.map (fun v => a v)) →
          p.coeff e = 0) ∧ p.coeff (orderExponent order a) = 0 := by
  classical
  constructor
  · intro hz
    obtain ⟨a, ha, hmin⟩ := exists_support_lex_min order p hp
    refine ⟨a, fun v => (support_exponents_le_totalDegree p a ha v).trans hD,
      mem_support_iff.mp ha, ?_, ?_⟩
    · intro e he hlex
      by_contra hn
      exact hmin e (mem_support_iff.mpr hn) hlex
    · rwa [← eval_zero_nestedTrailing_of_lex_min order horder a p ha hmin]
  · rintro ⟨a, haD, ha, hmin, hz⟩
    have hlex : ∀ e ∈ p.support,
        ¬ List.Lex (· < ·) (order.map (fun v => e v)) (order.map (fun v => a v)) := by
      intro e he hlt
      exact (mem_support_iff.mp he) (hmin e
        (fun v => (support_exponents_le_totalDegree p e he v).trans hD) hlt)
    rwa [eval_zero_nestedTrailing_of_lex_min order horder a p (mem_support_iff.mpr ha) hlex]

end APSCounting893.Main
end Component_6

section Component_7

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma nat_testBit_false_of_bits_length_le (a q : ℕ) (h : a.bits.length ≤ q) : a.testBit q = false := by
  rw [Nat.testBit_eq_inth]
  exact (List.getI_eq_default (l := a.bits) h)

lemma nat_ne_zero_iff_exists_bit_below (a U : ℕ) (h : a.bits.length ≤ U) :
    a ≠ 0 ↔ ∃ q < U, a.testBit q = true := by
  constructor
  · intro ha
    obtain ⟨q, hq, _⟩ := Nat.exists_most_significant_bit ha
    have hlt : q < a.bits.length := by
      by_contra hn
      have hf := nat_testBit_false_of_bits_length_le a q (Nat.le_of_not_gt hn)
      rw [hq] at hf
      cases hf
    exact ⟨q, hlt.trans_le h, hq⟩
  · rintro ⟨q, hq, hb⟩ hz
    simp [hz] at hb

lemma coefficient_ne_zero_iff_query {k : ℕ}
    (R : Word → MvPolynomial (Fin (k + 1)) ℚ) (rho : CoefficientRepresentation k)
    (hrep : RepresentsPolynomialFamily R rho) (x : Word) (e : Fin (k + 1) →₀ ℕ)
    (U : ℕ) (hbound : (rho x e).1.natAbs.bits.length ≤ U) :
    (R x).coeff e ≠ 0 ↔ ∃ q < U,
      CoefficientBitLanguage rho (coefficientQuery x e .numerator q) := by
  have hden : ((rho x e).2 : ℚ) ≠ 0 := by exact_mod_cast (hrep x e).1.ne'
  have hnonzero : (R x).coeff e ≠ 0 ↔ (rho x e).1.natAbs ≠ 0 := by
    rw [(hrep x e).2, div_ne_zero_iff]
    simpa only [Int.cast_ne_zero, Int.natAbs_ne_zero] using (and_iff_left hden)
  rw [hnonzero, nat_ne_zero_iff_exists_bit_below _ U hbound]
  apply exists_congr
  intro q
  rw [coefficientBitLanguage_query_iff]
  rfl

lemma coefficient_query_length {k : ℕ} (x : Word) (e : Fin (k + 1) →₀ ℕ)
    (part : CoefficientPart) (q : ℕ) :
    (coefficientQuery x e part q).length =
      (2 * x.length.bits.length + 1) + x.length +
      (2 * (k + 1).bits.length + 1) +
      (∑ i : Fin (k + 1), (2 * (e i).bits.length + 1)) + part.encode.length +
      (2 * q.bits.length + 1) := by
  simp only [coefficientQuery, encodeNat, encodeList, List.length_append, List.length_replicate,
    List.length_singleton, List.length_flatMap, List.length_ofFn]
  simp only [List.map_ofFn, List.sum_ofFn, Function.comp_apply]
  ring

lemma bit_query_implies_coefficient_ne_zero {k : ℕ}
    (R : Word → MvPolynomial (Fin (k + 1)) ℚ) (rho : CoefficientRepresentation k)
    (hrep : RepresentsPolynomialFamily R rho) (x : Word) (e : Fin (k + 1) →₀ ℕ) (q : ℕ)
    (h : CoefficientBitLanguage rho (coefficientQuery x e .numerator q)) : (R x).coeff e ≠ 0 := by
  have hb := (coefficientBitLanguage_query_iff rho x e .numerator q).mp h
  change (rho x e).1.natAbs.testBit q = true at hb
  have hq : q < (rho x e).1.natAbs.bits.length := by
    by_contra hq
    have hf := nat_testBit_false_of_bits_length_le (rho x e).1.natAbs q (by omega)
    rw [hb] at hf
    cases hf
  exact (coefficient_ne_zero_iff_query R rho hrep x e _ le_rfl).mpr ⟨q, hq, h⟩

lemma coefficient_zero_implies_no_bit_query {k : ℕ}
    (R : Word → MvPolynomial (Fin (k + 1)) ℚ) (rho : CoefficientRepresentation k)
    (hrep : RepresentsPolynomialFamily R rho) (x : Word) (e : Fin (k + 1) →₀ ℕ)
    (hz : (R x).coeff e = 0) (q : ℕ) :
    ¬ CoefficientBitLanguage rho (coefficientQuery x e .numerator q) := by
  intro h
  exact bit_query_implies_coefficient_ne_zero R rho hrep x e q h hz

end APSCounting893.Main
end Component_7

section Component_8

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma bits_length_le_of_lt_pow (a p : ℕ) (h : a < 2 ^ p) : a.bits.length ≤ p := by
  rw [Nat.size_eq_bits_len]
  exact Nat.size_le.mpr h

lemma bits_length_le_self (a : ℕ) : a.bits.length ≤ a :=
  bits_length_le_of_lt_pow a a a.lt_two_pow_self

lemma bits_length_le_of_le_pow (a p : ℕ) (h : a ≤ 2 ^ p) : a.bits.length ≤ p + 1 := by
  apply bits_length_le_of_lt_pow
  have hp : 0 < 2 ^ p := by positivity
  rw [pow_succ]
  omega

lemma polyBound_padding (c d n : ℕ) :
    n + 1 ≤ polyBound (c + 1) (d + 1) n ∧
      polyBound c d n + 1 ≤ polyBound (c + 1) (d + 1) n := by
  have hbase : 1 ≤ (n + 1) ^ d := Nat.one_le_pow d _ (by omega)
  simp only [polyBound, pow_succ]
  constructor
  · have hpos : 0 < (c + 1) * (n + 1) ^ d := Nat.mul_pos (by omega) hbase
    simpa only [Nat.mul_assoc] using Nat.le_mul_of_pos_left (n + 1) hpos
  · calc
      c * (n + 1) ^ d + 1 ≤ c * (n + 1) ^ d + (n + 1) ^ d := Nat.add_le_add_left hbase _
      _ = (c + 1) * (n + 1) ^ d := by ring
      _ ≤ (c + 1) * ((n + 1) ^ d * (n + 1)) :=
        Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ (by omega))

lemma coefficient_query_polynomial_length {k : ℕ} (x : Word)
    (e : Fin (k + 1) →₀ ℕ) (part : CoefficientPart) (q c d : ℕ)
    (he : ∀ v, e v ≤ 2 ^ polyBound c d x.length)
    (hq : q < 2 ^ (polyBound c d x.length + 1)) :
    (coefficientQuery x e part q).length ≤
      polyBound ((3 * (k + 1) + 12 + 2 * (k + 1).bits.length) * (c + 1))
        (d + 1) x.length := by
  have hx := bits_length_le_self x.length
  have he' : ∀ v, (e v).bits.length ≤ polyBound c d x.length + 1 :=
    fun v => bits_length_le_of_le_pow _ _ (he v)
  have hq' := bits_length_le_of_lt_pow q _ hq
  have hp : part.encode.length ≤ 2 := by cases part <;> decide
  have hs : (∑ i : Fin (k + 1), (2 * (e i).bits.length + 1)) ≤
      (k + 1) * (2 * (polyBound c d x.length + 1) + 1) := by
    calc
      _ ≤ ∑ i : Fin (k + 1), (2 * (polyBound c d x.length + 1) + 1) := by
        apply Finset.sum_le_sum
        intro i hi
        have hei := he' i
        omega
      _ = _ := by simp [Nat.mul_comm]
  have hpad := polyBound_padding c d x.length
  have hpos : 1 ≤ polyBound (c + 1) (d + 1) x.length := (by omega : 1 ≤ x.length + 1).trans hpad.1
  rw [coefficient_query_length]
  rw [show polyBound ((3 * (k + 1) + 12 + 2 * (k + 1).bits.length) * (c + 1))
      (d + 1) x.length = (3 * (k + 1) + 12 + 2 * (k + 1).bits.length) *
        polyBound (c + 1) (d + 1) x.length by simp only [polyBound, Nat.mul_assoc]]
  have hks := Nat.mul_le_mul_left (k + 1)
    (show 2 * (polyBound c d x.length + 1) + 1 ≤
      3 * polyBound (c + 1) (d + 1) x.length by omega)
  have hsb := Nat.le_mul_of_pos_right (k + 1).bits.length hpos
  nlinarith

lemma trailing_zero_iff_coefficient_bit_queries {k : ℕ}
    (R : Word → MvPolynomial (Fin (k + 1)) ℚ) (rho : CoefficientRepresentation k)
    (hrep : RepresentsPolynomialFamily R rho) (x : Word) (D U : ℕ)
    (hp : R x ≠ 0) (hD : (R x).totalDegree ≤ D)
    (hU : ∀ e, (rho x e).1.natAbs.bits.length ≤ U) :
    TrailingZeroLanguage R x ↔
      ∃ a : Fin (k + 1) →₀ ℕ, (∀ v, a v ≤ D) ∧
        (∃ q < U, CoefficientBitLanguage rho (coefficientQuery x a .numerator q)) ∧
        (∀ e : Fin (k + 1) →₀ ℕ, (∀ v, e v ≤ D) →
          List.Lex (· < ·)
            ((List.ofFn (fun i : Fin k => i.castSucc)).map (fun v => e v))
            ((List.ofFn (fun i : Fin k => i.castSucc)).map (fun v => a v)) →
          ¬ ∃ q < U, CoefficientBitLanguage rho (coefficientQuery x e .numerator q)) ∧
        (¬ ∃ q < U, CoefficientBitLanguage rho (coefficientQuery x
          (orderExponent (List.ofFn (fun i : Fin k => i.castSucc)) a) .numerator q)) := by
  have hn : (List.ofFn (fun i : Fin k => i.castSucc)).Nodup :=
    List.nodup_ofFn_ofInjective (Fin.castSucc_injective k)
  change MvPolynomial.eval (fun _ => (0 : ℚ)) (nestedTrailing _ (R x)) = 0 ↔ _
  rw [trailing_zero_iff_bounded_coefficients _ hn (R x) hp D hD]
  have hz : ∀ e, (R x).coeff e = 0 ↔
      ¬ ∃ q < U, CoefficientBitLanguage rho (coefficientQuery x e .numerator q) := by
    intro e
    rw [← coefficient_ne_zero_iff_query R rho hrep x e U (hU e)]
    exact not_not.symm
  simp_rw [hz, coefficient_ne_zero_iff_query R rho hrep x _ U (hU _)]

end APSCounting893.Main
end Component_8

section Component_9

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma decodeNats_code (ns : List ℕ) (rest : Word) :
    decodeNats ns.length (ns.flatMap encodeNat ++ rest) = some (ns, rest) := by
  induction ns with
  | nil => rfl
  | cons n ns ih =>
      simp only [List.length_cons, List.flatMap_cons, List.append_assoc, decodeNats,
        decodeNat_code, Option.bind_eq_bind, Option.bind_some, Option.pure_def, ih]

lemma exponentOfList_ofFn {k : ℕ} (a : Fin (k + 1) →₀ ℕ) :
    exponentOfList k (List.ofFn (fun i => a i)) = a := by
  ext i
  simp only [exponentOfList, Finsupp.onFinset_apply, List.getElem?_ofFn, dif_pos i.isLt, Option.getD_some]

lemma decodeExponent_code {k : ℕ} (a : Fin (k + 1) →₀ ℕ) (rest : Word) :
    decodeExponent k (encodeExponent a ++ rest) = some (a, rest) := by
  have hns := decodeNats_code (List.ofFn (fun i => a i)) rest
  simp only [List.length_ofFn] at hns
  simp only [decodeExponent, encodeExponent, encodeList, List.length_ofFn, List.append_assoc, decodeNat_code,
    Option.bind_eq_bind, Option.bind_some, Option.pure_def, if_pos rfl, ite_true, hns, exponentOfList_ofFn]

lemma decodeExistential_code {k : ℕ} (a : Fin (k + 1) →₀ ℕ) (q : ℕ) (pad : Word) :
    decodeExistential k (encodeExistential a q ++ pad) = some (a, q) := by
  simp only [decodeExistential, encodeExistential, List.append_assoc, decodeExponent_code,
    decodeNat_code, Option.bind_eq_bind, Option.bind_some, Option.pure_def]

lemma decodeUniversal_code {k : ℕ} (e : Fin (k + 1) →₀ ℕ) (qE qF : ℕ) (pad : Word) :
    decodeUniversal k (encodeUniversal e qE qF ++ pad) = some (e, qE, qF) := by
  simp only [decodeUniversal, encodeUniversal, List.append_assoc, decodeExponent_code,
    decodeNat_code, Option.bind_eq_bind, Option.bind_some, Option.pure_def]

lemma baseTrailing_pair {k : ℕ} (rho : CoefficientRepresentation k)
    (x aWord u : Word) :
    BaseTrailingLanguage rho (pairWord (pairWord x aWord) u) =
      (match decodeExistential k aWord with
      | none => False
      | some (a, qA) => CoefficientBitLanguage rho (coefficientQuery x a .numerator qA) ∧
          match decodeUniversal k u with
          | none => True
          | some (e, qE, qF) =>
              (¬ List.Lex (· < ·)
                ((List.ofFn (fun i : Fin k => i.castSucc)).map (fun v => e v))
                ((List.ofFn (fun i : Fin k => i.castSucc)).map (fun v => a v)) ∨
                ¬ CoefficientBitLanguage rho (coefficientQuery x e .numerator qE)) ∧
              ¬ CoefficientBitLanguage rho (coefficientQuery x
                (orderExponent (List.ofFn (fun i : Fin k => i.castSucc)) a) .numerator qF)) := by
  simp only [BaseTrailingLanguage, decodePair_pairWord] <;> rfl

lemma decodeNats_inverse (n : ℕ) (w : Word) (ns : List ℕ) (rest : Word)
    (h : decodeNats n w = some (ns, rest)) : ns.length = n ∧ w = ns.flatMap encodeNat ++ rest := by
  induction n generalizing w ns rest with
  | zero =>
      have heq : ([], w) = (ns, rest) := by simpa [decodeNats] using h
      cases heq
      exact ⟨rfl, rfl⟩
  | succ n ih =>
      cases ha : decodeNat w with
      | none => simp [decodeNats, ha] at h
      | some p =>
          cases hr : decodeNats n p.2 with
          | none => simp [decodeNats, ha, hr] at h
          | some q =>
              have heq : (p.1 :: q.1, q.2) = (ns, rest) := by simpa [decodeNats, ha, hr] using h
              cases heq
              obtain ⟨hlen, hword⟩ := ih p.2 q.1 q.2 hr
              constructor
              · simp [hlen]
              · rw [decodeNat_inverse w p.1 p.2 ha, hword]
                simp [List.append_assoc]

lemma ofFn_exponentOfList (k : ℕ) (ns : List ℕ) (h : ns.length = k + 1) :
    List.ofFn (fun i => exponentOfList k ns i) = ns := by
  apply List.ext_getElem
  · simpa only [List.length_ofFn] using h.symm
  · intro i hi hi'
    simp only [List.getElem_ofFn, exponentOfList, Finsupp.onFinset_apply]
    rw [List.getElem?_eq_getElem hi']
    rfl

lemma decodeExponent_inverse (k : ℕ) (w : Word) (a : Fin (k + 1) →₀ ℕ) (rest : Word)
    (h : decodeExponent k w = some (a, rest)) : w = encodeExponent a ++ rest := by
  cases hn : decodeNat w with
  | none => simp [decodeExponent, hn] at h
  | some p =>
      by_cases hp : p.1 = k + 1
      · cases hns : decodeNats (k + 1) p.2 with
        | none => simp [decodeExponent, hn, hp, hns] at h
        | some q =>
            have heq : (exponentOfList k q.1, q.2) = (a, rest) := by
              simpa [decodeExponent, hn, hp, hns] using h
            cases heq
            obtain ⟨hlen, hword⟩ := decodeNats_inverse (k + 1) p.2 q.1 q.2 hns
            rw [decodeNat_inverse w p.1 p.2 hn, hword]
            simp only [encodeExponent, encodeList, ofFn_exponentOfList k q.1 hlen,
              hlen, hp, List.append_assoc]
      · simp [decodeExponent, hn, hp] at h

end APSCounting893.Main
end Component_9

section Component_10

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

def trailingQueryConstant (k c : ℕ) : ℕ :=
  (3 * (k + 1) + 12 + 2 * (k + 1).bits.length) * (c + 1)

def trailingWitnessConstant (k c : ℕ) : ℕ := 4 * trailingQueryConstant k c

lemma trailingWitnessConstant_pos (k c : ℕ) : 0 < trailingWitnessConstant k c := by
  unfold trailingWitnessConstant trailingQueryConstant
  positivity

lemma polyBound_mono_input (c d n m : ℕ) (h : n ≤ m) : polyBound c d n ≤ polyBound c d m :=
  Nat.mul_le_mul_left c (Nat.pow_le_pow_left (by omega) d)

lemma trailingQueryBound_padding (k c d n : ℕ) :
    polyBound c d n + 1 ≤ polyBound (trailingQueryConstant k c) (d + 1) n := by
  apply (polyBound_padding c d n).2.trans
  unfold polyBound trailingQueryConstant
  exact Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_left _ (by omega))

lemma encodeExistential_length_le_query {k : ℕ} (x : Word) (a : Fin (k + 1) →₀ ℕ) (q : ℕ) :
    (encodeExistential a q).length ≤ (coefficientQuery x a .numerator q).length := by
  simp only [encodeExistential, encodeExponent, coefficientQuery, List.length_append]
  omega

lemma encodeExistential_length_bound {k : ℕ} (x : Word) (a : Fin (k + 1) →₀ ℕ) (q c d : ℕ)
    (ha : ∀ v, a v ≤ 2 ^ polyBound c d x.length)
    (hq : q < 2 ^ (polyBound c d x.length + 1)) :
    (encodeExistential a q).length ≤ polyBound (trailingWitnessConstant k c) (d + 1) x.length := by
  have hbound := coefficient_query_polynomial_length x a .numerator q c d ha hq
  have hsmall := (encodeExistential_length_le_query x a q).trans hbound
  change (encodeExistential a q).length ≤ polyBound (trailingQueryConstant k c) (d + 1) x.length at hsmall
  calc
    _ ≤ polyBound (trailingQueryConstant k c) (d + 1) x.length := hsmall
    _ ≤ 4 * polyBound (trailingQueryConstant k c) (d + 1) x.length := by omega
    _ = _ := by simp only [trailingWitnessConstant, polyBound, Nat.mul_assoc]


lemma encodeUniversal_length_bound {k : ℕ} (x : Word) (e : Fin (k + 1) →₀ ℕ) (qE qF c d : ℕ)
    (he : ∀ v, e v ≤ 2 ^ polyBound c d x.length)
    (hE : qE < 2 ^ (polyBound c d x.length + 1))
    (hF : qF < 2 ^ (polyBound c d x.length + 1)) :
    (encodeUniversal e qE qF).length ≤ polyBound (trailingWitnessConstant k c) (d + 1) x.length := by
  have hbound := coefficient_query_polynomial_length x e .numerator qE c d he hE
  have hsmall := (encodeExistential_length_le_query x e qE).trans hbound
  have hpad := trailingQueryBound_padding k c d x.length
  have hbits := bits_length_le_of_lt_pow qF _ hF
  have hlen : (encodeNat qF).length = 2 * qF.bits.length + 1 := by simp [encodeNat]; omega
  have hcode : (encodeUniversal e qE qF).length = (encodeExistential e qE).length + (encodeNat qF).length := by
    simp only [encodeUniversal, encodeExistential, List.length_append]
  rw [hcode, hlen]
  change (encodeExistential e qE).length ≤ polyBound (trailingQueryConstant k c) (d + 1) x.length at hsmall
  rw [show polyBound (trailingWitnessConstant k c) (d + 1) x.length =
      4 * polyBound (trailingQueryConstant k c) (d + 1) x.length by
        simp only [trailingWitnessConstant, polyBound, Nat.mul_assoc]]
  nlinarith

end APSCounting893.Main
end Component_10

section Component_11
set_option autoImplicit false
namespace APSCounting893.Main
lemma bounded_exists_inOraclePP (A : Language) (a b : ℕ) (ha : 0 < a) :
    InOraclePP A (fun x => ∃ y : Word, y.length = polyBound a b x.length ∧ A (pairWord x y)) :=
  (bounded_quantification_oracle_pp A a b ha).1
lemma bounded_forall_inOraclePP (A : Language) (a b : ℕ) (ha : 0 < a) :
    InOraclePP A (fun x => ∀ y : Word, y.length = polyBound a b x.length → A (pairWord x y)) :=
  (bounded_quantification_oracle_pp A a b ha).2
lemma AtCHLevel.bounded_exists {A : Language} {j : ℕ} (hA : AtCHLevel j A)
    (a b : ℕ) (ha : 0 < a) : AtCHLevel (j + 1)
      (fun x => ∃ y : Word, y.length = polyBound a b x.length ∧ A (pairWord x y)) :=
  ⟨A, hA, bounded_exists_inOraclePP A a b ha⟩

lemma AtCHLevel.bounded_forall {A : Language} {j : ℕ} (hA : AtCHLevel j A)
    (a b : ℕ) (ha : 0 < a) : AtCHLevel (j + 1)
      (fun x => ∀ y : Word, y.length = polyBound a b x.length → A (pairWord x y)) :=
  ⟨A, hA, bounded_forall_inOraclePP A a b ha⟩


end APSCounting893.Main
end Component_11

section Component_12

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

noncomputable def QuantifiedTrailingLanguage {k : ℕ} (rho : CoefficientRepresentation k) (c d : ℕ) : Language :=
  fun x => ∃ aWord : Word,
    aWord.length = polyBound (trailingWitnessConstant k c) (d + 1) x.length ∧
    ∀ u : Word, u.length = polyBound (trailingWitnessConstant k c) (d + 1) (pairWord x aWord).length →
      BaseTrailingLanguage rho (pairWord (pairWord x aWord) u)

lemma trailing_zero_iff_quantified {k : ℕ}
    (R : Word → MvPolynomial (Fin (k + 1)) ℚ) (rho : CoefficientRepresentation k)
    (hrep : RepresentsPolynomialFamily R rho) (x : Word) (c d : ℕ)
    (hp : R x ≠ 0) (hdeg : (R x).totalDegree ≤ 2 ^ polyBound c d x.length)
    (hnum : ∀ e, (rho x e).1.natAbs.bits.length ≤ 2 ^ polyBound c d x.length) :
    TrailingZeroLanguage R x ↔ QuantifiedTrailingLanguage rho c d x := by
  classical
  let U := 2 ^ (polyBound c d x.length + 1)
  have hUpos : 0 < U := by dsimp [U]; positivity
  have hU : ∀ e, (rho x e).1.natAbs.bits.length ≤ U := by
    intro e
    exact (hnum e).trans (Nat.pow_le_pow_right (by decide) (Nat.le_succ _))
  have hn : (List.ofFn (fun i : Fin k => i.castSucc)).Nodup :=
    List.nodup_ofFn_ofInjective (Fin.castSucc_injective k)
  have hcoeff := trailing_zero_iff_bounded_coefficients
    (List.ofFn (fun i : Fin k => i.castSucc)) hn (R x) hp (2 ^ polyBound c d x.length) hdeg
  constructor
  · intro hz
    obtain ⟨a, haD, hane, hmin, hfinal⟩ := hcoeff.mp hz
    obtain ⟨qA, hqA, hbitA⟩ := (coefficient_ne_zero_iff_query R rho hrep x a U (hU a)).mp hane
    let W := polyBound (trailingWitnessConstant k c) (d + 1) x.length
    have hlenA : (encodeExistential a qA).length ≤ W :=
      encodeExistential_length_bound x a qA c d haD hqA
    let aw := encodeExistential a qA ++ List.replicate (W - (encodeExistential a qA).length) false
    have hlenaw : aw.length = W := by simp only [aw, List.length_append, List.length_replicate]; omega
    refine ⟨aw, hlenaw, ?_⟩
    intro u hu
    have hdecodeA : decodeExistential k aw = some (a, qA) := decodeExistential_code a qA _
    rw [baseTrailing_pair, hdecodeA]
    refine ⟨hbitA, ?_⟩
    cases hdecodeU : decodeUniversal k u with
    | none => trivial
    | some z =>
        rcases z with ⟨e, qE, qF⟩
        constructor
        · by_cases hlex : List.Lex (· < ·)
              ((List.ofFn (fun i : Fin k => i.castSucc)).map (fun v => e v))
              ((List.ofFn (fun i : Fin k => i.castSucc)).map (fun v => a v))
          · right
            intro hbitE
            have henz := bit_query_implies_coefficient_ne_zero R rho hrep x e qE hbitE
            have heD : ∀ v, e v ≤ 2 ^ polyBound c d x.length :=
              fun v => (support_exponents_le_totalDegree (R x) e (mem_support_iff.mpr henz) v).trans hdeg
            exact henz (hmin e heD hlex)
          · exact Or.inl hlex
        · exact coefficient_zero_implies_no_bit_query R rho hrep x _ hfinal qF
  · rintro ⟨aw, hlenaw, hforall⟩
    let UW := polyBound (trailingWitnessConstant k c) (d + 1) (pairWord x aw).length
    have hb0 := hforall (List.replicate UW false) (by simp [UW])
    rw [baseTrailing_pair] at hb0
    cases hdecodeA : decodeExistential k aw with
    | none => simp [hdecodeA] at hb0
    | some z =>
        rcases z with ⟨a, qA⟩
        rw [hdecodeA] at hb0
        have hbitA := hb0.1
        have hane := bit_query_implies_coefficient_ne_zero R rho hrep x a qA hbitA
        have haD : ∀ v, a v ≤ 2 ^ polyBound c d x.length :=
          fun v => (support_exponents_le_totalDegree (R x) a (mem_support_iff.mpr hane) v).trans hdeg
        have hprobe : ∀ (e : Fin (k + 1) →₀ ℕ) (qE qF : ℕ),
            (∀ v, e v ≤ 2 ^ polyBound c d x.length) → qE < U → qF < U →
            (¬ List.Lex (· < ·)
              ((List.ofFn (fun i : Fin k => i.castSucc)).map (fun v => e v))
              ((List.ofFn (fun i : Fin k => i.castSucc)).map (fun v => a v)) ∨
              ¬ CoefficientBitLanguage rho (coefficientQuery x e .numerator qE)) ∧
            ¬ CoefficientBitLanguage rho (coefficientQuery x
              (orderExponent (List.ofFn (fun i : Fin k => i.castSucc)) a) .numerator qF) := by
          intro e qE qF heD hqE hqF
          have hlenraw := encodeUniversal_length_bound x e qE qF c d heD hqE hqF
          have hxlen : x.length ≤ (pairWord x aw).length := by rw [pairWord_length]; omega
          have hlenraw' : (encodeUniversal e qE qF).length ≤ UW :=
            hlenraw.trans (polyBound_mono_input _ _ _ _ hxlen)
          let u := encodeUniversal e qE qF ++ List.replicate (UW - (encodeUniversal e qE qF).length) false
          have hlenU : u.length = UW := by simp only [u, List.length_append, List.length_replicate]; omega
          have hb := hforall u hlenU
          rw [baseTrailing_pair, hdecodeA] at hb
          have hdec : decodeUniversal k u = some (e, qE, qF) := decodeUniversal_code e qE qF _
          rw [hdec] at hb
          exact hb.2
        apply hcoeff.mpr
        refine ⟨a, haD, hane, ?_, ?_⟩
        · intro e heD hlex
          by_contra henz
          obtain ⟨qE, hqE, hbitE⟩ := (coefficient_ne_zero_iff_query R rho hrep x e U (hU e)).mp henz
          have hpr := (hprobe e qE 0 heD hqE hUpos).1
          rcases hpr with hnlex | hnbit
          · exact hnlex hlex
          · exact hnbit hbitE
        · by_contra hnonzero
          obtain ⟨qF, hqF, hbitF⟩ :=
            (coefficient_ne_zero_iff_query R rho hrep x _ U (hU _)).mp hnonzero
          exact (hprobe 0 0 qF (by simp) hUpos hqF).2 hbitF

end APSCounting893.Main
end Component_12

section Component_13

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
end Component_13

section Component_14

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
end Component_14

section Component_15

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma trailing_test_ch_of_base_oracleP {k : ℕ}
    (R : Word → MvPolynomial (Fin (k + 1)) ℚ) (rho : CoefficientRepresentation k)
    (hnonzero : ∀ x, R x ≠ 0) (hrep : RepresentsPolynomialFamily R rho)
    (hbound : SinglyExponentialFamily R rho)
    (hbits : InCountingHierarchy (CoefficientBitLanguage rho))
    (hbase : InOracleP (CoefficientBitLanguage rho) (BaseTrailingLanguage rho)) :
    InCountingHierarchy (TrailingZeroLanguage R) := by
  obtain ⟨c, d, hbounds⟩ := hbound
  obtain ⟨j, hlevel⟩ := hbits
  have hBase : AtCHLevel (j + 1) (BaseTrailingLanguage rho) := ⟨_, hlevel, hbase.inOraclePP⟩
  have hForall := hBase.bounded_forall (trailingWitnessConstant k c) (d + 1) (trailingWitnessConstant_pos k c)
  have hExists := hForall.bounded_exists (trailingWitnessConstant k c) (d + 1) (trailingWitnessConstant_pos k c)
  have hQ : AtCHLevel (j + 1 + 1 + 1) (QuantifiedTrailingLanguage rho c d) := hExists
  have hEq : TrailingZeroLanguage R = QuantifiedTrailingLanguage rho c d := by
    funext x
    apply propext
    exact trailing_zero_iff_quantified R rho hrep x c d (hnonzero x) (hbounds x).1
      (fun e => (hbounds x).2 e |>.1)
  rw [hEq]
  exact ⟨_, hQ⟩

end APSCounting893.Main
end Component_15


set_option autoImplicit false

theorem solution (k : ℕ) (R : APSCounting893.Main.Word → MvPolynomial (Fin (k + 1)) ℚ)
    (rho : APSCounting893.Main.CoefficientRepresentation k) (hnonzero : ∀ x, R x ≠ 0)
    (hrep : APSCounting893.Main.RepresentsPolynomialFamily R rho)
    (hbound : APSCounting893.Main.SinglyExponentialFamily R rho)
    (hbits : APSCounting893.Main.InCountingHierarchy (APSCounting893.Main.CoefficientBitLanguage rho)) :
    APSCounting893.Main.InCountingHierarchy (APSCounting893.Main.TrailingZeroLanguage R) := by
  exact APSCounting893.Main.trailing_test_ch_of_base_oracleP R rho hnonzero hrep hbound hbits
    (APSCounting893.Main.trailing_verifier_in_oracleP k rho)
