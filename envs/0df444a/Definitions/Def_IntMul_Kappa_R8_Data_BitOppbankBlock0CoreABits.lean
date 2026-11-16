-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreABits
-- name    : IntMul_Kappa_R8_Data_BitOppbankBlock0CoreABits
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T17:05:17.679833+00:00
-- url     : https://prove2.me/theorems/f05d7a3c-b69e-4b2f-833b-16ef9e2970c8
-- title:
--   Block-0 `srcS_vals` Nodup and injectivity
-- statement:
--   # Block-0 srcS_vals Nodup
--
--   Bit-mask, popcount, Nodup and injectivity lemmas for `srcS_vals`. Depends on the published `Block0CoreAData` pack. Prefix / block-0 helper only; not a full-word W1F certificate.
-- source:
--   IntMul Kappa R8 Bit Oppbank FormalOK: CoreA bits split. Prefix / block-0 pack only; not a full-word W1F certificate.

import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankGenF
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankLab1
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankQHNetRecR
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreAData
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.ByCases
import Mathlib.Tactic.Ext

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
Block-0 `srcS_vals` bit-mask / Nodup / injectivity lemmas.
Prefix / block-0 helper only; not a full-word W1F certificate.
-/

open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.Gen (genF genStepF mvF)
open IntMul.Kappa.R8.Bit.Oppbank.Lab (ValidOn MovesV)
open IntMul.Kappa.R8.Bit.Oppbank.Pnd (nestOK argRel isND)
open IntMul.Kappa.R8.Bit.Oppbank.QHNetRecR

theorem srcS_vals_len : srcS_vals.length = 1771 := rfl
theorem srcS_mask_fold : srcS_vals.foldl orBit 0 = srcS_mask := rfl
theorem srcS_mask_pop : popcnt srcS_mask = 1771 := rfl
theorem srcS_map_eq : (List.range v).map srcS = srcS_vals := rfl

theorem mem_bitFinset {n k : ℕ} : k ∈ bitFinset n ↔ n.testBit k = true := by
  constructor
  · intro h
    simp only [bitFinset, Finset.mem_filter] at h
    exact h.2
  · intro h
    simp only [bitFinset, Finset.mem_filter, Finset.mem_range]
    refine ⟨?_, h⟩
    have hx : 2 ^ k ≤ n := Nat.ge_two_pow_of_testBit h
    have hk : k ≤ 2 ^ k := Nat.le_of_lt Nat.lt_two_pow_self
    exact Nat.lt_succ_of_le (le_trans hk hx)

theorem testBit_one_shift (q k : ℕ) :
    ((1 : ℕ) <<< q).testBit k = true ↔ k = q := by
  have h1 : (1 : ℕ) <<< q = 2 ^ q := by
    rw [Nat.shiftLeft_eq, Nat.one_mul]
  rw [h1, Nat.testBit_two_pow]
  simp [eq_comm]

theorem testBit_orBit (acc q k : ℕ) :
    (orBit acc q).testBit k = true ↔ acc.testBit k = true ∨ k = q := by
  simp only [orBit, Nat.testBit_or, Bool.or_eq_true, testBit_one_shift]

theorem testBit_foldl (acc : ℕ) (L : List ℕ) (k : ℕ) :
    (L.foldl orBit acc).testBit k = true ↔ acc.testBit k = true ∨ k ∈ L := by
  induction L generalizing acc with
  | nil =>
    simp
  | cons q L ih =>
    simp only [List.foldl_cons, List.mem_cons]
    rw [ih]
    constructor
    · intro h
      rcases h with h | h
      · rcases (testBit_orBit acc q k).1 h with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    · intro h
      rcases h with h | h | h
      · exact Or.inl ((testBit_orBit acc q k).2 (Or.inl h))
      · exact Or.inl ((testBit_orBit acc q k).2 (Or.inr h))
      · exact Or.inr h

theorem testBit_fold_zero (L : List ℕ) (k : ℕ) :
    (L.foldl orBit 0).testBit k = true ↔ k ∈ L := by
  simpa [Nat.zero_testBit] using testBit_foldl 0 L k

theorem bitFinset_fold (L : List ℕ) :
    bitFinset (L.foldl orBit 0) = L.toFinset := by
  ext k
  simp [mem_bitFinset, testBit_fold_zero, List.mem_toFinset]


theorem and_one_eq_testBit (n : ℕ) :
    n &&& 1 = if n.testBit 0 = true then 1 else 0 := by
  rw [Nat.and_comm, Nat.one_and_eq_mod_two]
  have hbit : n.testBit 0 = decide (n % 2 = 1) := by
    simp [Nat.testBit_zero]
  rw [hbit]
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · simp [h]
  · simp [h]

theorem bitFinset_decomp (n : ℕ) :
    bitFinset n =
      (if n.testBit 0 = true then ({0} : Finset ℕ) else ∅) ∪
        (bitFinset (n >>> 1)).map ⟨Nat.succ, Nat.succ_injective⟩ := by
  ext k
  constructor
  · intro hk
    have hbit : n.testBit k = true := mem_bitFinset.1 hk
    cases k with
    | zero =>
      simp [hbit]
    | succ k =>
      refine Finset.mem_union.2 (Or.inr ?_)
      refine Finset.mem_map.2 ⟨k, ?_, rfl⟩
      have hbit' : n.testBit (1 + k) = true := by
        rwa [Nat.add_comm]
      exact mem_bitFinset.2 (by simpa [Nat.testBit_shiftRight] using hbit')
  · intro hk
    simp only [Finset.mem_union] at hk
    rcases hk with hk | hk
    · split_ifs at hk with ht
      · simp only [Finset.mem_singleton] at hk
        subst k
        exact mem_bitFinset.2 ht
      · simp at hk
    · rcases Finset.mem_map.1 hk with ⟨k', hk', rfl⟩
      have hbit' : (n >>> 1).testBit k' = true := mem_bitFinset.1 hk'
      have : n.testBit (1 + k') = true := by
        simpa [Nat.testBit_shiftRight] using hbit'
      exact mem_bitFinset.2 (by rwa [Nat.add_comm] at this)

theorem disjoint_bitFinset_decomp (n : ℕ) :
    Disjoint (if n.testBit 0 = true then ({0} : Finset ℕ) else ∅)
      ((bitFinset (n >>> 1)).map ⟨Nat.succ, Nat.succ_injective⟩) := by
  refine Finset.disjoint_left.2 ?_
  intro a ha hb
  rcases Finset.mem_map.1 hb with ⟨k, -, hka⟩
  have hsucc : a = Nat.succ k := by
    simpa [Function.Embedding.coeFn_mk] using hka.symm
  have ha0 : a = 0 := by
    split_ifs at ha with _ht
    · exact Finset.mem_singleton.1 ha
    · exact False.elim (by simp at ha)
  exact Nat.succ_ne_zero k (hsucc.symm.trans ha0)

theorem pop1_zero : pop1 0 = 0 := by
  simp [pop1]

theorem bitFinset_zero : bitFinset 0 = ∅ := by
  ext k
  simp [mem_bitFinset, Nat.zero_testBit]

theorem pop1_pos {n : ℕ} (h : n ≠ 0) : pop1 n = (n &&& 1) + pop1 (n >>> 1) := by
  rw [pop1, dif_neg h]

theorem pop1_eq_card (n : ℕ) : pop1 n = (bitFinset n).card := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases h : n = 0
    · subst n
      rw [pop1_zero, bitFinset_zero, Finset.card_empty]
    · have hlt : n >>> 1 < n := by
        have hn : 0 < n := Nat.pos_of_ne_zero h
        simpa [Nat.shiftRight_eq_div_pow] using
          Nat.div_lt_self hn (by decide : (1 : ℕ) < 2)
      rw [pop1_pos h, ih (n >>> 1) hlt, bitFinset_decomp n,
        Finset.card_union_of_disjoint (disjoint_bitFinset_decomp n),
        Finset.card_map, and_one_eq_testBit]
      split_ifs with _ht
      · rw [Finset.card_singleton]
      · rw [Finset.card_empty, Nat.zero_add]


theorem bitFinset_or (a b : ℕ) :
    bitFinset (a ||| b) = bitFinset a ∪ bitFinset b := by
  ext k
  simp only [mem_bitFinset, Nat.testBit_or, Bool.or_eq_true, Finset.mem_union]

theorem pop1_or_disjoint (a b : ℕ)
    (h : ∀ i, a.testBit i = true → b.testBit i = true → False) :
    pop1 (a ||| b) = pop1 a + pop1 b := by
  rw [pop1_eq_card, pop1_eq_card, pop1_eq_card, bitFinset_or,
    Finset.card_union_of_disjoint]
  refine Finset.disjoint_left.2 ?_
  intro x hx hy
  exact h x (mem_bitFinset.1 hx) (mem_bitFinset.1 hy)

theorem decompose_mod_shift (n k : ℕ) :
    (n % 2 ^ k) ||| ((n >>> k) <<< k) = n := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_or, Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft]
  by_cases hi : i < k
  · simp [hi]
  · have hik : k ≤ i := Nat.le_of_not_gt hi
    have hadd : k + (i - k) = i := Nat.add_sub_cancel' hik
    have : ((n >>> k).testBit (i - k)) = n.testBit i := by
      rw [Nat.testBit_shiftRight, hadd]
    simp [hi, hik, this]

theorem bitFinset_shiftLeft (n k : ℕ) :
    bitFinset (n <<< k) =
      (bitFinset n).map ⟨fun i => i + k, add_left_injective k⟩ := by
  ext j
  constructor
  · intro hj
    have hshift : (n <<< k).testBit j = true := mem_bitFinset.1 hj
    have hbits : (decide (k ≤ j) && n.testBit (j - k)) = true := by
      simpa [Nat.testBit_shiftLeft] using hshift
    have hpair : decide (k ≤ j) = true ∧ n.testBit (j - k) = true := by
      simpa [Bool.and_eq_true] using hbits
    have hkj : k ≤ j := of_decide_eq_true hpair.1
    refine Finset.mem_map.2 ⟨j - k, mem_bitFinset.2 hpair.2, ?_⟩
    exact Nat.sub_add_cancel hkj
  · intro hj
    rcases Finset.mem_map.1 hj with ⟨i, hi, rfl⟩
    have hbit : n.testBit i = true := mem_bitFinset.1 hi
    have : (n <<< k).testBit (i + k) = true := by
      simp [Nat.testBit_shiftLeft, Nat.le_add_left, Nat.add_sub_cancel_left, hbit]
    exact mem_bitFinset.2 this

theorem pop1_shiftLeft (n k : ℕ) : pop1 (n <<< k) = pop1 n := by
  rw [pop1_eq_card, pop1_eq_card, bitFinset_shiftLeft, Finset.card_map]

theorem pop1_add_shift (n k : ℕ) :
    pop1 n = pop1 (n % 2 ^ k) + pop1 (n >>> k) := by
  have hdec : n = (n % 2 ^ k) ||| ((n >>> k) <<< k) :=
    (decompose_mod_shift n k).symm
  conv_lhs => rw [hdec]
  rw [pop1_or_disjoint]
  · rw [pop1_shiftLeft]
  · intro i hlo hhi
    have hilt : i < k := by
      have hmod : (n % 2 ^ k).testBit i = (decide (i < k) && n.testBit i) :=
        Nat.testBit_mod_two_pow n k i
      have hand : (decide (i < k) && n.testBit i) = true := by
        rwa [← hmod]
      have hpair : decide (i < k) = true ∧ n.testBit i = true := by
        simpa [Bool.and_eq_true] using hand
      exact of_decide_eq_true hpair.1
    have hkle : k ≤ i := by
      have hshift : (decide (k ≤ i) && (n >>> k).testBit (i - k)) = true := by
        simpa [Nat.testBit_shiftLeft] using hhi
      have hpair : decide (k ≤ i) = true ∧ (n >>> k).testBit (i - k) = true := by
        simpa [Bool.and_eq_true] using hshift
      exact of_decide_eq_true hpair.1
    exact (Nat.not_le_of_gt hilt) hkle


theorem pop1_lt_16 (n : ℕ) (h : n < 16) : pop1 n = pop4 n := by
  interval_cases n <;> simp [pop1, pop4]

theorem pop4_eq_low (n : ℕ) : pop4 n = pop4 (n &&& 15) := by
  unfold pop4
  have h : (n &&& 15) &&& 15 = n &&& 15 := by
    rw [Nat.and_assoc, show ((15 : ℕ) &&& 15) = 15 from rfl]
  rw [h]

theorem pop4_eq_pop1_mod16 (n : ℕ) : pop4 n = pop1 (n % 16) := by
  have h15 : (15 : ℕ) = 2 ^ 4 - 1 := rfl
  have hand : n &&& 15 = n % 16 := by
    rw [h15, Nat.and_two_pow_sub_one_eq_mod]
  have hlt : n &&& 15 < 16 := by
    have : (15 : ℕ) < 2 ^ 4 := by decide
    exact Nat.and_lt_two_pow n this
  rw [pop4_eq_low, hand, pop1_lt_16 _ (by rwa [hand] at hlt)]

theorem mod_pow_mod (n a b : ℕ) (h : b ≤ a) : n % 2 ^ a % 2 ^ b = n % 2 ^ b := by
  have : 2 ^ b ∣ 2 ^ a := Nat.pow_dvd_pow (2 : ℕ) h
  exact Nat.mod_mod_of_dvd n this

theorem shiftRight_mod_pow (n k m : ℕ) :
    (n % 2 ^ (k + m)) >>> k = (n >>> k) % 2 ^ m := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_shiftRight, Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow,
    Nat.testBit_shiftRight]
  simp [Nat.add_lt_add_iff_left]

theorem pop16_eq_pop1_mod (n : ℕ) : pop16 n = pop1 (n % 2 ^ 16) := by
  have peel4 (x : ℕ) : pop1 x = pop1 (x % 16) + pop1 (x >>> 4) := by
    change pop1 x = pop1 (x % 2 ^ 4) + pop1 (x >>> 4)
    exact pop1_add_shift x 4
  have hsr : ∀ (x a b : ℕ), (x >>> a) >>> b = x >>> (a + b) := by
    intro x a b
    simp [Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul, Nat.pow_add]
  have h0 := peel4 (n % 2 ^ 16)
  have h1 := peel4 ((n % 2 ^ 16) >>> 4)
  have h2 := peel4 (((n % 2 ^ 16) >>> 4) >>> 4)
  have h3 := peel4 ((((n % 2 ^ 16) >>> 4) >>> 4) >>> 4)
  have htail' : (((((n % 2 ^ 16) >>> 4) >>> 4) >>> 4) >>> 4) = 0 := by
    rw [hsr, hsr, hsr]
    change (n % 2 ^ 16) >>> 16 = 0
    have : n % 2 ^ 16 < 2 ^ 16 := Nat.mod_lt _ (Nat.two_pow_pos _)
    simp [Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt this]
  have r0 : (n % 2 ^ 16) % 16 = n % 16 := by
    change (n % 2 ^ 16) % (2 ^ 4) = n % (2 ^ 4)
    exact mod_pow_mod n 16 4 (by decide)
  have r1 : ((n % 2 ^ 16) >>> 4) % 16 = (n >>> 4) % 16 := by
    have hsh : (n % 2 ^ 16) >>> 4 = (n >>> 4) % 2 ^ 12 := by
      change (n % 2 ^ (4 + 12)) >>> 4 = (n >>> 4) % 2 ^ 12
      exact shiftRight_mod_pow n 4 12
    change ((n % 2 ^ 16) >>> 4) % (2 ^ 4) = (n >>> 4) % (2 ^ 4)
    rw [hsh]
    exact mod_pow_mod (n >>> 4) 12 4 (by decide)
  have r2 : (((n % 2 ^ 16) >>> 4) >>> 4) % 16 = (n >>> 8) % 16 := by
    have hx : ((n % 2 ^ 16) >>> 4) >>> 4 = (n % 2 ^ 16) >>> 8 := by
      rw [hsr]
    have hsh : (n % 2 ^ 16) >>> 8 = (n >>> 8) % 2 ^ 8 := by
      change (n % 2 ^ (8 + 8)) >>> 8 = (n >>> 8) % 2 ^ 8
      exact shiftRight_mod_pow n 8 8
    change (((n % 2 ^ 16) >>> 4) >>> 4) % (2 ^ 4) = (n >>> 8) % (2 ^ 4)
    rw [hx, hsh]
    exact mod_pow_mod (n >>> 8) 8 4 (by decide)
  have r3 : ((((n % 2 ^ 16) >>> 4) >>> 4) >>> 4) % 16 = (n >>> 12) % 16 := by
    have hx : (((n % 2 ^ 16) >>> 4) >>> 4) >>> 4 = (n % 2 ^ 16) >>> 12 := by
      rw [hsr, hsr]
    have hsh : (n % 2 ^ 16) >>> 12 = (n >>> 12) % 2 ^ 4 := by
      change (n % 2 ^ (12 + 4)) >>> 12 = (n >>> 12) % 2 ^ 4
      exact shiftRight_mod_pow n 12 4
    change ((((n % 2 ^ 16) >>> 4) >>> 4) >>> 4) % (2 ^ 4) = (n >>> 12) % (2 ^ 4)
    rw [hx, hsh]
    exact Nat.mod_mod _ _
  rw [pop16, pop4_eq_pop1_mod16, pop4_eq_pop1_mod16, pop4_eq_pop1_mod16,
    pop4_eq_pop1_mod16, h0, r0, h1, r1, h2, r2, h3, r3, htail', pop1_zero]
  ac_rfl


theorem pop1_eq_popcntF (fuel n : ℕ) (h : n < 2 ^ (16 * fuel)) :
    pop1 n = popcntF fuel n := by
  induction fuel generalizing n with
  | zero =>
    have hn : n = 0 := Nat.lt_one_iff.mp (by simpa using h)
    rw [hn, pop1_zero]
    simp [popcntF]
  | succ fuel ih =>
    unfold popcntF
    by_cases hn : n = 0
    · rw [hn, pop1_zero]
      simp
    · have hsplit : pop1 n = pop16 n + pop1 (n >>> 16) := by
        have := pop1_add_shift n 16
        rwa [pop16_eq_pop1_mod]
      have hlt : n >>> 16 < 2 ^ (16 * fuel) := by
        have hpow : 16 * fuel.succ = 16 * fuel + 16 := Nat.mul_succ _ _
        have hnlt : n < 2 ^ (16 * fuel + 16) := by
          rwa [hpow] at h
        have hpa : 2 ^ (16 * fuel + 16) = 2 ^ (16 * fuel) * 2 ^ 16 :=
          Nat.pow_add _ _ _
        have : n < 2 ^ (16 * fuel) * 2 ^ 16 := by rwa [hpa] at hnlt
        have : n / 2 ^ 16 < 2 ^ (16 * fuel) :=
          Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at this)
        simpa [Nat.shiftRight_eq_div_pow] using this
      rw [if_neg hn, hsplit, ih (n >>> 16) hlt]

theorem srcS_vals_all_lt : srcS_vals.all (fun q => decide (q < 11091)) = true := rfl

theorem srcS_vals_lt_11091 : ∀ q ∈ srcS_vals, q < 11091 := by
  intro q hq
  have hall : ∀ q ∈ srcS_vals, decide (q < 11091) = true := by
    simpa [List.all_eq_true] using srcS_vals_all_lt
  exact of_decide_eq_true (hall q hq)

theorem lt_two_pow_of_high_bits {n M : ℕ}
    (h : ∀ k, n.testBit k = true → k < M) : n < 2 ^ M := by
  by_contra hge
  have : 2 ^ M ≤ n := Nat.le_of_not_gt hge
  rcases Nat.exists_ge_and_testBit_of_ge_two_pow this with ⟨i, hi, hbit⟩
  have htrue : n.testBit i = true := by
    simpa using hbit
  have : i < M := h i htrue
  exact (Nat.not_le_of_gt this) hi

theorem srcS_mask_lt : srcS_mask < 2 ^ (16 * 700) := by
  have hbits : ∀ k, srcS_mask.testBit k = true → k < 11091 := by
    intro k hk
    have : (srcS_vals.foldl orBit 0).testBit k = true := by
      rwa [srcS_mask_fold]
    have : k ∈ srcS_vals := (testBit_fold_zero srcS_vals k).1 this
    exact srcS_vals_lt_11091 k this
  have hlt : srcS_mask < 2 ^ 11091 := lt_two_pow_of_high_bits hbits
  have hle : 2 ^ 11091 ≤ 2 ^ (16 * 700) :=
    Nat.pow_le_pow_right (by decide : (0 : ℕ) < 2) (by decide : 11091 ≤ 16 * 700)
  exact Nat.lt_of_lt_of_le hlt hle

theorem srcS_vals_nodup : srcS_vals.Nodup := by
  have hpop1 : pop1 srcS_mask = 1771 := by
    have h := pop1_eq_popcntF 700 srcS_mask srcS_mask_lt
    have hp : popcntF 700 srcS_mask = 1771 := srcS_mask_pop
    exact h.trans hp
  have hcard : srcS_vals.toFinset.card = srcS_vals.length := by
    calc
      srcS_vals.toFinset.card
          = (bitFinset (srcS_vals.foldl orBit 0)).card := by
            rw [bitFinset_fold]
      _ = (bitFinset srcS_mask).card := by rw [srcS_mask_fold]
      _ = pop1 srcS_mask := (pop1_eq_card srcS_mask).symm
      _ = 1771 := hpop1
      _ = srcS_vals.length := srcS_vals_len.symm
  have hm :
      (↑srcS_vals : Multiset ℕ).toFinset.card =
        Multiset.card (↑srcS_vals : Multiset ℕ) := by
    rw [List.toFinset_coe, Multiset.coe_card]
    exact hcard
  have hnd : (↑srcS_vals : Multiset ℕ).Nodup :=
    (Multiset.toFinset_card_eq_card_iff_nodup (m := (↑srcS_vals : Multiset ℕ))).1 hm
  exact Multiset.coe_nodup.1 hnd

theorem srcS_inj {t t' : ℕ} (ht : t < v) (ht' : t' < v)
    (heq : srcS t = srcS t') : t = t' := by
  have nd : srcS_vals.Nodup := srcS_vals_nodup
  have hlen : srcS_vals.length = v := by
    have hv : v = 1771 := rfl
    rw [srcS_vals_len, hv]
  have htL : t < srcS_vals.length := by rw [hlen]; exact ht
  have htL' : t' < srcS_vals.length := by rw [hlen]; exact ht'
  have hget_t : srcS t = srcS_vals[t]'htL := by
    have hidx : t < ((List.range v).map srcS).length := by
      simpa [srcS_map_eq] using htL
    have heql : srcS_vals[t]'htL = ((List.range v).map srcS)[t]'hidx := by
      simp [srcS_map_eq]
    rw [heql, List.getElem_map, List.getElem_range]
  have hget_t' : srcS t' = srcS_vals[t']'htL' := by
    have hidx : t' < ((List.range v).map srcS).length := by
      simpa [srcS_map_eq] using htL'
    have heql : srcS_vals[t']'htL' = ((List.range v).map srcS)[t']'hidx := by
      simp [srcS_map_eq]
    rw [heql, List.getElem_map, List.getElem_range]
  have : srcS_vals.get ⟨t, htL⟩ = srcS_vals.get ⟨t', htL'⟩ := by
    change srcS_vals[t] = srcS_vals[t']
    rw [← hget_t, ← hget_t', heq]
  exact Fin.val_eq_of_eq ((List.Nodup.get_inj_iff nd).1 this)


