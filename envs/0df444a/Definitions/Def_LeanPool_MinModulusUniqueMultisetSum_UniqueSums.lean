-- Prove2me | Definitions.Def_LeanPool_MinModulusUniqueMultisetSum_UniqueSums
-- name    : LeanPool_MinModulusUniqueMultisetSum_UniqueSums
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-20T22:39:44.11027+00:00
-- url     : https://prove2.me/theorems/cf709ab7-8e52-4d92-b03b-b8ceebd995f9
-- title:
--   Unique Sums
-- statement:
--   Definitions and structural lemmas for Unique Sums, from José A. R. Fonollosa; maintained by LeanPool contributors's pinned Minimum modulus for the unique multiset-sum problem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MinModulusUniqueMultisetSum/UniqueSums.lean

module
public import Mathlib.Data.Nat.Log
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Nat.SuccPred
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Ring.RingNF
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace MinModulus
open Finset
def a (i : ℕ) : ℕ := 2 ^ i - 1
def dsum (n : ℕ) (k : ℕ → ℕ) : ℕ := ∑ i ∈ range n, k i
def val (n : ℕ) (k : ℕ → ℕ) : ℕ := ∑ i ∈ range n, k i * 2 ^ i
def Supp (n : ℕ) (k : ℕ → ℕ) : Prop := ∀ i, n ≤ i → k i = 0
def Valid (n N : ℕ) : Prop :=
  ∀ k : ℕ → ℕ, dsum n k = n →
    (∑ i ∈ range n, k i * a i) ≡ (∑ i ∈ range n, a i) [MOD N] →
    ∀ i < n, k i = 1
lemma sum_two_pow (w : ℕ) : ∑ i ∈ range w, 2 ^ i = 2 ^ w - 1 := by
  induction w with
  | zero => rfl
  | succ w ih =>
    have h1 : 1 ≤ 2 ^ w := Nat.one_le_pow _ _ (by norm_num)
    have h2 : 2 ^ (w + 1) = 2 * 2 ^ w := by rw [pow_succ]; ring
    rw [Finset.sum_range_succ, ih]
    omega
lemma sum_a_add_dsum (n : ℕ) (k : ℕ → ℕ) :
    (∑ i ∈ range n, k i * a i) + dsum n k = val n k := by
  unfold dsum val
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : 1 ≤ 2 ^ i := Nat.one_le_pow _ _ (by norm_num)
  have ha : a i + 1 = 2 ^ i := Nat.sub_add_cancel h1
  calc k i * a i + k i = k i * (a i + 1) := by ring
    _ = k i * 2 ^ i := by rw [ha]
lemma not_valid_of_witness_LeanPool_e110dec {n N M : ℕ} (hn : 1 ≤ n)
    (hne : M ≠ 2 ^ n - 1) (hmod : M ≡ (2 ^ n - 1) [MOD N])
    (h : ∃ k, val n k = M ∧ dsum n k = n) : ¬ Valid n N := by
  obtain ⟨k, hv, hd⟩ := h
  intro hval
  -- the all-ones vector
  have hd1 : dsum n (fun _ => 1) = n := by
    unfold dsum
    rw [Finset.sum_const, smul_eq_mul, mul_one, card_range]
  have hv1 : val n (fun _ => 1) = 2 ^ n - 1 := by
    unfold val
    calc (∑ i ∈ range n, 1 * 2 ^ i) = ∑ i ∈ range n, 2 ^ i :=
          Finset.sum_congr rfl fun i _ => one_mul _
      _ = 2 ^ n - 1 := sum_two_pow n
  -- convert `hmod` into the congruence `Valid` expects
  have e1 : (∑ i ∈ range n, k i * a i) + n = M := by
    have h0 := sum_a_add_dsum n k
    rw [hd, hv] at h0
    exact h0
  have e2 : (∑ i ∈ range n, a i) + n = 2 ^ n - 1 := by
    have h0 := sum_a_add_dsum n (fun _ => 1)
    simp only [one_mul] at h0
    rw [hd1, hv1] at h0
    exact h0
  have hcong : (∑ i ∈ range n, k i * a i) ≡ (∑ i ∈ range n, a i) [MOD N] := by
    apply Nat.ModEq.add_right_cancel' n
    rw [e1, e2]
    exact hmod
  -- Valid forces k = all-ones, contradicting val = M ≠ 2^n − 1
  have hone := hval k hd hcong
  have hvk : val n k = 2 ^ n - 1 := by
    unfold val
    calc (∑ i ∈ range n, k i * 2 ^ i) = ∑ i ∈ range n, 2 ^ i :=
          Finset.sum_congr rfl fun i hi => by
            rw [hone i (Finset.mem_range.mp hi), one_mul]
      _ = 2 ^ n - 1 := sum_two_pow n
  omega
lemma supp_mono {e w : ℕ} (h : e ≤ w) {k : ℕ → ℕ} (hs : Supp e k) : Supp w k :=
  fun i hi => hs i (by omega)
lemma val_pad {e w : ℕ} (h : e ≤ w) {k : ℕ → ℕ} (hs : Supp e k) :
    val w k = val e k := by
  unfold val
  refine (Finset.sum_subset (Finset.range_subset_range.mpr h) fun i _ hni => ?_).symm
  have he : e ≤ i := by
    by_contra hc
    exact hni (Finset.mem_range.mpr (by omega))
  rw [hs i he, zero_mul]
lemma dsum_pad {e w : ℕ} (h : e ≤ w) {k : ℕ → ℕ} (hs : Supp e k) :
    dsum w k = dsum e k := by
  unfold dsum
  refine (Finset.sum_subset (Finset.range_subset_range.mpr h) fun i _ hni => ?_).symm
  have he : e ≤ i := by
    by_contra hc
    exact hni (Finset.mem_range.mpr (by omega))
  exact hs i he
lemma update_top_LeanPool_e110dec (w c : ℕ) (k : ℕ → ℕ) (hs : Supp w k) :
    Supp (w + 1) (Function.update k w c) ∧
    val (w + 1) (Function.update k w c) = val w k + c * 2 ^ w ∧
    dsum (w + 1) (Function.update k w c) = dsum w k + c := by
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    rw [Function.update_of_ne (by omega)]
    exact hs i (by omega)
  · unfold val
    rw [Finset.sum_range_succ, Function.update_self]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    have := Finset.mem_range.mp hi
    rw [Function.update_of_ne (by omega)]
  · unfold dsum
    rw [Finset.sum_range_succ, Function.update_self]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    have := Finset.mem_range.mp hi
    rw [Function.update_of_ne (by omega)]
def shift (c : ℕ) (k : ℕ → ℕ) : ℕ → ℕ := fun i => if i = 0 then c else k (i - 1)
lemma shift_supp {w c : ℕ} {k : ℕ → ℕ} (h : Supp w k) :
    Supp (w + 1) (shift c k) := by
  intro i hi
  unfold shift
  rw [if_neg (by omega)]
  exact h (i - 1) (by omega)
lemma shift_val (w c : ℕ) (k : ℕ → ℕ) :
    val (w + 1) (shift c k) = 2 * val w k + c := by
  unfold val
  rw [Finset.sum_range_succ']
  have h0 : shift c k 0 * 2 ^ 0 = c := by unfold shift; simp
  have hstep : ∀ i ∈ range w, shift c k (i + 1) * 2 ^ (i + 1) = 2 * (k i * 2 ^ i) := by
    intro i _
    unfold shift
    rw [if_neg (Nat.succ_ne_zero i), Nat.add_sub_cancel, pow_succ]
    ring
  rw [Finset.sum_congr rfl hstep, h0, ← Finset.mul_sum]
lemma shift_dsum (w c : ℕ) (k : ℕ → ℕ) :
    dsum (w + 1) (shift c k) = dsum w k + c := by
  unfold dsum
  rw [Finset.sum_range_succ']
  have h0 : shift c k 0 = c := by unfold shift; simp
  have hstep : ∀ i ∈ range w, shift c k (i + 1) = k i := by
    intro i _
    unfold shift
    rw [if_neg (Nat.succ_ne_zero i), Nat.add_sub_cancel]
  rw [Finset.sum_congr rfl hstep, h0]
lemma ones_rep_LeanPool_e110dec (w : ℕ) :
    ∃ k, Supp w k ∧ val w k = 2 ^ w - 1 ∧ dsum w k = w := by
  refine ⟨fun i => if i < w then 1 else 0, fun i hi => if_neg (by omega), ?_, ?_⟩
  · unfold val
    calc (∑ i ∈ range w, (if i < w then 1 else 0) * 2 ^ i)
        = ∑ i ∈ range w, 2 ^ i := by
          refine Finset.sum_congr rfl fun i hi => ?_
          rw [if_pos (Finset.mem_range.mp hi), one_mul]
      _ = 2 ^ w - 1 := sum_two_pow w
  · unfold dsum
    calc (∑ i ∈ range w, (if i < w then 1 else 0))
        = ∑ i ∈ range w, 1 := by
          refine Finset.sum_congr rfl fun i hi => ?_
          rw [if_pos (Finset.mem_range.mp hi)]
      _ = w := by rw [Finset.sum_const, smul_eq_mul, mul_one, card_range]
lemma ones_erase_rep_LeanPool_e110dec {w e : ℕ} (he : e < w) :
    ∃ k, Supp w k ∧ val w k = 2 ^ w - 1 - 2 ^ e ∧ dsum w k = w - 1 := by
  have hmem : e ∈ range w := Finset.mem_range.mpr he
  have h1 : 1 ≤ 2 ^ e := Nat.one_le_pow _ _ (by norm_num)
  refine ⟨fun i => if i = e then 0 else if i < w then 1 else 0,
    fun i hi => by
      have hne : ¬ i = e := by omega
      have hlt : ¬ i < w := by omega
      simp [hne, hlt], ?_, ?_⟩
  · simp only [val]
    have hsplit : (∑ i ∈ range w,
          (if i = e then 0 else if i < w then 1 else 0) * 2 ^ i)
        + (∑ i ∈ range w, if i = e then 2 ^ e else 0)
        = ∑ i ∈ range w, 2 ^ i := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i hi => ?_
      by_cases hie : i = e
      · subst hie; simp
      · simp [hie, Finset.mem_range.mp hi]
    have hone : (∑ i ∈ range w, if i = e then 2 ^ e else 0) = 2 ^ e := by
      rw [Finset.sum_ite_eq' (range w) e (fun _ => 2 ^ e), if_pos hmem]
    rw [sum_two_pow] at hsplit
    omega
  · simp only [dsum]
    have hsplit : (∑ i ∈ range w, (if i = e then 0 else if i < w then 1 else 0))
        + (∑ i ∈ range w, if i = e then 1 else 0)
        = ∑ i ∈ range w, 1 := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i hi => ?_
      by_cases hie : i = e
      · subst hie; simp
      · simp [hie, Finset.mem_range.mp hi]
    have hone : (∑ i ∈ range w, if i = e then 1 else 0) = 1 := by
      rw [Finset.sum_ite_eq' (range w) e (fun _ => 1), if_pos hmem]
    have hcard : (∑ i ∈ range w, (1 : ℕ)) = w := by
      rw [Finset.sum_const, smul_eq_mul, mul_one, card_range]
    omega
lemma exists_rep_lt_LeanPool_e110dec : ∀ w x : ℕ, x < 2 ^ w - 1 →
    ∃ k, Supp w k ∧ val w k = x ∧ dsum w k ≤ w - 1 := by
  intro w
  induction w with
  | zero =>
    intro x hx
    rw [pow_zero] at hx
    omega
  | succ w ih =>
    intro x hx
    have h2 : 2 ^ (w + 1) = 2 * 2 ^ w := by rw [pow_succ]; ring
    have h1 : 1 ≤ 2 ^ w := Nat.one_le_pow _ _ (by norm_num)
    rcases Nat.lt_or_ge x (2 ^ w - 1) with h | h
    · obtain ⟨k, hs, hv, hd⟩ := ih x h
      exact ⟨k, supp_mono (by omega) hs,
        by rw [val_pad (by omega) hs, hv],
        by rw [dsum_pad (by omega) hs]; omega⟩
    · rcases Nat.lt_or_ge x (2 ^ w) with h' | h'
      · -- x = 2^w − 1: the all-ones representation, w coins
        have hx' : x = 2 ^ w - 1 := by omega
        obtain ⟨k, hs, hv, hd⟩ := ones_rep_LeanPool_e110dec w
        exact ⟨k, supp_mono (by omega) hs,
          by rw [val_pad (by omega) hs, hv, hx'],
          by rw [dsum_pad (by omega) hs]; omega⟩
      · -- 2^w ≤ x < 2^{w+1} − 1: recurse sharply below a top coin
        have hw1 : 1 ≤ w := by
          rcases Nat.eq_zero_or_pos w with rfl | hw
          · norm_num at hx h'
            omega
          · exact hw
        obtain ⟨k, hs, hv, hd⟩ := ih (x - 2 ^ w) (by omega)
        obtain ⟨us, uv, ud⟩ := update_top_LeanPool_e110dec w 1 k hs
        exact ⟨Function.update k w 1, us, by rw [uv, hv]; omega, by rw [ud]; omega⟩
lemma exists_rep_compl_LeanPool_e110dec : ∀ w s : ℕ, s < 2 ^ w → s ≠ 0 → (¬ ∃ e, s = 2 ^ e) →
    ∃ k, Supp w k ∧ val w k = 2 ^ w - 1 - s ∧ dsum w k ≤ w - 2 := by
  intro w
  induction w with
  | zero =>
    intro s hs h0 _
    rw [pow_zero] at hs
    omega
  | succ w ih =>
    intro s hs h0 hp
    have h2 : 2 ^ (w + 1) = 2 * 2 ^ w := by rw [pow_succ]; ring
    have h1 : 1 ≤ 2 ^ w := Nat.one_le_pow _ _ (by norm_num)
    rcases Nat.even_or_odd s with ⟨q, hq⟩ | ⟨q, hq⟩
    · -- s = 2q even: coin at 0 + shifted witness for q
      have hq0 : q ≠ 0 := by omega
      have hqp : ¬ ∃ e, q = 2 ^ e := by
        rintro ⟨e, rfl⟩
        exact hp ⟨e + 1, by rw [pow_succ]; omega⟩
      have hqlt : q < 2 ^ w := by omega
      have hw2 : 2 ≤ w := by
        rcases Nat.lt_or_ge w 2 with hw | hw
        · exfalso
          rcases (by omega : w = 0 ∨ w = 1) with rfl | rfl
          · -- w = 0: s < 2 but s = 2q ≥ 2
            norm_num at hs
            omega
          · -- w = 1: q = 1 = 2^0, excluded as a power
            norm_num at hqlt
            exact hqp ⟨0, by rw [pow_zero]; omega⟩
        · exact hw
      obtain ⟨k, hks, hkv, hkd⟩ := ih q hqlt hq0 hqp
      refine ⟨shift 1 k, shift_supp hks, ?_, ?_⟩
      · rw [shift_val, hkv]; omega
      · rw [shift_dsum]; omega
    · -- s = 2q + 1 odd
      have hq1 : 1 ≤ q := by
        rcases Nat.eq_zero_or_pos q with rfl | h
        · exact absurd ⟨0, by rw [pow_zero]; omega⟩ hp
        · exact h
      have hqlt : q < 2 ^ w := by omega
      by_cases hqp : ∃ e, q = 2 ^ e
      · -- q = 2^e: base is all-ones-minus-bit-e, exactly w − 1 coins
        obtain ⟨e, rfl⟩ := hqp
        have hew : e < w := by
          by_contra hc
          push Not at hc
          have hle' : 2 ^ w ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) hc
          omega
        have he2 : 2 ^ (e + 1) = 2 * 2 ^ e := by rw [pow_succ]; ring
        have hle : 2 ^ (e + 1) ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) (by omega)
        obtain ⟨k, hks, hkv, hkd⟩ := ones_erase_rep_LeanPool_e110dec hew
        refine ⟨shift 0 k, shift_supp hks, ?_, ?_⟩
        · rw [shift_val, hkv]; omega
        · rw [shift_dsum]; omega
      · -- q not a power: shifted witness for q
        obtain ⟨k, hks, hkv, hkd⟩ := ih q hqlt (by omega) hqp
        refine ⟨shift 0 k, shift_supp hks, ?_, ?_⟩
        · rw [shift_val, hkv]; omega
        · rw [shift_dsum]; omega
lemma dsum_succ_of_lt_LeanPool_e110dec {n M s : ℕ}
    (h : ∃ k, val n k = M ∧ dsum n k = s) (hlt : s < M) :
    ∃ k, val n k = M ∧ dsum n k = s + 1 := by
  obtain ⟨k, hv, hd⟩ := h
  -- some index i ≥ 1 carries a coin, else value = digit sum
  have hex : ∃ i, 1 ≤ i ∧ i < n ∧ 1 ≤ k i := by
    by_contra hno
    push Not at hno
    have hvd : val n k = dsum n k := by
      unfold val dsum
      refine Finset.sum_congr rfl fun i hi => ?_
      rcases Nat.eq_zero_or_pos i with rfl | hi1
      · simp
      · have hk0 : k i = 0 := by
          have := hno i hi1 (Finset.mem_range.mp hi)
          omega
        rw [hk0]
        ring
    omega
  obtain ⟨i, hi1, hin, hki⟩ := hex
  obtain ⟨A, hA⟩ : ∃ A, k i = A + 1 := ⟨k i - 1, by omega⟩
  have hii : i - 1 ≠ i := by omega
  have hmem : i ∈ range n := Finset.mem_range.mpr hin
  have hmem' : i - 1 ∈ (range n).erase i :=
    Finset.mem_erase.mpr ⟨hii, Finset.mem_range.mpr (by omega)⟩
  -- decompose a sum by peeling index i, then i − 1
  have decomp : ∀ f : ℕ → ℕ, (∑ j ∈ range n, f j)
      = f i + (f (i - 1) + ∑ j ∈ ((range n).erase i).erase (i - 1), f j) := by
    intro f
    rw [← Finset.add_sum_erase _ _ hmem, ← Finset.add_sum_erase _ _ hmem']
  refine ⟨fun j => if j = i then A else if j = i - 1 then k (i - 1) + 2 else k j,
    ?_, ?_⟩
  · -- value is preserved
    unfold val
    rw [decomp fun j =>
      (if j = i then A else if j = i - 1 then k (i - 1) + 2 else k j) * 2 ^ j]
    unfold val at hv
    rw [decomp fun j => k j * 2 ^ j] at hv
    have hrest : (∑ j ∈ ((range n).erase i).erase (i - 1),
        (if j = i then A else if j = i - 1 then k (i - 1) + 2 else k j) * 2 ^ j)
        = ∑ j ∈ ((range n).erase i).erase (i - 1), k j * 2 ^ j := by
      refine Finset.sum_congr rfl fun j hj => ?_
      obtain ⟨hj1, hj2⟩ := Finset.mem_erase.mp hj
      obtain ⟨hj3, _⟩ := Finset.mem_erase.mp hj2
      rw [if_neg hj3, if_neg hj1]
    rw [if_pos rfl, if_neg hii, if_pos rfl, hrest]
    rw [hA] at hv
    have hpi : 2 ^ i = 2 ^ (i - 1) * 2 := by
      rw [← pow_succ]
      congr 1
      omega
    rw [hpi] at hv ⊢
    -- (A+1)·2P + B·P + R = M  ⟹  A·2P + (B+2)·P + R = M
    ring_nf at hv ⊢
    omega
  · -- digit sum goes up by one
    unfold dsum
    rw [decomp fun j =>
      if j = i then A else if j = i - 1 then k (i - 1) + 2 else k j]
    unfold dsum at hd
    rw [decomp k] at hd
    have hrest : (∑ j ∈ ((range n).erase i).erase (i - 1),
        (if j = i then A else if j = i - 1 then k (i - 1) + 2 else k j))
        = ∑ j ∈ ((range n).erase i).erase (i - 1), k j := by
      refine Finset.sum_congr rfl fun j hj => ?_
      obtain ⟨hj1, hj2⟩ := Finset.mem_erase.mp hj
      obtain ⟨hj3, _⟩ := Finset.mem_erase.mp hj2
      rw [if_neg hj3, if_neg hj1]
    rw [if_pos rfl, if_neg hii, if_pos rfl, hrest]
    omega
lemma exists_dsum_eq_LeanPool_e110dec {n M t : ℕ}
    (h : ∃ k, val n k = M ∧ dsum n k ≤ t) (htM : t ≤ M) :
    ∃ k, val n k = M ∧ dsum n k = t := by
  obtain ⟨k, hv, hd⟩ := h
  suffices aux : ∀ d s, s + d = t → (∃ k, val n k = M ∧ dsum n k = s) →
      ∃ k, val n k = M ∧ dsum n k = t by
    exact aux (t - dsum n k) (dsum n k) (by omega) ⟨k, hv, rfl⟩
  intro d
  induction d with
  | zero =>
    intro s h0 hk
    obtain rfl : s = t := by omega
    exact hk
  | succ d ih =>
    intro s h0 hk
    exact ih (s + 1) (by omega) (dsum_succ_of_lt_LeanPool_e110dec hk (by omega))
lemma succ_le_two_pow_pred_LeanPool_e110dec : ∀ n, 3 ≤ n → n + 1 ≤ 2 ^ (n - 1) := by
  intro n
  induction n with
  | zero => omega
  | succ p ih =>
    intro h
    rcases Nat.lt_or_ge p 3 with h3 | h3
    · have hp : p = 2 := by omega
      subst hp
      norm_num
    · have hp := ih h3
      have h1 : p + 1 - 1 = p := by omega
      rw [h1]
      have h2 : 2 ^ p = 2 * 2 ^ (p - 1) := by
        rw [← pow_succ']
        congr 1
        omega
      omega
theorem theoremB_LeanPool_e110dec {n N : ℕ} (hn : 2 ≤ n) (hN2 : 2 ≤ N)
    (hNlt : N < 2 ^ n - 2 ^ Nat.log 2 n) : ¬ Valid n N := by
  set m := Nat.log 2 n with hm
  have hmn : 2 ^ m ≤ n := Nat.pow_log_le_self 2 (by omega)
  have hnm : n < 2 ^ (m + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  have h1m : 1 ≤ 2 ^ m := Nat.one_le_pow _ _ (by norm_num)
  -- n = 2 makes the N-range empty, so n ≥ 3
  have hn3 : 3 ≤ n := by
    by_contra hc
    have h2 : n = 2 := by omega
    subst h2
    have hlog : Nat.log 2 2 = 1 :=
      Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)
    rw [hm, hlog] at hNlt
    norm_num at hNlt
    omega
  have hpow : 2 ^ n = 2 * 2 ^ (n - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have h1p : 1 ≤ 2 ^ (n - 1) := Nat.one_le_pow _ _ (by norm_num)
  have hnlt : n < 2 ^ n := Nat.lt_two_pow_self
  have hn12 : n + 1 ≤ 2 ^ (n - 1) := succ_le_two_pow_pred_LeanPool_e110dec n hn3
  have hm_le : 2 ^ m ≤ 2 ^ (n - 1) := by omega   -- 2^m ≤ n < 2^{n-1}
  rcases lt_trichotomy N (2 ^ (n - 1)) with hlt | heq | hgt
  · -- ── case (i): 2 ≤ N < 2^{n-1}; witness value M = 2^n − 1 + N
    obtain ⟨k0, hs, hv, hd⟩ := exists_rep_lt_LeanPool_e110dec (n - 1) (N - 1) (by omega)
    obtain ⟨us, uv, ud⟩ := update_top_LeanPool_e110dec (n - 1) 2 k0 hs
    have hn' : n - 1 + 1 = n := by omega
    rw [hn', hv] at uv
    rw [hn'] at ud
    have hbase : ∃ k, val n k = 2 ^ n - 1 + N ∧ dsum n k ≤ n :=
      ⟨Function.update k0 (n - 1) 2, by rw [uv]; omega, by rw [ud]; omega⟩
    have hex := exists_dsum_eq_LeanPool_e110dec hbase (by omega)
    refine not_valid_of_witness_LeanPool_e110dec (by omega) (by omega) ?_ hex
    have hle : 2 ^ n - 1 ≤ 2 ^ n - 1 + N := by omega
    refine ((Nat.modEq_iff_dvd' hle).mpr ?_).symm
    have heq' : 2 ^ n - 1 + N - (2 ^ n - 1) = N := by omega
    rw [heq']
  · -- ── case (ii): N = 2^{n-1}; witness value M = 2^{n-1} − 1  (V = −N)
    obtain ⟨k0, hs, hv, hd⟩ := ones_rep_LeanPool_e110dec (n - 1)
    have hbase : ∃ k, val n k = 2 ^ (n - 1) - 1 ∧ dsum n k ≤ n :=
      ⟨k0, by rw [val_pad (by omega) hs, hv], by rw [dsum_pad (by omega) hs]; omega⟩
    have hex := exists_dsum_eq_LeanPool_e110dec hbase (by omega)
    refine not_valid_of_witness_LeanPool_e110dec (by omega) (by omega) ?_ hex
    have hle : 2 ^ (n - 1) - 1 ≤ 2 ^ n - 1 := by omega
    refine (Nat.modEq_iff_dvd' hle).mpr ?_
    have heq' : 2 ^ n - 1 - (2 ^ (n - 1) - 1) = N := by omega
    rw [heq']
  · -- N > 2^{n-1}: the gap s := 2^n − N satisfies 2^m < s < 2^{n-1}
    have hs_ub : 2 ^ n - N < 2 ^ (n - 1) := by omega
    have hs_lb : 2 ^ m < 2 ^ n - N := by omega
    by_cases hpw : ∃ e, 2 ^ n - N = 2 ^ e
    · -- ── case (iv): single-power gap 2^e; witness M = 2^e − 1  (V = −N)
      obtain ⟨e, he⟩ := hpw
      have hme : m < e := by
        by_contra hc
        push Not at hc
        have hle' : 2 ^ e ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hc
        omega
      have he2 : 2 ^ (m + 1) ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hen : e ≤ n - 1 := by
        by_contra hc
        push Not at hc
        have := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hc.le
        omega
      obtain ⟨k0, hs0, hv0, hd0⟩ := ones_rep_LeanPool_e110dec e
      have hbase : ∃ k, val n k = 2 ^ e - 1 ∧ dsum n k ≤ n :=
        ⟨k0, by rw [val_pad (by omega) hs0, hv0],
          by rw [dsum_pad (by omega) hs0, hd0]; omega⟩
      have hex := exists_dsum_eq_LeanPool_e110dec hbase (by omega)
      refine not_valid_of_witness_LeanPool_e110dec (by omega) (by omega) ?_ hex
      have hle : 2 ^ e - 1 ≤ 2 ^ n - 1 := by omega
      refine (Nat.modEq_iff_dvd' hle).mpr ?_
      have heq' : 2 ^ n - 1 - (2 ^ e - 1) = N := by omega
      rw [heq']
    · -- ── case (iii): gap with ≥ 2 bits; witness value M = 2^n − 1 + N
      obtain ⟨k0, hs0, hv0, hd0⟩ :=
        exists_rep_compl_LeanPool_e110dec (n - 1) (2 ^ n - N) hs_ub (by omega) hpw
      obtain ⟨us, uv, ud⟩ := update_top_LeanPool_e110dec (n - 1) 3 k0 hs0
      have hn' : n - 1 + 1 = n := by omega
      rw [hn', hv0] at uv
      rw [hn'] at ud
      have hbase : ∃ k, val n k = 2 ^ n - 1 + N ∧ dsum n k ≤ n :=
        ⟨Function.update k0 (n - 1) 3, by rw [uv]; omega, by rw [ud]; omega⟩
      have hex := exists_dsum_eq_LeanPool_e110dec hbase (by omega)
      refine not_valid_of_witness_LeanPool_e110dec (by omega) (by omega) ?_ hex
      have hle : 2 ^ n - 1 ≤ 2 ^ n - 1 + N := by omega
      refine ((Nat.modEq_iff_dvd' hle).mpr ?_).symm
      have heq' : 2 ^ n - 1 + N - (2 ^ n - 1) = N := by omega
      rw [heq']
example : ¬ Valid 5 24 :=
  theoremB_LeanPool_e110dec (by norm_num) (by norm_num)
    (by rw [Nat.log_eq_of_pow_le_of_lt_pow (by norm_num : 2 ^ 2 ≤ 5)
          (by norm_num : 5 < 2 ^ (2 + 1))]
        norm_num)
example : ¬ Valid 4 8 :=
  theoremB_LeanPool_e110dec (by norm_num) (by norm_num)
    (by rw [Nat.log_eq_of_pow_le_of_lt_pow (by norm_num : 2 ^ 2 ≤ 4)
          (by norm_num : 4 < 2 ^ (2 + 1))]
        norm_num)
def gmin : ℕ → ℕ → ℕ
  | 0, M => M
  | w + 1, M => M % 2 + gmin w (M / 2)
end MinModulus


