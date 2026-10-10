-- Prove2me | solution 1 for ArtinPrimitiveRoots.rough_count_character
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T13:40:52.963997+00:00
-- url     : https://prove2.me/submissions/cb4148e9-f2c4-457c-a12e-b2c00afcf94f

import Mathlib
import Definitions.Def_ArtinSieve

section
/-! # Shared tools for prover S (A106): Bonferroni truncation, residue counts, Abel summation -/

namespace ArtinPrimitiveRoots.A106S

open Real Finset

/-! ## Bonferroni truncation -/

/-- The alternating sum `Σ_{S ⊆ P, |S| < n} (-1)^{|S|} ∏_{p ∈ S} a p`. -/
noncomputable def bonfTrunc (P : Finset ℕ) (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ S ∈ P.powerset, if S.card < n then (-1 : ℝ) ^ S.card * ∏ p ∈ S, a p else 0

/-- The elementary symmetric sum `e_n(a) = Σ_{S ⊆ P, |S| = n} ∏_{p ∈ S} a p`. -/
noncomputable def esym (P : Finset ℕ) (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ S ∈ P.powerset, if S.card = n then ∏ p ∈ S, a p else 0

lemma bonfTrunc_zero (P : Finset ℕ) (a : ℕ → ℝ) : bonfTrunc P a 0 = 0 := by
  simp [bonfTrunc]

lemma esym_zero (P : Finset ℕ) (a : ℕ → ℝ) : esym P a 0 = 1 := by
  unfold esym
  rw [Finset.sum_eq_single ∅]
  · simp
  · intro S _ hS; simp [Finset.card_eq_zero, hS]
  · intro h; exact absurd (Finset.empty_mem_powerset P) h

lemma bonfTrunc_insert (P : Finset ℕ) (a : ℕ → ℝ) (q : ℕ) (hq : q ∉ P) (n : ℕ) :
    bonfTrunc (insert q P) a (n + 1) = bonfTrunc P a (n + 1) - a q * bonfTrunc P a n := by
  unfold bonfTrunc
  rw [Finset.sum_powerset_insert hq, sub_eq_add_neg, Finset.mul_sum, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun S hS => ?_
  have hqS : q ∉ S := fun h => hq (Finset.mem_powerset.1 hS h)
  rw [Finset.card_insert_of_notMem hqS, Finset.prod_insert hqS]
  by_cases h : S.card < n
  · rw [if_pos (by omega), if_pos h]; ring
  · rw [if_neg (by omega), if_neg h]; ring

lemma esym_insert (P : Finset ℕ) (a : ℕ → ℝ) (q : ℕ) (hq : q ∉ P) (n : ℕ) :
    esym (insert q P) a (n + 1) = esym P a (n + 1) + a q * esym P a n := by
  unfold esym
  rw [Finset.sum_powerset_insert hq, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun S hS => ?_
  have hqS : q ∉ S := fun h => hq (Finset.mem_powerset.1 hS h)
  rw [Finset.card_insert_of_notMem hqS, Finset.prod_insert hqS]
  by_cases h : S.card = n
  · rw [if_pos (by omega), if_pos h]
  · rw [if_neg (by omega), if_neg h]; ring

lemma bonf_signed (a : ℕ → ℝ) (P : Finset ℕ) (ha : ∀ p ∈ P, 0 ≤ a p ∧ a p ≤ 1) :
    ∀ n : ℕ, 0 ≤ (-1 : ℝ) ^ n * (∏ p ∈ P, (1 - a p) - bonfTrunc P a n) ∧
      (-1 : ℝ) ^ n * (∏ p ∈ P, (1 - a p) - bonfTrunc P a n) ≤ esym P a n := by
  induction P using Finset.induction_on with
  | empty => intro n; cases n <;> simp [bonfTrunc, esym]
  | insert q P hq ih =>
    have ha' : ∀ p ∈ P, 0 ≤ a p ∧ a p ≤ 1 := fun p hp => ha p (Finset.mem_insert_of_mem hp)
    have haq := ha q (Finset.mem_insert_self q P)
    intro n
    cases n with
    | zero =>
      simp only [pow_zero, one_mul, bonfTrunc_zero, sub_zero, esym_zero]
      refine ⟨Finset.prod_nonneg fun p hp => by linarith [(ha p hp).2],
        Finset.prod_le_one (fun p hp => by linarith [(ha p hp).2])
          (fun p hp => by linarith [(ha p hp).1])⟩
    | succ n =>
      obtain ⟨h1, h2⟩ := ih ha' (n + 1)
      obtain ⟨h3, h4⟩ := ih ha' n
      rw [bonfTrunc_insert P a q hq, esym_insert P a q hq, Finset.prod_insert hq]
      have e : (-1 : ℝ) ^ (n + 1) * ((1 - a q) * ∏ p ∈ P, (1 - a p) -
          (bonfTrunc P a (n + 1) - a q * bonfTrunc P a n)) =
          (-1 : ℝ) ^ (n + 1) * (∏ p ∈ P, (1 - a p) - bonfTrunc P a (n + 1)) +
            a q * ((-1 : ℝ) ^ n * (∏ p ∈ P, (1 - a p) - bonfTrunc P a n)) := by
        rw [pow_succ]; ring
      rw [e]
      constructor
      · have := mul_nonneg haq.1 h3; linarith
      · have := mul_le_mul_of_nonneg_left h4 haq.1; linarith

/-- Bonferroni's inequalities: the truncation error is at most the next elementary symmetric
sum. -/
lemma bonferroni (a : ℕ → ℝ) (P : Finset ℕ) (ha : ∀ p ∈ P, 0 ≤ a p ∧ a p ≤ 1) (n : ℕ) :
    |∏ p ∈ P, (1 - a p) - bonfTrunc P a n| ≤ esym P a n := by
  obtain ⟨h1, h2⟩ := bonf_signed a P ha n
  have : |∏ p ∈ P, (1 - a p) - bonfTrunc P a n| =
      (-1 : ℝ) ^ n * (∏ p ∈ P, (1 - a p) - bonfTrunc P a n) := by
    rw [← abs_of_nonneg h1, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  rw [this]; exact h2

lemma pow_succ_add_le (s a : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ a) (n : ℕ) :
    s ^ (n + 1) + (n + 1) * a * s ^ n ≤ (s + a) ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h0 : 0 ≤ s ^ n := pow_nonneg hs n
    have h1 : 0 ≤ (n + 1 : ℝ) * a * a * s ^ n := by positivity
    calc s ^ (n + 1 + 1) + ((n + 1 : ℕ) + 1 : ℝ) * a * s ^ (n + 1)
        ≤ (s + a) * (s ^ (n + 1) + (n + 1) * a * s ^ n) := by
          push_cast; rw [pow_succ, pow_succ]; nlinarith
      _ ≤ (s + a) * (s + a) ^ (n + 1) := mul_le_mul_of_nonneg_left ih (by linarith)
      _ = (s + a) ^ (n + 1 + 1) := by rw [pow_succ]; ring

lemma esym_nonneg (a : ℕ → ℝ) (P : Finset ℕ) (ha : ∀ p ∈ P, 0 ≤ a p) (n : ℕ) :
    0 ≤ esym P a n := by
  unfold esym
  refine Finset.sum_nonneg fun S hS => ?_
  split_ifs
  · exact Finset.prod_nonneg fun p hp => ha p (Finset.mem_powerset.1 hS hp)
  · exact le_refl _

/-- `e_n(a) ≤ (Σ a)^n / n!`. -/
lemma esym_le (a : ℕ → ℝ) (P : Finset ℕ) (ha : ∀ p ∈ P, 0 ≤ a p) :
    ∀ n : ℕ, esym P a n ≤ (∑ p ∈ P, a p) ^ n / n.factorial := by
  induction P using Finset.induction_on with
  | empty =>
    intro n; cases n with
    | zero => simp [esym_zero]
    | succ n => simp [esym]
  | insert q P hq ih =>
    have ha' : ∀ p ∈ P, 0 ≤ a p := fun p hp => ha p (Finset.mem_insert_of_mem hp)
    have haq := ha q (Finset.mem_insert_self q P)
    intro n
    cases n with
    | zero => simp [esym_zero]
    | succ n =>
      rw [esym_insert P a q hq, Finset.sum_insert hq]
      have hs : 0 ≤ ∑ p ∈ P, a p := Finset.sum_nonneg ha'
      have h1 := ih ha' (n + 1)
      have h2 := mul_le_mul_of_nonneg_left (ih ha' n) haq
      have hb := pow_succ_add_le (∑ p ∈ P, a p) (a q) hs haq n
      have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
      have hf1 : ((n + 1).factorial : ℝ) = (n + 1) * n.factorial := by
        push_cast [Nat.factorial_succ]; ring
      calc esym P a (n + 1) + a q * esym P a n
          ≤ (∑ p ∈ P, a p) ^ (n + 1) / (n + 1).factorial +
              a q * ((∑ p ∈ P, a p) ^ n / n.factorial) := add_le_add h1 h2
        _ = ((∑ p ∈ P, a p) ^ (n + 1) + (n + 1) * a q * (∑ p ∈ P, a p) ^ n) /
              (n + 1).factorial := by
            rw [hf1]; field_simp
        _ ≤ (a q + ∑ p ∈ P, a p) ^ (n + 1) / (n + 1).factorial := by
            rw [add_comm (a q)]
            exact div_le_div_of_nonneg_right hb (by positivity)

/-- `s^n/n! ≤ exp(-n/2)` once `n ≥ 2e·s`; we use the cruder `n ≥ 8 s`. -/
lemma pow_div_factorial_le (s : ℝ) (hs : 0 ≤ s) (n : ℕ) (hn : 8 * s ≤ n) :
    s ^ n / n.factorial ≤ exp (-(n : ℝ)) := by
  have h := pow_div_factorial_le_exp (8 * s) (by positivity) n
  have h8 : (8 * s) ^ n = 8 ^ n * s ^ n := by rw [mul_pow]
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have h8n : exp (2 * (n : ℝ)) ≤ (8 : ℝ) ^ n := by
    rw [← exp_log (show (0 : ℝ) < 8 by norm_num), ← exp_nat_mul]
    apply exp_le_exp.2
    have : (2 : ℝ) ≤ log 8 := by
      have : (8 : ℝ) = 2 ^ 3 := by norm_num
      rw [this, log_pow]; push_cast; linarith [log_two_gt_d9]
    nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hpos : (0 : ℝ) < 8 ^ n := by positivity
  rw [h8, mul_div_assoc] at h
  have h3 : s ^ n / n.factorial ≤ exp (8 * s) / 8 ^ n := by
    rw [le_div_iff₀ hpos]; linarith
  calc s ^ n / n.factorial ≤ exp (8 * s) / 8 ^ n := h3
    _ ≤ exp (n : ℝ) / exp (2 * n) := by
        apply div_le_div₀ (exp_pos _).le (exp_le_exp.2 hn) (exp_pos _) h8n
    _ = exp (-(n : ℝ)) := by rw [← exp_sub]; ring_nf

/-! ## Residue classes in intervals -/

lemma count_modEq_Ico (q : ℕ) (hq : 0 < q) (a b v : ℕ) (hab : a ≤ b) :
    |((#{n ∈ Ico a b | n ≡ v [MOD q]} : ℕ) : ℝ) - ((b : ℝ) - a) / q| ≤ 2 := by
  have h1 : (Ico a b).filter (fun n => n ≡ v [MOD q]) =
      ((range b).filter (fun n => n ≡ v [MOD q])) \ ((range a).filter (fun n => n ≡ v [MOD q])) := by
    ext n; simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_sdiff, Finset.mem_range]; constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h2, h3⟩, fun h => by omega⟩
    · rintro ⟨⟨h2, h3⟩, h4⟩; exact ⟨⟨by by_contra h; exact h4 ⟨by omega, h3⟩, h2⟩, h3⟩
  have hsub : ((range a).filter (fun n => n ≡ v [MOD q])) ⊆ ((range b).filter (fun n => n ≡ v [MOD q])) := by
    intro n; simp only [mem_filter, mem_range]; rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
  rw [h1, card_sdiff_of_subset hsub]
  have cb := Nat.count_modEq_card (b := b) hq v
  have ca := Nat.count_modEq_card (b := a) hq v
  rw [Nat.count_eq_card_filter_range] at cb ca
  rw [Nat.cast_sub (card_le_card hsub), cb, ca]
  have hb1 : ((b / q : ℕ) : ℝ) ≤ (b : ℝ) / q := Nat.cast_div_le
  have hb2 : (b : ℝ) / q - 1 ≤ ((b / q : ℕ) : ℝ) := by
    have := Nat.lt_div_mul_add (a := b) hq
    rw [div_sub_one (by positivity), div_le_iff₀ (by positivity)]
    have : (b : ℝ) < ((b / q : ℕ) : ℝ) * q + q := by exact_mod_cast this
    linarith
  have ha1 : ((a / q : ℕ) : ℝ) ≤ (a : ℝ) / q := Nat.cast_div_le
  have ha2 : (a : ℝ) / q - 1 ≤ ((a / q : ℕ) : ℝ) := by
    have := Nat.lt_div_mul_add (a := a) hq
    rw [div_sub_one (by positivity), div_le_iff₀ (by positivity)]
    have : (a : ℝ) < ((a / q : ℕ) : ℝ) * q + q := by exact_mod_cast this
    linarith
  have e1 : ((if v % q < b % q then 1 else 0 : ℕ) : ℝ) ≤ 1 := by split_ifs <;> simp
  have e2 : (0 : ℝ) ≤ ((if v % q < b % q then 1 else 0 : ℕ) : ℝ) := by positivity
  have e3 : ((if v % q < a % q then 1 else 0 : ℕ) : ℝ) ≤ 1 := by split_ifs <;> simp
  have e4 : (0 : ℝ) ≤ ((if v % q < a % q then 1 else 0 : ℕ) : ℝ) := by positivity
  rw [sub_div, Nat.cast_add, Nat.cast_add]
  rw [abs_le]; constructor <;> linarith

/-- An order-connected bounded set of reals lies between the open and closed intervals of its
infimum and supremum, and its measure is their difference. -/
lemma ordConnected_facts (I : Set ℝ) (hI : I.OrdConnected) (hne : I.Nonempty) (X : ℝ)
    (hIX : I ⊆ Set.Icc 0 X) :
    Set.Ioo (sInf I) (sSup I) ⊆ I ∧ I ⊆ Set.Icc (sInf I) (sSup I) ∧ 0 ≤ sInf I ∧
      sInf I ≤ sSup I ∧ sSup I ≤ X ∧
      (MeasureTheory.volume I).toReal = sSup I - sInf I := by
  have hb : BddBelow I := ⟨0, fun y hy => (hIX hy).1⟩
  have ha : BddAbove I := ⟨X, fun y hy => (hIX hy).2⟩
  have hc : IsConnected I := ⟨hne, hI.isPreconnected⟩
  have h1 := hc.Ioo_csInf_csSup_subset hb ha
  have h2 : I ⊆ Set.Icc (sInf I) (sSup I) := fun y hy => ⟨csInf_le hb hy, le_csSup ha hy⟩
  obtain ⟨y, hy⟩ := hne
  have hab : sInf I ≤ sSup I := (h2 hy).1.trans (h2 hy).2
  refine ⟨h1, h2, le_csInf ⟨y, hy⟩ fun z hz => (hIX hz).1, hab,
    csSup_le ⟨y, hy⟩ fun z hz => (hIX hz).2, ?_⟩
  have v1 := MeasureTheory.measure_mono (μ := MeasureTheory.volume) h1
  have v2 := MeasureTheory.measure_mono (μ := MeasureTheory.volume) h2
  rw [Real.volume_Ioo] at v1
  rw [Real.volume_Icc] at v2
  rw [le_antisymm v2 v1, ENNReal.toReal_ofReal (by linarith)]

open Classical in
/-- Residue classes in an order-connected set of nonnegative reals. -/
lemma count_ordConnected (I : Set ℝ) (hI : I.OrdConnected) (X : ℝ) (hIX : I ⊆ Set.Icc 0 X)
    (q : ℕ) (hq : 0 < q) (v : ℕ) :
    |((((range (⌊X⌋₊ + 1)).filter (fun t : ℕ => (t : ℝ) ∈ I ∧ t ≡ v [MOD q])).card : ℕ) : ℝ) -
      (MeasureTheory.volume I).toReal / q| ≤ 3 := by
  rcases I.eq_empty_or_nonempty with h | hne
  · subst h; simp
  obtain ⟨hIoo, hIcc, ha0, hab, hbX, hvol⟩ := ordConnected_facts I hI hne X hIX
  set a := sInf I
  set b := sSup I
  rw [hvol]
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  rw [abs_le]; constructor
  · -- lower bound
    by_cases hc : ⌊a⌋₊ + 1 ≤ ⌈b⌉₊
    · have hsub : (Ico (⌊a⌋₊ + 1) ⌈b⌉₊).filter (fun n => n ≡ v [MOD q]) ⊆
          (range (⌊X⌋₊ + 1)).filter (fun t : ℕ => (t : ℝ) ∈ I ∧ t ≡ v [MOD q]) := by
        intro t ht
        simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_range] at ht ⊢
        have h1 : a < t := Nat.lt_of_floor_lt (by omega)
        have h2 : (t : ℝ) < b := Nat.lt_ceil.1 ht.1.2
        refine ⟨?_, hIoo ⟨h1, h2⟩, ht.2⟩
        have : t ≤ ⌊X⌋₊ := Nat.le_floor (by linarith)
        omega
      have hcard := card_le_card hsub
      have hc' := count_modEq_Ico q hq _ _ v hc
      have hf : (⌊a⌋₊ : ℝ) ≤ a := Nat.floor_le ha0
      have hcb : b ≤ (⌈b⌉₊ : ℝ) := Nat.le_ceil b
      have : ((⌈b⌉₊ : ℝ) - ((⌊a⌋₊ + 1 : ℕ) : ℝ)) / q ≥ (b - a) / q - 1 / q := by
        rw [← sub_div]; apply div_le_div_of_nonneg_right _ hq'.le; push_cast; linarith
      have h1q : 1 / (q : ℝ) ≤ 1 := by
        rw [div_le_one hq']; exact_mod_cast hq
      have hcard' : ((#{n ∈ Ico (⌊a⌋₊ + 1) ⌈b⌉₊ | n ≡ v [MOD q]} : ℕ) : ℝ) ≤
          ((((range (⌊X⌋₊ + 1)).filter (fun t : ℕ => (t : ℝ) ∈ I ∧ t ≡ v [MOD q])).card : ℕ) : ℝ) := by
        exact_mod_cast hcard
      rw [abs_le] at hc'
      linarith [hc'.1]
    · have : (⌈b⌉₊ : ℝ) ≤ ⌊a⌋₊ := by exact_mod_cast (by omega : ⌈b⌉₊ ≤ ⌊a⌋₊)
      have hf : (⌊a⌋₊ : ℝ) ≤ a := Nat.floor_le ha0
      have hcb : b ≤ (⌈b⌉₊ : ℝ) := Nat.le_ceil b
      have : (b - a) / q ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hq'.le
      have : (0 : ℝ) ≤ ((((range (⌊X⌋₊ + 1)).filter (fun t : ℕ => (t : ℝ) ∈ I ∧ t ≡ v [MOD q])).card : ℕ) : ℝ) :=
        Nat.cast_nonneg _
      linarith
  · -- upper bound
    have hc : ⌈a⌉₊ ≤ ⌊b⌋₊ + 1 := (Nat.ceil_mono hab).trans (Nat.ceil_le_floor_add_one b)
    have hsub : (range (⌊X⌋₊ + 1)).filter (fun t : ℕ => (t : ℝ) ∈ I ∧ t ≡ v [MOD q]) ⊆
        (Ico ⌈a⌉₊ (⌊b⌋₊ + 1)).filter (fun n => n ≡ v [MOD q]) := by
      intro t ht
      simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_range] at ht ⊢
      have := hIcc ht.2.1
      refine ⟨⟨Nat.ceil_le.2 this.1, Nat.lt_succ_of_le (Nat.le_floor this.2)⟩, ht.2.2⟩
    have hcard := card_le_card hsub
    have hc' := count_modEq_Ico q hq _ _ v hc
    have hf : (⌊b⌋₊ : ℝ) ≤ b := Nat.floor_le (ha0.trans hab)
    have hca : a ≤ (⌈a⌉₊ : ℝ) := Nat.le_ceil a
    have : ((((⌊b⌋₊ + 1 : ℕ) : ℝ)) - ⌈a⌉₊) / q ≤ (b - a) / q + 1 / q := by
      rw [← add_div]; apply div_le_div_of_nonneg_right _ hq'.le; push_cast; linarith
    have h1q : 1 / (q : ℝ) ≤ 1 := by
      rw [div_le_one hq']; exact_mod_cast hq
    have hcard' : ((((range (⌊X⌋₊ + 1)).filter (fun t : ℕ => (t : ℝ) ∈ I ∧ t ≡ v [MOD q])).card : ℕ) : ℝ) ≤
        ((#{n ∈ Ico ⌈a⌉₊ (⌊b⌋₊ + 1) | n ≡ v [MOD q]} : ℕ) : ℝ) := by
      exact_mod_cast hcard
    rw [abs_le] at hc'
    linarith [hc'.2]

/-! ## Abel summation over tails -/

/-! ## Exponential sums over progressions -/

/-! ## Brun's pure sieve and character sums -/

lemma prod_dvd_iff (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (m : ℕ) :
    (∀ p ∈ S, p ∣ m) ↔ (∏ p ∈ S, p) ∣ m :=
  ⟨fun h => Finset.prod_primes_dvd m (fun p hp => (hS p hp).prime) h,
    fun h _ hp => (Finset.dvd_prod_of_mem _ hp).trans h⟩

open Classical in
/-- Brun's pure sieve (Bonferroni truncation) for a weighted sum over integers free of the
primes in `P`. -/
lemma sieve_decomp (R P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (n : ℕ) (c : ℕ → ℂ) :
    ‖∑ m ∈ R, (if ∀ p ∈ P, ¬ p ∣ m then c m else 0) -
        ∑ S ∈ P.powerset, (if S.card < n then (-1 : ℂ) ^ S.card *
          ∑ m ∈ R, (if (∏ p ∈ S, p) ∣ m then c m else 0) else 0)‖ ≤
      ∑ S ∈ P.powerset, (if S.card = n then
          ∑ m ∈ R, (if (∏ p ∈ S, p) ∣ m then ‖c m‖ else 0) else 0) := by
  let a : ℕ → ℕ → ℝ := fun m p => if p ∣ m then 1 else 0
  have ha : ∀ m, ∀ p ∈ P, 0 ≤ a m p ∧ a m p ≤ 1 := fun m p _ => by
    simp only [a]; split_ifs <;> norm_num
  have hind : ∀ m, (if ∀ p ∈ P, ¬ p ∣ m then (1 : ℝ) else 0) = ∏ p ∈ P, (1 - a m p) := by
    intro m
    simp only [a]
    rw [show (fun p => (1 : ℝ) - if p ∣ m then 1 else 0) = fun p => if ¬ p ∣ m then 1 else 0 from
      funext fun p => by split_ifs <;> norm_num, Finset.prod_boole]
  have hprod : ∀ m, ∀ S ∈ P.powerset, ∏ p ∈ S, a m p = if (∏ p ∈ S, p) ∣ m then 1 else 0 := by
    intro m S hS
    have hS' : ∀ p ∈ S, p.Prime := fun p hp => hP p (Finset.mem_powerset.1 hS hp)
    simp only [a]
    rw [Finset.prod_boole]
    simp only [prod_dvd_iff S hS' m]
  -- rewrite both sums pointwise in `m`
  have e1 : ∑ m ∈ R, (if ∀ p ∈ P, ¬ p ∣ m then c m else 0) =
      ∑ m ∈ R, c m * ((∏ p ∈ P, (1 - a m p) : ℝ) : ℂ) := by
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← hind m]; split_ifs <;> simp
  have e2 : ∑ S ∈ P.powerset, (if S.card < n then (-1 : ℂ) ^ S.card *
        ∑ m ∈ R, (if (∏ p ∈ S, p) ∣ m then c m else 0) else 0) =
      ∑ m ∈ R, c m * ((bonfTrunc P (a m) n : ℝ) : ℂ) := by
    simp only [bonfTrunc]
    push_cast
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun S hS => ?_
    split_ifs with h
    · refine Finset.sum_congr rfl fun m _ => ?_
      have := hprod m S hS
      rw [this]
      split_ifs <;> push_cast <;> ring
    · simp
  have e3 : ∑ S ∈ P.powerset, (if S.card = n then
          ∑ m ∈ R, (if (∏ p ∈ S, p) ∣ m then ‖c m‖ else 0) else 0) =
      ∑ m ∈ R, ‖c m‖ * esym P (a m) n := by
    simp only [esym, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun S hS => ?_
    split_ifs with h
    · refine Finset.sum_congr rfl fun m _ => ?_
      rw [hprod m S hS]
      split_ifs <;> simp
    · simp
  rw [e1, e2, e3, ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ => ?_)
  rw [← mul_sub, norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (bonferroni (a m) P (ha m) n) (norm_nonneg _)

open Classical in
/-- Reindexing multiples of `d`. -/
lemma sum_dvd_reindex (B d : ℕ) (hd : 0 < d) (g : ℕ → ℂ) :
    ∑ m ∈ range B, (if d ∣ m then g m else 0) =
      ∑ t ∈ range B, (if d * t < B then g (d * t) else 0) := by
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  have : (range B).filter (fun m => d ∣ m) =
      ((range B).filter (fun t => d * t < B)).image (fun t => d * t) := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hm, t, rfl⟩
      refine ⟨t, ⟨?_, hm⟩, rfl⟩
      exact lt_of_le_of_lt (Nat.le_mul_of_pos_left t hd) hm
    · rintro ⟨t, ⟨_, ht⟩, rfl⟩
      exact ⟨ht, dvd_mul_right d t⟩
  rw [this, Finset.sum_image (fun t _ t' _ h => Nat.eq_of_mul_eq_mul_left hd h)]

/-- Splitting a sum into residue classes. -/
lemma sum_residues (s : Finset ℕ) (k : ℕ) (hk : 0 < k) (f : ℕ → ℂ) :
    ∑ t ∈ s, f t = ∑ b ∈ range k, ∑ t ∈ s.filter (fun t => t ≡ b [MOD k]), f t := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun t => t % k) (t := range k)
    (fun t _ => Finset.mem_range.2 (Nat.mod_lt t hk))]
  refine Finset.sum_congr rfl fun b hb => ?_
  have hb' : b % k = b := Nat.mod_eq_of_lt (Finset.mem_range.1 hb)
  congr 1
  ext t
  simp only [Finset.mem_filter, Nat.ModEq, hb']

/-- A sum over `range k` of a function of residues is the sum over `ZMod k`. -/
lemma sum_range_zmod (k : ℕ) [NeZero k] (f : ZMod k → ℂ) :
    ∑ b ∈ range k, f (b : ZMod k) = ∑ x : ZMod k, f x := by
  refine Finset.sum_nbij' (fun b => (b : ZMod k)) (fun x => x.val) ?_ ?_ ?_ ?_ ?_
  · intro b _; exact Finset.mem_univ _
  · intro x _; exact Finset.mem_range.2 (ZMod.val_lt x)
  · intro b hb; simp [ZMod.val_natCast, Nat.mod_eq_of_lt (Finset.mem_range.1 hb)]
  · intro x _; simp
  · intro b _; rfl

open Classical in
/-- Orthogonality of a Dirichlet character over `range k`. -/
lemma sum_char_range (k : ℕ) (hk : 0 < k) (χ : DirichletCharacter ℂ k) :
    ∑ b ∈ range k, χ (b : ZMod k) = if χ = 1 then (Nat.totient k : ℂ) else 0 := by
  have : NeZero k := ⟨hk.ne'⟩
  rw [sum_range_zmod k (fun x => χ x)]
  split_ifs with h
  · subst h
    classical
    rw [MulChar.sum_one_eq_card_units, ZMod.card_units_eq_totient]
  · exact MulChar.sum_eq_zero_of_ne_one h

lemma card_powerset_le (P : Finset ℕ) :
    ∀ n : ℕ, (∑ S ∈ P.powerset, (if S.card ≤ n then (1 : ℝ) else 0)) ≤ ((P.card : ℝ) + 1) ^ n := by
  induction P using Finset.induction_on with
  | empty =>
    intro n
    rw [Finset.powerset_empty, Finset.sum_singleton, Finset.card_empty, if_pos (Nat.zero_le n)]
    simp
  | insert q P hq ih =>
    intro n
    rw [Finset.sum_powerset_insert hq, Finset.card_insert_of_notMem hq]
    cases n with
    | zero =>
      have h1 : ∑ S ∈ P.powerset, (if S.card ≤ 0 then (1 : ℝ) else 0) ≤ 1 := by
        have := ih 0; rwa [pow_zero] at this
      have h2 : ∑ S ∈ P.powerset, (if (insert q S).card ≤ 0 then (1 : ℝ) else 0) = 0 := by
        refine Finset.sum_eq_zero fun S hS => ?_
        rw [if_neg]; have := Finset.card_pos.2 (Finset.insert_nonempty q S); omega
      rw [h2]; simp only [add_zero, pow_zero]; exact h1
    | succ n =>
      have h2 : ∑ S ∈ P.powerset, (if (insert q S).card ≤ n + 1 then (1 : ℝ) else 0) =
          ∑ S ∈ P.powerset, (if S.card ≤ n then (1 : ℝ) else 0) := by
        refine Finset.sum_congr rfl fun S hS => ?_
        have hqS : q ∉ S := fun h => hq (Finset.mem_powerset.1 hS h)
        rw [Finset.card_insert_of_notMem hqS]
        simp only [add_le_add_iff_right]
      rw [h2]
      have hb := pow_succ_add_le ((P.card : ℝ) + 1) 1 (by positivity) zero_le_one n
      have hp : (1 : ℝ) ≤ ((P.card : ℝ) + 1) ^ n := one_le_pow₀ (by linarith [(Nat.cast_nonneg P.card : (0:ℝ) ≤ P.card)])
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have := ih (n + 1)
      have := ih n
      push_cast
      have : ((P.card : ℝ) + 1) ^ n ≤ (n + 1) * 1 * ((P.card : ℝ) + 1) ^ n := by nlinarith
      nlinarith

/-! ## Dilated intervals -/

/-- The set `{y : d y ∈ J}`. -/
def scaleSet (d : ℕ) (J : Set ℝ) : Set ℝ := (fun y : ℝ => (d : ℝ) * y) ⁻¹' J

lemma scaleSet_ordConnected (d : ℕ) (J : Set ℝ) (hJ : J.OrdConnected) :
    (scaleSet d J).OrdConnected := by
  refine ⟨fun y₁ h₁ y₂ h₂ y hy => ?_⟩
  simp only [scaleSet, Set.mem_preimage] at h₁ h₂ ⊢
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  exact hJ.out h₁ h₂ ⟨mul_le_mul_of_nonneg_left hy.1 hd, mul_le_mul_of_nonneg_left hy.2 hd⟩

lemma scaleSet_subset (d : ℕ) (hd : 0 < d) (J : Set ℝ) (M : ℝ) (hJ : J ⊆ Set.Icc M (2 * M)) :
    scaleSet d J ⊆ Set.Icc (M / d) (2 * (M / d)) := by
  intro y hy
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have := hJ hy
  simp only [Set.mem_Icc] at this ⊢
  constructor
  · rw [div_le_iff₀ hd']; linarith
  · rw [← mul_div_assoc, le_div_iff₀ hd']; linarith

lemma scaleSet_volume (d : ℕ) (hd : 0 < d) (J : Set ℝ) :
    (MeasureTheory.volume (scaleSet d J)).toReal = (MeasureTheory.volume J).toReal / d := by
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  rw [scaleSet, Real.volume_preimage_mul_left hd', ENNReal.toReal_mul, ENNReal.toReal_ofReal
    (abs_nonneg _), abs_inv, abs_of_pos (by exact_mod_cast hd)]
  ring

lemma volume_le (J : Set ℝ) (M : ℝ) (hM : 0 < M) (hJ : J ⊆ Set.Icc M (2 * M)) :
    (MeasureTheory.volume J).toReal ≤ M := by
  have h := MeasureTheory.measure_mono (μ := MeasureTheory.volume) hJ
  rw [Real.volume_Icc] at h
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  rw [ENNReal.toReal_ofReal (by linarith)] at this
  linarith

end ArtinPrimitiveRoots.A106S
end

section
namespace ArtinPrimitiveRoots.A106S

open Real Finset

/-! # (10.17) `rough_count_character` by Brun's pure sieve (prover S) -/

open Classical in
/-- Multiples of `d` in `J`, counted with a character, split into residue classes. -/
lemma inner_char (M : ℝ) (hM : 0 < M) (k : ℕ) (hk : 0 < k) (χ : DirichletCharacter ℂ k)
    (J : Set ℝ) (hJ : J.OrdConnected) (hJM : J ⊆ Set.Icc M (2 * M)) (d : ℕ) (hd : 0 < d) :
    ‖∑ m ∈ range (⌊2 * M⌋₊ + 1), (if d ∣ m then (if (m : ℝ) ∈ J then χ (m : ZMod k) else 0)
        else 0) -
      χ (d : ZMod k) * (((MeasureTheory.volume J).toReal / d / k : ℝ) : ℂ) *
        ∑ b ∈ range k, χ (b : ZMod k)‖ ≤ 3 * k := by
  set B := ⌊2 * M⌋₊ + 1
  set Jd := scaleSet d J
  have hJd : Jd.OrdConnected := scaleSet_ordConnected d J hJ
  have hJd0 : Jd ⊆ Set.Icc 0 (2 * M) := by
    intro y hy
    have h := scaleSet_subset d hd J M hJM hy
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
    refine ⟨le_trans (by positivity) h.1, h.2.trans ?_⟩
    have : M / d ≤ M := div_le_self hM.le hd1
    linarith
  -- reindex
  rw [sum_dvd_reindex B d hd]
  have e1 : ∑ t ∈ range B, (if d * t < B then (if ((d * t : ℕ) : ℝ) ∈ J then
        χ ((d * t : ℕ) : ZMod k) else 0) else 0) =
      χ (d : ZMod k) * ∑ t ∈ range B, (if (t : ℝ) ∈ Jd then χ (t : ZMod k) else 0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    have hmem : ((d * t : ℕ) : ℝ) ∈ J ↔ (t : ℝ) ∈ Jd := by
      simp only [Jd, scaleSet, Set.mem_preimage]; push_cast; rfl
    by_cases h : (t : ℝ) ∈ Jd
    · have hJ' : ((d * t : ℕ) : ℝ) ∈ J := hmem.2 h
      have hlt : d * t < B := by
        have := (hJM hJ').2
        have : d * t ≤ ⌊2 * M⌋₊ := Nat.le_floor this
        omega
      rw [if_pos hlt, if_pos hJ', if_pos h, Nat.cast_mul, map_mul]
    · rw [if_neg h, mul_zero]
      split_ifs with h1 h2
      · exact absurd (hmem.1 h2) h
      · rfl
      · rfl
  rw [e1]
  -- split into residues
  have e2 : ∑ t ∈ range B, (if (t : ℝ) ∈ Jd then χ (t : ZMod k) else 0) =
      ∑ b ∈ range k, χ (b : ZMod k) *
        (((range B).filter (fun t : ℕ => (t : ℝ) ∈ Jd ∧ t ≡ b [MOD k])).card : ℂ) := by
    rw [sum_residues (range B) k hk]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← Finset.sum_filter, Finset.filter_filter]
    rw [Finset.sum_congr rfl (g := fun _ => χ (b : ZMod k)) (fun (t : ℕ) ht => by
      rw [(ZMod.natCast_eq_natCast_iff t b k).2 (Finset.mem_filter.1 ht).2.1])]
    rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    congr 3
    ext t; simp only [and_comm]
  rw [e2, mul_assoc (χ (d : ZMod k)), ← mul_sub, norm_mul]
  have hχd : ‖χ (d : ZMod k)‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
  have hsum : ‖∑ b ∈ range k, χ (b : ZMod k) *
        (((range B).filter (fun t : ℕ => (t : ℝ) ∈ Jd ∧ t ≡ b [MOD k])).card : ℂ) -
      (((MeasureTheory.volume J).toReal / d / k : ℝ) : ℂ) * ∑ b ∈ range k, χ (b : ZMod k)‖ ≤
      3 * k := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ b ∈ range k, ‖χ (b : ZMod k) *
            (((range B).filter (fun t : ℕ => (t : ℝ) ∈ Jd ∧ t ≡ b [MOD k])).card : ℂ) -
          (((MeasureTheory.volume J).toReal / d / k : ℝ) : ℂ) * χ (b : ZMod k)‖
        ≤ ∑ b ∈ range k, (3 : ℝ) := by
          refine Finset.sum_le_sum fun b _ => ?_
          have hc := count_ordConnected Jd hJd (2 * M) hJd0 k hk b
          rw [scaleSet_volume d hd J] at hc
          rw [show χ (b : ZMod k) *
              (((range B).filter (fun t : ℕ => (t : ℝ) ∈ Jd ∧ t ≡ b [MOD k])).card : ℂ) -
              (((MeasureTheory.volume J).toReal / d / k : ℝ) : ℂ) * χ (b : ZMod k) =
              χ (b : ZMod k) * ((((((range B).filter
                (fun t : ℕ => (t : ℝ) ∈ Jd ∧ t ≡ b [MOD k])).card : ℝ) -
                (MeasureTheory.volume J).toReal / d / k : ℝ)) : ℂ) by push_cast; ring]
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          calc ‖χ (b : ZMod k)‖ * |((((range B).filter
                (fun t : ℕ => (t : ℝ) ∈ Jd ∧ t ≡ b [MOD k])).card : ℝ) -
                (MeasureTheory.volume J).toReal / d / k)| ≤ 1 * 3 :=
                mul_le_mul (DirichletCharacter.norm_le_one χ _) hc (abs_nonneg _) zero_le_one
            _ = 3 := one_mul 3
      _ = 3 * k := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
  calc ‖χ (d : ZMod k)‖ * _ ≤ 1 * (3 * k) := mul_le_mul hχd hsum (norm_nonneg _) zero_le_one
    _ = 3 * k := one_mul _

lemma esym_mono (P : Finset ℕ) (a b : ℕ → ℝ) (h : ∀ p ∈ P, 0 ≤ a p ∧ a p ≤ b p) (n : ℕ) :
    esym P a n ≤ esym P b n := by
  unfold esym
  refine Finset.sum_le_sum fun S hS => ?_
  split_ifs
  · exact Finset.prod_le_prod (fun p hp => (h p (Finset.mem_powerset.1 hS hp)).1)
      (fun p hp => (h p (Finset.mem_powerset.1 hS hp)).2)
  · exact le_refl _

/-- The primes up to `W`. -/
noncomputable def primesUpTo (W : ℝ) : Finset ℕ := (range (⌊W⌋₊ + 1)).filter Nat.Prime

lemma mem_primesUpTo (W : ℝ) (hW : 0 ≤ W) (p : ℕ) : p ∈ primesUpTo W ↔ p.Prime ∧ (p : ℝ) ≤ W := by
  simp only [primesUpTo, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h2, (Nat.le_floor_iff hW).1 (by omega)⟩
  · rintro ⟨h1, h2⟩; exact ⟨Nat.lt_succ_of_le (Nat.le_floor h2), h1⟩

lemma rough_iff (W : ℝ) (hW : 0 ≤ W) (m : ℕ) (hm : 0 < m) :
    IsRough W m ↔ ∀ p ∈ primesUpTo W, ¬ p ∣ m := by
  constructor
  · rintro ⟨_, h⟩ p hp hpm
    have hp' := (mem_primesUpTo W hW p).1 hp
    have := h p (Nat.mem_primeFactors.2 ⟨hp'.1, hpm, hm.ne'⟩)
    linarith [hp'.2]
  · intro h
    refine ⟨hm, fun p hp => ?_⟩
    have hp' := Nat.mem_primeFactors.1 hp
    by_contra hle
    exact h p ((mem_primesUpTo W hW p).2 ⟨hp'.1, not_lt.1 hle⟩) hp'.2.1

/-- `V(W) = (φ(k)/k) ∏_{p ≤ W, p ∤ k} (1 - 1/p)` when every prime factor of `k` is at most `W`. -/
lemma mertens_split (W : ℝ) (hW : 0 ≤ W) (k : ℕ) (hk : 0 < k)
    (hkW : ∀ p ∈ k.primeFactors, (p : ℝ) ≤ W) :
    mertensProduct W = ((Nat.totient k : ℝ) / k) *
      ∏ p ∈ primesUpTo W, (1 - (if p ∣ k then 0 else 1 / (p : ℝ))) := by
  classical
  have h1 : ∏ p ∈ primesUpTo W, (1 - (if p ∣ k then 0 else 1 / (p : ℝ))) =
      ∏ p ∈ (primesUpTo W).filter (fun p => ¬ p ∣ k), (1 - 1 / (p : ℝ)) := by
    rw [Finset.prod_filter]
    refine Finset.prod_congr rfl fun p _ => ?_
    split_ifs <;> simp
  have h2 : (primesUpTo W).filter (fun p => p ∣ k) = k.primeFactors := by
    ext p
    simp only [Finset.mem_filter, Nat.mem_primeFactors]
    constructor
    · rintro ⟨hp, hpk⟩; exact ⟨((mem_primesUpTo W hW p).1 hp).1, hpk, hk.ne'⟩
    · rintro ⟨hp, hpk, hk0⟩
      exact ⟨(mem_primesUpTo W hW p).2 ⟨hp, hkW p (Nat.mem_primeFactors.2 ⟨hp, hpk, hk0⟩)⟩, hpk⟩
  have h3 : ((Nat.totient k : ℝ) / k) = ∏ p ∈ k.primeFactors, (1 - 1 / (p : ℝ)) := by
    have := Nat.totient_eq_mul_prod_factors k
    have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
    have h := congrArg (fun q : ℚ => (q : ℝ)) this
    simp only [Rat.cast_natCast, Rat.cast_mul, Rat.cast_prod, Rat.cast_sub, Rat.cast_one,
      Rat.cast_inv] at h
    rw [h, mul_div_cancel_left₀ _ hk']
    simp [one_div]
  rw [h1, h3, ← h2, Finset.prod_filter_mul_prod_filter_not]
  rfl

lemma char_one_prod (k : ℕ) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    (1 : DirichletCharacter ℂ k) ((∏ p ∈ S, p : ℕ) : ZMod k) =
      ∏ p ∈ S, (if p ∣ k then (0 : ℂ) else 1) := by
  rw [Nat.cast_prod, map_prod]
  refine Finset.prod_congr rfl fun p hp => ?_
  by_cases h : p ∣ k
  · rw [if_pos h]
    apply MulChar.map_nonunit
    rw [ZMod.isUnit_iff_coprime, Nat.Prime.coprime_iff_not_dvd (hS p hp)]
    exact not_not.2 h
  · rw [if_neg h]
    apply MulChar.one_apply
    rw [ZMod.isUnit_iff_coprime, Nat.Prime.coprime_iff_not_dvd (hS p hp)]
    exact h

open Classical in
lemma err_count (M : ℝ) (hM : 0 < M) (k : ℕ) (χ : DirichletCharacter ℂ k)
    (J : Set ℝ) (hJ : J.OrdConnected) (hJM : J ⊆ Set.Icc M (2 * M)) (d : ℕ) (hd : 0 < d) :
    ∑ m ∈ range (⌊2 * M⌋₊ + 1),
        (if d ∣ m then ‖(if (m : ℝ) ∈ J then χ (m : ZMod k) else 0)‖ else 0) ≤
      (MeasureTheory.volume J).toReal / d + 3 := by
  have hJ0 : J ⊆ Set.Icc 0 (2 * M) := fun y hy => ⟨by linarith [(hJM hy).1], (hJM hy).2⟩
  have hc := count_ordConnected J hJ (2 * M) hJ0 d hd 0
  rw [abs_le] at hc
  have h1 : ∑ m ∈ range (⌊2 * M⌋₊ + 1),
        (if d ∣ m then ‖(if (m : ℝ) ∈ J then χ (m : ZMod k) else 0)‖ else 0) ≤
      ∑ m ∈ range (⌊2 * M⌋₊ + 1), (if (m : ℝ) ∈ J ∧ m ≡ 0 [MOD d] then (1 : ℝ) else 0) := by
    refine Finset.sum_le_sum fun m _ => ?_
    by_cases h1 : d ∣ m
    · by_cases h2 : (m : ℝ) ∈ J
      · rw [if_pos h1, if_pos h2, if_pos ⟨h2, Nat.modEq_zero_iff_dvd.2 h1⟩]
        exact DirichletCharacter.norm_le_one χ _
      · rw [if_pos h1, if_neg h2, norm_zero]; split_ifs <;> norm_num
    · rw [if_neg h1]; split_ifs <;> norm_num
  rw [Finset.sum_boole] at h1
  linarith [hc.2]

open Classical in
/-- (10.17) with explicit error, at Bonferroni level `n`. -/
lemma rcc_core (W : ℝ) (hW : 0 ≤ W) (M : ℝ) (hM : 0 < M) (k : ℕ) (hk : 0 < k)
    (hkW : ∀ p ∈ k.primeFactors, (p : ℝ) ≤ W) (χ : DirichletCharacter ℂ k)
    (J : Set ℝ) (hJ : J.OrdConnected) (hJM : J ⊆ Set.Icc M (2 * M)) (n : ℕ) :
    ‖(∑ m ∈ range (⌊2 * M⌋₊ + 1),
        if (m : ℝ) ∈ J ∧ IsRough W m then χ (m : ZMod k) else 0) -
      (if χ = 1 then ((mertensProduct W * (MeasureTheory.volume J).toReal : ℝ) : ℂ) else 0)‖ ≤
      2 * M * esym (primesUpTo W) (fun p => 1 / (p : ℝ)) n +
        3 * k * (((primesUpTo W).card : ℝ) + 1) ^ n := by
  set P := primesUpTo W
  set R := range (⌊2 * M⌋₊ + 1)
  set V := (MeasureTheory.volume J).toReal
  have hP : ∀ p ∈ P, p.Prime := fun p hp => ((mem_primesUpTo W hW p).1 hp).1
  have hV0 : 0 ≤ V := ENNReal.toReal_nonneg
  have hVM : V ≤ M := volume_le J M hM hJM
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  set c : ℕ → ℂ := fun m => if (m : ℝ) ∈ J then χ (m : ZMod k) else 0
  -- step 1: roughness is sieving by `P`
  have e0 : (∑ m ∈ R, if (m : ℝ) ∈ J ∧ IsRough W m then χ (m : ZMod k) else 0) =
      ∑ m ∈ R, (if ∀ p ∈ P, ¬ p ∣ m then c m else 0) := by
    refine Finset.sum_congr rfl fun m _ => ?_
    by_cases hmJ : (m : ℝ) ∈ J
    · have hm0 : 0 < m := by
        have := (hJM hmJ).1; exact_mod_cast (lt_of_lt_of_le hM this)
      simp only [c, hmJ, true_and, if_true, rough_iff W hW m hm0]
      rfl
    · simp [c, hmJ]
  have hdec := sieve_decomp R P hP n c
  rw [← e0] at hdec
  set Main := ∑ S ∈ P.powerset, (if S.card < n then (-1 : ℂ) ^ S.card *
      ∑ m ∈ R, (if (∏ p ∈ S, p) ∣ m then c m else 0) else 0)
  set Err := ∑ S ∈ P.powerset, (if S.card = n then
      ∑ m ∈ R, (if (∏ p ∈ S, p) ∣ m then ‖c m‖ else 0) else 0)
  have hdpos : ∀ S ∈ P.powerset, 0 < ∏ p ∈ S, p := fun S hS =>
    Finset.prod_pos fun p hp => (hP p (Finset.mem_powerset.1 hS hp)).pos
  -- step 2: the error of the truncation
  have hErr : Err ≤ V * esym P (fun p => 1 / (p : ℝ)) n +
      ∑ S ∈ P.powerset, (if S.card = n then (3 : ℝ) else 0) := by
    rw [esym, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun S hS => ?_
    split_ifs with h
    · have := err_count M hM k χ J hJ hJM _ (hdpos S hS)
      have hprod : ∏ p ∈ S, 1 / (p : ℝ) = 1 / ((∏ p ∈ S, p : ℕ) : ℝ) := by
        rw [Nat.cast_prod, Finset.prod_div_distrib, Finset.prod_const_one]
      rw [hprod, mul_one_div]
      exact this
    · simp
  -- step 3: the main terms
  set Sχ := ∑ b ∈ range k, χ (b : ZMod k)
  set Main' := ∑ S ∈ P.powerset, (if S.card < n then (-1 : ℂ) ^ S.card *
      (χ ((∏ p ∈ S, p : ℕ) : ZMod k) * ((V / (∏ p ∈ S, p : ℕ) / k : ℝ) : ℂ) * Sχ) else 0)
  have hMain : ‖Main - Main'‖ ≤ ∑ S ∈ P.powerset, (if S.card < n then 3 * (k : ℝ) else 0) := by
    rw [← Finset.sum_sub_distrib]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun S hS => ?_)
    split_ifs with h
    · rw [← mul_sub, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
      exact inner_char M hM k hk χ J hJ hJM _ (hdpos S hS)
    · simp
  have hMain' : ‖Main' - (if χ = 1 then ((mertensProduct W * V : ℝ) : ℂ) else 0)‖ ≤
      M * esym P (fun p => 1 / (p : ℝ)) n := by
    have hsum := sum_char_range k hk χ
    by_cases hχ : χ = 1
    · rw [if_pos hχ]
      rw [if_pos hχ] at hsum
      set a : ℕ → ℝ := fun p => if p ∣ k then 0 else 1 / (p : ℝ)
      have ha : ∀ p ∈ P, 0 ≤ a p ∧ a p ≤ 1 := by
        intro p hp
        have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (hP p hp).one_lt.le
        simp only [a]; split_ifs
        · norm_num
        · exact ⟨by positivity, by rw [div_le_one (by linarith)]; exact hp1⟩
      have hMain'eq : Main' = (((V / k * Nat.totient k) * bonfTrunc P a n : ℝ) : ℂ) := by
        simp only [Main', Sχ, hsum]
        rw [bonfTrunc, Finset.mul_sum, Complex.ofReal_sum]
        refine Finset.sum_congr rfl fun S hS => ?_
        split_ifs with h1
        · have hS' : ∀ p ∈ S, p.Prime := fun p hp => hP p (Finset.mem_powerset.1 hS hp)
          subst hχ
          rw [char_one_prod k S hS']
          have e1 : (∏ p ∈ S, (if p ∣ k then (0 : ℂ) else 1)) =
              ((∏ p ∈ S, (if p ∣ k then (0 : ℝ) else 1) : ℝ) : ℂ) := by
            rw [Complex.ofReal_prod]
            refine Finset.prod_congr rfl fun p _ => ?_
            split_ifs <;> simp
          have e2 : ∏ p ∈ S, a p =
              (∏ p ∈ S, (if p ∣ k then (0 : ℝ) else 1)) / ((∏ p ∈ S, p : ℕ) : ℝ) := by
            rw [Nat.cast_prod, div_eq_mul_inv, ← Finset.prod_inv_distrib,
              ← Finset.prod_mul_distrib]
            refine Finset.prod_congr rfl fun p _ => ?_
            simp only [a]; split_ifs <;> simp
          rw [e1, e2]
          push_cast
          ring
        · simp
      rw [hMain'eq]
      have hsplit : mertensProduct W = Nat.totient k / k * ∏ p ∈ P, (1 - a p) :=
        mertens_split W hW k hk hkW
      rw [hsplit]
      have hb := bonferroni a P ha n
      have hes : esym P a n ≤ esym P (fun p => 1 / (p : ℝ)) n := by
        refine esym_mono P a _ (fun p hp => ⟨(ha p hp).1, ?_⟩) n
        simp only [a]; split_ifs
        · have : (0 : ℝ) < p := by exact_mod_cast (hP p hp).pos
          positivity
        · exact le_refl _
      have hφ : (Nat.totient k : ℝ) / k ≤ 1 := by
        rw [div_le_one hk']; exact_mod_cast Nat.totient_le k
      have hφ0 : 0 ≤ (Nat.totient k : ℝ) / k := by positivity
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      have e : V / k * Nat.totient k * bonfTrunc P a n -
          (Nat.totient k / k * ∏ p ∈ P, (1 - a p)) * V =
          - (V * (Nat.totient k / k)) * ((∏ p ∈ P, (1 - a p)) - bonfTrunc P a n) := by ring
      rw [e, abs_mul, abs_neg, abs_of_nonneg (by positivity)]
      have hes0 : 0 ≤ esym P a n := esym_nonneg a P (fun p hp => (ha p hp).1) n
      calc V * (Nat.totient k / k) * |∏ p ∈ P, (1 - a p) - bonfTrunc P a n|
          ≤ M * 1 * esym P a n := by
            apply mul_le_mul (mul_le_mul hVM hφ hφ0 hM.le) hb (abs_nonneg _) (by positivity)
        _ ≤ M * esym P (fun p => 1 / (p : ℝ)) n := by
            rw [mul_one]; exact mul_le_mul_of_nonneg_left hes hM.le
    · rw [if_neg hχ]
      rw [if_neg hχ] at hsum
      have : Main' = 0 := by
        simp only [Main', Sχ, hsum, mul_zero]; simp
      rw [this, sub_zero, norm_zero]
      have : 0 ≤ esym P (fun p => 1 / (p : ℝ)) n :=
        esym_nonneg _ P (fun p _ => by positivity) n
      positivity
  -- step 4: assemble
  have hcount : ∑ S ∈ P.powerset, (if S.card = n then (3 : ℝ) else 0) +
      ∑ S ∈ P.powerset, (if S.card < n then 3 * (k : ℝ) else 0) ≤
      3 * k * ((P.card : ℝ) + 1) ^ n := by
    have hc := card_powerset_le P n
    rw [← Finset.sum_add_distrib, mul_comm (3 * (k : ℝ)) _]
    calc ∑ S ∈ P.powerset, ((if S.card = n then (3 : ℝ) else 0) +
          (if S.card < n then 3 * (k : ℝ) else 0))
        ≤ ∑ S ∈ P.powerset, (if S.card ≤ n then (1 : ℝ) else 0) * (3 * k) := by
          refine Finset.sum_le_sum fun S _ => ?_
          have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
          by_cases h1 : S.card = n
          · rw [if_pos h1, if_neg (by omega), if_pos (by omega)]; linarith
          · by_cases h2 : S.card < n
            · rw [if_neg h1, if_pos h2, if_pos (by omega)]; linarith
            · rw [if_neg h1, if_neg h2, if_neg (by omega)]; simp
      _ = (∑ S ∈ P.powerset, (if S.card ≤ n then (1 : ℝ) else 0)) * (3 * k) := by
          rw [Finset.sum_mul]
      _ ≤ ((P.card : ℝ) + 1) ^ n * (3 * k) := mul_le_mul_of_nonneg_right hc (by positivity)
  have htri : ‖(∑ m ∈ R, if (m : ℝ) ∈ J ∧ IsRough W m then χ (m : ZMod k) else 0) -
      (if χ = 1 then ((mertensProduct W * V : ℝ) : ℂ) else 0)‖ ≤
      ‖(∑ m ∈ R, if (m : ℝ) ∈ J ∧ IsRough W m then χ (m : ZMod k) else 0) - Main‖ +
        ‖Main - Main'‖ + ‖Main' - (if χ = 1 then ((mertensProduct W * V : ℝ) : ℂ) else 0)‖ := by
    have := norm_sub_le_norm_sub_add_norm_sub
      (∑ m ∈ R, if (m : ℝ) ∈ J ∧ IsRough W m then χ (m : ZMod k) else 0) Main
      (if χ = 1 then ((mertensProduct W * V : ℝ) : ℂ) else 0)
    have := norm_sub_le_norm_sub_add_norm_sub Main Main'
      (if χ = 1 then ((mertensProduct W * V : ℝ) : ℂ) else 0)
    linarith
  have hes0 : 0 ≤ esym P (fun p => 1 / (p : ℝ)) n := esym_nonneg _ P (fun p _ => by positivity) n
  have hVe : V * esym P (fun p => 1 / (p : ℝ)) n ≤ M * esym P (fun p => 1 / (p : ℝ)) n :=
    mul_le_mul_of_nonneg_right hVM hes0
  linarith

/-! ## Asymptotics -/

open Filter in
/-- `C · L^β ≤ L^α` eventually, for `0 ≤ β < α`. -/
lemma ev_rpow_lt (C β α : ℝ) (_hβ : 0 ≤ β) (hβα : β < α) :
    ∀ᶠ L : ℝ in atTop, C * L ^ β ≤ L ^ α := by
  have hu := tendsto_rpow_atTop (show 0 < α - β by linarith)
  filter_upwards [eventually_ge_atTop (1 : ℝ), hu.eventually_ge_atTop C] with L hL hC
  have hL0 : 0 < L := by linarith
  have e : L ^ α = L ^ (α - β) * L ^ β := by rw [← rpow_add hL0]; ring_nf
  rw [e]
  exact mul_le_mul_of_nonneg_right hC (by positivity)

lemma log_le_rpow (L ε : ℝ) (hL : 0 ≤ L) (hε : 0 < ε) : log L ≤ L ^ ε / ε :=
  Real.log_le_rpow_div hL hε

open Filter in
lemma rcc_eventually (w A₀ A₁ : ℝ) (hw : 0 < w) (hA₀ : 0 < A₀) (hA₁ : 0 < A₁) :
    ∀ᶠ L : ℝ in atTop, 1 ≤ L ∧ A₀ * log L ≤ L ^ (0.24 : ℝ) ∧
      8 * (1 + L ^ (0.24 : ℝ)) ≤ L ^ (1 / 2 : ℝ) ∧ A₁ * log L ≤ L ^ (1 / 2 : ℝ) ∧
      log 3 + A₀ * log L + (L ^ (1 / 2 : ℝ) + 1) * (L ^ (0.24 : ℝ) + 2) + A₁ * log L ≤ w * L := by
  filter_upwards [eventually_ge_atTop (1 : ℝ), ev_rpow_lt (A₀ / 0.12) 0.12 0.24 (by norm_num)
    (by norm_num), ev_rpow_lt 16 0.24 (1 / 2) (by norm_num) (by norm_num),
    ev_rpow_lt (4 * A₁) (1 / 4) (1 / 2) (by norm_num) (by norm_num),
    ev_rpow_lt ((8 + 2 * A₀ + 2 * A₁) / w) 0.74 1 (by norm_num) (by norm_num)]
    with L hL1 h2 h3 h4 h5
  have hL0 : 0 ≤ L := by linarith
  have r24 : 1 ≤ L ^ (0.24 : ℝ) := one_le_rpow hL1 (by norm_num)
  have r12 : 1 ≤ L ^ (0.12 : ℝ) := one_le_rpow hL1 (by norm_num)
  have r74 : 1 ≤ L ^ (0.74 : ℝ) := one_le_rpow hL1 (by norm_num)
  have r50 : 1 ≤ L ^ (1 / 2 : ℝ) := one_le_rpow hL1 (by norm_num)
  have r25 : 0 ≤ L ^ (1 / 4 : ℝ) := by positivity
  have hlog0 : 0 ≤ log L := log_nonneg hL1
  refine ⟨hL1, ?_, ?_, ?_, ?_⟩
  · have := log_le_rpow L 0.12 hL0 (by norm_num)
    have : A₀ * log L ≤ A₀ / 0.12 * L ^ (0.12 : ℝ) := by
      calc A₀ * log L ≤ A₀ * (L ^ (0.12 : ℝ) / 0.12) := mul_le_mul_of_nonneg_left this hA₀.le
        _ = A₀ / 0.12 * L ^ (0.12 : ℝ) := by ring
    linarith
  · linarith
  · have := log_le_rpow L (1 / 4) hL0 (by norm_num)
    have : A₁ * log L ≤ 4 * A₁ * L ^ (1 / 4 : ℝ) := by
      calc A₁ * log L ≤ A₁ * (L ^ (1 / 4 : ℝ) / (1 / 4)) := mul_le_mul_of_nonneg_left this hA₁.le
        _ = 4 * A₁ * L ^ (1 / 4 : ℝ) := by ring
    linarith
  · have hl := log_le_rpow L 0.74 hL0 (by norm_num)
    have hl2 : log L ≤ 2 * L ^ (0.74 : ℝ) := by
      have : L ^ (0.74 : ℝ) / 0.74 ≤ 2 * L ^ (0.74 : ℝ) := by
        rw [div_le_iff₀ (by norm_num)]; nlinarith
      linarith
    have hprod : (L ^ (1 / 2 : ℝ) + 1) * (L ^ (0.24 : ℝ) + 2) ≤ 6 * L ^ (0.74 : ℝ) := by
      have e : L ^ (0.74 : ℝ) = L ^ (1 / 2 : ℝ) * L ^ (0.24 : ℝ) := by
        rw [← rpow_add (by linarith)]; norm_num
      rw [e]; nlinarith
    have h3' : log 3 ≤ 2 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num); linarith
    have : (8 + 2 * A₀ + 2 * A₁) * L ^ (0.74 : ℝ) ≤ w * L := by
      have h5' := h5
      rw [rpow_one] at h5'
      rw [div_mul_eq_mul_div, div_le_iff₀ hw] at h5'
      linarith
    nlinarith

lemma recip_sum_le (W : ℝ) (hW : 1 ≤ W) :
    ∑ p ∈ primesUpTo W, 1 / (p : ℝ) ≤ 1 + log W := by
  have h1 : ∑ p ∈ primesUpTo W, 1 / (p : ℝ) ≤ ∑ i ∈ Finset.Icc 1 ⌊W⌋₊, ((i : ℝ))⁻¹ := by
    simp only [one_div]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      have := (mem_primesUpTo W (by linarith) p).1 hp
      simp only [Finset.mem_Icc]
      exact ⟨this.1.one_lt.le, Nat.le_floor this.2⟩
    · intro i _ _; positivity
  have h2 : ∑ i ∈ Finset.Icc 1 ⌊W⌋₊, ((i : ℝ))⁻¹ = (harmonic ⌊W⌋₊ : ℝ) := by
    rw [harmonic_eq_sum_Icc]; push_cast; rfl
  have h3 := harmonic_le_one_add_log ⌊W⌋₊
  have h4 : log (⌊W⌋₊ : ℝ) ≤ log W := by
    have : (1 : ℝ) ≤ ⌊W⌋₊ := by exact_mod_cast (Nat.floor_pos.2 hW)
    exact log_le_log (by linarith) (Nat.floor_le (by linarith))
  linarith

lemma card_primesUpTo_le (W : ℝ) (hW : 0 ≤ W) : ((primesUpTo W).card : ℝ) ≤ W + 1 := by
  have h : (primesUpTo W).card ≤ ⌊W⌋₊ + 1 :=
    (Finset.card_filter_le _ _).trans (Finset.card_range _).le
  have : ((⌊W⌋₊ + 1 : ℕ) : ℝ) ≤ W + 1 := by push_cast; linarith [Nat.floor_le hW]
  exact (Nat.cast_le.2 h).trans this

end ArtinPrimitiveRoots.A106S

namespace ArtinPrimitiveRoots

open Real A106S

end ArtinPrimitiveRoots
end

section
open ArtinPrimitiveRoots
open Real A106S
open Classical in
theorem solution (wMinus wPlus : ℝ) (hw : 0 < wMinus) (hww : wMinus < wPlus)
    (hwPlus : wPlus < 1) :
    ∀ A₀ A₁ : ℝ, 0 < A₀ → 0 < A₁ →
      ∃ K x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      ∀ M : ℝ, 0 < M → wMinus ≤ log M / log x → log (2 * M) / log x ≤ wPlus →
      ∀ k : ℕ, 0 < k → (k : ℝ) ≤ log x ^ A₀ → ∀ χ : DirichletCharacter ℂ k,
      ∀ J : Set ℝ, J.OrdConnected → J ⊆ Set.Icc M (2 * M) →
        ‖(∑ m ∈ Finset.range (⌊2 * M⌋₊ + 1),
            if (m : ℝ) ∈ J ∧ IsRough (sieveLevel x) m then χ (m : ZMod k) else 0) -
          (if χ = 1 then
            ((mertensProduct (sieveLevel x) * (MeasureTheory.volume J).toReal : ℝ) : ℂ)
          else 0)‖ ≤ K * (M * log x ^ (-A₁)) := by
  intro A₀ A₁ hA₀ hA₁
  obtain ⟨L₀, hL₀⟩ := Filter.eventually_atTop.1 (rcc_eventually wMinus A₀ A₁ hw hA₀ hA₁)
  refine ⟨3, max (exp L₀) (exp 1), fun x hx M hM hMlo _ k hk hkL χ J hJ hJM => ?_⟩
  have hx0 : 0 < x := lt_of_lt_of_le (exp_pos 1) (le_of_max_le_right hx)
  set L := log x with hLdef
  have hLL₀ : L₀ ≤ L := by
    rw [hLdef, ← log_exp L₀]; exact log_le_log (exp_pos _) (le_of_max_le_left hx)
  obtain ⟨hL1, hF2, hF3, hF4, hF5⟩ := hL₀ L hLL₀
  have hL0 : 0 < L := by linarith
  set W := sieveLevel x with hWdef
  have hWexp : W = exp (L ^ (0.24 : ℝ)) := rfl
  have hW1 : 1 ≤ W := by rw [hWexp]; exact one_le_exp (by positivity)
  have hW0 : 0 ≤ W := by linarith
  have hlogW : log W = L ^ (0.24 : ℝ) := by rw [hWexp, log_exp]
  -- k ≤ W
  have hkLA : (k : ℝ) ≤ exp (A₀ * log L) := by
    rw [mul_comm, ← rpow_def_of_pos hL0]; exact hkL
  have hkW' : (k : ℝ) ≤ W := by rw [hWexp]; exact hkLA.trans (exp_le_exp.2 hF2)
  have hkW : ∀ p ∈ k.primeFactors, (p : ℝ) ≤ W := by
    intro p hp
    have : p ≤ k := Nat.le_of_dvd hk (Nat.dvd_of_mem_primeFactors hp)
    exact (Nat.cast_le.2 this).trans hkW'
  -- the truncation level
  set n := ⌈L ^ (1 / 2 : ℝ)⌉₊ with hn
  have hn1 : L ^ (1 / 2 : ℝ) ≤ n := Nat.le_ceil _
  have hn2 : (n : ℝ) < L ^ (1 / 2 : ℝ) + 1 := Nat.ceil_lt_add_one (by positivity)
  have core := rcc_core W hW0 M hM k hk hkW χ J hJ hJM n
  -- the Bonferroni error
  have hs := recip_sum_le W hW1
  rw [hlogW] at hs
  have hs0 : 0 ≤ ∑ p ∈ primesUpTo W, 1 / (p : ℝ) := Finset.sum_nonneg fun p _ => by positivity
  have he1 := esym_le (fun p => 1 / (p : ℝ)) (primesUpTo W) (fun p _ => by positivity) n
  have he2 := pow_div_factorial_le (∑ p ∈ primesUpTo W, 1 / (p : ℝ)) hs0 n (by linarith)
  have he3 : exp (-(n : ℝ)) ≤ L ^ (-A₁) := by
    rw [rpow_def_of_pos hL0]
    apply exp_le_exp.2
    linarith
  have hesym : esym (primesUpTo W) (fun p => 1 / (p : ℝ)) n ≤ L ^ (-A₁) := by linarith
  -- M is large
  have hlogM : wMinus * L ≤ log M := by
    rwa [le_div_iff₀ hL0] at hMlo
  have hcard := card_primesUpTo_le W hW0
  have hpow : (((primesUpTo W).card : ℝ) + 1) ^ n ≤ (W + 2) ^ n :=
    pow_le_pow_left₀ (by positivity) (by linarith) n
  have hlogW2 : log (W + 2) ≤ L ^ (0.24 : ℝ) + 2 := by
    have h3 : W + 2 ≤ 3 * W := by linarith
    have : log (W + 2) ≤ log 3 + log W := by
      rw [← log_mul (by norm_num) (by linarith)]; exact log_le_log (by linarith) h3
    have h3' : log 3 ≤ 2 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num); linarith
    linarith
  have hlogk : log k ≤ A₀ * log L := by
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    have := log_le_log hk0 hkLA
    rwa [log_exp] at this
  have hbig : 3 * (k : ℝ) * (W + 2) ^ n ≤ M * L ^ (-A₁) := by
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    have lhs : 3 * (k : ℝ) * (W + 2) ^ n = exp (log 3 + log k + n * log (W + 2)) := by
      rw [exp_add, exp_add, exp_log (by norm_num), exp_log hk0, ← log_pow,
        exp_log (by positivity)]
    have rhs : M * L ^ (-A₁) = exp (log M - A₁ * log L) := by
      rw [exp_sub, exp_log hM, rpow_def_of_pos hL0, div_eq_mul_inv, ← exp_neg]; ring_nf
    rw [lhs, rhs]
    apply exp_le_exp.2
    have hlw : 0 ≤ log (W + 2) := log_nonneg (by linarith)
    have : (n : ℝ) * log (W + 2) ≤ (L ^ (1 / 2 : ℝ) + 1) * (L ^ (0.24 : ℝ) + 2) :=
      mul_le_mul hn2.le hlogW2 hlw (by positivity)
    linarith
  calc _ ≤ 2 * M * esym (primesUpTo W) (fun p => 1 / (p : ℝ)) n +
        3 * k * (((primesUpTo W).card : ℝ) + 1) ^ n := core
    _ ≤ 2 * M * L ^ (-A₁) + 3 * k * (W + 2) ^ n := by
        gcongr
    _ ≤ 3 * (M * L ^ (-A₁)) := by linarith
end
