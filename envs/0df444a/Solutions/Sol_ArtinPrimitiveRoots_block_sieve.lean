-- Prove2me | solution 1 for ArtinPrimitiveRoots.block_sieve
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T10:20:42.331229+00:00
-- url     : https://prove2.me/submissions/74113848-7d4d-4986-81d2-1ce1f62e91ed

import Mathlib

/-!
# Block sieve (OpenAI, "Primitive roots for every admissible integer base", Lemma 11.1)

Following the paper's proof (Ford–Halberstam product inequalities): blocks of primes
`B_j = P ∩ (z^{2^{-j-1}}, z^{2^{-j}}]`, truncated inclusion–exclusion of even degree
`h_j = (j+1) H` in each block, and the product over blocks.
-/

namespace ArtinPrimitiveRoots.BlockSieveAux

open Finset Real
open scoped Nat
open Classical

/-! ## Single-block combinatorics -/

/-- Coefficient of the truncated inclusion–exclusion polynomial `U_h`. -/
noncomputable def cU (h : ℕ) (J : Finset ℕ) : ℝ := if J.card ≤ h then (-1 : ℝ) ^ J.card else 0

/-- Coefficient of the correction polynomial `T_h` (unsigned degree `h+1` terms). -/
noncomputable def cT (h : ℕ) (J : Finset ℕ) : ℝ := if J.card = h + 1 then 1 else 0

/-- Indicator of the empty set. -/
noncomputable def ind (T : Finset ℕ) : ℝ := if T = ∅ then 1 else 0

/-- Value of the polynomial with coefficients `lam` at the set `T` of conditions that hold. -/
noncomputable def F (lam : Finset ℕ → ℝ) (T : Finset ℕ) : ℝ := ∑ J ∈ T.powerset, lam J

/-- Product Bernoulli weight of the event "exactly `T` holds" inside `Q`. -/
noncomputable def μ (g : ℕ → ℝ) (Q T : Finset ℕ) : ℝ :=
  ∏ p ∈ Q, if p ∈ T then g p else 1 - g p

/-- Main term (expectation) of the polynomial with coefficients `lam` on `Q`. -/
noncomputable def Mn (g : ℕ → ℝ) (Q : Finset ℕ) (lam : Finset ℕ → ℝ) : ℝ :=
  ∑ J ∈ Q.powerset, lam J * ∏ p ∈ J, g p

lemma alt_choose (n h : ℕ) :
    ∑ k ∈ range (h + 1), (-1 : ℝ) ^ k * ((n + 1).choose k : ℝ) = (-1) ^ h * (n.choose h : ℝ) := by
  induction h with
  | zero => simp
  | succ h ih =>
    rw [Finset.sum_range_succ, ih, Nat.choose_succ_succ]
    push_cast
    ring

lemma F_cU (h : ℕ) (T : Finset ℕ) :
    F (cU h) T = ∑ k ∈ range (h + 1), (-1 : ℝ) ^ k * (T.card.choose k : ℝ) := by
  have h1 : F (cU h) T = ∑ m ∈ range (T.card + 1),
      (T.card.choose m) • (fun k => if k ≤ h then (-1 : ℝ) ^ k else 0) m :=
    Finset.sum_powerset_apply_card (fun k => if k ≤ h then (-1 : ℝ) ^ k else 0)
  rw [h1]
  have hL1 : range (T.card + 1) ⊆ range (T.card + h + 2) := range_subset_range.2 (by omega)
  have hL2 : range (h + 1) ⊆ range (T.card + h + 2) := range_subset_range.2 (by omega)
  rw [Finset.sum_subset hL1, ← Finset.sum_subset hL2]
  · apply Finset.sum_congr rfl
    intro m hm
    have : m ≤ h := by simp at hm; omega
    simp [this, nsmul_eq_mul, mul_comm]
  · intro m _ hm
    have : ¬ m ≤ h := by simp at hm; omega
    simp [this]
  · intro m _ hm
    have : T.card < m := by simp at hm; omega
    simp [Nat.choose_eq_zero_of_lt this]

lemma F_cT (h : ℕ) (T : Finset ℕ) : F (cT h) T = (T.card.choose (h + 1) : ℝ) := by
  unfold F cT
  rw [Finset.sum_boole, ← Finset.powersetCard_eq_filter, Finset.card_powersetCard]

lemma block_ineq (h : ℕ) (he : Even h) (T : Finset ℕ) :
    0 ≤ ind T ∧ ind T ≤ F (cU h) T ∧ F (cU h) T - ind T ≤ F (cT h) T := by
  by_cases hT : T = ∅
  · subst hT
    simp [ind, F, cU, cT]
  · have hind : ind T = 0 := by simp [ind, hT]
    obtain ⟨m, hm⟩ : ∃ m, T.card = m + 1 :=
      ⟨T.card - 1, by have := Finset.card_pos.2 (Finset.nonempty_iff_ne_empty.2 hT); omega⟩
    rw [hind, F_cU, F_cT, hm, alt_choose, Even.neg_one_pow he, Nat.choose_succ_succ]
    push_cast
    refine ⟨le_refl _, by positivity, ?_⟩
    simp

/-! ## Expectations -/

lemma expect (g : ℕ → ℝ) (Q : Finset ℕ) (lam : Finset ℕ → ℝ) :
    Mn g Q lam = ∑ T ∈ Q.powerset, μ g Q T * F lam T := by
  induction Q using Finset.induction_on generalizing lam with
  | empty => simp [Mn, μ, F]
  | @insert a Q ha ih =>
    have hμ1 : ∀ T ∈ Q.powerset, μ g (insert a Q) T = (1 - g a) * μ g Q T := by
      intro T hT
      have haT : a ∉ T := fun h => ha (mem_powerset.1 hT h)
      rw [μ, prod_insert ha, if_neg haT]; rfl
    have hμ2 : ∀ T ∈ Q.powerset, μ g (insert a Q) (insert a T) = g a * μ g Q T := by
      intro T _
      rw [μ, prod_insert ha, if_pos (mem_insert_self a T), μ]
      congr 1
      apply prod_congr rfl
      intro p hp
      have hpa : p ≠ a := fun h => ha (h ▸ hp)
      simp [mem_insert, hpa]
    have hF : ∀ T ∈ Q.powerset,
        F lam (insert a T) = F lam T + F (fun J => lam (insert a J)) T := by
      intro T hT
      have haT : a ∉ T := fun h => ha (mem_powerset.1 hT h)
      simp only [F]; rw [sum_powerset_insert haT]
    have hM : Mn g (insert a Q) lam = Mn g Q lam + g a * Mn g Q (fun J => lam (insert a J)) := by
      simp only [Mn]
      rw [sum_powerset_insert ha, mul_sum]
      congr 1
      apply sum_congr rfl
      intro J hJ
      have haJ : a ∉ J := fun h => ha (mem_powerset.1 hJ h)
      rw [prod_insert haJ]; ring
    rw [hM, ih, ih, sum_powerset_insert ha, mul_sum, ← sum_add_distrib, ← sum_add_distrib]
    apply sum_congr rfl
    intro T hT
    rw [hμ1 T hT, hμ2 T hT, hF T hT]
    ring

lemma μ_nonneg (g : ℕ → ℝ) (Q T : Finset ℕ) (hg : ∀ p ∈ Q, 0 ≤ g p ∧ g p ≤ 1) :
    0 ≤ μ g Q T := by
  apply prod_nonneg
  intro p hp
  have := hg p hp
  split_ifs <;> linarith

lemma expect_ind (g : ℕ → ℝ) (Q : Finset ℕ) :
    ∑ T ∈ Q.powerset, μ g Q T * ind T = ∏ p ∈ Q, (1 - g p) := by
  simp [ind, μ]

lemma block_expect (g : ℕ → ℝ) (h : ℕ) (he : Even h) (Q : Finset ℕ)
    (hg : ∀ p ∈ Q, 0 ≤ g p ∧ g p ≤ 1) :
    ∏ p ∈ Q, (1 - g p) ≤ Mn g Q (cU h) ∧ Mn g Q (cU h) ≤ ∏ p ∈ Q, (1 - g p) + Mn g Q (cT h) := by
  rw [expect, expect, ← expect_ind g Q]
  constructor
  · apply sum_le_sum
    intro T _
    exact mul_le_mul_of_nonneg_left (block_ineq h he T).2.1 (μ_nonneg g Q T hg)
  · rw [← sum_add_distrib]
    apply sum_le_sum
    intro T _
    have := block_ineq h he T
    have := μ_nonneg g Q T hg
    nlinarith

lemma esymm_le (g : ℕ → ℝ) (Q : Finset ℕ) (hg : ∀ p ∈ Q, 0 ≤ g p) (m : ℕ) :
    Mn g Q (fun J => if J.card = m then 1 else 0) ≤ (∑ p ∈ Q, g p) ^ m / (m ! : ℝ) := by
  have bern : ∀ (x y : ℝ), 0 ≤ x → 0 ≤ y → ∀ n : ℕ,
      x ^ (n + 1) + (n + 1) * y * x ^ n ≤ (x + y) ^ (n + 1) := by
    intro x y hx hy n
    induction n with
    | zero => simp
    | succ n ih =>
      have h1 : 0 ≤ x ^ n := pow_nonneg hx n
      have h2 : (x + y) * (x ^ (n + 1) + (n + 1) * y * x ^ n) ≤ (x + y) * (x + y) ^ (n + 1) :=
        mul_le_mul_of_nonneg_left ih (by linarith)
      have h3 : 0 ≤ (n + 1 : ℝ) * y * y * x ^ n := by positivity
      push_cast
      rw [pow_succ (x + y) (n + 1), pow_succ x (n + 1), pow_succ x n]
      rw [pow_succ x n] at h2
      nlinarith
  induction Q using Finset.induction_on generalizing m with
  | empty => cases m <;> simp [Mn]
  | @insert a Q ha ih =>
    have hg' : ∀ p ∈ Q, 0 ≤ g p := fun p hp => hg p (mem_insert_of_mem hp)
    have hga : 0 ≤ g a := hg a (mem_insert_self a Q)
    have hsplit : ∀ m, Mn g (insert a Q) (fun J => if J.card = m then 1 else 0) =
        Mn g Q (fun J => if J.card = m then 1 else 0) +
          g a * Mn g Q (fun J => if J.card + 1 = m then 1 else 0) := by
      intro m
      simp only [Mn]
      rw [sum_powerset_insert ha, mul_sum]
      congr 1
      apply sum_congr rfl
      intro J hJ
      have haJ : a ∉ J := fun h => ha (mem_powerset.1 hJ h)
      rw [prod_insert haJ, card_insert_of_notMem haJ]; ring
    have hs : 0 ≤ ∑ p ∈ Q, g p := sum_nonneg hg'
    rw [hsplit, sum_insert ha]
    cases m with
    | zero =>
      have h0 : Mn g Q (fun J => if J.card + 1 = 0 then 1 else 0) = 0 := by simp [Mn]
      rw [h0]
      have := ih hg' 0
      simpa using this
    | succ k =>
      simp only [Nat.add_right_cancel_iff]
      have i1 := ih hg' (k + 1)
      have i2 := ih hg' k
      have hb := bern (∑ p ∈ Q, g p) (g a) hs hga k
      have hk : (0 : ℝ) < (k ! : ℝ) := by exact_mod_cast Nat.factorial_pos k
      rw [Nat.factorial_succ] at i1 ⊢
      push_cast at i1 ⊢
      have e1 : g a * ((∑ p ∈ Q, g p) ^ k / (k ! : ℝ)) =
          ((k + 1) * g a * (∑ p ∈ Q, g p) ^ k) / ((k + 1) * (k ! : ℝ)) := by
        field_simp
      calc Mn g Q (fun J => if J.card = k + 1 then 1 else 0) +
            g a * Mn g Q (fun J => if J.card = k then 1 else 0)
          ≤ (∑ p ∈ Q, g p) ^ (k + 1) / ((k + 1) * (k ! : ℝ)) +
            g a * ((∑ p ∈ Q, g p) ^ k / (k ! : ℝ)) :=
            add_le_add i1 (mul_le_mul_of_nonneg_left i2 hga)
        _ = ((∑ p ∈ Q, g p) ^ (k + 1) + (k + 1) * g a * (∑ p ∈ Q, g p) ^ k) /
              ((k + 1) * (k ! : ℝ)) := by rw [e1, add_div]
        _ ≤ (g a + ∑ p ∈ Q, g p) ^ (k + 1) / ((k + 1) * (k ! : ℝ)) := by
            apply div_le_div_of_nonneg_right _ (by positivity)
            rw [add_comm (g a)]; exact hb

lemma cT_nonneg (h : ℕ) (J : Finset ℕ) : 0 ≤ cT h J := by
  unfold cT; split_ifs <;> norm_num

lemma Mn_cT_nonneg (g : ℕ → ℝ) (h : ℕ) (Q : Finset ℕ) (hg : ∀ p ∈ Q, 0 ≤ g p) :
    0 ≤ Mn g Q (cT h) := by
  apply sum_nonneg
  intro J _
  exact mul_nonneg (cT_nonneg h J) (prod_nonneg fun p hp => hg p (mem_powerset.1 ‹_› hp))

lemma block_lower (g : ℕ → ℝ) (η C : ℝ) (hη : 0 < η) (Q : Finset ℕ)
    (hg : ∀ p ∈ Q, 0 ≤ g p ∧ g p ≤ 1 - η) (hs : ∑ p ∈ Q, g p ≤ C) :
    exp (-(C / η)) ≤ ∏ p ∈ Q, (1 - g p) := by
  have per : ∀ p ∈ Q, exp (-(g p / η)) ≤ 1 - g p := by
    intro p hp
    obtain ⟨hu0, hu1⟩ := hg p hp
    set u := g p
    have h1 : 1 + u / η ≤ exp (u / η) := by linarith [add_one_le_exp (u / η)]
    have h2 : 1 ≤ (1 - u) * (1 + u / η) := by
      rw [show (1 - u) * (1 + u / η) = 1 + u * (1 - η - u) / η by field_simp; ring]
      have := div_nonneg (mul_nonneg hu0 (by linarith : (0:ℝ) ≤ 1 - η - u)) hη.le
      linarith
    have h3 : 1 ≤ (1 - u) * exp (u / η) := by
      have : (1 - u) * (1 + u / η) ≤ (1 - u) * exp (u / η) :=
        mul_le_mul_of_nonneg_left h1 (by linarith)
      linarith
    calc exp (-(u / η)) = exp (-(u / η)) * 1 := by ring
      _ ≤ exp (-(u / η)) * ((1 - u) * exp (u / η)) :=
          mul_le_mul_of_nonneg_left h3 (exp_pos _).le
      _ = (1 - u) * (exp (-(u / η)) * exp (u / η)) := by ring
      _ = 1 - u := by rw [← exp_add]; simp
  calc exp (-(C / η)) ≤ exp (∑ p ∈ Q, -(g p / η)) := by
        apply exp_le_exp.2
        rw [sum_neg_distrib, ← sum_div]
        exact neg_le_neg (div_le_div_of_nonneg_right hs hη.le)
    _ = ∏ p ∈ Q, exp (-(g p / η)) := exp_sum _ _
    _ ≤ ∏ p ∈ Q, (1 - g p) := prod_le_prod (fun _ _ => (exp_pos _).le) per

/-! ## Products over blocks -/

lemma prod_ite_add (K : Finset ℕ) (j₀ : ℕ) (hj₀ : j₀ ∈ K) (A B : ℕ → ℝ) :
    ∏ k ∈ K, (if j₀ = k then A k + B k else A k) =
      ∏ k ∈ K, A k + ∏ k ∈ K, (if j₀ = k then B k else A k) := by
  rw [← mul_prod_erase K _ hj₀, ← mul_prod_erase K A hj₀, ← mul_prod_erase K _ hj₀]
  have e1 : ∏ k ∈ K.erase j₀, (if j₀ = k then A k + B k else A k) = ∏ k ∈ K.erase j₀, A k :=
    prod_congr rfl (fun k hk => if_neg (fun h => (mem_erase.1 hk).1 h.symm))
  have e2 : ∏ k ∈ K.erase j₀, (if j₀ = k then B k else A k) = ∏ k ∈ K.erase j₀, A k :=
    prod_congr rfl (fun k hk => if_neg (fun h => (mem_erase.1 hk).1 h.symm))
  rw [e1, e2]; simp only [if_true]; ring

lemma key (blk : ℕ → ℕ) (K : Finset ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, blk p ∈ K)
    (f : ℕ → Finset ℕ → ℝ) :
    ∑ J ∈ P.powerset, ∏ k ∈ K, f k (J.filter (fun p => blk p = k)) =
      ∏ k ∈ K, ∑ J ∈ (P.filter (fun p => blk p = k)).powerset, f k J := by
  induction P using Finset.induction_on generalizing f with
  | empty => simp
  | @insert a P ha ih =>
    have hP' : ∀ p ∈ P, blk p ∈ K := fun p hp => hP p (mem_insert_of_mem hp)
    have haK : blk a ∈ K := hP a (mem_insert_self a P)
    rw [sum_powerset_insert ha]
    have h2 : ∀ J ∈ P.powerset, ∏ k ∈ K, f k ((insert a J).filter (fun p => blk p = k)) =
        ∏ k ∈ K, (fun k S => if blk a = k then f k (insert a S) else f k S) k
          (J.filter (fun p => blk p = k)) := by
      intro J _
      apply prod_congr rfl
      intro k _
      dsimp only
      rw [filter_insert]
      split_ifs <;> rfl
    rw [sum_congr rfl h2, ih hP' f,
      ih hP' (fun k S => if blk a = k then f k (insert a S) else f k S)]
    have h3 : ∀ k ∈ K, ∑ J ∈ ((insert a P).filter (fun p => blk p = k)).powerset, f k J =
        if blk a = k then (∑ J ∈ (P.filter (fun p => blk p = k)).powerset, f k J) +
          ∑ J ∈ (P.filter (fun p => blk p = k)).powerset, f k (insert a J)
        else ∑ J ∈ (P.filter (fun p => blk p = k)).powerset, f k J := by
      intro k _
      rw [filter_insert]
      split_ifs with h
      · exact sum_powerset_insert (fun hm => ha (mem_filter.1 hm).1) _
      · rfl
    rw [prod_congr rfl h3, prod_ite_add K (blk a) haK]
    congr 1
    apply prod_congr rfl
    intro k _
    split_ifs <;> rfl

lemma key_F (blk : ℕ → ℕ) (K : Finset ℕ) (T : Finset ℕ) (hT : ∀ p ∈ T, blk p ∈ K)
    (f : ℕ → Finset ℕ → ℝ) :
    F (fun J => ∏ k ∈ K, f k (J.filter (fun p => blk p = k))) T =
      ∏ k ∈ K, F (f k) (T.filter (fun p => blk p = k)) := by
  simp only [F]
  exact key blk K T hT f

lemma key_Mn (g : ℕ → ℝ) (blk : ℕ → ℕ) (K : Finset ℕ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, blk p ∈ K) (f : ℕ → Finset ℕ → ℝ) :
    Mn g P (fun J => ∏ k ∈ K, f k (J.filter (fun p => blk p = k))) =
      ∏ k ∈ K, Mn g (P.filter (fun p => blk p = k)) (f k) := by
  simp only [Mn]
  have h1 : ∀ J ∈ P.powerset, (∏ k ∈ K, f k (J.filter (fun p => blk p = k))) * ∏ p ∈ J, g p =
      ∏ k ∈ K, (fun k S => f k S * ∏ p ∈ S, g p) k (J.filter (fun p => blk p = k)) := by
    intro J hJ
    rw [← prod_fiberwise_of_maps_to (s := J) (t := K) (g := blk)
      (fun p hp => hP p (mem_powerset.1 hJ hp)) g, ← prod_mul_distrib]
  rw [sum_congr rfl h1, key blk K P hP (fun k S => f k S * ∏ p ∈ S, g p)]

lemma ind_prod (blk : ℕ → ℕ) (K : Finset ℕ) (T : Finset ℕ) (hT : ∀ p ∈ T, blk p ∈ K) :
    ind T = ∏ k ∈ K, ind (T.filter (fun p => blk p = k)) := by
  by_cases h : T = ∅
  · subst h; simp [ind]
  · obtain ⟨p, hp⟩ := Finset.nonempty_iff_ne_empty.2 h
    rw [show ind T = 0 by simp [ind, h]]
    symm
    apply prod_eq_zero (hT p hp)
    have : T.filter (fun q => blk q = blk p) ≠ ∅ :=
      Finset.nonempty_iff_ne_empty.1 ⟨p, mem_filter.2 ⟨hp, rfl⟩⟩
    rw [ind, if_neg this]

lemma telescope (s : Finset ℕ) (x y w : ℕ → ℝ) (hx : ∀ k ∈ s, 0 ≤ x k)
    (hxy : ∀ k ∈ s, x k ≤ y k) (hw : ∀ k ∈ s, y k - x k ≤ w k) :
    ∏ k ∈ s, y k - ∏ k ∈ s, x k ≤ ∑ j ∈ s, ∏ k ∈ s, (if k = j then w k else y k) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hx' : ∀ k ∈ s, 0 ≤ x k := fun k hk => hx k (mem_insert_of_mem hk)
    have hxy' : ∀ k ∈ s, x k ≤ y k := fun k hk => hxy k (mem_insert_of_mem hk)
    have hw' : ∀ k ∈ s, y k - x k ≤ w k := fun k hk => hw k (mem_insert_of_mem hk)
    have IH := ih hx' hxy' hw'
    have hxa := hx a (mem_insert_self a s)
    have hxya := hxy a (mem_insert_self a s)
    have hwa := hw a (mem_insert_self a s)
    have hX : 0 ≤ ∏ k ∈ s, x k := prod_nonneg hx'
    have hXY : ∏ k ∈ s, x k ≤ ∏ k ∈ s, y k := prod_le_prod hx' hxy'
    rw [sum_insert ha, prod_insert ha, prod_insert ha, prod_insert ha, if_pos rfl]
    have e1 : ∏ k ∈ s, (if k = a then w k else y k) = ∏ k ∈ s, y k :=
      prod_congr rfl (fun k hk => if_neg (fun (h : k = a) => ha (h ▸ hk)))
    have e2 : ∑ j ∈ s, ∏ k ∈ insert a s, (if k = j then w k else y k) =
        y a * ∑ j ∈ s, ∏ k ∈ s, (if k = j then w k else y k) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro j hj
      rw [prod_insert ha, if_neg (fun (h : a = j) => ha (h ▸ hj))]
    rw [e1, e2]
    nlinarith [mul_le_mul_of_nonneg_left IH (le_trans hxa hxya),
      mul_le_mul_of_nonneg_left hXY (by linarith : 0 ≤ w a), mul_le_mul_of_nonneg_right hwa hX]

lemma numeric (s : Finset ℕ) (a M t : ℕ → ℝ) (ha : ∀ k ∈ s, 0 < a k)
    (haM : ∀ k ∈ s, a k ≤ M k) (hMt : ∀ k ∈ s, M k ≤ a k + t k) (ht : ∀ k ∈ s, 0 ≤ t k) :
    ∏ k ∈ s, a k ≤ ∏ k ∈ s, M k ∧
    ∏ k ∈ s, M k ≤ (∏ k ∈ s, a k) * exp (∑ k ∈ s, t k / a k) ∧
    ∑ j ∈ s, ∏ k ∈ s, (if k = j then t k else M k) ≤
      (∏ k ∈ s, a k) * ((∑ k ∈ s, t k / a k) * exp (∑ k ∈ s, t k / a k)) := by
  have hY : ∀ k ∈ s, M k ≤ a k * exp (t k / a k) := by
    intro k hk
    have := add_one_le_exp (t k / a k)
    have ha' := ha k hk
    calc M k ≤ a k + t k := hMt k hk
      _ = a k * (t k / a k + 1) := by field_simp; ring
      _ ≤ a k * exp (t k / a k) := mul_le_mul_of_nonneg_left this ha'.le
  have hM0 : ∀ k ∈ s, 0 ≤ M k := fun k hk => le_trans (ha k hk).le (haM k hk)
  have hprodY : ∏ k ∈ s, (a k * exp (t k / a k)) =
      (∏ k ∈ s, a k) * exp (∑ k ∈ s, t k / a k) := by
    rw [prod_mul_distrib, exp_sum]
  refine ⟨prod_le_prod (fun k hk => (ha k hk).le) haM, ?_, ?_⟩
  · rw [← hprodY]; exact prod_le_prod hM0 hY
  · have per : ∀ j ∈ s, ∏ k ∈ s, (if k = j then t k else M k) ≤
        (t j / a j) * ((∏ k ∈ s, a k) * exp (∑ k ∈ s, t k / a k)) := by
      intro j hj
      calc ∏ k ∈ s, (if k = j then t k else M k)
          ≤ ∏ k ∈ s, ((if k = j then t k / a k else 1) * (a k * exp (t k / a k))) := by
            apply prod_le_prod
            · intro k hk; split_ifs
              · exact ht k hk
              · exact hM0 k hk
            · intro k hk
              split_ifs
              · have ha' := ha k hk
                have e : t k / a k * (a k * exp (t k / a k)) = t k * exp (t k / a k) := by
                  field_simp
                rw [e]
                nlinarith [one_le_exp (div_nonneg (ht k hk) ha'.le), ht k hk]
              · simpa using hY k hk
        _ = (∏ k ∈ s, (if k = j then t k / a k else 1)) * ∏ k ∈ s, (a k * exp (t k / a k)) :=
            prod_mul_distrib
        _ = _ := by rw [prod_ite_eq' s j, if_pos hj, hprodY]
    calc ∑ j ∈ s, ∏ k ∈ s, (if k = j then t k else M k)
        ≤ ∑ j ∈ s, (t j / a j) * ((∏ k ∈ s, a k) * exp (∑ k ∈ s, t k / a k)) := sum_le_sum per
      _ = _ := by rw [← sum_mul]; ring

/-! ## The sieve polynomials -/

noncomputable def lamU (blk : ℕ → ℕ) (K : Finset ℕ) (hh : ℕ → ℕ) (J : Finset ℕ) : ℝ :=
  ∏ k ∈ K, cU (hh k) (J.filter (fun p => blk p = k))

noncomputable def fk (hh : ℕ → ℕ) (j k : ℕ) : Finset ℕ → ℝ :=
  if k = j then cT (hh k) else cU (hh k)

noncomputable def kap (blk : ℕ → ℕ) (K : Finset ℕ) (hh : ℕ → ℕ) (j : ℕ) (J : Finset ℕ) : ℝ :=
  ∏ k ∈ K, fk hh j k (J.filter (fun p => blk p = k))

noncomputable def lamL (blk : ℕ → ℕ) (K : Finset ℕ) (hh : ℕ → ℕ) (J : Finset ℕ) : ℝ :=
  lamU blk K hh J - ∑ j ∈ K, kap blk K hh j J

/-- Support condition: degree at most `hh k` in each block, except one block of degree
at most `hh j₀ + 1`. -/
def Good (blk : ℕ → ℕ) (K : Finset ℕ) (hh : ℕ → ℕ) (J : Finset ℕ) : Prop :=
  ∃ j₀ : ℕ, ∀ k ∈ K, (J.filter (fun p => blk p = k)).card ≤ hh k + if k = j₀ then 1 else 0

lemma fk_abs (hh : ℕ → ℕ) (j k : ℕ) (S : Finset ℕ) : |fk hh j k S| ≤ 1 := by
  unfold fk
  by_cases hkj : k = j
  · rw [if_pos hkj]; unfold cT; split_ifs <;> simp
  · rw [if_neg hkj]; unfold cU; split_ifs <;> simp

lemma fk_ne (hh : ℕ → ℕ) (j k : ℕ) (S : Finset ℕ) (h : fk hh j k S ≠ 0) :
    S.card ≤ hh k + if k = j then 1 else 0 := by
  unfold fk at h
  by_cases hkj : k = j
  · rw [if_pos hkj] at h ⊢
    unfold cT at h
    split_ifs at h with h1
    · omega
    · exact absurd rfl h
  · rw [if_neg hkj] at h ⊢
    unfold cU at h
    split_ifs at h with h1
    · omega
    · exact absurd rfl h

lemma kap_coef (blk : ℕ → ℕ) (K : Finset ℕ) (hh : ℕ → ℕ) (j : ℕ) (J : Finset ℕ) :
    |kap blk K hh j J| ≤ 1 ∧ (kap blk K hh j J ≠ 0 → Good blk K hh J) := by
  refine ⟨?_, ?_⟩
  · rw [kap, abs_prod]; exact prod_le_one (fun _ _ => abs_nonneg _) (fun k _ => fk_abs _ _ _ _)
  · intro hne
    exact ⟨j, fun k hk => fk_ne hh j k _ (fun h0 => hne (prod_eq_zero hk h0))⟩

lemma lamU_coef (blk : ℕ → ℕ) (K : Finset ℕ) (hh : ℕ → ℕ) (J : Finset ℕ) :
    |lamU blk K hh J| ≤ 1 ∧ (lamU blk K hh J ≠ 0 → Good blk K hh J) := by
  have hc : ∀ h J, |cU h J| ≤ 1 := by intro h J; unfold cU; split_ifs <;> simp
  refine ⟨?_, ?_⟩
  · rw [lamU, abs_prod]; exact prod_le_one (fun _ _ => abs_nonneg _) (fun k _ => hc _ _)
  · intro hne
    refine ⟨0, fun k hk => ?_⟩
    have : cU (hh k) (J.filter (fun p => blk p = k)) ≠ 0 := fun h0 => hne (prod_eq_zero hk h0)
    unfold cU at this
    split_ifs at this with h1
    · omega
    · exact absurd rfl this

lemma lamL_coef (blk : ℕ → ℕ) (K : Finset ℕ) (hh : ℕ → ℕ) (J : Finset ℕ) :
    |lamL blk K hh J| ≤ 1 ∧ (lamL blk K hh J ≠ 0 → Good blk K hh J) := by
  by_cases hall : ∀ k ∈ K, (J.filter (fun p => blk p = k)).card ≤ hh k
  · have h0 : ∀ j ∈ K, kap blk K hh j J = 0 := by
      intro j hj
      apply prod_eq_zero hj
      have := hall j hj
      rw [fk, if_pos rfl, cT, if_neg (by omega)]
    have : lamL blk K hh J = lamU blk K hh J := by
      rw [lamL, sum_eq_zero h0, sub_zero]
    rw [this]; exact lamU_coef blk K hh J
  · push Not at hall
    obtain ⟨k0, hk0, hgt⟩ := hall
    have hU : lamU blk K hh J = 0 := by
      apply prod_eq_zero hk0
      rw [cU, if_neg (by omega)]
    have hkap : ∀ j ∈ K, j ≠ k0 → kap blk K hh j J = 0 := by
      intro j _ hj
      apply prod_eq_zero hk0
      rw [fk, if_neg (fun h => hj h.symm), cU, if_neg (by omega)]
    have : lamL blk K hh J = - kap blk K hh k0 J := by
      rw [lamL, hU, sum_eq_single_of_mem k0 hk0 hkap]; ring
    rw [this, abs_neg]
    obtain ⟨h1, h2⟩ := kap_coef blk K hh k0 J
    exact ⟨h1, fun hne => h2 (fun h => hne (by rw [h, neg_zero]))⟩

lemma geom_weighted (N : ℕ) : ∑ k ∈ range N, ((k : ℝ) + 1) * (1 / 2) ^ k ≤ 4 := by
  have : ∀ N : ℕ, ∑ k ∈ range N, ((k : ℝ) + 1) * (1 / 2) ^ k =
      4 - 2 * ((N : ℝ) + 2) * (1 / 2) ^ N := by
    intro N
    induction N with
    | zero => norm_num
    | succ n ih => rw [sum_range_succ, ih, pow_succ]; push_cast; ring
  rw [this]
  have : 0 ≤ 2 * ((N : ℝ) + 2) * (1 / 2) ^ N := by positivity
  linarith

lemma good_size (blk : ℕ → ℕ) (N H : ℕ) (z : ℝ) (hz : 1 ≤ z) (J : Finset ℕ)
    (hJ : ∀ p ∈ J, blk p < N) (hJz : ∀ p ∈ J, (p : ℝ) ≤ z ^ ((1 / 2 : ℝ) ^ (blk p)))
    (hg : Good blk (range N) (fun k => (k + 1) * H) J) :
    ((∏ p ∈ J, p : ℕ) : ℝ) ≤ z ^ (4 * H + 2) := by
  obtain ⟨j₀, hj₀⟩ := hg
  have hz0 : 0 < z := by linarith
  rw [Nat.cast_prod]
  have h1 : ∏ p ∈ J, (p : ℝ) ≤ ∏ p ∈ J, z ^ ((1 / 2 : ℝ) ^ (blk p)) :=
    prod_le_prod (fun p _ => Nat.cast_nonneg p) hJz
  have h2 : ∏ p ∈ J, z ^ ((1 / 2 : ℝ) ^ (blk p)) = z ^ (∑ p ∈ J, (1 / 2 : ℝ) ^ (blk p)) :=
    (Real.rpow_sum_of_pos hz0 _ _).symm
  have h3 : ∑ p ∈ J, (1 / 2 : ℝ) ^ (blk p) =
      ∑ k ∈ range N, ((J.filter (fun p => blk p = k)).card : ℝ) * (1 / 2) ^ k := by
    rw [← sum_fiberwise_of_maps_to (s := J) (t := range N) (g := blk)
      (fun p hp => mem_range.2 (hJ p hp))]
    apply sum_congr rfl
    intro k _
    rw [sum_congr rfl (fun p hp => by rw [(mem_filter.1 hp).2]), sum_const, nsmul_eq_mul]
  have h4 : ∑ k ∈ range N, ((J.filter (fun p => blk p = k)).card : ℝ) * (1 / 2) ^ k ≤
      ∑ k ∈ range N, (((k : ℝ) + 1) * H * (1 / 2) ^ k +
        (if k = j₀ then (1 : ℝ) else 0) * (1 / 2) ^ k) := by
    apply sum_le_sum
    intro k hk
    have := hj₀ k hk
    have hc : ((J.filter (fun p => blk p = k)).card : ℝ) ≤
        ((k : ℝ) + 1) * H + (if k = j₀ then 1 else 0) := by
      by_cases hkj : k = j₀
      · rw [if_pos hkj] at this ⊢; exact_mod_cast this
      · rw [if_neg hkj] at this ⊢; exact_mod_cast this
    have := mul_le_mul_of_nonneg_right hc (pow_nonneg (by norm_num : (0:ℝ) ≤ 1 / 2) k)
    linarith
  have h5 : ∑ k ∈ range N, (((k : ℝ) + 1) * H * (1 / 2) ^ k +
        (if k = j₀ then (1 : ℝ) else 0) * (1 / 2) ^ k) ≤ 4 * H + 1 := by
    rw [sum_add_distrib]
    have e1 : ∑ k ∈ range N, ((k : ℝ) + 1) * H * (1 / 2) ^ k =
        H * ∑ k ∈ range N, ((k : ℝ) + 1) * (1 / 2) ^ k := by
      rw [mul_sum]; apply sum_congr rfl; intro k _; ring
    have e2 : ∑ k ∈ range N, (if k = j₀ then (1:ℝ) else 0) * (1 / 2) ^ k ≤ 1 := by
      simp only [ite_mul, one_mul, zero_mul]
      rw [sum_ite_eq']
      split_ifs
      · exact pow_le_one₀ (by norm_num) (by norm_num)
      · norm_num
    rw [e1]
    have := geom_weighted N
    have hH : (0:ℝ) ≤ H := Nat.cast_nonneg H
    nlinarith
  calc ∏ p ∈ J, (p : ℝ) ≤ z ^ (∑ p ∈ J, (1 / 2 : ℝ) ^ (blk p)) := h1.trans_eq h2
    _ ≤ z ^ (((4 * H + 2 : ℕ)) : ℝ) := by
        apply Real.rpow_le_rpow_of_exponent_le hz
        rw [h3]; push_cast; linarith [h4, h5]
    _ = z ^ (4 * H + 2) := Real.rpow_natCast z _

/-! ## Transfer to the weighted set -/

/-- The remainder `E(d)`. -/
noncomputable def Ew {α : Type*} (Aset : Finset α) (ω : α → ℝ) (bad : ℕ → α → Prop) (X' : ℝ)
    (g : ℕ → ℝ) (d : ℕ) : ℝ :=
  (∑ a ∈ Aset.filter (fun a => ∀ p ∈ d.primeFactors, bad p a), ω a) - X' * ∏ p ∈ d.primeFactors, g p

lemma transfer {α : Type*} (Aset : Finset α) (ω : α → ℝ) (Pset : Finset ℕ)
    (hP : ∀ p ∈ Pset, p.Prime) (bad : ℕ → α → Prop) (X' : ℝ) (g : ℕ → ℝ)
    (lam : Finset ℕ → ℝ) :
    ∑ a ∈ Aset, ω a * F lam (Pset.filter (fun p => bad p a)) =
      X' * Mn g Pset lam + ∑ J ∈ Pset.powerset, lam J * Ew Aset ω bad X' g (∏ p ∈ J, p) := by
  have hA : ∀ J ∈ Pset.powerset,
      (∑ a ∈ Aset.filter (fun a => ∀ p ∈ J, bad p a), ω a) =
        X' * ∏ p ∈ J, g p + Ew Aset ω bad X' g (∏ p ∈ J, p) := by
    intro J hJ
    have hpf : (∏ p ∈ J, p).primeFactors = J :=
      Nat.primeFactors_prod (fun p hp => hP p (mem_powerset.1 hJ hp))
    rw [Ew, hpf]; ring
  have h1 : ∀ a ∈ Aset, ω a * F lam (Pset.filter (fun p => bad p a)) =
      ∑ J ∈ Pset.powerset, if (∀ p ∈ J, bad p a) then ω a * lam J else 0 := by
    intro a _
    rw [F, mul_sum, ← sum_filter]
    apply sum_congr _ (fun _ _ => rfl)
    ext J
    simp only [mem_powerset, mem_filter, subset_iff]
    constructor
    · intro h; exact ⟨fun p hp => (h hp).1, fun p hp => (h hp).2⟩
    · intro h p hp; exact ⟨h.1 hp, h.2 p hp⟩
  rw [sum_congr rfl h1, sum_comm]
  have h2 : ∀ J ∈ Pset.powerset,
      (∑ a ∈ Aset, if (∀ p ∈ J, bad p a) then ω a * lam J else 0) =
        lam J * (X' * ∏ p ∈ J, g p) + lam J * Ew Aset ω bad X' g (∏ p ∈ J, p) := by
    intro J hJ
    rw [← sum_filter, ← sum_mul, hA J hJ]; ring
  rw [sum_congr rfl h2, sum_add_distrib, Mn, mul_sum]
  congr 1
  apply sum_congr rfl; intro J _; ring

lemma S_eq {α : Type*} (Aset : Finset α) (ω : α → ℝ) (Pset : Finset ℕ) (bad : ℕ → α → Prop) :
    ∑ a ∈ Aset.filter (fun a => ∀ p ∈ Pset, ¬ bad p a), ω a =
      ∑ a ∈ Aset, ω a * ind (Pset.filter (fun p => bad p a)) := by
  rw [sum_filter]
  apply sum_congr rfl
  intro a _
  rw [ind]
  by_cases h : ∀ p ∈ Pset, ¬ bad p a
  · rw [if_pos h, if_pos (filter_eq_empty_iff.2 h), mul_one]
  · rw [if_neg h, if_neg (fun h' => h (filter_eq_empty_iff.1 h')), mul_zero]

lemma error_bound {α : Type*} (Aset : Finset α) (ω : α → ℝ) (Pset : Finset ℕ)
    (hP : ∀ p ∈ Pset, p.Prime) (bad : ℕ → α → Prop) (X' : ℝ) (g : ℕ → ℝ) (L : ℝ)
    (lam : Finset ℕ → ℝ) (hlam : ∀ J ∈ Pset.powerset, |lam J| ≤ 1)
    (hsupp : ∀ J ∈ Pset.powerset, lam J ≠ 0 → ((∏ p ∈ J, p : ℕ) : ℝ) ≤ L) :
    |∑ J ∈ Pset.powerset, lam J * Ew Aset ω bad X' g (∏ p ∈ J, p)| ≤
      ∑ d ∈ (∏ p ∈ Pset, p).divisors.filter (fun d : ℕ => (d : ℝ) ≤ L),
        |Ew Aset ω bad X' g d| := by
  have hinj : Set.InjOn (fun J : Finset ℕ => ∏ p ∈ J, p)
      ↑(Pset.powerset.filter (fun J => ((∏ p ∈ J, p : ℕ) : ℝ) ≤ L)) := by
    intro J1 h1 J2 h2 heq
    simp only [coe_filter, Set.mem_ofPred_eq, mem_powerset] at h1 h2
    have e1 := Nat.primeFactors_prod (fun p hp => hP p (h1.1 hp))
    have e2 := Nat.primeFactors_prod (fun p hp => hP p (h2.1 hp))
    rw [← e1, ← e2]; simp only at heq; rw [heq]
  calc |∑ J ∈ Pset.powerset, lam J * Ew Aset ω bad X' g (∏ p ∈ J, p)|
      ≤ ∑ J ∈ Pset.powerset, |lam J * Ew Aset ω bad X' g (∏ p ∈ J, p)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ J ∈ Pset.powerset, if ((∏ p ∈ J, p : ℕ) : ℝ) ≤ L then
          |Ew Aset ω bad X' g (∏ p ∈ J, p)| else 0 := by
        apply sum_le_sum
        intro J hJ
        rw [abs_mul]
        by_cases h0 : lam J = 0
        · rw [h0, abs_zero, zero_mul]; split_ifs <;> simp
        · rw [if_pos (hsupp J hJ h0)]
          exact mul_le_of_le_one_left (abs_nonneg _) (hlam J hJ)
    _ = ∑ J ∈ Pset.powerset.filter (fun J => ((∏ p ∈ J, p : ℕ) : ℝ) ≤ L),
          |Ew Aset ω bad X' g (∏ p ∈ J, p)| := by rw [sum_filter]
    _ = ∑ d ∈ (Pset.powerset.filter (fun J => ((∏ p ∈ J, p : ℕ) : ℝ) ≤ L)).image
          (fun J => ∏ p ∈ J, p), |Ew Aset ω bad X' g d| := (sum_image (f := fun d => |Ew Aset ω bad X' g d|) hinj).symm
    _ ≤ _ := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro d hd
          obtain ⟨J, hJ, rfl⟩ := mem_image.1 hd
          rw [mem_filter, mem_powerset] at hJ
          refine mem_filter.2 ⟨Nat.mem_divisors.2 ⟨prod_dvd_prod_of_subset _ _ _ hJ.1, ?_⟩, hJ.2⟩
          exact prod_ne_zero_iff.2 (fun p hp => (hP p hp).ne_zero)
        · intro _ _ _; exact abs_nonneg _

/-! ## Block assignment -/

lemma blocks_exist (z : ℝ) (hz : 2 ≤ z) :
    ∃ blk : ℕ → ℕ, ∀ p : ℕ, p.Prime → (p : ℝ) ≤ z →
      (p : ℝ) ≤ z ^ ((1 / 2 : ℝ) ^ (blk p)) ∧
      z ^ ((1 / 2 : ℝ) ^ (blk p + 1)) < p ∧
      1 < z ^ ((1 / 2 : ℝ) ^ (blk p + 1)) ∧
      (z ^ ((1 / 2 : ℝ) ^ (blk p + 1))) ^ 2 = z ^ ((1 / 2 : ℝ) ^ (blk p)) := by
  refine ⟨fun p => Nat.log 2 ⌊Real.log z / Real.log p⌋₊, ?_⟩
  intro p hp hpz
  have hz1 : (1 : ℝ) < z := by linarith
  have hz0 : (0 : ℝ) < z := by linarith
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hlp : 0 < Real.log p := Real.log_pos hp1
  have hlz : Real.log p ≤ Real.log z := Real.log_le_log (by linarith) hpz
  set x := Real.log z / Real.log p with hx
  have hx1 : 1 ≤ x := by rw [hx, le_div_iff₀ hlp]; linarith
  set j := Nat.log 2 ⌊x⌋₊ with hj
  have hfl : ⌊x⌋₊ ≠ 0 := by
    have : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx1)
    omega
  have hA : (2 : ℝ) ^ j ≤ x := by
    have h1 : 2 ^ j ≤ ⌊x⌋₊ := Nat.pow_log_le_self 2 hfl
    have h2 : ((2 ^ j : ℕ) : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast h1
    push_cast at h2
    exact h2.trans (Nat.floor_le (by linarith))
  have hB : x < (2 : ℝ) ^ (j + 1) := by
    have h1 : ⌊x⌋₊ < 2 ^ (j + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
    have h3 : ((⌊x⌋₊ + 1 : ℕ) : ℝ) ≤ ((2 ^ (j + 1) : ℕ) : ℝ) := by exact_mod_cast h1
    push_cast at h3
    linarith [Nat.lt_floor_add_one x]
  have hpexp : (p : ℝ) = exp (Real.log p) := (exp_log (by linarith)).symm
  have hhalf : ∀ m : ℕ, (1 / 2 : ℝ) ^ m = 1 / 2 ^ m := fun m => by rw [one_div_pow]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Real.rpow_def_of_pos hz0, hpexp, exp_le_exp, hhalf, mul_one_div,
      le_div_iff₀ (by positivity)]
    rw [hx, le_div_iff₀ hlp] at hA
    linarith
  · rw [Real.rpow_def_of_pos hz0, hpexp, exp_lt_exp, hhalf, mul_one_div,
      div_lt_iff₀ (by positivity)]
    rw [hx, div_lt_iff₀ hlp] at hB
    linarith
  · exact Real.one_lt_rpow hz1 (by positivity)
  · rw [← Real.rpow_natCast, ← Real.rpow_mul hz0.le]
    congr 1
    push_cast
    rw [pow_succ]; ring

/-! ## The core estimate for a fixed even `H` -/

theorem core (η C : ℝ) (hη : 0 < η) (H : ℕ) (hH : Even H) (ε : ℝ) (hε : 0 ≤ ε)
    (hεH : ∀ k : ℕ, C ^ ((k + 1) * H + 1) / ((((k + 1) * H + 1) ! : ℕ) : ℝ) ≤ ε * (1 / 2) ^ (k + 1))
    {α : Type*} (Aset : Finset α) (ω : α → ℝ) (hω : ∀ a ∈ Aset, 0 ≤ ω a)
    (z : ℝ) (hz : 2 ≤ z) (Pset : Finset ℕ) (hP : ∀ p ∈ Pset, p.Prime ∧ (p : ℝ) ≤ z)
    (bad : ℕ → α → Prop) (X' : ℝ) (hX : 0 ≤ X') (g : ℕ → ℝ)
    (hg : ∀ p ∈ Pset, 0 ≤ g p ∧ g p ≤ 1 - η)
    (blk : ℕ → ℕ) (hblk1 : ∀ p ∈ Pset, (p : ℝ) ≤ z ^ ((1 / 2 : ℝ) ^ (blk p)))
    (hblk2 : ∀ k, ∑ p ∈ Pset.filter (fun p => blk p = k), g p ≤ C) :
    ∑ a ∈ Aset.filter (fun a => ∀ p ∈ Pset, ¬ bad p a), ω a ≤
        X' * (∏ p ∈ Pset, (1 - g p)) * exp (ε * exp (C / η)) +
        ∑ d ∈ (∏ p ∈ Pset, p).divisors.filter (fun d : ℕ => (d : ℝ) ≤ z ^ (4 * H + 2)),
          |Ew Aset ω bad X' g d| ∧
      X' * (∏ p ∈ Pset, (1 - g p)) -
        X' * (∏ p ∈ Pset, (1 - g p)) * ((ε * exp (C / η)) * exp (ε * exp (C / η))) -
        ∑ d ∈ (∏ p ∈ Pset, p).divisors.filter (fun d : ℕ => (d : ℝ) ≤ z ^ (4 * H + 2)),
          |Ew Aset ω bad X' g d| ≤
        ∑ a ∈ Aset.filter (fun a => ∀ p ∈ Pset, ¬ bad p a), ω a := by
  have hPprime : ∀ p ∈ Pset, p.Prime := fun p hp => (hP p hp).1
  set N := Pset.sup blk + 1 with hN
  set K := range N with hK
  have hPK : ∀ p ∈ Pset, blk p ∈ K := fun p hp => mem_range.2 (Nat.lt_succ_of_le (le_sup hp))
  set hh : ℕ → ℕ := fun k => (k + 1) * H with hhh
  have hhe : ∀ k, Even (hh k) := fun k => hH.mul_left _
  have hg1 : ∀ p ∈ Pset, 0 ≤ g p ∧ g p ≤ 1 :=
    fun p hp => ⟨(hg p hp).1, by linarith [(hg p hp).2]⟩
  -- block quantities
  have hBsub : ∀ k, Pset.filter (fun p => blk p = k) ⊆ Pset := fun k => filter_subset _ _
  set a : ℕ → ℝ := fun k => ∏ p ∈ Pset.filter (fun p => blk p = k), (1 - g p) with ha_def
  set M : ℕ → ℝ := fun k => Mn g (Pset.filter (fun p => blk p = k)) (cU (hh k)) with hM_def
  set t : ℕ → ℝ := fun k => Mn g (Pset.filter (fun p => blk p = k)) (cT (hh k)) with ht_def
  have ha_low : ∀ k, exp (-(C / η)) ≤ a k := fun k =>
    block_lower g η C hη _ (fun p hp => hg p (hBsub k hp)) (hblk2 k)
  have ha_pos : ∀ k, 0 < a k := fun k => lt_of_lt_of_le (exp_pos _) (ha_low k)
  have haM : ∀ k, a k ≤ M k ∧ M k ≤ a k + t k := fun k =>
    block_expect g (hh k) (hhe k) _ (fun p hp => hg1 p (hBsub k hp))
  have ht0 : ∀ k, 0 ≤ t k := fun k =>
    Mn_cT_nonneg g (hh k) _ (fun p hp => (hg p (hBsub k hp)).1)
  have ht_le : ∀ k, t k ≤ ε * (1 / 2) ^ (k + 1) := by
    intro k
    have h1 := esymm_le g (Pset.filter (fun p => blk p = k))
      (fun p hp => (hg p (hBsub k hp)).1) (hh k + 1)
    have hs0 : 0 ≤ ∑ p ∈ Pset.filter (fun p => blk p = k), g p :=
      sum_nonneg (fun p hp => (hg p (hBsub k hp)).1)
    have h2 : (∑ p ∈ Pset.filter (fun p => blk p = k), g p) ^ (hh k + 1) ≤ C ^ (hh k + 1) :=
      pow_le_pow_left₀ hs0 (hblk2 k) _
    calc t k = Mn g (Pset.filter (fun p => blk p = k))
          (fun J => if J.card = hh k + 1 then 1 else 0) := rfl
      _ ≤ (∑ p ∈ Pset.filter (fun p => blk p = k), g p) ^ (hh k + 1) / ((hh k + 1)! : ℝ) := h1
      _ ≤ C ^ (hh k + 1) / ((hh k + 1)! : ℝ) :=
          div_le_div_of_nonneg_right h2 (Nat.cast_nonneg _)
      _ ≤ ε * (1 / 2) ^ (k + 1) := hεH k
  set R := ∑ k ∈ K, t k / a k with hR_def
  set R0 := ε * exp (C / η) with hR0_def
  have hR0 : 0 ≤ R := sum_nonneg (fun k _ => div_nonneg (ht0 k) (ha_pos k).le)
  have hR : R ≤ R0 := by
    have h1 : ∀ k ∈ K, t k / a k ≤ ε * exp (C / η) * (1 / 2) ^ (k + 1) := by
      intro k _
      have hinv : 1 / a k ≤ exp (C / η) := by
        have := one_div_le_one_div_of_le (exp_pos _) (ha_low k)
        rwa [one_div (exp _), ← exp_neg, neg_neg] at this
      calc t k / a k = t k * (1 / a k) := by ring
        _ ≤ (ε * (1 / 2) ^ (k + 1)) * exp (C / η) :=
            mul_le_mul (ht_le k) hinv (one_div_nonneg.2 (ha_pos k).le) (by positivity)
        _ = _ := by ring
    have hgeo : ∑ k ∈ K, (1 / 2 : ℝ) ^ (k + 1) ≤ 1 := by
      have := sum_geometric_two_le N
      have e : ∑ k ∈ K, (1 / 2 : ℝ) ^ (k + 1) = (1 / 2) * ∑ k ∈ range N, (1 / 2 : ℝ) ^ k := by
        rw [mul_sum]; apply sum_congr rfl; intro k _; ring
      rw [e]; linarith
    calc R ≤ ∑ k ∈ K, ε * exp (C / η) * (1 / 2) ^ (k + 1) := sum_le_sum h1
      _ = ε * exp (C / η) * ∑ k ∈ K, (1 / 2 : ℝ) ^ (k + 1) := by rw [mul_sum]
      _ ≤ ε * exp (C / η) * 1 := mul_le_mul_of_nonneg_left hgeo (by positivity)
      _ = R0 := by ring
  obtain ⟨hn1, hn2, hn3⟩ := numeric K a M t (fun k _ => ha_pos k) (fun k _ => (haM k).1)
    (fun k _ => (haM k).2) (fun k _ => ht0 k)
  have hPr : ∏ k ∈ K, a k = ∏ p ∈ Pset, (1 - g p) :=
    prod_fiberwise_of_maps_to hPK (fun p => 1 - g p)
  rw [hPr] at hn1 hn2 hn3
  set Pr := ∏ p ∈ Pset, (1 - g p) with hPr_def
  have hPr0 : 0 ≤ Pr := prod_nonneg (fun p hp => by linarith [(hg1 p hp).2])
  -- polynomial identities
  have hFU : ∀ T, (∀ p ∈ T, blk p ∈ K) → F (lamU blk K hh) T =
      ∏ k ∈ K, F (cU (hh k)) (T.filter (fun p => blk p = k)) :=
    fun T hT => key_F blk K T hT (fun k => cU (hh k))
  have hfkF : ∀ j k S, F (fk hh j k) S =
      if k = j then F (cT (hh k)) S else F (cU (hh k)) S := by
    intro j k S; unfold fk; split_ifs <;> rfl
  have hfkM : ∀ j k S, Mn g S (fk hh j k) =
      if k = j then Mn g S (cT (hh k)) else Mn g S (cU (hh k)) := by
    intro j k S; unfold fk; split_ifs <;> rfl
  have hFk : ∀ j T, (∀ p ∈ T, blk p ∈ K) → F (kap blk K hh j) T =
      ∏ k ∈ K, (if k = j then F (cT (hh k)) (T.filter (fun p => blk p = k))
        else F (cU (hh k)) (T.filter (fun p => blk p = k))) := by
    intro j T hT
    rw [show F (kap blk K hh j) T = ∏ k ∈ K, F (fk hh j k) (T.filter (fun p => blk p = k)) from
      key_F blk K T hT (fun k => fk hh j k)]
    exact prod_congr rfl (fun k _ => hfkF j k _)
  have hFL : ∀ T, F (lamL blk K hh) T = F (lamU blk K hh) T - ∑ j ∈ K, F (kap blk K hh j) T := by
    intro T
    simp only [F, lamL]
    rw [sum_sub_distrib, sum_comm]
  have hMU : Mn g Pset (lamU blk K hh) = ∏ k ∈ K, M k :=
    key_Mn g blk K Pset hPK (fun k => cU (hh k))
  have hMk : ∀ j, Mn g Pset (kap blk K hh j) = ∏ k ∈ K, (if k = j then t k else M k) := by
    intro j
    rw [show Mn g Pset (kap blk K hh j) =
        ∏ k ∈ K, Mn g (Pset.filter (fun p => blk p = k)) (fk hh j k) from
      key_Mn g blk K Pset hPK (fun k => fk hh j k)]
    exact prod_congr rfl (fun k _ => hfkM j k _)
  have hML : Mn g Pset (lamL blk K hh) =
      Mn g Pset (lamU blk K hh) - ∑ j ∈ K, Mn g Pset (kap blk K hh j) := by
    simp only [Mn, lamL]
    rw [sum_comm (s := K), ← sum_sub_distrib]
    apply sum_congr rfl; intro J _
    rw [sub_mul, sum_mul]
  -- pointwise inequalities
  have hup : ∀ T ⊆ Pset, ind T ≤ F (lamU blk K hh) T := by
    intro T hT
    have hTK : ∀ p ∈ T, blk p ∈ K := fun p hp => hPK p (hT hp)
    rw [hFU T hTK, ind_prod blk K T hTK]
    exact prod_le_prod (fun k _ => (block_ineq (hh k) (hhe k) _).1)
      (fun k _ => (block_ineq (hh k) (hhe k) _).2.1)
  have hlow : ∀ T ⊆ Pset, F (lamL blk K hh) T ≤ ind T := by
    intro T hT
    have hTK : ∀ p ∈ T, blk p ∈ K := fun p hp => hPK p (hT hp)
    rw [hFL, hFU T hTK, ind_prod blk K T hTK, sum_congr rfl (fun j _ => hFk j T hTK)]
    have := telescope K (fun k => ind (T.filter (fun p => blk p = k)))
      (fun k => F (cU (hh k)) (T.filter (fun p => blk p = k)))
      (fun k => F (cT (hh k)) (T.filter (fun p => blk p = k)))
      (fun k _ => (block_ineq (hh k) (hhe k) _).1)
      (fun k _ => (block_ineq (hh k) (hhe k) _).2.1)
      (fun k _ => (block_ineq (hh k) (hhe k) _).2.2)
    linarith
  -- errors
  have hz1 : (1 : ℝ) ≤ z := by linarith
  have hsize : ∀ J ∈ Pset.powerset, Good blk K hh J →
      ((∏ p ∈ J, p : ℕ) : ℝ) ≤ z ^ (4 * H + 2) := by
    intro J hJ hgood
    have hJP := mem_powerset.1 hJ
    exact good_size blk N H z hz1 J (fun p hp => mem_range.1 (hPK p (hJP hp)))
      (fun p hp => hblk1 p (hJP hp)) hgood
  set Err := ∑ d ∈ (∏ p ∈ Pset, p).divisors.filter (fun d : ℕ => (d : ℝ) ≤ z ^ (4 * H + 2)),
          |Ew Aset ω bad X' g d| with hErr_def
  have hEU := error_bound Aset ω Pset hPprime bad X' g (z ^ (4 * H + 2)) (lamU blk K hh)
    (fun J _ => (lamU_coef blk K hh J).1)
    (fun J hJ h0 => hsize J hJ ((lamU_coef blk K hh J).2 h0))
  have hEL := error_bound Aset ω Pset hPprime bad X' g (z ^ (4 * H + 2)) (lamL blk K hh)
    (fun J _ => (lamL_coef blk K hh J).1)
    (fun J hJ h0 => hsize J hJ ((lamL_coef blk K hh J).2 h0))
  have hTU := transfer Aset ω Pset hPprime bad X' g (lamU blk K hh)
  have hTL := transfer Aset ω Pset hPprime bad X' g (lamL blk K hh)
  rw [← hErr_def] at hEU hEL
  rw [S_eq]
  have hSU : ∑ a ∈ Aset, ω a * ind (Pset.filter (fun p => bad p a)) ≤
      ∑ a ∈ Aset, ω a * F (lamU blk K hh) (Pset.filter (fun p => bad p a)) :=
    sum_le_sum (fun a ha => mul_le_mul_of_nonneg_left (hup _ (filter_subset _ _)) (hω a ha))
  have hSL : ∑ a ∈ Aset, ω a * F (lamL blk K hh) (Pset.filter (fun p => bad p a)) ≤
      ∑ a ∈ Aset, ω a * ind (Pset.filter (fun p => bad p a)) :=
    sum_le_sum (fun a ha => mul_le_mul_of_nonneg_left (hlow _ (filter_subset _ _)) (hω a ha))
  have hexp : exp R ≤ exp R0 := exp_le_exp.2 hR
  have hRe : R * exp R ≤ R0 * exp R0 :=
    mul_le_mul hR hexp (exp_pos _).le (le_trans hR0 hR)
  constructor
  · rw [hTU, hMU] at hSU
    have h1 := le_abs_self (∑ J ∈ Pset.powerset, lamU blk K hh J *
      Ew Aset ω bad X' g (∏ p ∈ J, p))
    have h2 : X' * ∏ k ∈ K, M k ≤ X' * Pr * exp R0 := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (hn2.trans (mul_le_mul_of_nonneg_left hexp hPr0)) hX
    linarith
  · rw [hTL, hML, hMU, sum_congr rfl (fun j _ => hMk j)] at hSL
    have h1 := neg_abs_le (∑ J ∈ Pset.powerset, lamL blk K hh J *
      Ew Aset ω bad X' g (∏ p ∈ J, p))
    have h2 : X' * Pr - X' * Pr * (R0 * exp R0) ≤
        X' * (∏ k ∈ K, M k - ∑ j ∈ K, ∏ k ∈ K, (if k = j then t k else M k)) := by
      have : Pr - Pr * (R0 * exp R0) ≤
          ∏ k ∈ K, M k - ∑ j ∈ K, ∏ k ∈ K, (if k = j then t k else M k) := by
        nlinarith [mul_le_mul_of_nonneg_left hRe hPr0]
      nlinarith [mul_le_mul_of_nonneg_left this hX]
    linarith

/-- Applying `core` with the paper's block assignment. -/
theorem core' (η C₀ : ℝ) (hη : 0 < η) (H : ℕ) (hH : Even H) (ε : ℝ) (hε : 0 ≤ ε)
    (hεH : ∀ k : ℕ, (max C₀ 0) ^ ((k + 1) * H + 1) / ((((k + 1) * H + 1) ! : ℕ) : ℝ) ≤
      ε * (1 / 2) ^ (k + 1))
    {α : Type*} (Aset : Finset α) (ω : α → ℝ) (hω : ∀ a ∈ Aset, 0 ≤ ω a)
    (z : ℝ) (hz : 2 ≤ z) (Pset : Finset ℕ) (hP : ∀ p ∈ Pset, p.Prime ∧ (p : ℝ) ≤ z)
    (bad : ℕ → α → Prop) (X' : ℝ) (hX : 0 ≤ X') (g : ℕ → ℝ)
    (hg : ∀ p ∈ Pset, 0 ≤ g p ∧ g p ≤ 1 - η)
    (hsum : ∀ v : ℝ, 1 < v → ∑ p ∈ Pset.filter (fun p : ℕ => v < p ∧ (p : ℝ) ≤ v ^ 2), g p ≤ C₀) :
    ∑ a ∈ Aset.filter (fun a => ∀ p ∈ Pset, ¬ bad p a), ω a ≤
        X' * (∏ p ∈ Pset, (1 - g p)) * exp (ε * exp (max C₀ 0 / η)) +
        ∑ d ∈ (∏ p ∈ Pset, p).divisors.filter (fun d : ℕ => (d : ℝ) ≤ z ^ (4 * H + 2)),
          |Ew Aset ω bad X' g d| ∧
      X' * (∏ p ∈ Pset, (1 - g p)) -
        X' * (∏ p ∈ Pset, (1 - g p)) *
          ((ε * exp (max C₀ 0 / η)) * exp (ε * exp (max C₀ 0 / η))) -
        ∑ d ∈ (∏ p ∈ Pset, p).divisors.filter (fun d : ℕ => (d : ℝ) ≤ z ^ (4 * H + 2)),
          |Ew Aset ω bad X' g d| ≤
        ∑ a ∈ Aset.filter (fun a => ∀ p ∈ Pset, ¬ bad p a), ω a := by
  obtain ⟨blk, hblk⟩ := blocks_exist z hz
  refine core η (max C₀ 0) hη H hH ε hε hεH Aset ω hω z hz Pset hP bad X'
    hX g hg blk (fun p hp => (hblk p (hP p hp).1 (hP p hp).2).1) ?_
  intro k
  have hv : 1 < z ^ ((1 / 2 : ℝ) ^ (k + 1)) := Real.one_lt_rpow (by linarith) (by positivity)
  calc ∑ p ∈ Pset.filter (fun p => blk p = k), g p
      ≤ ∑ p ∈ Pset.filter (fun p : ℕ => z ^ ((1 / 2 : ℝ) ^ (k + 1)) < p ∧
          (p : ℝ) ≤ (z ^ ((1 / 2 : ℝ) ^ (k + 1))) ^ 2), g p := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro p hp
          rw [mem_filter] at hp ⊢
          obtain ⟨h1, h2, -, h4⟩ := hblk p (hP p hp.1).1 (hP p hp.1).2
          rw [hp.2] at h1 h2 h4
          refine ⟨hp.1, h2, ?_⟩
          rw [h4]; exact h1
        · intro p hp _; exact (hg p (mem_filter.1 hp).1).1
    _ ≤ C₀ := hsum _ hv
    _ ≤ max C₀ 0 := le_max_left _ _

/-- The factorial decay used for large `H`. -/
lemma large_H (C : ℝ) :
    ∃ H₀ : ℕ, 1 ≤ H₀ ∧ ∀ H : ℕ, H₀ ≤ H → ∀ k : ℕ,
      C ^ ((k + 1) * H + 1) / ((((k + 1) * H + 1) ! : ℕ) : ℝ) ≤ exp (-(H : ℝ)) * (1 / 2) ^ (k + 1) := by
  have ht := FloorSemiring.tendsto_pow_div_factorial_atTop (exp 2 * C)
  obtain ⟨n0, hn0⟩ := Filter.eventually_atTop.1 ((tendsto_order.1 ht).2 1 one_pos)
  refine ⟨n0 + 1, by omega, fun H hH k => ?_⟩
  have hH1 : (1 : ℝ) ≤ H := by exact_mod_cast (show 1 ≤ H by omega)
  have hnn : n0 ≤ (k + 1) * H + 1 := by nlinarith
  have h1 := (hn0 _ hnn).le
  set n := (k + 1) * H + 1 with hn
  have he2 : exp 2 ^ n * exp (-(2 * n : ℝ)) = 1 := by
    rw [← exp_nat_mul, ← exp_add]; ring_nf; simp
  have h2 : C ^ n / (n ! : ℝ) = exp (-(2 * n : ℝ)) * ((exp 2 * C) ^ n / (n ! : ℝ)) := by
    rw [mul_pow]
    calc C ^ n / (n ! : ℝ) = 1 * (C ^ n / (n ! : ℝ)) := by ring
      _ = (exp 2 ^ n * exp (-(2 * n : ℝ))) * (C ^ n / (n ! : ℝ)) := by rw [he2]
      _ = _ := by ring
  have h3 : C ^ n / (n ! : ℝ) ≤ exp (-(2 * n : ℝ)) := by
    rw [h2]; nlinarith [exp_pos (-(2 * n : ℝ))]
  have hle : exp (-1) ≤ (1 / 2 : ℝ) := by
    have : 2 ≤ exp 1 := by linarith [add_one_le_exp (1 : ℝ)]
    rw [exp_neg, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) this
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  calc C ^ n / (n ! : ℝ) ≤ exp (-(2 * n : ℝ)) := h3
    _ ≤ exp (-(H : ℝ) + ((k + 1 : ℕ) : ℝ) * (-1)) := by
        apply exp_le_exp.2
        rw [hn]; push_cast; nlinarith
    _ = exp (-(H : ℝ)) * exp (-1) ^ (k + 1) := by rw [← exp_nat_mul, ← exp_add]
    _ ≤ exp (-(H : ℝ)) * (1 / 2) ^ (k + 1) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (exp_pos _).le hle _) (exp_pos _).le

/-- The factorial bound used for `H = 2`. -/
lemma small_H (C : ℝ) (hC : 0 ≤ C) (k : ℕ) :
    C ^ ((k + 1) * 2 + 1) / ((((k + 1) * 2 + 1) ! : ℕ) : ℝ) ≤ exp (2 * C) * (1 / 2) ^ (k + 1) := by
  set n := (k + 1) * 2 + 1 with hn
  have h1 := Real.pow_div_factorial_le_exp (2 * C) (by linarith) n
  have e : C ^ n / (n ! : ℝ) = (2 * C) ^ n / (n ! : ℝ) * (1 / 2) ^ n := by
    rw [mul_pow, one_div_pow]; field_simp
  rw [e]
  have h2 : (1 / 2 : ℝ) ^ n ≤ (1 / 2) ^ (k + 1) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  calc _ ≤ exp (2 * C) * (1 / 2) ^ n := mul_le_mul_of_nonneg_right h1 (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_left h2 (exp_pos _).le

end ArtinPrimitiveRoots.BlockSieveAux

open Real

open Classical in
theorem solution (η₀ C₀ : ℝ) (hη₀ : 0 < η₀) :
    (∃ H₀ : ℕ, ∃ B : ℝ, ∀ H : ℕ, H₀ ≤ H → Even H →
      ∀ {α : Type*} (Aset : Finset α) (ω : α → ℝ), (∀ a ∈ Aset, 0 ≤ ω a) →
      ∀ (z : ℝ), 2 ≤ z → ∀ Pset : Finset ℕ, (∀ p ∈ Pset, p.Prime ∧ (p : ℝ) ≤ z) →
      ∀ bad : ℕ → α → Prop, ∀ X' : ℝ, 0 ≤ X' → ∀ g : ℕ → ℝ,
        (∀ p ∈ Pset, 0 ≤ g p ∧ g p ≤ 1 - η₀) →
        (∀ v : ℝ, 1 < v → ∑ p ∈ Pset.filter (fun p : ℕ => v < p ∧ (p : ℝ) ≤ v ^ 2), g p ≤ C₀) →
      let A : ℕ → ℝ := fun d => ∑ a ∈ Aset.filter (fun a => ∀ p ∈ d.primeFactors, bad p a), ω a
      let E : ℕ → ℝ := fun d => A d - X' * ∏ p ∈ d.primeFactors, g p
      let S : ℝ := ∑ a ∈ Aset.filter (fun a => ∀ p ∈ Pset, ¬ bad p a), ω a
      |S - X' * ∏ p ∈ Pset, (1 - g p)| ≤
        B * (X' * ∏ p ∈ Pset, (1 - g p)) * exp (-(H : ℝ)) +
          B * ∑ d ∈ (∏ p ∈ Pset, p).divisors.filter (fun d : ℕ => (d : ℝ) ≤ z ^ (4 * H + 2)), |E d|) ∧
    (∃ B : ℝ, ∀ {α : Type*} (Aset : Finset α) (ω : α → ℝ), (∀ a ∈ Aset, 0 ≤ ω a) →
      ∀ (z : ℝ), 2 ≤ z → ∀ Pset : Finset ℕ, (∀ p ∈ Pset, p.Prime ∧ (p : ℝ) ≤ z) →
      ∀ bad : ℕ → α → Prop, ∀ X' : ℝ, 0 ≤ X' → ∀ g : ℕ → ℝ,
        (∀ p ∈ Pset, 0 ≤ g p ∧ g p ≤ 1 - η₀) →
        (∀ v : ℝ, 1 < v → ∑ p ∈ Pset.filter (fun p : ℕ => v < p ∧ (p : ℝ) ≤ v ^ 2), g p ≤ C₀) →
      let A : ℕ → ℝ := fun d => ∑ a ∈ Aset.filter (fun a => ∀ p ∈ d.primeFactors, bad p a), ω a
      let E : ℕ → ℝ := fun d => A d - X' * ∏ p ∈ d.primeFactors, g p
      let S : ℝ := ∑ a ∈ Aset.filter (fun a => ∀ p ∈ Pset, ¬ bad p a), ω a
      S ≤ B * (X' * ∏ p ∈ Pset, (1 - g p) +
          ∑ d ∈ (∏ p ∈ Pset, p).divisors.filter (fun d : ℕ => (d : ℝ) ≤ z ^ (10 : ℕ)), |E d|)) := by
  set c : ℝ := max C₀ 0 with hc_def
  have hc : 0 ≤ c := le_max_right _ _
  set Q : ℝ := exp (c / η₀) with hQ_def
  have hQ : 0 ≤ Q := (exp_pos _).le
  constructor
  · obtain ⟨H₀, -, hH₀⟩ := ArtinPrimitiveRoots.BlockSieveAux.large_H c
    refine ⟨H₀, max 1 (Q * exp Q), ?_⟩
    intro H hH hHe α Aset ω hω z hz Pset hP bad X' hX g hg hsum
    dsimp only
    obtain ⟨h1, h2⟩ := ArtinPrimitiveRoots.BlockSieveAux.core' η₀ C₀ hη₀ H hHe (exp (-(H : ℝ))) (exp_pos _).le
      (hH₀ H hH) Aset ω hω z hz Pset hP bad X' hX g hg hsum
    simp only [ArtinPrimitiveRoots.BlockSieveAux.Ew] at h1 h2
    set S := ∑ a ∈ Aset.filter (fun a => ∀ p ∈ Pset, ¬ bad p a), ω a
    set P := X' * ∏ p ∈ Pset, (1 - g p) with hP_def
    set Err := ∑ d ∈ (∏ p ∈ Pset, p).divisors.filter (fun d : ℕ => (d : ℝ) ≤ z ^ (4 * H + 2)),
      |(∑ a ∈ Aset.filter (fun a => ∀ p ∈ d.primeFactors, bad p a), ω a) -
        X' * ∏ p ∈ d.primeFactors, g p|
    have hPnn : 0 ≤ P := mul_nonneg hX (Finset.prod_nonneg fun p hp => by linarith [hg p hp])
    have hErr : 0 ≤ Err := Finset.sum_nonneg fun _ _ => abs_nonneg _
    set e := exp (-(H : ℝ)) with he_def
    have he0 : 0 ≤ e := (exp_pos _).le
    have he1 : e ≤ 1 := by rw [he_def, exp_le_one_iff]; simp
    set R := e * Q with hR_def
    have hR0 : 0 ≤ R := mul_nonneg he0 hQ
    have hRQ : R ≤ Q := by nlinarith
    have hexpR : exp R - 1 ≤ R * exp R := by
      have := add_one_le_exp (-R)
      have h3 : exp (-R) * exp R = 1 := by rw [← exp_add]; simp
      nlinarith [exp_pos R]
    have hRB : R * exp R ≤ e * max 1 (Q * exp Q) := by
      calc R * exp R ≤ e * (Q * exp Q) := by
            rw [hR_def, mul_assoc]
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left (exp_le_exp.2 hRQ) hQ) he0
        _ ≤ _ := mul_le_mul_of_nonneg_left (le_max_right _ _) he0
    have hB1 : 1 ≤ max 1 (Q * exp Q) := le_max_left _ _
    have hPR : P * (R * exp R) ≤ max 1 (Q * exp Q) * P * e := by
      nlinarith [mul_le_mul_of_nonneg_left hRB hPnn]
    have hPR' : P * exp R - P ≤ P * (R * exp R) := by nlinarith [mul_le_mul_of_nonneg_left hexpR hPnn]
    rw [abs_le]
    constructor <;> nlinarith
  · refine ⟨max 1 (exp (exp (2 * c) * Q)), ?_⟩
    intro α Aset ω hω z hz Pset hP bad X' hX g hg hsum
    dsimp only
    obtain ⟨h1, -⟩ := ArtinPrimitiveRoots.BlockSieveAux.core' η₀ C₀ hη₀ 2 even_two (exp (2 * c)) (exp_pos _).le
      (ArtinPrimitiveRoots.BlockSieveAux.small_H c hc) Aset ω hω z hz Pset hP bad X' hX g hg hsum
    simp only [ArtinPrimitiveRoots.BlockSieveAux.Ew] at h1
    rw [show (4 * 2 + 2 : ℕ) = 10 from rfl] at h1
    set S := ∑ a ∈ Aset.filter (fun a => ∀ p ∈ Pset, ¬ bad p a), ω a
    set P := X' * ∏ p ∈ Pset, (1 - g p) with hP_def
    set Err := ∑ d ∈ (∏ p ∈ Pset, p).divisors.filter (fun d : ℕ => (d : ℝ) ≤ z ^ (10 : ℕ)),
      |(∑ a ∈ Aset.filter (fun a => ∀ p ∈ d.primeFactors, bad p a), ω a) -
        X' * ∏ p ∈ d.primeFactors, g p|
    have hPnn : 0 ≤ P := mul_nonneg hX (Finset.prod_nonneg fun p hp => by linarith [hg p hp])
    have hErr : 0 ≤ Err := Finset.sum_nonneg fun _ _ => abs_nonneg _
    have hm1 := le_max_left 1 (exp (exp (2 * c) * Q))
    have hm2 := le_max_right 1 (exp (exp (2 * c) * Q))
    nlinarith [mul_le_mul_of_nonneg_left hm2 hPnn, mul_le_mul_of_nonneg_right hm1 hErr]

