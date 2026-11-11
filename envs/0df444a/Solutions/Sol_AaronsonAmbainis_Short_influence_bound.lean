-- Prove2me | solution 1 for AaronsonAmbainis.Short.influence_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T04:36:17.540199+00:00
-- url     : https://prove2.me/submissions/c94d041a-671c-4cb8-93ce-539b8d426bf4

import Mathlib
import Definitions.Def_AaronsonAmbainis_Short
import Theorems.Thm_AaronsonAmbainis_Short_cov_le_of_dtree
import Theorems.Thm_AaronsonAmbainis_Short_exists_dtree
import Theorems.Thm_AaronsonAmbainis_Short_exists_level
import Theorems.Thm_AaronsonAmbainis_rowBoundPM
import Theorems.Thm_AaronsonAmbainis_Level_isRow_levRow
import Theorems.Thm_AaronsonAmbainis_Level_sum_meanAbsIncr_le_cost
import Theorems.Thm_AaronsonAmbainis_Level_meanAbsIncr_sq_le
import Theorems.Thm_AaronsonAmbainis_Level_meanAbsIncr_nonneg
import Theorems.Thm_AaronsonAmbainis_Bridge_variance_le_one
import Theorems.Thm_AaronsonAmbainis_Bridge_variance_eq_zero_of_degree_zero

open AaronsonAmbainis
open Finset

namespace AASolMain

/-! ### Real arithmetic -/

lemma arith1 (v K I s e : ℝ) (hv : 0 < v) (hK : 0 < K)
    (hI : v / 8 * I ≤ K) (hs : 2 ^ 19 * K ^ 3 ≤ s * v ^ 5)
    (hFe : s * e ^ 2 ≤ (K / (v / 8 / 2)) ^ 2 / 4 * I) : e ≤ v / 32 := by
  have hvne : v ≠ 0 := hv.ne'
  have h1 : (K / (v / 8 / 2)) ^ 2 / 4 * I = 64 * K ^ 2 * I / v ^ 2 := by
    field_simp
    ring
  have h2 : s * e ^ 2 * v ^ 2 ≤ 64 * K ^ 2 * I := by
    rw [h1, le_div_iff₀ (by positivity)] at hFe
    exact hFe
  have h3 : s * e ^ 2 * v ^ 3 ≤ 512 * K ^ 3 := by
    calc s * e ^ 2 * v ^ 3 = (s * e ^ 2 * v ^ 2) * v := by ring
      _ ≤ (64 * K ^ 2 * I) * v := mul_le_mul_of_nonneg_right h2 hv.le
      _ = 512 * K ^ 2 * (v / 8 * I) := by ring
      _ ≤ 512 * K ^ 2 * K := mul_le_mul_of_nonneg_left hI (by positivity)
      _ = 512 * K ^ 3 := by ring
  have h4 : 2 ^ 19 * K ^ 3 * (e ^ 2 * v ^ 3) ≤ 512 * K ^ 3 * v ^ 5 := by
    calc 2 ^ 19 * K ^ 3 * (e ^ 2 * v ^ 3) ≤ s * v ^ 5 * (e ^ 2 * v ^ 3) :=
          mul_le_mul_of_nonneg_right hs (by positivity)
      _ = (s * e ^ 2 * v ^ 3) * v ^ 5 := by ring
      _ ≤ 512 * K ^ 3 * v ^ 5 := mul_le_mul_of_nonneg_right h3 (by positivity)
  have h5 : (32 * e) ^ 2 ≤ v ^ 2 := by
    have hpos : 0 < 512 * K ^ 3 * v ^ 3 := by positivity
    have e1 : 512 * K ^ 3 * v ^ 3 * ((32 * e) ^ 2) = 2 ^ 19 * K ^ 3 * (e ^ 2 * v ^ 3) := by ring
    have e2 : 512 * K ^ 3 * v ^ 3 * v ^ 2 = 512 * K ^ 3 * v ^ 5 := by ring
    have : 512 * K ^ 3 * v ^ 3 * ((32 * e) ^ 2) ≤ 512 * K ^ 3 * v ^ 3 * v ^ 2 := by
      rw [e1, e2]; exact h4
    exact le_of_mul_le_mul_left this hpos
  have h6 : 32 * e ≤ v := by
    by_contra h
    push Not at h
    nlinarith [mul_pos (sub_pos.mpr h) (show 0 < 32 * e + v by linarith)]
  linarith

lemma arith2 (v K s m R : ℝ) (hv : 0 < v) (hK : 0 < K) (hs : s * v ^ 5 ≤ 2 ^ 20 * K ^ 3)
    (h1 : v / 10 ≤ s / 2 * m) (h2 : m ^ 2 ≤ 4 * R) (hm : 0 ≤ m) :
    v ^ 12 ≤ 2 ^ 50 * K ^ 6 * R := by
  have a1 : v ^ 6 ≤ 5 * 2 ^ 20 * K ^ 3 * m := by
    calc v ^ 6 = v ^ 5 * v := by ring
      _ ≤ v ^ 5 * (5 * s * m) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = 5 * (s * v ^ 5) * m := by ring
      _ ≤ 5 * (2 ^ 20 * K ^ 3) * m :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs (by norm_num)) hm
      _ = 5 * 2 ^ 20 * K ^ 3 * m := by ring
  have a2 : (v ^ 6) ^ 2 ≤ (5 * 2 ^ 20 * K ^ 3 * m) ^ 2 := pow_le_pow_left₀ (by positivity) a1 2
  have hR : 0 ≤ R := by nlinarith [sq_nonneg m]
  have hKR : 0 ≤ K ^ 6 * R := mul_nonneg (by positivity) hR
  calc v ^ 12 = (v ^ 6) ^ 2 := by ring
    _ ≤ (5 * 2 ^ 20 * K ^ 3 * m) ^ 2 := a2
    _ = 25 * 2 ^ 40 * K ^ 6 * m ^ 2 := by ring
    _ ≤ 25 * 2 ^ 40 * K ^ 6 * (4 * R) := mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = 100 * 2 ^ 40 * (K ^ 6 * R) := by ring
    _ ≤ 2 ^ 50 * (K ^ 6 * R) := mul_le_mul_of_nonneg_right (by norm_num) hKR
    _ = 2 ^ 50 * K ^ 6 * R := by ring

/-! ### Decision trees are closed under post-composition -/

lemma dtree_comp {ι : Type} {α β : Type} (φ : α → β) {n : ℕ} {F : Cube ι → α}
    (h : Short.DTree n F) : Short.DTree n (fun x => φ (F x)) := by
  induction h with
  | const n c => exact Short.DTree.const n (φ c)
  | query n i h0 h1 _ _ ih0 ih1 =>
    have h := Short.DTree.query n i _ _ ih0 ih1
    simp only [apply_ite φ]
    exact h

/-! ### Averages on the cube -/

variable {ι : Type} [Fintype ι] [DecidableEq ι]

lemma card_cube : ((Fintype.card (Cube ι) : ℕ) : ℝ) = 2 ^ Fintype.card ι := by
  simp [Cube]

lemma abs_mean_le (f : Cube ι → ℝ) (hf : ∀ x, |f x| ≤ 1) : |mean f| ≤ 1 := by
  unfold mean
  rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < 2 ^ Fintype.card ι),
    div_le_one (by positivity)]
  calc |∑ x, f x| ≤ ∑ x, |f x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _x : Cube ι, (1:ℝ) := Finset.sum_le_sum (fun x _ => hf x)
    _ = 2 ^ Fintype.card ι := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, card_cube]

lemma abs_sub_mean_le (f : Cube ι → ℝ) (hf : ∀ x, |f x| ≤ 1) (x : Cube ι) :
    |f x - mean f| ≤ 2 :=
  (abs_sub _ _).trans (by linarith [hf x, abs_mean_le f hf])

lemma half_var_le (f : Cube ι → ℝ) (hf : ∀ x, |f x| ≤ 1) :
    variance f / 2 ≤ mean (fun x => |f x - mean f|) := by
  show (∑ x, (f x - mean f) ^ 2) / 2 ^ Fintype.card ι / 2
    ≤ (∑ x, |f x - mean f|) / 2 ^ Fintype.card ι
  rw [div_right_comm]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  rw [Finset.sum_div]
  refine Finset.sum_le_sum (fun x _ => ?_)
  have h2 := abs_sub_mean_le f hf x
  have h0 := abs_nonneg (f x - mean f)
  have hsq := sq_abs (f x - mean f)
  nlinarith

lemma cov_lower (f : Cube ι → ℝ) (hf : ∀ x, |f x| ≤ 1) (F : Cube ι → Bool) (t η : ℝ)
    (hη : 0 < η) (ht : |t - mean f| ≤ η / 2) :
    mean (fun x => |f x - mean f|) - 2 * η
      - 4 * ((((univ.filter fun x : Cube ι => η ≤ |f x - mean f|).filter
          fun x => F x ≠ Level.lev f t x).card : ℝ) / 2 ^ Fintype.card ι)
      ≤ mean (fun x => (f x - mean f) * (if F x then (1:ℝ) else -1)) := by
  obtain ⟨B, hB⟩ : ∃ B : Finset (Cube ι), B = ((univ.filter fun x : Cube ι =>
      η ≤ |f x - mean f|).filter fun x => F x ≠ Level.lev f t x) := ⟨_, rfl⟩
  rw [← hB]
  have hN : (0:ℝ) < 2 ^ Fintype.card ι := by positivity
  have hpt : ∀ x, |f x - mean f| - 2 * η - 4 * (if x ∈ B then (1:ℝ) else 0)
      ≤ (f x - mean f) * (if F x then (1:ℝ) else -1) := by
    intro x
    have hz2 := abs_sub_mean_le f hf x
    have hlow : -|f x - mean f| ≤ (f x - mean f) * (if F x then (1:ℝ) else -1) := by
      split_ifs
      · linarith [neg_abs_le (f x - mean f)]
      · linarith [le_abs_self (f x - mean f)]
    by_cases hxB : x ∈ B
    · rw [if_pos hxB]; linarith [abs_nonneg (f x - mean f)]
    · rw [if_neg hxB]
      by_cases hxU : η ≤ |f x - mean f|
      · have hFG : F x = Level.lev f t x := by
          by_contra hne
          apply hxB
          rw [hB]
          simp only [mem_filter, mem_univ, true_and]
          exact ⟨hxU, hne⟩
        have hlev : Level.lev f t x = decide (t < f x) := rfl
        obtain ⟨h1, h2⟩ := abs_le.mp ht
        have hkey : (f x - mean f) * (if F x then (1:ℝ) else -1) = |f x - mean f| := by
          rw [hFG, hlev]
          by_cases hc : t < f x
          · have hval : (if decide (t < f x) = true then (1:ℝ) else -1) = 1 := by simp [hc]
            rw [hval, mul_one]
            rcases abs_cases (f x - mean f) with ⟨h, _⟩ | ⟨h, _⟩
            · exact h.symm
            · exfalso; rw [h] at hxU; linarith
          · have hval : (if decide (t < f x) = true then (1:ℝ) else -1) = -1 := by simp [hc]
            rw [hval]
            push Not at hc
            rcases abs_cases (f x - mean f) with ⟨h, _⟩ | ⟨h, _⟩
            · exfalso; rw [h] at hxU; linarith
            · rw [h]; ring
        linarith
      · push Not at hxU
        linarith [abs_nonneg (f x - mean f)]
  have hsum := Finset.sum_le_sum (fun x (_ : x ∈ (univ : Finset (Cube ι))) => hpt x)
  have hL : ∑ x : Cube ι, (|f x - mean f| - 2 * η - 4 * (if x ∈ B then (1:ℝ) else 0))
      = (∑ x, |f x - mean f|) - 2 * η * 2 ^ Fintype.card ι - 4 * (B.card : ℝ) := by
    have hb : ∑ x : Cube ι, (if x ∈ B then (1:ℝ) else 0) = (B.card : ℝ) := by
      simp
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, card_cube, ← Finset.mul_sum, hb]
    ring
  rw [hL] at hsum
  have hdiv := div_le_div_of_nonneg_right hsum hN.le
  have hE : ((∑ x, |f x - mean f|) - 2 * η * 2 ^ Fintype.card ι - 4 * (B.card : ℝ))
      / 2 ^ Fintype.card ι
      = (∑ x, |f x - mean f|) / 2 ^ Fintype.card ι - 2 * η
        - 4 * ((B.card : ℝ) / 2 ^ Fintype.card ι) := by
    field_simp
  rw [hE] at hdiv
  exact hdiv

/-! ### The influence bound -/

theorem main_aux (d : ℕ) (f : Cube ι → ℝ) (hf : ∀ x, |f x| ≤ 1) (hdeg : HasDegreeLE f d)
    (hv : 0 < variance f) :
    ∃ j, variance f ^ 12 ≤ 2 ^ 50 * Real.pi ^ 12 * (d : ℝ) ^ 12 * inflR f j := by
  by_contra hcon
  push Not at hcon
  have hhalf := half_var_le f hf
  have hv1 : variance f ≤ 1 := Bridge.variance_le_one hf
  have hd : 1 ≤ d := by
    rcases Nat.eq_zero_or_pos d with h0 | h
    · subst h0
      have := Bridge.variance_eq_zero_of_degree_zero hdeg
      linarith
    · exact h
  obtain ⟨a, ha0, hasum, harow⟩ := rowBoundPM ι d f hf hdeg
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = Real.pi ^ 2 * (d:ℝ) ^ 2 := ⟨_, rfl⟩
  rw [← hK] at hasum
  obtain ⟨v, hvdef⟩ : ∃ v : ℝ, v = variance f := ⟨_, rfl⟩
  rw [← hvdef] at hv hcon hhalf hv1
  have hK1 : 1 ≤ K := by
    have hpi : (1:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
    have hd' : (1:ℝ) ≤ d := by exact_mod_cast hd
    have h1 : (1:ℝ) ≤ Real.pi ^ 2 := one_le_pow₀ hpi
    have h2 : (1:ℝ) ≤ (d:ℝ) ^ 2 := one_le_pow₀ hd'
    rw [hK]
    calc (1:ℝ) = 1 * 1 := by ring
      _ ≤ Real.pi ^ 2 * (d:ℝ) ^ 2 := mul_le_mul h1 h2 zero_le_one (by positivity)
  have hK0 : 0 < K := by linarith
  have hη : 0 < v / 8 := by positivity
  obtain ⟨t, ht1, ht2, hI⟩ :=
    Short.exists_level f (mean f - v / 8 / 2) (mean f + v / 8 / 2) (by linarith)
  have hcost : ∑ j, meanAbsIncr f j ≤ K := Level.sum_meanAbsIncr_le_cost hasum harow
  have hI' : v / 8 * ∑ j, infl (Level.lev f t) j ≤ K := by
    have : (mean f + v / 8 / 2 - (mean f - v / 8 / 2)) = v / 8 := by ring
    rw [this] at hI
    exact hI.trans hcost
  have htabs : |t - mean f| ≤ v / 8 / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hrow : ∀ x, IsRow (Level.lev f t) x (Level.levRow f a t x) :=
    fun x => Level.isRow_levRow ha0 harow t x
  have hγ : 0 < K / (v / 8 / 2) := by positivity
  have hU : ∀ x ∈ (univ.filter fun x : Cube ι => v / 8 ≤ |f x - mean f|),
      ∑ j, Level.levRow f a t x j ≤ K / (v / 8 / 2) := by
    intro x hx
    have hx' : v / 8 ≤ |f x - mean f| := (Finset.mem_filter.mp hx).2
    have hdist : v / 8 / 2 ≤ |f x - t| := by
      have h3 := abs_sub_le (f x) t (mean f)
      linarith
    have hne : f x ≠ t := by
      intro h
      rw [h, sub_self, abs_zero] at hdist
      linarith
    have hsumeq : ∑ j, Level.levRow f a t x j = (∑ j, a x j) / |f x - t| := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      show (if f x = t then 1 else a x j / |f x - t|) = _
      rw [if_neg hne]
    rw [hsumeq]
    exact div_le_div₀ hK0.le (hasum x) (by positivity) hdist
  obtain ⟨s, hs⟩ : ∃ s : ℕ, s = ⌈2 ^ 19 * K ^ 3 / v ^ 5⌉₊ := ⟨_, rfl⟩
  obtain ⟨F, hF, hFe⟩ := Short.exists_dtree (Level.lev f t) (Level.levRow f a t) hrow
    (univ.filter fun x : Cube ι => v / 8 ≤ |f x - mean f|) (K / (v / 8 / 2)) hγ hU s
  have hv5 : 0 < v ^ 5 := by positivity
  have hK3 : 1 ≤ K ^ 3 := one_le_pow₀ hK1
  have hv5le : v ^ 5 ≤ 1 := pow_le_one₀ hv.le hv1
  have hsA : 2 ^ 19 * K ^ 3 / v ^ 5 ≤ (s:ℝ) := by rw [hs]; exact Nat.le_ceil _
  have hs_lo : 2 ^ 19 * K ^ 3 ≤ (s:ℝ) * v ^ 5 := by
    rwa [div_le_iff₀ hv5] at hsA
  have hs_hi : (s:ℝ) * v ^ 5 ≤ 2 ^ 20 * K ^ 3 := by
    have h := Nat.ceil_lt_add_one (show (0:ℝ) ≤ 2 ^ 19 * K ^ 3 / v ^ 5 by positivity)
    rw [← hs] at h
    have h' : (s:ℝ) * v ^ 5 ≤ (2 ^ 19 * K ^ 3 / v ^ 5 + 1) * v ^ 5 :=
      mul_le_mul_of_nonneg_right h.le hv5.le
    have h'' : (2 ^ 19 * K ^ 3 / v ^ 5 + 1) * v ^ 5 = 2 ^ 19 * K ^ 3 + v ^ 5 := by
      field_simp
    linarith
  have hs0 : 0 < (s:ℝ) := by
    have : 0 < 2 ^ 19 * K ^ 3 / v ^ 5 := by positivity
    linarith
  obtain ⟨e, he⟩ : ∃ e : ℝ, e = (((univ.filter fun x : Cube ι =>
      v / 8 ≤ |f x - mean f|).filter fun x => F x ≠ Level.lev f t x).card : ℝ)
      / 2 ^ Fintype.card ι := ⟨_, rfl⟩
  rw [← he] at hFe
  have he0 : 0 ≤ e := by rw [he]; positivity
  have he_le : e ≤ v / 32 := arith1 v K _ s e hv hK0 hI' hs_lo hFe
  have hh : Short.DTree s (fun x => if F x then (1:ℝ) else -1) :=
    dtree_comp (fun b : Bool => if b then (1:ℝ) else -1) hF
  have hhb : ∀ x, |(if F x then (1:ℝ) else -1)| ≤ 1 := by
    intro x
    split_ifs <;> simp
  have hcov := cov_lower f hf F t (v / 8) hη htabs
  rw [← he] at hcov
  have hcov2 : v / 8 ≤ mean (fun x => (f x - mean f) * (if F x then (1:ℝ) else -1)) := by
    linarith
  have hM : ∀ j, meanAbsIncr f j ≤ v / (5 * s) := by
    intro j
    by_contra hlt
    push Not at hlt
    have h1 : v / 10 ≤ (s:ℝ) / 2 * meanAbsIncr f j := by
      rw [div_lt_iff₀ (by positivity)] at hlt
      linarith
    have h2 := arith2 v K s (meanAbsIncr f j) (inflR f j) hv hK0 hs_hi h1
      (Level.meanAbsIncr_sq_le f j) (Level.meanAbsIncr_nonneg f j)
    have hc := hcon j
    have hK6 : K ^ 6 = Real.pi ^ 12 * (d:ℝ) ^ 12 := by rw [hK]; ring
    have h3 : 2 ^ 50 * K ^ 6 * inflR f j = 2 ^ 50 * Real.pi ^ 12 * (d:ℝ) ^ 12 * inflR f j := by
      rw [hK6]; ring
    rw [h3] at h2
    linarith
  have hbd := Short.cov_le_of_dtree f (fun x => if F x then (1:ℝ) else -1) s hh hhb
    (v / (5 * s)) (by positivity) hM
  have h8 : (s:ℝ) / 2 * (v / (5 * s)) = v / 10 := by
    field_simp
    norm_num
  rw [h8] at hbd
  have h9 : v / 8 ≤ v / 10 := hcov2.trans ((le_abs_self _).trans hbd)
  linarith

end AASolMain

theorem solution {ι : Type} [Fintype ι] [DecidableEq ι]
    (d : ℕ) (f : Cube ι → ℝ) (hf : ∀ x, |f x| ≤ 1) (hdeg : HasDegreeLE f d)
    (hv : 0 < variance f) :
    ∃ j, variance f ^ 12 ≤ 2 ^ 50 * Real.pi ^ 12 * (d : ℝ) ^ 12 * inflR f j :=
  AASolMain.main_aux d f hf hdeg hv
