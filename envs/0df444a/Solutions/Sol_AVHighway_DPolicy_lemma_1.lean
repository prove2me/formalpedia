-- Prove2me | solution 1 for AVHighway.DPolicy.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T15:06:24.150874+00:00
-- url     : https://prove2.me/submissions/db758e02-940b-4a12-a718-84a377655d92

import Mathlib
import Definitions.Def_AVHighway_DPolicy_LossQueue

set_option autoImplicit false
open AVHighway.DPolicy

theorem avh_wpos (L : ℝ) (hL : 0 < L) (V : ℕ → ℝ) (cap : ℕ)
    (hV : ∀ n, 1 ≤ n → n ≤ cap → 0 < V n) (lam : ℝ) (hlam : 0 < lam) (n : ℕ) (hn : n ≤ cap) :
    0 < weight L V lam n := by
  unfold weight
  apply div_pos (pow_pos (mul_pos hlam hL) _)
  exact mul_pos (Nat.cast_pos.2 (Nat.factorial_pos _))
    (Finset.prod_pos fun k hk => hV k (Finset.mem_Icc.1 hk).1 (le_trans (Finset.mem_Icc.1 hk).2 hn))

theorem avh_shift (L : ℝ) (hL : 0 < L) (V : ℕ → ℝ) (cap : ℕ)
    (hV : ∀ n, 1 ≤ n → n ≤ cap → 0 < V n) (lam : ℝ) (m : ℕ) (hm : m + 1 ≤ cap) :
    ((m + 1 : ℕ) : ℝ) * weight L V lam (m + 1) = lam * L * weight L V lam m / V (m + 1) := by
  have hVm : 0 < V (m + 1) := hV (m + 1) (by omega) hm
  have hP : 0 < ∏ k ∈ Finset.Icc 1 m, V k :=
    Finset.prod_pos fun k hk => hV k (Finset.mem_Icc.1 hk).1 (by have := (Finset.mem_Icc.1 hk).2; omega)
  have hf : (0 : ℝ) < (m.factorial : ℝ) := Nat.cast_pos.2 (Nat.factorial_pos _)
  unfold weight
  rw [Finset.prod_Icc_succ_top (by omega), Nat.factorial_succ]
  push_cast
  field_simp
  ring

theorem avh_key (L : ℝ) (hL : 0 < L) (V : ℕ → ℝ) (cap : ℕ) (hcap : 1 ≤ cap)
    (hV : ∀ n, 1 ≤ n → n ≤ cap → 0 < V n) (lam : ℝ) (hlam : 0 < lam) :
    meanTravelTime L V cap lam =
      L * (∑ n ∈ Finset.range cap, weight L V lam n / V (n + 1)) /
        ∑ n ∈ Finset.range cap, weight L V lam n := by
  have hw := avh_wpos L hL V cap hV lam hlam
  have hS : 0 < ∑ n ∈ Finset.range cap, weight L V lam n :=
    Finset.sum_pos (fun n hn => hw n (by have := Finset.mem_range.1 hn; omega))
      ⟨0, Finset.mem_range.2 (by omega)⟩
  have hZ : ∑ m ∈ Finset.range (cap + 1), weight L V lam m
      = ∑ n ∈ Finset.range cap, weight L V lam n + weight L V lam cap := Finset.sum_range_succ _ _
  have hZpos : 0 < ∑ m ∈ Finset.range (cap + 1), weight L V lam m := by
    rw [hZ]; exact add_pos hS (hw cap le_rfl)
  have hnum : ∑ n ∈ Finset.Icc (1:ℕ) cap, (n : ℝ) * weight L V lam n
      = lam * L * ∑ n ∈ Finset.range cap, weight L V lam n / V (n + 1) := by
    have h1 : ∑ n ∈ Finset.Icc (1:ℕ) cap, (n : ℝ) * weight L V lam n
        = ∑ n ∈ Finset.range cap, ((n + 1 : ℕ) : ℝ) * weight L V lam (n + 1) := by
      rw [Finset.range_eq_Ico, Finset.sum_Ico_add' (fun n : ℕ => (n : ℝ) * weight L V lam n) 0 cap 1]
      rfl
    rw [h1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [avh_shift L hL V cap hV lam m (by have := Finset.mem_range.1 hm; omega)]
    ring
  unfold meanTravelTime throughput stationary
  have : ∑ n ∈ Finset.Icc (1:ℕ) cap, (n : ℝ) * (weight L V lam n / ∑ m ∈ Finset.range (cap + 1), weight L V lam m)
      = (∑ n ∈ Finset.Icc (1:ℕ) cap, (n : ℝ) * weight L V lam n) /
        ∑ m ∈ Finset.range (cap + 1), weight L V lam m := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun n _ => by ring
  rw [this, hnum]
  rw [hZ] at hZpos ⊢
  have hS' := hS.ne'
  have hZ' := hZpos.ne'
  have h3 : 1 - weight L V lam cap / (∑ n ∈ Finset.range cap, weight L V lam n + weight L V lam cap)
      = (∑ n ∈ Finset.range cap, weight L V lam n) /
        (∑ n ∈ Finset.range cap, weight L V lam n + weight L V lam cap) := by
    field_simp
    ring
  rw [h3]
  field_simp

theorem avh_cross (n : ℕ) (c a : ℕ → ℝ) (hc : ∀ m, m < n → 0 ≤ c m) (ha : ∀ m k, m ≤ k → k < n → a m ≤ a k)
    (x y : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y) :
    (∑ m ∈ Finset.range n, x ^ m * c m * a m) * (∑ m ∈ Finset.range n, y ^ m * c m) ≤
      (∑ m ∈ Finset.range n, y ^ m * c m * a m) * (∑ m ∈ Finset.range n, x ^ m * c m) := by
  set G : ℕ → ℕ → ℝ := fun m k => c m * c k * (a k - a m) * (y ^ k * x ^ m - x ^ k * y ^ m) with hG
  have hy : 0 ≤ y := hx.trans hxy
  have hGlt : ∀ m k, m < k → k < n → 0 ≤ G m k := by
    intro m k hmk hk
    obtain ⟨d, rfl⟩ : ∃ d, k = m + d := ⟨k - m, by omega⟩
    have h1 : 0 ≤ a (m + d) - a m := sub_nonneg.2 (ha m (m + d) (by omega) hk)
    have h2 : y ^ (m + d) * x ^ m - x ^ (m + d) * y ^ m = x ^ m * y ^ m * (y ^ d - x ^ d) := by
      ring
    have h3 : 0 ≤ y ^ d - x ^ d := sub_nonneg.2 (pow_le_pow_left₀ hx hxy d)
    simp only [hG]
    rw [h2]
    have := hc m (by omega); have := hc (m + d) hk
    positivity
  have hGsymm : ∀ m k, G m k = G k m := by intro m k; simp only [hG]; ring
  have hGnn : ∀ m ∈ Finset.range n, ∀ k ∈ Finset.range n, 0 ≤ G m k := by
    intro m hm k hk
    have hm := Finset.mem_range.1 hm
    have hk := Finset.mem_range.1 hk
    rcases lt_trichotomy m k with h | h | h
    · exact hGlt m k h hk
    · subst h; simp [hG]
    · rw [hGsymm]; exact hGlt k m h hm
  have hsum : ∑ m ∈ Finset.range n, ∑ k ∈ Finset.range n, G m k
      = 2 * ((∑ m ∈ Finset.range n, y ^ m * c m * a m) * (∑ m ∈ Finset.range n, x ^ m * c m)
        - (∑ m ∈ Finset.range n, x ^ m * c m * a m) * (∑ m ∈ Finset.range n, y ^ m * c m)) := by
    have e : ∀ m k, G m k = (x ^ m * c m) * (y ^ k * c k * a k) - (y ^ m * c m) * (x ^ k * c k * a k)
        - (x ^ m * c m * a m) * (y ^ k * c k) + (y ^ m * c m * a m) * (x ^ k * c k) := by
      intro m k; simp only [hG]; ring
    simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    simp only [← Finset.sum_mul_sum]
    rw [mul_comm (∑ m ∈ Finset.range n, x ^ m * c m)]
    rw [mul_comm (∑ m ∈ Finset.range n, y ^ m * c m)]
    ring
  have : 0 ≤ ∑ m ∈ Finset.range n, ∑ k ∈ Finset.range n, G m k :=
    Finset.sum_nonneg fun m hm => Finset.sum_nonneg fun k hk => hGnn m hm k hk
  rw [hsum] at this
  linarith

theorem solution (L : ℝ) (hL : 0 < L) (V : ℕ → ℝ) (cap : ℕ) (hcap : 1 ≤ cap)
    (hV : ∀ n, 1 ≤ n → n ≤ cap → 0 < V n) (hVanti : AntitoneOn V (Set.Icc 1 cap)) :
    MonotoneOn (meanTravelTime L V cap) (Set.Ioi 0) := by
  intro lam hlam lam' hlam' hle
  have hlam : 0 < lam := hlam
  have hlam' : 0 < lam' := hlam'
  rw [avh_key L hL V cap hcap hV lam hlam, avh_key L hL V cap hcap hV lam' hlam']
  set c : ℕ → ℝ := fun m => 1 / ((m.factorial : ℝ) * ∏ k ∈ Finset.Icc 1 m, V k) with hc
  set a : ℕ → ℝ := fun m => 1 / V (m + 1) with ha
  have hw : ∀ (l : ℝ) (m : ℕ), weight L V l m = (l * L) ^ m * c m := by
    intro l m; simp only [weight, hc]; rw [div_eq_mul_one_div]
  have hcpos : ∀ m, m < cap → 0 < c m := by
    intro m hm
    simp only [hc]
    apply one_div_pos.2
    exact mul_pos (Nat.cast_pos.2 (Nat.factorial_pos _))
      (Finset.prod_pos fun k hk => hV k (Finset.mem_Icc.1 hk).1 (by have := (Finset.mem_Icc.1 hk).2; omega))
  have hanti : ∀ m k, m ≤ k → k < cap → a m ≤ a k := by
    intro m k hmk hk
    simp only [ha]
    have h1 : V (k + 1) ≤ V (m + 1) :=
      hVanti ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega)
    exact one_div_le_one_div_of_le (hV (k + 1) (by omega) (by omega)) h1
  have hN : ∀ l : ℝ, ∑ n ∈ Finset.range cap, weight L V l n / V (n + 1)
      = ∑ m ∈ Finset.range cap, (l * L) ^ m * c m * a m := by
    intro l
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [hw]; simp only [ha]; rw [div_eq_mul_one_div]
  have hD : ∀ l : ℝ, ∑ n ∈ Finset.range cap, weight L V l n
      = ∑ m ∈ Finset.range cap, (l * L) ^ m * c m := by
    intro l
    exact Finset.sum_congr rfl fun m _ => hw l m
  rw [hN, hN, hD, hD]
  have hDpos : ∀ l : ℝ, 0 < l → 0 < ∑ m ∈ Finset.range cap, (l * L) ^ m * c m := by
    intro l hl
    exact Finset.sum_pos (fun m hm => mul_pos (pow_pos (mul_pos hl hL) _) (hcpos m (Finset.mem_range.1 hm)))
      ⟨0, Finset.mem_range.2 (by omega)⟩
  have hcr := avh_cross cap c a (fun m hm => (hcpos m hm).le) hanti (lam * L) (lam' * L)
    (mul_pos hlam hL).le (mul_le_mul_of_nonneg_right hle hL.le)
  rw [mul_div_assoc, mul_div_assoc]
  apply mul_le_mul_of_nonneg_left _ hL.le
  rw [div_le_div_iff₀ (hDpos lam hlam) (hDpos lam' hlam')]
  exact hcr
