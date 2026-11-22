-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_HintUpstream4620261120
-- name    : LinearSetReconciliation327_Main_HintUpstream4620261120
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-22T08:40:39.39053+00:00
-- url     : https://prove2.me/theorems/90782b6e-eb5f-4cb9-98ff-ae48d2fd61a3
-- title:
--   LinearSetReconciliation327 — HintUpstream46 (2026-11-20)
-- statement:
--   Internal dependency module `Definitions.LinearSetReconciliation327_Main_HintUpstream4620261120` of the LinearSetReconciliation327 development that formalizes Theorem 5.1 (Performance of HintSketch). It factors the toggle-program / decoder construction into a small node so that every node compiles well inside the platform's compilation limit; it contains only the definitions, structures, lemmas and proofs belonging to this module, and it is sorry-free. This definition is a supporting node, not a statement of independent mathematical interest.
-- source:
--   Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, STOC 2027 submission #327 (October 2026), Theorem 5.1 (HintSketch), PDF p.19 (printed p.18)

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_Basic

set_option autoImplicit false

open scoped ENNReal
open Finset

namespace LinearSetReconciliation327.Main.HintUpstream46

/-! ## Auxiliary lemmas for Lemma 4.6 (summing prefix tails) -/

lemma G_nonneg (a : ℕ) (z : ℝ) : 0 ≤ G a z := by
  unfold G
  exact le_min zero_le_one (Real.rpow_nonneg (by norm_num) _)

lemma G_le_one (a : ℕ) (z : ℝ) : G a z ≤ 1 := min_le_left _ _

lemma G_le_rpow (a : ℕ) (z : ℝ) : G a z ≤ (2 : ℝ) ^ (z - (a : ℝ)) := min_le_right _ _

/-- `2^{-r} = (1/2)^r` for natural `r`. -/
lemma two_rpow_neg_nat (r : ℕ) : (2 : ℝ) ^ (-(r : ℝ)) = (1 / 2 : ℝ) ^ r := by
  have h1 : (2 : ℝ) ^ (-(r : ℝ)) = ((2 : ℝ) ^ (-1 : ℝ)) ^ (r : ℝ) := by
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  rw [h1, Real.rpow_neg_one, Real.rpow_natCast]
  norm_num

/-- Tail estimate: if `z < k + 1` and `a ≥ k + 1` then `G a z ≤ (1/2)^{a-k-1}`. -/
lemma G_tail_le {z : ℝ} {k a : ℕ} (hz : z < (k : ℝ) + 1) (ha : k + 1 ≤ a) :
    G a z ≤ (1 / 2 : ℝ) ^ (a - (k + 1)) := by
  have hcast : ((a - (k + 1) : ℕ) : ℝ) = (a : ℝ) - ((k : ℝ) + 1) := by
    have h := Nat.sub_add_cancel ha
    have h' := congrArg (fun x : ℕ => (x : ℝ)) h
    push_cast at h'
    linarith
  have h2 : z - (a : ℝ) ≤ -(((a - (k + 1) : ℕ)) : ℝ) := by
    linarith
  calc G a z ≤ (2 : ℝ) ^ (z - (a : ℝ)) := G_le_rpow a z
    _ ≤ (2 : ℝ) ^ (-(((a - (k + 1) : ℕ)) : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) h2
    _ = (1 / 2 : ℝ) ^ (a - (k + 1)) := two_rpow_neg_nat _

lemma tsum_half_pow : ∑' r : ℕ, (1 / 2 : ℝ) ^ r = 2 := by
  rw [tsum_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)]
  norm_num

lemma summable_half_pow : Summable fun r : ℕ => (1 / 2 : ℝ) ^ r :=
  summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)

lemma tsum_half_pow_mul : ∑' r : ℕ, (r : ℝ) * (1 / 2 : ℝ) ^ r = 2 := by
  rw [tsum_coe_mul_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)]
  norm_num

lemma summable_half_pow_mul : Summable fun r : ℕ => (r : ℝ) * (1 / 2 : ℝ) ^ r := by
  simpa [div_pow] using
    summable_pow_mul_geometric_of_norm_lt_one (k := 1) (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)

/-- Shifting a summable nonnegative sequence down by `k` only decreases its finite sums. -/
lemma sum_shift_le_tsum {f : ℕ → ℝ} (hf : ∀ i, 0 ≤ f i) (hsum : Summable f)
    {s : Finset ℕ} {k : ℕ} (hk : ∀ a ∈ s, k ≤ a) :
    ∑ a ∈ s, f (a - k) ≤ ∑' i, f i := by
  have hinj : Set.InjOn (fun a : ℕ => a - k) (s : Set ℕ) := by
    intro a ha b hb hab
    have h1 := hk a ha
    have h2 := hk b hb
    have hab' : a - k = b - k := hab
    omega
  rw [← Finset.sum_image hinj]
  exact hsum.sum_le_tsum _ (fun i _ => hf i)

lemma head_card_le (n k : ℕ) :
    ((range n).filter (fun a => a ≤ k)).card ≤ k + 1 := by
  have h : (range n).filter (fun a => a ≤ k) ⊆ range (k + 1) := by
    intro a ha
    simp only [mem_filter, mem_range] at ha
    simp only [mem_range]
    omega
  calc ((range n).filter (fun a => a ≤ k)).card ≤ (range (k + 1)).card := card_le_card h
    _ = k + 1 := by simp

/-- Head of the first sum: the first `k+1` terms contribute at most `k+1`. -/
lemma sum_G_head_le (z : ℝ) (k n : ℕ) :
    ∑ a ∈ (range n).filter (fun a => a ≤ k), G a z ≤ (k : ℝ) + 1 := by
  classical
  have h1 : ∑ a ∈ (range n).filter (fun a => a ≤ k), G a z
      ≤ ∑ a ∈ (range n).filter (fun a => a ≤ k), (1 : ℝ) :=
    sum_le_sum (fun a _ => G_le_one a z)
  rw [sum_const, nsmul_eq_mul, mul_one] at h1
  have h2 : ((((range n).filter (fun a => a ≤ k)).card : ℕ) : ℝ) ≤ (k : ℝ) + 1 := by
    have hc : (((range n).filter (fun a => a ≤ k)).card : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
      exact_mod_cast head_card_le n k
    push_cast at hc
    linarith
  linarith

/-- Tail of the first sum: geometric decay contributes at most `2`. -/
lemma sum_G_tail_le (z : ℝ) (k n : ℕ) (hkz' : z < (k : ℝ) + 1) :
    ∑ a ∈ (range n).filter (fun a => ¬ a ≤ k), G a z ≤ 2 := by
  classical
  have h1 : ∑ a ∈ (range n).filter (fun a => ¬ a ≤ k), G a z
      ≤ ∑ a ∈ (range n).filter (fun a => ¬ a ≤ k), (1 / 2 : ℝ) ^ (a - (k + 1)) := by
    refine sum_le_sum (fun a ha => ?_)
    simp only [mem_filter, mem_range] at ha
    exact G_tail_le hkz' (by omega)
  have h2 : ∑ a ∈ (range n).filter (fun a => ¬ a ≤ k), (1 / 2 : ℝ) ^ (a - (k + 1)) ≤ 2 := by
    have h := sum_shift_le_tsum (f := fun r : ℕ => (1 / 2 : ℝ) ^ r) (fun i => by positivity)
      summable_half_pow (s := (range n).filter (fun a => ¬ a ≤ k)) (k := k + 1) (fun a ha => by
        simp only [mem_filter, mem_range] at ha
        omega)
    rw [tsum_half_pow] at h
    exact h
  linarith

/-- Head of the second sum: at most `(k+1) z ≤ z(1+z)`. -/
lemma sum_aG_head_le (z : ℝ) (k n : ℕ) (hz : 0 ≤ z) (hkz : (k : ℝ) ≤ z) :
    ∑ a ∈ (range n).filter (fun a => a ≤ k), (a : ℝ) * G a z ≤ z * (z + 1) := by
  classical
  have h1 : ∑ a ∈ (range n).filter (fun a => a ≤ k), (a : ℝ) * G a z
      ≤ ∑ a ∈ (range n).filter (fun a => a ≤ k), z := by
    refine sum_le_sum (fun a ha => ?_)
    simp only [mem_filter, mem_range] at ha
    have ha_le : (a : ℝ) ≤ (k : ℝ) := by exact_mod_cast ha.2
    have hG1 : G a z ≤ 1 := G_le_one a z
    have hG0 : 0 ≤ G a z := G_nonneg a z
    have ha0 : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg a
    nlinarith
  rw [sum_const, nsmul_eq_mul] at h1
  have hcard : ((((range n).filter (fun a => a ≤ k)).card : ℕ) : ℝ) ≤ z + 1 := by
    have hc : (((range n).filter (fun a => a ≤ k)).card : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
      exact_mod_cast head_card_le n k
    push_cast at hc
    linarith
  nlinarith [mul_le_mul_of_nonneg_right hcard hz]

/-- Tail of the second sum: `∑_{a>k} a G_a(z) ≤ 2k+4 ≤ 2z+4`. -/
lemma sum_aG_tail_le (z : ℝ) (k n : ℕ) (hkz : (k : ℝ) ≤ z)
    (hkz' : z < (k : ℝ) + 1) :
    ∑ a ∈ (range n).filter (fun a => ¬ a ≤ k), (a : ℝ) * G a z ≤ 2 * z + 4 := by
  classical
  set T : Finset ℕ := (range n).filter (fun a => ¬ a ≤ k) with hT
  have h1 : ∑ a ∈ T, (a : ℝ) * G a z
      ≤ ∑ a ∈ T, (a : ℝ) * (1 / 2 : ℝ) ^ (a - (k + 1)) := by
    refine sum_le_sum (fun a ha => ?_)
    rw [hT] at ha
    simp only [mem_filter, mem_range] at ha
    have hka : k + 1 ≤ a := by omega
    have hgt : G a z ≤ (1 / 2 : ℝ) ^ (a - (k + 1)) := G_tail_le hkz' hka
    have hG0 : 0 ≤ G a z := G_nonneg a z
    have hp0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (a - (k + 1)) := by positivity
    have ha0 : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg a
    nlinarith
  have hdecomp : ∑ a ∈ T, (a : ℝ) * (1 / 2 : ℝ) ^ (a - (k + 1))
      = ((k : ℝ) + 1) * (∑ a ∈ T, (1 / 2 : ℝ) ^ (a - (k + 1)))
        + ∑ a ∈ T, (((a - (k + 1) : ℕ)) : ℝ) * (1 / 2 : ℝ) ^ (a - (k + 1)) := by
    have hpt : ∀ a ∈ T, (a : ℝ) * (1 / 2 : ℝ) ^ (a - (k + 1))
        = ((k : ℝ) + 1) * (1 / 2 : ℝ) ^ (a - (k + 1))
          + (((a - (k + 1) : ℕ)) : ℝ) * (1 / 2 : ℝ) ^ (a - (k + 1)) := by
      intro a ha
      rw [hT] at ha
      simp only [mem_filter, mem_range] at ha
      have hka : k + 1 ≤ a := by omega
      have hcast : (a : ℝ) = (k : ℝ) + 1 + ((a - (k + 1) : ℕ) : ℝ) := by
        have h := Nat.sub_add_cancel hka
        have h' := congrArg (fun x : ℕ => (x : ℝ)) h
        push_cast at h'
        linarith
      rw [hcast]
      ring
    rw [sum_congr rfl hpt, sum_add_distrib, mul_sum]
  have hb1 : ∑ a ∈ T, (1 / 2 : ℝ) ^ (a - (k + 1)) ≤ 2 := by
    have h := sum_shift_le_tsum (f := fun r : ℕ => (1 / 2 : ℝ) ^ r) (fun i => by positivity)
      summable_half_pow (s := T) (k := k + 1)
      (fun a ha => by rw [hT] at ha; simp only [mem_filter] at ha; omega)
    rw [tsum_half_pow] at h
    exact h
  have hb2 : ∑ a ∈ T, (((a - (k + 1) : ℕ)) : ℝ) * (1 / 2 : ℝ) ^ (a - (k + 1)) ≤ 2 := by
    have h := sum_shift_le_tsum (f := fun r : ℕ => (r : ℝ) * (1 / 2 : ℝ) ^ r)
      (fun i => by positivity) summable_half_pow_mul (s := T) (k := k + 1)
      (fun a ha => by rw [hT] at ha; simp only [mem_filter] at ha; omega)
    rw [tsum_half_pow_mul] at h
    exact h
  calc ∑ a ∈ T, (a : ℝ) * G a z
      ≤ ∑ a ∈ T, (a : ℝ) * (1 / 2 : ℝ) ^ (a - (k + 1)) := h1
    _ = ((k : ℝ) + 1) * (∑ a ∈ T, (1 / 2 : ℝ) ^ (a - (k + 1)))
          + ∑ a ∈ T, (((a - (k + 1) : ℕ)) : ℝ) * (1 / 2 : ℝ) ^ (a - (k + 1)) := hdecomp
    _ ≤ 2 * z + 4 := by
        have h2 : ((k : ℝ) + 1) * (∑ a ∈ T, (1 / 2 : ℝ) ^ (a - (k + 1))) ≤ ((k : ℝ) + 1) * 2 :=
          mul_le_mul_of_nonneg_left hb1 (by positivity)
        linarith

/-- `∑_{a<n} G_a(z) ≤ z + 32`. -/
lemma sum_G_le (z : ℝ) (hz : 0 ≤ z) (n : ℕ) :
    ∑ a ∈ range n, G a z ≤ z + 32 := by
  classical
  set k := Nat.floor z with hk
  have hkz : (k : ℝ) ≤ z := Nat.floor_le hz
  have hkz' : z < (k : ℝ) + 1 := Nat.lt_floor_add_one z
  have hsplit : ∑ a ∈ range n, G a z
      = ∑ a ∈ (range n).filter (fun a => a ≤ k), G a z
        + ∑ a ∈ (range n).filter (fun a => ¬ a ≤ k), G a z :=
    (sum_filter_add_sum_filter_not _ _ _).symm
  rw [hsplit]
  have hhead := sum_G_head_le z k n
  have htail := sum_G_tail_le z k n hkz'
  linarith

/-- `∑_{a<n} a·G_a(z) ≤ 32(1+z)^2`. -/
lemma sum_aG_le (z : ℝ) (hz : 0 ≤ z) (n : ℕ) :
    ∑ a ∈ range n, (a : ℝ) * G a z ≤ 32 * (1 + z) ^ 2 := by
  classical
  set k := Nat.floor z with hk
  have hkz : (k : ℝ) ≤ z := Nat.floor_le hz
  have hkz' : z < (k : ℝ) + 1 := Nat.lt_floor_add_one z
  have hsplit : ∑ a ∈ range n, (a : ℝ) * G a z
      = ∑ a ∈ (range n).filter (fun a => a ≤ k), (a : ℝ) * G a z
        + ∑ a ∈ (range n).filter (fun a => ¬ a ≤ k), (a : ℝ) * G a z :=
    (sum_filter_add_sum_filter_not _ _ _).symm
  rw [hsplit]
  have hhead := sum_aG_head_le z k n hz hkz
  have htail := sum_aG_tail_le z k n hkz hkz'
  have hfin : z * (z + 1) + (2 * z + 4) ≤ 32 * (1 + z) ^ 2 := by
    nlinarith [hz, sq_nonneg z]
  linarith

/-- Lemma 4.6 (Summing prefix tails), PDF p.17 (printed p.16): one absolute `C`, both sums over all
`a ≥ 0`, as extended nonnegative sums. -/
theorem lemma_4_6 :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℝ, 0 ≤ z →
      (∑' a : ℕ, ENNReal.ofReal (G a z)) ≤ ENNReal.ofReal (z + C) ∧
      (∑' a : ℕ, ENNReal.ofReal ((a : ℝ) * G a z)) ≤ ENNReal.ofReal (C * (1 + z) ^ 2) := by
  refine ⟨32, by norm_num, fun z hz => ⟨?_, ?_⟩⟩
  · refine ENNReal.tsum_le_of_sum_range_le (fun n => ?_)
    rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => G_nonneg a z)]
    exact ENNReal.ofReal_le_ofReal (sum_G_le z hz n)
  · refine ENNReal.tsum_le_of_sum_range_le (fun n => ?_)
    rw [← ENNReal.ofReal_sum_of_nonneg
      (fun a _ => mul_nonneg (Nat.cast_nonneg a) (G_nonneg a z))]
    exact ENNReal.ofReal_le_ofReal (sum_aG_le z hz n)

end LinearSetReconciliation327.Main.HintUpstream46

#print axioms LinearSetReconciliation327.Main.HintUpstream46.lemma_4_6


