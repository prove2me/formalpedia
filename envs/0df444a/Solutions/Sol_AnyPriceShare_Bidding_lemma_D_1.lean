-- Prove2me | solution 1 for AnyPriceShare.Bidding.lemma_D_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T01:52:48.313812+00:00
-- url     : https://prove2.me/submissions/c0a36ddf-e53f-4f60-acc6-d7fa231d2423

import Mathlib
import Definitions.Def_AnyPriceShare_Bidding_Basic

open AnyPriceShare.Bidding

namespace APSD1Sol

/-- The set whose supremum is the TPS. -/
theorem tps_bdd {m : ℕ} (u : Fin m → ℝ) (β : ℝ) (hβ : 0 < β) (S : Finset (Fin m)) :
    BddAbove {z : ℝ | β * ∑ j ∈ S, min (u j) z = z} := by
  refine ⟨β * ∑ j ∈ S, u j, fun z hz => ?_⟩
  simp only [Set.mem_ofPred_eq] at hz
  rw [← hz]
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => min_le_left _ _) hβ.le

theorem tps_zero_mem {m : ℕ} (u : Fin m → ℝ) (hu : ∀ j, 0 ≤ u j) (β : ℝ) (S : Finset (Fin m)) :
    (0 : ℝ) ∈ {z : ℝ | β * ∑ j ∈ S, min (u j) z = z} := by
  simp only [Set.mem_ofPred_eq]
  rw [Finset.sum_eq_zero fun j _ => min_eq_right (hu j)]; simp

theorem tps_cont {m : ℕ} (u : Fin m → ℝ) (β : ℝ) (S : Finset (Fin m)) :
    Continuous fun z : ℝ => β * ∑ j ∈ S, min (u j) z := by
  fun_prop

theorem tps_mem {m : ℕ} (u : Fin m → ℝ) (hu : ∀ j, 0 ≤ u j) (β : ℝ) (hβ : 0 < β)
    (S : Finset (Fin m)) : β * ∑ j ∈ S, min (u j) (tps β u S) = tps β u S := by
  have hc : IsClosed {z : ℝ | β * ∑ j ∈ S, min (u j) z = z} :=
    isClosed_eq (tps_cont u β S) continuous_id
  exact hc.csSup_mem ⟨0, tps_zero_mem u hu β S⟩ (tps_bdd u β hβ S)

theorem tps_nonneg {m : ℕ} (u : Fin m → ℝ) (hu : ∀ j, 0 ≤ u j) (β : ℝ) (hβ : 0 < β)
    (S : Finset (Fin m)) : 0 ≤ tps β u S :=
  le_csSup (tps_bdd u β hβ S) (tps_zero_mem u hu β S)

/-- Above the TPS the capped proportional share is strictly below the cap (intermediate value
theorem). -/
theorem tps_lt {m : ℕ} (u : Fin m → ℝ) (hu : ∀ j, 0 ≤ u j) (β : ℝ) (hβ : 0 < β)
    (S : Finset (Fin m)) (z : ℝ) (hz : tps β u S < z) : β * ∑ j ∈ S, min (u j) z < z := by
  by_contra hcon
  push Not at hcon
  set g : ℝ → ℝ := fun t => β * ∑ j ∈ S, min (u j) t - t with hg
  have hgc : Continuous g := (tps_cont u β S).sub continuous_id
  set b' := max z (β * ∑ j ∈ S, u j)
  have hzb : z ≤ b' := le_max_left _ _
  have hgz : 0 ≤ g z := by simp only [hg]; linarith
  have hgb : g b' ≤ 0 := by
    have : β * ∑ j ∈ S, min (u j) b' ≤ β * ∑ j ∈ S, u j :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => min_le_left _ _) hβ.le
    simp only [hg]; linarith [le_max_right z (β * ∑ j ∈ S, u j)]
  obtain ⟨t, ⟨ht1, -⟩, ht⟩ :=
    intermediate_value_Icc' hzb hgc.continuousOn ⟨hgb, hgz⟩
  have hmem : t ∈ {z : ℝ | β * ∑ j ∈ S, min (u j) z = z} := by
    simp only [Set.mem_ofPred_eq]; simp only [hg] at ht; linarith
  have := le_csSup (tps_bdd u β hβ S) hmem
  unfold tps at hz
  linarith


end APSD1Sol

open APSD1Sol in
theorem solution {m : ℕ} (u : Fin m → ℝ) (hu : ∀ j, 0 ≤ u j)
    (S K : Finset (Fin m)) (hK : K ⊂ S)
    (β : ℝ) (hβ : 0 < β) (hβK : β ≤ 1 / ((K.card : ℝ) + 1)) :
    tps β u S ≤ tps (β / (1 - (K.card : ℝ) * β)) u (S \ K) := by
  set z := tps β u S
  set κ : ℝ := (K.card : ℝ) with hκ
  have hκ0 : 0 ≤ κ := Nat.cast_nonneg _
  -- `1 - |K| β ≥ β > 0`
  have hden : β ≤ 1 - κ * β := by
    rw [le_div_iff₀ (by positivity)] at hβK; linarith
  have hd : 0 < 1 - κ * β := lt_of_lt_of_le hβ hden
  set β' := β / (1 - κ * β)
  have hβ' : 0 < β' := div_pos hβ hd
  have hz0 : 0 ≤ z := tps_nonneg u hu β hβ S
  have hfix : β * ∑ j ∈ S, min (u j) z = z := tps_mem u hu β hβ S
  -- split the capped sum over `K` and `S ∖ K`
  have hsplit : ∑ j ∈ S, min (u j) z ≤ κ * z + ∑ j ∈ S \ K, min (u j) z := by
    rw [← Finset.sum_sdiff hK.subset]
    have : ∑ j ∈ K, min (u j) z ≤ κ * z := by
      calc ∑ j ∈ K, min (u j) z ≤ ∑ j ∈ K, z := Finset.sum_le_sum fun j _ => min_le_right _ _
        _ = κ * z := by simp [κ]
    linarith
  -- rearranging: `z ≤ β' ∑_{S ∖ K} min(u_j, z)`
  have hle : z ≤ β' * ∑ j ∈ S \ K, min (u j) z := by
    have h1 : z ≤ β * (κ * z) + β * ∑ j ∈ S \ K, min (u j) z := by
      have := mul_le_mul_of_nonneg_left hsplit hβ.le
      linarith
    have h2 : z * (1 - κ * β) ≤ β * ∑ j ∈ S \ K, min (u j) z := by nlinarith
    simp only [β']
    rw [div_mul_eq_mul_div, le_div_iff₀ hd]
    linarith
  by_contra hcon
  push Not at hcon
  have := tps_lt u hu β' hβ' (S \ K) z hcon
  linarith
