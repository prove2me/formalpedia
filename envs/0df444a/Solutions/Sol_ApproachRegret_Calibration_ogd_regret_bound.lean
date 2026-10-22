-- Prove2me | solution 1 for ApproachRegret.Calibration.ogd_regret_bound
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:39:54.747463+00:00
-- url     : https://prove2.me/submissions/eda35002-c7f6-4787-b347-a53b5cd226a5

import Mathlib
import Definitions.Def_ApproachRegret_Calibration_Game
import Definitions.Def_ApproachRegret_Calibration_Algorithms

set_option autoImplicit false
open scoped InnerProductSpace
open ApproachRegret.Calibration

theorem proj_aux {n : ℕ} (K : Set (ApproachRegret.ToOLO.E n)) (hK : Convex ℝ K)
    (y z u : ApproachRegret.ToOLO.E n) (hz : IsProj K y z) (hu : u ∈ K) :
    ‖z - u‖ ^ 2 ≤ ‖y - u‖ ^ 2 := by
  have key : ∀ s : ℝ, 0 < s → s ≤ 1 → 0 ≤ 2 * ⟪z - y, u - z⟫_ℝ + s * ‖u - z‖ ^ 2 := by
    intro s hs0 hs1
    have e : z + s • (u - z) = (1 - s) • z + s • u := by module
    have hzs : z + s • (u - z) ∈ K := by
      rw [e]; exact hK hz.1 hu (by linarith) hs0.le (by ring)
    have h1 := hz.2 _ hzs
    have h1' : ‖z - y‖ ^ 2 ≤ ‖z + s • (u - z) - y‖ ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h1 2
    have h2 : ‖z + s • (u - z) - y‖ ^ 2 =
        ‖z - y‖ ^ 2 + 2 * s * ⟪z - y, u - z⟫_ℝ + s ^ 2 * ‖u - z‖ ^ 2 := by
      have : z + s • (u - z) - y = (z - y) + s • (u - z) := by abel
      rw [this, norm_add_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
      ring
    rw [h2] at h1'
    have h3 : 0 ≤ s * (2 * ⟪z - y, u - z⟫_ℝ + s * ‖u - z‖ ^ 2) := by nlinarith
    exact nonneg_of_mul_nonneg_right h3 hs0
  have hin : 0 ≤ ⟪z - y, u - z⟫_ℝ := by
    by_contra hneg
    push_neg at hneg
    set δ := -⟪z - y, u - z⟫_ℝ with hδ
    have hδ0 : 0 < δ := by linarith
    set N := ‖u - z‖ ^ 2 with hN
    have hN0 : 0 ≤ N := by positivity
    set s := min 1 (δ / (N + 1)) with hs
    have hs0 : 0 < s := lt_min one_pos (div_pos hδ0 (by linarith))
    have hs1 : s ≤ 1 := min_le_left _ _
    have hsd : s ≤ δ / (N + 1) := min_le_right _ _
    have := key s hs0 hs1
    have h5 : s * (N + 1) ≤ δ := by
      calc s * (N + 1) ≤ δ / (N + 1) * (N + 1) := by gcongr
        _ = δ := by field_simp
    nlinarith
  have hexp : ‖y - u‖ ^ 2 = ‖y - z‖ ^ 2 + 2 * ⟪z - y, u - z⟫_ℝ + ‖z - u‖ ^ 2 := by
    have : y - u = (y - z) + (z - u) := by abel
    rw [this, norm_add_sq_real]
    have : ⟪y - z, z - u⟫_ℝ = ⟪z - y, u - z⟫_ℝ := by
      rw [← neg_sub z y, ← neg_sub u z, inner_neg_neg]
    rw [this]
  nlinarith [sq_nonneg ‖y - z‖]

theorem solution {n : ℕ} (K : Set (ApproachRegret.ToOLO.E n)) (hKne : K.Nonempty) (hKc : IsClosed K)
    (hKcvx : Convex ℝ K) (T : ℕ) (hT : 1 ≤ T) (D G : ℝ) (hD : 0 < D) (hG : 0 < G)
    (g θ : ℕ → ApproachRegret.ToOLO.E n) (hθ1 : θ 1 ∈ K) (hdiam : ∀ x ∈ K, ‖x - θ 1‖ ≤ D)
    (hg : ∀ t, 1 ≤ t → t ≤ T → ‖g t‖ ≤ G)
    (hrun : IsOGDRun K (D / (G * Real.sqrt T)) T g θ) :
    linRegret K T g θ ≤ D * G * Real.sqrt T := by
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  have hsq : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT0
  have hsq2 : Real.sqrt T ^ 2 = T := Real.sq_sqrt hT0.le
  generalize Real.sqrt (T : ℝ) = s at hsq hsq2 hrun ⊢
  set η := D / (G * s) with hη
  have hη0 : 0 < η := by positivity
  -- per-round inequality
  have step : ∀ u ∈ K, ∀ t, 1 ≤ t → t ≤ T →
      2 * η * ⟪g t, θ t - u⟫_ℝ ≤ ‖θ t - u‖ ^ 2 - ‖θ (t + 1) - u‖ ^ 2 + η ^ 2 * ‖g t‖ ^ 2 := by
    intro u hu t ht1 htT
    have h := proj_aux K hKcvx _ _ u (hrun t ht1 htT) hu
    have e : θ t - η • g t - u = (θ t - u) - η • g t := by abel
    have hL : ‖θ t - η • g t - u‖ ^ 2 =
        ‖θ t - u‖ ^ 2 - 2 * η * ⟪g t, θ t - u⟫_ℝ + η ^ 2 * ‖g t‖ ^ 2 := by
      rw [e, norm_sub_sq_real (θ t - u) (η • g t), inner_smul_right, norm_smul, mul_pow,
        Real.norm_eq_abs, sq_abs, real_inner_comm]
      ring
    rw [hL] at h
    linarith
  have tele : ∀ u ∈ K, ∀ m, m ≤ T →
      2 * η * ∑ t ∈ Finset.Icc 1 m, ⟪g t, θ t - u⟫_ℝ ≤
        ‖θ 1 - u‖ ^ 2 - ‖θ (m + 1) - u‖ ^ 2 + η ^ 2 * ∑ t ∈ Finset.Icc 1 m, ‖g t‖ ^ 2 := by
    intro u hu m
    induction m with
    | zero => intro _; simp
    | succ m ih =>
      intro hm
      rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega)]
      have h1 := ih (by omega)
      have h2 := step u hu (m + 1) (by omega) hm
      nlinarith
  have hbound : ∀ u ∈ K, ∑ t ∈ Finset.Icc 1 T, ⟪g t, θ t⟫_ℝ - D * G * s ≤
      ∑ t ∈ Finset.Icc 1 T, ⟪g t, u⟫_ℝ := by
    intro u hu
    have h1 := tele u hu T le_rfl
    have hsum : ∑ t ∈ Finset.Icc 1 T, ‖g t‖ ^ 2 ≤ ∑ t ∈ Finset.Icc 1 T, G ^ 2 := by
      apply Finset.sum_le_sum
      intro t ht
      rw [Finset.mem_Icc] at ht
      exact pow_le_pow_left₀ (norm_nonneg _) (hg t ht.1 ht.2) 2
    simp only [Finset.sum_const, Nat.card_Icc, add_tsub_cancel_right, nsmul_eq_mul] at hsum
    have hd : ‖θ 1 - u‖ ≤ D := by rw [norm_sub_rev]; exact hdiam u hu
    have hd2 : ‖θ 1 - u‖ ^ 2 ≤ D ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hd 2
    have hsub : ∑ t ∈ Finset.Icc 1 T, ⟪g t, θ t - u⟫_ℝ =
        ∑ t ∈ Finset.Icc 1 T, ⟪g t, θ t⟫_ℝ - ∑ t ∈ Finset.Icc 1 T, ⟪g t, u⟫_ℝ := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun t _ => inner_sub_right _ _ _)
    rw [hsub] at h1
    have e1 : D ^ 2 + η ^ 2 * (T * G ^ 2) = 2 * η * (D * G * s) := by
      rw [hη, ← hsq2]; field_simp; ring
    have h3 : 2 * η * (∑ t ∈ Finset.Icc 1 T, ⟪g t, θ t⟫_ℝ - ∑ t ∈ Finset.Icc 1 T, ⟪g t, u⟫_ℝ) ≤
        2 * η * (D * G * s) := by
      have : ‖θ (T + 1) - u‖ ^ 2 ≥ 0 := by positivity
      have hη2 : η ^ 2 * ∑ t ∈ Finset.Icc 1 T, ‖g t‖ ^ 2 ≤ η ^ 2 * (T * G ^ 2) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
      linarith
    have h2η : 0 < 2 * η := by positivity
    have := le_of_mul_le_mul_left h3 h2η
    linarith
  unfold linRegret
  have himg : ∑ t ∈ Finset.Icc 1 T, ⟪g t, θ t⟫_ℝ - D * G * s ≤
      sInf ((fun x => ∑ t ∈ Finset.Icc 1 T, ⟪g t, x⟫_ℝ) '' K) := by
    apply le_csInf (hKne.image _)
    rintro _ ⟨u, hu, rfl⟩
    exact hbound u hu
  linarith
