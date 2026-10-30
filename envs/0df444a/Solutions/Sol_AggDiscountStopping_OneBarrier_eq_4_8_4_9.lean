-- Prove2me | solution 1 for AggDiscountStopping.OneBarrier.eq_4_8_4_9
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T19:12:28.141927+00:00
-- url     : https://prove2.me/submissions/7996c33f-cb63-4860-97f6-a4371a7667a0

import Mathlib
import Definitions.Def_AggDiscountStopping_OneBarrier_Setting
import Theorems.Thm_AggDiscountStopping_OneBarrier_proposition_4_4

open MeasureTheory Set Filter Topology
open scoped NNReal
open AggDiscountStopping.OneBarrier

theorem solution (M : Model) (hM : M.Valid) (hCi : M.CondI) (hCii1 : M.CondII1)
    (φ : ℝ → ℝ → ℝ) (hφ : ∀ r, 0 ≤ r → IsDecreasingSolution M r (φ r))
    (hG : ∀ a, 0 < a → Integrable (fun r => deriv (φ r) a / φ r a) M.F) :
    StrictMonoOn (fun a => G M φ a + 1 / (M.K - a)) (Ioo 0 M.K) ∧
      ContinuousOn (fun a => G M φ a + 1 / (M.K - a)) (Ioo 0 M.K) ∧
      (∀ᶠ a in 𝓝[<] M.K, 0 < G M φ a + 1 / (M.K - a)) ∧
      ∃ aStar : ℝ, 0 ≤ aStar ∧ aStar < M.K ∧
        (0 < aStar → G M φ aStar + 1 / (M.K - aStar) = 0) ∧
        ∀ a ∈ Ioo 0 M.K, (0 < G M φ a + 1 / (M.K - a) ↔ aStar < a) := by
  have hK := hM.K_pos
  have hae : ∀ᵐ r ∂M.F, 0 ≤ r := by
    rw [ae_iff]
    have : {r : ℝ | ¬ 0 ≤ r} = Iio 0 := by ext r; simp
    rw [this]; exact hM.F_nonneg
  set gr : ℝ → ℝ → ℝ := fun r a => deriv (φ r) a / φ r a with hgr
  -- monotonicity of φ′_r/φ_r in a (Proposition 4.4)
  have hmono_r : ∀ r, 0 ≤ r → MonotoneOn (gr r) (Ioi 0) := by
    intro r hr a ha b hb hab
    have h := proposition_4_4 M hM hCi hCii1 r hr (φ r) (hφ r hr) ha hb hab
    simp only [mtilde, neg_div] at h
    simp only [hgr]
    linarith
  -- G is monotone on (0, ∞)
  have hGmono : MonotoneOn (G M φ) (Ioi 0) := by
    intro a ha b hb hab
    unfold G
    apply integral_mono_ae (hG a ha) (hG b hb)
    filter_upwards [hae] with r hr
    exact hmono_r r hr ha hb hab
  -- G is continuous on (0, ∞)
  have hGcont : ∀ a0, 0 < a0 → ContinuousAt (G M φ) a0 := by
    intro a0 ha0
    unfold G
    have hnb : Ioo (a0 / 2) (2 * a0) ∈ 𝓝 a0 := Ioo_mem_nhds (by linarith) (by linarith)
    apply MeasureTheory.continuousAt_of_dominated
      (bound := fun r => ‖gr r (a0 / 2)‖ + ‖gr r (2 * a0)‖)
    · filter_upwards [hnb] with a ha
      exact (hG a (by linarith [ha.1])).aestronglyMeasurable
    · filter_upwards [hnb] with a ha
      filter_upwards [hae] with r hr
      have h1 := hmono_r r hr (show a0 / 2 ∈ Ioi (0:ℝ) by simp only [mem_Ioi]; linarith)
        (show a ∈ Ioi (0:ℝ) by simp only [mem_Ioi]; linarith [ha.1]) ha.1.le
      have h2 := hmono_r r hr (show a ∈ Ioi (0:ℝ) by simp only [mem_Ioi]; linarith [ha.1])
        (show 2 * a0 ∈ Ioi (0:ℝ) by simp only [mem_Ioi]; linarith) ha.2.le
      simp only [Real.norm_eq_abs] at *
      rw [abs_le]
      constructor
      · have := neg_abs_le (gr r (a0 / 2))
        have := abs_nonneg (gr r (2 * a0))
        simp only [hgr] at *
        linarith
      · have := le_abs_self (gr r (2 * a0))
        have := abs_nonneg (gr r (a0 / 2))
        simp only [hgr] at *
        linarith
    · exact ((hG _ (by linarith)).norm).add (hG _ (by linarith)).norm
    · filter_upwards [hae] with r hr
      have hs := (hφ r hr).smooth
      have hnhds : Ioi (0:ℝ) ∈ 𝓝 a0 := isOpen_Ioi.mem_nhds ha0
      have hc1 : ContinuousAt (φ r) a0 :=
        ((hs.continuousOn) a0 ha0).continuousAt hnhds
      have hc2 : ContinuousAt (deriv (φ r)) a0 :=
        (((hs.deriv_of_isOpen isOpen_Ioi (m := 1) (by norm_num)).continuousOn) a0
          ha0).continuousAt hnhds
      exact hc2.div hc1 ((hφ r hr).pos a0 ha0).ne'
  set h : ℝ → ℝ := fun a => G M φ a + 1 / (M.K - a) with hh
  have hinvmono : StrictMonoOn (fun a : ℝ => 1 / (M.K - a)) (Ioo 0 M.K) := by
    intro a ha b hb hab
    simp only
    apply one_div_lt_one_div_of_lt (by linarith [hb.2]) (by linarith)
  have hstrict : StrictMonoOn h (Ioo 0 M.K) := by
    intro a ha b hb hab
    have h1 := hGmono (show a ∈ Ioi (0:ℝ) from ha.1) (show b ∈ Ioi (0:ℝ) from hb.1) hab.le
    have h2 := hinvmono ha hb hab
    simp only [hh] at *
    linarith
  have hcont : ContinuousOn h (Ioo 0 M.K) := by
    intro a ha
    apply ContinuousAt.continuousWithinAt
    apply (hGcont a ha.1).add
    apply ContinuousAt.div continuousAt_const (continuousAt_const.sub continuousAt_id)
    have := ha.2; intro h0; simp only [Pi.sub_apply, id] at h0; linarith
  -- eventual positivity to the left of K
  set g0 := G M φ (M.K / 2) with hg0
  set δ := 1 / (|g0| + 1) with hδ
  have hδpos : 0 < δ := by positivity
  have hev : ∀ᶠ a in 𝓝[<] M.K, 0 < h a := by
    have hmem : Ioo (max (M.K / 2) (M.K - δ)) M.K ∈ 𝓝[<] M.K :=
      Ioo_mem_nhdsLT (max_lt (by linarith) (by linarith))
    filter_upwards [hmem] with a ha
    have ha1 : M.K / 2 < a := lt_of_le_of_lt (le_max_left _ _) ha.1
    have ha2 : M.K - δ < a := lt_of_le_of_lt (le_max_right _ _) ha.1
    have hGa : g0 ≤ G M φ a :=
      hGmono (show M.K / 2 ∈ Ioi (0:ℝ) by simp only [mem_Ioi]; linarith)
        (show a ∈ Ioi (0:ℝ) by simp only [mem_Ioi]; linarith) ha1.le
    have hKa : 0 < M.K - a := by linarith [ha.2]
    have hinv : |g0| + 1 < 1 / (M.K - a) := by
      rw [lt_div_iff₀ hKa]
      have : M.K - a < δ := by linarith
      have h3 : (|g0| + 1) * (M.K - a) < (|g0| + 1) * δ :=
        mul_lt_mul_of_pos_left this (by positivity)
      have h4 : (|g0| + 1) * δ = 1 := by rw [hδ]; field_simp
      linarith
    have := neg_abs_le g0
    simp only [hh]
    linarith
  refine ⟨hstrict, hcont, hev, ?_⟩
  by_cases hT : ∃ t ∈ Ioo 0 M.K, h t ≤ 0
  · obtain ⟨t, ht, htle⟩ := hT
    -- a point b ∈ (t, K) with h b > 0
    obtain ⟨b, hb, hbpos⟩ : ∃ b ∈ Ioo t M.K, 0 < h b := by
      have hmem : Ioo t M.K ∈ 𝓝[<] M.K := Ioo_mem_nhdsLT ht.2
      obtain ⟨b, hb1, hb2⟩ := (hev.and hmem).exists
      exact ⟨b, hb2, hb1⟩
    have hsub : Icc t b ⊆ Ioo 0 M.K := fun y hy => ⟨lt_of_lt_of_le ht.1 hy.1,
      lt_of_le_of_lt hy.2 hb.2⟩
    have hivt := intermediate_value_Icc hb.1.le (hcont.mono hsub)
    obtain ⟨c, hc, hc0⟩ := hivt ⟨htle, hbpos.le⟩
    have hcI := hsub hc
    refine ⟨c, hcI.1.le, hcI.2, fun _ => hc0, ?_⟩
    intro a ha
    constructor
    · intro hpos
      by_contra hle
      push Not at hle
      rcases eq_or_lt_of_le hle with he | hlt
      · rw [he] at hpos; simp only [hh] at hpos hc0; linarith
      · have := hstrict ha hcI hlt
        simp only [hh] at this hc0 hpos
        linarith
    · intro hlt
      have := hstrict hcI ha hlt
      simp only [hh] at this hc0 ⊢
      linarith
  · push Not at hT
    refine ⟨0, le_rfl, hK, fun h0 => absurd h0 (lt_irrefl 0), ?_⟩
    intro a ha
    exact ⟨fun _ => ha.1, fun _ => hT a ha⟩
