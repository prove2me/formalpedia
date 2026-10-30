-- Prove2me | solution 1 for AggDiscountStopping.OneBarrier.lemma_2_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T19:01:31.436173+00:00
-- url     : https://prove2.me/submissions/d3a315ce-dcaf-4cd0-a3c8-87c0c42eb854

import Mathlib
import Definitions.Def_AggDiscountStopping_OneBarrier_Setting

open MeasureTheory Set Filter Topology
open scoped NNReal
open AggDiscountStopping.OneBarrier

/-- If arbitrarily small positive times lie in `S`, then `sInf S = 0`. -/
lemma ads_sInf_eq_zero (S : Set ℝ≥0) (h : ∀ ε : ℝ≥0, 0 < ε → ∃ t ∈ S, t < ε) :
    sInf S = 0 := by
  by_contra hne
  have hpos : 0 < sInf S := pos_iff_ne_zero.mpr hne
  obtain ⟨t, htS, htlt⟩ := h (sInf S) hpos
  exact absurd (csInf_le (OrderBot.bddBelow S) htS) (not_le.mpr htlt)

theorem solution {Ω : Type*} [MeasurableSpace Ω] (M : Model) (hM : M.Valid)
    (D : Diffusion Ω) (hD : D.Valid) (φ : ℝ → ℝ → ℝ) (hφ : IsLaplaceRep M D φ)
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    (∀ᵐ ω ∂D.P, D.enters x (Icc 0 a) ω ∧ D.entryTime x (Icc 0 a) ω = 0) ∧
      J M D x (Icc 0 a) = M.att (M.g x) := by
  have hprob := hD.prob
  have hae : ∀ᵐ ω ∂D.P, D.enters x (Icc 0 a) ω ∧ D.entryTime x (Icc 0 a) ω = 0 := by
    rcases eq_or_lt_of_le hxa with hxe | hxlt
    · -- x = a : use the Laplace representation at r = 1
      subst hxe
      have hL := hφ.laplace 1 zero_le_one x x ha le_rfl
      have hpos := (hφ.sol 1 zero_le_one).pos x ha
      rw [div_self hpos.ne'] at hL
      have hle1 : ∀ ω, D.hitDisc 1 x x ω ≤ 1 := by
        intro ω
        unfold Diffusion.hitDisc
        split_ifs
        · rw [Real.exp_le_one_iff]
          have := (D.entryTime x {x} ω).2
          linarith
        · exact zero_le_one
      have hint : Integrable (D.hitDisc 1 x x) D.P := by
        apply Integrable.of_integral_ne_zero
        unfold Diffusion.hitLaplace at hL
        rw [hL]; exact one_ne_zero
      have hint2 : Integrable (fun ω => 1 - D.hitDisc 1 x x ω) D.P :=
        (integrable_const 1).sub hint
      have hzero : ∫ ω, (1 - D.hitDisc 1 x x ω) ∂D.P = 0 := by
        rw [integral_sub (integrable_const 1) hint]
        unfold Diffusion.hitLaplace at hL
        rw [hL]; simp
      have hae0 := (integral_eq_zero_iff_of_nonneg
        (fun ω => sub_nonneg.mpr (hle1 ω)) hint2).mp hzero
      filter_upwards [hae0] with ω hω
      simp only [Pi.zero_apply] at hω
      have h1 : D.hitDisc 1 x x ω = 1 := by linarith
      unfold Diffusion.hitDisc at h1
      split_ifs at h1 with hen
      · have hτ : (D.entryTime x {x} ω : ℝ) = 0 := by
          have := Real.exp_eq_one_iff _ |>.mp h1
          linarith
        have hτ0 : D.entryTime x {x} ω = 0 := by exact_mod_cast hτ
        have hsub : {t : ℝ≥0 | 0 < t ∧ D.X x t ω ∈ ({x} : Set ℝ)} ⊆
            {t : ℝ≥0 | 0 < t ∧ D.X x t ω ∈ Icc 0 x} := by
          rintro t ⟨ht0, ht⟩
          refine ⟨ht0, ?_⟩
          rw [mem_singleton_iff] at ht
          rw [ht]; exact ⟨hx0, le_rfl⟩
        refine ⟨?_, ?_⟩
        · obtain ⟨t, ht⟩ := hen
          exact ⟨t, hsub ht⟩
        · have hle : D.entryTime x (Icc 0 x) ω ≤ D.entryTime x {x} ω :=
            csInf_le_csInf (OrderBot.bddBelow _) hen hsub
          rw [hτ0] at hle
          exact le_antisymm hle zero_le
      · exact absurd h1 zero_ne_one
    · -- x < a : the path stays in [0, a] for small positive times
      refine Filter.Eventually.of_forall (fun ω => ?_)
      have hc : Continuous fun t => D.X x t ω := hD.cont x ω
      have hev : ∀ᶠ t in 𝓝 (0 : ℝ≥0), D.X x t ω < a := by
        have := hc.tendsto 0
        rw [hD.start x ω] at this
        exact this (Iio_mem_nhds hxlt)
      obtain ⟨δ, hδpos, hδ⟩ : ∃ δ : ℝ≥0, 0 < δ ∧ ∀ t : ℝ≥0, t < δ → D.X x t ω < a := by
        rcases (Metric.eventually_nhds_iff.mp hev) with ⟨e, he, hball⟩
        refine ⟨⟨e, he.le⟩, he, fun t ht => hball ?_⟩
        rw [NNReal.dist_eq]
        simp only [NNReal.coe_zero, sub_zero]
        rw [abs_of_nonneg (NNReal.coe_nonneg t)]
        exact_mod_cast ht
      have hmem : ∀ t : ℝ≥0, 0 < t → t < δ →
          t ∈ {t : ℝ≥0 | 0 < t ∧ D.X x t ω ∈ Icc 0 a} :=
        fun t ht0 htδ => ⟨ht0, hD.nonneg x hx0 t ω, (hδ t htδ).le⟩
      refine ⟨⟨δ / 2, hmem (δ / 2) (half_pos hδpos) (NNReal.half_lt_self hδpos.ne')⟩, ?_⟩
      apply ads_sInf_eq_zero
      intro e he
      refine ⟨min e δ / 2, hmem _ (half_pos (lt_min he hδpos)) ?_, ?_⟩
      · exact lt_of_lt_of_le (NNReal.half_lt_self (lt_min he hδpos).ne') (min_le_right _ _)
      · exact lt_of_lt_of_le (NNReal.half_lt_self (lt_min he hδpos).ne') (min_le_left _ _)
  refine ⟨hae, ?_⟩
  have hpay : ∀ r, ∫ ω, discPayoff M D r x (Icc 0 a) ω ∂D.P = M.g x := by
    intro r
    have : (fun ω => discPayoff M D r x (Icc 0 a) ω) =ᵐ[D.P] fun _ => M.g x := by
      filter_upwards [hae] with ω hω
      unfold discPayoff
      rw [if_pos hω.1, hω.2]
      simp [hD.start x ω]
    rw [integral_congr_ae this]
    simp
  have hF := hM.F_prob
  unfold J
  simp only [hpay]
  simp
