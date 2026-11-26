-- Prove2me | solution 1 for Arxivcond_mat_0408414.specular_width_from_scaling
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T09:29:31.318561+00:00
-- url     : https://prove2.me/submissions/948d476c-bdc4-4824-bfff-5ec014ff719e

import Mathlib
import Definitions.Def_Arxivcond_mat_0408414_Basic

open MeasureTheory ProbabilityTheory Filter Topology Real Asymptotics

namespace SW
open Arxivcond_mat_0408414

lemma chi_eq (lam H s θ θ0 : ℝ) (hlam : 0 < lam) (hs : 0 < s) :
    chiRatio lam H s θ θ0 = (sin θ - sin θ0) / (cos θ + cos θ0) ^ (1 / H) * (s ^ (1 / H))⁻¹ := by
  unfold chiRatio deltaRough deltaAng
  rw [rpow_neg hs.le]
  by_cases h : sin θ - sin θ0 = 0
  · simp [h]
  · field_simp

end SW

open Arxivcond_mat_0408414 SW in
theorem solution (lam H θ0 : ℝ) (hlam : 0 < lam) (hH0 : 0 < H) (hH1 : H ≤ 1)
    (hθ0 : θ0 ∈ Set.Ioo (-(π / 2)) (π / 2)) :
    ∃ δ : ℝ → ℝ,
      (∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < δ s ∧ chiRatio lam H s (θ0 + δ s) θ0 = 1 ∧
        ∀ t ∈ Set.Ioo 0 (δ s), chiRatio lam H s (θ0 + t) θ0 < 1) ∧
      Tendsto (fun s : ℝ => δ s / ((2 * s) ^ (1 / H) * (cos θ0) ^ (1 / H - 1))) (𝓝[>] 0) (𝓝 1) := by
  have hp : 0 < 1 / H := by positivity
  have hc0 : 0 < cos θ0 := cos_pos_of_mem_Ioo hθ0
  set φ : ℝ → ℝ := fun t => (sin (θ0 + t) - sin θ0) / (cos (θ0 + t) + cos θ0) ^ (1 / H) with hφ
  set t1 := (π / 2 - θ0) / 2 with ht1
  have ht1p : 0 < t1 := by rw [ht1]; linarith [hθ0.2]
  have hcpos : ∀ t ∈ Set.Icc 0 t1, 0 < cos (θ0 + t) + cos θ0 := by
    intro t ht
    have : 0 < cos (θ0 + t) := cos_pos_of_mem_Ioo ⟨by linarith [hθ0.1, ht.1], by linarith [ht.2, hθ0.2]⟩
    linarith
  have hφc : ContinuousOn φ (Set.Icc 0 t1) := by
    refine ContinuousOn.div (by fun_prop) ?_ (fun t ht => (rpow_pos_of_pos (hcpos t ht) _).ne')
    exact ContinuousOn.rpow_const (by fun_prop) (fun t ht => Or.inl (hcpos t ht).ne')
  have hφpos : ∀ t ∈ Set.Ioc 0 t1, 0 < φ t := by
    intro t ht
    have hs : sin θ0 < sin (θ0 + t) :=
      sin_lt_sin_of_lt_of_le_pi_div_two (by linarith [hθ0.1]) (by linarith [ht.2, hθ0.2]) (by linarith [ht.1])
    exact div_pos (by linarith) (rpow_pos_of_pos (hcpos t ⟨ht.1.le, ht.2⟩) _)
  have hφ0 : φ 0 = 0 := by simp [hφ]
  set D := cos θ0 / (2 * cos θ0) ^ (1 / H) with hD
  have hDp : 0 < D := by positivity
  have hderiv : HasDerivAt φ D 0 := by
    have hN : HasDerivAt (fun t => sin (θ0 + t) - sin θ0) (cos (θ0 + 0) * 1) 0 :=
      (((hasDerivAt_id (0:ℝ)).const_add θ0).sin).sub_const _
    have hC : HasDerivAt (fun t => cos (θ0 + t) + cos θ0) (-sin (θ0 + 0) * 1) 0 :=
      (((hasDerivAt_id (0:ℝ)).const_add θ0).cos).add_const _
    have hC0 : cos (θ0 + 0) + cos θ0 = 2 * cos θ0 := by simp; ring
    have hCp := hC.rpow_const (p := 1 / H) (Or.inl (by rw [hC0]; positivity))
    have := hN.div hCp (by rw [hC0]; positivity)
    have hval : D = (cos (θ0 + 0) * 1 * (cos (θ0 + 0) + cos θ0) ^ (1 / H) -
        (sin (θ0 + 0) - sin θ0) * (-sin (θ0 + 0) * 1 * (1 / H) * (cos (θ0 + 0) + cos θ0) ^ (1 / H - 1))) /
      ((cos (θ0 + 0) + cos θ0) ^ (1 / H)) ^ 2 := by
      simp only [add_zero, sub_self, zero_mul, sub_zero, mul_one]
      rw [show cos θ0 + cos θ0 = 2 * cos θ0 by ring, hD]
      have : 0 < (2 * cos θ0) ^ (1 / H) := by positivity
      field_simp
    rw [hval]; exact this
  -- σ and δ
  let S : ℝ → Set ℝ := fun s => Set.Icc 0 t1 ∩ φ ⁻¹' Set.Ici (s ^ (1 / H))
  refine ⟨fun s => sInf (S s), ?_⟩
  have key : ∀ s : ℝ, 0 < s → s ^ (1 / H) < φ t1 →
      sInf (S s) ∈ S s ∧ 0 < sInf (S s) ∧ φ (sInf (S s)) = s ^ (1 / H) ∧
        ∀ t ∈ Set.Ioo 0 (sInf (S s)), φ t < s ^ (1 / H) := by
    intro s hs hσ
    have hσp : 0 < s ^ (1 / H) := by positivity
    have hne : (S s).Nonempty := ⟨t1, ⟨⟨ht1p.le, le_rfl⟩, hσ.le⟩⟩
    have hbdd : BddBelow (S s) := ⟨0, fun t ht => ht.1.1⟩
    have hcl : IsClosed (S s) := hφc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
    have hmem := hcl.csInf_mem hne hbdd
    have hpos : 0 < sInf (S s) := by
      rcases hmem.1.1.lt_or_eq with h | h
      · exact h
      · exfalso; have := hmem.2; rw [← h] at this; simp only [Set.mem_preimage, Set.mem_Ici, hφ0] at this; linarith
    have hbelow : ∀ t ∈ Set.Ioo 0 (sInf (S s)), φ t < s ^ (1 / H) := by
      intro t ht
      by_contra hcon
      have : t ∈ S s := ⟨⟨ht.1.le, by linarith [ht.2, hmem.1.2]⟩, le_of_not_gt hcon⟩
      linarith [csInf_le hbdd this, ht.2]
    refine ⟨hmem, hpos, ?_, hbelow⟩
    obtain ⟨c, hc, hcv⟩ := intermediate_value_Icc hpos.le (hφc.mono (Set.Icc_subset_Icc le_rfl hmem.1.2))
      (show s ^ (1 / H) ∈ Set.Icc (φ 0) (φ (sInf (S s))) from ⟨by rw [hφ0]; exact hσp.le, hmem.2⟩)
    have hcS : c ∈ S s := ⟨⟨hc.1, hc.2.trans hmem.1.2⟩, by simp only [Set.mem_preimage, Set.mem_Ici]; rw [hcv]⟩
    have := csInf_le hbdd hcS
    have hce : c = sInf (S s) := le_antisymm hc.2 this
    rw [← hce, hcv]
  have hσ0 : Tendsto (fun s : ℝ => s ^ (1 / H)) (𝓝[>] 0) (𝓝 0) := by
    have := (Real.continuous_rpow_const hp.le).tendsto 0
    rw [zero_rpow hp.ne'] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hev : ∀ ε > 0, ∀ᶠ s in 𝓝[>] (0:ℝ), 0 < s ∧ s ^ (1 / H) < ε :=
    fun ε hε => (eventually_mem_nhdsWithin).and (hσ0.eventually (gt_mem_nhds hε))
  have hgood := hev (φ t1) (hφpos t1 ⟨ht1p, le_rfl⟩)
  constructor
  · filter_upwards [hgood] with s ⟨hs, hσ⟩
    obtain ⟨-, hpos, heq, hbelow⟩ := key s hs hσ
    have hσp : 0 < s ^ (1 / H) := by positivity
    refine ⟨hpos, ?_, fun t ht => ?_⟩
    · rw [chi_eq lam H s _ _ hlam hs]
      change φ (sInf (S s)) * _ = 1
      rw [heq, mul_inv_cancel₀ hσp.ne']
    · rw [chi_eq lam H s _ _ hlam hs]
      change φ t * _ < 1
      rw [← div_eq_mul_inv, div_lt_one hσp]
      exact hbelow t ht
  · -- δ → 0+
    have hδ : Tendsto (fun s => sInf (S s)) (𝓝[>] 0) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · refine tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩
        · filter_upwards [hgood] with s ⟨hs, hσ⟩
          exact ha.trans (key s hs hσ).2.1
        · set ε := min (b / 2) t1
          have hε : 0 < ε := lt_min (by linarith) ht1p
          have hφε := hφpos ε ⟨hε, min_le_right _ _⟩
          filter_upwards [hgood, hev _ hφε] with s ⟨hs, hσ⟩ ⟨_, hσε⟩
          have hεS : ε ∈ S s := ⟨⟨hε.le, min_le_right _ _⟩, hσε.le⟩
          have := csInf_le ⟨0, fun t ht => ht.1.1⟩ hεS
          have : ε < b := lt_of_le_of_lt (min_le_left _ _) (by linarith)
          linarith
      · filter_upwards [hgood] with s ⟨hs, hσ⟩
        exact (key s hs hσ).2.1
    have hsl := hderiv.tendsto_slope_zero_right.comp hδ
    have hq : Tendsto (fun s => s ^ (1 / H) / sInf (S s)) (𝓝[>] 0) (𝓝 D) := by
      refine hsl.congr' ?_
      filter_upwards [hgood] with s ⟨hs, hσ⟩
      simp only [Function.comp, zero_add, hφ0, sub_zero, smul_eq_mul]
      rw [(key s hs hσ).2.2.1]; ring
    have hinv := (hq.inv₀ hDp.ne').mul_const ((2 : ℝ) ^ (1 / H) * cos θ0 ^ (1 / H - 1))⁻¹
    have hval : D⁻¹ * ((2 : ℝ) ^ (1 / H) * cos θ0 ^ (1 / H - 1))⁻¹ = 1 := by
      rw [hD, mul_rpow (by norm_num) hc0.le, rpow_sub_one hc0.ne']
      have : 0 < (2:ℝ) ^ (1 / H) := by positivity
      have : 0 < cos θ0 ^ (1 / H) := by positivity
      field_simp
    rw [hval] at hinv
    refine hinv.congr' ?_
    filter_upwards [hgood] with s ⟨hs, hσ⟩
    have hσp : 0 < s ^ (1 / H) := by positivity
    have hδp := (key s hs hσ).2.1
    rw [mul_rpow (by norm_num) hs.le]
    have : 0 < (2:ℝ) ^ (1 / H) := by positivity
    have : 0 < cos θ0 ^ (1 / H - 1) := by positivity
    field_simp
