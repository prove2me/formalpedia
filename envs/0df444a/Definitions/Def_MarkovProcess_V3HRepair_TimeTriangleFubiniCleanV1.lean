-- Prove2me | Definitions.Def_MarkovProcess_V3HRepair_TimeTriangleFubiniCleanV1
-- name    : MarkovProcess_V3HRepair_TimeTriangleFubiniCleanV1
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-01T09:48:43.202305+00:00
-- url     : https://prove2.me/theorems/ef548a6e-f764-46b8-95e7-dcd9478ca545
-- title:
--   Verified MarkovProcess source repair: TimeTriangleFubiniCleanV1
-- statement:
--   Tonelli and Fubini identities under the triangular time domain shear, with accompanying exponential integration estimates.
-- source:
--   Scott Armstrong, MarkovProcess (Apache-2.0), pinned upstream commit 1f8060caa137731fa08029592019eeaf9d997fe5; source-faithful adapted proof module V3HRepaired.TimeTriangleFubiniCleanV1, archived SHA-256 f4af2427051acbef30e6bd7e28cbc67b30a1535ab389c963bcede3cfda4fd5c0.

import Mathlib

open MeasureTheory Set
open scoped ENNReal

namespace intervalIntegral

noncomputable section

-- The namespace placement is upstream-facing: this is a pure companion to interval integrals.
/-- Tonelli's theorem on the time triangle, followed by the volume-preserving shear
`(s, u) ↦ (s, s + u)`. -/
theorem lintegral_timeTriangle_sub {h : ℝ × ℝ → ℝ≥0∞} (hh : Measurable h) :
    (∫⁻ t in Ioi (0 : ℝ), ∫⁻ s in Ioo (0 : ℝ) t, h (s, t - s)) =
      ∫⁻ s in Ioi (0 : ℝ), ∫⁻ u in Ioi (0 : ℝ), h (s, u) := by
  let S : Set (ℝ × ℝ) := {p | 0 < p.1 ∧ p.1 < p.2}
  let F : ℝ × ℝ → ℝ≥0∞ := fun p ↦ S.indicator (fun z ↦ h (z.1, z.2 - z.1)) p
  have hS : MeasurableSet S :=
    (measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_lt measurable_fst measurable_snd)
  have hF : Measurable F := by
    exact (hh.comp (measurable_fst.prodMk (measurable_snd.sub measurable_fst))).indicator hS
  have hleft : (∫⁻ t in Ioi (0 : ℝ), ∫⁻ s in Ioo (0 : ℝ) t, h (s, t - s)) =
      ∫⁻ t, ∫⁻ s, F (s, t) := by
    rw [← lintegral_indicator measurableSet_Ioi]
    apply lintegral_congr
    intro t
    by_cases ht : t ∈ Ioi (0 : ℝ)
    · rw [indicator_of_mem ht, ← lintegral_indicator measurableSet_Ioo]
      apply lintegral_congr
      intro s
      by_cases hs : s ∈ Ioo (0 : ℝ) t
      · rw [indicator_of_mem hs]
        dsimp only [F]
        rw [indicator_of_mem]
        exact hs
      · rw [indicator_of_notMem hs]
        dsimp only [F]
        rw [indicator_of_notMem]
        exact fun hst ↦ hs hst
    · rw [indicator_of_notMem ht]
      have hzero : ∀ s : ℝ, F (s, t) = 0 := fun s ↦ by
        dsimp only [F]
        rw [indicator_of_notMem]
        exact fun hs ↦ ht (hs.1.trans hs.2)
      simp_rw [hzero]
      exact lintegral_zero.symm
  have hright : (∫⁻ s in Ioi (0 : ℝ), ∫⁻ u in Ioi (0 : ℝ), h (s, u)) =
      ∫⁻ s, ∫⁻ u, F (s, s + u) := by
    rw [← lintegral_indicator measurableSet_Ioi]
    apply lintegral_congr
    intro s
    by_cases hs : s ∈ Ioi (0 : ℝ)
    · rw [indicator_of_mem hs, ← lintegral_indicator measurableSet_Ioi]
      apply lintegral_congr
      intro u
      by_cases hu : u ∈ Ioi (0 : ℝ)
      · rw [indicator_of_mem hu]
        dsimp only [F]
        rw [indicator_of_mem]
        · ring_nf
        · exact ⟨hs, lt_add_of_pos_right s hu⟩
      · rw [indicator_of_notMem hu]
        dsimp only [F]
        rw [indicator_of_notMem]
        intro hsu
        change 0 < s ∧ s < s + u at hsu
        have hu0 : u ≤ 0 := le_of_not_gt hu
        linarith only [hsu.2, hu0]
    · rw [indicator_of_notMem hs]
      have hzero : ∀ u : ℝ, F (s, s + u) = 0 := fun u ↦ by
        dsimp only [F]
        rw [indicator_of_notMem]
        exact fun hsu ↦ hs hsu.1
      simp_rw [hzero]
      exact lintegral_zero.symm
  rw [hleft, hright]
  have hFswap : Measurable fun p : ℝ × ℝ ↦ F (p.2, p.1) :=
    hF.comp measurable_swap
  calc
    (∫⁻ t, ∫⁻ s, F (s, t)) = ∫⁻ s, ∫⁻ t, F (s, t) :=
      lintegral_lintegral_swap hFswap.aemeasurable
    _ = ∫⁻ p, F p ∂volume.prod volume :=
      (lintegral_prod F hF.aemeasurable).symm
    _ = ∫⁻ p, F (p.1, p.1 + p.2) ∂volume.prod volume := by
      exact ((measurePreserving_prod_add volume volume).lintegral_comp_emb
        (MeasurableEquiv.shearAddRight ℝ).measurableEmbedding F).symm
    _ = ∫⁻ s, ∫⁻ u, F (s, s + u) := lintegral_prod _ (hF.comp
      (measurable_fst.prodMk measurable_add)).aemeasurable

/-- Fubini's theorem on the time triangle, followed by the volume-preserving shear
`(s, u) ↦ (s, s + u)`, for an integrable real-valued function on the positive quadrant. -/
theorem integral_timeTriangle_sub {h : ℝ × ℝ → ℝ} (hh : Measurable h)
    (hint : Integrable ((Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)).indicator h)
      (volume.prod volume)) :
    (∫ t in Ioi (0 : ℝ), ∫ s in Ioo (0 : ℝ) t, h (s, t - s)) =
      ∫ s in Ioi (0 : ℝ), ∫ u in Ioi (0 : ℝ), h (s, u) := by
  let Q : Set (ℝ × ℝ) := Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)
  let S : Set (ℝ × ℝ) := {p | 0 < p.1 ∧ p.1 < p.2}
  let G : ℝ × ℝ → ℝ := fun p ↦ Q.indicator h p
  let F : ℝ × ℝ → ℝ := fun p ↦ S.indicator (fun z ↦ h (z.1, z.2 - z.1)) p
  have hQ : MeasurableSet Q := measurableSet_Ioi.prod measurableSet_Ioi
  have hS : MeasurableSet S :=
    (measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_lt measurable_fst measurable_snd)
  have hG : Measurable G := hh.indicator hQ
  have hF : Measurable F :=
    (hh.comp (measurable_fst.prodMk (measurable_snd.sub measurable_fst))).indicator hS
  have hFG : (fun p : ℝ × ℝ ↦ F (p.1, p.1 + p.2)) = G := by
    funext p
    by_cases hp : p ∈ Q
    · dsimp only [F, G]
      rw [indicator_of_mem, indicator_of_mem hp]
      · ring_nf
      · exact ⟨hp.1, lt_add_of_pos_right p.1 hp.2⟩
    · dsimp only [F, G]
      rw [indicator_of_notMem, indicator_of_notMem hp]
      intro hmem
      have hp2 : 0 < p.2 := by linarith only [hmem.2]
      exact hp ⟨hmem.1, hp2⟩
  have hGint : Integrable G (volume.prod volume) := by simpa only [G, Q] using hint
  have hFint : Integrable F (volume.prod volume) := by
    have hcomp := (measurePreserving_prod_add volume volume).integrable_comp
      hF.aestronglyMeasurable
    apply hcomp.mp
    rw [Function.comp_def, hFG]
    exact hGint
  have hleft : (∫ t in Ioi (0 : ℝ), ∫ s in Ioo (0 : ℝ) t, h (s, t - s)) =
      ∫ t, ∫ s, F (s, t) := by
    rw [← MeasureTheory.integral_indicator measurableSet_Ioi]
    apply MeasureTheory.integral_congr_ae
    exact Filter.Eventually.of_forall fun t ↦ by
      by_cases ht : t ∈ Ioi (0 : ℝ)
      · rw [indicator_of_mem ht, ← MeasureTheory.integral_indicator measurableSet_Ioo]
        apply MeasureTheory.integral_congr_ae
        exact Filter.Eventually.of_forall fun s ↦ by
          by_cases hs : s ∈ Ioo (0 : ℝ) t
          · rw [indicator_of_mem hs]
            dsimp only [F]
            rw [indicator_of_mem]
            exact hs
          · rw [indicator_of_notMem hs]
            dsimp only [F]
            rw [indicator_of_notMem]
            exact fun hst ↦ hs hst
      · rw [indicator_of_notMem ht]
        have hzero : ∀ s : ℝ, F (s, t) = 0 := fun s ↦ by
          dsimp only [F]
          rw [indicator_of_notMem]
          exact fun hs ↦ ht (hs.1.trans hs.2)
        simp_rw [hzero]
        simp only [MeasureTheory.integral_zero]
  have hright : (∫ s in Ioi (0 : ℝ), ∫ u in Ioi (0 : ℝ), h (s, u)) =
      ∫ s, ∫ u, G (s, u) := by
    rw [← MeasureTheory.integral_indicator measurableSet_Ioi]
    apply MeasureTheory.integral_congr_ae
    exact Filter.Eventually.of_forall fun s ↦ by
      by_cases hs : s ∈ Ioi (0 : ℝ)
      · rw [indicator_of_mem hs, ← MeasureTheory.integral_indicator measurableSet_Ioi]
        apply MeasureTheory.integral_congr_ae
        exact Filter.Eventually.of_forall fun u ↦ by
          by_cases hu : u ∈ Ioi (0 : ℝ)
          · rw [indicator_of_mem hu]
            dsimp only [G, Q]
            rw [indicator_of_mem]
            exact ⟨hs, hu⟩
          · rw [indicator_of_notMem hu]
            dsimp only [G, Q]
            rw [indicator_of_notMem]
            exact fun hsu ↦ hu hsu.2
      · rw [indicator_of_notMem hs]
        have hzero : ∀ u : ℝ, G (s, u) = 0 := fun u ↦ by
          dsimp only [G, Q]
          rw [indicator_of_notMem]
          exact fun hsu ↦ hs hsu.1
        simp_rw [hzero]
        simp only [MeasureTheory.integral_zero]
  rw [hleft, hright]
  calc
    (∫ t, ∫ s, F (s, t)) = ∫ s, ∫ t, F (s, t) :=
      (integral_integral_swap hFint).symm
    _ = ∫ p, F p ∂volume.prod volume :=
      (MeasureTheory.integral_prod F hFint).symm
    _ = ∫ p, F (p.1, p.1 + p.2) ∂volume.prod volume := by
      exact ((measurePreserving_prod_add volume volume).integral_comp'
        (f := MeasurableEquiv.shearAddRight ℝ) F).symm
    _ = ∫ p, G p ∂volume.prod volume := by rw [hFG]
    _ = ∫ s, ∫ u, G (s, u) := MeasureTheory.integral_prod G hGint

private theorem exp_mul_sub_le_sub_exp {x y : ℝ} :
    Real.exp x * (y - x) ≤ Real.exp y - Real.exp x := by
  rw [le_sub_iff_add_le]
  calc
    Real.exp x * (y - x) + Real.exp x = Real.exp x * ((y - x) + 1) := by ring
    _ ≤ Real.exp x * Real.exp (y - x) :=
      mul_le_mul_of_nonneg_left (Real.add_one_le_exp (y - x)) (Real.exp_pos x).le
    _ = Real.exp y := by
      rw [← Real.exp_add]
      congr 1
      ring

private theorem sub_exp_le_exp_mul_sub {x y : ℝ} :
    Real.exp y - Real.exp x ≤ Real.exp y * (y - x) := by
  have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (x - y)) (Real.exp_pos y).le
  have h' : Real.exp y * ((x - y) + 1) ≤ Real.exp x := by
    calc
      Real.exp y * ((x - y) + 1) ≤ Real.exp y * Real.exp (x - y) := h
      _ = Real.exp x := by
        rw [← Real.exp_add]
        congr 1
        ring
  rw [sub_le_iff_le_add]
  calc
    Real.exp y = Real.exp y * ((x - y) + 1) + Real.exp y * (y - x) := by ring
    _ ≤ Real.exp x + Real.exp y * (y - x) := by
      simpa only [add_comm] using add_le_add_right h' (Real.exp y * (y - x))
    _ = Real.exp y * (y - x) + Real.exp x := add_comm _ _


end
end intervalIntegral
#print axioms intervalIntegral.lintegral_timeTriangle_sub
#print axioms intervalIntegral.integral_timeTriangle_sub


