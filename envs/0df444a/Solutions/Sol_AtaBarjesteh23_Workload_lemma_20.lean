-- Prove2me | solution 1 for AtaBarjesteh23.Workload.lemma_20
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T19:59:51.218283+00:00
-- url     : https://prove2.me/submissions/b52987e3-af14-43c4-8b36-e3feeadc23a0

import Mathlib
import Definitions.Def_AtaBarjesteh23_Workload_Setting
import Definitions.Def_AtaBarjesteh23_Workload_DriftBM
import Definitions.Def_AtaBarjesteh23_Workload_Control

open MeasureTheory Set Filter Topology

/-- If `z(p) = 0` and `z' > 0` at every zero of `z` on `[p, q]`, then `z > 0` on `(p, q]`. -/
theorem AtaB_pos_of_deriv_pos_at_zeros {p q : ℝ} (hpq : p < q) (z z' : ℝ → ℝ)
    (hz : ∀ w ∈ Icc p q, HasDerivWithinAt z (z' w) (Icc p q) w) (hzp : z p = 0)
    (hcross : ∀ w ∈ Icc p q, z w = 0 → 0 < z' w) : ∀ w ∈ Ioc p q, 0 < z w := by
  have hcont : ContinuousOn z (Icc p q) := fun w hw => (hz w hw).continuousWithinAt
  -- first `z ≥ 0` on `[p, q]` by the fencing theorem
  have hnonneg : ∀ w ∈ Icc p q, (fun _ => (0 : ℝ)) w ≤ z w := by
    refine image_le_of_deriv_right_lt_deriv_boundary' (f' := fun _ => 0) (B' := z') continuousOn_const
      (fun x _ => hasDerivWithinAt_const _ _ _) (by simp [hzp]) hcont ?_ ?_
    · intro x hx
      exact (hz x (Ico_subset_Icc_self hx)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem hx)
    · intro x hx hx0
      exact hcross x (Ico_subset_Icc_self hx) hx0.symm
  intro w hw
  rcases (hnonneg w (Ioc_subset_Icc_self hw)).lt_or_eq with h | h
  · exact h
  exfalso
  have hw0 : z w = 0 := h.symm
  have hd := (hz w (Ioc_subset_Icc_self hw)).mono (Ioo_subset_Icc_self.trans
    (Icc_subset_Icc_right hw.2) : Ioo p w ⊆ Icc p q)
  rw [hasDerivWithinAt_iff_tendsto_slope' (by simp), nhdsWithin_Ioo_eq_nhdsLT hw.1] at hd
  have hle : z' w ≤ 0 := by
    refine le_of_tendsto hd ?_
    filter_upwards [Ioo_mem_nhdsLT hw.1] with y hy
    rw [slope_def_field, hw0, sub_zero]
    exact div_nonpos_of_nonneg_of_nonpos
      (hnonneg y ⟨hy.1.le, hy.2.le.trans hw.2⟩) (by linarith [hy.2])
  linarith [hcross w (Ioc_subset_Icc_self hw) hw0]

open AtaBarjesteh23.Workload in
theorem solution (M : Model) (hM : M.Standing) (wbar : ℝ) (hwbar : 0 < wbar) (v : ℝ → ℝ)
    (hv0 : v 0 = 0)
    (hode : ∀ w ∈ Icc 0 wbar, HasDerivWithinAt v
      (-(M.a / (2 * M.σ ^ 2)) * v w ^ 2 + 2 * M.μ / M.σ ^ 2 * v w - 2 * M.hStar / M.σ ^ 2 * w)
      (Icc 0 wbar) w) :
    ∀ w ∈ Ioc 0 wbar, v w < 0 ∧ derivWithin v (Icc 0 wbar) w < 0 := by
  obtain ⟨hK, hm, hh, -, -, -, -, hσ⟩ := hM
  have hhs : 0 < M.hStar := by
    have : Nonempty (Fin M.K) := ⟨⟨0, hK⟩⟩
    obtain ⟨k, hk⟩ := exists_eq_ciInf_of_finite (f := fun k : Fin M.K => M.h k / M.m k)
    rw [Model.hStar, ← hk]
    exact div_pos (hh k) (hm k)
  set c1 := M.a / (2 * M.σ ^ 2)
  set c2 := 2 * M.μ / M.σ ^ 2
  set c4 := 2 * M.hStar / M.σ ^ 2
  have hc4 : 0 < c4 := by positivity
  set F : ℝ → ℝ := fun w => -c1 * v w ^ 2 + c2 * v w - c4 * w with hF
  have hGd : ∀ w ∈ Icc 0 wbar, HasDerivWithinAt (fun w => -F w)
      (-(-c1 * (2 * v w * F w) + c2 * F w - c4)) (Icc 0 wbar) w := by
    intro w hw
    have hv := hode w hw
    have h1 := (hv.pow 2).const_mul (-c1)
    have h2 := hv.const_mul c2
    have h3 := (hasDerivWithinAt_id w (Icc 0 wbar)).const_mul c4
    have := ((h1.add h2).sub h3).neg
    refine (this.congr_deriv ?_).congr (fun y _ => by simp [F]) (by simp [F])
    simp only [F]
    push_cast
    ring
  have hpos := AtaB_pos_of_deriv_pos_at_zeros hwbar (fun w => -F w) _ hGd
    (by simp [F, hv0]) (by
      intro w _ hw0
      have : F w = 0 := by simpa using hw0
      rw [this]; simpa using hc4)
  have hFneg : ∀ w ∈ Ioc 0 wbar, F w < 0 := fun w hw => by simpa using hpos w hw
  have hcont : ContinuousOn v (Icc 0 wbar) := fun w hw => (hode w hw).continuousWithinAt
  have hanti : StrictAntiOn v (Icc 0 wbar) := by
    refine strictAntiOn_of_hasDerivWithinAt_neg (convex_Icc 0 wbar) hcont (f' := F) ?_ ?_
    · intro x hx
      rw [interior_Icc] at hx ⊢
      exact (hode x (Ioo_subset_Icc_self hx)).mono Ioo_subset_Icc_self
    · intro x hx
      rw [interior_Icc] at hx
      exact hFneg x ⟨hx.1, hx.2.le⟩
  intro w hw
  refine ⟨?_, ?_⟩
  · rw [← hv0]
    exact hanti ⟨le_rfl, hwbar.le⟩ (Ioc_subset_Icc_self hw) hw.1
  · rw [(hode w (Ioc_subset_Icc_self hw)).derivWithin
      (uniqueDiffOn_Icc hwbar w (Ioc_subset_Icc_self hw))]
    exact hFneg w hw
