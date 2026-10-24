-- Prove2me | solution 1 for AtaBarjesteh23.Workload.lemma_19
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T19:57:24.563064+00:00
-- url     : https://prove2.me/submissions/0e7359e1-e42d-466e-88c5-8673de0b1d66

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
    (hv0 : v 0 = -M.kappa)
    (hode : ∀ w ∈ Icc 0 wbar, HasDerivWithinAt v
      (M.a / (2 * M.σ ^ 2) * (v w ^ 2 - M.kappa ^ 2) - 2 * M.μ / M.σ ^ 2 * (v w + M.kappa)
        + 2 * M.bStar / M.σ ^ 2 * w) (Icc 0 wbar) w) :
    ∀ w ∈ Ioc 0 wbar, 0 < derivWithin v (Icc 0 wbar) w := by
  obtain ⟨hK, hm, -, hb, -, -, -, hσ⟩ := hM
  have hbs : 0 < M.bStar := by
    have : Nonempty (Fin M.K) := ⟨⟨0, hK⟩⟩
    obtain ⟨k, hk⟩ := exists_eq_ciInf_of_finite (f := fun k : Fin M.K => M.b k / M.m k)
    rw [Model.bStar, ← hk]
    exact div_pos (hb k) (hm k)
  set c1 := M.a / (2 * M.σ ^ 2)
  set c2 := 2 * M.μ / M.σ ^ 2
  set c3 := 2 * M.bStar / M.σ ^ 2
  have hc3 : 0 < c3 := by positivity
  set F : ℝ → ℝ := fun w => c1 * (v w ^ 2 - M.kappa ^ 2) - c2 * (v w + M.kappa) + c3 * w
    with hF
  have hFd : ∀ w ∈ Icc 0 wbar, HasDerivWithinAt F
      (c1 * (2 * v w * F w) - c2 * F w + c3) (Icc 0 wbar) w := by
    intro w hw
    have hv := hode w hw
    have h1 := ((hv.pow 2).sub_const (M.kappa ^ 2)).const_mul c1
    have h2 := (hv.add_const M.kappa).const_mul c2
    have h3 := (hasDerivWithinAt_id w (Icc 0 wbar)).const_mul c3
    have := (h1.sub h2).add h3
    refine (this.congr_deriv ?_).congr (fun y _ => by simp [F]) (by simp [F])
    simp only [F]
    push_cast
    ring
  have hpos := AtaB_pos_of_deriv_pos_at_zeros hwbar F _ hFd
    (by simp [F, hv0]) (by intro w _ hw0; rw [hw0]; simpa using hc3)
  intro w hw
  rw [(hode w (Ioc_subset_Icc_self hw)).derivWithin
    (uniqueDiffOn_Icc hwbar w (Ioc_subset_Icc_self hw))]
  exact hpos w hw
