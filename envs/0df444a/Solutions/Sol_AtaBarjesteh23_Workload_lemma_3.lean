-- Prove2me | solution 1 for AtaBarjesteh23.Workload.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T20:01:42.861156+00:00
-- url     : https://prove2.me/submissions/ed51f549-6d08-4cb3-a894-7405c95aa20a

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
theorem solution (M : Model) (hM : M.Standing) (l u γ : ℝ) (v : ℝ → ℝ)
    (hv : M.BellmanV l u γ v) :
    0 < γ ∧ l = M.lgam γ ∧ l < 0 ∧ u = M.ugam γ ∧ 0 < u := by
  obtain ⟨hK, hm, hh, hb, hr, hH, hμ, hσ⟩ := hM
  obtain ⟨hlu, hC1, hode, hvl, hvu, hdl, hdu⟩ := hv
  have : Nonempty (Fin M.K) := ⟨⟨0, hK⟩⟩
  have hbs : 0 < M.bStar := by
    obtain ⟨k, hk⟩ := exists_eq_ciInf_of_finite (f := fun k : Fin M.K => M.b k / M.m k)
    rw [Model.bStar, ← hk]
    exact div_pos (hb k) (hm k)
  have hhs : 0 < M.hStar := by
    obtain ⟨k, hk⟩ := exists_eq_ciInf_of_finite (f := fun k : Fin M.K => M.h k / M.m k)
    rw [Model.hStar, ← hk]
    exact div_pos (hh k) (hm k)
  have hks : 0 < M.kappa := by
    obtain ⟨k, hk⟩ := exists_eq_ciInf_of_finite (f := fun k : Fin M.K => M.r k / M.m k)
    rw [Model.kappa, ← hk]
    exact div_pos (hr k) (hm k)
  have hmne : M.m ≠ 0 := by
    intro h
    have := hm ⟨0, hK⟩
    rw [h] at this
    simp at this
  have ha : 0 < M.a := by
    have := hH.inv.dotProduct_mulVec_pos hmne
    simpa [Model.a] using this
  have hhmax : ∀ w, M.hcost w = max (M.hStar * w) (-(M.bStar * w)) := by
    intro w
    unfold Model.hcost
    split_ifs with h
    · rw [max_eq_left]; nlinarith
    · rw [max_eq_right]; push_neg at h; nlinarith
  have hhcont : Continuous M.hcost := by
    have : M.hcost = fun w => max (M.hStar * w) (-(M.bStar * w)) := funext hhmax
    rw [this]; fun_prop
  have hhneg : ∀ w ≤ 0, M.hcost w = -(M.bStar * w) := by
    intro w hw
    rw [hhmax, max_eq_right]; nlinarith
  have hhpos : ∀ w, 0 ≤ w → M.hcost w = M.hStar * w := by
    intro w hw
    rw [hhmax, max_eq_left]; nlinarith
  have hh0 : ∀ w, 0 ≤ M.hcost w := by
    intro w; rw [hhmax]
    rcases le_total 0 w with h | h
    · exact le_max_of_le_left (by positivity)
    · exact le_max_of_le_right (by nlinarith)
  set c1 := M.a / (2 * M.σ ^ 2)
  set c2 := 2 * M.μ / M.σ ^ 2
  set R : ℝ → ℝ := fun w => c1 * v w ^ 2 - c2 * v w + 2 * (γ - M.hcost w) / M.σ ^ 2 with hR
  have hUD : UniqueDiffOn ℝ (Icc l u) := uniqueDiffOn_Icc hlu
  have hvcont : ContinuousOn v (Icc l u) := hC1.continuousOn
  have hRcont : ContinuousOn R (Icc l u) := by
    have := hhcont.continuousOn (s := Icc l u)
    simp only [R]
    fun_prop
  have hdcont : ContinuousOn (derivWithin v (Icc l u)) (Icc l u) :=
    hC1.continuousOn_derivWithin hUD le_rfl
  have hEq : EqOn (derivWithin v (Icc l u)) R (Icc l u) := by
    refine EqOn.of_subset_closure (s := Ioo l u) ?_ hdcont hRcont Ioo_subset_Icc_self
      (by rw [closure_Ioo hlu.ne])
    intro w hw
    rw [derivWithin_of_mem_nhds (Icc_mem_nhds hw.1 hw.2)]
    exact hode w hw
  have hlmem : l ∈ Icc l u := ⟨le_rfl, hlu.le⟩
  have humem : u ∈ Icc l u := ⟨hlu.le, le_rfl⟩
  have hRu : R u = 0 := by rw [← hEq humem]; exact hdu
  have hRl : R l = 0 := by rw [← hEq hlmem]; exact hdl
  have hσ2 : 0 < M.σ ^ 2 := by positivity
  have hγ : M.hcost u = γ := by
    simp only [R, hvu] at hRu
    have : 2 * (γ - M.hcost u) / M.σ ^ 2 = 0 := by linarith
    rw [div_eq_zero_iff] at this
    rcases this with h | h
    · linarith
    · linarith
  have hlval : M.hcost l = γ + M.μ * M.kappa + M.a / 4 * M.kappa ^ 2 := by
    simp only [R, hvl] at hRl
    have h2 : (c1 * (-M.kappa) ^ 2 - c2 * -M.kappa + 2 * (γ - M.hcost l) / M.σ ^ 2) * M.σ ^ 2
        = 0 := by rw [hRl]; ring
    simp only [c1, c2] at h2
    field_simp at h2
    linarith
  have hγ0 : 0 ≤ γ := hγ ▸ hh0 u
  have hl0 : l < 0 := by
    by_contra hl
    push_neg at hl
    have h1 := hhpos l hl
    have h2 := hhpos u (hl.trans hlu.le)
    have : M.hStar * l < M.hStar * u := mul_lt_mul_of_pos_left hlu hhs
    have : 0 < M.μ * M.kappa + M.a / 4 * M.kappa ^ 2 := by positivity
    linarith
  have hu0 : 0 < u := by
    by_contra hu
    push_neg at hu
    -- on `[l, u] ⊆ (-∞, 0]` the holding cost is linear and `R` solves a linear equation
    -- with positive forcing, so it cannot vanish at both ends
    set F : ℝ → ℝ := fun w => c1 * v w ^ 2 - c2 * v w + 2 * (γ + M.bStar * w) / M.σ ^ 2
      with hF
    have hRF : ∀ w ∈ Icc l u, R w = F w := by
      intro w hw
      simp only [R, F, hhneg w (hw.2.trans hu)]
      ring
    have hvd : ∀ w ∈ Icc l u, HasDerivWithinAt v (F w) (Icc l u) w := by
      intro w hw
      have := ((hC1.differentiableOn (by norm_num)) w hw).hasDerivWithinAt
      rwa [hEq hw, hRF w hw] at this
    have hFd : ∀ w ∈ Icc l u, HasDerivWithinAt F
        (c1 * (2 * v w * F w) - c2 * F w + 2 * M.bStar / M.σ ^ 2) (Icc l u) w := by
      intro w hw
      have hv := hvd w hw
      have h1 := (hv.pow 2).const_mul c1
      have h2 := hv.const_mul c2
      have h3 := (((hasDerivWithinAt_id w (Icc l u)).const_mul M.bStar).const_add
        γ).const_mul 2 |>.div_const (M.σ ^ 2)
      have := (h1.sub h2).add h3
      refine (this.congr_deriv ?_).congr (fun y _ => by simp [F]) (by simp [F])
      simp only [F]
      push_cast
      ring
    have hc : 0 < 2 * M.bStar / M.σ ^ 2 := by positivity
    have hpos := AtaB_pos_of_deriv_pos_at_zeros hlu F _ hFd
      (by rw [← hRF l hlmem]; exact hRl) (by intro w _ hw0; rw [hw0]; simpa using hc)
    have := hpos u ⟨hlu, le_rfl⟩
    rw [← hRF u humem, hRu] at this
    exact lt_irrefl _ this
  have hγu : M.hStar * u = γ := by rw [← hhpos u hu0.le]; exact hγ
  refine ⟨?_, ?_, hl0, ?_, hu0⟩
  · rw [← hγu]; positivity
  · have h1 := hhneg l hl0.le
    simp only [Model.lgam]
    rw [← hlval, h1]
    field_simp
  · simp only [Model.ugam]
    rw [← hγu]
    field_simp
