-- Prove2me | solution 1 for ApproachRegret.ToOLO.lemma13_dist_cone
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-06T13:53:33.087083+00:00
-- url     : https://prove2.me/submissions/4a00e81a-b838-4e47-84f6-ced261056b5f

import Definitions.Def_ApproachRegret_ToOLO_Cones

open scoped RealInnerProductSpace
open Set
set_option autoImplicit false

namespace ParentGeometry
open ApproachRegret.ToOLO

lemma polar_bound {d : ℕ} {C : Set (E d)} (hne : C.Nonempty)
    {θ x : E d} (hθ : θ ∈ polar C) (hθn : ‖θ‖ ≤ 1) :
    ⟪θ, x⟫ ≤ Metric.infDist x C := by
  apply (Metric.le_infDist hne).2
  intro y hy
  have h1 := hθ y hy
  have h2 := real_inner_le_norm θ (x-y)
  have h3 : ⟪θ, x⟫ = ⟪θ, x-y⟫ + ⟪θ, y⟫ := by rw [inner_sub_right]; ring
  rw [dist_eq_norm]
  nlinarith [norm_nonneg (x-y)]

theorem cone_distance {d : ℕ} (C : Set (E d)) (x : E d)
    (hC : Convex ℝ C) (hcone : ∀ z ∈ C, ∀ α : ℝ, 0 ≤ α → α • z ∈ C)
    (hne : C.Nonempty) :
    IsGreatest ((fun θ : E d => ⟪θ, x⟫) ''
      (polar C ∩ Metric.closedBall 0 1)) (Metric.infDist x C) := by
  have hcl : (closure C).Nonempty := hne.closure
  obtain ⟨v,hv,hmin⟩ := exists_norm_eq_iInf_of_complete_convex hcl
    isClosed_closure.isComplete hC.closure x
  have hp := (norm_eq_iInf_iff_real_inner_le_zero hC.closure hv).1 hmin
  have hzero : (0 : E d) ∈ closure C := by
    obtain ⟨z,hz⟩ := hne
    exact subset_closure (by simpa using hcone z hz 0 le_rfl)
  have htwo : (2 : ℝ) • v ∈ closure C := by
    have hm : MapsTo (fun z : E d => (2 : ℝ) • z) C C :=
      fun z hz => hcone z hz 2 (by norm_num)
    exact hm.closure (by fun_prop) hv
  have hp0 := hp 0 hzero
  have hp2 := hp (2 • v) htwo
  simp only [zero_sub, inner_neg_right] at hp0
  simp only [two_smul, add_sub_cancel_left] at hp2
  have horth : ⟪x-v,v⟫ = 0 := by linarith
  have hpolar : x-v ∈ polar C := by
    intro z hz
    have h := hp z (subset_closure hz)
    rw [inner_sub_right, horth] at h
    simpa using h
  have hdist : ‖x-v‖ = Metric.infDist x C := by
    rw [← Metric.infDist_closure, Metric.infDist_eq_iInf]
    simpa only [dist_eq_norm] using hmin
  have hupper : ∀ z ∈ ((fun θ : E d => ⟪θ,x⟫) ''
      (polar C ∩ Metric.closedBall 0 1)), z ≤ Metric.infDist x C := by
    rintro z ⟨θ,⟨hpol,hball⟩,rfl⟩
    exact polar_bound hne hpol (by simpa using hball)
  refine ⟨?_,hupper⟩
  by_cases hnorm : ‖x-v‖ = 0
  · refine ⟨0,⟨?_,by simp⟩,?_⟩
    · intro z hz; simp
    · simpa using hnorm.symm.trans hdist
  · let θ : E d := ‖x-v‖⁻¹ • (x-v)
    have hpos : 0 ≤ ‖x-v‖⁻¹ := inv_nonneg.mpr (norm_nonneg _)
    have hθpol : θ ∈ polar C := by
      intro z hz
      simpa [θ, inner_smul_left] using mul_nonpos_of_nonneg_of_nonpos hpos (hpolar z hz)
    have hθnorm : ‖θ‖ = 1 := by
      simp [θ, norm_smul, Real.norm_eq_abs, abs_of_nonneg hpos, hnorm]
    have hprod : ⟪x-v,x⟫ = ‖x-v‖ ^ 2 := by
      have hh := real_inner_self_eq_norm_sq (x-v)
      rw [inner_sub_right, horth, sub_zero] at hh
      exact hh
    refine ⟨θ,⟨hθpol,by simpa using hθnorm.le⟩,?_⟩
    change ⟪θ,x⟫ = Metric.infDist x C
    rw [show ⟪θ,x⟫ = ‖x-v‖⁻¹ * ⟪x-v,x⟫ by simp [θ, inner_smul_left], hprod, ← hdist]
    field_simp

end ParentGeometry



open ApproachRegret.ToOLO

/-- Lemma 13, p. 35, including attainment of the maximum. -/
theorem solution {d : ℕ} (C : Set (E d)) (x : E d)
    (hC : Convex ℝ C) (hcone : ∀ z ∈ C, ∀ α : ℝ, 0 ≤ α → α • z ∈ C)
    (hne : C.Nonempty) :
    IsGreatest ((fun θ : E d => ⟪θ, x⟫) ''
      (polar C ∩ Metric.closedBall 0 1)) (Metric.infDist x C) := by exact ParentGeometry.cone_distance C x hC hcone hne


