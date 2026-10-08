-- Prove2me | solution 1 for ApproachRegret.ToApproach.lemma13_dist_cone
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T14:26:19.934992+00:00
-- url     : https://prove2.me/submissions/5bb1ef92-1c0d-4199-bff5-a6f74bf54436

import Mathlib
import Definitions.Def_ApproachRegret_ToApproach_Setup

open scoped RealInnerProductSpace

set_option autoImplicit false

namespace ApproachRegret66f6

open ApproachRegret.ToOLO ApproachRegret.ToApproach

theorem convex_of_cc {d : ℕ} {C : Set (E d)} (hC : IsConvexCone C) : Convex ℝ C := by
  intro z hz w hw a b ha hb _
  exact hC.2 _ (hC.1 a ha z hz) _ (hC.1 b hb w hw)

theorem closure_smul_mem {d : ℕ} {C : Set (E d)} (hC : IsConvexCone C) {α : ℝ} (hα : 0 ≤ α)
    {z : E d} (hz : z ∈ closure C) : α • z ∈ closure C :=
  map_mem_closure (continuous_const_smul α) hz (fun w hw => hC.1 α hα w hw)

theorem upper {d : ℕ} {C : Set (E d)} (hCne : C.Nonempty) (x θ : E d)
    (hθ : θ ∈ polar C) (hθn : θ ∈ Metric.closedBall (0 : E d) 1) :
    ⟪θ, x⟫ ≤ Metric.infDist x C := by
  rw [Metric.le_infDist hCne]
  intro y hy
  have h1 : ⟪θ, y⟫ ≤ 0 := hθ y hy
  have h2 : ⟪θ, x - y⟫ ≤ ‖θ‖ * ‖x - y‖ := real_inner_le_norm θ (x - y)
  have h3 : ‖θ‖ ≤ 1 := by simpa using hθn
  have h4 : ⟪θ, x - y⟫ = ⟪θ, x⟫ - ⟪θ, y⟫ := inner_sub_right θ x y
  rw [dist_eq_norm]
  nlinarith [norm_nonneg (x - y), norm_nonneg θ]

end ApproachRegret66f6

open RealInnerProductSpace in
theorem solution {d : ℕ} (C : Set (ApproachRegret.ToOLO.E d)) (hC : ApproachRegret.ToApproach.IsConvexCone C) (hCne : C.Nonempty)
    (x : ApproachRegret.ToOLO.E d) :
    IsGreatest ((fun θ : ApproachRegret.ToOLO.E d => ⟪θ, x⟫) '' (ApproachRegret.ToOLO.polar C ∩ Metric.closedBall 0 1))
      (Metric.infDist x C) := by
  set K := closure C with hK
  have hKc : Convex ℝ K := (ApproachRegret66f6.convex_of_cc hC).closure
  have hKne : K.Nonempty := hCne.closure
  have hKcomp : IsComplete K := isClosed_closure.isComplete
  obtain ⟨p, hpK, hp⟩ := exists_norm_eq_iInf_of_complete_convex hKne hKcomp hKc x
  have hvar := (norm_eq_iInf_iff_real_inner_le_zero hKc hpK).1 hp
  -- ⟪x - p, p⟫ = 0
  have h0 : (0 : ApproachRegret.ToOLO.E d) ∈ K := by
    obtain ⟨c, hc⟩ := hCne
    have := ApproachRegret66f6.closure_smul_mem hC (le_refl 0) (subset_closure hc)
    simpa using this
  have h2p : (2 : ℝ) • p ∈ K := ApproachRegret66f6.closure_smul_mem hC (by norm_num) hpK
  have hA := hvar 0 h0
  have hB := hvar _ h2p
  have hpp : ⟪x - p, p⟫ = 0 := by
    have e1 : (0 : ApproachRegret.ToOLO.E d) - p = -p := by simp
    have e2 : (2 : ℝ) • p - p = p := by rw [two_smul]; abel
    rw [e1, inner_neg_right] at hA
    rw [e2] at hB
    linarith
  -- x - p is in the polar
  have hpol : ∀ z ∈ C, ⟪x - p, z⟫ ≤ 0 := by
    intro z hz
    have hm : (2 : ℝ) • ((1/2 : ℝ) • p + (1/2 : ℝ) • z) ∈ K :=
      ApproachRegret66f6.closure_smul_mem hC (by norm_num)
        (hKc hpK (subset_closure hz) (by norm_num) (by norm_num) (by norm_num))
    have e : (2 : ℝ) • ((1/2 : ℝ) • p + (1/2 : ℝ) • z) - p = z := by
      rw [smul_add, smul_smul, smul_smul]; norm_num
    have := hvar _ hm
    rwa [e] at this
  set v := x - p with hv
  set θ := ‖v‖⁻¹ • v with hθ
  have hθpol : θ ∈ ApproachRegret.ToOLO.polar C := by
    intro z hz
    show ⟪‖v‖⁻¹ • v, z⟫ ≤ 0
    rw [real_inner_smul_left]
    exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.2 (norm_nonneg _)) (hpol z hz)
  have hθball : θ ∈ Metric.closedBall (0 : ApproachRegret.ToOLO.E d) 1 := by
    rw [Metric.mem_closedBall, dist_zero_right, hθ, norm_smul, norm_inv, norm_norm]
    rcases eq_or_ne ‖v‖ 0 with h | h
    · rw [h]; simp
    · rw [inv_mul_cancel₀ h]
  have hθx : ⟪θ, x⟫ = ‖v‖ := by
    have hx : x = v + p := by rw [hv]; abel
    rw [hθ, real_inner_smul_left]
    conv_lhs => rw [hx]
    rw [inner_add_right, hpp, add_zero, real_inner_self_eq_norm_sq]
    rcases eq_or_ne ‖v‖ 0 with h | h
    · rw [h]; simp
    · field_simp
  have hup := ApproachRegret66f6.upper hCne x θ hθpol hθball
  have hlow : Metric.infDist x C ≤ ‖v‖ := by
    rw [← Metric.infDist_closure, ← hK, hv, ← dist_eq_norm]
    exact Metric.infDist_le_dist_of_mem hpK
  refine ⟨⟨θ, ⟨hθpol, hθball⟩, ?_⟩, ?_⟩
  · show ⟪θ, x⟫ = Metric.infDist x C
    linarith
  · rintro r ⟨φ, ⟨hφp, hφb⟩, rfl⟩
    exact ApproachRegret66f6.upper hCne x φ hφp hφb
