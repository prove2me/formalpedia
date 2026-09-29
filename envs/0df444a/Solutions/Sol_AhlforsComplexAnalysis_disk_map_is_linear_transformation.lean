-- Prove2me | solution 1 for AhlforsComplexAnalysis.disk_map_is_linear_transformation
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T13:20:56.564791+00:00
-- url     : https://prove2.me/submissions/e6753288-a70f-4238-9934-719ca3a9f47a

import Definitions.Def_AhlforsComplexAnalysis_Defs
import Mathlib

open AhlforsComplexAnalysis
open Metric Set Filter Topology

namespace AhlforsDisk

/-- The inverse of an injective holomorphic map on a connected open set is holomorphic. -/
lemma inv_differentiableOn {U V : Set ℂ} (hU : IsOpen U) (hUc : IsPreconnected U)
    (hV : IsOpen V) {G H : ℂ → ℂ} (hG : AnalyticOnNhd ℂ G U) (hinj : InjOn G U)
    (hHmaps : MapsTo H V U) (hGH : ∀ v ∈ V, G (H v) = v) (hGmaps : MapsTo G U V)
    (hne : ∃ x ∈ U, ∃ y ∈ U, x ≠ y) :
    DifferentiableOn ℂ H V := by
  -- open mapping
  have hopen : ∀ s ⊆ U, IsOpen s → IsOpen (G '' s) := by
    rcases hG.is_constant_or_isOpen hUc with ⟨w, hw⟩ | h
    · obtain ⟨x, hx, y, hy, hxy⟩ := hne
      exact absurd (hinj hx hy ((hw x hx).trans (hw y hy).symm)) hxy
    · exact h
  have hHG : ∀ x ∈ U, H (G x) = x := fun x hx =>
    hinj (hHmaps (hGmaps hx)) hx (hGH _ (hGmaps hx))
  -- continuity of H
  have hcont : ∀ v ∈ V, ContinuousAt H v := by
    intro v hv
    rw [ContinuousAt, (nhds_basis_opens (H v)).tendsto_right_iff]
    intro W ⟨hW, hWo⟩
    have hmem : v ∈ G '' (W ∩ U) := ⟨H v, ⟨hW, hHmaps hv⟩, hGH v hv⟩
    filter_upwards [(hopen _ inter_subset_right (hWo.inter hU)).mem_nhds hmem] with v' hv'
    obtain ⟨x, ⟨hxW, hxU⟩, rfl⟩ := hv'
    rw [hHG x hxU]; exact hxW
  -- derivative of G is not locally zero
  have hGd : AnalyticOnNhd ℂ (deriv G) U := hG.deriv
  have hnz : ∀ x ∈ U, ∀ᶠ z in 𝓝[≠] x, deriv G z ≠ 0 := by
    intro x hx
    rcases (hGd x hx).eventually_eq_zero_or_eventually_ne_zero with h | h
    · exfalso
      have hz : EqOn (deriv G) 0 U :=
        hGd.eqOn_zero_of_preconnected_of_eventuallyEq_zero hUc hx h
      obtain ⟨a, ha, b, hb, hab⟩ := hne
      exact hab (hinj ha hb (hU.is_const_of_deriv_eq_zero hUc hG.differentiableOn hz ha hb))
    · exact h
  intro v hv
  -- punctured neighbourhood behaviour
  have hx : H v ∈ U := hHmaps hv
  have htend : Tendsto H (𝓝[≠] v) (𝓝[≠] (H v)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      ((hcont v hv).tendsto.mono_left nhdsWithin_le_nhds) ?_
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (hV.mem_nhds hv)] with v' hv' hv'V
    intro h
    exact hv' (by rw [← hGH v' hv'V, ← hGH v hv, h]; exact Set.mem_singleton _)
  have hev : ∀ᶠ v' in 𝓝[≠] v, deriv G (H v') ≠ 0 := htend.eventually (hnz _ hx)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.1 (hev.and
    (nhdsWithin_le_nhds (hV.mem_nhds hv)))
  obtain ⟨δ, hδ, hδV⟩ := Metric.isOpen_iff.1 hV v hv
  set ρ := min ε δ with hρ
  have hρ0 : 0 < ρ := lt_min hε hδ
  have hsub : ball v ρ ⊆ V := (ball_subset_ball (min_le_right _ _)).trans hδV
  have hdiff : DifferentiableOn ℂ H (ball v ρ \ {v}) := by
    intro v' ⟨hv'b, hv'ne⟩
    have hv'V : v' ∈ V := hsub hv'b
    have hd : deriv G (H v') ≠ 0 :=
      (hball ⟨ball_subset_ball (min_le_left _ _) hv'b, hv'ne⟩).1
    have hGda : HasDerivAt G (deriv G (H v')) (H v') :=
      ((hG _ (hHmaps hv'V)).differentiableAt).hasDerivAt
    have := HasDerivAt.of_local_left_inverse (hcont v' hv'V) hGda hd
      (by filter_upwards [hV.mem_nhds hv'V] with y hy; exact hGH y hy)
    exact this.differentiableAt.differentiableWithinAt
  have := (Complex.differentiableOn_compl_singleton_and_continuousAt_iff
    (ball_mem_nhds v hρ0)).1 ⟨hdiff, hcont v hv⟩
  exact (this.differentiableAt (ball_mem_nhds v hρ0)).differentiableWithinAt


lemma mob_norm {c w : ℂ} (hc : ‖c‖ < 1) (hw : ‖w‖ < 1) :
    ‖w + c‖ < ‖1 + (starRingEnd ℂ) c * w‖ ∧ 1 + (starRingEnd ℂ) c * w ≠ 0 := by
  have hc2 : c.re ^ 2 + c.im ^ 2 < 1 := by
    have h := Complex.sq_norm c
    rw [Complex.normSq_apply] at h
    have : ‖c‖ ^ 2 < 1 := by nlinarith [norm_nonneg c]
    nlinarith
  have hw2 : w.re ^ 2 + w.im ^ 2 < 1 := by
    have h := Complex.sq_norm w
    rw [Complex.normSq_apply] at h
    have : ‖w‖ ^ 2 < 1 := by nlinarith [norm_nonneg w]
    nlinarith
  have key : ‖1 + (starRingEnd ℂ) c * w‖ ^ 2 - ‖w + c‖ ^ 2 =
      (1 - (w.re ^ 2 + w.im ^ 2)) * (1 - (c.re ^ 2 + c.im ^ 2)) := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im, Complex.mul_re,
      Complex.mul_im, Complex.conj_re, Complex.conj_im]
    ring
  have pos : 0 < (1 - (w.re ^ 2 + w.im ^ 2)) * (1 - (c.re ^ 2 + c.im ^ 2)) :=
    mul_pos (by linarith) (by linarith)
  constructor
  · exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) (by linarith)
  · intro h
    rw [h, norm_zero] at key
    nlinarith [sq_nonneg ‖w + c‖]

/-- the disk automorphism `w ↦ (w + c) / (1 + c̄ w)` -/
noncomputable def mob (c : ℂ) (w : ℂ) : ℂ := (w + c) / (1 + (starRingEnd ℂ) c * w)

lemma mob_mem {c w : ℂ} (hc : ‖c‖ < 1) (hw : ‖w‖ < 1) : ‖mob c w‖ < 1 := by
  obtain ⟨h1, h2⟩ := mob_norm hc hw
  rw [mob, norm_div, div_lt_one (norm_pos_iff.2 h2)]
  exact h1

lemma one_sub_conj_mul_ne {c : ℂ} (hc : ‖c‖ < 1) : 1 - (starRingEnd ℂ) c * c ≠ 0 := by
  rw [← Complex.normSq_eq_conj_mul_self]
  intro h
  have h' : (Complex.normSq c : ℂ) = 1 := by linear_combination -h
  have : Complex.normSq c = 1 := by exact_mod_cast h'
  rw [← Complex.sq_norm] at this
  nlinarith [norm_nonneg c]

lemma mob_neg_mob {c w : ℂ} (hc : ‖c‖ < 1) (hw : ‖w‖ < 1) : mob (-c) (mob c w) = w := by
  have hd := (mob_norm hc hw).2
  have hk := one_sub_conj_mul_ne hc
  set d := 1 + (starRingEnd ℂ) c * w with hddef
  set k := 1 - (starRingEnd ℂ) c * c with hkdef
  have e1 : mob c w + -c = w * k / d := by
    rw [mob, ← hddef]; field_simp; rw [hddef, hkdef]; ring
  have e2 : 1 + (starRingEnd ℂ) (-c) * mob c w = k / d := by
    rw [mob, ← hddef, map_neg]; field_simp; rw [hddef, hkdef]; ring
  rw [mob, e1, e2]
  field_simp


lemma mob_zero (c : ℂ) : mob c 0 = c := by simp [mob]

lemma mob_diff {c w : ℂ} (hc : ‖c‖ < 1) (hw : ‖w‖ < 1) : DifferentiableAt ℂ (mob c) w :=
  ((differentiableAt_id.add_const c).div (by fun_prop) (mob_norm hc hw).2)

theorem disk_main {a b : ℂ} {r s : ℝ}
    (hr : 0 < r) (hs : 0 < s) {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (Metric.ball a r))
    (hinj : Set.InjOn f (Metric.ball a r)) (honto : f '' Metric.ball a r = Metric.ball b s) :
    ∃ α β γ δ : ℂ, α * δ - β * γ ≠ 0 ∧
      ∀ z ∈ Metric.ball a r, γ * z + δ ≠ 0 ∧ f z = (α * z + β) / (γ * z + δ) := by
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have memD : ∀ w : ℂ, w ∈ ball (0 : ℂ) 1 ↔ ‖w‖ < 1 := fun w => mem_ball_zero_iff
  have hA : ∀ w ∈ ball (0 : ℂ) 1, a + r * w ∈ ball a r := by
    intro w hw
    rw [memD] at hw
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hr]
    nlinarith [norm_nonneg w]
  have hAinv : ∀ z ∈ ball a r, (z - a) / r ∈ ball (0 : ℂ) 1 := by
    intro z hz
    rw [memD, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, div_lt_one hr]
    rwa [mem_ball, dist_eq_norm] at hz
  set F : ℂ → ℂ := fun w => (f (a + r * w) - b) / s with hFdef
  have hFd : DifferentiableOn ℂ F (ball 0 1) := by
    intro w hw
    have h1 : DifferentiableAt ℂ f (a + r * w) := (hf _ (hA w hw)).differentiableAt
    have h2 : DifferentiableAt ℂ (fun w : ℂ => f (a + r * w)) w :=
      h1.comp w (by fun_prop : DifferentiableAt ℂ (fun w : ℂ => a + r * w) w)
    exact ((h2.sub_const b).div_const (s : ℂ)).differentiableWithinAt
  have hFmaps : ∀ w ∈ ball (0 : ℂ) 1, F w ∈ ball (0 : ℂ) 1 := by
    intro w hw
    have : f (a + r * w) ∈ ball b s := honto ▸ mem_image_of_mem f (hA w hw)
    rw [mem_ball, dist_eq_norm] at this
    rw [memD, hFdef, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs, div_lt_one hs]
    exact this
  have hFonto : ∀ v ∈ ball (0 : ℂ) 1, ∃ w ∈ ball (0 : ℂ) 1, F w = v := by
    intro v hv
    have : b + s * v ∈ ball b s := by
      rw [memD] at hv
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hs]
      nlinarith [norm_nonneg v]
    rw [← honto] at this
    obtain ⟨z, hz, hfz⟩ := this
    refine ⟨(z - a) / r, hAinv z hz, ?_⟩
    rw [hFdef]
    simp only
    rw [show a + r * ((z - a) / r) = z by field_simp; ring, hfz]
    field_simp; ring
  have hFinj : InjOn F (ball 0 1) := by
    intro w1 h1 w2 h2 h
    have h' := (div_left_inj' hsC).1 h
    rw [sub_left_inj] at h'
    have := hinj (hA w1 h1) (hA w2 h2) h'
    exact mul_left_cancel₀ hrC (by linear_combination this)
  obtain ⟨c, hcD, hFc⟩ := hFonto 0 (by simp)
  have hc : ‖c‖ < 1 := (memD c).1 hcD
  have hnc : ‖-c‖ < 1 := by rwa [norm_neg]
  set G : ℂ → ℂ := fun w => F (mob c w) with hGdef
  have hmobmaps : ∀ w ∈ ball (0 : ℂ) 1, mob c w ∈ ball (0 : ℂ) 1 := fun w hw =>
    (memD _).2 (mob_mem hc ((memD w).1 hw))
  have hGd : DifferentiableOn ℂ G (ball 0 1) :=
    hFd.comp (fun w hw => (mob_diff hc ((memD w).1 hw)).differentiableWithinAt) hmobmaps
  have hG0 : G 0 = 0 := by simp only [hGdef, mob_zero, hFc]
  have hGmaps : MapsTo G (ball 0 1) (ball 0 1) := fun w hw => hFmaps _ (hmobmaps w hw)
  have hGinj : InjOn G (ball 0 1) := by
    intro w1 h1 w2 h2 h
    have := hFinj (hmobmaps w1 h1) (hmobmaps w2 h2) h
    rw [← mob_neg_mob hc ((memD w1).1 h1), ← mob_neg_mob hc ((memD w2).1 h2), this]
  have hmm : ∀ v ∈ ball (0 : ℂ) 1, mob c (mob (-c) v) = v := fun v hv => by
    have := mob_neg_mob hnc ((memD v).1 hv); rwa [neg_neg] at this
  have hGonto : ∀ v ∈ ball (0 : ℂ) 1, ∃ w ∈ ball (0 : ℂ) 1, G w = v := by
    intro v hv
    obtain ⟨w, hw, hFw⟩ := hFonto v hv
    exact ⟨mob (-c) w, (memD _).2 (mob_mem hnc ((memD w).1 hw)), by
      simp only [hGdef]; rw [hmm w hw, hFw]⟩
  set H := Function.invFunOn G (ball (0 : ℂ) 1) with hHdef
  have hGH : ∀ v ∈ ball (0 : ℂ) 1, G (H v) = v := fun v hv =>
    Function.invFunOn_eq (hGonto v hv)
  have hHmaps : MapsTo H (ball 0 1) (ball 0 1) := fun v hv =>
    Function.invFunOn_mem (hGonto v hv)
  have hHd : DifferentiableOn ℂ H (ball 0 1) :=
    inv_differentiableOn isOpen_ball (convex_ball 0 1).isPreconnected isOpen_ball
      (hGd.analyticOnNhd isOpen_ball) hGinj hHmaps hGH hGmaps
      ⟨0, by simp, 1 / 2, by rw [memD]; norm_num, by norm_num⟩
  have hH0 : H 0 = 0 := hGinj (hHmaps (by simp)) (by simp) (by rw [hGH 0 (by simp), hG0])
  have hGle : ∀ w ∈ ball (0 : ℂ) 1, ‖G w‖ ≤ ‖w‖ := fun w hw =>
    Complex.norm_le_norm_of_mapsTo_ball hGd (fun x hx => ball_subset_closedBall (hGmaps hx))
      hG0 ((memD w).1 hw)
  have hHle : ∀ v ∈ ball (0 : ℂ) 1, ‖H v‖ ≤ ‖v‖ := fun v hv =>
    Complex.norm_le_norm_of_mapsTo_ball hHd (fun x hx => ball_subset_closedBall (hHmaps hx))
      hH0 ((memD v).1 hv)
  have hGeq : ∀ w ∈ ball (0 : ℂ) 1, ‖G w‖ = ‖w‖ := by
    intro w hw
    have hHG : H (G w) = w := hGinj (hHmaps (hGmaps hw)) hw (hGH _ (hGmaps hw))
    have := hHle _ (hGmaps hw)
    rw [hHG] at this
    exact le_antisymm (hGle w hw) this
  have hhalf : (1 / 2 : ℂ) ∈ ball (0 : ℂ) 1 := by rw [memD]; norm_num
  obtain ⟨C, hC, hCeq⟩ := Complex.affine_of_mapsTo_ball_of_exists_norm_dslope_eq_div'
    (c := 0) (R₁ := 1) (R₂ := 1) hGd
    (fun x hx => by rw [hG0]; exact ball_subset_closedBall (hGmaps hx))
    ⟨1 / 2, hhalf, by
      rw [dslope_of_ne _ (by norm_num : (1 / 2 : ℂ) ≠ 0), slope_def_field, hG0, sub_zero,
        sub_zero, norm_div, hGeq _ hhalf]
      norm_num⟩
  have hC0 : C ≠ 0 := by intro h; rw [h, norm_zero] at hC; norm_num at hC
  have hFform : ∀ v ∈ ball (0 : ℂ) 1, F v = mob (-c) v * C := by
    intro v hv
    have h1 : F v = G (mob (-c) v) := by simp only [hGdef]; rw [hmm v hv]
    rw [h1, hCeq ((memD _).2 (mob_mem hnc ((memD v).1 hv))), hG0]
    simp only [sub_zero, zero_add, smul_eq_mul]
  have hk := one_sub_conj_mul_ne hc
  refine ⟨s * C - b * (starRingEnd ℂ) c, b * (r + (starRingEnd ℂ) c * a) - s * C * (a + c * r),
    -(starRingEnd ℂ) c, r + (starRingEnd ℂ) c * a, ?_, fun z hz => ?_⟩
  · have e : (s * C - b * (starRingEnd ℂ) c) * (r + (starRingEnd ℂ) c * a) -
        (b * (r + (starRingEnd ℂ) c * a) - s * C * (a + c * r)) * -(starRingEnd ℂ) c =
        s * C * r * (1 - (starRingEnd ℂ) c * c) := by ring
    rw [e]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero hsC hC0) hrC) hk
  · set v := (z - a) / r with hv
    have hvD := hAinv z hz
    have hden : 1 + (starRingEnd ℂ) (-c) * v ≠ 0 := (mob_norm hnc ((memD v).1 hvD)).2
    have hzv : z = a + r * v := by rw [hv]; field_simp; ring
    have hgd : -(starRingEnd ℂ) c * z + (r + (starRingEnd ℂ) c * a) =
        r * (1 + (starRingEnd ℂ) (-c) * v) := by rw [hzv, map_neg]; ring
    refine ⟨by rw [hgd]; exact mul_ne_zero hrC hden, ?_⟩
    have hfz : f z = b + s * F v := by
      rw [hFdef]; simp only; rw [← hzv]; field_simp; ring
    rw [hfz, hFform v hvD, hgd, mob, eq_div_iff (mul_ne_zero hrC hden)]
    have hq : (v + -c) / (1 + (starRingEnd ℂ) (-c) * v) * (1 + (starRingEnd ℂ) (-c) * v) =
        v + -c := div_mul_cancel₀ _ hden
    rw [hzv]
    rw [map_neg] at hq ⊢
    linear_combination (↑s * C * ↑r) * hq

end AhlforsDisk

open AhlforsDisk

theorem solution {a b : ℂ} {r s : ℝ}
    (hr : 0 < r) (hs : 0 < s) {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (Metric.ball a r))
    (hinj : Set.InjOn f (Metric.ball a r)) (honto : f '' Metric.ball a r = Metric.ball b s) :
    ∃ α β γ δ : ℂ, α * δ - β * γ ≠ 0 ∧
      ∀ z ∈ Metric.ball a r, γ * z + δ ≠ 0 ∧ f z = (α * z + β) / (γ * z + δ) := by
  exact AhlforsDisk.disk_main hr hs hf hinj honto
