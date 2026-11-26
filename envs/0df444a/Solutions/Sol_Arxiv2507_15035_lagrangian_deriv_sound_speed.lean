-- Prove2me | solution 1 for Arxiv2507_15035.lagrangian_deriv_sound_speed
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T04:05:53.423812+00:00
-- url     : https://prove2.me/submissions/e807fb1b-464b-4e55-a72f-6ec2b59953e4

import Mathlib
import Definitions.Def_Arxiv2507_15035_Basic

set_option autoImplicit false

open MeasureTheory Filter Topology

namespace S77LD
open Arxiv2507_15035

lemma q_deriv (ω a b t : ℝ) (hne : a + t * b ≠ 0) :
    HasDerivAt (fun t : ℝ => (ω / (a + t * b)) ^ 2) (-2 * ω ^ 2 * b / (a + t * b) ^ 3) t := by
  have h1 : HasDerivAt (fun y : ℝ => a + y * b) (1 * b) t := ((hasDerivAt_id' t).mul_const b).const_add a
  have h2 := ((h1.inv hne).const_mul ω).pow 2
  have e : (fun t : ℝ => (ω / (a + t * b)) ^ 2) = fun y => (ω * (a + y * b)⁻¹) ^ 2 := by
    funext y; rw [div_eq_mul_inv]
  rw [e]
  refine HasDerivAt.congr_deriv h2 ?_
  simp only [Pi.inv_apply]
  norm_num
  field_simp

end S77LD

open Arxiv2507_15035 S77LD in
theorem solution {n M : ℕ} (ω : ℝ) (hω : 0 < ω)
    (c : Pt n → ℝ) (ROI : Set (Pt n)) (c0 : ℝ) (hc : IsSoundSpeed c ROI c0)
    (s : Pt n → ℂ) (xf : Fin M → Pt n) (y : Fin M → ℂ)
    (u : Pt n → ℂ) (hu : ContDiff ℝ 2 u) (lam : Pt n → ℂ) (hlam : LocallyIntegrable lam)
    (hint : Integrable (fun x => (starRingEnd ℂ) (lam x) * (helmholtzOp ω c u x + s x)))
    (h : Pt n → ℝ) (hh : IsTestFn h) :
    HasDerivAt (fun t : ℝ => lagrangianTerm ω (fun x => c x + t * h x) s xf y u lam)
      (∫ x, 2 * ω ^ 2 * ((starRingEnd ℂ) (lam x) * u x).re / c x ^ 3 * h x) 0 := by
  obtain ⟨hcm, ⟨m, hm, hmc⟩, -, -, -⟩ := hc
  have hhc : Continuous h := hh.1.continuous
  obtain ⟨C, hC⟩ := hhc.bounded_above_of_compact_support hh.2
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC 0)
  set ε := m / (2 * (C + 1)) with hε
  have hεpos : 0 < ε := by positivity
  have hpos : ∀ t ∈ Metric.ball (0:ℝ) ε, ∀ x, m / 2 ≤ c x + t * h x := by
    intro t ht x
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at ht
    have h1 : |t * h x| ≤ ε * C := by
      rw [abs_mul]; exact mul_le_mul ht.le (by simpa [Real.norm_eq_abs] using hC x) (abs_nonneg _) hεpos.le
    have h2 : ε * C ≤ m / 2 := by
      rw [hε, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    have := neg_abs_le (t * h x)
    linarith [hmc x]
  set F : ℝ → Pt n → ℂ := fun t x => (starRingEnd ℂ) (lam x) *
      (Laplacian.laplacian u x + (((ω / (c x + t * h x)) ^ 2 : ℝ) : ℂ) * u x + s x) with hF
  set F' : ℝ → Pt n → ℂ := fun t x => (starRingEnd ℂ) (lam x) * u x *
      (((-2 * ω ^ 2 * h x / (c x + t * h x) ^ 3) : ℝ) : ℂ) with hF'
  have hF0 : F 0 = fun x => (starRingEnd ℂ) (lam x) * (helmholtzOp ω c u x + s x) := by
    funext x; simp [hF, helmholtzOp]
  have hlamm : AEStronglyMeasurable (fun x => (starRingEnd ℂ) (lam x)) volume :=
    Complex.continuous_conj.comp_aestronglyMeasurable hlam.aestronglyMeasurable
  have hFm : ∀ t, AEStronglyMeasurable (F t) volume := by
    intro t
    have e : F t = fun x => F 0 x + (starRingEnd ℂ) (lam x) * u x *
        ((((ω / (c x + t * h x)) ^ 2 - (ω / (c x + 0 * h x)) ^ 2 : ℝ)) : ℂ) := by
      funext x; simp only [hF]; push_cast; ring
    rw [e]
    refine (hF0 ▸ hint).aestronglyMeasurable.add ((hlamm.mul hu.continuous.aestronglyMeasurable).mul ?_)
    exact (Complex.measurable_ofReal.comp (by fun_prop)).aestronglyMeasurable
  have hK : IsCompact (tsupport h) := hh.2
  set B := 2 * ω ^ 2 * C / (m / 2) ^ 3 with hB
  have hbi : IntegrableOn (fun x => ‖lam x‖ * ‖u x‖ * B) (tsupport h) := by
    have := ((show IntegrableOn (fun x => ‖lam x‖) (tsupport h) volume from
      (hlam.integrableOn_isCompact hK).norm).mul_continuousOn
      (hu.continuous.norm.continuousOn) hK)
    exact this.mul_const B
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (x₀ := (0:ℝ))
    (F := F) (F' := F') (bound := (tsupport h).indicator (fun x => ‖lam x‖ * ‖u x‖ * B))
    (Metric.ball_mem_nhds 0 hεpos) (Eventually.of_forall hFm) (hF0 ▸ hint)
    ((hlamm.mul hu.continuous.aestronglyMeasurable).mul
      (Complex.measurable_ofReal.comp (by fun_prop)).aestronglyMeasurable) ?_
    (hbi.integrable_indicator hK.measurableSet) ?_
  rotate_left
  · refine Eventually.of_forall (fun x t ht => ?_)
    have hd := hpos t ht x
    by_cases hx : x ∈ tsupport h
    · rw [Set.indicator_of_mem hx]
      simp only [hF', norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [abs_div, abs_of_pos (pow_pos (by linarith) 3 : 0 < (c x + t * h x) ^ 3), hB]
      apply div_le_div₀ (by positivity)
      · have hCx := hC x; rw [Real.norm_eq_abs] at hCx
        obtain ⟨a1, a2⟩ := abs_le.1 hCx
        rw [abs_le]; constructor <;> nlinarith [sq_nonneg ω]
      · positivity
      · exact pow_le_pow_left₀ (by positivity) hd 3
    · rw [Set.indicator_of_notMem hx]
      simp only [hF']; rw [image_eq_zero_of_notMem_tsupport hx]; simp
  · refine Eventually.of_forall (fun x t ht => ?_)
    have hd := hpos t ht x
    have hne : c x + t * h x ≠ 0 := by linarith
    have hq := (q_deriv ω (c x) (h x) t hne).ofReal_comp
    have := ((hq.mul_const (u x)).const_add (Laplacian.laplacian u x)).add_const (s x)
    have := this.const_mul ((starRingEnd ℂ) (lam x))
    refine this.congr_deriv ?_
    simp only [hF']; ring
  obtain ⟨hint', hd⟩ := hd
  have hre := (Complex.reCLM.hasFDerivAt.comp_hasDerivAt (0:ℝ) hd)
  have hL := (hasDerivAt_const (0:ℝ) (misfit xf y u)).sub hre
  have e : (fun t : ℝ => lagrangianTerm ω (fun x => c x + t * h x) s xf y u lam) =
      fun t => misfit xf y u - (Complex.reCLM ∘ fun t => ∫ x, F t x) t := by
    funext t; simp [lagrangianTerm, realPairing, helmholtzOp, hF]
  rw [e]
  refine hL.congr_deriv ?_
  simp only [Complex.reCLM_apply, zero_sub]
  have hr : (∫ a, F' 0 a).re = ∫ a, (F' 0 a).re := (integral_re hint').symm
  rw [hr, ← integral_neg]
  congr 1; funext x
  simp only [hF', zero_mul, add_zero, Complex.re_mul_ofReal]
  ring
