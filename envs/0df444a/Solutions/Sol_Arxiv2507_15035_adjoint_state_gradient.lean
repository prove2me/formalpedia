-- Prove2me | solution 1 for Arxiv2507_15035.adjoint_state_gradient
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T04:09:54.793431+00:00
-- url     : https://prove2.me/submissions/acb288e5-43f6-4031-98fd-0f667907d10a

import Mathlib
import Definitions.Def_Arxiv2507_15035_Basic

set_option autoImplicit false

open MeasureTheory Filter Topology

namespace S76AD
open Arxiv2507_15035

lemma two_le {n : ℕ} {φ : Pt n → ℂ} (h : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) : ContDiff ℝ 2 φ :=
  h.of_le (WithTop.coe_le_coe.2 le_top)

lemma lap_cont {n : ℕ} (φ : Pt n → ℂ) (hφ : ContDiff ℝ 2 φ) : Continuous (Laplacian.laplacian φ) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  apply continuous_finsetSum; intro i _
  exact (continuous_eval_const _).comp (hφ.continuous_iteratedFDeriv (by norm_num))

lemma lap_supp {n : ℕ} (φ : Pt n → ℂ) (hφ : HasCompactSupport φ) :
    HasCompactSupport (Laplacian.laplacian φ) := by
  refine (hφ.iteratedFDeriv (𝕜 := ℝ) 2).mono ?_
  intro x hx
  contrapose! hx
  simp only [Function.mem_support, not_not] at hx ⊢
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  simp [hx]

lemma int_conj {n : ℕ} (lam : Pt n → ℂ) (hlam : LocallyIntegrable lam) (g : Pt n → ℂ)
    (hg : Continuous g) (hgs : HasCompactSupport g) :
    Integrable (fun x => (starRingEnd ℂ) (lam x) * g x) := by
  have h1 := hlam.integrable_smul_right_of_hasCompactSupport (g := fun x => (starRingEnd ℂ) (g x))
    (Complex.continuous_conj.comp hg) (hgs.comp_left (map_zero _))
  have h2 := (Complex.conjCLE.toContinuousLinearMap).integrable_comp h1
  have e : (fun a => (Complex.conjCLE.toContinuousLinearMap) (lam a • (starRingEnd ℂ) (g a))) =
      fun x => (starRingEnd ℂ) (lam x) * g x := by
    funext x; simp [smul_eq_mul, mul_comm]
  rwa [e] at h2

lemma S_int {n : ℕ} (ω : ℝ) (c : Pt n → ℝ) (ROI : Set (Pt n)) (c0 : ℝ) (hc : IsSoundSpeed c ROI c0)
    (lam : Pt n → ℂ) (hlam : LocallyIntegrable lam) (φ : Pt n → ℂ) (hφ : IsTestFn φ) :
    Integrable (fun x => (starRingEnd ℂ) (lam x) * helmholtzOp ω c φ x) := by
  obtain ⟨hcm, ⟨m, hm, hmc⟩, -, -, -⟩ := hc
  have hφ2 := two_le hφ.1
  have i1 := int_conj lam hlam _ (lap_cont φ hφ2) (lap_supp φ hφ.2)
  have i2 := int_conj lam hlam φ hφ2.continuous hφ.2
  have hmeas : AEStronglyMeasurable (fun x => (((ω / c x) ^ 2 : ℝ) : ℂ)) volume := by
    apply Measurable.aestronglyMeasurable
    exact Complex.measurable_ofReal.comp ((measurable_const.div hcm).pow_const 2)
  have i3 := i2.bdd_mul (c := (ω / m) ^ 2) hmeas (Filter.Eventually.of_forall fun x => by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hcx : 0 < c x := lt_of_lt_of_le hm (hmc x)
    rw [div_pow, div_pow]
    apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
    exact pow_le_pow_left₀ hm.le (hmc x) 2)
  have e : (fun x => (starRingEnd ℂ) (lam x) * helmholtzOp ω c φ x) = fun x =>
      (starRingEnd ℂ) (lam x) * Laplacian.laplacian φ x +
        (((ω / c x) ^ 2 : ℝ) : ℂ) * ((starRingEnd ℂ) (lam x) * φ x) := by
    funext x; simp only [helmholtzOp]; ring
  rw [e]; exact i1.add i3

lemma S_lin {n : ℕ} (ω : ℝ) (c : Pt n → ℝ) (u φ : Pt n → ℂ) (hu : ContDiff ℝ 2 u)
    (hφ : ContDiff ℝ 2 φ) (t : ℝ) (x : Pt n) :
    helmholtzOp ω c (fun x => u x + t • φ x) x = helmholtzOp ω c u x + t * helmholtzOp ω c φ x := by
  have e : (fun x => u x + t • φ x) = u + t • φ := rfl
  simp only [helmholtzOp]
  rw [e, ContDiffAt.laplacian_add (f₂ := t • φ) hu.contDiffAt (hφ.contDiffAt.const_smul t),
    InnerProductSpace.laplacian_smul t hφ.contDiffAt]
  simp [Complex.real_smul]; ring

lemma S_I {n : ℕ} (ω : ℝ) (c : Pt n → ℝ) (φ : Pt n → ℂ) (hφ : ContDiff ℝ 2 φ) (x : Pt n) :
    helmholtzOp ω c (fun x => Complex.I * φ x) x = Complex.I * helmholtzOp ω c φ x := by
  have e : (fun x => Complex.I * φ x) = Complex.I • φ := rfl
  simp only [helmholtzOp]
  rw [e, InnerProductSpace.laplacian_smul Complex.I hφ.contDiffAt]
  simp [smul_eq_mul]; ring

lemma S_conj {n : ℕ} (ω : ℝ) (c : Pt n → ℝ) (φ : Pt n → ℂ) (x : Pt n) :
    helmholtzOp ω c (fun x => (starRingEnd ℂ) (φ x)) x = (starRingEnd ℂ) (helmholtzOp ω c φ x) := by
  have e : (fun x => (starRingEnd ℂ) (φ x)) = (Complex.conjCLE : ℂ ≃L[ℝ] ℂ) ∘ φ := rfl
  simp only [helmholtzOp]
  rw [e, InnerProductSpace.laplacian_CLE_comp_left]
  simp [map_add, map_mul, Complex.conj_ofReal]

lemma test_conj {n : ℕ} (φ : Pt n → ℂ) (hφ : IsTestFn φ) : IsTestFn (fun x => (starRingEnd ℂ) (φ x)) := by
  refine ⟨?_, ?_⟩
  · have := (Complex.conjCLE : ℂ ≃L[ℝ] ℂ).contDiff.comp hφ.1
    exact this
  · exact hφ.2.comp_left (g := fun z => (starRingEnd ℂ) z) (map_zero _)

lemma test_I {n : ℕ} (φ : Pt n → ℂ) (hφ : IsTestFn φ) : IsTestFn (fun x => Complex.I * φ x) := by
  refine ⟨contDiff_const.mul hφ.1, ?_⟩
  exact hφ.2.comp_left (g := fun z => Complex.I * z) (by simp)

lemma misfit_exp {n M : ℕ} (xf : Fin M → Pt n) (y : Fin M → ℂ) (u φ : Pt n → ℂ) (t : ℝ) :
    misfit xf y (fun x => u x + t • φ x) = misfit xf y u +
      t * (∑ i, 2 * (starRingEnd ℂ) (u (xf i) - y i) * φ (xf i)).re +
      t ^ 2 * ∑ i, ‖φ (xf i)‖ ^ 2 := by
  simp only [misfit, Complex.re_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.real_smul]
  simp [Complex.mul_re, Complex.mul_im]
  ring

end S76AD

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

theorem lag_deriv {n M : ℕ} (ω : ℝ) (hω : 0 < ω)
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

end S77LD

open Arxiv2507_15035 S76AD S77LD in
theorem solution {n M : ℕ} (ω : ℝ) (hω : 0 < ω)
    (c : Pt n → ℝ) (ROI : Set (Pt n)) (c0 : ℝ) (hc : IsSoundSpeed c ROI c0)
    (s : Pt n → ℂ) (xf : Fin M → Pt n) (y : Fin M → ℂ)
    (u : Pt n → ℂ) (hu : ContDiff ℝ 2 u) (hfwd : ∀ᵐ x, helmholtzOp ω c u x = -s x)
    (lam : Pt n → ℂ) (hadj : IsWeakPointSourceSol ω c lam xf (fun i => u (xf i) - y i)) :
    (∀ φ : Pt n → ℂ, IsTestFn φ →
      HasDerivAt (fun t : ℝ => lagrangianTerm ω c s xf y u (fun x => 2 * lam x + t • φ x)) 0 0) ∧
    (∀ φ : Pt n → ℂ, IsTestFn φ →
      HasDerivAt (fun t : ℝ =>
        lagrangianTerm ω c s xf y (fun x => u x + t • φ x) (fun x => 2 * lam x)) 0 0) ∧
    (∀ h : Pt n → ℝ, IsTestFn h →
      HasDerivAt (fun t : ℝ =>
        lagrangianTerm ω (fun x => c x + t * h x) s xf y u (fun x => 2 * lam x))
        (∫ x, 4 * ω ^ 2 * ((starRingEnd ℂ) (lam x) * u x).re / c x ^ 3 * h x) 0) := by
  have hlam : LocallyIntegrable lam := hadj.1
  have hz : ∀ l : Pt n → ℂ, (fun x => (starRingEnd ℂ) (l x) * (helmholtzOp ω c u x + s x)) =ᵐ[volume] 0 := by
    intro l
    filter_upwards [hfwd] with x hx
    simp [hx]
  have hz0 : ∀ l : Pt n → ℂ, ∫ x, (starRingEnd ℂ) (l x) * (helmholtzOp ω c u x + s x) = 0 := by
    intro l; rw [integral_congr_ae (hz l)]; simp
  refine ⟨?_, ?_, ?_⟩
  · intro φ hφ
    have e : (fun t : ℝ => lagrangianTerm ω c s xf y u (fun x => 2 * lam x + t • φ x)) =
        fun _ => misfit xf y u := by
      funext t; unfold lagrangianTerm realPairing
      rw [hz0 (fun x => 2 * lam x + t • φ x)]; simp
    rw [e]; exact hasDerivAt_const _ _
  · intro φ hφ
    set A := ∫ x, (starRingEnd ℂ) (lam x) * helmholtzOp ω c φ x with hA
    have hAc : (starRingEnd ℂ) A = ∑ i, (u (xf i) - y i) * (starRingEnd ℂ) (φ (xf i)) := by
      rw [← hadj.2 _ (test_conj φ hφ), hA, ← integral_conj]
      congr 1; funext x; rw [S_conj]; simp
    have hA' : A = ∑ i, (starRingEnd ℂ) (u (xf i) - y i) * φ (xf i) := by
      have := congrArg (starRingEnd ℂ) hAc
      rw [Complex.conj_conj] at this
      rw [this, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp
    have hform : ∀ t : ℝ, lagrangianTerm ω c s xf y (fun x => u x + t • φ x) (fun x => 2 * lam x) =
        misfit xf y u + t ^ 2 * ∑ i, ‖φ (xf i)‖ ^ 2 := by
      intro t
      unfold lagrangianTerm realPairing
      rw [misfit_exp]
      have e : (fun x => (starRingEnd ℂ) (2 * lam x) * (helmholtzOp ω c (fun x => u x + t • φ x) x + s x))
          =ᵐ[volume] fun x => ((t : ℂ) * 2) * ((starRingEnd ℂ) (lam x) * helmholtzOp ω c φ x) := by
        filter_upwards [hfwd] with x hx
        rw [S_lin ω c u φ hu (two_le hφ.1), hx]
        simp only [map_mul, map_ofNat]; ring
      rw [integral_congr_ae e, integral_const_mul, ← hA, hA']
      have : ((t : ℂ) * 2 * ∑ i, (starRingEnd ℂ) (u (xf i) - y i) * φ (xf i)).re =
          t * (∑ i, 2 * (starRingEnd ℂ) (u (xf i) - y i) * φ (xf i)).re := by
        rw [mul_assoc, Complex.re_ofReal_mul, Finset.mul_sum]
        congr 2; refine Finset.sum_congr rfl fun i _ => ?_; ring
      rw [this]; ring
    have e : (fun t : ℝ => lagrangianTerm ω c s xf y (fun x => u x + t • φ x) (fun x => 2 * lam x)) =
        fun t => misfit xf y u + t ^ 2 * ∑ i, ‖φ (xf i)‖ ^ 2 := by
      funext t; exact hform t
    rw [e]
    have h2 := ((hasDerivAt_pow 2 (0:ℝ)).mul_const (∑ i, ‖φ (xf i)‖ ^ 2)).const_add (misfit xf y u)
    exact h2.congr_deriv (by simp)
  · intro h hh
    have hint : Integrable (fun x => (starRingEnd ℂ) (2 * lam x) * (helmholtzOp ω c u x + s x)) :=
      (integrable_zero _ _ _).congr (hz (fun x => 2 * lam x)).symm
    have hl2 : LocallyIntegrable (fun x => 2 * lam x) := by
      exact hlam.smul (2 : ℂ)
    have := lag_deriv ω hω c ROI c0 hc s xf y u hu (fun x => 2 * lam x) hl2 hint h hh
    refine this.congr_deriv ?_
    congr 1; funext x
    simp only [map_mul, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]
    norm_num
    left; ring
