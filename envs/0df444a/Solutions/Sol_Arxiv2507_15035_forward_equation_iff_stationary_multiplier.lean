-- Prove2me | solution 1 for Arxiv2507_15035.forward_equation_iff_stationary_multiplier
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T03:14:10.536392+00:00
-- url     : https://prove2.me/submissions/6420ae20-ebf5-42d7-8f58-865367f25f4d

import Mathlib
import Definitions.Def_Arxiv2507_15035_Basic

set_option autoImplicit false

open MeasureTheory Filter Topology

namespace S76FE
open Arxiv2507_15035

lemma f_loc {n : ℕ} (ω : ℝ) (c : Pt n → ℝ) (ROI : Set (Pt n)) (c0 : ℝ) (hc : IsSoundSpeed c ROI c0)
    (s : Pt n → ℂ) (hs : LocallyIntegrable s) (u : Pt n → ℂ) (hu : ContDiff ℝ 2 u) :
    LocallyIntegrable (fun x => helmholtzOp ω c u x + s x) := by
  obtain ⟨hcm, ⟨m, hm, hmc⟩, -, -, -⟩ := hc
  have h1 : Continuous (Laplacian.laplacian u) := by
    rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
    apply continuous_finset_sum; intro i _
    exact (continuous_eval_const _).comp (hu.continuous_iteratedFDeriv (by norm_num))
  have h2 : LocallyIntegrable (fun x => (((ω / c x) ^ 2 : ℝ) : ℂ) * u x) := by
    rw [locallyIntegrable_iff]
    intro K hK
    have hmeas : AEStronglyMeasurable (fun x => (((ω / c x) ^ 2 : ℝ) : ℂ)) (volume.restrict K) := by
      apply Measurable.aestronglyMeasurable
      exact Complex.measurable_ofReal.comp ((measurable_const.div hcm).pow_const 2)
    refine (hu.continuous.continuousOn.integrableOn_compact hK).bdd_mul (c := (ω / m) ^ 2) hmeas (Filter.Eventually.of_forall fun x => ?_)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hcx : 0 < c x := lt_of_lt_of_le hm (hmc x)
    rw [div_pow, div_pow]
    apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
    exact pow_le_pow_left₀ hm.le (hmc x) 2
  have : (fun x => helmholtzOp ω c u x + s x) =
      (fun x => Laplacian.laplacian u x + (((ω / c x) ^ 2 : ℝ) : ℂ) * u x) + s := by
    funext x; rfl
  rw [this]
  exact (h1.locallyIntegrable.add h2).add hs

end S76FE

open Arxiv2507_15035 S76FE in
theorem solution {n M : ℕ} (ω : ℝ) (hω : 0 < ω)
    (c : Pt n → ℝ) (ROI : Set (Pt n)) (c0 : ℝ) (hc : IsSoundSpeed c ROI c0)
    (s : Pt n → ℂ) (hs : LocallyIntegrable s) (xf : Fin M → Pt n) (y : Fin M → ℂ)
    (u : Pt n → ℂ) (hu : ContDiff ℝ 2 u) (lam : Pt n → ℂ)
    (hint : Integrable (fun x => (starRingEnd ℂ) (lam x) * (helmholtzOp ω c u x + s x))) :
    (∀ φ : Pt n → ℂ, IsTestFn φ →
      HasDerivAt (fun t : ℝ => lagrangianTerm ω c s xf y u (fun x => lam x + t • φ x)) 0 0) ↔
    ∀ᵐ x, helmholtzOp ω c u x = -s x := by
  obtain ⟨f, hf⟩ : ∃ f : Pt n → ℂ, f = fun x => helmholtzOp ω c u x + s x := ⟨_, rfl⟩
  have hfl : LocallyIntegrable f := by rw [hf]; exact f_loc ω c ROI c0 hc s hs u hu
  have hint' : Integrable (fun x => (starRingEnd ℂ) (lam x) * f x) := by rw [hf]; exact hint
  have hL : ∀ l : Pt n → ℂ, lagrangianTerm ω c s xf y u l =
      misfit xf y u - (∫ x, (starRingEnd ℂ) (l x) * f x).re := by
    intro l; unfold lagrangianTerm realPairing; rw [hf]
  have hform : ∀ φ : Pt n → ℂ, IsTestFn φ → ∀ t : ℝ,
      lagrangianTerm ω c s xf y u (fun x => lam x + t • φ x) =
        lagrangianTerm ω c s xf y u lam - t * (∫ x, (starRingEnd ℂ) (φ x) * f x).re := by
    intro φ hφ t
    have hφi : Integrable (fun x => (starRingEnd ℂ) (φ x) * f x) := by
      have := hfl.integrable_smul_left_of_hasCompactSupport (g := fun x => (starRingEnd ℂ) (φ x))
        (Complex.continuous_conj.comp hφ.1.continuous)
        (hφ.2.comp_left (map_zero _))
      simpa [smul_eq_mul] using this
    rw [hL, hL]
    have e : (fun x => (starRingEnd ℂ) (lam x + t • φ x) * f x) =
        fun x => (starRingEnd ℂ) (lam x) * f x + t • ((starRingEnd ℂ) (φ x) * f x) := by
      funext x; simp [Complex.real_smul, map_add]; ring
    rw [e, integral_add (f := fun x => (starRingEnd ℂ) (lam x) * f x)
      (g := fun x => t • ((starRingEnd ℂ) (φ x) * f x)) hint' (hφi.smul t), integral_smul, Complex.add_re, Complex.smul_re,
      smul_eq_mul]
    ring
  have hderiv : ∀ φ : Pt n → ℂ, IsTestFn φ →
      HasDerivAt (fun t : ℝ => lagrangianTerm ω c s xf y u (fun x => lam x + t • φ x))
        (-(∫ x, (starRingEnd ℂ) (φ x) * f x).re) 0 := by
    intro φ hφ
    have : (fun t : ℝ => lagrangianTerm ω c s xf y u (fun x => lam x + t • φ x)) =
        fun t => lagrangianTerm ω c s xf y u lam - t * (∫ x, (starRingEnd ℂ) (φ x) * f x).re := by
      funext t; exact hform φ hφ t
    rw [this]
    have := ((hasDerivAt_id (0:ℝ)).mul_const ((∫ x, (starRingEnd ℂ) (φ x) * f x).re)).const_sub
      (lagrangianTerm ω c s xf y u lam)
    simpa using this
  constructor
  · intro H
    have hre : ∀ φ : Pt n → ℂ, IsTestFn φ → (∫ x, (starRingEnd ℂ) (φ x) * f x).re = 0 := by
      intro φ hφ
      have := (hderiv φ hφ).unique (H φ hφ)
      linarith
    have hz := ae_eq_zero_of_integral_contDiff_smul_eq_zero hfl (fun g hg hgs => by
      have hc1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => ((g x : ℝ) : ℂ)) := by
        have := Complex.ofRealCLM.contDiff.comp hg
        have e : (⇑Complex.ofRealCLM ∘ g) = fun x => ((g x : ℝ) : ℂ) := by funext x; simp
        rwa [e] at this
      have hφ1 : IsTestFn (fun x => ((g x : ℝ) : ℂ)) := by
        refine ⟨hc1, ?_⟩
        exact hgs.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
      have hφ2 : IsTestFn (fun x => Complex.I * ((g x : ℝ) : ℂ)) := by
        refine ⟨contDiff_const.mul hc1, ?_⟩
        exact hgs.comp_left (g := fun r : ℝ => Complex.I * (r : ℂ)) (by simp)
      have r1 := hre _ hφ1
      have r2 := hre _ hφ2
      have e1 : (∫ x, (starRingEnd ℂ) ((g x : ℝ) : ℂ) * f x) = ∫ x, g x • f x := by
        congr 1; funext x; simp [Complex.real_smul]
      have e2 : (∫ x, (starRingEnd ℂ) (Complex.I * ((g x : ℝ) : ℂ)) * f x) =
          -Complex.I * ∫ x, g x • f x := by
        rw [← integral_const_mul]; congr 1; funext x; simp [Complex.real_smul]; ring
      rw [e1] at r1
      rw [e2] at r2
      apply Complex.ext
      · simpa using r1
      · simpa [Complex.mul_re] using r2)
    filter_upwards [hz] with x hx
    have : helmholtzOp ω c u x + s x = 0 := by rw [hf] at hx; exact hx
    linear_combination this
  · intro H φ hφ
    have h0 : (∫ x, (starRingEnd ℂ) (φ x) * f x) = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [H] with x hx
      simp [hf, hx]
    have := hderiv φ hφ
    rw [h0] at this
    simpa using this
