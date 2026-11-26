-- Prove2me | solution 1 for Arxiv2507_15035.adjoint_equation_iff_stationary_field
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T03:17:52.566829+00:00
-- url     : https://prove2.me/submissions/80bab2d4-465f-4e9d-95bb-d8a852760d32

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
  apply continuous_finset_sum; intro i _
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

open Arxiv2507_15035 S76AD in
theorem solution {n M : ℕ} (ω : ℝ) (hω : 0 < ω)
    (c : Pt n → ℝ) (ROI : Set (Pt n)) (c0 : ℝ) (hc : IsSoundSpeed c ROI c0)
    (s : Pt n → ℂ) (xf : Fin M → Pt n) (y : Fin M → ℂ)
    (u : Pt n → ℂ) (hu : ContDiff ℝ 2 u) (lam : Pt n → ℂ) (hlam : LocallyIntegrable lam)
    (hint : Integrable (fun x => (starRingEnd ℂ) (lam x) * (helmholtzOp ω c u x + s x))) :
    (∀ φ : Pt n → ℂ, IsTestFn φ →
      HasDerivAt (fun t : ℝ => lagrangianTerm ω c s xf y (fun x => u x + t • φ x) lam) 0 0) ↔
    IsWeakPointSourceSol ω c lam xf (fun i => 2 * (u (xf i) - y i)) := by
  obtain ⟨A, hA⟩ : ∃ A : (Pt n → ℂ) → ℂ, A = fun φ => ∫ x, (starRingEnd ℂ) (lam x) * helmholtzOp ω c φ x :=
    ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : (Pt n → ℂ) → ℂ, B = fun φ => ∑ i, 2 * (starRingEnd ℂ) (u (xf i) - y i) * φ (xf i) :=
    ⟨_, rfl⟩
  have hform : ∀ φ : Pt n → ℂ, IsTestFn φ → ∀ t : ℝ,
      lagrangianTerm ω c s xf y (fun x => u x + t • φ x) lam =
        lagrangianTerm ω c s xf y u lam + t * ((B φ).re - (A φ).re) +
          t ^ 2 * ∑ i, ‖φ (xf i)‖ ^ 2 := by
    intro φ hφ t
    have hSi := S_int ω c ROI c0 hc lam hlam φ hφ
    unfold lagrangianTerm realPairing
    rw [misfit_exp]
    have e : (fun x => (starRingEnd ℂ) (lam x) * (helmholtzOp ω c (fun x => u x + t • φ x) x + s x)) =
        fun x => (starRingEnd ℂ) (lam x) * (helmholtzOp ω c u x + s x) +
          (t : ℂ) * ((starRingEnd ℂ) (lam x) * helmholtzOp ω c φ x) := by
      funext x; rw [S_lin ω c u φ hu (two_le hφ.1)]; ring
    rw [e, integral_add hint (hSi.const_mul (t : ℂ)), integral_const_mul, Complex.add_re,
      Complex.re_ofReal_mul, hA, hB]
    ring
  have hderiv : ∀ φ : Pt n → ℂ, IsTestFn φ →
      HasDerivAt (fun t : ℝ => lagrangianTerm ω c s xf y (fun x => u x + t • φ x) lam)
        ((B φ).re - (A φ).re) 0 := by
    intro φ hφ
    have : (fun t : ℝ => lagrangianTerm ω c s xf y (fun x => u x + t • φ x) lam) =
        fun t => lagrangianTerm ω c s xf y u lam + t * ((B φ).re - (A φ).re) +
          t ^ 2 * ∑ i, ‖φ (xf i)‖ ^ 2 := by
      funext t; exact hform φ hφ t
    rw [this]
    have h1 := ((hasDerivAt_id (0:ℝ)).mul_const ((B φ).re - (A φ).re)).const_add
      (lagrangianTerm ω c s xf y u lam)
    have h2 := (hasDerivAt_pow 2 (0:ℝ)).mul_const (∑ i, ‖φ (xf i)‖ ^ 2)
    have e : (fun t : ℝ => lagrangianTerm ω c s xf y u lam + t * ((B φ).re - (A φ).re) +
          t ^ 2 * ∑ i, ‖φ (xf i)‖ ^ 2) =
        (fun x => lagrangianTerm ω c s xf y u lam + id x * ((B φ).re - (A φ).re)) +
          fun y => y ^ 2 * ∑ i, ‖φ (xf i)‖ ^ 2 := by
      funext t; simp only [Pi.add_apply, id]
    rw [e]
    exact (h1.add h2).congr_deriv (by simp)
  have hAI : ∀ φ, IsTestFn φ → A (fun x => Complex.I * φ x) = Complex.I * A φ := by
    intro φ hφ
    rw [hA]; simp only
    rw [← integral_const_mul]; congr 1; funext x
    rw [S_I ω c φ (two_le hφ.1)]; ring
  have hBI : ∀ φ, B (fun x => Complex.I * φ x) = Complex.I * B φ := by
    intro φ; rw [hB]; simp only; rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_; ring
  have hAc : ∀ φ : Pt n → ℂ, A (fun x => (starRingEnd ℂ) (φ x)) =
      (starRingEnd ℂ) (∫ x, lam x * helmholtzOp ω c φ x) := by
    intro φ; rw [hA]; simp only
    rw [← integral_conj]; congr 1; funext x
    rw [S_conj]; simp
  have hBc : ∀ φ : Pt n → ℂ, B (fun x => (starRingEnd ℂ) (φ x)) =
      (starRingEnd ℂ) (∑ i, 2 * (u (xf i) - y i) * φ (xf i)) := by
    intro φ; rw [hB]; simp only; rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_; simp only [map_mul, map_ofNat]
  have key : (∀ φ : Pt n → ℂ, IsTestFn φ → (B φ).re - (A φ).re = 0) ↔
      ∀ φ : Pt n → ℂ, IsTestFn φ → A φ = B φ := by
    constructor
    · intro H φ hφ
      have r1 := H φ hφ
      have r2 := H _ (test_I φ hφ)
      rw [hAI φ hφ, hBI φ] at r2
      simp at r2
      apply Complex.ext <;> linarith
    · intro H φ hφ; rw [H φ hφ]; ring
  have key2 : (∀ φ : Pt n → ℂ, IsTestFn φ → A φ = B φ) ↔
      ∀ φ : Pt n → ℂ, IsTestFn φ → ∫ x, lam x * helmholtzOp ω c φ x = ∑ i, 2 * (u (xf i) - y i) * φ (xf i) := by
    constructor
    · intro H φ hφ
      have := H _ (test_conj φ hφ)
      rw [hAc, hBc] at this
      exact (starRingEnd ℂ).injective this
    · intro H φ hφ
      have hφ' : φ = fun x => (starRingEnd ℂ) ((fun x => (starRingEnd ℂ) (φ x)) x) := by
        funext x; simp
      rw [hφ', hAc, hBc, H _ (test_conj φ hφ)]
  constructor
  · intro H
    refine ⟨hlam, ?_⟩
    apply key2.1
    apply key.1
    intro φ hφ
    exact (hderiv φ hφ).unique (H φ hφ)
  · rintro ⟨-, H⟩ φ hφ
    have h0 := key.2 (key2.2 H) φ hφ
    have := hderiv φ hφ
    rwa [h0] at this
