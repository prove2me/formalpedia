-- Prove2me | solution 1 for Arxiv2001_06227.local_energy_balance
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T02:59:03.309579+00:00
-- url     : https://prove2.me/submissions/e3cf0643-6eb1-49c2-8d9e-51951839d9e0

import Mathlib
import Definitions.Def_Arxiv2001_06227_Basic

set_option autoImplicit false

open MeasureTheory Filter Topology

namespace S76LE
open Arxiv2001_06227

lemma pd_term (K : ℝ) (Es : Space → ℂ) (hEs : ContDiff ℝ 2 Es) (i : Fin 3) (x : Space) :
    pd (fun y => K * ((starRingEnd ℂ) (Es y) * pd Es i y).im) i x =
      K * ((starRingEnd ℂ) (Es x) * pd (pd Es i) i x).im := by
  have hE : HasFDerivAt Es (fderiv ℝ Es x) x :=
    ((hEs.differentiable (by norm_num)) x).hasFDerivAt
  have hPd : ContDiff ℝ 1 (pd Es i) := by
    unfold pd
    exact (hEs.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hP : HasFDerivAt (pd Es i) (fderiv ℝ (pd Es i) x) x :=
    ((hPd.differentiable (by norm_num)) x).hasFDerivAt
  have hS := (hE.star).mul hP
  have hI := ((Complex.imCLM.hasFDerivAt).comp x hS).const_mul K
  have hfun : (fun y => K * ((starRingEnd ℂ) (Es y) * pd Es i y).im) =
      (fun y => K * (⇑Complex.imCLM ∘ ((fun x => star (Es x)) * pd Es i)) y) := by
    funext y; simp [Complex.star_def]
  rw [hfun]
  show fderiv ℝ _ x (EuclideanSpace.single i 1) = _
  rw [hI.fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.add_apply, smul_eq_mul, Complex.imCLM_apply, ContinuousLinearEquiv.coe_coe, starL'_apply]
  have h0 : (pd Es i x * star (fderiv ℝ Es x (EuclideanSpace.single i 1))).im = 0 := by
    show (pd Es i x * star (pd Es i x)).im = 0
    rw [Complex.star_def, Complex.mul_conj]; simp
  rw [Complex.add_im, h0, add_zero, Complex.star_def]
  rfl

lemma sca_eq (mu0 omega : ℝ) (Es : Space → ℂ) (hEs : ContDiff ℝ 2 Es) (x : Space) :
    scaPower mu0 omega Es x =
      1 / (2 * mu0 * omega) * ((starRingEnd ℂ) (Es x) * lap Es x).im := by
  unfold scaPower div3 energyCurrent lap
  simp only [pd_term _ Es hEs]
  simp only [Finset.mul_sum, Complex.im_sum]

end S76LE

open Arxiv2001_06227 S76LE in
theorem solution (eps0 mu0 c omega : ℝ) (heps0 : 0 < eps0) (hmu0 : 0 < mu0)
    (hc : 0 < c) (homega : 0 < omega) (hvac : mu0 * eps0 * c ^ 2 = 1)
    (deps E0 Es : Space → ℂ) (hEs : ContDiff ℝ 2 Es)
    (hsca : IsScatteredField c omega deps E0 Es) (x : Space) :
    extPower (inducedCurrent eps0 omega deps (E0 + Es)) E0 x =
      absPower (inducedCurrent eps0 omega deps (E0 + Es)) (E0 + Es) x + scaPower mu0 omega Es x := by
  rw [sca_eq mu0 omega Es hEs x]
  have hD := hsca x
  obtain ⟨D, hDdef⟩ : ∃ D, D = deps x * (E0 x + Es x) := ⟨_, rfl⟩
  obtain ⟨k2, hk2⟩ : ∃ k2 : ℝ, k2 = (omega / c) ^ 2 := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = 1 / (2 * mu0 * omega) := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = omega * eps0 := ⟨_, rfl⟩
  have hrel : 2 * k2 * K = A := by
    rw [hk2, hK, hA]
    have : mu0 = 1 / (eps0 * c ^ 2) := by field_simp; linarith
    rw [this]; field_simp
  have hD' : lap Es x + (k2 : ℂ) * Es x = -((k2 : ℂ) * D) := by
    rw [hk2, hDdef, hD]; ring
  have hj : inducedCurrent eps0 omega deps (E0 + Es) x = -(Complex.I * (A : ℂ)) * D := by
    unfold inducedCurrent; rw [hA, hDdef]; simp only [Pi.add_apply]; push_cast; ring
  unfold extPower absPower
  rw [hj, ← hK]
  have hr := congrArg Complex.re hD'
  have hi := congrArg Complex.im hD'
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im,
    Complex.conj_re, Complex.conj_im, Pi.add_apply] at hr hi ⊢
  linear_combination K * ((Es x).im * hr - (Es x).re * hi) - ((Es x).im * D.re - (Es x).re * D.im) / 2 * hrel
