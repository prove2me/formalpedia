-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8OriginRealTaylorTransfer
-- name    : CK_GeneralCK_Certificates_E8OriginRealTaylorTransfer
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T20:31:40.369568+00:00
-- url     : https://prove2.me/theorems/b2b4e69b-4cdb-45ad-a2d8-cf6201afe2a5
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8OriginRealTaylorTransfer` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8OriginRealTaylorTransfer` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8OriginRealTaylorTransfer` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8OriginRealTaylorTransfer (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8OriginRealTaylorTransfer.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8OriginQRealRegularity
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Taylor

-- ===== source module GeneralCK.Certificates.E8OriginRealTaylorTransfer =====
section

/-! Transfer of the complex Cauchy data to the real inverse branch. -/

namespace GeneralCK.Certificates.E8OriginRealTaylorTransfer

open Metric Set Filter
open E8QuantitativeBranchBridge
open E8OriginAnalyticCertificate
open E8OriginPositiveConsumer
open E8OriginQRealRegularity
open E8OriginRemainder
open E8AnalyticGerm

theorem iteratedDeriv_qDisc_contDiffAt (cert : QuantitativeCertificate)
    (n : ℕ) {z : ℂ} (hz : z ∈ ball (0 : ℂ) yOuterRadius) :
    ContDiffAt ℂ ⊤ (iteratedDeriv n (qDisc cert.inverse)) z := by
  have hbase : ContDiffAt ℂ ⊤ (qDisc cert.inverse) z :=
    (((qDisc_diffCont cert.inverse).differentiableOn.contDiffOn isOpen_ball)
      z hz).contDiffAt (isOpen_ball.mem_nhds hz)
  induction n with
  | zero => simpa only [iteratedDeriv_zero]
  | succ n ih =>
      rw [iteratedDeriv_succ]
      exact ih.derivWithin (by simp)

/-- On the real axis, every real derivative is the real part of the
corresponding complex derivative. -/
theorem iteratedDeriv_qReal_eq_re (cert : QuantitativeCertificate) (n : ℕ)
    {y : ℝ} (hy : abs y < yOuterRadius) :
    iteratedDeriv n (qReal cert) y =
      (iteratedDeriv n (qDisc cert.inverse) (y : ℂ)).re := by
  induction n generalizing y with
  | zero => simp only [iteratedDeriv_zero, qReal]
  | succ n ih =>
      rw [iteratedDeriv_succ, iteratedDeriv_succ]
      have hy' : (y : ℂ) ∈ ball (0 : ℂ) yOuterRadius := by
        simpa [mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs] using hy
      have hc := iteratedDeriv_qDisc_contDiffAt cert n hy'
      have hcomplex : HasDerivAt (iteratedDeriv n (qDisc cert.inverse))
          (deriv (iteratedDeriv n (qDisc cert.inverse)) (y : ℂ)) (y : ℂ) :=
        (hc.differentiableAt (by simp)).hasDerivAt
      have hreal := hcomplex.real_of_complex
      have hopen : IsOpen {x : ℝ | abs x < yOuterRadius} :=
        isOpen_lt continuous_abs continuous_const
      have heq : (iteratedDeriv n (qReal cert)) =ᶠ[nhds y]
          (fun x : ℝ => (iteratedDeriv n (qDisc cert.inverse) (x : ℂ)).re) := by
        filter_upwards [hopen.mem_nhds hy] with x hx
        exact ih hx
      rw [heq.deriv_eq, hreal.deriv]

theorem iteratedDeriv_qReal_zero (cert : QuantitativeCertificate) (n : ℕ) :
    iteratedDeriv n (qReal cert) 0 = (iteratedDeriv n qGerm 0).re := by
  rw [iteratedDeriv_qReal_eq_re cert n (by norm_num [yOuterRadius])]
  have h := congrArg Complex.re (cert.coeffAgreement n)
  simpa using h

theorem iteratedDeriv_qReal_zero_eq_qTaylorCoeff
    (cert : QuantitativeCertificate) (n : ℕ) :
    iteratedDeriv n (qReal cert) 0 =
      (n.factorial : ℝ) * (qTaylorCoeff n).re := by
  rw [iteratedDeriv_qReal_zero]
  have hfac : (n.factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  have hc : iteratedDeriv n qGerm 0 =
      (n.factorial : ℂ) * qTaylorCoeff n := by
    unfold qTaylorCoeff
    field_simp
  have hr := congrArg Complex.re hc
  simpa using hr

/-- The complex order-17 Cauchy estimate is therefore exactly the real
order-17 estimate needed by one-variable Taylor's theorem. -/
theorem qReal_seventeenth_derivative_le (cert : QuantitativeCertificate) :
    ∀ y ∈ closedBall (0 : ℝ) (4 / 25 : ℝ),
      ‖iteratedDeriv 17 (qReal cert) y‖ ≤ (q17AbsBound : ℝ) := by
  intro y hy
  have hyAbs : abs y ≤ (4 / 25 : ℝ) := by
    simpa [mem_closedBall, dist_zero_right, Real.norm_eq_abs] using hy
  have hyOuter : abs y < yOuterRadius :=
    hyAbs.trans_lt (by norm_num [yOuterRadius])
  rw [iteratedDeriv_qReal_eq_re cert 17 hyOuter]
  calc
    ‖(iteratedDeriv 17 (qDisc cert.inverse) (y : ℂ)).re‖ ≤
        ‖iteratedDeriv 17 (qDisc cert.inverse) (y : ℂ)‖ :=
      Complex.abs_re_le_norm _
    _ ≤ (q17AbsBound : ℝ) := cert.tailBound (y : ℂ) (by
      simpa [mem_closedBall, dist_zero_right, Complex.norm_real,
        Real.norm_eq_abs] using hyAbs)

theorem iteratedDeriv_iteratedDeriv (f : ℝ → ℝ) (m n : ℕ) :
    iteratedDeriv m (iteratedDeriv n f) = iteratedDeriv (m + n) f := by
  rw [iteratedDeriv_eq_iterate, iteratedDeriv_eq_iterate,
    iteratedDeriv_eq_iterate]
  exact Function.iterate_add_apply deriv m n f |>.symm

theorem iteratedDeriv_qReal_contDiffAt (cert : QuantitativeCertificate)
    (n : ℕ) {y : ℝ} (hy : abs y < yOuterRadius) :
    ContDiffAt ℝ ⊤ (iteratedDeriv n (qReal cert)) y := by
  have hbase := qReal_contDiffAt cert hy
  induction n with
  | zero => simpa only [iteratedDeriv_zero]
  | succ n ih =>
      rw [iteratedDeriv_succ]
      exact ih.derivWithin (by simp)

/-- Lagrange remainder bound for each of the four derivatives used by the
mixed-derivative checker.  The factorial and exponent match the retained
`tailError` computation exactly. -/
theorem qReal_derivative_taylor_remainder_le (cert : QuantitativeCertificate)
    (j : ℕ) (hj : j ≤ 5) {y : ℝ} (hy0 : 0 ≤ y) (hyR : y ≤ 4 / 25) :
    ‖iteratedDeriv j (qReal cert) y -
        taylorWithinEval (iteratedDeriv j (qReal cert)) (16 - j)
          (uIcc 0 y) 0 y‖ ≤
      (q17AbsBound : ℝ) * y ^ (17 - j) / (17 - j).factorial := by
  by_cases hyZero : y = 0
  · subst y
    have hdegreePos : 0 < 17 - j := by omega
    simp [Nat.ne_of_gt hdegreePos]
  have hyPos : 0 < y := lt_of_le_of_ne hy0 (Ne.symm hyZero)
  have hcont : ContDiffOn ℝ ((16 - j) + 1)
      (iteratedDeriv j (qReal cert)) (uIcc 0 y) := by
    intro z hz
    refine ((iteratedDeriv_qReal_contDiffAt cert j ?_).of_le (by simp)).contDiffWithinAt
    rw [abs_of_nonneg (by simpa [uIcc, hyPos.le] using hz.1)]
    have hzR : z ≤ 4 / 25 := by
      have : z ≤ y := by simpa [uIcc, hyPos.le] using hz.2
      exact this.trans hyR
    exact hzR.trans_lt (by norm_num [yOuterRadius])
  obtain ⟨x, hx, hrem⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (f := iteratedDeriv j (qReal cert)) (n := 16 - j) (Ne.symm hyZero) hcont
  rw [hrem]
  have hxIcc : x ∈ closedBall (0 : ℝ) (4 / 25 : ℝ) := by
    have hx' : 0 < x ∧ x < y := by simpa [uIoo, hyPos.le] using hx
    simpa [mem_closedBall, dist_zero_right, Real.norm_eq_abs,
      abs_of_nonneg hx'.1.le] using hx'.2.le.trans hyR
  have htail := qReal_seventeenth_derivative_le cert x hxIcc
  have horder : (16 - j) + 1 + j = 17 := by omega
  have hdegree : (16 - j) + 1 = 17 - j := by omega
  rw [iteratedDeriv_iteratedDeriv, horder, hdegree]
  rw [norm_div, norm_mul, sub_zero, norm_pow]
  simp only [Real.norm_eq_abs, abs_of_nonneg hy0]
  have hfac : (0 : ℝ) ≤ ((17 - j).factorial : ℝ) := by positivity
  rw [abs_of_nonneg hfac]
  have htail' : |iteratedDeriv 17 (qReal cert) x| ≤ (q17AbsBound : ℝ) := by
    simpa only [Real.norm_eq_abs] using htail
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right htail' (pow_nonneg hy0 _)) hfac

noncomputable def qRealTaylorDerivative (cert : QuantitativeCertificate)
    (j : ℕ) (y : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (17 - j),
    ((k.factorial : ℝ)⁻¹ * y ^ k) *
      iteratedDeriv (k + j) (qReal cert) 0

noncomputable def qSourceTaylorDerivative (j : ℕ) (y : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (16 - j),
    ((k + j).factorial : ℝ) / k.factorial *
      (E8AnalyticCoefficientBoxes.sourceCenter (k + j) : ℝ) * y ^ k

noncomputable def qSourceDerivativeError (j : ℕ) (y : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (16 - j),
    ((k + j).factorial : ℝ) / k.factorial *
      (E8AnalyticCoefficientBoxes.sourceHalfWidth (k + j) : ℝ) * y ^ k

theorem qRealTaylorDerivative_eq_coefficients
    (cert : QuantitativeCertificate) (j : ℕ) (y : ℝ) :
    qRealTaylorDerivative cert j y =
      ∑ k ∈ Finset.range (17 - j),
        ((k + j).factorial : ℝ) / k.factorial *
          (qTaylorCoeff (k + j)).re * y ^ k := by
  unfold qRealTaylorDerivative
  apply Finset.sum_congr rfl
  intro k hk
  rw [iteratedDeriv_qReal_zero_eq_qTaylorCoeff]
  have hkfac : (k.factorial : ℝ) ≠ 0 := by positivity
  field_simp

theorem qRealTaylorDerivative_eq_coefficients15
    (cert : QuantitativeCertificate) (j : ℕ) (hj : j ≤ 5) (y : ℝ) :
    qRealTaylorDerivative cert j y =
      ∑ k ∈ Finset.range (16 - j),
        ((k + j).factorial : ℝ) / k.factorial *
          (qTaylorCoeff (k + j)).re * y ^ k := by
  rw [qRealTaylorDerivative_eq_coefficients]
  have hdegree : 17 - j = (16 - j) + 1 := by omega
  rw [hdegree, Finset.sum_range_succ]
  have hindex : 16 - j + j = 16 := by omega
  rw [hindex, qTaylorCoeff_eq_zero_of_even (show Even 16 by decide)]
  simp

theorem qTaylorCoeff_re_sourceCenter_le {n : ℕ} (hn : n < 16) :
    |(qTaylorCoeff n).re -
        (E8AnalyticCoefficientBoxes.sourceCenter n : ℝ)| ≤
      (E8AnalyticCoefficientBoxes.sourceHalfWidth n : ℝ) := by
  have hbox := E8AnalyticCoefficientBoxes.all_coefficients_enclosed
    E8QCoeff15.oddQCoefficientsInSourceBoxes hn
  have hre := Complex.abs_re_le_norm
    (qTaylorCoeff n -
      (E8AnalyticCoefficientBoxes.sourceCenter n : ℂ))
  exact hre.trans (by simpa using hbox)

/-- The unconditional q3--q15 source boxes control the finite Taylor
polynomial of every derivative used by the mixed checker. -/
theorem qRealTaylorDerivative_sub_source_le
    (cert : QuantitativeCertificate) (j : ℕ) (hj : j ≤ 5)
    {y : ℝ} (hy : 0 ≤ y) :
    ‖qRealTaylorDerivative cert j y - qSourceTaylorDerivative j y‖ ≤
      qSourceDerivativeError j y := by
  rw [qRealTaylorDerivative_eq_coefficients15 cert j hj]
  unfold qSourceTaylorDerivative qSourceDerivativeError
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ k ∈ Finset.range (16 - j),
        ‖((k + j).factorial : ℝ) / k.factorial *
            (qTaylorCoeff (k + j)).re * y ^ k -
          ((k + j).factorial : ℝ) / k.factorial *
            (E8AnalyticCoefficientBoxes.sourceCenter (k + j) : ℝ) * y ^ k‖ :=
      norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range (16 - j),
        ((k + j).factorial : ℝ) / k.factorial *
          (E8AnalyticCoefficientBoxes.sourceHalfWidth (k + j) : ℝ) * y ^ k := by
      gcongr with k hk
      have hk' := Finset.mem_range.mp hk
      have hn : k + j < 16 := by omega
      have hfac : 0 ≤ ((k + j).factorial : ℝ) / k.factorial := by positivity
      have hpow : 0 ≤ y ^ k := pow_nonneg hy _
      have heq :
          ((k + j).factorial : ℝ) / k.factorial *
                (qTaylorCoeff (k + j)).re * y ^ k -
              ((k + j).factorial : ℝ) / k.factorial *
                (E8AnalyticCoefficientBoxes.sourceCenter (k + j) : ℝ) * y ^ k =
            ((k + j).factorial : ℝ) / k.factorial *
              ((qTaylorCoeff (k + j)).re -
                (E8AnalyticCoefficientBoxes.sourceCenter (k + j) : ℝ)) * y ^ k := by
        ring
      rw [heq, norm_mul, norm_mul]
      simp only [Real.norm_eq_abs, abs_of_nonneg hfac, norm_pow,
        abs_of_nonneg hy]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (qTaylorCoeff_re_sourceCenter_le hn) hpow)
        hfac

theorem taylorWithinEval_qReal_eq (cert : QuantitativeCertificate)
    (j : ℕ) (hj : j ≤ 5) {y : ℝ} (hy : 0 < y) :
    taylorWithinEval (iteratedDeriv j (qReal cert)) (16 - j)
        (uIcc 0 y) 0 y = qRealTaylorDerivative cert j y := by
  rw [taylor_within_apply]
  have hdegree : 16 - j + 1 = 17 - j := by omega
  rw [hdegree]
  apply Finset.sum_congr rfl
  intro k hk
  have hzeroMem : (0 : ℝ) ∈ uIcc 0 y := by simp [uIcc, hy.le]
  have hcd := iteratedDeriv_qReal_contDiffAt cert j
    (show abs (0 : ℝ) < yOuterRadius by norm_num [yOuterRadius])
  rw [iteratedDerivWithin_eq_iteratedDeriv
    (uniqueDiffOn_uIcc (Ne.symm hy.ne')) (hcd.of_le (by simp)) hzeroMem]
  rw [congrFun (iteratedDeriv_iteratedDeriv (qReal cert) k j) 0]
  simp only [sub_zero, smul_eq_mul]

theorem qReal_derivative_exact_polynomial_remainder_le
    (cert : QuantitativeCertificate) (j : ℕ) (hj : j ≤ 5)
    {y : ℝ} (hy0 : 0 ≤ y) (hyR : y ≤ 4 / 25) :
    ‖iteratedDeriv j (qReal cert) y - qRealTaylorDerivative cert j y‖ ≤
      (q17AbsBound : ℝ) * y ^ (17 - j) / (17 - j).factorial := by
  by_cases hyZero : y = 0
  · subst y
    have hdegreePos : 0 < 17 - j := by omega
    rw [zero_pow (Nat.ne_of_gt hdegreePos), mul_zero, zero_div,
      norm_le_zero_iff]
    unfold qRealTaylorDerivative
    rw [Finset.sum_eq_single 0]
    · simp
    · intro k hk hk0
      simp [hk0]
    · simp
      omega
  rw [← taylorWithinEval_qReal_eq cert j hj (lt_of_le_of_ne hy0 (Ne.symm hyZero))]
  exact qReal_derivative_taylor_remainder_le cert j hj hy0 hyR

theorem qReal_derivative_source_polynomial_le
    (cert : QuantitativeCertificate) (j : ℕ) (hj : j ≤ 5)
    {y : ℝ} (hy0 : 0 ≤ y) (hyR : y ≤ 4 / 25) :
    ‖iteratedDeriv j (qReal cert) y - qSourceTaylorDerivative j y‖ ≤
      (q17AbsBound : ℝ) * y ^ (17 - j) / (17 - j).factorial +
        qSourceDerivativeError j y := by
  have hsplit :
      iteratedDeriv j (qReal cert) y - qSourceTaylorDerivative j y =
        (iteratedDeriv j (qReal cert) y - qRealTaylorDerivative cert j y) +
          (qRealTaylorDerivative cert j y - qSourceTaylorDerivative j y) := by
    ring
  rw [hsplit]
  exact (norm_add_le _ _).trans (add_le_add
    (qReal_derivative_exact_polynomial_remainder_le cert j hj hy0 hyR)
    (qRealTaylorDerivative_sub_source_le cert j hj hy0))

end GeneralCK.Certificates.E8OriginRealTaylorTransfer

end


