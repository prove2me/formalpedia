-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8AnalyticTaylor17
-- name    : CK_GeneralCK_Certificates_E8AnalyticTaylor17
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T12:54:20.312338+00:00
-- url     : https://prove2.me/theorems/f416d455-1251-46ca-9640-942f2dcbad9f
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8AnalyticTaylor17` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8AnalyticTaylor17` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8AnalyticTaylor17` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8AnalyticTaylor17 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8AnalyticTaylor17.lean)

import Definitions.Def_CK_GeneralCK_PureGapE8AnalyticRealBridge
import Mathlib.Analysis.Analytic.Order

-- ===== source module GeneralCK.Certificates.E8AnalyticTaylor17 =====
section

/-!
# Degree-17 Taylor interface for the analytic E8 inverse germ

This module supplies the exact analytic statement consumed by an origin
certificate.  The coefficient convention is derivative divided by factorial,
exactly the convention of `E8InverseJet` and the source checker.
-/

namespace GeneralCK.Certificates.E8AnalyticTaylor17

open Set Filter Function
open E8AnalyticGerm
open E8InverseJet

/-- The exact degree-17 Taylor polynomial of the analytic inverse germ. -/
noncomputable def qPolynomial17 (z : ℂ) : ℂ :=
  ∑ i ∈ Finset.range 18, z ^ i * qTaylorCoeff i

/-- The source polynomial stops at degree 15; the degree-16 coefficient is
zero by oddness, so its analytic tail begins at degree 17. -/
noncomputable def qPolynomial15 (z : ℂ) : ℂ :=
  ∑ i ∈ Finset.range 16, z ^ i * qTaylorCoeff i

/-- A supplied coefficient table agrees with the concrete analytic jet. -/
def AgreesWithQJet17 (q : ℕ → ℂ) : Prop :=
  ∀ i ≤ 17, q i = qTaylorCoeff i

/-- Rational checker data agree with the analytic jet after the canonical
embedding into the complex numbers. -/
def RatAgreesWithQJet17 (q : ℕ → ℚ) : Prop :=
  AgreesWithQJet17 (fun i => (q i : ℂ))

/-- Coefficient agreement rewrites the concrete Taylor polynomial exactly. -/
theorem sum_eq_qPolynomial17 {q : ℕ → ℂ} (hq : AgreesWithQJet17 q)
    (z : ℂ) :
    (∑ i ∈ Finset.range 18, z ^ i * q i) = qPolynomial17 z := by
  apply Finset.sum_congr rfl
  intro i hi
  rw [hq i (Nat.le_pred_of_lt (Finset.mem_range.mp hi))]

/-- Exact degree-17 polynomial plus an analytic order-18 remainder.  The
identity is global because the remainder is zero-filled away from the local
analytic neighborhood; analyticity of the remainder is asserted at zero. -/
theorem exists_qGerm_degree17_remainder :
    ∃ r : ℂ → ℂ, AnalyticAt ℂ r 0 ∧ ∀ z,
      qGerm z = qPolynomial17 z + z ^ 18 * r z := by
  obtain ⟨r, hr, heq⟩ := analyticAt_qGerm.exists_eq_sum_add_pow_mul 18
  refine ⟨r, hr, fun z => ?_⟩
  rw [heq z]
  congr 1
  unfold qPolynomial17
  apply Finset.sum_congr rfl
  intro i hi
  unfold qTaylorCoeff
  simp only [smul_eq_mul]
  ring

theorem exists_qGerm_degree15_odd_remainder :
    ∃ r : ℂ → ℂ, AnalyticAt ℂ r 0 ∧ ∀ z,
      qGerm z = qPolynomial15 z + z ^ 17 * r z := by
  obtain ⟨r, hr, heq⟩ := analyticAt_qGerm.exists_eq_sum_add_pow_mul 17
  refine ⟨r, hr, fun z => ?_⟩
  rw [heq z]
  congr 1
  have hsum :
      (∑ i ∈ Finset.range 17,
          (z ^ i / i.factorial) • iteratedDeriv i qGerm 0) =
        ∑ i ∈ Finset.range 17, z ^ i * qTaylorCoeff i := by
    apply Finset.sum_congr rfl
    intro i hi
    unfold qTaylorCoeff
    simp only [smul_eq_mul]
    ring
  rw [hsum, Finset.sum_range_succ,
    qTaylorCoeff_eq_zero_of_even (show Even 16 by decide)]
  simp [qPolynomial15]

/-- Degree-15 interval form matching `cert_local_K.cpp`: coefficient errors
are explicit and the sole analytic tail begins with `z^17`. -/
theorem exists_degree15_odd_remainder_around (q : ℕ → ℂ) :
    ∃ r : ℂ → ℂ, AnalyticAt ℂ r 0 ∧ ∀ z,
      qGerm z =
        (∑ i ∈ Finset.range 16, z ^ i * q i) +
        (∑ i ∈ Finset.range 16, z ^ i * (qTaylorCoeff i - q i)) +
        z ^ 17 * r z := by
  obtain ⟨r, hr, heq⟩ := exists_qGerm_degree15_odd_remainder
  refine ⟨r, hr, fun z => ?_⟩
  rw [heq z]
  unfold qPolynomial15
  rw [← Finset.sum_add_distrib]
  apply congrArg (fun w : ℂ => w + z ^ 17 * r z)
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- Reusable certificate interface: any checked table identified with the
analytic coefficients gives the requested polynomial/remainder formula. -/
theorem exists_degree17_remainder_of_agreement {q : ℕ → ℂ}
    (hq : AgreesWithQJet17 q) :
    ∃ r : ℂ → ℂ, AnalyticAt ℂ r 0 ∧ ∀ z,
      qGerm z = (∑ i ∈ Finset.range 18, z ^ i * q i) + z ^ 18 * r z := by
  obtain ⟨r, hr, heq⟩ := exists_qGerm_degree17_remainder
  refine ⟨r, hr, fun z => ?_⟩
  rw [heq z, sum_eq_qPolynomial17 hq]

/-- The complete handoff from the executable order-17 convolution check and
coefficient identification to the concrete analytic polynomial/remainder.
The two premises deliberately separate formal inverse arithmetic from the
analytic coefficient-enclosure/identification obligation. -/
theorem inverseJetCheck_to_qGerm_remainder {theta q : ℕ → ℚ}
    (hcheck : inverseJetCheck 17 theta q = true)
    (hq : RatAgreesWithQJet17 q) :
    (∀ k ≤ 17, composeCoeff theta q k = targetCoeff k) ∧
      ∃ r : ℂ → ℂ, AnalyticAt ℂ r 0 ∧ ∀ z,
        qGerm z =
          (∑ i ∈ Finset.range 18, z ^ i * (q i : ℂ)) + z ^ 18 * r z := by
  constructor
  · intro k hk
    exact orderSeventeenCheck_sound hcheck hk
  · exact exists_degree17_remainder_of_agreement hq

/-- Interval-friendly version: an arbitrary supplied table contributes an
explicit coefficient-error polynomial, while the only analytic tail starts
at order 18.  This is directly usable when each true coefficient is enclosed
between checked rational endpoints rather than equal to a rational number. -/
theorem exists_degree17_remainder_around (q : ℕ → ℂ) :
    ∃ r : ℂ → ℂ, AnalyticAt ℂ r 0 ∧ ∀ z,
      qGerm z =
        (∑ i ∈ Finset.range 18, z ^ i * q i) +
        (∑ i ∈ Finset.range 18, z ^ i * (qTaylorCoeff i - q i)) +
        z ^ 18 * r z := by
  obtain ⟨r, hr, heq⟩ := exists_qGerm_degree17_remainder
  refine ⟨r, hr, fun z => ?_⟩
  rw [heq z]
  unfold qPolynomial17
  rw [← Finset.sum_add_distrib]
  apply congrArg (fun w : ℂ => w + z ^ 18 * r z)
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- Norm form of the interval-friendly handoff.  A coefficient enclosure can
replace each displayed coefficient norm by its checked rational upper bound;
only the final analytic multiplier still needs a uniform bound. -/
theorem exists_degree17_error_bound (q : ℕ → ℂ) :
    ∃ r : ℂ → ℂ, AnalyticAt ℂ r 0 ∧ ∀ z,
      ‖qGerm z - (∑ i ∈ Finset.range 18, z ^ i * q i)‖ ≤
        (∑ i ∈ Finset.range 18,
          ‖z‖ ^ i * ‖qTaylorCoeff i - q i‖) + ‖z‖ ^ 18 * ‖r z‖ := by
  obtain ⟨r, hr, heq⟩ := exists_degree17_remainder_around q
  refine ⟨r, hr, fun z => ?_⟩
  rw [heq z]
  have hrewrite :
      (∑ i ∈ Finset.range 18, z ^ i * q i) +
          (∑ i ∈ Finset.range 18, z ^ i * (qTaylorCoeff i - q i)) +
          z ^ 18 * r z -
          (∑ i ∈ Finset.range 18, z ^ i * q i) =
        (∑ i ∈ Finset.range 18, z ^ i * (qTaylorCoeff i - q i)) +
          z ^ 18 * r z := by ring
  rw [hrewrite]
  calc
    _ ≤ ‖∑ i ∈ Finset.range 18,
          z ^ i * (qTaylorCoeff i - q i)‖ + ‖z ^ 18 * r z‖ := norm_add_le _ _
    _ ≤ (∑ i ∈ Finset.range 18,
          ‖z ^ i * (qTaylorCoeff i - q i)‖) + ‖z ^ 18 * r z‖ := by
      gcongr
      exact norm_sum_le _ _
    _ = _ := by simp only [norm_mul, norm_pow]

/-- Oddness discharges every even coefficient entry through order 17 (and,
in fact, at every order). -/
theorem even_coefficients_zero {i : ℕ} (hi : Even i) :
    qTaylorCoeff i = 0 :=
  qTaylorCoeff_eq_zero_of_even hi

end GeneralCK.Certificates.E8AnalyticTaylor17

end


