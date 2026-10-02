-- Prove2me | Definitions.Def_CK_GeneralCK_PureGapD0Origin
-- name    : CK_GeneralCK_PureGapD0Origin
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T10:15:36.73063+00:00
-- url     : https://prove2.me/theorems/71be3f7d-0549-4b95-bfaa-9636cceb83d8
-- title:
--   Courtade–Kumar proof module `GeneralCK.PureGapD0Origin` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PureGapD0Origin` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PureGapD0Origin` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PureGapD0Origin (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PureGapD0Origin.lean)

import Definitions.Def_CK_GeneralCK_PureGapHalfMeanAnalytic
import Definitions.Def_CK_GeneralCK_PureGapD0AxisPolynomial
import Definitions.Def_CK_GeneralCK_Certificates_E8AdaptiveOriginOwnerBridge

-- ===== source module GeneralCK.PureGapD0Origin =====
section

/-! The existing source-K certificate also proves the scalar D0 origin
interval. This module supplies the axis algebra and the two integrations. -/

namespace GeneralCK.PureGapD0Origin
open Set Filter
open scoped Topology
open Certificates E8OriginAnalyticCertificate E8OriginPositiveConsumer
open E8OriginMixedDerivativeConsumer E8OriginQRealRegularity
open E8OriginMixedKTransfer E8OriginRealTaylorTransfer E8OriginRemainder

noncomputable def first (Q : ℝ → ℝ) (q0 s : ℝ) : ℝ :=
  iteratedDeriv 2 Q s * Q (2 * s) +
    2 * iteratedDeriv 1 Q s * iteratedDeriv 1 Q (2 * s) -
    4 * q0 * iteratedDeriv 1 Q (2 * s) + 2 * q0 * iteratedDeriv 1 Q s

theorem hasDerivAt_D0 {Q : ℝ → ℝ} {q0 s : ℝ}
    (h1 : HasDerivAt Q (iteratedDeriv 1 Q s) s)
    (h2 : HasDerivAt (iteratedDeriv 1 Q) (iteratedDeriv 2 Q s) s)
    (h1two : HasDerivAt Q (iteratedDeriv 1 Q (2 * s)) (2 * s)) :
    HasDerivAt (e8D0 Q q0) (first Q q0 s) s := by
  have ht := h1two.comp s ((hasDerivAt_id s).const_mul 2)
  have hd := (h2.mul ht).sub ((ht.sub h1).const_mul (2 * q0))
  convert! hd using 1
  · funext x
    simp only [e8D0, iteratedDeriv_one, Function.comp_apply, Pi.sub_apply, Pi.mul_apply]
  · simp only [first, Function.comp_apply]
    ring

theorem hasDerivAt_first {Q : ℝ → ℝ} {q0 s : ℝ}
    (hzero : Q 0 = 0) (hfirst : iteratedDeriv 1 Q 0 = q0)
    (h2 : HasDerivAt (iteratedDeriv 1 Q) (iteratedDeriv 2 Q s) s)
    (h3 : HasDerivAt (iteratedDeriv 2 Q) (iteratedDeriv 3 Q s) s)
    (h1two : HasDerivAt Q (iteratedDeriv 1 Q (2 * s)) (2 * s))
    (h2two : HasDerivAt (iteratedDeriv 1 Q) (iteratedDeriv 2 Q (2 * s)) (2 * s)) :
    HasDerivAt (first Q q0) (mixedKFormula Q s 0) s := by
  have ht := h1two.comp s ((hasDerivAt_id s).const_mul 2)
  have ht2 := h2two.comp s ((hasDerivAt_id s).const_mul 2)
  have hd := ((((h3.mul ht).add ((h2.const_mul 2).mul ht2)).sub
    (ht2.const_mul (4 * q0))).add (h2.const_mul (2 * q0)))
  convert! hd using 1
  simp only [mixedKFormula, add_zero, hzero, hfirst, Function.comp_apply]
  ring

theorem deriv_qReal_zero (cert : QuantitativeCertificate) :
    iteratedDeriv 1 (qReal cert) 0 = pureGapQ0 := by
  rw [iteratedDeriv_qReal_zero_eq_qTaylorCoeff, E8AnalyticGerm.qTaylorCoeff_one]
  norm_num [pureGapQ0, Complex.div_re]
  exact Complex.log_ofReal_re 2

theorem mixedK_axis_pos (cert : QuantitativeCertificate) {s : ℝ}
    (hs : 0 < s) (hR : s ≤ (2 / 25 : ℝ)) :
    0 < mixedKFormula (qReal cert) s 0 := by
  have htransfer := mixedKFormula_sub_taylor_le_remainder cert hs.le (le_refl 0)
    (by simpa [radius] using hR)
  have hc := weighted_taylor_sub_sourceKFormula_le_coefficient cert hs.le (le_refl 0)
    (by simpa [radius] using hR)
  have hsource := PureGapD0AxisPolynomial.polynomial_lower hs.le hR
  have htail : (remainderOverRadiusCubed : ℝ) < ((13 / 1000000 : ℚ) : ℝ) :=
    Rat.cast_lt.mpr remainderOverRadiusCubed_lt
  norm_num at htail
  have hcoeff := coefficientCubicErrorFactor_lt
  rw [abs_le] at htransfer hc
  simp only [add_zero] at htransfer hc
  nlinarith [pow_pos hs 3]

theorem D0_qReal_pos (cert : QuantitativeCertificate) {s : ℝ}
    (hs : 0 < s) (hR : s ≤ (2 / 25 : ℝ)) :
    0 < e8D0 (qReal cert) pureGapQ0 s := by
  have hzero := qReal_zero cert
  have hfirst := deriv_qReal_zero cert
  have hlayers (x : ℝ) (hx : x ∈ Icc 0 s) :=
    qReal_three_derivative_layers cert (show |x| < E8QuantitativeBranchBridge.yOuterRadius by
      rw [abs_of_nonneg hx.1]
      exact (hx.2.trans hR).trans_lt (by norm_num [E8QuantitativeBranchBridge.yOuterRadius]))
  have htwo (x : ℝ) (hx : x ∈ Icc 0 s) :=
    qReal_three_derivative_layers cert (show |2 * x| < E8QuantitativeBranchBridge.yOuterRadius by
      rw [abs_of_nonneg (by linarith [hx.1])]
      have : 2 * x ≤ (4 / 25 : ℝ) := by linarith [hx.2]
      exact this.trans_lt (by norm_num [E8QuantitativeBranchBridge.yOuterRadius]))
  have hdfirst (x : ℝ) (hx : x ∈ Icc 0 s) :
      HasDerivAt (first (qReal cert) pureGapQ0) (mixedKFormula (qReal cert) x 0) x :=
    hasDerivAt_first hzero hfirst (hlayers x hx).2.1 (hlayers x hx).2.2
      (htwo x hx).1 (htwo x hx).2.1
  have hdfun (x : ℝ) (hx : x ∈ Icc 0 s) :
      HasDerivAt (e8D0 (qReal cert) pureGapQ0) (first (qReal cert) pureGapQ0 x) x :=
    hasDerivAt_D0 (hlayers x hx).1 (hlayers x hx).2.1 (htwo x hx).1
  have hmfirst : StrictMonoOn (first (qReal cert) pureGapQ0) (Icc 0 s) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 s)
    · intro x hx
      exact (hdfirst x hx).continuousAt.continuousWithinAt
    · intro x hx
      have hx' : 0 < x ∧ x < s := by simpa using hx
      rw [(hdfirst x ⟨hx'.1.le, hx'.2.le⟩).deriv]
      exact mixedK_axis_pos cert hx'.1 (hx'.2.le.trans hR)
  have hfirst0 : first (qReal cert) pureGapQ0 0 = 0 := by
    simp only [first, mul_zero, hzero, hfirst]
    ring
  have hm : StrictMonoOn (e8D0 (qReal cert) pureGapQ0) (Icc 0 s) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 s)
    · intro x hx
      exact (hdfun x hx).continuousAt.continuousWithinAt
    · intro x hx
      have hx' : 0 < x ∧ x < s := by simpa using hx
      rw [(hdfun x ⟨hx'.1.le, hx'.2.le⟩).deriv]
      have ht := hmfirst ⟨le_rfl, hs.le⟩ ⟨hx'.1.le, hx'.2.le⟩ hx'.1
      simpa only [hfirst0] using ht
  have ht := hm ⟨le_rfl, hs.le⟩ ⟨hs.le, le_rfl⟩ hs
  simpa only [e8D0, mul_zero, hzero, sub_self, sub_zero] using ht

/-- Concrete scalar positivity on precisely the range needed at a half-mean
stationary point in the origin interval. -/
theorem D0_e8Q_pos_on_origin {s : ℝ} (hs : 0 < s) (hR : s ≤ (2 / 25 : ℝ))
    (hsRange : s ∈ e8SlopeRange) (h2sRange : 2 * s ∈ e8SlopeRange) :
    0 < e8D0 e8Q pureGapQ0 s := by
  let cert := E8AdaptiveOriginOwnerBridge.quantitativeCertificate
  have hagree : RealAgreementOnOrigin cert :=
    E8TauDiscRealAgreement.realAgreementOnOrigin_of_globalDerivativeBound
      Generated.E8AdaptiveFamily.FullCertificate.global_derivative_bound
  have heq : qReal cert =ᶠ[nhds s] e8Q := by
    filter_upwards [e8SlopeRange_mem_nhds hsRange,
      Iio_mem_nhds (show s < (4 / 25 : ℝ) by linarith)] with x hx hxR
    exact hagree x hx hxR.le
  have hp := D0_qReal_pos cert hs hR
  rw [e8D0, heq.deriv_eq, hagree s hsRange (by linarith),
    hagree (2 * s) h2sRange (by linarith)] at hp
  exact hp

#print axioms D0_qReal_pos
#print axioms D0_e8Q_pos_on_origin

end GeneralCK.PureGapD0Origin

end


