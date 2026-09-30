-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisRegularSourceBounds
-- name    : CK_GeneralCK_Certificates_E8TAxisRegularSourceBounds
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T20:42:07.359+00:00
-- url     : https://prove2.me/theorems/b6011a39-3af2-4ef3-8067-c5f0639a14f2
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisRegularSourceBounds` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisRegularSourceBounds` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisRegularSourceBounds` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisRegularSourceBounds (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisRegularSourceBounds.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TauDiscRealAgreement
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisRegularGermJet
import Definitions.Def_CK_GeneralCK_Certificates_E8OriginRealTaylorTransfer

-- ===== source module GeneralCK.Certificates.E8TAxisRegularSourceBounds =====
section

/-!
# Source-polynomial bounds for the regular E8 endpoint jet

The quantitative inverse and the regular real inverse agree on full
neighborhoods, including at zero. This transfers ordinary derivatives and
the six regular jet components to the already proved source Taylor bounds.
-/

namespace GeneralCK.Certificates.E8TAxisRegularSourceBounds

open Set Filter Metric GeneralCK E8AnalyticGerm
open E8QuantitativeBranchBridge E8TauInverseContraction
open E8OriginAnalyticCertificate E8OriginPositiveConsumer
open E8TauDiscRealAgreement E8OriginRealTaylorTransfer E8OriginRemainder
open E8TAxisRegularGermJet

private abbrev tauDisc : Set ℂ := closedBall 0 tauRadius

theorem mem_slopeRange_below_anchor
    (hLip : LipschitzOnWith (1 : NNReal) thetaTauRemainder tauDisc)
    {y : ℝ} (hy : 0 < y) (hyUpper : y < 6 / 5) : y ∈ e8SlopeRange := by
  have hanchor : e8Theta (Real.log 2 / 5) ∈ e8SlopeRange :=
    ⟨Real.log 2 / 5, show 0 < Real.log 2 / 5 by positivity, rfl⟩
  exact e8SlopeRange_downward hanchor hy
    (hyUpper.le.trans (six_fifths_le_e8Theta_logTwo_div_five hLip))

theorem qReal_eventually_eq_regular_zero (cert : QuantitativeCertificate) :
    qReal cert =ᶠ[nhds (0 : ℝ)] e8RegularQ := by
  have h := qDisc_eventuallyEq_qGerm cert.inverse
  have hc : Tendsto (fun y : ℝ => (y : ℂ)) (nhds 0) (nhds 0) :=
    Complex.continuous_ofReal.continuousAt
  have hg : qReal cert =ᶠ[nhds (0 : ℝ)] (fun y => (qGerm (y : ℂ)).re) := by
    filter_upwards [hc.eventually h] with y hy
    exact congrArg Complex.re hy
  exact hg.trans e8RegularQ_eventually_eq_germ.symm

/-- Agreement is on a full neighborhood, not merely within the nonnegative
axis, so every ordinary iterated derivative transfers at zero as well. -/
theorem qReal_eventually_eq_regular
    (hLip : LipschitzOnWith (1 : NNReal) thetaTauRemainder tauDisc)
    {y : ℝ} (hy : 0 ≤ y) (hyUpper : y < 6 / 5) :
    qReal (quantitativeCertificateOfLipschitz hLip) =ᶠ[nhds y] e8RegularQ := by
  rcases hy.eq_or_lt with rfl | hy
  · exact qReal_eventually_eq_regular_zero _
  · filter_upwards [Ioi_mem_nhds hy, Iio_mem_nhds hyUpper] with z hz hzUpper
    rw [e8RegularQ_eq_e8Q hz.le]
    exact realAgreementBelowAnchor_of_lipschitz hLip z
      (mem_slopeRange_below_anchor hLip hz hzUpper) hzUpper

theorem qReal_eq_regular
    (hLip : LipschitzOnWith (1 : NNReal) thetaTauRemainder tauDisc)
    {y : ℝ} (hy : 0 ≤ y) (hyUpper : y < 6 / 5) :
    qReal (quantitativeCertificateOfLipschitz hLip) y = e8RegularQ y :=
  (qReal_eventually_eq_regular hLip hy hyUpper).eq_of_nhds

theorem iteratedDeriv_qReal_eq_regular
    (hLip : LipschitzOnWith (1 : NNReal) thetaTauRemainder tauDisc)
    (j : ℕ) {y : ℝ} (hy : 0 ≤ y) (hyUpper : y < 6 / 5) :
    iteratedDeriv j (qReal (quantitativeCertificateOfLipschitz hLip)) y =
      iteratedDeriv j e8RegularQ y :=
  Filter.EventuallyEq.iteratedDeriv_eq j
    (qReal_eventually_eq_regular hLip hy hyUpper)

/-- The actual regular inverse inherits the source bound at all points of
the closed interval, including both endpoints. -/
theorem regular_derivative_source_polynomial_le
    (hLip : LipschitzOnWith (1 : NNReal) thetaTauRemainder tauDisc)
    (j : ℕ) (hj : j ≤ 5) {y : ℝ} (hy : 0 ≤ y) (hyUpper : y ≤ 4 / 25) :
    ‖iteratedDeriv j e8RegularQ y - qSourceTaylorDerivative j y‖ ≤
      (q17AbsBound : ℝ) * y ^ (17 - j) / (17 - j).factorial +
        qSourceDerivativeError j y := by
  rw [← iteratedDeriv_qReal_eq_regular hLip j hy
    (hyUpper.trans_lt (by norm_num))]
  exact qReal_derivative_source_polynomial_le _ j hj hy hyUpper

/-- Index the six raw jet fields; all public derivative statements below
restrict the index to `j≤5`. -/
def component (jet : Jet5) : ℕ → ℝ → ℝ
  | 0 => jet.d0
  | 1 => jet.d1
  | 2 => jet.d2
  | 3 => jet.d3
  | 4 => jet.d4
  | _ => jet.d5

theorem component_hasDerivAt {jet : Jet5} {y : ℝ} (h : jet.SoundAt y)
    {j : ℕ} (hj : j < 5) :
    HasDerivAt (component jet j) (component jet (j + 1) y) y := by
  interval_cases j
  · exact h.1
  · exact h.2.1
  · exact h.2.2.1
  · exact h.2.2.2.1
  · exact h.2.2.2.2

theorem regular_component_eq_iteratedDeriv_of_mem (j : ℕ) (hj : j ≤ 5)
    {y : ℝ} (hy : y ∈ e8SlopeRange) :
    component regularQJet j y = iteratedDeriv j e8RegularQ y := by
  induction j generalizing y with
  | zero => exact regularQJet_d0_eq_regular y
  | succ j ih =>
      have heq : component regularQJet j =ᶠ[nhds y] iteratedDeriv j e8RegularQ := by
        filter_upwards [e8SlopeRange_mem_nhds hy] with z hz
        exact ih (by omega) hz
      calc
        component regularQJet (j + 1) y = deriv (component regularQJet j) y :=
          (component_hasDerivAt (regularQJet_soundAt_of_mem hy) (by omega)).deriv.symm
        _ = deriv (iteratedDeriv j e8RegularQ) y := heq.deriv_eq
        _ = iteratedDeriv (j + 1) e8RegularQ y := by rw [iteratedDeriv_succ]

theorem regular_component_zero_eq_qReal (cert : QuantitativeCertificate)
    (j : ℕ) (hj : j ≤ 5) :
    component regularQJet j 0 = iteratedDeriv j (qReal cert) 0 := by
  interval_cases j <;>
    simpa only [component, regularQJet, patchComponent, lt_self_iff_false, if_false,
      analyticComponent, Complex.ofReal_zero] using
      (iteratedDeriv_qReal_zero cert _).symm

theorem regular_component_eq_iteratedDeriv
    (hLip : LipschitzOnWith (1 : NNReal) thetaTauRemainder tauDisc)
    (j : ℕ) (hj : j ≤ 5) {y : ℝ} (hy : 0 ≤ y) (hyUpper : y < 6 / 5) :
    component regularQJet j y = iteratedDeriv j e8RegularQ y := by
  rcases hy.eq_or_lt with rfl | hy
  · exact (regular_component_zero_eq_qReal (quantitativeCertificateOfLipschitz hLip) j hj).trans
      (iteratedDeriv_qReal_eq_regular hLip j (le_refl 0) (by norm_num))
  · exact regular_component_eq_iteratedDeriv_of_mem j hj
      (mem_slopeRange_below_anchor hLip hy hyUpper)

/-- Concrete source-polynomial enclosure of each regular jet component on
`[0,4/25]`. No punctured-axis exception remains. -/
theorem regular_component_source_polynomial_le
    (hLip : LipschitzOnWith (1 : NNReal) thetaTauRemainder tauDisc)
    (j : ℕ) (hj : j ≤ 5) {y : ℝ} (hy : 0 ≤ y) (hyUpper : y ≤ 4 / 25) :
    ‖component regularQJet j y - qSourceTaylorDerivative j y‖ ≤
      (q17AbsBound : ℝ) * y ^ (17 - j) / (17 - j).factorial +
        qSourceDerivativeError j y := by
  rw [regular_component_eq_iteratedDeriv hLip j hj hy
    (hyUpper.trans_lt (by norm_num))]
  exact regular_derivative_source_polynomial_le hLip j hj hy hyUpper

end GeneralCK.Certificates.E8TAxisRegularSourceBounds

#print axioms GeneralCK.Certificates.E8TAxisRegularSourceBounds.qReal_eventually_eq_regular
#print axioms GeneralCK.Certificates.E8TAxisRegularSourceBounds.iteratedDeriv_qReal_eq_regular
#print axioms GeneralCK.Certificates.E8TAxisRegularSourceBounds.regular_derivative_source_polynomial_le
#print axioms GeneralCK.Certificates.E8TAxisRegularSourceBounds.regular_component_eq_iteratedDeriv
#print axioms GeneralCK.Certificates.E8TAxisRegularSourceBounds.regular_component_source_polynomial_le

end


