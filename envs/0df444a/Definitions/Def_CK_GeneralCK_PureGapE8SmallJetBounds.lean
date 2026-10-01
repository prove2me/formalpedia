-- Prove2me | Definitions.Def_CK_GeneralCK_PureGapE8SmallJetBounds
-- name    : CK_GeneralCK_PureGapE8SmallJetBounds
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T04:31:22.405572+00:00
-- url     : https://prove2.me/theorems/ed7680fb-768a-4a8b-a200-9896ab9af460
-- title:
--   Courtade–Kumar proof module `GeneralCK.PureGapE8SmallJetBounds` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PureGapE8SmallJetBounds` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PureGapE8SmallJetBounds` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PureGapE8SmallJetBounds (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PureGapE8SmallJetBounds.lean)

import Definitions.Def_CK_GeneralCK_PureGapE8RegularizedInverse
import Definitions.Def_CK_GeneralCK_Certificates_E8AdaptiveOriginOwnerBridge
import Definitions.Def_CK_GeneralCK_Certificates_E8OriginMixedKTransfer

-- ===== source module GeneralCK.PureGapE8SmallJetBounds =====
section

/-!
# Unconditional coarse local bounds for the regular E8 inverse jet

The completed complex-disc certificate and exact Taylor coefficient boxes
already imply these deliberately loose bounds.  No new numerical owner is
needed at the small argument occurring in the two axis strips.
-/

namespace GeneralCK

open Set Filter Certificates
open E8OriginAnalyticCertificate E8OriginPositiveConsumer
open E8OriginRealTaylorTransfer E8OriginMixedKTransfer E8OriginRemainder

theorem qReal_first_three_jets_abs_le_one (cert : QuantitativeCertificate)
    {y : ℝ} (hy : 0 ≤ y) (hyR : y ≤ 4 / 25) (j : ℕ) (hj : j ≤ 2) :
    |iteratedDeriv j (qReal cert) y| ≤ 1 := by
  have ht := qReal_derivative_taylor_tail_le_scaled cert j (by omega)
    hy (r := 2 / 25) (by linarith) (by norm_num) (by norm_num)
  have htri := norm_add_le
    (iteratedDeriv j (qReal cert) y - qRealTaylorDerivative cert j y)
    (qRealTaylorDerivative cert j y)
  rw [sub_add_cancel] at htri
  have hb0 : (tailError 0 : ℝ) * (2 / 25 : ℝ) ^ 17 + (p0c : ℝ) * (2 / 25) ≤ 1 := by
    norm_num [tailError, q17AbsBound, p0c, radius, coeffAbsUpper,
      a1, a3, a5, a7, a9, a11, a13, a15, Finset.sum_range_succ]
  have hb1 : (tailError 1 : ℝ) * (2 / 25 : ℝ) ^ 16 + (p1c : ℝ) ≤ 1 := by
    norm_num [tailError, q17AbsBound, p1c, radius, coeffAbsUpper,
      a1, a3, a5, a7, a9, a11, a13, a15, Finset.sum_range_succ]
  have hb2 : (tailError 2 : ℝ) * (2 / 25 : ℝ) ^ 15 + (p2c : ℝ) * (2 / 25) ≤ 1 := by
    norm_num [tailError, q17AbsBound, p2c, radius, coeffAbsUpper,
      a1, a3, a5, a7, a9, a11, a13, a15, Finset.sum_Icc_succ_top]
  rw [← Real.norm_eq_abs]
  interval_cases j
  · have hp := qRealTaylorDerivative_zero_le_p0c cert hy (r := 2 / 25)
      (by linarith) (by norm_num) (by norm_num [radius])
    exact htri.trans ((add_le_add ht hp).trans hb0)
  · have hp := qRealTaylorDerivative_one_le_p1c cert hy (r := 2 / 25)
      (by linarith) (by norm_num) (by norm_num [radius])
    exact htri.trans ((add_le_add ht hp).trans hb1)
  · have hp := qRealTaylorDerivative_two_le_p2c cert hy (r := 2 / 25)
      (by linarith) (by norm_num) (by norm_num [radius])
    exact htri.trans ((add_le_add ht hp).trans hb2)

theorem e8RegularQ_first_three_jets_abs_le_one {y : ℝ}
    (hy : y ∈ e8SlopeRange) (hyR : y < 4 / 25) (j : ℕ) (hj : j ≤ 2) :
    |iteratedDeriv j e8RegularQ y| ≤ 1 := by
  let cert := E8AdaptiveOriginOwnerBridge.quantitativeCertificate
  have hagree : RealAgreementOnOrigin cert :=
    E8TauDiscRealAgreement.realAgreementOnOrigin_of_globalDerivativeBound
      Generated.E8AdaptiveFamily.FullCertificate.global_derivative_bound
  have heq : e8RegularQ =ᶠ[nhds y] qReal cert := by
    filter_upwards [e8SlopeRange_mem_nhds hy, Iio_mem_nhds hyR] with z hz hzR
    rw [e8RegularQ_eq_e8Q (e8SlopeRange_subset_pos hz).le]
    exact (hagree z hz hzR.le).symm
  rw [heq.iteratedDeriv_eq j]
  exact qReal_first_three_jets_abs_le_one cert (e8SlopeRange_subset_pos hy).le hyR.le j hj

theorem e8RegularQ_small_jet_upper {y : ℝ} (hy : y ∈ e8SlopeRange)
    (hyR : y ≤ 1 / 50) :
    e8RegularQ y ≤ 1 ∧ deriv e8RegularQ y ≤ 1 ∧ deriv (deriv e8RegularQ) y ≤ 1 := by
  have hj (j : ℕ) (hj : j ≤ 2) : iteratedDeriv j e8RegularQ y ≤ 1 :=
    (le_abs_self _).trans (e8RegularQ_first_three_jets_abs_le_one hy (by linarith) j hj)
  exact ⟨by simpa using hj 0 (by omega),
    by simpa only [iteratedDeriv_one] using hj 1 (by omega),
    by simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using hj 2 (by omega)⟩

#print axioms qReal_first_three_jets_abs_le_one
#print axioms e8RegularQ_first_three_jets_abs_le_one
#print axioms e8RegularQ_small_jet_upper

end GeneralCK

end


