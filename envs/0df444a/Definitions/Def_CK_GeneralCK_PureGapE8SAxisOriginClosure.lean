-- Prove2me | Definitions.Def_CK_GeneralCK_PureGapE8SAxisOriginClosure
-- name    : CK_GeneralCK_PureGapE8SAxisOriginClosure
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T19:42:11.703787+00:00
-- url     : https://prove2.me/theorems/20d62b38-d869-44ed-8844-9f0acfd21097
-- title:
--   Courtade–Kumar proof module `GeneralCK.PureGapE8SAxisOriginClosure` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PureGapE8SAxisOriginClosure` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PureGapE8SAxisOriginClosure` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PureGapE8SAxisOriginClosure (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PureGapE8SAxisOriginClosure.lean)

import Definitions.Def_CK_GeneralCK_PureGapE8AxisConsumers
import Definitions.Def_CK_GeneralCK_Certificates_E8AdaptiveOriginOwnerBridge
import Definitions.Def_CK_GeneralCK_Certificates_E8OriginMixedKClosure

-- ===== source module GeneralCK.PureGapE8SAxisOriginClosure =====
section

/-!
# The unconditional origin portion of the s-axis derivative owner

The source-K certificate proves the second-s derivative itself positive on
the origin simplex.  The exact residual s-axis owner is therefore restricted
to the strict complement `2/25 < s+t`.
-/

namespace GeneralCK

open Set Filter Certificates
open E8OriginAnalyticCertificate E8OriginPositiveConsumer
open E8OriginMixedDerivativeConsumer E8OriginMixedKClosure

theorem deltaSS_pos_of_mixed_certificate {Q : ℝ → ℝ} {R s t : ℝ}
    (h : MixedDerivativeCertificate Q R) (hs : 0 ≤ s) (ht : 0 < t)
    (hR : s + t ≤ R) : 0 < deltaSS Q s t := by
  have hm : StrictMonoOn (fun v => deltaSS Q s v) (Icc 0 t) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 t)
    · intro v hv
      exact (h.hasDeriv_deltaSS s v hs hv.1 (by linarith [hv.2])).continuousAt.continuousWithinAt
    · intro v hv
      have hv' : v ∈ Ioo 0 t := by simpa using hv
      rw [(h.hasDeriv_deltaSS s v hs hv'.1.le (by linarith [hv'.2])).deriv]
      exact h.mixed_pos s v hs hv'.1 (by linarith [hv'.2])
  have hp := hm ⟨le_rfl, ht.le⟩ ⟨ht.le, le_rfl⟩ ht
  simpa only [h.deltaSS_zero_right s hs (by linarith)] using hp

theorem e8RegularDeltaSS_eq_quantitative_on_origin
    (cert : QuantitativeCertificate) (hagree : RealAgreementOnOrigin cert)
    {s t : ℝ} (hadm : E8Admissible s t) (hR : s + t ≤ 2 / 25) :
    e8RegularDeltaSS s t = deltaSS (qReal cert) s t := by
  have heq (x : ℝ) (hx : x ∈ e8SlopeRange) (hxR : x < 4 / 25) :
      e8RegularQ =ᶠ[nhds x] qReal cert := by
    filter_upwards [e8SlopeRange_mem_nhds hx, Iio_mem_nhds hxR] with z hz hzR
    rw [e8RegularQ_eq_e8Q (e8SlopeRange_subset_pos hz).le]
    exact (hagree z hz hzR.le).symm
  have hB : ∀ᶠ u in nhds s, e8RegularQ (2 * u + t) = qReal cert (2 * u + t) :=
    (heq _ hadm.2.2.2.2.2 (by linarith [hadm.2.1])).comp_tendsto
      ((continuous_const.mul continuous_id).add continuous_const).continuousAt
  have hC : ∀ᶠ u in nhds s, e8RegularQ (u + t) = qReal cert (u + t) :=
    (heq _ hadm.2.2.2.2.1 (by linarith)).comp_tendsto
      (continuous_id.add continuous_const).continuousAt
  have hD := heq s hadm.2.2.1 (by linarith [hadm.2.1])
  have hA : e8RegularQ t = qReal cert t :=
    (heq t hadm.2.2.2.1 (by linarith [hadm.1])).self_of_nhds
  have hdelta : (fun u => e8Delta e8RegularQ u t) =ᶠ[nhds s]
      (fun u => e8Delta (qReal cert) u t) := by
    filter_upwards [hB, hC, hD] with u huB huC huD
    simp only [e8Delta, huB, huC, huD, hA]
  simpa only [iteratedDeriv_succ, iteratedDeriv_zero,
    e8RegularDeltaSS, e8RegularDeltaS, deltaSS, deltaS] using hdelta.iteratedDeriv_eq 2

/-- Actual regular inverse, with the source-K transfer and complex-disc
certificate fully discharged. -/
theorem e8RegularDeltaSS_pos_on_origin {s t : ℝ}
    (hadm : E8Admissible s t) (hR : s + t ≤ 2 / 25) :
    0 < e8RegularDeltaSS s t := by
  let cert := E8AdaptiveOriginOwnerBridge.quantitativeCertificate
  have hagree : RealAgreementOnOrigin cert :=
    E8TauDiscRealAgreement.realAgreementOnOrigin_of_globalDerivativeBound
      Generated.E8AdaptiveFamily.FullCertificate.global_derivative_bound
  rw [e8RegularDeltaSS_eq_quantitative_on_origin cert hagree hadm hR]
  exact deltaSS_pos_of_mixed_certificate
    (mixedDerivativeCertificate_from_sourceK cert) hadm.1.le hadm.2.1 hR

def E8SAxisDerivativeRemainder : Prop :=
  ∀ s t : ℝ, E8Admissible s t → s ≤ 1 / 50 →
    3 / 50 ≤ t → t ≤ 20 → 2 / 25 < s + t → 0 < e8RegularDeltaSS s t

theorem e8_sAxis_derivative_of_remainder (h : E8SAxisDerivativeRemainder) :
    E8SAxisDerivativeBound := by
  intro s t hadm hs ht0 ht1
  by_cases hR : s + t ≤ 2 / 25
  · exact e8RegularDeltaSS_pos_on_origin hadm hR
  · exact h s t hadm hs ht0 ht1 (lt_of_not_ge hR)

theorem e8_sAxis_of_derivative_remainder (h : E8SAxisDerivativeRemainder) :
    E8PositiveOn (fun s t => s ≤ 1 / 50 ∧ 3 / 50 ≤ t ∧ t ≤ 20) :=
  e8_sAxis_of_derivative_bound (e8_sAxis_derivative_of_remainder h)

#print axioms deltaSS_pos_of_mixed_certificate
#print axioms e8RegularDeltaSS_eq_quantitative_on_origin
#print axioms e8RegularDeltaSS_pos_on_origin
#print axioms e8_sAxis_derivative_of_remainder
#print axioms e8_sAxis_of_derivative_remainder

end GeneralCK

end


