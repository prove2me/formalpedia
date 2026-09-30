-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8OriginPositiveConsumer
-- name    : CK_GeneralCK_Certificates_E8OriginPositiveConsumer
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T20:00:40.90452+00:00
-- url     : https://prove2.me/theorems/27b78df6-dff7-489f-b85b-0dedaca454d2
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8OriginPositiveConsumer` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8OriginPositiveConsumer` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8OriginPositiveConsumer` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8OriginPositiveConsumer (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8OriginPositiveConsumer.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8OriginAnalyticCertificate

-- ===== source module GeneralCK.Certificates.E8OriginPositiveConsumer =====
section

/-!
# Handoff from the analytic origin branch to the E8 owner

This file isolates the last two mathematical statements made by the source
origin checker: real-axis identification of the quantitative branch and
positivity of its replayed degree-15 Taylor enclosure.  Once supplied, the
result is exactly the `E8PositiveOn` field used by the global case split.
-/

namespace GeneralCK.Certificates.E8OriginPositiveConsumer

open E8QuantitativeBranchBridge
open E8OriginAnalyticCertificate
open E8TauDiscCertificateOfContraction

noncomputable def qReal (cert : QuantitativeCertificate) (y : ℝ) : ℝ :=
  (qDisc cert.inverse (y : ℂ)).re

def RealAgreementOnOrigin (cert : QuantitativeCertificate) : Prop :=
  ∀ y : ℝ, y ∈ e8SlopeRange → y ≤ (4 / 25 : ℝ) → qReal cert y = e8Q y

def DiscOriginPositive (cert : QuantitativeCertificate) : Prop :=
  ∀ s t : ℝ, E8Admissible s t → s + t ≤ (2 / 25 : ℝ) →
    0 < e8Delta (qReal cert) s t

/-- The quantitative analytic certificate is now a direct consumer for the
origin owner.  The factor `4/25` is exactly the largest argument `2s+t`
appearing in `e8Delta` when `s+t ≤ 2/25`. -/
theorem e8PositiveOn_of_quantitativeCertificate
    (cert : QuantitativeCertificate)
    (hreal : RealAgreementOnOrigin cert)
    (hpositive : DiscOriginPositive cert) :
    E8PositiveOn fun s t => s + t ≤ (2 / 25 : ℝ) := by
  intro s t hadm hst
  have hs0 : 0 ≤ s := hadm.1.le
  have ht0 : 0 ≤ t := hadm.2.1.le
  have hs : s ≤ (4 / 25 : ℝ) := by linarith
  have ht : t ≤ (4 / 25 : ℝ) := by linarith
  have hsum0 : 0 ≤ s + t := by positivity
  have hsum : s + t ≤ (4 / 25 : ℝ) := by linarith
  have htwo0 : 0 ≤ 2 * s + t := by positivity
  have htwo : 2 * s + t ≤ (4 / 25 : ℝ) := by linarith
  have hp := hpositive s t hadm hst
  unfold e8Delta at hp ⊢
  rw [hreal s hadm.2.2.1 hs, hreal t hadm.2.2.2.1 ht,
    hreal (s + t) hadm.2.2.2.2.1 hsum,
    hreal (2 * s + t) hadm.2.2.2.2.2 htwo] at hp
  exact hp

def GlobalDerivativeBound : Prop :=
  ∀ tau : ℂ, ‖tau‖ ≤ (2 / 5 : ℝ) →
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ)

noncomputable def certificateOfGlobalDerivativeBound
    (hAggregate : GlobalDerivativeBound) : QuantitativeCertificate :=
  quantitativeCertificate_of_expr_bound hAggregate

/-- Final aggregate-facing origin interface.  The generated adaptive family
supplies `hAggregate`; the remaining arguments are precisely the real-axis
identification and the degree-15 origin polynomial replay for the resulting
quantitative branch. -/
theorem e8PositiveOn_of_globalDerivativeBound
    (hAggregate : GlobalDerivativeBound)
    (hreal : RealAgreementOnOrigin (certificateOfGlobalDerivativeBound hAggregate))
    (hpositive : DiscOriginPositive (certificateOfGlobalDerivativeBound hAggregate)) :
    E8PositiveOn fun s t => s + t ≤ (2 / 25 : ℝ) :=
  e8PositiveOn_of_quantitativeCertificate _ hreal hpositive

end GeneralCK.Certificates.E8OriginPositiveConsumer

end


