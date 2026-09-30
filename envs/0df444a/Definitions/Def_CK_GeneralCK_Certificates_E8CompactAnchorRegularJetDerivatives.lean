-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8CompactAnchorRegularJetDerivatives
-- name    : CK_GeneralCK_Certificates_E8CompactAnchorRegularJetDerivatives
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T18:39:32.827469+00:00
-- url     : https://prove2.me/theorems/c41b1273-15ec-4d4a-9c01-a396a9de6364
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8CompactAnchorRegularJetDerivatives` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8CompactAnchorRegularJetDerivatives` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8CompactAnchorRegularJetDerivatives` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8CompactAnchorRegularJetDerivatives (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8CompactAnchorRegularJetDerivatives.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8CompactAnchorDeltaJet

-- ===== source module GeneralCK.Certificates.E8CompactAnchorRegularJetDerivatives =====
section

/-!
# Canonical inverse jet as actual regular second and third derivatives

The compact pilot's interval boxes enclose the canonical inverse `qJet`.
On the open positive slope range, its raw second and third components
coincide with the corresponding derivatives of `e8RegularQ`.
-/

namespace GeneralCK.Certificates.E8CompactAnchorRegularJetDerivatives

open GeneralCK Filter E8TAxisDeltaDirectionalJet

theorem qJet_d1_eq_deriv_regular {y : ℝ}
    (hy : y ∈ e8SlopeRange) :
    qJet.d1 y = deriv e8RegularQ y := by
  simpa only [qPrimeJet, shift] using qPrimeJet_d0_eq_deriv_regular hy

theorem qJet_d2_eq_deriv2_regular {y : ℝ}
    (hy : y ∈ e8SlopeRange) :
    qJet.d2 y = deriv (deriv e8RegularQ) y := by
  have heq : qJet.d1 =ᶠ[nhds y] deriv e8RegularQ := by
    filter_upwards [e8SlopeRange_mem_nhds hy] with z hz
    exact qJet_d1_eq_deriv_regular hz
  have h := Filter.EventuallyEq.deriv_eq heq
  rw [(qJet_soundAt hy).2.1.deriv] at h
  exact h

theorem qJet_d3_eq_deriv3_regular {y : ℝ}
    (hy : y ∈ e8SlopeRange) :
    qJet.d3 y = deriv (deriv (deriv e8RegularQ)) y := by
  have heq : qJet.d2 =ᶠ[nhds y]
      (fun z => deriv (deriv e8RegularQ) z) := by
    filter_upwards [e8SlopeRange_mem_nhds hy] with z hz
    exact qJet_d2_eq_deriv2_regular hz
  have h := Filter.EventuallyEq.deriv_eq heq
  rw [(qJet_soundAt hy).2.2.1.deriv] at h
  exact h

#print axioms qJet_d1_eq_deriv_regular
#print axioms qJet_d2_eq_deriv2_regular
#print axioms qJet_d3_eq_deriv3_regular

end GeneralCK.Certificates.E8CompactAnchorRegularJetDerivatives

end


