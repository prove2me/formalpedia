-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0201Certified__20_q14
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0201Certified__20_q14
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T00:27:05.308256+00:00
-- url     : https://prove2.me/theorems/afb09b9d-74b0-409c-9d39-e9c34666dd8f
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0201Certified (+19 modules: GeneralCK.Certificates.E8TAxisProd0202Certified, GeneralCK.Certificates.E8TAxisProd0203Certified…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0201Certified (+19 modules: GeneralCK.Certificates.E8TAxisProd0202Certified, GeneralCK.Certificates.E8TAxisProd0203Certified, GeneralCK.Certificates.E8TAxisProd0204Certified, GeneralCK.Certificates.E8TAxisProd0205Certified, GeneralCK.Certificates.E8TAxisProd0206Certified, GeneralCK.Certificates.E8TAxisProd0207Certified, GeneralCK.Certificates.E8TAxisProd0208Certified, GeneralCK.Certificates.E8TAxisProd0209Certified, GeneralCK.Certificates.E8TAxisProd0210Certified, GeneralCK.Certificates.E8TAxisProd0211Certified, GeneralCK.Certificates.E8TAxisProd0212Certified, GeneralCK.Certificates.E8TAxisProd0213Certified, GeneralCK.Certificates.E8TAxisProd0214Certified, GeneralCK.Certificates.E8TAxisProd0215Certified, GeneralCK.Certificates.E8TAxisProd0216Certified, GeneralCK.Certificates.E8TAxisProd0217Certified, GeneralCK.Certificates.E8TAxisProd0218Certified, GeneralCK.Certificates.E8TAxisProd0219Certified, GeneralCK.Certificates.E8TAxisProd0220Certified) (piece 15 of 20)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0201Certified (+19 modules: GeneralCK.Certificates.E8TAxisProd0202Certified, GeneralCK.Certificates.E8TAxisProd0203Certified, GeneralCK.Certificates.E8TAxisProd0204Certified, GeneralCK.Certificates.E8TAxisProd0205Certified, GeneralCK.Certificates.E8TAxisProd0206Certified, GeneralCK.Certificates.E8TAxisProd0207Certified, GeneralCK.Certificates.E8TAxisProd0208Certified, GeneralCK.Certificates.E8TAxisProd0209Certified, GeneralCK.Certificates.E8TAxisProd0210Certified, GeneralCK.Certificates.E8TAxisProd0211Certified, GeneralCK.Certificates.E8TAxisProd0212Certified, GeneralCK.Certificates.E8TAxisProd0213Certified, GeneralCK.Certificates.E8TAxisProd0214Certified, GeneralCK.Certificates.E8TAxisProd0215Certified, GeneralCK.Certificates.E8TAxisProd0216Certified, GeneralCK.Certificates.E8TAxisProd0217Certified, GeneralCK.Certificates.E8TAxisProd0218Certified, GeneralCK.Certificates.E8TAxisProd0219Certified, GeneralCK.Certificates.E8TAxisProd0220Certified) (piece 15 of 20)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0201Certified (+19 modules: GeneralCK.Certificates.E8TAxisProd0202Certified, GeneralCK.Certificates.E8TAxisProd0203Certified, GeneralCK.Certificates.E8TAxisProd0204Certified, GeneralCK.Certificates.E8TAxisProd0205Certified, GeneralCK.Certificates.E8TAxisProd0206Certified, GeneralCK.Certificates.E8TAxisProd0207Certified, GeneralCK.Certificates.E8TAxisProd0208Certified, GeneralCK.Certificates.E8TAxisProd0209Certified, GeneralCK.Certificates.E8TAxisProd0210Certified, GeneralCK.Certificates.E8TAxisProd0211Certified, GeneralCK.Certificates.E8TAxisProd0212Certified, GeneralCK.Certificates.E8TAxisProd0213Certified, GeneralCK.Certificates.E8TAxisProd0214Certified, GeneralCK.Certificates.E8TAxisProd0215Certified, GeneralCK.Certificates.E8TAxisProd0216Certified, GeneralCK.Certificates.E8TAxisProd0217Certified, GeneralCK.Certificates.E8TAxisProd0218Certified, GeneralCK.Certificates.E8TAxisProd0219Certified, GeneralCK.Certificates.E8TAxisProd0220Certified) (piece 15 of 20) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0201Certified (+19 modules: GeneralCK/Certificates/E8TAxisProd0202Certified, GeneralCK/Certificates/E8TAxisProd0203Certified, GeneralCK/Certificates/E8TAxisProd0204Certified, GeneralCK/Certificates/E8TAxisProd0205Certified, GeneralCK/Certificates/E8TAxisProd0206Certified, GeneralCK/Certificates/E8TAxisProd0207Certified, GeneralCK/Certificates/E8TAxisProd0208Certified, GeneralCK/Certificates/E8TAxisProd0209Certified, GeneralCK/Certificates/E8TAxisProd0210Certified, GeneralCK/Certificates/E8TAxisProd0211Certified, GeneralCK/Certificates/E8TAxisProd0212Certified, GeneralCK/Certificates/E8TAxisProd0213Certified, GeneralCK/Certificates/E8TAxisProd0214Certified, GeneralCK/Certificates/E8TAxisProd0215Certified, GeneralCK/Certificates/E8TAxisProd0216Certified, GeneralCK/Certificates/E8TAxisProd0217Certified, GeneralCK/Certificates/E8TAxisProd0218Certified, GeneralCK/Certificates/E8TAxisProd0219Certified, GeneralCK/Certificates/E8TAxisProd0220Certified) (piece 15 of 20).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0201Certified__20_q14_q02

namespace GeneralCK.Certificates.E8TAxisProd0215Certified
open GeneralCK Set E8TAxisDeltaDirectionalJet E8TAxisMixedCoefficients
open E8TAxisGeneralCenteredTaylor E8TAxisPartitionKernel
open E8TAxisProd0215Geometry E8TAxisProd0215CertifiedArithmetic
theorem cellPositive : CellPositive rectangle := by
  apply E8TAxisCellCertificateSchema.Certificate.cellPositive certificate
  · simpa [certificate, rectangle, Rect.Covers, InCell] using center_mem
  · intro s t h
    have hi : InCell s t := by simpa [certificate, rectangle, Rect.Covers, InCell] using h
    rcases hi with ⟨hsl, hsu, htl, htu⟩
    obtain ⟨aa, _, haa, hya⟩ := E8TAxisProd0215EndpointWitnesses.wholeA_covers_slope
      (s := t) ⟨htl, htu⟩
    obtain ⟨ab, _, hab, hyb⟩ := E8TAxisProd0215EndpointWitnesses.wholeB_covers_slope
      (s := 2*s+t) ⟨by linarith, by linarith⟩
    obtain ⟨ac, _, hac, hyc⟩ := E8TAxisProd0215EndpointWitnesses.wholeC_covers_slope
      (s := s+t) ⟨by linarith, by linarith⟩
    obtain ⟨ad, _, had, hyd⟩ := E8TAxisProd0215EndpointWitnesses.wholeD_covers_slope
      (s := s) ⟨hsl, hsu⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [← hya]; exact ⟨E8TAxisStableScalar.X aa, E8TAxisStableScalar.X_pos haa,
        E8TAxisStableScalar.e8Theta_X haa⟩
    · rw [← hyb]; exact ⟨E8TAxisStableScalar.X ab, E8TAxisStableScalar.X_pos hab,
        E8TAxisStableScalar.e8Theta_X hab⟩
    · rw [← hyc]; exact ⟨E8TAxisStableScalar.X ac, E8TAxisStableScalar.X_pos hac,
        E8TAxisStableScalar.e8Theta_X hac⟩
    · rw [← hyd]; exact ⟨E8TAxisStableScalar.X ad, E8TAxisStableScalar.X_pos had,
        E8TAxisStableScalar.e8Theta_X had⟩
  · intro s t h
    exact (displacement_mem (by simpa [certificate, rectangle, Rect.Covers, InCell] using h)).1
  · intro s t h
    exact (displacement_mem (by simpa [certificate, rectangle, Rect.Covers, InCell] using h)).2
  · exact centerEnclosed_of_contains centerBoxes_contains
  · intro s t h
    apply wholeEnclosed_of_contains
    apply wholeBoxes_contains
    simpa [certificate, rectangle, Rect.Covers, InCell] using h
  · exact replay_positive

#print axioms centerBoxes_contains
#print axioms wholeBoxes_contains
#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisProd0215Certified


