-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0118Certified__16_q00
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0118Certified__16_q00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T22:34:03.929991+00:00
-- url     : https://prove2.me/theorems/30301f3b-708b-4001-94b8-911b47590367
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0118Certified (+15 modules: GeneralCK.Certificates.E8TAxisProd0119Certified, GeneralCK.Certificates.E8TAxisProd0120Certified…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0118Certified (+15 modules: GeneralCK.Certificates.E8TAxisProd0119Certified, GeneralCK.Certificates.E8TAxisProd0120Certified, GeneralCK.Certificates.E8TAxisProd0121Certified, GeneralCK.Certificates.E8TAxisProd0122Certified, GeneralCK.Certificates.E8TAxisProd0123Certified, GeneralCK.Certificates.E8TAxisProd0124Certified, GeneralCK.Certificates.E8TAxisProd0125Certified, GeneralCK.Certificates.E8TAxisProd0126Certified, GeneralCK.Certificates.E8TAxisProd0127Certified, GeneralCK.Certificates.E8TAxisProd0128Certified, GeneralCK.Certificates.E8TAxisProd0129Certified, GeneralCK.Certificates.E8TAxisProd0130Certified, GeneralCK.Certificates.E8TAxisProd0131Certified, GeneralCK.Certificates.E8TAxisProd0132Certified, GeneralCK.Certificates.E8TAxisProd0133Certified) (piece 1 of 16)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0118Certified (+15 modules: GeneralCK.Certificates.E8TAxisProd0119Certified, GeneralCK.Certificates.E8TAxisProd0120Certified, GeneralCK.Certificates.E8TAxisProd0121Certified, GeneralCK.Certificates.E8TAxisProd0122Certified, GeneralCK.Certificates.E8TAxisProd0123Certified, GeneralCK.Certificates.E8TAxisProd0124Certified, GeneralCK.Certificates.E8TAxisProd0125Certified, GeneralCK.Certificates.E8TAxisProd0126Certified, GeneralCK.Certificates.E8TAxisProd0127Certified, GeneralCK.Certificates.E8TAxisProd0128Certified, GeneralCK.Certificates.E8TAxisProd0129Certified, GeneralCK.Certificates.E8TAxisProd0130Certified, GeneralCK.Certificates.E8TAxisProd0131Certified, GeneralCK.Certificates.E8TAxisProd0132Certified, GeneralCK.Certificates.E8TAxisProd0133Certified) (piece 1 of 16)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0118Certified (+15 modules: GeneralCK.Certificates.E8TAxisProd0119Certified, GeneralCK.Certificates.E8TAxisProd0120Certified, GeneralCK.Certificates.E8TAxisProd0121Certified, GeneralCK.Certificates.E8TAxisProd0122Certified, GeneralCK.Certificates.E8TAxisProd0123Certified, GeneralCK.Certificates.E8TAxisProd0124Certified, GeneralCK.Certificates.E8TAxisProd0125Certified, GeneralCK.Certificates.E8TAxisProd0126Certified, GeneralCK.Certificates.E8TAxisProd0127Certified, GeneralCK.Certificates.E8TAxisProd0128Certified, GeneralCK.Certificates.E8TAxisProd0129Certified, GeneralCK.Certificates.E8TAxisProd0130Certified, GeneralCK.Certificates.E8TAxisProd0131Certified, GeneralCK.Certificates.E8TAxisProd0132Certified, GeneralCK.Certificates.E8TAxisProd0133Certified) (piece 1 of 16) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0118Certified (+15 modules: GeneralCK/Certificates/E8TAxisProd0119Certified, GeneralCK/Certificates/E8TAxisProd0120Certified, GeneralCK/Certificates/E8TAxisProd0121Certified, GeneralCK/Certificates/E8TAxisProd0122Certified, GeneralCK/Certificates/E8TAxisProd0123Certified, GeneralCK/Certificates/E8TAxisProd0124Certified, GeneralCK/Certificates/E8TAxisProd0125Certified, GeneralCK/Certificates/E8TAxisProd0126Certified, GeneralCK/Certificates/E8TAxisProd0127Certified, GeneralCK/Certificates/E8TAxisProd0128Certified, GeneralCK/Certificates/E8TAxisProd0129Certified, GeneralCK/Certificates/E8TAxisProd0130Certified, GeneralCK/Certificates/E8TAxisProd0131Certified, GeneralCK/Certificates/E8TAxisProd0132Certified, GeneralCK/Certificates/E8TAxisProd0133Certified) (piece 1 of 16).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0103CertifiedArithmetic__19
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0118EndpointWitnesses
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisCellCertificateSchema
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0119EndpointWitnesses
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0120EndpointWitnesses
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0121EndpointWitnesses
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0122CertifiedArithmetic__18
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0122EndpointWitnesses
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0123EndpointWitnesses
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0124EndpointWitnesses
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0125EndpointWitnesses
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0126EndpointWitnesses
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0127EndpointWitnesses
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0128EndpointWitnesses
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0129EndpointWitnesses
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0130EndpointWitnesses
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0131EndpointWitnesses
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0132EndpointWitnesses
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0133EndpointWitnesses

-- ===== source module GeneralCK.Certificates.E8TAxisProd0118Certified =====
section

namespace GeneralCK.Certificates.E8TAxisProd0118Certified
open GeneralCK Set E8TAxisDeltaDirectionalJet E8TAxisMixedCoefficients
open E8TAxisGeneralCenteredTaylor E8TAxisPartitionKernel
open E8TAxisProd0118Geometry E8TAxisProd0118CertifiedArithmetic

theorem centerBoxes_contains : centerBoxes.ContainsAt centerS centerT := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0118EndpointWitnesses.centerA_covers
    have hh := E8TAxisProd0118GraphCenterA.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0118EndpointWitnesses.centerB_covers
    have hh := E8TAxisProd0118GraphCenterB.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0118EndpointWitnesses.centerC_covers
    have hh := E8TAxisProd0118GraphCenterC.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0118EndpointWitnesses.centerD_covers
    have hh := E8TAxisProd0118GraphCenterD.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh

theorem wholeBoxes_contains {s t : ℝ} (h : InCell s t) : wholeBoxes.ContainsAt s t := by
  rcases h with ⟨hsl, hsu, htl, htu⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0118EndpointWitnesses.wholeA_covers_slope
      (s := t) ⟨htl, htu⟩
    have hh := E8TAxisProd0118GraphWholeA.qJetBox_contains ha hpos
    rwa [hy] at hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0118EndpointWitnesses.wholeB_covers_slope
      (s := 2*s+t) ⟨by linarith, by linarith⟩
    have hh := E8TAxisProd0118GraphWholeB.qJetBox_contains ha hpos
    rwa [hy] at hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0118EndpointWitnesses.wholeC_covers_slope
      (s := s+t) ⟨by linarith, by linarith⟩
    have hh := E8TAxisProd0118GraphWholeC.qJetBox_contains ha hpos
    rwa [hy] at hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0118EndpointWitnesses.wholeD_covers_slope
      (s := s) ⟨hsl, hsu⟩
    have hh := E8TAxisProd0118GraphWholeD.qJetBox_contains ha hpos
    rwa [hy] at hh

noncomputable def certificate : E8TAxisCellCertificateSchema.Certificate precision :=
  ⟨rectangle, centerS, centerT, data⟩

theorem cellPositive : CellPositive rectangle := by
  apply E8TAxisCellCertificateSchema.Certificate.cellPositive certificate
  · simpa [certificate, rectangle, Rect.Covers, InCell] using center_mem
  · intro s t h
    have hi : InCell s t := by simpa [certificate, rectangle, Rect.Covers, InCell] using h
    rcases hi with ⟨hsl, hsu, htl, htu⟩
    obtain ⟨aa, _, haa, hya⟩ := E8TAxisProd0118EndpointWitnesses.wholeA_covers_slope
      (s := t) ⟨htl, htu⟩
    obtain ⟨ab, _, hab, hyb⟩ := E8TAxisProd0118EndpointWitnesses.wholeB_covers_slope
      (s := 2*s+t) ⟨by linarith, by linarith⟩
    obtain ⟨ac, _, hac, hyc⟩ := E8TAxisProd0118EndpointWitnesses.wholeC_covers_slope
      (s := s+t) ⟨by linarith, by linarith⟩
    obtain ⟨ad, _, had, hyd⟩ := E8TAxisProd0118EndpointWitnesses.wholeD_covers_slope
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
end GeneralCK.Certificates.E8TAxisProd0118Certified

end


