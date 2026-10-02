-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0057Certified__17_q02_q00
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0057Certified__17_q02_q00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T16:45:53.794047+00:00
-- url     : https://prove2.me/theorems/1f14e19c-3438-40bd-8db9-65f7a1d4303f
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0057Certified (+16 modules: GeneralCK.Certificates.E8TAxisZero0058Certified, GeneralCK.Certificates.E8TAxisZero0059Certified…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0057Certified (+16 modules: GeneralCK.Certificates.E8TAxisZero0058Certified, GeneralCK.Certificates.E8TAxisZero0059Certified, GeneralCK.Certificates.E8TAxisZero0060Certified, GeneralCK.Certificates.E8TAxisZero0061Certified, GeneralCK.Certificates.E8TAxisZero0062Certified, GeneralCK.Certificates.E8TAxisZero0063Certified, GeneralCK.Certificates.E8TAxisZero0064Certified, GeneralCK.Certificates.E8TAxisZero0065Certified, GeneralCK.Certificates.E8TAxisZero0066Certified, GeneralCK.Certificates.E8TAxisZero0067Certified, GeneralCK.Certificates.E8TAxisZero0068Certified, GeneralCK.Certificates.E8TAxisZero0069Certified, GeneralCK.Certificates.E8TAxisZero0070Certified, GeneralCK.Certificates.E8TAxisZero0071Certified, GeneralCK.Certificates.E8TAxisZero0072Certified, GeneralCK.Certificates.E8TAxisZero0073Certified) (piece 3 of 17) (piece 1 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0057Certified (+16 modules: GeneralCK.Certificates.E8TAxisZero0058Certified, GeneralCK.Certificates.E8TAxisZero0059Certified, GeneralCK.Certificates.E8TAxisZero0060Certified, GeneralCK.Certificates.E8TAxisZero0061Certified, GeneralCK.Certificates.E8TAxisZero0062Certified, GeneralCK.Certificates.E8TAxisZero0063Certified, GeneralCK.Certificates.E8TAxisZero0064Certified, GeneralCK.Certificates.E8TAxisZero0065Certified, GeneralCK.Certificates.E8TAxisZero0066Certified, GeneralCK.Certificates.E8TAxisZero0067Certified, GeneralCK.Certificates.E8TAxisZero0068Certified, GeneralCK.Certificates.E8TAxisZero0069Certified, GeneralCK.Certificates.E8TAxisZero0070Certified, GeneralCK.Certificates.E8TAxisZero0071Certified, GeneralCK.Certificates.E8TAxisZero0072Certified, GeneralCK.Certificates.E8TAxisZero0073Certified) (piece 3 of 17) (piece 1 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0057Certified (+16 modules: GeneralCK.Certificates.E8TAxisZero0058Certified, GeneralCK.Certificates.E8TAxisZero0059Certified, GeneralCK.Certificates.E8TAxisZero0060Certified, GeneralCK.Certificates.E8TAxisZero0061Certified, GeneralCK.Certificates.E8TAxisZero0062Certified, GeneralCK.Certificates.E8TAxisZero0063Certified, GeneralCK.Certificates.E8TAxisZero0064Certified, GeneralCK.Certificates.E8TAxisZero0065Certified, GeneralCK.Certificates.E8TAxisZero0066Certified, GeneralCK.Certificates.E8TAxisZero0067Certified, GeneralCK.Certificates.E8TAxisZero0068Certified, GeneralCK.Certificates.E8TAxisZero0069Certified, GeneralCK.Certificates.E8TAxisZero0070Certified, GeneralCK.Certificates.E8TAxisZero0071Certified, GeneralCK.Certificates.E8TAxisZero0072Certified, GeneralCK.Certificates.E8TAxisZero0073Certified) (piece 3 of 17) (piece 1 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0057Certified (+16 modules: GeneralCK/Certificates/E8TAxisZero0058Certified, GeneralCK/Certificates/E8TAxisZero0059Certified, GeneralCK/Certificates/E8TAxisZero0060Certified, GeneralCK/Certificates/E8TAxisZero0061Certified, GeneralCK/Certificates/E8TAxisZero0062Certified, GeneralCK/Certificates/E8TAxisZero0063Certified, GeneralCK/Certificates/E8TAxisZero0064Certified, GeneralCK/Certificates/E8TAxisZero0065Certified, GeneralCK/Certificates/E8TAxisZero0066Certified, GeneralCK/Certificates/E8TAxisZero0067Certified, GeneralCK/Certificates/E8TAxisZero0068Certified, GeneralCK/Certificates/E8TAxisZero0069Certified, GeneralCK/Certificates/E8TAxisZero0070Certified, GeneralCK/Certificates/E8TAxisZero0071Certified, GeneralCK/Certificates/E8TAxisZero0072Certified, GeneralCK/Certificates/E8TAxisZero0073Certified) (piece 3 of 17) (piece 1 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0057Certified__17_q01
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0047CertifiedArithmetic__15
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0059EndpointWitnesses
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisRegularCellCertificateSchema



namespace GeneralCK.Certificates.E8TAxisZero0059Certified
open GeneralCK Set DyadicInterval E8TAxisMixedCoefficients E8TAxisPartitionKernel
open E8TAxisRegularGermJet E8TAxisRegularDirectionalJet
open E8TAxisZero0059Geometry E8TAxisZero0059CertifiedArithmetic

theorem centerBoxes_contains : centerBoxes.ContainsRegularAt centerS centerT := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply E8TAxisZero0059GraphCenterA.regular_contains
    norm_num [centerT]
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisZero0059EndpointWitnesses.centerB_covers
    have hh := E8TAxisZero0059GraphCenterB.qJetBox_contains ha hpos
    have hp : 0 < E8TAxisStableScalar.Y a := E8TAxisStableScalar.Y_pos hpos
    have hr := E8TAxisRegularGermJet.DyadicJet5Enclosure.Contains.regular_of_pos hh hp
    rw [hy] at hr
    exact hr
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisZero0059EndpointWitnesses.centerC_covers
    have hh := E8TAxisZero0059GraphCenterC.qJetBox_contains ha hpos
    have hp : 0 < E8TAxisStableScalar.Y a := E8TAxisStableScalar.Y_pos hpos
    have hr := E8TAxisRegularGermJet.DyadicJet5Enclosure.Contains.regular_of_pos hh hp
    rw [hy] at hr
    exact hr
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisZero0059EndpointWitnesses.centerD_covers
    have hh := E8TAxisZero0059GraphCenterD.qJetBox_contains ha hpos
    have hp : 0 < E8TAxisStableScalar.Y a := E8TAxisStableScalar.Y_pos hpos
    have hr := E8TAxisRegularGermJet.DyadicJet5Enclosure.Contains.regular_of_pos hh hp
    rw [hy] at hr
    exact hr

theorem wholeBoxes_contains {s t : ℝ} (h : InCell s t) :
    wholeBoxes.ContainsRegularAt s t := by
  rcases h with ⟨hsl, hsu, htl, htu⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply E8TAxisZero0059GraphWholeA.regular_contains
    simpa [tLower, tUpper] using (show t ∈ Icc tLower tUpper from ⟨htl, htu⟩)
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisZero0059EndpointWitnesses.wholeB_covers_slope
      (s := 2*s+t) ⟨by linarith, by linarith⟩
    have hh := E8TAxisZero0059GraphWholeB.qJetBox_contains ha hpos
    have hp : 0 < E8TAxisStableScalar.Y a := E8TAxisStableScalar.Y_pos hpos
    have hr := E8TAxisRegularGermJet.DyadicJet5Enclosure.Contains.regular_of_pos hh hp
    rwa [hy] at hr
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisZero0059EndpointWitnesses.wholeC_covers_slope
      (s := s+t) ⟨by linarith, by linarith⟩
    have hh := E8TAxisZero0059GraphWholeC.qJetBox_contains ha hpos
    have hp : 0 < E8TAxisStableScalar.Y a := E8TAxisStableScalar.Y_pos hpos
    have hr := E8TAxisRegularGermJet.DyadicJet5Enclosure.Contains.regular_of_pos hh hp
    rwa [hy] at hr
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisZero0059EndpointWitnesses.wholeD_covers_slope
      (s := s) ⟨by linarith, by linarith⟩
    have hh := E8TAxisZero0059GraphWholeD.qJetBox_contains ha hpos
    have hp : 0 < E8TAxisStableScalar.Y a := E8TAxisStableScalar.Y_pos hpos
    have hr := E8TAxisRegularGermJet.DyadicJet5Enclosure.Contains.regular_of_pos hh hp
    rwa [hy] at hr

end GeneralCK.Certificates.E8TAxisZero0059Certified


