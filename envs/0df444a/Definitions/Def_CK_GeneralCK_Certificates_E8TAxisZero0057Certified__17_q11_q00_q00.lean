-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0057Certified__17_q11_q00_q00
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0057Certified__17_q11_q00_q00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T20:09:53.074985+00:00
-- url     : https://prove2.me/theorems/3b2d9a25-4a0f-4b9f-8867-c9f48de5dae0
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0057Certified (+16 modules: GeneralCK.Certificates.E8TAxisZero0058Certified, GeneralCK.Certificates.E8TAxisZero0059Certified…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0057Certified (+16 modules: GeneralCK.Certificates.E8TAxisZero0058Certified, GeneralCK.Certificates.E8TAxisZero0059Certified, GeneralCK.Certificates.E8TAxisZero0060Certified, GeneralCK.Certificates.E8TAxisZero0061Certified, GeneralCK.Certificates.E8TAxisZero0062Certified, GeneralCK.Certificates.E8TAxisZero0063Certified, GeneralCK.Certificates.E8TAxisZero0064Certified, GeneralCK.Certificates.E8TAxisZero0065Certified, GeneralCK.Certificates.E8TAxisZero0066Certified, GeneralCK.Certificates.E8TAxisZero0067Certified, GeneralCK.Certificates.E8TAxisZero0068Certified, GeneralCK.Certificates.E8TAxisZero0069Certified, GeneralCK.Certificates.E8TAxisZero0070Certified, GeneralCK.Certificates.E8TAxisZero0071Certified, GeneralCK.Certificates.E8TAxisZero0072Certified, GeneralCK.Certificates.E8TAxisZero0073Certified) (piece 12 of 17) (piece 1 of 4) (piece 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0057Certified (+16 modules: GeneralCK.Certificates.E8TAxisZero0058Certified, GeneralCK.Certificates.E8TAxisZero0059Certified, GeneralCK.Certificates.E8TAxisZero0060Certified, GeneralCK.Certificates.E8TAxisZero0061Certified, GeneralCK.Certificates.E8TAxisZero0062Certified, GeneralCK.Certificates.E8TAxisZero0063Certified, GeneralCK.Certificates.E8TAxisZero0064Certified, GeneralCK.Certificates.E8TAxisZero0065Certified, GeneralCK.Certificates.E8TAxisZero0066Certified, GeneralCK.Certificates.E8TAxisZero0067Certified, GeneralCK.Certificates.E8TAxisZero0068Certified, GeneralCK.Certificates.E8TAxisZero0069Certified, GeneralCK.Certificates.E8TAxisZero0070Certified, GeneralCK.Certificates.E8TAxisZero0071Certified, GeneralCK.Certificates.E8TAxisZero0072Certified, GeneralCK.Certificates.E8TAxisZero0073Certified) (piece 12 of 17) (piece 1 of 4) (piece 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0057Certified (+16 modules: GeneralCK.Certificates.E8TAxisZero0058Certified, GeneralCK.Certificates.E8TAxisZero0059Certified, GeneralCK.Certificates.E8TAxisZero0060Certified, GeneralCK.Certificates.E8TAxisZero0061Certified, GeneralCK.Certificates.E8TAxisZero0062Certified, GeneralCK.Certificates.E8TAxisZero0063Certified, GeneralCK.Certificates.E8TAxisZero0064Certified, GeneralCK.Certificates.E8TAxisZero0065Certified, GeneralCK.Certificates.E8TAxisZero0066Certified, GeneralCK.Certificates.E8TAxisZero0067Certified, GeneralCK.Certificates.E8TAxisZero0068Certified, GeneralCK.Certificates.E8TAxisZero0069Certified, GeneralCK.Certificates.E8TAxisZero0070Certified, GeneralCK.Certificates.E8TAxisZero0071Certified, GeneralCK.Certificates.E8TAxisZero0072Certified, GeneralCK.Certificates.E8TAxisZero0073Certified) (piece 12 of 17) (piece 1 of 4) (piece 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0057Certified (+16 modules: GeneralCK/Certificates/E8TAxisZero0058Certified, GeneralCK/Certificates/E8TAxisZero0059Certified, GeneralCK/Certificates/E8TAxisZero0060Certified, GeneralCK/Certificates/E8TAxisZero0061Certified, GeneralCK/Certificates/E8TAxisZero0062Certified, GeneralCK/Certificates/E8TAxisZero0063Certified, GeneralCK/Certificates/E8TAxisZero0064Certified, GeneralCK/Certificates/E8TAxisZero0065Certified, GeneralCK/Certificates/E8TAxisZero0066Certified, GeneralCK/Certificates/E8TAxisZero0067Certified, GeneralCK/Certificates/E8TAxisZero0068Certified, GeneralCK/Certificates/E8TAxisZero0069Certified, GeneralCK/Certificates/E8TAxisZero0070Certified, GeneralCK/Certificates/E8TAxisZero0071Certified, GeneralCK/Certificates/E8TAxisZero0072Certified, GeneralCK/Certificates/E8TAxisZero0073Certified) (piece 12 of 17) (piece 1 of 4) (piece 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0057Certified__17_q10
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0062CertifiedArithmetic__17
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0068EndpointWitnesses
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisRegularCellCertificateSchema




namespace GeneralCK.Certificates.E8TAxisZero0068Certified
open GeneralCK Set DyadicInterval E8TAxisMixedCoefficients E8TAxisPartitionKernel
open E8TAxisRegularGermJet E8TAxisRegularDirectionalJet
open E8TAxisZero0068Geometry E8TAxisZero0068CertifiedArithmetic

theorem centerBoxes_contains : centerBoxes.ContainsRegularAt centerS centerT := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply E8TAxisZero0068GraphCenterA.regular_contains
    norm_num [centerT]
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisZero0068EndpointWitnesses.centerB_covers
    have hh := E8TAxisZero0068GraphCenterB.qJetBox_contains ha hpos
    have hp : 0 < E8TAxisStableScalar.Y a := E8TAxisStableScalar.Y_pos hpos
    have hr := E8TAxisRegularGermJet.DyadicJet5Enclosure.Contains.regular_of_pos hh hp
    rw [hy] at hr
    exact hr
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisZero0068EndpointWitnesses.centerC_covers
    have hh := E8TAxisZero0068GraphCenterC.qJetBox_contains ha hpos
    have hp : 0 < E8TAxisStableScalar.Y a := E8TAxisStableScalar.Y_pos hpos
    have hr := E8TAxisRegularGermJet.DyadicJet5Enclosure.Contains.regular_of_pos hh hp
    rw [hy] at hr
    exact hr
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisZero0068EndpointWitnesses.centerD_covers
    have hh := E8TAxisZero0068GraphCenterD.qJetBox_contains ha hpos
    have hp : 0 < E8TAxisStableScalar.Y a := E8TAxisStableScalar.Y_pos hpos
    have hr := E8TAxisRegularGermJet.DyadicJet5Enclosure.Contains.regular_of_pos hh hp
    rw [hy] at hr
    exact hr

end GeneralCK.Certificates.E8TAxisZero0068Certified


