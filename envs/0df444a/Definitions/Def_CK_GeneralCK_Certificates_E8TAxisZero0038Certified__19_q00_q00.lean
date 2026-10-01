-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0038Certified__19_q00_q00
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0038Certified__19_q00_q00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T05:22:18.443593+00:00
-- url     : https://prove2.me/theorems/61f8a70e-79d7-4d8e-8c11-459a76c1ef56
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0038Certified (+18 modules: GeneralCK.Certificates.E8TAxisZero0039Certified, GeneralCK.Certificates.E8TAxisZero0040Certified…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0038Certified (+18 modules: GeneralCK.Certificates.E8TAxisZero0039Certified, GeneralCK.Certificates.E8TAxisZero0040Certified, GeneralCK.Certificates.E8TAxisZero0041Certified, GeneralCK.Certificates.E8TAxisZero0042Certified, GeneralCK.Certificates.E8TAxisZero0043Certified, GeneralCK.Certificates.E8TAxisZero0044Certified, GeneralCK.Certificates.E8TAxisZero0045Certified, GeneralCK.Certificates.E8TAxisZero0046Certified, GeneralCK.Certificates.E8TAxisZero0047Certified, GeneralCK.Certificates.E8TAxisZero0048Certified, GeneralCK.Certificates.E8TAxisZero0049Certified, GeneralCK.Certificates.E8TAxisZero0050Certified, GeneralCK.Certificates.E8TAxisZero0051Certified, GeneralCK.Certificates.E8TAxisZero0052Certified, GeneralCK.Certificates.E8TAxisZero0053Certified, GeneralCK.Certificates.E8TAxisZero0054Certified, GeneralCK.Certificates.E8TAxisZero0055Certified, GeneralCK.Certificates.E8TAxisZero0056Certified) (piece 1 of 19) (piece 1 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0038Certified (+18 modules: GeneralCK.Certificates.E8TAxisZero0039Certified, GeneralCK.Certificates.E8TAxisZero0040Certified, GeneralCK.Certificates.E8TAxisZero0041Certified, GeneralCK.Certificates.E8TAxisZero0042Certified, GeneralCK.Certificates.E8TAxisZero0043Certified, GeneralCK.Certificates.E8TAxisZero0044Certified, GeneralCK.Certificates.E8TAxisZero0045Certified, GeneralCK.Certificates.E8TAxisZero0046Certified, GeneralCK.Certificates.E8TAxisZero0047Certified, GeneralCK.Certificates.E8TAxisZero0048Certified, GeneralCK.Certificates.E8TAxisZero0049Certified, GeneralCK.Certificates.E8TAxisZero0050Certified, GeneralCK.Certificates.E8TAxisZero0051Certified, GeneralCK.Certificates.E8TAxisZero0052Certified, GeneralCK.Certificates.E8TAxisZero0053Certified, GeneralCK.Certificates.E8TAxisZero0054Certified, GeneralCK.Certificates.E8TAxisZero0055Certified, GeneralCK.Certificates.E8TAxisZero0056Certified) (piece 1 of 19) (piece 1 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0038Certified (+18 modules: GeneralCK.Certificates.E8TAxisZero0039Certified, GeneralCK.Certificates.E8TAxisZero0040Certified, GeneralCK.Certificates.E8TAxisZero0041Certified, GeneralCK.Certificates.E8TAxisZero0042Certified, GeneralCK.Certificates.E8TAxisZero0043Certified, GeneralCK.Certificates.E8TAxisZero0044Certified, GeneralCK.Certificates.E8TAxisZero0045Certified, GeneralCK.Certificates.E8TAxisZero0046Certified, GeneralCK.Certificates.E8TAxisZero0047Certified, GeneralCK.Certificates.E8TAxisZero0048Certified, GeneralCK.Certificates.E8TAxisZero0049Certified, GeneralCK.Certificates.E8TAxisZero0050Certified, GeneralCK.Certificates.E8TAxisZero0051Certified, GeneralCK.Certificates.E8TAxisZero0052Certified, GeneralCK.Certificates.E8TAxisZero0053Certified, GeneralCK.Certificates.E8TAxisZero0054Certified, GeneralCK.Certificates.E8TAxisZero0055Certified, GeneralCK.Certificates.E8TAxisZero0056Certified) (piece 1 of 19) (piece 1 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0038Certified (+18 modules: GeneralCK/Certificates/E8TAxisZero0039Certified, GeneralCK/Certificates/E8TAxisZero0040Certified, GeneralCK/Certificates/E8TAxisZero0041Certified, GeneralCK/Certificates/E8TAxisZero0042Certified, GeneralCK/Certificates/E8TAxisZero0043Certified, GeneralCK/Certificates/E8TAxisZero0044Certified, GeneralCK/Certificates/E8TAxisZero0045Certified, GeneralCK/Certificates/E8TAxisZero0046Certified, GeneralCK/Certificates/E8TAxisZero0047Certified, GeneralCK/Certificates/E8TAxisZero0048Certified, GeneralCK/Certificates/E8TAxisZero0049Certified, GeneralCK/Certificates/E8TAxisZero0050Certified, GeneralCK/Certificates/E8TAxisZero0051Certified, GeneralCK/Certificates/E8TAxisZero0052Certified, GeneralCK/Certificates/E8TAxisZero0053Certified, GeneralCK/Certificates/E8TAxisZero0054Certified, GeneralCK/Certificates/E8TAxisZero0055Certified, GeneralCK/Certificates/E8TAxisZero0056Certified) (piece 1 of 19) (piece 1 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0031CertifiedArithmetic__16
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0038EndpointWitnesses
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisRegularCellCertificateSchema
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0039EndpointWitnesses
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0040EndpointWitnesses
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0041EndpointWitnesses
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0042EndpointWitnesses
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0043EndpointWitnesses
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0044EndpointWitnesses
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0045EndpointWitnesses
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0046EndpointWitnesses
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0047CertifiedArithmetic__15
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0047EndpointWitnesses
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0048EndpointWitnesses
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0049EndpointWitnesses
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0050EndpointWitnesses
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0051EndpointWitnesses
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0052EndpointWitnesses
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0053EndpointWitnesses
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0054EndpointWitnesses
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0055EndpointWitnesses
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0056EndpointWitnesses



namespace GeneralCK.Certificates.E8TAxisZero0038Certified
open GeneralCK Set DyadicInterval E8TAxisMixedCoefficients E8TAxisPartitionKernel
open E8TAxisRegularGermJet E8TAxisRegularDirectionalJet
open E8TAxisZero0038Geometry E8TAxisZero0038CertifiedArithmetic

theorem centerBoxes_contains : centerBoxes.ContainsRegularAt centerS centerT := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply E8TAxisZero0038GraphCenterA.regular_contains
    norm_num [centerT]
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisZero0038EndpointWitnesses.centerB_covers
    have hh := E8TAxisZero0038GraphCenterB.qJetBox_contains ha hpos
    have hp : 0 < E8TAxisStableScalar.Y a := E8TAxisStableScalar.Y_pos hpos
    have hr := E8TAxisRegularGermJet.DyadicJet5Enclosure.Contains.regular_of_pos hh hp
    rw [hy] at hr
    exact hr
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisZero0038EndpointWitnesses.centerC_covers
    have hh := E8TAxisZero0038GraphCenterC.qJetBox_contains ha hpos
    have hp : 0 < E8TAxisStableScalar.Y a := E8TAxisStableScalar.Y_pos hpos
    have hr := E8TAxisRegularGermJet.DyadicJet5Enclosure.Contains.regular_of_pos hh hp
    rw [hy] at hr
    exact hr
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisZero0038EndpointWitnesses.centerD_covers
    have hh := E8TAxisZero0038GraphCenterD.qJetBox_contains ha hpos
    have hp : 0 < E8TAxisStableScalar.Y a := E8TAxisStableScalar.Y_pos hpos
    have hr := E8TAxisRegularGermJet.DyadicJet5Enclosure.Contains.regular_of_pos hh hp
    rw [hy] at hr
    exact hr

theorem wholeBoxes_contains {s t : ℝ} (h : InCell s t) :
    wholeBoxes.ContainsRegularAt s t := by
  rcases h with ⟨hsl, hsu, htl, htu⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply E8TAxisZero0038GraphWholeA.regular_contains
    simpa [tLower, tUpper] using (show t ∈ Icc tLower tUpper from ⟨htl, htu⟩)
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisZero0038EndpointWitnesses.wholeB_covers_slope
      (s := 2*s+t) ⟨by linarith, by linarith⟩
    have hh := E8TAxisZero0038GraphWholeB.qJetBox_contains ha hpos
    have hp : 0 < E8TAxisStableScalar.Y a := E8TAxisStableScalar.Y_pos hpos
    have hr := E8TAxisRegularGermJet.DyadicJet5Enclosure.Contains.regular_of_pos hh hp
    rwa [hy] at hr
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisZero0038EndpointWitnesses.wholeC_covers_slope
      (s := s+t) ⟨by linarith, by linarith⟩
    have hh := E8TAxisZero0038GraphWholeC.qJetBox_contains ha hpos
    have hp : 0 < E8TAxisStableScalar.Y a := E8TAxisStableScalar.Y_pos hpos
    have hr := E8TAxisRegularGermJet.DyadicJet5Enclosure.Contains.regular_of_pos hh hp
    rwa [hy] at hr
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisZero0038EndpointWitnesses.wholeD_covers_slope
      (s := s) ⟨by linarith, by linarith⟩
    have hh := E8TAxisZero0038GraphWholeD.qJetBox_contains ha hpos
    have hp : 0 < E8TAxisStableScalar.Y a := E8TAxisStableScalar.Y_pos hpos
    have hr := E8TAxisRegularGermJet.DyadicJet5Enclosure.Contains.regular_of_pos hh hp
    rwa [hy] at hr

end GeneralCK.Certificates.E8TAxisZero0038Certified


