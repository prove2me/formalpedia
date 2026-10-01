-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0579Certified__25_q00_q00
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0579Certified__25_q00_q00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T21:10:04.720334+00:00
-- url     : https://prove2.me/theorems/0d92dc54-15d2-4ce4-a516-7cc73a0c86e4
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0579Certified (+24 modules: GeneralCK.Certificates.E8TAxisProd0580Certified, GeneralCK.Certificates.E8TAxisProd0581Certified…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0579Certified (+24 modules: GeneralCK.Certificates.E8TAxisProd0580Certified, GeneralCK.Certificates.E8TAxisProd0581Certified, GeneralCK.Certificates.E8TAxisProd0582Certified, GeneralCK.Certificates.E8TAxisProd0583Certified, GeneralCK.Certificates.E8TAxisProd0584Certified, GeneralCK.Certificates.E8TAxisProd0585Certified, GeneralCK.Certificates.E8TAxisProd0586Certified, GeneralCK.Certificates.E8TAxisProd0587Certified, GeneralCK.Certificates.E8TAxisProd0588Certified, GeneralCK.Certificates.E8TAxisProd0589Certified, GeneralCK.Certificates.E8TAxisProd0590Certified, GeneralCK.Certificates.E8TAxisProd0591Certified, GeneralCK.Certificates.E8TAxisProd0592Certified, GeneralCK.Certificates.E8TAxisProd0593Certified, GeneralCK.Certificates.E8TAxisProd0594Certified, GeneralCK.Certificates.E8TAxisProd0595Certified, GeneralCK.Certificates.E8TAxisProd0596Certified, GeneralCK.Certificates.E8TAxisProd0597Certified, GeneralCK.Certificates.E8TAxisProd0598Certified, GeneralCK.Certificates.E8TAxisProd0599Certified, GeneralCK.Certificates.E8TAxisProd0600Certified, GeneralCK.Certificates.E8TAxisProd0601Certified, GeneralCK.Certificates.E8TAxisProd0602Certified, GeneralCK.Certificates.E8TAxisProd0603Certified) (piece 1 of 25) (piece 1 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0579Certified (+24 modules: GeneralCK.Certificates.E8TAxisProd0580Certified, GeneralCK.Certificates.E8TAxisProd0581Certified, GeneralCK.Certificates.E8TAxisProd0582Certified, GeneralCK.Certificates.E8TAxisProd0583Certified, GeneralCK.Certificates.E8TAxisProd0584Certified, GeneralCK.Certificates.E8TAxisProd0585Certified, GeneralCK.Certificates.E8TAxisProd0586Certified, GeneralCK.Certificates.E8TAxisProd0587Certified, GeneralCK.Certificates.E8TAxisProd0588Certified, GeneralCK.Certificates.E8TAxisProd0589Certified, GeneralCK.Certificates.E8TAxisProd0590Certified, GeneralCK.Certificates.E8TAxisProd0591Certified, GeneralCK.Certificates.E8TAxisProd0592Certified, GeneralCK.Certificates.E8TAxisProd0593Certified, GeneralCK.Certificates.E8TAxisProd0594Certified, GeneralCK.Certificates.E8TAxisProd0595Certified, GeneralCK.Certificates.E8TAxisProd0596Certified, GeneralCK.Certificates.E8TAxisProd0597Certified, GeneralCK.Certificates.E8TAxisProd0598Certified, GeneralCK.Certificates.E8TAxisProd0599Certified, GeneralCK.Certificates.E8TAxisProd0600Certified, GeneralCK.Certificates.E8TAxisProd0601Certified, GeneralCK.Certificates.E8TAxisProd0602Certified, GeneralCK.Certificates.E8TAxisProd0603Certified) (piece 1 of 25) (piece 1 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0579Certified (+24 modules: GeneralCK.Certificates.E8TAxisProd0580Certified, GeneralCK.Certificates.E8TAxisProd0581Certified, GeneralCK.Certificates.E8TAxisProd0582Certified, GeneralCK.Certificates.E8TAxisProd0583Certified, GeneralCK.Certificates.E8TAxisProd0584Certified, GeneralCK.Certificates.E8TAxisProd0585Certified, GeneralCK.Certificates.E8TAxisProd0586Certified, GeneralCK.Certificates.E8TAxisProd0587Certified, GeneralCK.Certificates.E8TAxisProd0588Certified, GeneralCK.Certificates.E8TAxisProd0589Certified, GeneralCK.Certificates.E8TAxisProd0590Certified, GeneralCK.Certificates.E8TAxisProd0591Certified, GeneralCK.Certificates.E8TAxisProd0592Certified, GeneralCK.Certificates.E8TAxisProd0593Certified, GeneralCK.Certificates.E8TAxisProd0594Certified, GeneralCK.Certificates.E8TAxisProd0595Certified, GeneralCK.Certificates.E8TAxisProd0596Certified, GeneralCK.Certificates.E8TAxisProd0597Certified, GeneralCK.Certificates.E8TAxisProd0598Certified, GeneralCK.Certificates.E8TAxisProd0599Certified, GeneralCK.Certificates.E8TAxisProd0600Certified, GeneralCK.Certificates.E8TAxisProd0601Certified, GeneralCK.Certificates.E8TAxisProd0602Certified, GeneralCK.Certificates.E8TAxisProd0603Certified) (piece 1 of 25) (piece 1 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0579Certified (+24 modules: GeneralCK/Certificates/E8TAxisProd0580Certified, GeneralCK/Certificates/E8TAxisProd0581Certified, GeneralCK/Certificates/E8TAxisProd0582Certified, GeneralCK/Certificates/E8TAxisProd0583Certified, GeneralCK/Certificates/E8TAxisProd0584Certified, GeneralCK/Certificates/E8TAxisProd0585Certified, GeneralCK/Certificates/E8TAxisProd0586Certified, GeneralCK/Certificates/E8TAxisProd0587Certified, GeneralCK/Certificates/E8TAxisProd0588Certified, GeneralCK/Certificates/E8TAxisProd0589Certified, GeneralCK/Certificates/E8TAxisProd0590Certified, GeneralCK/Certificates/E8TAxisProd0591Certified, GeneralCK/Certificates/E8TAxisProd0592Certified, GeneralCK/Certificates/E8TAxisProd0593Certified, GeneralCK/Certificates/E8TAxisProd0594Certified, GeneralCK/Certificates/E8TAxisProd0595Certified, GeneralCK/Certificates/E8TAxisProd0596Certified, GeneralCK/Certificates/E8TAxisProd0597Certified, GeneralCK/Certificates/E8TAxisProd0598Certified, GeneralCK/Certificates/E8TAxisProd0599Certified, GeneralCK/Certificates/E8TAxisProd0600Certified, GeneralCK/Certificates/E8TAxisProd0601Certified, GeneralCK/Certificates/E8TAxisProd0602Certified, GeneralCK/Certificates/E8TAxisProd0603Certified) (piece 1 of 25) (piece 1 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0568CertifiedArithmetic__14
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0579EndpointWitnesses
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisCellCertificateSchema
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0580EndpointWitnesses
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0581EndpointWitnesses
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0582CertifiedArithmetic__15
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0582EndpointWitnesses
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0583EndpointWitnesses
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0584EndpointWitnesses
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0585EndpointWitnesses
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0586EndpointWitnesses
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0587EndpointWitnesses
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0588EndpointWitnesses
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0589EndpointWitnesses
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0590EndpointWitnesses
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0591EndpointWitnesses
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0592EndpointWitnesses
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0593EndpointWitnesses
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0594EndpointWitnesses
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0595EndpointWitnesses
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0596EndpointWitnesses
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0597CertifiedArithmetic__15
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0597EndpointWitnesses
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0598EndpointWitnesses
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0599EndpointWitnesses
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0600EndpointWitnesses
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0601EndpointWitnesses
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0602EndpointWitnesses
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0603EndpointWitnesses



namespace GeneralCK.Certificates.E8TAxisProd0579Certified
open GeneralCK Set E8TAxisDeltaDirectionalJet E8TAxisMixedCoefficients
open E8TAxisGeneralCenteredTaylor E8TAxisPartitionKernel
open E8TAxisProd0579Geometry E8TAxisProd0579CertifiedArithmetic

theorem centerBoxes_contains : centerBoxes.ContainsAt centerS centerT := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0579EndpointWitnesses.centerA_covers
    have hh := E8TAxisProd0579GraphCenterA.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0579EndpointWitnesses.centerB_covers
    have hh := E8TAxisProd0579GraphCenterB.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0579EndpointWitnesses.centerC_covers
    have hh := E8TAxisProd0579GraphCenterC.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0579EndpointWitnesses.centerD_covers
    have hh := E8TAxisProd0579GraphCenterD.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh

end GeneralCK.Certificates.E8TAxisProd0579Certified


