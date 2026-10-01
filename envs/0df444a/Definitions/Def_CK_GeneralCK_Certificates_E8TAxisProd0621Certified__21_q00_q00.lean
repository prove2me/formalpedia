-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0621Certified__21_q00_q00
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0621Certified__21_q00_q00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T20:52:04.682648+00:00
-- url     : https://prove2.me/theorems/5eb6fef6-33dc-4898-8b85-ccf91333cede
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0621Certified (+20 modules: GeneralCK.Certificates.E8TAxisProd0622Certified, GeneralCK.Certificates.E8TAxisProd0623Certified…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0621Certified (+20 modules: GeneralCK.Certificates.E8TAxisProd0622Certified, GeneralCK.Certificates.E8TAxisProd0623Certified, GeneralCK.Certificates.E8TAxisProd0624Certified, GeneralCK.Certificates.E8TAxisProd0625Certified, GeneralCK.Certificates.E8TAxisProd0626Certified, GeneralCK.Certificates.E8TAxisProd0627Certified, GeneralCK.Certificates.E8TAxisProd0628Certified, GeneralCK.Certificates.E8TAxisProd0629Certified, GeneralCK.Certificates.E8TAxisProd0630Certified, GeneralCK.Certificates.E8TAxisProd0631Certified, GeneralCK.Certificates.E8TAxisProd0632Certified, GeneralCK.Certificates.E8TAxisProd0633Certified, GeneralCK.Certificates.E8TAxisProd0634Certified, GeneralCK.Certificates.E8TAxisProd0635Certified, GeneralCK.Certificates.E8TAxisProd0636Certified, GeneralCK.Certificates.E8TAxisProd0637Certified, GeneralCK.Certificates.E8TAxisProd0638Certified, GeneralCK.Certificates.E8TAxisProd0639Certified, GeneralCK.Certificates.E8TAxisProd0640Certified, GeneralCK.Certificates.E8TAxisProd0641Certified) (piece 1 of 21) (piece 1 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0621Certified (+20 modules: GeneralCK.Certificates.E8TAxisProd0622Certified, GeneralCK.Certificates.E8TAxisProd0623Certified, GeneralCK.Certificates.E8TAxisProd0624Certified, GeneralCK.Certificates.E8TAxisProd0625Certified, GeneralCK.Certificates.E8TAxisProd0626Certified, GeneralCK.Certificates.E8TAxisProd0627Certified, GeneralCK.Certificates.E8TAxisProd0628Certified, GeneralCK.Certificates.E8TAxisProd0629Certified, GeneralCK.Certificates.E8TAxisProd0630Certified, GeneralCK.Certificates.E8TAxisProd0631Certified, GeneralCK.Certificates.E8TAxisProd0632Certified, GeneralCK.Certificates.E8TAxisProd0633Certified, GeneralCK.Certificates.E8TAxisProd0634Certified, GeneralCK.Certificates.E8TAxisProd0635Certified, GeneralCK.Certificates.E8TAxisProd0636Certified, GeneralCK.Certificates.E8TAxisProd0637Certified, GeneralCK.Certificates.E8TAxisProd0638Certified, GeneralCK.Certificates.E8TAxisProd0639Certified, GeneralCK.Certificates.E8TAxisProd0640Certified, GeneralCK.Certificates.E8TAxisProd0641Certified) (piece 1 of 21) (piece 1 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0621Certified (+20 modules: GeneralCK.Certificates.E8TAxisProd0622Certified, GeneralCK.Certificates.E8TAxisProd0623Certified, GeneralCK.Certificates.E8TAxisProd0624Certified, GeneralCK.Certificates.E8TAxisProd0625Certified, GeneralCK.Certificates.E8TAxisProd0626Certified, GeneralCK.Certificates.E8TAxisProd0627Certified, GeneralCK.Certificates.E8TAxisProd0628Certified, GeneralCK.Certificates.E8TAxisProd0629Certified, GeneralCK.Certificates.E8TAxisProd0630Certified, GeneralCK.Certificates.E8TAxisProd0631Certified, GeneralCK.Certificates.E8TAxisProd0632Certified, GeneralCK.Certificates.E8TAxisProd0633Certified, GeneralCK.Certificates.E8TAxisProd0634Certified, GeneralCK.Certificates.E8TAxisProd0635Certified, GeneralCK.Certificates.E8TAxisProd0636Certified, GeneralCK.Certificates.E8TAxisProd0637Certified, GeneralCK.Certificates.E8TAxisProd0638Certified, GeneralCK.Certificates.E8TAxisProd0639Certified, GeneralCK.Certificates.E8TAxisProd0640Certified, GeneralCK.Certificates.E8TAxisProd0641Certified) (piece 1 of 21) (piece 1 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0621Certified (+20 modules: GeneralCK/Certificates/E8TAxisProd0622Certified, GeneralCK/Certificates/E8TAxisProd0623Certified, GeneralCK/Certificates/E8TAxisProd0624Certified, GeneralCK/Certificates/E8TAxisProd0625Certified, GeneralCK/Certificates/E8TAxisProd0626Certified, GeneralCK/Certificates/E8TAxisProd0627Certified, GeneralCK/Certificates/E8TAxisProd0628Certified, GeneralCK/Certificates/E8TAxisProd0629Certified, GeneralCK/Certificates/E8TAxisProd0630Certified, GeneralCK/Certificates/E8TAxisProd0631Certified, GeneralCK/Certificates/E8TAxisProd0632Certified, GeneralCK/Certificates/E8TAxisProd0633Certified, GeneralCK/Certificates/E8TAxisProd0634Certified, GeneralCK/Certificates/E8TAxisProd0635Certified, GeneralCK/Certificates/E8TAxisProd0636Certified, GeneralCK/Certificates/E8TAxisProd0637Certified, GeneralCK/Certificates/E8TAxisProd0638Certified, GeneralCK/Certificates/E8TAxisProd0639Certified, GeneralCK/Certificates/E8TAxisProd0640Certified, GeneralCK/Certificates/E8TAxisProd0641Certified) (piece 1 of 21) (piece 1 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0612CertifiedArithmetic__13
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0621EndpointWitnesses
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisCellCertificateSchema
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0622EndpointWitnesses
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0623EndpointWitnesses
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0624EndpointWitnesses
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0625CertifiedArithmetic__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0625EndpointWitnesses
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0626EndpointWitnesses
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0627EndpointWitnesses
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0628EndpointWitnesses
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0629EndpointWitnesses
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0630EndpointWitnesses
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0631EndpointWitnesses
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0632EndpointWitnesses
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0633EndpointWitnesses
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0634EndpointWitnesses
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0635EndpointWitnesses
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0636CertifiedArithmetic__16
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0636EndpointWitnesses
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0637EndpointWitnesses
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0638EndpointWitnesses
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0639EndpointWitnesses
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0640EndpointWitnesses
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0641EndpointWitnesses



namespace GeneralCK.Certificates.E8TAxisProd0621Certified
open GeneralCK Set E8TAxisDeltaDirectionalJet E8TAxisMixedCoefficients
open E8TAxisGeneralCenteredTaylor E8TAxisPartitionKernel
open E8TAxisProd0621Geometry E8TAxisProd0621CertifiedArithmetic

theorem centerBoxes_contains : centerBoxes.ContainsAt centerS centerT := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0621EndpointWitnesses.centerA_covers
    have hh := E8TAxisProd0621GraphCenterA.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0621EndpointWitnesses.centerB_covers
    have hh := E8TAxisProd0621GraphCenterB.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0621EndpointWitnesses.centerC_covers
    have hh := E8TAxisProd0621GraphCenterC.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0621EndpointWitnesses.centerD_covers
    have hh := E8TAxisProd0621GraphCenterD.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh

end GeneralCK.Certificates.E8TAxisProd0621Certified


