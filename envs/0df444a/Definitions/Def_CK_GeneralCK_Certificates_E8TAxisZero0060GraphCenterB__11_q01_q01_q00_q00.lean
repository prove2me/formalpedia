-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0060GraphCenterB__11_q01_q01_q00_q00
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0060GraphCenterB__11_q01_q01_q00_q00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T07:03:48.382404+00:00
-- url     : https://prove2.me/theorems/2c75a075-77d9-45a5-8a8e-5557bce5b197
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0060GraphCenterB (+10 modules: GeneralCK.Certificates.E8TAxisZero0061GraphCenterB, GeneralCK.Certificates.E8TAxisZero0062Gra…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0060GraphCenterB (+10 modules: GeneralCK.Certificates.E8TAxisZero0061GraphCenterB, GeneralCK.Certificates.E8TAxisZero0062GraphCenterB, GeneralCK.Certificates.E8TAxisZero0063GraphCenterB, GeneralCK.Certificates.E8TAxisZero0064GraphCenterB, GeneralCK.Certificates.E8TAxisZero0065GraphCenterB, GeneralCK.Certificates.E8TAxisZero0066GraphCenterB, GeneralCK.Certificates.E8TAxisZero0067GraphCenterB, GeneralCK.Certificates.E8TAxisZero0068GraphCenterB, GeneralCK.Certificates.E8TAxisZero0069GraphCenterB, GeneralCK.Certificates.E8TAxisZero0070GraphCenterB) (piece 2 of 11) (piece 2 of 3) (piece 1 of 4) (piece 1 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0060GraphCenterB (+10 modules: GeneralCK.Certificates.E8TAxisZero0061GraphCenterB, GeneralCK.Certificates.E8TAxisZero0062GraphCenterB, GeneralCK.Certificates.E8TAxisZero0063GraphCenterB, GeneralCK.Certificates.E8TAxisZero0064GraphCenterB, GeneralCK.Certificates.E8TAxisZero0065GraphCenterB, GeneralCK.Certificates.E8TAxisZero0066GraphCenterB, GeneralCK.Certificates.E8TAxisZero0067GraphCenterB, GeneralCK.Certificates.E8TAxisZero0068GraphCenterB, GeneralCK.Certificates.E8TAxisZero0069GraphCenterB, GeneralCK.Certificates.E8TAxisZero0070GraphCenterB) (piece 2 of 11) (piece 2 of 3) (piece 1 of 4) (piece 1 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0060GraphCenterB (+10 modules: GeneralCK.Certificates.E8TAxisZero0061GraphCenterB, GeneralCK.Certificates.E8TAxisZero0062GraphCenterB, GeneralCK.Certificates.E8TAxisZero0063GraphCenterB, GeneralCK.Certificates.E8TAxisZero0064GraphCenterB, GeneralCK.Certificates.E8TAxisZero0065GraphCenterB, GeneralCK.Certificates.E8TAxisZero0066GraphCenterB, GeneralCK.Certificates.E8TAxisZero0067GraphCenterB, GeneralCK.Certificates.E8TAxisZero0068GraphCenterB, GeneralCK.Certificates.E8TAxisZero0069GraphCenterB, GeneralCK.Certificates.E8TAxisZero0070GraphCenterB) (piece 2 of 11) (piece 2 of 3) (piece 1 of 4) (piece 1 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0060GraphCenterB (+10 modules: GeneralCK/Certificates/E8TAxisZero0061GraphCenterB, GeneralCK/Certificates/E8TAxisZero0062GraphCenterB, GeneralCK/Certificates/E8TAxisZero0063GraphCenterB, GeneralCK/Certificates/E8TAxisZero0064GraphCenterB, GeneralCK/Certificates/E8TAxisZero0065GraphCenterB, GeneralCK/Certificates/E8TAxisZero0066GraphCenterB, GeneralCK/Certificates/E8TAxisZero0067GraphCenterB, GeneralCK/Certificates/E8TAxisZero0068GraphCenterB, GeneralCK/Certificates/E8TAxisZero0069GraphCenterB, GeneralCK/Certificates/E8TAxisZero0070GraphCenterB) (piece 2 of 11) (piece 2 of 3) (piece 1 of 4) (piece 1 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0060GraphCenterB__11_q01_q00



namespace GeneralCK.Certificates.E8TAxisZero0061GraphCenterB
open DyadicInterval E8TAxisStableInterval E8TAxisZero0061PaddedInputs
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
def qData : DyadicJet5Enclosure precision :=
  ⟨⟨370928898159614779772034741012508403230476890379, 370928898159614779772034741012508411909795531802⟩,
   ⟨-640838109799657524689921745166074156563389123216, -640838109799657524689921745166074134335609272817⟩,
   ⟨918865397569861560862493158446995156177166559325, 918865397569861560862493158446995222786763239673⟩,
   ⟨-611617035870928275879350731242560964719857128889, -611617035870928275879350731242560721276447209198⟩,
   ⟨-2494963621052961420656039711951516311884397216290, -2494963621052961420656039711951515197779924240687⟩,
   ⟨13920793658305410819492379071014844465667164176726, 13920793658305410819492379071014850895922918328470⟩⟩

theorem qData_checked : qNumerator.mul qDenominatorInv = qData := by decide

def l1Data : DyadicJet5Enclosure precision :=
  ⟨⟨103056806692937110732138662144390812131343362728, 103056806692937110732138662144390814330366618281⟩,
   ⟨-199014471484340603288967762554478463605704176497, -199014471484340603288967762554478459228045473121⟩,
   ⟨370928898159614779772034741012508402596366349891, 370928898159614779772034741012508412543906072291⟩,
   ⟨-640838109799657524689921745166074157873005584751, -640838109799657524689921745166074133025992811284⟩,
   ⟨918865397569861560862493158446995154049311839154, 918865397569861560862493158446995224914617959847⟩,
   ⟨-611617035870928275879350731242560961414281238919, -611617035870928275879350731242560724582023099173⟩⟩

end GeneralCK.Certificates.E8TAxisZero0061GraphCenterB


