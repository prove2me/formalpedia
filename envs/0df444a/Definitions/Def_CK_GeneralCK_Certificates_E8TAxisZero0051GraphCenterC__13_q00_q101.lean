-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0051GraphCenterC__13_q00_q101
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0051GraphCenterC__13_q00_q101
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T06:02:58.102806+00:00
-- url     : https://prove2.me/theorems/6cf9aa7b-30a1-4fc4-82eb-1202777ea4b1
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0051GraphCenterC (+12 modules: GeneralCK.Certificates.E8TAxisZero0052GraphCenterC, GeneralCK.Certificates.E8TAxisZero0053Gra…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0051GraphCenterC (+12 modules: GeneralCK.Certificates.E8TAxisZero0052GraphCenterC, GeneralCK.Certificates.E8TAxisZero0053GraphCenterC, GeneralCK.Certificates.E8TAxisZero0054GraphCenterC, GeneralCK.Certificates.E8TAxisZero0055GraphCenterC, GeneralCK.Certificates.E8TAxisZero0056GraphCenterC, GeneralCK.Certificates.E8TAxisZero0057GraphCenterC, GeneralCK.Certificates.E8TAxisZero0058GraphCenterC, GeneralCK.Certificates.E8TAxisZero0059GraphCenterC, GeneralCK.Certificates.E8TAxisZero0060GraphCenterC, GeneralCK.Certificates.E8TAxisZero0061GraphCenterC, GeneralCK.Certificates.E8TAxisZero0062GraphCenterC, GeneralCK.Certificates.E8TAxisZero0063GraphCenterC) (piece 1 of 13) (piece 2 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0051GraphCenterC (+12 modules: GeneralCK.Certificates.E8TAxisZero0052GraphCenterC, GeneralCK.Certificates.E8TAxisZero0053GraphCenterC, GeneralCK.Certificates.E8TAxisZero0054GraphCenterC, GeneralCK.Certificates.E8TAxisZero0055GraphCenterC, GeneralCK.Certificates.E8TAxisZero0056GraphCenterC, GeneralCK.Certificates.E8TAxisZero0057GraphCenterC, GeneralCK.Certificates.E8TAxisZero0058GraphCenterC, GeneralCK.Certificates.E8TAxisZero0059GraphCenterC, GeneralCK.Certificates.E8TAxisZero0060GraphCenterC, GeneralCK.Certificates.E8TAxisZero0061GraphCenterC, GeneralCK.Certificates.E8TAxisZero0062GraphCenterC, GeneralCK.Certificates.E8TAxisZero0063GraphCenterC) (piece 1 of 13) (piece 2 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0051GraphCenterC (+12 modules: GeneralCK.Certificates.E8TAxisZero0052GraphCenterC, GeneralCK.Certificates.E8TAxisZero0053GraphCenterC, GeneralCK.Certificates.E8TAxisZero0054GraphCenterC, GeneralCK.Certificates.E8TAxisZero0055GraphCenterC, GeneralCK.Certificates.E8TAxisZero0056GraphCenterC, GeneralCK.Certificates.E8TAxisZero0057GraphCenterC, GeneralCK.Certificates.E8TAxisZero0058GraphCenterC, GeneralCK.Certificates.E8TAxisZero0059GraphCenterC, GeneralCK.Certificates.E8TAxisZero0060GraphCenterC, GeneralCK.Certificates.E8TAxisZero0061GraphCenterC, GeneralCK.Certificates.E8TAxisZero0062GraphCenterC, GeneralCK.Certificates.E8TAxisZero0063GraphCenterC) (piece 1 of 13) (piece 2 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0051GraphCenterC (+12 modules: GeneralCK/Certificates/E8TAxisZero0052GraphCenterC, GeneralCK/Certificates/E8TAxisZero0053GraphCenterC, GeneralCK/Certificates/E8TAxisZero0054GraphCenterC, GeneralCK/Certificates/E8TAxisZero0055GraphCenterC, GeneralCK/Certificates/E8TAxisZero0056GraphCenterC, GeneralCK/Certificates/E8TAxisZero0057GraphCenterC, GeneralCK/Certificates/E8TAxisZero0058GraphCenterC, GeneralCK/Certificates/E8TAxisZero0059GraphCenterC, GeneralCK/Certificates/E8TAxisZero0060GraphCenterC, GeneralCK/Certificates/E8TAxisZero0061GraphCenterC, GeneralCK/Certificates/E8TAxisZero0062GraphCenterC, GeneralCK/Certificates/E8TAxisZero0063GraphCenterC) (piece 1 of 13) (piece 2 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0051GraphCenterC__13_q00_q100

namespace GeneralCK.Certificates.E8TAxisZero0051GraphCenterC
open DyadicInterval E8TAxisStableInterval E8TAxisZero0051PaddedInputs
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem yJetBox_checked : yConstant.mul ySum = yJetBox := by decide

def qJetBox : DyadicJet5Enclosure precision :=
  ⟨⟨512028152735516604881972450347078842027421047784, 512028152735516604881972450347078847915764345934⟩,
   ⟨255168449824747935312739776046026762834278680653, 255168449824747935312739776046026777654491867493⟩,
   ⟨113907593696192713144762099550064900847120213733, 113907593696192713144762099550064936226687268960⟩,
   ⟨83487624390379146732204924157497800043490997415, 83487624390379146732204924157497881809314631558⟩,
   ⟨56606487700455450741487428661063477926004585267, 56606487700455450741487428661063709629700075100⟩,
   ⟨33135699736992592575687177582578234535187378127, 33135699736992592575687177582579069685506644114⟩⟩

theorem qJetBox_checked : E8TAxisReparamInterval.eval xJetBox yJetBox = qJetBox := by decide

theorem onePlusZBox_eq : onePlusZBox centerCInput = onePlusZ := by
  simp only [onePlusZBox, one_checked, zData_checked, onePlusZ_checked]

theorem rBox_eq : rBox centerCInput = rData := by
  simp only [rBox, one_checked, zData_checked, onePlusZBox_eq, negativeZ_checked, rNumerator_checked, onePlusZInv_checked, rData_checked]

theorem qBox_eq : qBox centerCInput = qData := by
  simp only [qBox, four_checked, zData_checked, onePlusZBox_eq, qNumerator_checked, qDenominator_checked, qDenominatorInv_checked, qData_checked]

theorem l1Box_eq : l1Box centerCInput = l1Data := by
  simp only [l1Box, onePlusZBox_eq, l1Data_checked]

theorem ellBox_eq : ellBox centerCInput = ellData := by
  simp only [ellBox, alphaJet_checked, l1Box_eq, ellData_checked]

theorem hBox_eq : hBox centerCInput = hData := by
  simp only [hBox, l1Box_eq, two_checked, alphaJet_checked, zData_checked, onePlusZBox_eq, twiceAlpha_checked, twiceAlphaZ_checked, onePlusZInv_checked, hCorrection_checked, hData_checked]

end GeneralCK.Certificates.E8TAxisZero0051GraphCenterC


