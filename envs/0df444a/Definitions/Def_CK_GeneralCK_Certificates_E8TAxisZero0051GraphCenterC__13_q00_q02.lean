-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0051GraphCenterC__13_q00_q02
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0051GraphCenterC__13_q00_q02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T06:08:09.863576+00:00
-- url     : https://prove2.me/theorems/3a3a2662-e272-4a33-a5dc-f5282685762e
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0051GraphCenterC (+12 modules: GeneralCK.Certificates.E8TAxisZero0052GraphCenterC, GeneralCK.Certificates.E8TAxisZero0053Gra…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0051GraphCenterC (+12 modules: GeneralCK.Certificates.E8TAxisZero0052GraphCenterC, GeneralCK.Certificates.E8TAxisZero0053GraphCenterC, GeneralCK.Certificates.E8TAxisZero0054GraphCenterC, GeneralCK.Certificates.E8TAxisZero0055GraphCenterC, GeneralCK.Certificates.E8TAxisZero0056GraphCenterC, GeneralCK.Certificates.E8TAxisZero0057GraphCenterC, GeneralCK.Certificates.E8TAxisZero0058GraphCenterC, GeneralCK.Certificates.E8TAxisZero0059GraphCenterC, GeneralCK.Certificates.E8TAxisZero0060GraphCenterC, GeneralCK.Certificates.E8TAxisZero0061GraphCenterC, GeneralCK.Certificates.E8TAxisZero0062GraphCenterC, GeneralCK.Certificates.E8TAxisZero0063GraphCenterC) (piece 1 of 13) (piece 3 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0051GraphCenterC (+12 modules: GeneralCK.Certificates.E8TAxisZero0052GraphCenterC, GeneralCK.Certificates.E8TAxisZero0053GraphCenterC, GeneralCK.Certificates.E8TAxisZero0054GraphCenterC, GeneralCK.Certificates.E8TAxisZero0055GraphCenterC, GeneralCK.Certificates.E8TAxisZero0056GraphCenterC, GeneralCK.Certificates.E8TAxisZero0057GraphCenterC, GeneralCK.Certificates.E8TAxisZero0058GraphCenterC, GeneralCK.Certificates.E8TAxisZero0059GraphCenterC, GeneralCK.Certificates.E8TAxisZero0060GraphCenterC, GeneralCK.Certificates.E8TAxisZero0061GraphCenterC, GeneralCK.Certificates.E8TAxisZero0062GraphCenterC, GeneralCK.Certificates.E8TAxisZero0063GraphCenterC) (piece 1 of 13) (piece 3 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0051GraphCenterC (+12 modules: GeneralCK.Certificates.E8TAxisZero0052GraphCenterC, GeneralCK.Certificates.E8TAxisZero0053GraphCenterC, GeneralCK.Certificates.E8TAxisZero0054GraphCenterC, GeneralCK.Certificates.E8TAxisZero0055GraphCenterC, GeneralCK.Certificates.E8TAxisZero0056GraphCenterC, GeneralCK.Certificates.E8TAxisZero0057GraphCenterC, GeneralCK.Certificates.E8TAxisZero0058GraphCenterC, GeneralCK.Certificates.E8TAxisZero0059GraphCenterC, GeneralCK.Certificates.E8TAxisZero0060GraphCenterC, GeneralCK.Certificates.E8TAxisZero0061GraphCenterC, GeneralCK.Certificates.E8TAxisZero0062GraphCenterC, GeneralCK.Certificates.E8TAxisZero0063GraphCenterC) (piece 1 of 13) (piece 3 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0051GraphCenterC (+12 modules: GeneralCK/Certificates/E8TAxisZero0052GraphCenterC, GeneralCK/Certificates/E8TAxisZero0053GraphCenterC, GeneralCK/Certificates/E8TAxisZero0054GraphCenterC, GeneralCK/Certificates/E8TAxisZero0055GraphCenterC, GeneralCK/Certificates/E8TAxisZero0056GraphCenterC, GeneralCK/Certificates/E8TAxisZero0057GraphCenterC, GeneralCK/Certificates/E8TAxisZero0058GraphCenterC, GeneralCK/Certificates/E8TAxisZero0059GraphCenterC, GeneralCK/Certificates/E8TAxisZero0060GraphCenterC, GeneralCK/Certificates/E8TAxisZero0061GraphCenterC, GeneralCK/Certificates/E8TAxisZero0062GraphCenterC, GeneralCK/Certificates/E8TAxisZero0063GraphCenterC) (piece 1 of 13) (piece 3 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0051GraphCenterC__13_q00_q101

namespace GeneralCK.Certificates.E8TAxisZero0051GraphCenterC
open DyadicInterval E8TAxisStableInterval E8TAxisZero0051PaddedInputs
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem xBox_eq : xBox centerCInput = xJetBox := by
  simp only [xBox, logtwo_checked, rBox_eq, two_checked, hBox_eq, xNumerator_checked, xDenominator_checked, xDenominatorInv_checked, xJetBox_checked]

theorem yBox_eq : yBox centerCInput = yJetBox := by
  simp only [yBox, two_checked, logtwo_checked, alphaJet_checked, rBox_eq, hBox_eq, qBox_eq, ellBox_eq, logtwoInv_checked, yConstant_checked, yNumerator_checked, yDenominator_checked, yDenominatorInv_checked, yCorrection_checked, ySum_checked, yJetBox_checked]

theorem stable_eval_eq :
    E8TAxisReparamInterval.eval (xBox centerCInput) (yBox centerCInput) = qJetBox := by
  rw [xBox_eq, yBox_eq, qJetBox_checked]

theorem denominatorsPositive : DenominatorsPositive centerCInput := by
  simp only [DenominatorsPositive, onePlusZBox_eq, qDenominator_checked,
    two_checked, hBox_eq, xDenominator_checked, qBox_eq, ellBox_eq, yDenominator_checked]
  exact ⟨by decide, by decide, by decide, by decide, by decide⟩

theorem yPrime_pos : 0 < (yBox centerCInput).d1.lo := by
  rw [yBox_eq]
  decide

end GeneralCK.Certificates.E8TAxisZero0051GraphCenterC


