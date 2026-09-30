-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0051GraphCenterC__13_q00
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0051GraphCenterC__13_q00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T06:52:00.392989+00:00
-- url     : https://prove2.me/theorems/63657691-e4c7-4f7f-8db9-b770aa06cef7
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0051GraphCenterC (+12 modules: GeneralCK.Certificates.E8TAxisZero0052GraphCenterC, GeneralCK.Certificates.E8TAxisZero0053Gra…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0051GraphCenterC (+12 modules: GeneralCK.Certificates.E8TAxisZero0052GraphCenterC, GeneralCK.Certificates.E8TAxisZero0053GraphCenterC, GeneralCK.Certificates.E8TAxisZero0054GraphCenterC, GeneralCK.Certificates.E8TAxisZero0055GraphCenterC, GeneralCK.Certificates.E8TAxisZero0056GraphCenterC, GeneralCK.Certificates.E8TAxisZero0057GraphCenterC, GeneralCK.Certificates.E8TAxisZero0058GraphCenterC, GeneralCK.Certificates.E8TAxisZero0059GraphCenterC, GeneralCK.Certificates.E8TAxisZero0060GraphCenterC, GeneralCK.Certificates.E8TAxisZero0061GraphCenterC, GeneralCK.Certificates.E8TAxisZero0062GraphCenterC, GeneralCK.Certificates.E8TAxisZero0063GraphCenterC) (piece 1 of 13)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0051GraphCenterC (+12 modules: GeneralCK.Certificates.E8TAxisZero0052GraphCenterC, GeneralCK.Certificates.E8TAxisZero0053GraphCenterC, GeneralCK.Certificates.E8TAxisZero0054GraphCenterC, GeneralCK.Certificates.E8TAxisZero0055GraphCenterC, GeneralCK.Certificates.E8TAxisZero0056GraphCenterC, GeneralCK.Certificates.E8TAxisZero0057GraphCenterC, GeneralCK.Certificates.E8TAxisZero0058GraphCenterC, GeneralCK.Certificates.E8TAxisZero0059GraphCenterC, GeneralCK.Certificates.E8TAxisZero0060GraphCenterC, GeneralCK.Certificates.E8TAxisZero0061GraphCenterC, GeneralCK.Certificates.E8TAxisZero0062GraphCenterC, GeneralCK.Certificates.E8TAxisZero0063GraphCenterC) (piece 1 of 13)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0051GraphCenterC (+12 modules: GeneralCK.Certificates.E8TAxisZero0052GraphCenterC, GeneralCK.Certificates.E8TAxisZero0053GraphCenterC, GeneralCK.Certificates.E8TAxisZero0054GraphCenterC, GeneralCK.Certificates.E8TAxisZero0055GraphCenterC, GeneralCK.Certificates.E8TAxisZero0056GraphCenterC, GeneralCK.Certificates.E8TAxisZero0057GraphCenterC, GeneralCK.Certificates.E8TAxisZero0058GraphCenterC, GeneralCK.Certificates.E8TAxisZero0059GraphCenterC, GeneralCK.Certificates.E8TAxisZero0060GraphCenterC, GeneralCK.Certificates.E8TAxisZero0061GraphCenterC, GeneralCK.Certificates.E8TAxisZero0062GraphCenterC, GeneralCK.Certificates.E8TAxisZero0063GraphCenterC) (piece 1 of 13) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0051GraphCenterC (+12 modules: GeneralCK/Certificates/E8TAxisZero0052GraphCenterC, GeneralCK/Certificates/E8TAxisZero0053GraphCenterC, GeneralCK/Certificates/E8TAxisZero0054GraphCenterC, GeneralCK/Certificates/E8TAxisZero0055GraphCenterC, GeneralCK/Certificates/E8TAxisZero0056GraphCenterC, GeneralCK/Certificates/E8TAxisZero0057GraphCenterC, GeneralCK/Certificates/E8TAxisZero0058GraphCenterC, GeneralCK/Certificates/E8TAxisZero0059GraphCenterC, GeneralCK/Certificates/E8TAxisZero0060GraphCenterC, GeneralCK/Certificates/E8TAxisZero0061GraphCenterC, GeneralCK/Certificates/E8TAxisZero0062GraphCenterC, GeneralCK/Certificates/E8TAxisZero0063GraphCenterC) (piece 1 of 13).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0051GraphCenterC__13_q00_q02

namespace GeneralCK.Certificates.E8TAxisZero0051GraphCenterC
open DyadicInterval E8TAxisStableInterval E8TAxisZero0051PaddedInputs
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem qJetBox_contains {a : ℝ} (ha : centerCInput.alpha.Contains a) (hapos : 0 < a) :
    qJetBox.Contains
      (E8InverseJet5Bridge.e8QJet5 E8InverseJet5Bridge.e8ThetaCanonicalJet5)
      (E8TAxisStableScalar.Y a) := by
  rw [← stable_eval_eq]
  exact checked_stable_contains_canonical
    centerC_primitive_checks.1 centerC_primitive_checks.2
    E8TAxisZero0051StableWitnesses.logTwo_checked denominatorsPositive yPrime_pos ha hapos

#print axioms stable_eval_eq
#print axioms qJetBox_contains
end GeneralCK.Certificates.E8TAxisZero0051GraphCenterC


