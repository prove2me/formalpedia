-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0071PaddedInputs
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0071PaddedInputs
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T22:45:51.662194+00:00
-- url     : https://prove2.me/theorems/11152c94-0115-40b4-8e43-18e65c02bf7b
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0071PaddedInputs` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0071PaddedInputs` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0071PaddedInputs` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0071PaddedInputs (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0071PaddedInputs.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0071PaddedInputs_part00

namespace GeneralCK.Certificates.E8TAxisZero0071PaddedInputs
open DyadicInterval E8TAxisStableInterval
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
def wholeDAlpha : DyadicInterval precision := ⟨648844592727412176647428020776866274458553129992, 659917674403335303398947154306570012946038804784⟩
def wholeDInput : Inputs precision :=
  { E8TAxisZero0071StableWitnesses.wholeDInput with alpha := wholeDAlpha }

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDInput.alpha)
      wholeDInput.expNegTwo E8TAxisZero0071StableWitnesses.wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDInput.expNegTwo)
      wholeDInput.logOnePlusExp E8TAxisZero0071StableWitnesses.wholeDLogWitness = true := by decide

#print axioms centerB_primitive_checks
#print axioms wholeB_primitive_checks
end GeneralCK.Certificates.E8TAxisZero0071PaddedInputs


