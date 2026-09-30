-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0065PaddedInputs_q01
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0065PaddedInputs_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T00:18:41.721319+00:00
-- url     : https://prove2.me/theorems/95841907-46a6-47e8-9938-e9f83026ffcd
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0065PaddedInputs (piece 2 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0065PaddedInputs (piece 2 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0065PaddedInputs (piece 2 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0065PaddedInputs (piece 2 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0065PaddedInputs (piece 2 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0065PaddedInputs_q00

namespace GeneralCK.Certificates.E8TAxisZero0065PaddedInputs
open DyadicInterval E8TAxisStableInterval
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCInput.alpha)
      centerCInput.expNegTwo E8TAxisZero0065StableWitnesses.centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCInput.expNegTwo)
      centerCInput.logOnePlusExp E8TAxisZero0065StableWitnesses.centerCLogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨721949241039261777105100229686264310385339384231, 721949241039261777105100229686264310385372938664⟩
def centerDInput : Inputs precision :=
  { E8TAxisZero0065StableWitnesses.centerDInput with alpha := centerDAlpha }

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDInput.alpha)
      centerDInput.expNegTwo E8TAxisZero0065StableWitnesses.centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDInput.expNegTwo)
      centerDInput.logOnePlusExp E8TAxisZero0065StableWitnesses.centerDLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1755682615968192604006724080732632442415708551686, 1790577155268251264318358183860781884376008230639⟩
def wholeBInput : Inputs precision :=
  { E8TAxisZero0065StableWitnesses.wholeBInput with alpha := wholeBAlpha }

end GeneralCK.Certificates.E8TAxisZero0065PaddedInputs


