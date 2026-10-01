-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0056EndpointWitnesses_q01_q00_q00
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0056EndpointWitnesses_q01_q00_q00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T20:39:45.763499+00:00
-- url     : https://prove2.me/theorems/cbd4571d-f2b7-4aab-b548-de53bbf1ba17
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0056EndpointWitnesses (piece 2 of 4) (piece 1 of 4) (piece 1 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0056EndpointWitnesses (piece 2 of 4) (piece 1 of 4) (piece 1 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0056EndpointWitnesses (piece 2 of 4) (piece 1 of 4) (piece 1 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0056EndpointWitnesses (piece 2 of 4) (piece 1 of 4) (piece 1 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0056EndpointWitnesses (piece 2 of 4) (piece 1 of 4) (piece 1 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0056EndpointWitnesses_q00



namespace GeneralCK.Certificates.E8TAxisZero0056EndpointWitnesses
open Set DyadicInterval E8TAxisStableInterval E8TAxisStableScalar
open E8TAxisFirstCellInverseCoverage E8TAxisZero0056Geometry
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
def centerDLowerLog : DyadicInterval precision := ⟨408063947160780491089293755661542511144698609570, 408063947160780491089293755661542511144698710769⟩
def centerDLowerYBox : DyadicInterval precision := ⟨4314855224588657912415410142839713696312245797685, 4314855224588657912415410142839713696312247719038⟩
def centerDLowerInput : Inputs precision :=
  ⟨centerDLowerAlpha, centerDLowerExp, centerDLowerLog, endpointLogTwo⟩
def centerDLowerExpWitness : ExpWitness precision :=
  ⟨470725140515848859951996893419642375106206368599, scale precision, 470725140515848859951996893419642375106206499672, scale precision,
    0, 1024, 0, 1024, ⟨-1655801479599168435578757487370556305555978011357, -1655801479599168435578757487370556305555978009294⟩, ⟨-1655801479599168435578757487370556305555977604407, -1655801479599168435578757487370556305555977602344⟩⟩

theorem centerDLower_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDLowerAlpha) centerDLowerExp centerDLowerExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDLowerExp) centerDLowerLog fastLogWitness = true := by decide +kernel

end GeneralCK.Certificates.E8TAxisZero0056EndpointWitnesses


