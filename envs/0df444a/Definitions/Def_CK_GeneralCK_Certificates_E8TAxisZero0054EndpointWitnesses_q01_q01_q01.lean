-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0054EndpointWitnesses_q01_q01_q01
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0054EndpointWitnesses_q01_q01_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T21:41:44.358259+00:00
-- url     : https://prove2.me/theorems/684be275-72ca-45a2-9b1a-b80f11163f7c
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0054EndpointWitnesses (piece 2 of 4) (piece 2 of 4) (piece 2 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0054EndpointWitnesses (piece 2 of 4) (piece 2 of 4) (piece 2 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0054EndpointWitnesses (piece 2 of 4) (piece 2 of 4) (piece 2 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0054EndpointWitnesses (piece 2 of 4) (piece 2 of 4) (piece 2 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0054EndpointWitnesses (piece 2 of 4) (piece 2 of 4) (piece 2 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0054EndpointWitnesses_q01_q01_q00

namespace GeneralCK.Certificates.E8TAxisZero0054EndpointWitnesses
open Set DyadicInterval E8TAxisStableInterval E8TAxisStableScalar
open E8TAxisFirstCellInverseCoverage E8TAxisZero0054Geometry
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
def wholeBLowerLog : DyadicInterval precision := ⟨75790943549876871789636664824308865659127167984, 75790943549876871789636664824308865659127294489⟩
def wholeBLowerYBox : DyadicInterval precision := ⟨8787278594452053795699655056706651655681240628162, 8787278594452053795699655056706651655681250629996⟩
def wholeBLowerInput : Inputs precision :=
  ⟨wholeBLowerAlpha, wholeBLowerExp, wholeBLowerLog, endpointLogTwo⟩
def wholeBLowerExpWitness : ExpWitness precision :=
  ⟨77790552611549477616722994034945111529042798829, scale precision, 77790552611549477616722994034945111529042929902, scale precision,
    0, 1024, 0, 1024, ⟨-4286876182841290758319817480246583832971392394893, -4286876182841290758319817480246583832971392392746⟩, ⟨-4286876182841290758319817480246583832971389932351, -4286876182841290758319817480246583832971389930196⟩⟩

theorem wholeBLower_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBLowerAlpha) wholeBLowerExp wholeBLowerExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBLowerExp) wholeBLowerLog fastLogWitness = true := by decide +kernel

end GeneralCK.Certificates.E8TAxisZero0054EndpointWitnesses


