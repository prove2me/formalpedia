-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0052EndpointWitnesses_q02_q00_q01
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0052EndpointWitnesses_q02_q00_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T00:19:28.390647+00:00
-- url     : https://prove2.me/theorems/45bc63c3-52ef-49c8-8ecf-d11c0d7330ba
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0052EndpointWitnesses (piece 3 of 4) (piece 1 of 3) (piece 2 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0052EndpointWitnesses (piece 3 of 4) (piece 1 of 3) (piece 2 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0052EndpointWitnesses (piece 3 of 4) (piece 1 of 3) (piece 2 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0052EndpointWitnesses (piece 3 of 4) (piece 1 of 3) (piece 2 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0052EndpointWitnesses (piece 3 of 4) (piece 1 of 3) (piece 2 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0052EndpointWitnesses_q02_q00_q00

namespace GeneralCK.Certificates.E8TAxisZero0052EndpointWitnesses
open Set DyadicInterval E8TAxisStableInterval E8TAxisStableScalar
open E8TAxisFirstCellInverseCoverage E8TAxisZero0052Geometry
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
def wholeCUpperYBox : DyadicInterval precision := ⟨4553034319547428497366416905421445444671942091636, 4553034319547428497366416905421445444671944181107⟩
def wholeCUpperInput : Inputs precision :=
  ⟨wholeCUpperAlpha, wholeCUpperExp, wholeCUpperLog, endpointLogTwo⟩
def wholeCUpperExpWitness : ExpWitness precision :=
  ⟨436207571869314072928007112569681797670619196197, scale precision, 436207571869314072928007112569681797670619327270, scale precision,
    0, 1024, 0, 1024, ⟨-1767103811035192057233622761967255986022993509719, -1767103811035192057233622761967255986022993507656⟩, ⟨-1767103811035192057233622761967255986022993070565, -1767103811035192057233622761967255986022993068498⟩⟩

theorem wholeCUpper_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCUpperAlpha) wholeCUpperExp wholeCUpperExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCUpperExp) wholeCUpperLog fastLogWitness = true := by decide +kernel

theorem wholeCUpper_denominators : DenominatorsPositive wholeCUpperInput := by
  unfold DenominatorsPositive
  decide +kernel

end GeneralCK.Certificates.E8TAxisZero0052EndpointWitnesses


