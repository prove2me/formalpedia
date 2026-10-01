-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0057EndpointWitnesses_q02_q00_q01
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0057EndpointWitnesses_q02_q00_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T05:55:24.233983+00:00
-- url     : https://prove2.me/theorems/cbcdbdd8-cf78-4929-bc14-92a0e2bc6aea
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0057EndpointWitnesses (piece 3 of 4) (piece 1 of 3) (piece 2 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0057EndpointWitnesses (piece 3 of 4) (piece 1 of 3) (piece 2 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0057EndpointWitnesses (piece 3 of 4) (piece 1 of 3) (piece 2 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0057EndpointWitnesses (piece 3 of 4) (piece 1 of 3) (piece 2 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0057EndpointWitnesses (piece 3 of 4) (piece 1 of 3) (piece 2 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0057EndpointWitnesses_q02_q00_q00

namespace GeneralCK.Certificates.E8TAxisZero0057EndpointWitnesses
open Set DyadicInterval E8TAxisStableInterval E8TAxisStableScalar
open E8TAxisFirstCellInverseCoverage E8TAxisZero0057Geometry
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
def wholeCUpperYBox : DyadicInterval precision := ⟨4290420744089531879251692287042738339577519058222, 4290420744089531879251692287042738339577520962997⟩
def wholeCUpperInput : Inputs precision :=
  ⟨wholeCUpperAlpha, wholeCUpperExp, wholeCUpperLog, endpointLogTwo⟩
def wholeCUpperExpWitness : ExpWitness precision :=
  ⟨474359630541427216902466151616827440433595459511, scale precision, 474359630541427216902466151616827440433595590584, scale precision,
    0, 1024, 0, 1024, ⟨-1644560500012960486049290506200867814134873178701, -1644560500012960486049290506200867814134873176644⟩, ⟨-1644560500012960486049290506200867814134872774869, -1644560500012960486049290506200867814134872772810⟩⟩

theorem wholeCUpper_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCUpperAlpha) wholeCUpperExp wholeCUpperExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCUpperExp) wholeCUpperLog fastLogWitness = true := by decide +kernel

theorem wholeCUpper_denominators : DenominatorsPositive wholeCUpperInput := by
  unfold DenominatorsPositive
  decide +kernel

end GeneralCK.Certificates.E8TAxisZero0057EndpointWitnesses


