-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0067StableWitnesses
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0067StableWitnesses
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:50:28.061987+00:00
-- url     : https://prove2.me/theorems/9ff0578a-ad20-4d00-934c-c7d3c0e10de1
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0067StableWitnesses` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0067StableWitnesses` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0067StableWitnesses` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0067StableWitnesses (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0067StableWitnesses.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0067StableWitnesses_q02

namespace GeneralCK.Certificates.E8TAxisZero0067StableWitnesses
open DyadicInterval E8TAxisStableInterval
set_option maxRecDepth 100000
theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerB_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisZero0067StableWitnesses


