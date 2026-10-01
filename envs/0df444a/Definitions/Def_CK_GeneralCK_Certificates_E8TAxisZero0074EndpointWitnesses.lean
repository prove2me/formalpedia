-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0074EndpointWitnesses
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0074EndpointWitnesses
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T16:24:46.569558+00:00
-- url     : https://prove2.me/theorems/fd2bcb5d-e6d7-4294-ac05-871f16c212d8
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0074EndpointWitnesses` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0074EndpointWitnesses` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0074EndpointWitnesses` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0074EndpointWitnesses (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0074EndpointWitnesses.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0074EndpointWitnesses_q02

namespace GeneralCK.Certificates.E8TAxisZero0074EndpointWitnesses
open Set DyadicInterval E8TAxisStableInterval E8TAxisStableScalar
open E8TAxisFirstCellInverseCoverage E8TAxisZero0074Geometry
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
theorem wholeD_covers_slope {s : ℝ} (hs : s ∈ Icc (sLower) (sUpper)) :
    ∃ a : ℝ, E8TAxisZero0074PaddedInputs.wholeDInput.alpha.Contains a ∧
      0 < a ∧ Y a = s := by
  apply covers_of_endpoint_enclosures (by decide) (by decide)
    wholeDLower_contains wholeDUpper_contains _ _ hs
  · norm_num [wholeDLowerYBox, scale, precision, centerS, centerT, sLower, sUpper, tLower, tUpper]
  · norm_num [wholeDUpperYBox, scale, precision, centerS, centerT, sLower, sUpper, tLower, tUpper]

#print axioms centerB_covers
#print axioms wholeD_covers_slope
#print axioms wholeB_covers_slope

end GeneralCK.Certificates.E8TAxisZero0074EndpointWitnesses


