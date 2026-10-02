-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddleAggregation_part01_d007_014
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddleAggregation_part01_d007_014
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T02:01:23.352033+00:00
-- url     : https://prove2.me/theorems/dc0af901-b17d-444f-bd1d-689cfaae6620
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapMiddleAggregation (proof segment of doubleCapHighResidual_middle)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapMiddleAggregation (proof segment of doubleCapHighResidual_middle)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapMiddleAggregation (proof segment of doubleCapHighResidual_middle)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapMiddleAggregation (proof segment of doubleCapHighResidual_middle) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapMiddleAggregation (proof segment of doubleCapHighResidual_middle).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddleAggregation_part01_d007_010
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddleAggregation_part01_d010_014
namespace GeneralCK.Certificates.DoubleCapMiddle
open GeneralCK
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem doubleCapHighResidual_middle_d007_014 (m : ℝ) (hL : 289/1024 ≤ m) (hU : m ≤ 1613/5120) : 0 ≤ doubleCapHighResidual m := by
  by_cases h : m ≤ 1517/5120
  · exact doubleCapHighResidual_middle_d007_010 m hL h
  · exact doubleCapHighResidual_middle_d010_014 m (lt_of_not_ge h).le hU

end GeneralCK.Certificates.DoubleCapMiddle


