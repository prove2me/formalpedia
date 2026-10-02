-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddleAggregation_Part000__8_q06_d002_004
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddleAggregation_Part000__8_q06_d002_004
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T07:31:44.010433+00:00
-- url     : https://prove2.me/theorems/46d5e597-1028-4fbc-93cb-f5306222d9a2
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part000 (proof segment of cover)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part000 (proof segment of cover)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part000 (proof segment of cover)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part000 (proof segment of cover) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapLowMiddleAggregation/Part000 (proof segment of cover).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddleAggregation_Part000__8_q06_v002
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddleAggregation_Part000__8_q06_v003

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part006 =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddleAggregation.Part006
open GeneralCK
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000


theorem cover_d002_004 (m : ℝ) (hL : (767 / 6400 : ℝ) ≤ m) (hU : m ≤ 141 / 800) : 0 ≤ doubleCapLowResidual m := by
  by_cases h : m ≤ (919 / 6400 : ℝ)
  · exact cover_v002 m hL h
  · exact cover_v003 m (lt_of_not_ge h).le hU

end GeneralCK.Certificates.DoubleCapLowMiddleAggregation.Part006


