-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddleAggregation_Part000__8_q06
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddleAggregation_Part000__8_q06
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T08:02:23.00621+00:00
-- url     : https://prove2.me/theorems/78138dbe-8697-4da0-a7e6-f59fa314808e
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part000 (+7 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part001, Ge…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part000 (+7 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part001, GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part002, GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part003, GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part004, GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part005, GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part006, GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part007) (piece 7 of 8)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part000 (+7 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part001, GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part002, GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part003, GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part004, GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part005, GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part006, GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part007) (piece 7 of 8)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part000 (+7 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part001, GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part002, GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part003, GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part004, GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part005, GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part006, GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part007) (piece 7 of 8) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapLowMiddleAggregation/Part000 (+7 modules: GeneralCK/Certificates/Generated/DoubleCapLowMiddleAggregation/Part001, GeneralCK/Certificates/Generated/DoubleCapLowMiddleAggregation/Part002, GeneralCK/Certificates/Generated/DoubleCapLowMiddleAggregation/Part003, GeneralCK/Certificates/Generated/DoubleCapLowMiddleAggregation/Part004, GeneralCK/Certificates/Generated/DoubleCapLowMiddleAggregation/Part005, GeneralCK/Certificates/Generated/DoubleCapLowMiddleAggregation/Part006, GeneralCK/Certificates/Generated/DoubleCapLowMiddleAggregation/Part007) (piece 7 of 8).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddleAggregation_Part000__8_q05
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0192__6
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0198__6
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0204__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0208__6
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0214__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0218__6
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddleAggregation_Part000__8_q06_d000_004

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part006 =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddleAggregation.Part006
open GeneralCK
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000


theorem cover : ∀ m, 1059 / 12800 ≤ m → m ≤ 141 / 800 → 0 ≤ doubleCapLowResidual m := by
  intro m hmLo hmHi
  exact cover_d000_004 m hmLo hmHi

end GeneralCK.Certificates.DoubleCapLowMiddleAggregation.Part006


