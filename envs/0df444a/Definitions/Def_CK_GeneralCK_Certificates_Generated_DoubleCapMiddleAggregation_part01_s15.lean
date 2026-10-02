-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddleAggregation_part01_s15
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddleAggregation_part01_s15
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T20:30:42.904701+00:00
-- url     : https://prove2.me/theorems/751ac771-97c8-461c-98e7-95992d6fd2bf
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

import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0460__6
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0466__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0470__5
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0475__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0479
namespace GeneralCK.Certificates.DoubleCapMiddle
open GeneralCK
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem doubleCapHighResidual_middle_seg15 (m : ℝ) (h0459 : ¬ (m ≤ 815/2048)) (hmHi : m ≤ 2/5) : 0 ≤ doubleCapHighResidual m := by
  by_cases h0460 : m ≤ 8153/20480
  · exact Cell0460.accepted_cell m (by linarith [(lt_of_not_ge h0459).le]) h0460
  ·
    by_cases h0461 : m ≤ 2039/5120
    · exact Cell0461.accepted_cell m (by linarith [(lt_of_not_ge h0460).le]) h0461
    ·
      by_cases h0462 : m ≤ 8159/20480
      · exact Cell0462.accepted_cell m (by linarith [(lt_of_not_ge h0461).le]) h0462
      ·
        by_cases h0463 : m ≤ 4081/10240
        · exact Cell0463.accepted_cell m (by linarith [(lt_of_not_ge h0462).le]) h0463
        ·
          by_cases h0464 : m ≤ 1633/4096
          · exact Cell0464.accepted_cell m (by linarith [(lt_of_not_ge h0463).le]) h0464
          ·
            by_cases h0465 : m ≤ 1021/2560
            · exact Cell0465.accepted_cell m (by linarith [(lt_of_not_ge h0464).le]) h0465
            ·
              by_cases h0466 : m ≤ 8171/20480
              · exact Cell0466.accepted_cell m (by linarith [(lt_of_not_ge h0465).le]) h0466
              ·
                by_cases h0467 : m ≤ 4087/10240
                · exact Cell0467.accepted_cell m (by linarith [(lt_of_not_ge h0466).le]) h0467
                ·
                  by_cases h0468 : m ≤ 16351/40960
                  · exact Cell0468.accepted_cell m (by linarith [(lt_of_not_ge h0467).le]) h0468
                  ·
                    by_cases h0469 : m ≤ 8177/20480
                    · exact Cell0469.accepted_cell m (by linarith [(lt_of_not_ge h0468).le]) h0469
                    ·
                      by_cases h0470 : m ≤ 16357/40960
                      · exact Cell0470.accepted_cell m (by linarith [(lt_of_not_ge h0469).le]) h0470
                      ·
                        by_cases h0471 : m ≤ 409/1024
                        · exact Cell0471.accepted_cell m (by linarith [(lt_of_not_ge h0470).le]) h0471
                        ·
                          by_cases h0472 : m ≤ 16363/40960
                          · exact Cell0472.accepted_cell m (by linarith [(lt_of_not_ge h0471).le]) h0472
                          ·
                            by_cases h0473 : m ≤ 8183/20480
                            · exact Cell0473.accepted_cell m (by linarith [(lt_of_not_ge h0472).le]) h0473
                            ·
                              by_cases h0474 : m ≤ 16369/40960
                              · exact Cell0474.accepted_cell m (by linarith [(lt_of_not_ge h0473).le]) h0474
                              ·
                                by_cases h0475 : m ≤ 4093/10240
                                · exact Cell0475.accepted_cell m (by linarith [(lt_of_not_ge h0474).le]) h0475
                                ·
                                  by_cases h0476 : m ≤ 3275/8192
                                  · exact Cell0476.accepted_cell m (by linarith [(lt_of_not_ge h0475).le]) h0476
                                  ·
                                    by_cases h0477 : m ≤ 8189/20480
                                    · exact Cell0477.accepted_cell m (by linarith [(lt_of_not_ge h0476).le]) h0477
                                    ·
                                      by_cases h0478 : m ≤ 16381/40960
                                      · exact Cell0478.accepted_cell m (by linarith [(lt_of_not_ge h0477).le]) h0478
                                      ·
                                        exact Cell0479.accepted_cell m (by linarith [(lt_of_not_ge h0478).le]) hmHi

end GeneralCK.Certificates.DoubleCapMiddle


