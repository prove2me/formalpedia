-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddleAggregation_Part000__8_q01
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddleAggregation_Part000__8_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T21:19:32.815137+00:00
-- url     : https://prove2.me/theorems/ef7196e0-77c4-489b-b67f-6c4d249a5653
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part000 (+7 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part001, Ge…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part000 (+7 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part001, GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part002, GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part003, GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part004, GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part005, GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part006, GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part007) (piece 2 of 8)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part000 (+7 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part001, GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part002, GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part003, GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part004, GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part005, GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part006, GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part007) (piece 2 of 8)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part000 (+7 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part001, GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part002, GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part003, GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part004, GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part005, GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part006, GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part007) (piece 2 of 8) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapLowMiddleAggregation/Part000 (+7 modules: GeneralCK/Certificates/Generated/DoubleCapLowMiddleAggregation/Part001, GeneralCK/Certificates/Generated/DoubleCapLowMiddleAggregation/Part002, GeneralCK/Certificates/Generated/DoubleCapLowMiddleAggregation/Part003, GeneralCK/Certificates/Generated/DoubleCapLowMiddleAggregation/Part004, GeneralCK/Certificates/Generated/DoubleCapLowMiddleAggregation/Part005, GeneralCK/Certificates/Generated/DoubleCapLowMiddleAggregation/Part006, GeneralCK/Certificates/Generated/DoubleCapLowMiddleAggregation/Part007) (piece 2 of 8).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddleAggregation_Part000__8_q00
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0027__7
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0034__5
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0039__5
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0044__5
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0049__5
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0054__5
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0059__6

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part001 =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddleAggregation.Part001
open GeneralCK
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

theorem cover : ∀ m : ℝ, 2523 / 204800 ≤ m → m ≤ 3131 / 204800 →
    0 ≤ doubleCapLowResidual m := by
  intro m hmLo hmHi
  by_cases h0032 : m ≤ (1271 / 102400 : ℝ)
  · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0032.accepted_cell m (by linarith [hmLo]) h0032
  ·
    by_cases h0033 : m ≤ (2561 / 204800 : ℝ)
    · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0033.accepted_cell m (by linarith [(lt_of_not_ge h0032).le]) h0033
    ·
      by_cases h0034 : m ≤ (129 / 10240 : ℝ)
      · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0034.accepted_cell m (by linarith [(lt_of_not_ge h0033).le]) h0034
      ·
        by_cases h0035 : m ≤ (2599 / 204800 : ℝ)
        · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0035.accepted_cell m (by linarith [(lt_of_not_ge h0034).le]) h0035
        ·
          by_cases h0036 : m ≤ (1309 / 102400 : ℝ)
          · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0036.accepted_cell m (by linarith [(lt_of_not_ge h0035).le]) h0036
          ·
            by_cases h0037 : m ≤ (2637 / 204800 : ℝ)
            · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0037.accepted_cell m (by linarith [(lt_of_not_ge h0036).le]) h0037
            ·
              by_cases h0038 : m ≤ (83 / 6400 : ℝ)
              · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0038.accepted_cell m (by linarith [(lt_of_not_ge h0037).le]) h0038
              ·
                by_cases h0039 : m ≤ (107 / 8192 : ℝ)
                · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0039.accepted_cell m (by linarith [(lt_of_not_ge h0038).le]) h0039
                ·
                  by_cases h0040 : m ≤ (1347 / 102400 : ℝ)
                  · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0040.accepted_cell m (by linarith [(lt_of_not_ge h0039).le]) h0040
                  ·
                    by_cases h0041 : m ≤ (2713 / 204800 : ℝ)
                    · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0041.accepted_cell m (by linarith [(lt_of_not_ge h0040).le]) h0041
                    ·
                      by_cases h0042 : m ≤ (683 / 51200 : ℝ)
                      · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0042.accepted_cell m (by linarith [(lt_of_not_ge h0041).le]) h0042
                      ·
                        by_cases h0043 : m ≤ (2751 / 204800 : ℝ)
                        · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0043.accepted_cell m (by linarith [(lt_of_not_ge h0042).le]) h0043
                        ·
                          by_cases h0044 : m ≤ (277 / 20480 : ℝ)
                          · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0044.accepted_cell m (by linarith [(lt_of_not_ge h0043).le]) h0044
                          ·
                            by_cases h0045 : m ≤ (2789 / 204800 : ℝ)
                            · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0045.accepted_cell m (by linarith [(lt_of_not_ge h0044).le]) h0045
                            ·
                              by_cases h0046 : m ≤ (351 / 25600 : ℝ)
                              · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0046.accepted_cell m (by linarith [(lt_of_not_ge h0045).le]) h0046
                              ·
                                by_cases h0047 : m ≤ (2827 / 204800 : ℝ)
                                · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0047.accepted_cell m (by linarith [(lt_of_not_ge h0046).le]) h0047
                                ·
                                  by_cases h0048 : m ≤ (1423 / 102400 : ℝ)
                                  · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0048.accepted_cell m (by linarith [(lt_of_not_ge h0047).le]) h0048
                                  ·
                                    by_cases h0049 : m ≤ (573 / 40960 : ℝ)
                                    · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0049.accepted_cell m (by linarith [(lt_of_not_ge h0048).le]) h0049
                                    ·
                                      by_cases h0050 : m ≤ (721 / 51200 : ℝ)
                                      · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0050.accepted_cell m (by linarith [(lt_of_not_ge h0049).le]) h0050
                                      ·
                                        by_cases h0051 : m ≤ (2903 / 204800 : ℝ)
                                        · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0051.accepted_cell m (by linarith [(lt_of_not_ge h0050).le]) h0051
                                        ·
                                          by_cases h0052 : m ≤ (1461 / 102400 : ℝ)
                                          · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0052.accepted_cell m (by linarith [(lt_of_not_ge h0051).le]) h0052
                                          ·
                                            by_cases h0053 : m ≤ (2941 / 204800 : ℝ)
                                            · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0053.accepted_cell m (by linarith [(lt_of_not_ge h0052).le]) h0053
                                            ·
                                              by_cases h0054 : m ≤ (37 / 2560 : ℝ)
                                              · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0054.accepted_cell m (by linarith [(lt_of_not_ge h0053).le]) h0054
                                              ·
                                                by_cases h0055 : m ≤ (2979 / 204800 : ℝ)
                                                · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0055.accepted_cell m (by linarith [(lt_of_not_ge h0054).le]) h0055
                                                ·
                                                  by_cases h0056 : m ≤ (1499 / 102400 : ℝ)
                                                  · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0056.accepted_cell m (by linarith [(lt_of_not_ge h0055).le]) h0056
                                                  ·
                                                    by_cases h0057 : m ≤ (3017 / 204800 : ℝ)
                                                    · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0057.accepted_cell m (by linarith [(lt_of_not_ge h0056).le]) h0057
                                                    ·
                                                      by_cases h0058 : m ≤ (759 / 51200 : ℝ)
                                                      · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0058.accepted_cell m (by linarith [(lt_of_not_ge h0057).le]) h0058
                                                      ·
                                                        by_cases h0059 : m ≤ (611 / 40960 : ℝ)
                                                        · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0059.accepted_cell m (by linarith [(lt_of_not_ge h0058).le]) h0059
                                                        ·
                                                          by_cases h0060 : m ≤ (1537 / 102400 : ℝ)
                                                          · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0060.accepted_cell m (by linarith [(lt_of_not_ge h0059).le]) h0060
                                                          ·
                                                            by_cases h0061 : m ≤ (3093 / 204800 : ℝ)
                                                            · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0061.accepted_cell m (by linarith [(lt_of_not_ge h0060).le]) h0061
                                                            ·
                                                              by_cases h0062 : m ≤ (389 / 25600 : ℝ)
                                                              · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0062.accepted_cell m (by linarith [(lt_of_not_ge h0061).le]) h0062
                                                              ·
                                                                exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0063.accepted_cell m (by linarith [(lt_of_not_ge h0062).le]) hmHi

#print axioms cover
end GeneralCK.Certificates.DoubleCapLowMiddleAggregation.Part001

end


