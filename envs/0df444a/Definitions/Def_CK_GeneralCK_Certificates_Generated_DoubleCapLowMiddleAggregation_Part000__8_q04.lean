-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddleAggregation_Part000__8_q04
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddleAggregation_Part000__8_q04
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T01:56:45.467081+00:00
-- url     : https://prove2.me/theorems/d7b13cc6-a895-4ca5-abf4-c0ee990d23dc
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part000 (+7 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part001, Ge…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part000 (+7 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part001, GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part002, GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part003, GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part004, GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part005, GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part006, GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part007) (piece 5 of 8)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part000 (+7 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part001, GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part002, GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part003, GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part004, GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part005, GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part006, GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part007) (piece 5 of 8)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part000 (+7 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part001, GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part002, GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part003, GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part004, GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part005, GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part006, GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part007) (piece 5 of 8) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapLowMiddleAggregation/Part000 (+7 modules: GeneralCK/Certificates/Generated/DoubleCapLowMiddleAggregation/Part001, GeneralCK/Certificates/Generated/DoubleCapLowMiddleAggregation/Part002, GeneralCK/Certificates/Generated/DoubleCapLowMiddleAggregation/Part003, GeneralCK/Certificates/Generated/DoubleCapLowMiddleAggregation/Part004, GeneralCK/Certificates/Generated/DoubleCapLowMiddleAggregation/Part005, GeneralCK/Certificates/Generated/DoubleCapLowMiddleAggregation/Part006, GeneralCK/Certificates/Generated/DoubleCapLowMiddleAggregation/Part007) (piece 5 of 8).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddleAggregation_Part000__8_q03
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0122__7
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0129__7
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0136__7
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0143__7
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0150__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0154__5
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0159__5

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part004 =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddleAggregation.Part004
open GeneralCK
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

theorem cover : ∀ m : ℝ, 1519 / 51200 ≤ m → m ≤ 1187 / 25600 →
    0 ≤ doubleCapLowResidual m := by
  intro m hmLo hmHi
  by_cases h0128 : m ≤ (769 / 25600 : ℝ)
  · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0128.accepted_cell m (by linarith [hmLo]) h0128
  ·
    by_cases h0129 : m ≤ (1557 / 51200 : ℝ)
    · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0129.accepted_cell m (by linarith [(lt_of_not_ge h0128).le]) h0129
    ·
      by_cases h0130 : m ≤ (197 / 6400 : ℝ)
      · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0130.accepted_cell m (by linarith [(lt_of_not_ge h0129).le]) h0130
      ·
        by_cases h0131 : m ≤ (319 / 10240 : ℝ)
        · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0131.accepted_cell m (by linarith [(lt_of_not_ge h0130).le]) h0131
        ·
          by_cases h0132 : m ≤ (807 / 25600 : ℝ)
          · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0132.accepted_cell m (by linarith [(lt_of_not_ge h0131).le]) h0132
          ·
            by_cases h0133 : m ≤ (1633 / 51200 : ℝ)
            · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0133.accepted_cell m (by linarith [(lt_of_not_ge h0132).le]) h0133
            ·
              by_cases h0134 : m ≤ (413 / 12800 : ℝ)
              · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0134.accepted_cell m (by linarith [(lt_of_not_ge h0133).le]) h0134
              ·
                by_cases h0135 : m ≤ (1671 / 51200 : ℝ)
                · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0135.accepted_cell m (by linarith [(lt_of_not_ge h0134).le]) h0135
                ·
                  by_cases h0136 : m ≤ (169 / 5120 : ℝ)
                  · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0136.accepted_cell m (by linarith [(lt_of_not_ge h0135).le]) h0136
                  ·
                    by_cases h0137 : m ≤ (1709 / 51200 : ℝ)
                    · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0137.accepted_cell m (by linarith [(lt_of_not_ge h0136).le]) h0137
                    ·
                      by_cases h0138 : m ≤ (27 / 800 : ℝ)
                      · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0138.accepted_cell m (by linarith [(lt_of_not_ge h0137).le]) h0138
                      ·
                        by_cases h0139 : m ≤ (1747 / 51200 : ℝ)
                        · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0139.accepted_cell m (by linarith [(lt_of_not_ge h0138).le]) h0139
                        ·
                          by_cases h0140 : m ≤ (883 / 25600 : ℝ)
                          · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0140.accepted_cell m (by linarith [(lt_of_not_ge h0139).le]) h0140
                          ·
                            by_cases h0141 : m ≤ (357 / 10240 : ℝ)
                            · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0141.accepted_cell m (by linarith [(lt_of_not_ge h0140).le]) h0141
                            ·
                              by_cases h0142 : m ≤ (451 / 12800 : ℝ)
                              · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0142.accepted_cell m (by linarith [(lt_of_not_ge h0141).le]) h0142
                              ·
                                by_cases h0143 : m ≤ (1823 / 51200 : ℝ)
                                · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0143.accepted_cell m (by linarith [(lt_of_not_ge h0142).le]) h0143
                                ·
                                  by_cases h0144 : m ≤ (921 / 25600 : ℝ)
                                  · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0144.accepted_cell m (by linarith [(lt_of_not_ge h0143).le]) h0144
                                  ·
                                    by_cases h0145 : m ≤ (1861 / 51200 : ℝ)
                                    · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0145.accepted_cell m (by linarith [(lt_of_not_ge h0144).le]) h0145
                                    ·
                                      by_cases h0146 : m ≤ (47 / 1280 : ℝ)
                                      · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0146.accepted_cell m (by linarith [(lt_of_not_ge h0145).le]) h0146
                                      ·
                                        by_cases h0147 : m ≤ (959 / 25600 : ℝ)
                                        · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0147.accepted_cell m (by linarith [(lt_of_not_ge h0146).le]) h0147
                                        ·
                                          by_cases h0148 : m ≤ (489 / 12800 : ℝ)
                                          · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0148.accepted_cell m (by linarith [(lt_of_not_ge h0147).le]) h0148
                                          ·
                                            by_cases h0149 : m ≤ (997 / 25600 : ℝ)
                                            · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0149.accepted_cell m (by linarith [(lt_of_not_ge h0148).le]) h0149
                                            ·
                                              by_cases h0150 : m ≤ (127 / 3200 : ℝ)
                                              · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0150.accepted_cell m (by linarith [(lt_of_not_ge h0149).le]) h0150
                                              ·
                                                by_cases h0151 : m ≤ (207 / 5120 : ℝ)
                                                · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0151.accepted_cell m (by linarith [(lt_of_not_ge h0150).le]) h0151
                                                ·
                                                  by_cases h0152 : m ≤ (527 / 12800 : ℝ)
                                                  · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0152.accepted_cell m (by linarith [(lt_of_not_ge h0151).le]) h0152
                                                  ·
                                                    by_cases h0153 : m ≤ (1073 / 25600 : ℝ)
                                                    · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0153.accepted_cell m (by linarith [(lt_of_not_ge h0152).le]) h0153
                                                    ·
                                                      by_cases h0154 : m ≤ (273 / 6400 : ℝ)
                                                      · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0154.accepted_cell m (by linarith [(lt_of_not_ge h0153).le]) h0154
                                                      ·
                                                        by_cases h0155 : m ≤ (1111 / 25600 : ℝ)
                                                        · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0155.accepted_cell m (by linarith [(lt_of_not_ge h0154).le]) h0155
                                                        ·
                                                          by_cases h0156 : m ≤ (113 / 2560 : ℝ)
                                                          · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0156.accepted_cell m (by linarith [(lt_of_not_ge h0155).le]) h0156
                                                          ·
                                                            by_cases h0157 : m ≤ (1149 / 25600 : ℝ)
                                                            · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0157.accepted_cell m (by linarith [(lt_of_not_ge h0156).le]) h0157
                                                            ·
                                                              by_cases h0158 : m ≤ (73 / 1600 : ℝ)
                                                              · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0158.accepted_cell m (by linarith [(lt_of_not_ge h0157).le]) h0158
                                                              ·
                                                                exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0159.accepted_cell m (by linarith [(lt_of_not_ge h0158).le]) hmHi

#print axioms cover
end GeneralCK.Certificates.DoubleCapLowMiddleAggregation.Part004

end


