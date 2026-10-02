-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddleAggregation_Part000__8_q05
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddleAggregation_Part000__8_q05
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T04:18:26.70277+00:00
-- url     : https://prove2.me/theorems/76d9b29d-db93-463b-ab2d-1a5cab9ccc31
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part000 (+7 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part001, Ge…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part000 (+7 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part001, GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part002, GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part003, GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part004, GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part005, GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part006, GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part007) (piece 6 of 8)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part000 (+7 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part001, GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part002, GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part003, GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part004, GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part005, GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part006, GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part007) (piece 6 of 8)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part000 (+7 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part001, GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part002, GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part003, GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part004, GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part005, GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part006, GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part007) (piece 6 of 8) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapLowMiddleAggregation/Part000 (+7 modules: GeneralCK/Certificates/Generated/DoubleCapLowMiddleAggregation/Part001, GeneralCK/Certificates/Generated/DoubleCapLowMiddleAggregation/Part002, GeneralCK/Certificates/Generated/DoubleCapLowMiddleAggregation/Part003, GeneralCK/Certificates/Generated/DoubleCapLowMiddleAggregation/Part004, GeneralCK/Certificates/Generated/DoubleCapLowMiddleAggregation/Part005, GeneralCK/Certificates/Generated/DoubleCapLowMiddleAggregation/Part006, GeneralCK/Certificates/Generated/DoubleCapLowMiddleAggregation/Part007) (piece 6 of 8).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddleAggregation_Part000__8_q04
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0159__5
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0164__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0168__5
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0173__3
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0176__3
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0179__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0183__6
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0189__3

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part005 =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddleAggregation.Part005
open GeneralCK
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

theorem cover : ∀ m : ℝ, 1187 / 25600 ≤ m → m ≤ 1059 / 12800 →
    0 ≤ doubleCapLowResidual m := by
  intro m hmLo hmHi
  by_cases h0160 : m ≤ (603 / 12800 : ℝ)
  · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0160.accepted_cell m (by linarith [hmLo]) h0160
  ·
    by_cases h0161 : m ≤ (49 / 1024 : ℝ)
    · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0161.accepted_cell m (by linarith [(lt_of_not_ge h0160).le]) h0161
    ·
      by_cases h0162 : m ≤ (311 / 6400 : ℝ)
      · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0162.accepted_cell m (by linarith [(lt_of_not_ge h0161).le]) h0162
      ·
        by_cases h0163 : m ≤ (1263 / 25600 : ℝ)
        · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0163.accepted_cell m (by linarith [(lt_of_not_ge h0162).le]) h0163
        ·
          by_cases h0164 : m ≤ (641 / 12800 : ℝ)
          · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0164.accepted_cell m (by linarith [(lt_of_not_ge h0163).le]) h0164
          ·
            by_cases h0165 : m ≤ (1301 / 25600 : ℝ)
            · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0165.accepted_cell m (by linarith [(lt_of_not_ge h0164).le]) h0165
            ·
              by_cases h0166 : m ≤ (33 / 640 : ℝ)
              · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0166.accepted_cell m (by linarith [(lt_of_not_ge h0165).le]) h0166
              ·
                by_cases h0167 : m ≤ (1339 / 25600 : ℝ)
                · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0167.accepted_cell m (by linarith [(lt_of_not_ge h0166).le]) h0167
                ·
                  by_cases h0168 : m ≤ (679 / 12800 : ℝ)
                  · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0168.accepted_cell m (by linarith [(lt_of_not_ge h0167).le]) h0168
                  ·
                    by_cases h0169 : m ≤ (1377 / 25600 : ℝ)
                    · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0169.accepted_cell m (by linarith [(lt_of_not_ge h0168).le]) h0169
                    ·
                      by_cases h0170 : m ≤ (349 / 6400 : ℝ)
                      · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0170.accepted_cell m (by linarith [(lt_of_not_ge h0169).le]) h0170
                      ·
                        by_cases h0171 : m ≤ (283 / 5120 : ℝ)
                        · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0171.accepted_cell m (by linarith [(lt_of_not_ge h0170).le]) h0171
                        ·
                          by_cases h0172 : m ≤ (717 / 12800 : ℝ)
                          · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0172.accepted_cell m (by linarith [(lt_of_not_ge h0171).le]) h0172
                          ·
                            by_cases h0173 : m ≤ (1453 / 25600 : ℝ)
                            · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0173.accepted_cell m (by linarith [(lt_of_not_ge h0172).le]) h0173
                            ·
                              by_cases h0174 : m ≤ (23 / 400 : ℝ)
                              · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0174.accepted_cell m (by linarith [(lt_of_not_ge h0173).le]) h0174
                              ·
                                by_cases h0175 : m ≤ (151 / 2560 : ℝ)
                                · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0175.accepted_cell m (by linarith [(lt_of_not_ge h0174).le]) h0175
                                ·
                                  by_cases h0176 : m ≤ (387 / 6400 : ℝ)
                                  · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0176.accepted_cell m (by linarith [(lt_of_not_ge h0175).le]) h0176
                                  ·
                                    by_cases h0177 : m ≤ (793 / 12800 : ℝ)
                                    · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0177.accepted_cell m (by linarith [(lt_of_not_ge h0176).le]) h0177
                                    ·
                                      by_cases h0178 : m ≤ (203 / 3200 : ℝ)
                                      · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0178.accepted_cell m (by linarith [(lt_of_not_ge h0177).le]) h0178
                                      ·
                                        by_cases h0179 : m ≤ (831 / 12800 : ℝ)
                                        · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0179.accepted_cell m (by linarith [(lt_of_not_ge h0178).le]) h0179
                                        ·
                                          by_cases h0180 : m ≤ (17 / 256 : ℝ)
                                          · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0180.accepted_cell m (by linarith [(lt_of_not_ge h0179).le]) h0180
                                          ·
                                            by_cases h0181 : m ≤ (869 / 12800 : ℝ)
                                            · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0181.accepted_cell m (by linarith [(lt_of_not_ge h0180).le]) h0181
                                            ·
                                              by_cases h0182 : m ≤ (111 / 1600 : ℝ)
                                              · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0182.accepted_cell m (by linarith [(lt_of_not_ge h0181).le]) h0182
                                              ·
                                                by_cases h0183 : m ≤ (907 / 12800 : ℝ)
                                                · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0183.accepted_cell m (by linarith [(lt_of_not_ge h0182).le]) h0183
                                                ·
                                                  by_cases h0184 : m ≤ (463 / 6400 : ℝ)
                                                  · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0184.accepted_cell m (by linarith [(lt_of_not_ge h0183).le]) h0184
                                                  ·
                                                    by_cases h0185 : m ≤ (189 / 2560 : ℝ)
                                                    · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0185.accepted_cell m (by linarith [(lt_of_not_ge h0184).le]) h0185
                                                    ·
                                                      by_cases h0186 : m ≤ (241 / 3200 : ℝ)
                                                      · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0186.accepted_cell m (by linarith [(lt_of_not_ge h0185).le]) h0186
                                                      ·
                                                        by_cases h0187 : m ≤ (983 / 12800 : ℝ)
                                                        · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0187.accepted_cell m (by linarith [(lt_of_not_ge h0186).le]) h0187
                                                        ·
                                                          by_cases h0188 : m ≤ (501 / 6400 : ℝ)
                                                          · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0188.accepted_cell m (by linarith [(lt_of_not_ge h0187).le]) h0188
                                                          ·
                                                            by_cases h0189 : m ≤ (1021 / 12800 : ℝ)
                                                            · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0189.accepted_cell m (by linarith [(lt_of_not_ge h0188).le]) h0189
                                                            ·
                                                              by_cases h0190 : m ≤ (13 / 160 : ℝ)
                                                              · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0190.accepted_cell m (by linarith [(lt_of_not_ge h0189).le]) h0190
                                                              ·
                                                                exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0191.accepted_cell m (by linarith [(lt_of_not_ge h0190).le]) hmHi

#print axioms cover
end GeneralCK.Certificates.DoubleCapLowMiddleAggregation.Part005

end


