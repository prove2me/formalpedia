-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddleAggregation_Part000__8_q00
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddleAggregation_Part000__8_q00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T19:34:25.31661+00:00
-- url     : https://prove2.me/theorems/bbe462cc-20e0-414d-8113-03e173cdb8b0
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part000 (+7 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part001, Ge…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part000 (+7 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part001, GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part002, GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part003, GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part004, GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part005, GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part006, GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part007) (piece 1 of 8)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part000 (+7 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part001, GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part002, GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part003, GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part004, GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part005, GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part006, GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part007) (piece 1 of 8)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part000 (+7 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part001, GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part002, GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part003, GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part004, GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part005, GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part006, GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part007) (piece 1 of 8) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapLowMiddleAggregation/Part000 (+7 modules: GeneralCK/Certificates/Generated/DoubleCapLowMiddleAggregation/Part001, GeneralCK/Certificates/Generated/DoubleCapLowMiddleAggregation/Part002, GeneralCK/Certificates/Generated/DoubleCapLowMiddleAggregation/Part003, GeneralCK/Certificates/Generated/DoubleCapLowMiddleAggregation/Part004, GeneralCK/Certificates/Generated/DoubleCapLowMiddleAggregation/Part005, GeneralCK/Certificates/Generated/DoubleCapLowMiddleAggregation/Part006, GeneralCK/Certificates/Generated/DoubleCapLowMiddleAggregation/Part007) (piece 1 of 8).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0000__5
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0005__6
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0011__5
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0016__6
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0022__5
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0027__7

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part000 =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddleAggregation.Part000
open GeneralCK
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

theorem cover : ∀ m : ℝ, 1 / 100 ≤ m → m ≤ 2523 / 204800 →
    0 ≤ doubleCapLowResidual m := by
  intro m hmLo hmHi
  by_cases h0000 : m ≤ (823 / 81920 : ℝ)
  · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0000.accepted_cell m (by linarith [hmLo]) h0000
  ·
    by_cases h0001 : m ≤ (2067 / 204800 : ℝ)
    · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0001.accepted_cell m (by linarith [(lt_of_not_ge h0000).le]) h0001
    ·
      by_cases h0002 : m ≤ (4153 / 409600 : ℝ)
      · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0002.accepted_cell m (by linarith [(lt_of_not_ge h0001).le]) h0002
      ·
        by_cases h0003 : m ≤ (1043 / 102400 : ℝ)
        · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0003.accepted_cell m (by linarith [(lt_of_not_ge h0002).le]) h0003
        ·
          by_cases h0004 : m ≤ (4191 / 409600 : ℝ)
          · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0004.accepted_cell m (by linarith [(lt_of_not_ge h0003).le]) h0004
          ·
            by_cases h0005 : m ≤ (421 / 40960 : ℝ)
            · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0005.accepted_cell m (by linarith [(lt_of_not_ge h0004).le]) h0005
            ·
              by_cases h0006 : m ≤ (4229 / 409600 : ℝ)
              · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0006.accepted_cell m (by linarith [(lt_of_not_ge h0005).le]) h0006
              ·
                by_cases h0007 : m ≤ (531 / 51200 : ℝ)
                · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0007.accepted_cell m (by linarith [(lt_of_not_ge h0006).le]) h0007
                ·
                  by_cases h0008 : m ≤ (4267 / 409600 : ℝ)
                  · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0008.accepted_cell m (by linarith [(lt_of_not_ge h0007).le]) h0008
                  ·
                    by_cases h0009 : m ≤ (2143 / 204800 : ℝ)
                    · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0009.accepted_cell m (by linarith [(lt_of_not_ge h0008).le]) h0009
                    ·
                      by_cases h0010 : m ≤ (861 / 81920 : ℝ)
                      · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0010.accepted_cell m (by linarith [(lt_of_not_ge h0009).le]) h0010
                      ·
                        by_cases h0011 : m ≤ (1081 / 102400 : ℝ)
                        · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0011.accepted_cell m (by linarith [(lt_of_not_ge h0010).le]) h0011
                        ·
                          by_cases h0012 : m ≤ (4343 / 409600 : ℝ)
                          · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0012.accepted_cell m (by linarith [(lt_of_not_ge h0011).le]) h0012
                          ·
                            by_cases h0013 : m ≤ (2181 / 204800 : ℝ)
                            · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0013.accepted_cell m (by linarith [(lt_of_not_ge h0012).le]) h0013
                            ·
                              by_cases h0014 : m ≤ (11 / 1024 : ℝ)
                              · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0014.accepted_cell m (by linarith [(lt_of_not_ge h0013).le]) h0014
                              ·
                                by_cases h0015 : m ≤ (2219 / 204800 : ℝ)
                                · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0015.accepted_cell m (by linarith [(lt_of_not_ge h0014).le]) h0015
                                ·
                                  by_cases h0016 : m ≤ (1119 / 102400 : ℝ)
                                  · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0016.accepted_cell m (by linarith [(lt_of_not_ge h0015).le]) h0016
                                  ·
                                    by_cases h0017 : m ≤ (2257 / 204800 : ℝ)
                                    · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0017.accepted_cell m (by linarith [(lt_of_not_ge h0016).le]) h0017
                                    ·
                                      by_cases h0018 : m ≤ (569 / 51200 : ℝ)
                                      · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0018.accepted_cell m (by linarith [(lt_of_not_ge h0017).le]) h0018
                                      ·
                                        by_cases h0019 : m ≤ (459 / 40960 : ℝ)
                                        · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0019.accepted_cell m (by linarith [(lt_of_not_ge h0018).le]) h0019
                                        ·
                                          by_cases h0020 : m ≤ (1157 / 102400 : ℝ)
                                          · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0020.accepted_cell m (by linarith [(lt_of_not_ge h0019).le]) h0020
                                          ·
                                            by_cases h0021 : m ≤ (2333 / 204800 : ℝ)
                                            · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0021.accepted_cell m (by linarith [(lt_of_not_ge h0020).le]) h0021
                                            ·
                                              by_cases h0022 : m ≤ (147 / 12800 : ℝ)
                                              · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0022.accepted_cell m (by linarith [(lt_of_not_ge h0021).le]) h0022
                                              ·
                                                by_cases h0023 : m ≤ (2371 / 204800 : ℝ)
                                                · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0023.accepted_cell m (by linarith [(lt_of_not_ge h0022).le]) h0023
                                                ·
                                                  by_cases h0024 : m ≤ (239 / 20480 : ℝ)
                                                  · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0024.accepted_cell m (by linarith [(lt_of_not_ge h0023).le]) h0024
                                                  ·
                                                    by_cases h0025 : m ≤ (2409 / 204800 : ℝ)
                                                    · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0025.accepted_cell m (by linarith [(lt_of_not_ge h0024).le]) h0025
                                                    ·
                                                      by_cases h0026 : m ≤ (607 / 51200 : ℝ)
                                                      · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0026.accepted_cell m (by linarith [(lt_of_not_ge h0025).le]) h0026
                                                      ·
                                                        by_cases h0027 : m ≤ (2447 / 204800 : ℝ)
                                                        · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0027.accepted_cell m (by linarith [(lt_of_not_ge h0026).le]) h0027
                                                        ·
                                                          by_cases h0028 : m ≤ (1233 / 102400 : ℝ)
                                                          · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0028.accepted_cell m (by linarith [(lt_of_not_ge h0027).le]) h0028
                                                          ·
                                                            by_cases h0029 : m ≤ (497 / 40960 : ℝ)
                                                            · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0029.accepted_cell m (by linarith [(lt_of_not_ge h0028).le]) h0029
                                                            ·
                                                              by_cases h0030 : m ≤ (313 / 25600 : ℝ)
                                                              · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0030.accepted_cell m (by linarith [(lt_of_not_ge h0029).le]) h0030
                                                              ·
                                                                exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0031.accepted_cell m (by linarith [(lt_of_not_ge h0030).le]) hmHi

#print axioms cover
end GeneralCK.Certificates.DoubleCapLowMiddleAggregation.Part000

end


