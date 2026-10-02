-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_FullCertificate
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_FullCertificate
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T06:51:02.996202+00:00
-- url     : https://prove2.me/theorems/faf0c970-0db3-4d08-ae8a-c5e53f52c676
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.FullCertificate` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.FullCertificate` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.FullCertificate` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.FullCertificate (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/FullCertificate.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage000__28
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage028__18
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage046__21
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage067__4

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.FullCertificate =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
theorem group_cover_0_1 {a z : ℝ} (ha : a ∈ Set.Icc (3 / 20) (383 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((379 / 2500):ℝ) with hl | hr
  · exact cover_0_15 ⟨ha.1,hl⟩ hz
  · exact cover_16_31 ⟨hr,ha.2⟩ hz
theorem group_cover_2_3 {a z : ℝ} (ha : a ∈ Set.Icc (383 / 2500) (391 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((387 / 2500):ℝ) with hl | hr
  · exact cover_32_47 ⟨ha.1,hl⟩ hz
  · exact cover_48_63 ⟨hr,ha.2⟩ hz
theorem group_cover_0_3 {a z : ℝ} (ha : a ∈ Set.Icc (3 / 20) (391 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((383 / 2500):ℝ) with hl | hr
  · exact group_cover_0_1 ⟨ha.1,hl⟩ hz
  · exact group_cover_2_3 ⟨hr,ha.2⟩ hz
theorem group_cover_4_5 {a z : ℝ} (ha : a ∈ Set.Icc (391 / 2500) (399 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((79 / 500):ℝ) with hl | hr
  · exact cover_64_79 ⟨ha.1,hl⟩ hz
  · exact cover_80_95 ⟨hr,ha.2⟩ hz
theorem group_cover_6_7 {a z : ℝ} (ha : a ∈ Set.Icc (399 / 2500) (407 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((403 / 2500):ℝ) with hl | hr
  · exact cover_96_111 ⟨ha.1,hl⟩ hz
  · exact cover_112_127 ⟨hr,ha.2⟩ hz
theorem group_cover_4_7 {a z : ℝ} (ha : a ∈ Set.Icc (391 / 2500) (407 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((399 / 2500):ℝ) with hl | hr
  · exact group_cover_4_5 ⟨ha.1,hl⟩ hz
  · exact group_cover_6_7 ⟨hr,ha.2⟩ hz
theorem group_cover_0_7 {a z : ℝ} (ha : a ∈ Set.Icc (3 / 20) (407 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((391 / 2500):ℝ) with hl | hr
  · exact group_cover_0_3 ⟨ha.1,hl⟩ hz
  · exact group_cover_4_7 ⟨hr,ha.2⟩ hz
theorem group_cover_8_9 {a z : ℝ} (ha : a ∈ Set.Icc (407 / 2500) (83 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((411 / 2500):ℝ) with hl | hr
  · exact cover_128_143 ⟨ha.1,hl⟩ hz
  · exact cover_144_159 ⟨hr,ha.2⟩ hz
theorem group_cover_10_11 {a z : ℝ} (ha : a ∈ Set.Icc (83 / 500) (423 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((419 / 2500):ℝ) with hl | hr
  · exact cover_160_175 ⟨ha.1,hl⟩ hz
  · exact cover_176_191 ⟨hr,ha.2⟩ hz
theorem group_cover_8_11 {a z : ℝ} (ha : a ∈ Set.Icc (407 / 2500) (423 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((83 / 500):ℝ) with hl | hr
  · exact group_cover_8_9 ⟨ha.1,hl⟩ hz
  · exact group_cover_10_11 ⟨hr,ha.2⟩ hz
theorem group_cover_12_13 {a z : ℝ} (ha : a ∈ Set.Icc (423 / 2500) (431 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((427 / 2500):ℝ) with hl | hr
  · exact cover_192_207 ⟨ha.1,hl⟩ hz
  · exact cover_208_223 ⟨hr,ha.2⟩ hz
theorem group_cover_15_16 {a z : ℝ} (ha : a ∈ Set.Icc (87 / 500) (443 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((439 / 2500):ℝ) with hl | hr
  · exact cover_240_255 ⟨ha.1,hl⟩ hz
  · exact cover_256_271 ⟨hr,ha.2⟩ hz
theorem group_cover_14_16 {a z : ℝ} (ha : a ∈ Set.Icc (431 / 2500) (443 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((87 / 500):ℝ) with hl | hr
  · exact cover_224_239 ⟨ha.1,hl⟩ hz
  · exact group_cover_15_16 ⟨hr,ha.2⟩ hz
theorem group_cover_12_16 {a z : ℝ} (ha : a ∈ Set.Icc (423 / 2500) (443 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((431 / 2500):ℝ) with hl | hr
  · exact group_cover_12_13 ⟨ha.1,hl⟩ hz
  · exact group_cover_14_16 ⟨hr,ha.2⟩ hz
theorem group_cover_8_16 {a z : ℝ} (ha : a ∈ Set.Icc (407 / 2500) (443 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((423 / 2500):ℝ) with hl | hr
  · exact group_cover_8_11 ⟨ha.1,hl⟩ hz
  · exact group_cover_12_16 ⟨hr,ha.2⟩ hz
theorem group_cover_0_16 {a z : ℝ} (ha : a ∈ Set.Icc (3 / 20) (443 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((407 / 2500):ℝ) with hl | hr
  · exact group_cover_0_7 ⟨ha.1,hl⟩ hz
  · exact group_cover_8_16 ⟨hr,ha.2⟩ hz
theorem group_cover_17_18 {a z : ℝ} (ha : a ∈ Set.Icc (443 / 2500) (451 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((447 / 2500):ℝ) with hl | hr
  · exact cover_272_287 ⟨ha.1,hl⟩ hz
  · exact cover_288_303 ⟨hr,ha.2⟩ hz
theorem group_cover_19_20 {a z : ℝ} (ha : a ∈ Set.Icc (451 / 2500) (459 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((91 / 500):ℝ) with hl | hr
  · exact cover_304_319 ⟨ha.1,hl⟩ hz
  · exact cover_320_335 ⟨hr,ha.2⟩ hz
theorem group_cover_17_20 {a z : ℝ} (ha : a ∈ Set.Icc (443 / 2500) (459 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((451 / 2500):ℝ) with hl | hr
  · exact group_cover_17_18 ⟨ha.1,hl⟩ hz
  · exact group_cover_19_20 ⟨hr,ha.2⟩ hz
theorem group_cover_21_22 {a z : ℝ} (ha : a ∈ Set.Icc (459 / 2500) (467 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((463 / 2500):ℝ) with hl | hr
  · exact cover_336_351 ⟨ha.1,hl⟩ hz
  · exact cover_352_367 ⟨hr,ha.2⟩ hz
theorem group_cover_24_25 {a z : ℝ} (ha : a ∈ Set.Icc (471 / 2500) (479 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((19 / 100):ℝ) with hl | hr
  · exact cover_384_399 ⟨ha.1,hl⟩ hz
  · exact cover_400_415 ⟨hr,ha.2⟩ hz
theorem group_cover_23_25 {a z : ℝ} (ha : a ∈ Set.Icc (467 / 2500) (479 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((471 / 2500):ℝ) with hl | hr
  · exact cover_368_383 ⟨ha.1,hl⟩ hz
  · exact group_cover_24_25 ⟨hr,ha.2⟩ hz
theorem group_cover_21_25 {a z : ℝ} (ha : a ∈ Set.Icc (459 / 2500) (479 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((467 / 2500):ℝ) with hl | hr
  · exact group_cover_21_22 ⟨ha.1,hl⟩ hz
  · exact group_cover_23_25 ⟨hr,ha.2⟩ hz
theorem group_cover_17_25 {a z : ℝ} (ha : a ∈ Set.Icc (443 / 2500) (479 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((459 / 2500):ℝ) with hl | hr
  · exact group_cover_17_20 ⟨ha.1,hl⟩ hz
  · exact group_cover_21_25 ⟨hr,ha.2⟩ hz
theorem group_cover_26_27 {a z : ℝ} (ha : a ∈ Set.Icc (479 / 2500) (487 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((483 / 2500):ℝ) with hl | hr
  · exact cover_416_431 ⟨ha.1,hl⟩ hz
  · exact cover_432_447 ⟨hr,ha.2⟩ hz
theorem group_cover_28_29 {a z : ℝ} (ha : a ∈ Set.Icc (487 / 2500) (99 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((491 / 2500):ℝ) with hl | hr
  · exact cover_448_463 ⟨ha.1,hl⟩ hz
  · exact cover_464_479 ⟨hr,ha.2⟩ hz
theorem group_cover_26_29 {a z : ℝ} (ha : a ∈ Set.Icc (479 / 2500) (99 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((487 / 2500):ℝ) with hl | hr
  · exact group_cover_26_27 ⟨ha.1,hl⟩ hz
  · exact group_cover_28_29 ⟨hr,ha.2⟩ hz
theorem group_cover_30_31 {a z : ℝ} (ha : a ∈ Set.Icc (99 / 500) (103 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((499 / 2500):ℝ) with hl | hr
  · exact cover_480_495 ⟨ha.1,hl⟩ hz
  · exact cover_496_511 ⟨hr,ha.2⟩ hz
theorem group_cover_33_34 {a z : ℝ} (ha : a ∈ Set.Icc (107 / 500) (23 / 100))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((111 / 500):ℝ) with hl | hr
  · exact cover_528_543 ⟨ha.1,hl⟩ hz
  · exact cover_544_559 ⟨hr,ha.2⟩ hz
theorem group_cover_32_34 {a z : ℝ} (ha : a ∈ Set.Icc (103 / 500) (23 / 100))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((107 / 500):ℝ) with hl | hr
  · exact cover_512_527 ⟨ha.1,hl⟩ hz
  · exact group_cover_33_34 ⟨hr,ha.2⟩ hz
theorem group_cover_30_34 {a z : ℝ} (ha : a ∈ Set.Icc (99 / 500) (23 / 100))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((103 / 500):ℝ) with hl | hr
  · exact group_cover_30_31 ⟨ha.1,hl⟩ hz
  · exact group_cover_32_34 ⟨hr,ha.2⟩ hz
theorem group_cover_26_34 {a z : ℝ} (ha : a ∈ Set.Icc (479 / 2500) (23 / 100))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((99 / 500):ℝ) with hl | hr
  · exact group_cover_26_29 ⟨ha.1,hl⟩ hz
  · exact group_cover_30_34 ⟨hr,ha.2⟩ hz
theorem group_cover_17_34 {a z : ℝ} (ha : a ∈ Set.Icc (443 / 2500) (23 / 100))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((479 / 2500):ℝ) with hl | hr
  · exact group_cover_17_25 ⟨ha.1,hl⟩ hz
  · exact group_cover_26_34 ⟨hr,ha.2⟩ hz
theorem group_cover_0_34 {a z : ℝ} (ha : a ∈ Set.Icc (3 / 20) (23 / 100))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((443 / 2500):ℝ) with hl | hr
  · exact group_cover_0_16 ⟨ha.1,hl⟩ hz
  · exact group_cover_17_34 ⟨hr,ha.2⟩ hz
theorem group_cover_35_36 {a z : ℝ} (ha : a ∈ Set.Icc (23 / 100) (123 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((119 / 500):ℝ) with hl | hr
  · exact cover_560_575 ⟨ha.1,hl⟩ hz
  · exact cover_576_591 ⟨hr,ha.2⟩ hz
theorem group_cover_37_38 {a z : ℝ} (ha : a ∈ Set.Icc (123 / 500) (131 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((127 / 500):ℝ) with hl | hr
  · exact cover_592_607 ⟨ha.1,hl⟩ hz
  · exact cover_608_623 ⟨hr,ha.2⟩ hz
theorem group_cover_35_38 {a z : ℝ} (ha : a ∈ Set.Icc (23 / 100) (131 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((123 / 500):ℝ) with hl | hr
  · exact group_cover_35_36 ⟨ha.1,hl⟩ hz
  · exact group_cover_37_38 ⟨hr,ha.2⟩ hz
theorem group_cover_39_40 {a z : ℝ} (ha : a ∈ Set.Icc (131 / 500) (139 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((27 / 100):ℝ) with hl | hr
  · exact cover_624_639 ⟨ha.1,hl⟩ hz
  · exact cover_640_655 ⟨hr,ha.2⟩ hz
theorem group_cover_42_43 {a z : ℝ} (ha : a ∈ Set.Icc (143 / 500) (38 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((147 / 500):ℝ) with hl | hr
  · exact cover_672_687 ⟨ha.1,hl⟩ hz
  · exact cover_688_703 ⟨hr,ha.2⟩ hz
theorem group_cover_41_43 {a z : ℝ} (ha : a ∈ Set.Icc (139 / 500) (38 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((143 / 500):ℝ) with hl | hr
  · exact cover_656_671 ⟨ha.1,hl⟩ hz
  · exact group_cover_42_43 ⟨hr,ha.2⟩ hz
theorem group_cover_39_43 {a z : ℝ} (ha : a ∈ Set.Icc (131 / 500) (38 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((139 / 500):ℝ) with hl | hr
  · exact group_cover_39_40 ⟨ha.1,hl⟩ hz
  · exact group_cover_41_43 ⟨hr,ha.2⟩ hz
theorem group_cover_35_43 {a z : ℝ} (ha : a ∈ Set.Icc (23 / 100) (38 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((131 / 500):ℝ) with hl | hr
  · exact group_cover_35_38 ⟨ha.1,hl⟩ hz
  · exact group_cover_39_43 ⟨hr,ha.2⟩ hz
theorem group_cover_44_45 {a z : ℝ} (ha : a ∈ Set.Icc (38 / 125) (42 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((8 / 25):ℝ) with hl | hr
  · exact cover_704_719 ⟨ha.1,hl⟩ hz
  · exact cover_720_735 ⟨hr,ha.2⟩ hz
theorem group_cover_46_47 {a z : ℝ} (ha : a ∈ Set.Icc (42 / 125) (46 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((44 / 125):ℝ) with hl | hr
  · exact cover_736_751 ⟨ha.1,hl⟩ hz
  · exact cover_752_767 ⟨hr,ha.2⟩ hz
theorem group_cover_44_47 {a z : ℝ} (ha : a ∈ Set.Icc (38 / 125) (46 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((42 / 125):ℝ) with hl | hr
  · exact group_cover_44_45 ⟨ha.1,hl⟩ hz
  · exact group_cover_46_47 ⟨hr,ha.2⟩ hz
theorem group_cover_48_49 {a z : ℝ} (ha : a ∈ Set.Icc (46 / 125) (2 / 5))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((48 / 125):ℝ) with hl | hr
  · exact cover_768_783 ⟨ha.1,hl⟩ hz
  · exact cover_784_799 ⟨hr,ha.2⟩ hz
theorem group_cover_51_52 {a z : ℝ} (ha : a ∈ Set.Icc (52 / 125) (56 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((54 / 125):ℝ) with hl | hr
  · exact cover_816_831 ⟨ha.1,hl⟩ hz
  · exact cover_832_847 ⟨hr,ha.2⟩ hz
theorem group_cover_50_52 {a z : ℝ} (ha : a ∈ Set.Icc (2 / 5) (56 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((52 / 125):ℝ) with hl | hr
  · exact cover_800_815 ⟨ha.1,hl⟩ hz
  · exact group_cover_51_52 ⟨hr,ha.2⟩ hz
theorem group_cover_48_52 {a z : ℝ} (ha : a ∈ Set.Icc (46 / 125) (56 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((2 / 5):ℝ) with hl | hr
  · exact group_cover_48_49 ⟨ha.1,hl⟩ hz
  · exact group_cover_50_52 ⟨hr,ha.2⟩ hz
theorem group_cover_44_52 {a z : ℝ} (ha : a ∈ Set.Icc (38 / 125) (56 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((46 / 125):ℝ) with hl | hr
  · exact group_cover_44_47 ⟨ha.1,hl⟩ hz
  · exact group_cover_48_52 ⟨hr,ha.2⟩ hz
theorem group_cover_35_52 {a z : ℝ} (ha : a ∈ Set.Icc (23 / 100) (56 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((38 / 125):ℝ) with hl | hr
  · exact group_cover_35_43 ⟨ha.1,hl⟩ hz
  · exact group_cover_44_52 ⟨hr,ha.2⟩ hz
theorem group_cover_53_54 {a z : ℝ} (ha : a ∈ Set.Icc (56 / 125) (12 / 25))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((58 / 125):ℝ) with hl | hr
  · exact cover_848_863 ⟨ha.1,hl⟩ hz
  · exact cover_864_879 ⟨hr,ha.2⟩ hz
theorem group_cover_55_56 {a z : ℝ} (ha : a ∈ Set.Icc (12 / 25) (67 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((62 / 125):ℝ) with hl | hr
  · exact cover_880_895 ⟨ha.1,hl⟩ hz
  · exact cover_896_911 ⟨hr,ha.2⟩ hz
theorem group_cover_53_56 {a z : ℝ} (ha : a ∈ Set.Icc (56 / 125) (67 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((12 / 25):ℝ) with hl | hr
  · exact group_cover_53_54 ⟨ha.1,hl⟩ hz
  · exact group_cover_55_56 ⟨hr,ha.2⟩ hz
theorem group_cover_57_58 {a z : ℝ} (ha : a ∈ Set.Icc (67 / 125) (79 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((73 / 125):ℝ) with hl | hr
  · exact cover_912_927 ⟨ha.1,hl⟩ hz
  · exact cover_928_943 ⟨hr,ha.2⟩ hz
theorem group_cover_60_61 {a z : ℝ} (ha : a ∈ Set.Icc (17 / 25) (97 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((91 / 125):ℝ) with hl | hr
  · exact cover_960_975 ⟨ha.1,hl⟩ hz
  · exact cover_976_991 ⟨hr,ha.2⟩ hz
theorem group_cover_59_61 {a z : ℝ} (ha : a ∈ Set.Icc (79 / 125) (97 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((17 / 25):ℝ) with hl | hr
  · exact cover_944_959 ⟨ha.1,hl⟩ hz
  · exact group_cover_60_61 ⟨hr,ha.2⟩ hz
theorem group_cover_57_61 {a z : ℝ} (ha : a ∈ Set.Icc (67 / 125) (97 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((79 / 125):ℝ) with hl | hr
  · exact group_cover_57_58 ⟨ha.1,hl⟩ hz
  · exact group_cover_59_61 ⟨hr,ha.2⟩ hz
theorem group_cover_53_61 {a z : ℝ} (ha : a ∈ Set.Icc (56 / 125) (97 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((67 / 125):ℝ) with hl | hr
  · exact group_cover_53_56 ⟨ha.1,hl⟩ hz
  · exact group_cover_57_61 ⟨hr,ha.2⟩ hz
theorem group_cover_62_63 {a z : ℝ} (ha : a ∈ Set.Icc (97 / 125) (109 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((103 / 125):ℝ) with hl | hr
  · exact cover_992_1007 ⟨ha.1,hl⟩ hz
  · exact cover_1008_1023 ⟨hr,ha.2⟩ hz
theorem group_cover_64_65 {a z : ℝ} (ha : a ∈ Set.Icc (109 / 125) (239 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((23 / 25):ℝ) with hl | hr
  · exact cover_1024_1039 ⟨ha.1,hl⟩ hz
  · exact cover_1040_1055 ⟨hr,ha.2⟩ hz
theorem group_cover_62_65 {a z : ℝ} (ha : a ∈ Set.Icc (97 / 125) (239 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((109 / 125):ℝ) with hl | hr
  · exact group_cover_62_63 ⟨ha.1,hl⟩ hz
  · exact group_cover_64_65 ⟨hr,ha.2⟩ hz
theorem group_cover_66_67 {a z : ℝ} (ha : a ∈ Set.Icc (239 / 250) (247 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((243 / 250):ℝ) with hl | hr
  · exact cover_1056_1071 ⟨ha.1,hl⟩ hz
  · exact cover_1072_1087 ⟨hr,ha.2⟩ hz
theorem group_cover_69_70 {a z : ℝ} (ha : a ∈ Set.Icc (1241 / 1250) (999 / 1000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((249 / 250):ℝ) with hl | hr
  · exact cover_1104_1119 ⟨ha.1,hl⟩ hz
  · exact cover_1120_1134 ⟨hr,ha.2⟩ hz
theorem group_cover_68_70 {a z : ℝ} (ha : a ∈ Set.Icc (247 / 250) (999 / 1000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1241 / 1250):ℝ) with hl | hr
  · exact cover_1088_1103 ⟨ha.1,hl⟩ hz
  · exact group_cover_69_70 ⟨hr,ha.2⟩ hz
theorem group_cover_66_70 {a z : ℝ} (ha : a ∈ Set.Icc (239 / 250) (999 / 1000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((247 / 250):ℝ) with hl | hr
  · exact group_cover_66_67 ⟨ha.1,hl⟩ hz
  · exact group_cover_68_70 ⟨hr,ha.2⟩ hz
theorem group_cover_62_70 {a z : ℝ} (ha : a ∈ Set.Icc (97 / 125) (999 / 1000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((239 / 250):ℝ) with hl | hr
  · exact group_cover_62_65 ⟨ha.1,hl⟩ hz
  · exact group_cover_66_70 ⟨hr,ha.2⟩ hz
theorem group_cover_53_70 {a z : ℝ} (ha : a ∈ Set.Icc (56 / 125) (999 / 1000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((97 / 125):ℝ) with hl | hr
  · exact group_cover_53_61 ⟨ha.1,hl⟩ hz
  · exact group_cover_62_70 ⟨hr,ha.2⟩ hz
theorem group_cover_35_70 {a z : ℝ} (ha : a ∈ Set.Icc (23 / 100) (999 / 1000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((56 / 125):ℝ) with hl | hr
  · exact group_cover_35_52 ⟨ha.1,hl⟩ hz
  · exact group_cover_53_70 ⟨hr,ha.2⟩ hz
theorem group_cover_0_70 {a z : ℝ} (ha : a ∈ Set.Icc (3 / 20) (999 / 1000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((23 / 100):ℝ) with hl | hr
  · exact group_cover_0_34 ⟨ha.1,hl⟩ hz
  · exact group_cover_35_70 ⟨hr,ha.2⟩ hz

theorem full_low_ratio_strip {a z : ℝ} (ha : a ∈ Set.Icc (3/20:ℝ) (999/1000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) :=
  group_cover_0_70 ha hz

end GeneralCK.Certificates.LowRatioFamily

end


