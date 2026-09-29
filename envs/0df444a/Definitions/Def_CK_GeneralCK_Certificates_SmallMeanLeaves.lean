-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_SmallMeanLeaves
-- name    : CK_GeneralCK_Certificates_SmallMeanLeaves
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:27:24.751061+00:00
-- url     : https://prove2.me/theorems/7ba932be-af34-4dd2-ac29-78fe9367149e
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.SmallMeanLeaves` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.SmallMeanLeaves` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.SmallMeanLeaves` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.SmallMeanLeaves (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/SmallMeanLeaves.lean)

import Definitions.Def_CK_GeneralCK_Certificates_SmallMeanEntropy

namespace GeneralCK.Certificates.SmallMean

theorem gamma_lower_0 : (2240782009 / 1000000000) ≤ gammaExpr (7 / 32) := by
  exact gamma_lower (e := (965201697 / 1000000000)) (by norm_num) (by norm_num)
    (by convert! entropy_22.1 using 1; norm_num) (by norm_num) (by norm_num)

theorem leaf_0 (gamma : ℝ → ℝ) (hmono : AntitoneOn gamma (Set.Ioc 0 1))
    (heq : gamma = gammaExpr) (r : ℝ) (hl : (1 / 6) ≤ r) (hu : r ≤ (7 / 32)) :
    0 < W gamma r := by
  exact leaf_sound gamma hmono (l := (1 / 6)) (u := (7 / 32)) (g := (2240782009 / 1000000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    (by rw [heq]; exact gamma_lower_0) (by norm_num) (by norm_num)

theorem gamma_lower_1 : (43750257 / 20000000) ≤ gammaExpr (47 / 192) := by
  exact gamma_lower (e := (956332329 / 1000000000)) (by norm_num) (by norm_num)
    (by convert! entropy_21.1 using 1; norm_num) (by norm_num) (by norm_num)

theorem leaf_1 (gamma : ℝ → ℝ) (hmono : AntitoneOn gamma (Set.Ioc 0 1))
    (heq : gamma = gammaExpr) (r : ℝ) (hl : (7 / 32) ≤ r) (hu : r ≤ (47 / 192)) :
    0 < W gamma r := by
  exact leaf_sound gamma hmono (l := (7 / 32)) (u := (47 / 192)) (g := (43750257 / 20000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    (by rw [heq]; exact gamma_lower_1) (by norm_num) (by norm_num)

theorem gamma_lower_2 : (1067952091 / 500000000) ≤ gammaExpr (13 / 48) := by
  exact gamma_lower (e := (946422049 / 1000000000)) (by norm_num) (by norm_num)
    (by convert! entropy_20.1 using 1; norm_num) (by norm_num) (by norm_num)

theorem leaf_2 (gamma : ℝ → ℝ) (hmono : AntitoneOn gamma (Set.Ioc 0 1))
    (heq : gamma = gammaExpr) (r : ℝ) (hl : (47 / 192) ≤ r) (hu : r ≤ (13 / 48)) :
    0 < W gamma r := by
  exact leaf_sound gamma hmono (l := (47 / 192)) (u := (13 / 48)) (g := (1067952091 / 500000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    (by rw [heq]; exact gamma_lower_2) (by norm_num) (by norm_num)

theorem gamma_lower_3 : (2110688077 / 1000000000) ≤ gammaExpr (109 / 384) := by
  exact gamma_lower (e := (117633991 / 125000000)) (by norm_num) (by norm_num)
    (by convert! entropy_19.1 using 1; norm_num) (by norm_num) (by norm_num)

theorem leaf_3 (gamma : ℝ → ℝ) (hmono : AntitoneOn gamma (Set.Ioc 0 1))
    (heq : gamma = gammaExpr) (r : ℝ) (hl : (13 / 48) ≤ r) (hu : r ≤ (109 / 384)) :
    0 < W gamma r := by
  exact leaf_sound gamma hmono (l := (13 / 48)) (u := (109 / 384)) (g := (2110688077 / 1000000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    (by rw [heq]; exact gamma_lower_3) (by norm_num) (by norm_num)

theorem gamma_lower_4 : (104292333 / 50000000) ≤ gammaExpr (19 / 64) := by
  exact gamma_lower (e := (935455763 / 1000000000)) (by norm_num) (by norm_num)
    (by convert! entropy_18.1 using 1; norm_num) (by norm_num) (by norm_num)

theorem leaf_4 (gamma : ℝ → ℝ) (hmono : AntitoneOn gamma (Set.Ioc 0 1))
    (heq : gamma = gammaExpr) (r : ℝ) (hl : (109 / 384) ≤ r) (hu : r ≤ (19 / 64)) :
    0 < W gamma r := by
  exact leaf_sound gamma hmono (l := (109 / 384)) (u := (19 / 64)) (g := (104292333 / 50000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    (by rw [heq]; exact gamma_lower_4) (by norm_num) (by norm_num)

theorem gamma_lower_5 : (1030683701 / 500000000) ≤ gammaExpr (119 / 384) := by
  exact gamma_lower (e := (232392837 / 250000000)) (by norm_num) (by norm_num)
    (by convert! entropy_17.1 using 1; norm_num) (by norm_num) (by norm_num)

theorem leaf_5 (gamma : ℝ → ℝ) (hmono : AntitoneOn gamma (Set.Ioc 0 1))
    (heq : gamma = gammaExpr) (r : ℝ) (hl : (19 / 64) ≤ r) (hu : r ≤ (119 / 384)) :
    0 < W gamma r := by
  exact leaf_sound gamma hmono (l := (19 / 64)) (u := (119 / 384)) (g := (1030683701 / 500000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    (by rw [heq]; exact gamma_lower_5) (by norm_num) (by norm_num)

theorem gamma_lower_6 : (509309529 / 250000000) ≤ gammaExpr (31 / 96) := by
  exact gamma_lower (e := (923416337 / 1000000000)) (by norm_num) (by norm_num)
    (by convert! entropy_16.1 using 1; norm_num) (by norm_num) (by norm_num)

theorem leaf_6 (gamma : ℝ → ℝ) (hmono : AntitoneOn gamma (Set.Ioc 0 1))
    (heq : gamma = gammaExpr) (r : ℝ) (hl : (119 / 384) ≤ r) (hu : r ≤ (31 / 96)) :
    0 < W gamma r := by
  exact leaf_sound gamma hmono (l := (119 / 384)) (u := (31 / 96)) (g := (509309529 / 250000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    (by rw [heq]; exact gamma_lower_6) (by norm_num) (by norm_num)

theorem gamma_lower_7 : (503361761 / 250000000) ≤ gammaExpr (43 / 128) := by
  exact gamma_lower (e := (916988241 / 1000000000)) (by norm_num) (by norm_num)
    (by convert! entropy_15.1 using 1; norm_num) (by norm_num) (by norm_num)

theorem leaf_7 (gamma : ℝ → ℝ) (hmono : AntitoneOn gamma (Set.Ioc 0 1))
    (heq : gamma = gammaExpr) (r : ℝ) (hl : (31 / 96) ≤ r) (hu : r ≤ (43 / 128)) :
    0 < W gamma r := by
  exact leaf_sound gamma hmono (l := (31 / 96)) (u := (43 / 128)) (g := (503361761 / 250000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    (by rw [heq]; exact gamma_lower_7) (by norm_num) (by norm_num)

theorem gamma_lower_8 : (99499139 / 50000000) ≤ gammaExpr (67 / 192) := by
  exact gamma_lower (e := (45514221 / 50000000)) (by norm_num) (by norm_num)
    (by convert! entropy_14.1 using 1; norm_num) (by norm_num) (by norm_num)

theorem leaf_8 (gamma : ℝ → ℝ) (hmono : AntitoneOn gamma (Set.Ioc 0 1))
    (heq : gamma = gammaExpr) (r : ℝ) (hl : (43 / 128) ≤ r) (hu : r ≤ (67 / 192)) :
    0 < W gamma r := by
  exact leaf_sound gamma hmono (l := (43 / 128)) (u := (67 / 192)) (g := (99499139 / 50000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    (by rw [heq]; exact gamma_lower_8) (by norm_num) (by norm_num)

theorem gamma_lower_9 : (983417099 / 500000000) ≤ gammaExpr (139 / 384) := by
  exact gamma_lower (e := (903302073 / 1000000000)) (by norm_num) (by norm_num)
    (by convert! entropy_13.1 using 1; norm_num) (by norm_num) (by norm_num)

theorem leaf_9 (gamma : ℝ → ℝ) (hmono : AntitoneOn gamma (Set.Ioc 0 1))
    (heq : gamma = gammaExpr) (r : ℝ) (hl : (67 / 192) ≤ r) (hu : r ≤ (139 / 384)) :
    0 < W gamma r := by
  exact leaf_sound gamma hmono (l := (67 / 192)) (u := (139 / 384)) (g := (983417099 / 500000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    (by rw [heq]; exact gamma_lower_9) (by norm_num) (by norm_num)

theorem gamma_lower_10 : (1943990469 / 1000000000) ≤ gammaExpr (3 / 8) := by
  exact gamma_lower (e := (896038231 / 1000000000)) (by norm_num) (by norm_num)
    (by convert! entropy_12.1 using 1; norm_num) (by norm_num) (by norm_num)

theorem leaf_10 (gamma : ℝ → ℝ) (hmono : AntitoneOn gamma (Set.Ioc 0 1))
    (heq : gamma = gammaExpr) (r : ℝ) (hl : (139 / 384) ≤ r) (hu : r ≤ (3 / 8)) :
    0 < W gamma r := by
  exact leaf_sound gamma hmono (l := (139 / 384)) (u := (3 / 8)) (g := (1943990469 / 1000000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    (by rw [heq]; exact gamma_lower_10) (by norm_num) (by norm_num)

theorem gamma_lower_11 : (949587901 / 500000000) ≤ gammaExpr (77 / 192) := by
  exact gamma_lower (e := (440326651 / 500000000)) (by norm_num) (by norm_num)
    (by convert! entropy_11.1 using 1; norm_num) (by norm_num) (by norm_num)

theorem leaf_11 (gamma : ℝ → ℝ) (hmono : AntitoneOn gamma (Set.Ioc 0 1))
    (heq : gamma = gammaExpr) (r : ℝ) (hl : (3 / 8) ≤ r) (hu : r ≤ (77 / 192)) :
    0 < W gamma r := by
  exact leaf_sound gamma hmono (l := (3 / 8)) (u := (77 / 192)) (g := (949587901 / 500000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    (by rw [heq]; exact gamma_lower_11) (by norm_num) (by norm_num)

theorem gamma_lower_12 : (1855457727 / 1000000000) ≤ gammaExpr (41 / 96) := by
  exact gamma_lower (e := (864102189 / 1000000000)) (by norm_num) (by norm_num)
    (by convert! entropy_10.1 using 1; norm_num) (by norm_num) (by norm_num)

theorem leaf_12 (gamma : ℝ → ℝ) (hmono : AntitoneOn gamma (Set.Ioc 0 1))
    (heq : gamma = gammaExpr) (r : ℝ) (hl : (77 / 192) ≤ r) (hu : r ≤ (41 / 96)) :
    0 < W gamma r := by
  exact leaf_sound gamma hmono (l := (77 / 192)) (u := (41 / 96)) (g := (1855457727 / 1000000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    (by rw [heq]; exact gamma_lower_12) (by norm_num) (by norm_num)

theorem gamma_lower_13 : (906379319 / 500000000) ≤ gammaExpr (29 / 64) := by
  exact gamma_lower (e := (846354099 / 1000000000)) (by norm_num) (by norm_num)
    (by convert! entropy_9.1 using 1; norm_num) (by norm_num) (by norm_num)

theorem leaf_13 (gamma : ℝ → ℝ) (hmono : AntitoneOn gamma (Set.Ioc 0 1))
    (heq : gamma = gammaExpr) (r : ℝ) (hl : (41 / 96) ≤ r) (hu : r ≤ (29 / 64)) :
    0 < W gamma r := by
  exact leaf_sound gamma hmono (l := (41 / 96)) (u := (29 / 64)) (g := (906379319 / 500000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    (by rw [heq]; exact gamma_lower_13) (by norm_num) (by norm_num)

theorem gamma_lower_14 : (354200797 / 200000000) ≤ gammaExpr (23 / 48) := by
  exact gamma_lower (e := (206843619 / 250000000)) (by norm_num) (by norm_num)
    (by convert! entropy_8.1 using 1; norm_num) (by norm_num) (by norm_num)

theorem leaf_14 (gamma : ℝ → ℝ) (hmono : AntitoneOn gamma (Set.Ioc 0 1))
    (heq : gamma = gammaExpr) (r : ℝ) (hl : (29 / 64) ≤ r) (hu : r ≤ (23 / 48)) :
    0 < W gamma r := by
  exact leaf_sound gamma hmono (l := (29 / 64)) (u := (23 / 48)) (g := (354200797 / 200000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    (by rw [heq]; exact gamma_lower_14) (by norm_num) (by norm_num)

theorem gamma_lower_15 : (845020181 / 500000000) ≤ gammaExpr (17 / 32) := by
  exact gamma_lower (e := (785560291 / 1000000000)) (by norm_num) (by norm_num)
    (by convert! entropy_5.1 using 1; norm_num) (by norm_num) (by norm_num)

theorem leaf_15 (gamma : ℝ → ℝ) (hmono : AntitoneOn gamma (Set.Ioc 0 1))
    (heq : gamma = gammaExpr) (r : ℝ) (hl : (23 / 48) ≤ r) (hu : r ≤ (17 / 32)) :
    0 < W gamma r := by
  exact leaf_sound gamma hmono (l := (23 / 48)) (u := (17 / 32)) (g := (845020181 / 500000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    (by rw [heq]; exact gamma_lower_15) (by norm_num) (by norm_num)

theorem gamma_lower_16 : (1612004011 / 1000000000) ≤ gammaExpr (7 / 12) := by
  exact gamma_lower (e := (11535701 / 15625000)) (by norm_num) (by norm_num)
    (by convert! entropy_4.1 using 1; norm_num) (by norm_num) (by norm_num)

theorem leaf_16 (gamma : ℝ → ℝ) (hmono : AntitoneOn gamma (Set.Ioc 0 1))
    (heq : gamma = gammaExpr) (r : ℝ) (hl : (17 / 32) ≤ r) (hu : r ≤ (7 / 12)) :
    0 < W gamma r := by
  exact leaf_sound gamma hmono (l := (17 / 32)) (u := (7 / 12)) (g := (1612004011 / 1000000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    (by rw [heq]; exact gamma_lower_16) (by norm_num) (by norm_num)

theorem gamma_lower_17 : (1462440039 / 1000000000) ≤ gammaExpr (11 / 16) := by
  exact gamma_lower (e := (625262403 / 1000000000)) (by norm_num) (by norm_num)
    (by convert! entropy_3.1 using 1; norm_num) (by norm_num) (by norm_num)

theorem leaf_17 (gamma : ℝ → ℝ) (hmono : AntitoneOn gamma (Set.Ioc 0 1))
    (heq : gamma = gammaExpr) (r : ℝ) (hl : (7 / 12) ≤ r) (hu : r ≤ (11 / 16)) :
    0 < W gamma r := by
  exact leaf_sound gamma hmono (l := (7 / 12)) (u := (11 / 16)) (g := (1462440039 / 1000000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    (by rw [heq]; exact gamma_lower_17) (by norm_num) (by norm_num)

theorem gamma_lower_18 : (1317138971 / 1000000000) ≤ gammaExpr (19 / 24) := by
  exact gamma_lower (e := (482066147 / 1000000000)) (by norm_num) (by norm_num)
    (by convert! entropy_2.1 using 1; norm_num) (by norm_num) (by norm_num)

theorem leaf_18 (gamma : ℝ → ℝ) (hmono : AntitoneOn gamma (Set.Ioc 0 1))
    (heq : gamma = gammaExpr) (r : ℝ) (hl : (11 / 16) ≤ r) (hu : r ≤ (19 / 24)) :
    0 < W gamma r := by
  exact leaf_sound gamma hmono (l := (11 / 16)) (u := (19 / 24)) (g := (1317138971 / 1000000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    (by rw [heq]; exact gamma_lower_18) (by norm_num) (by norm_num)

theorem gamma_lower_19 : (31 / 32) ≤ gammaExpr (1 / 1) := by
  exact gamma_lower (e := (0 / 1)) (by norm_num) (by norm_num)
    (by convert! entropy_0.1 using 1; norm_num) (by norm_num) (by norm_num)

theorem leaf_19 (gamma : ℝ → ℝ) (hmono : AntitoneOn gamma (Set.Ioc 0 1))
    (heq : gamma = gammaExpr) (r : ℝ) (hl : (19 / 24) ≤ r) (hu : r ≤ (1 / 1)) :
    0 < W gamma r := by
  exact leaf_sound gamma hmono (l := (19 / 24)) (u := (1 / 1)) (g := (31 / 32))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    (by rw [heq]; exact gamma_lower_19) (by norm_num) (by norm_num)

theorem gamma_sixth_gt : (23/10 : ℝ) < gammaExpr (1/6) := by
  have h := gamma_lower (r := (1/6 : ℝ)) (e := (489934377 / 500000000)) (g := (235/100 : ℝ))
    (by norm_num) (by norm_num)
    (by convert! entropy_23.1 using 1; norm_num) (by norm_num) (by norm_num)
  linarith

theorem entropy_one_over_32_lt : H (1/32) < (201/1000 : ℝ) := by
  have h := entropy_1.2
  linarith

end GeneralCK.Certificates.SmallMean


