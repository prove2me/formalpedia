-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_HighBiasCoarseBounds
-- name    : CK_GeneralCK_Certificates_Generated_HighBiasCoarseBounds
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T11:38:54.052444+00:00
-- url     : https://prove2.me/theorems/8c5e1017-2ef0-47fb-97f4-0e81fc7859f5
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.HighBiasCoarseBounds` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.HighBiasCoarseBounds` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.HighBiasCoarseBounds` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.HighBiasCoarseBounds (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/HighBiasCoarseBounds.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_HighBiasCoarseLogs

-- ===== source module GeneralCK.Certificates.Generated.HighBiasCoarseBounds =====
section
namespace GeneralCK.Certificates.HighBiasCoarse
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio GeneralCK.Reflection.HighBias
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
theorem coefficient_bounds (c e : ℝ)
    (hc : Bounds (2/5) (9/10) c) (he : Bounds (7/25) (7/20) e) :
    C2 c e≤6000 ∧ C1 c e≤8000 ∧ C0 c e≤3000 ∧ Cq c e≤210 := by
  let x0 : ℝ := Real.log (2 / 1)
  have hx0 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x0 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x1 : ℝ := (1 / 1)+(9 / 10)
  have hx1 : Bounds (19 / 10) (19 / 10) x1 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((9 / 10) : ℝ)) <;> norm_num
  let x2 : ℝ := (1 / 1)+(9 / 10)
  have hx2 : Bounds (19 / 10) (19 / 10) x2 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((9 / 10) : ℝ)) <;> norm_num
  let x3 : ℝ := Real.log x2
  have hx3 : Bounds (320926943 / 500000000) (641853887 / 1000000000) x3 := by
    exact bounds_log hx2 (by norm_num) (by simpa only [div_one] using reflection_log_1.1) (by simpa only [div_one] using reflection_log_1.2)
  let x4 : ℝ := x1*x3
  have hx4 : Bounds (6097611917 / 5000000000) (12195223853 / 10000000000) x4 := by
    apply bounds_mul hx1 hx3 <;> norm_num
  let x5 : ℝ := -(9 / 10)
  have hx5 : Bounds (-9 / 10) (-9 / 10) x5 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((9 / 10) : ℝ))
  let x6 : ℝ := (1 / 1)+x5
  have hx6 : Bounds (1 / 10) (1 / 10) x6 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx5 <;> norm_num
  let x7 : ℝ := (1 / 1)-(9 / 10)
  have hx7 : Bounds (1 / 10) (1 / 10) x7 := by
    exact hx6
  let x8 : ℝ := -(9 / 10)
  have hx8 : Bounds (-9 / 10) (-9 / 10) x8 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((9 / 10) : ℝ))
  let x9 : ℝ := (1 / 1)+x8
  have hx9 : Bounds (1 / 10) (1 / 10) x9 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx8 <;> norm_num
  let x10 : ℝ := (1 / 1)-(9 / 10)
  have hx10 : Bounds (1 / 10) (1 / 10) x10 := by
    exact hx9
  let x11 : ℝ := Real.log x10
  have hx11 : Bounds (-460517019 / 200000000) (-2302585091 / 1000000000) x11 := by
    exact bounds_log hx10 (by norm_num) (by simpa only [div_one] using reflection_log_2.1) (by simpa only [div_one] using reflection_log_2.2)
  let x12 : ℝ := x7*x11
  have hx12 : Bounds (-460517019 / 2000000000) (-2302585091 / 10000000000) x12 := by
    apply bounds_mul hx7 hx11 <;> norm_num
  let x13 : ℝ := x4+x12
  have hx13 : Bounds (9892638739 / 10000000000) (4946319381 / 5000000000) x13 := by
    apply bounds_add hx4 hx12 <;> norm_num
  let x14 : ℝ := (2 / 1)⁻¹
  have hx14 : Bounds (1 / 2) (1 / 2) x14 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x15 : ℝ := x13*x14
  have hx15 : Bounds (9892638739 / 20000000000) (4946319381 / 10000000000) x15 := by
    apply bounds_mul hx13 hx14 <;> norm_num
  let x16 : ℝ := x13/(2 / 1)
  have hx16 : Bounds (9892638739 / 20000000000) (4946319381 / 10000000000) x16 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx15
  let x17 : ℝ := -x16
  have hx17 : Bounds (-4946319381 / 10000000000) (-9892638739 / 20000000000) x17 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx16
  let x18 : ℝ := x0+x17
  have hx18 : Bounds (1985152419 / 10000000000) (3970304881 / 20000000000) x18 := by
    apply bounds_add hx0 hx17 <;> norm_num
  let x19 : ℝ := x0-x16
  have hx19 : Bounds (1985152419 / 10000000000) (3970304881 / 20000000000) x19 := by
    exact hx18
  let x20 : ℝ := biasE (9 / 10)
  have hx20 : Bounds (1985152419 / 10000000000) (3970304881 / 20000000000) x20 := by
    simpa +zetaDelta only [biasE, div_one] using hx19
  let x21 : ℝ := Real.log (2 / 1)
  have hx21 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x21 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x22 : ℝ := (1 / 1)+(2 / 5)
  have hx22 : Bounds (7 / 5) (7 / 5) x22 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((2 / 5) : ℝ)) <;> norm_num
  let x23 : ℝ := (1 / 1)+(2 / 5)
  have hx23 : Bounds (7 / 5) (7 / 5) x23 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((2 / 5) : ℝ)) <;> norm_num
  let x24 : ℝ := Real.log x23
  have hx24 : Bounds (84118059 / 250000000) (336472237 / 1000000000) x24 := by
    exact bounds_log hx23 (by norm_num) (by simpa only [div_one] using reflection_log_3.1) (by simpa only [div_one] using reflection_log_3.2)
  let x25 : ℝ := x22*x24
  have hx25 : Bounds (588826413 / 1250000000) (2355305659 / 5000000000) x25 := by
    apply bounds_mul hx22 hx24 <;> norm_num
  let x26 : ℝ := -(2 / 5)
  have hx26 : Bounds (-2 / 5) (-2 / 5) x26 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((2 / 5) : ℝ))
  let x27 : ℝ := (1 / 1)+x26
  have hx27 : Bounds (3 / 5) (3 / 5) x27 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx26 <;> norm_num
  let x28 : ℝ := (1 / 1)-(2 / 5)
  have hx28 : Bounds (3 / 5) (3 / 5) x28 := by
    exact hx27
  let x29 : ℝ := -(2 / 5)
  have hx29 : Bounds (-2 / 5) (-2 / 5) x29 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((2 / 5) : ℝ))
  let x30 : ℝ := (1 / 1)+x29
  have hx30 : Bounds (3 / 5) (3 / 5) x30 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx29 <;> norm_num
  let x31 : ℝ := (1 / 1)-(2 / 5)
  have hx31 : Bounds (3 / 5) (3 / 5) x31 := by
    exact hx30
  let x32 : ℝ := Real.log x31
  have hx32 : Bounds (-63853203 / 125000000) (-510825623 / 1000000000) x32 := by
    exact bounds_log hx31 (by norm_num) (by simpa only [div_one] using reflection_log_4.1) (by simpa only [div_one] using reflection_log_4.2)
  let x33 : ℝ := x28*x32
  have hx33 : Bounds (-191559609 / 625000000) (-1532476869 / 5000000000) x33 := by
    apply bounds_mul hx28 hx32 <;> norm_num
  let x34 : ℝ := x25+x33
  have hx34 : Bounds (41141439 / 250000000) (82282879 / 500000000) x34 := by
    apply bounds_add hx25 hx33 <;> norm_num
  let x35 : ℝ := (2 / 1)⁻¹
  have hx35 : Bounds (1 / 2) (1 / 2) x35 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x36 : ℝ := x34*x35
  have hx36 : Bounds (41141439 / 500000000) (82282879 / 1000000000) x36 := by
    apply bounds_mul hx34 hx35 <;> norm_num
  let x37 : ℝ := x34/(2 / 1)
  have hx37 : Bounds (41141439 / 500000000) (82282879 / 1000000000) x37 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx36
  let x38 : ℝ := -x37
  have hx38 : Bounds (-82282879 / 1000000000) (-41141439 / 500000000) x38 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx37
  let x39 : ℝ := x21+x38
  have hx39 : Bounds (610864301 / 1000000000) (610864303 / 1000000000) x39 := by
    apply bounds_add hx21 hx38 <;> norm_num
  let x40 : ℝ := x21-x37
  have hx40 : Bounds (610864301 / 1000000000) (610864303 / 1000000000) x40 := by
    exact hx39
  let x41 : ℝ := biasE (2 / 5)
  have hx41 : Bounds (610864301 / 1000000000) (610864303 / 1000000000) x41 := by
    simpa +zetaDelta only [biasE, div_one] using hx40
  let x42 : ℝ := biasE c
  have hx42 : Bounds (1985152419 / 10000000000) (610864303 / 1000000000) x42 := by
    exact bounds_biasE hc (by norm_num) (by norm_num) hx20.1 hx41.2
  let x43 : ℝ := Real.log (2 / 1)
  have hx43 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x43 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x44 : ℝ := c*c
  have hx44 : Bounds (4 / 25) (81 / 100) x44 := by
    apply bounds_mul hc hc <;> norm_num
  let x45 : ℝ := -x44
  have hx45 : Bounds (-81 / 100) (-4 / 25) x45 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx44
  let x46 : ℝ := (1 / 1)+x45
  have hx46 : Bounds (19 / 100) (21 / 25) x46 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx45 <;> norm_num
  let x47 : ℝ := (1 / 1)-x44
  have hx47 : Bounds (19 / 100) (21 / 25) x47 := by
    exact hx46
  let x48 : ℝ := Real.log x47
  have hx48 : Bounds (-207591401 / 125000000) (-174353387 / 1000000000) x48 := by
    exact bounds_log hx47 (by norm_num) (by simpa only [div_one] using reflection_log_5.1) (by simpa only [div_one] using reflection_log_6.2)
  let x49 : ℝ := (2 / 1)⁻¹
  have hx49 : Bounds (1 / 2) (1 / 2) x49 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x50 : ℝ := x48*x49
  have hx50 : Bounds (-207591401 / 250000000) (-174353387 / 2000000000) x50 := by
    apply bounds_mul hx48 hx49 <;> norm_num
  let x51 : ℝ := x48/(2 / 1)
  have hx51 : Bounds (-207591401 / 250000000) (-174353387 / 2000000000) x51 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx50
  let x52 : ℝ := -x51
  have hx52 : Bounds (174353387 / 2000000000) (207591401 / 250000000) x52 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx51
  let x53 : ℝ := x43+x52
  have hx53 : Bounds (1560647747 / 2000000000) (304702557 / 200000000) x53 := by
    apply bounds_add hx43 hx52 <;> norm_num
  let x54 : ℝ := x43-x51
  have hx54 : Bounds (1560647747 / 2000000000) (304702557 / 200000000) x54 := by
    exact hx53
  let x55 : ℝ := c*(1 / 1)
  have hx55 : Bounds (2 / 5) (9 / 10) x55 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x56 : ℝ := c*x55
  have hx56 : Bounds (4 / 25) (81 / 100) x56 := by
    apply bounds_mul hc hx55 <;> norm_num
  let x57 : ℝ := c^2
  have hx57 : Bounds (4 / 25) (81 / 100) x57 := by
    (convert hx56 using 1; ring)
  let x58 : ℝ := -x57
  have hx58 : Bounds (-81 / 100) (-4 / 25) x58 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx57
  let x59 : ℝ := (1 / 1)+x58
  have hx59 : Bounds (19 / 100) (21 / 25) x59 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx58 <;> norm_num
  let x60 : ℝ := (1 / 1)-x57
  have hx60 : Bounds (19 / 100) (21 / 25) x60 := by
    exact hx59
  let x61 : ℝ := (1 / 1)+c
  have hx61 : Bounds (7 / 5) (19 / 10) x61 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hc <;> norm_num
  let x62 : ℝ := -c
  have hx62 : Bounds (-9 / 10) (-2 / 5) x62 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hc
  let x63 : ℝ := (1 / 1)+x62
  have hx63 : Bounds (1 / 10) (3 / 5) x63 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx62 <;> norm_num
  let x64 : ℝ := (1 / 1)-c
  have hx64 : Bounds (1 / 10) (3 / 5) x64 := by
    exact hx63
  let x65 : ℝ := x64⁻¹
  have hx65 : Bounds (833333333333 / 500000000000) (10 / 1) x65 := by
    apply bounds_inv hx64 <;> norm_num
  let x66 : ℝ := x61*x65
  have hx66 : Bounds (583333333333 / 250000000000) (19 / 1) x66 := by
    apply bounds_mul hx61 hx65 <;> norm_num
  let x67 : ℝ := x61/x64
  have hx67 : Bounds (583333333333 / 250000000000) (19 / 1) x67 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx66
  let x68 : ℝ := Real.log x67
  have hx68 : Bounds (847297859 / 1000000000) (2944438981 / 1000000000) x68 := by
    exact bounds_log hx67 (by norm_num) (by simpa only [div_one] using reflection_log_7.1) (by simpa only [div_one] using reflection_log_8.2)
  let x69 : ℝ := (2 / 1)⁻¹
  have hx69 : Bounds (1 / 2) (1 / 2) x69 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x70 : ℝ := x68*x69
  have hx70 : Bounds (847297859 / 2000000000) (2944438981 / 2000000000) x70 := by
    apply bounds_mul hx68 hx69 <;> norm_num
  let x71 : ℝ := x68/(2 / 1)
  have hx71 : Bounds (847297859 / 2000000000) (2944438981 / 2000000000) x71 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx70
  let x72 : ℝ := (2 / 1)*x54
  have hx72 : Bounds (1560647747 / 1000000000) (304702557 / 100000000) x72 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx54 <;> norm_num
  let x73 : ℝ := c*(1 / 1)
  have hx73 : Bounds (2 / 5) (9 / 10) x73 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x74 : ℝ := c*x73
  have hx74 : Bounds (4 / 25) (81 / 100) x74 := by
    apply bounds_mul hc hx73 <;> norm_num
  let x75 : ℝ := c^2
  have hx75 : Bounds (4 / 25) (81 / 100) x75 := by
    (convert hx74 using 1; ring)
  let x76 : ℝ := -x75
  have hx76 : Bounds (-81 / 100) (-4 / 25) x76 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx75
  let x77 : ℝ := x72+x76
  have hx77 : Bounds (750647747 / 1000000000) (288702557 / 100000000) x77 := by
    apply bounds_add hx72 hx76 <;> norm_num
  let x78 : ℝ := x72-x75
  have hx78 : Bounds (750647747 / 1000000000) (288702557 / 100000000) x78 := by
    exact hx77
  let x79 : ℝ := x42*x78
  have hx79 : Bounds (149015019077 / 1000000000000) (881790431281 / 500000000000) x79 := by
    apply bounds_mul hx42 hx78 <;> norm_num
  let x80 : ℝ := (2 / 1)*e
  have hx80 : Bounds (14 / 25) (7 / 10) x80 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) he <;> norm_num
  let x81 : ℝ := x60*(1 / 1)
  have hx81 : Bounds (19 / 100) (21 / 25) x81 := by
    apply bounds_mul hx60 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x82 : ℝ := x60*x81
  have hx82 : Bounds (361 / 10000) (441 / 625) x82 := by
    apply bounds_mul hx60 hx81 <;> norm_num
  let x83 : ℝ := x60^2
  have hx83 : Bounds (361 / 10000) (441 / 625) x83 := by
    (convert hx82 using 1; ring)
  let x84 : ℝ := x80*x83
  have hx84 : Bounds (2527 / 125000) (3087 / 6250) x84 := by
    apply bounds_mul hx80 hx83 <;> norm_num
  let x85 : ℝ := x54*(1 / 1)
  have hx85 : Bounds (1560647747 / 2000000000) (304702557 / 200000000) x85 := by
    apply bounds_mul hx54 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x86 : ℝ := x54*x85
  have hx86 : Bounds (304452673777 / 500000000000) (2321091206059 / 1000000000000) x86 := by
    apply bounds_mul hx54 hx85 <;> norm_num
  let x87 : ℝ := x54*x86
  have hx87 : Bounds (237571689699 / 500000000000) (1768106063791 / 500000000000) x87 := by
    apply bounds_mul hx54 hx86 <;> norm_num
  let x88 : ℝ := x54^3
  have hx88 : Bounds (237571689699 / 500000000000) (1768106063791 / 500000000000) x88 := by
    (convert hx87 using 1; ring)
  let x89 : ℝ := x84*x88
  have hx89 : Bounds (9605498557 / 1000000000000) (218325736757 / 125000000000) x89 := by
    apply bounds_mul hx84 hx88 <;> norm_num
  let x90 : ℝ := x89⁻¹
  have hx90 : Bounds (572539004593 / 1000000000000) (20821407531653 / 200000000000) x90 := by
    apply bounds_inv hx89 <;> norm_num
  let x91 : ℝ := x79*x90
  have hx91 : Bounds (85316910691 / 1000000000000) (91800589636069 / 500000000000) x91 := by
    apply bounds_mul hx79 hx90 <;> norm_num
  let x92 : ℝ := x79/x89
  have hx92 : Bounds (85316910691 / 1000000000000) (91800589636069 / 500000000000) x92 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx91
  let x93 : ℝ := -x71
  have hx93 : Bounds (-2944438981 / 2000000000) (-847297859 / 2000000000) x93 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx71
  let x94 : ℝ := (2 / 1)*x54
  have hx94 : Bounds (1560647747 / 1000000000) (304702557 / 100000000) x94 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx54 <;> norm_num
  let x95 : ℝ := c*(1 / 1)
  have hx95 : Bounds (2 / 5) (9 / 10) x95 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x96 : ℝ := c*x95
  have hx96 : Bounds (4 / 25) (81 / 100) x96 := by
    apply bounds_mul hc hx95 <;> norm_num
  let x97 : ℝ := c^2
  have hx97 : Bounds (4 / 25) (81 / 100) x97 := by
    (convert hx96 using 1; ring)
  let x98 : ℝ := -x97
  have hx98 : Bounds (-81 / 100) (-4 / 25) x98 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx97
  let x99 : ℝ := x94+x98
  have hx99 : Bounds (750647747 / 1000000000) (288702557 / 100000000) x99 := by
    apply bounds_add hx94 hx98 <;> norm_num
  let x100 : ℝ := x94-x97
  have hx100 : Bounds (750647747 / 1000000000) (288702557 / 100000000) x100 := by
    exact hx99
  let x101 : ℝ := x93*x100
  have hx101 : Bounds (-2125167656863 / 500000000000) (-19875694653 / 62500000000) x101 := by
    apply bounds_mul hx93 hx100 <;> norm_num
  let x102 : ℝ := x60⁻¹
  have hx102 : Bounds (297619047619 / 250000000000) (5263157894737 / 1000000000000) x102 := by
    apply bounds_inv hx60 <;> norm_num
  let x103 : ℝ := c*x102
  have hx103 : Bounds (47619047619 / 100000000000) (296052631579 / 62500000000) x103 := by
    apply bounds_mul hc hx102 <;> norm_num
  let x104 : ℝ := c/x60
  have hx104 : Bounds (47619047619 / 100000000000) (296052631579 / 62500000000) x104 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx103
  let x105 : ℝ := (2 / 1)*x104
  have hx105 : Bounds (47619047619 / 50000000000) (296052631579 / 31250000000) x105 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx104 <;> norm_num
  let x106 : ℝ := (2 / 1)*c
  have hx106 : Bounds (4 / 5) (9 / 5) x106 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hc <;> norm_num
  let x107 : ℝ := -x106
  have hx107 : Bounds (-9 / 5) (-4 / 5) x107 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx106
  let x108 : ℝ := x105+x107
  have hx108 : Bounds (-42380952381 / 50000000000) (271052631579 / 31250000000) x108 := by
    apply bounds_add hx105 hx107 <;> norm_num
  let x109 : ℝ := x105-x106
  have hx109 : Bounds (-42380952381 / 50000000000) (271052631579 / 31250000000) x109 := by
    exact hx108
  let x110 : ℝ := x42*x109
  have hx110 : Bounds (-258890109367 / 500000000000) (5298444059707 / 1000000000000) x110 := by
    apply bounds_mul hx42 hx109 <;> norm_num
  let x111 : ℝ := x101+x110
  have hx111 : Bounds (-238405776623 / 50000000000) (4980432945259 / 1000000000000) x111 := by
    apply bounds_add hx101 hx110 <;> norm_num
  let x112 : ℝ := (2 / 1)*e
  have hx112 : Bounds (14 / 25) (7 / 10) x112 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) he <;> norm_num
  let x113 : ℝ := x60*(1 / 1)
  have hx113 : Bounds (19 / 100) (21 / 25) x113 := by
    apply bounds_mul hx60 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x114 : ℝ := x60*x113
  have hx114 : Bounds (361 / 10000) (441 / 625) x114 := by
    apply bounds_mul hx60 hx113 <;> norm_num
  let x115 : ℝ := x60^2
  have hx115 : Bounds (361 / 10000) (441 / 625) x115 := by
    (convert hx114 using 1; ring)
  let x116 : ℝ := x112*x115
  have hx116 : Bounds (2527 / 125000) (3087 / 6250) x116 := by
    apply bounds_mul hx112 hx115 <;> norm_num
  let x117 : ℝ := x54*(1 / 1)
  have hx117 : Bounds (1560647747 / 2000000000) (304702557 / 200000000) x117 := by
    apply bounds_mul hx54 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x118 : ℝ := x54*x117
  have hx118 : Bounds (304452673777 / 500000000000) (2321091206059 / 1000000000000) x118 := by
    apply bounds_mul hx54 hx117 <;> norm_num
  let x119 : ℝ := x54*x118
  have hx119 : Bounds (237571689699 / 500000000000) (1768106063791 / 500000000000) x119 := by
    apply bounds_mul hx54 hx118 <;> norm_num
  let x120 : ℝ := x54^3
  have hx120 : Bounds (237571689699 / 500000000000) (1768106063791 / 500000000000) x120 := by
    (convert hx119 using 1; ring)
  let x121 : ℝ := x116*x120
  have hx121 : Bounds (9605498557 / 1000000000000) (218325736757 / 125000000000) x121 := by
    apply bounds_mul hx116 hx120 <;> norm_num
  let x122 : ℝ := x121⁻¹
  have hx122 : Bounds (572539004593 / 1000000000000) (20821407531653 / 200000000000) x122 := by
    apply bounds_inv hx121 <;> norm_num
  let x123 : ℝ := x111*x122
  have hx123 : Bounds (-124098595824193 / 250000000000) (518498120186543 / 1000000000000) x123 := by
    apply bounds_mul hx111 hx122 <;> norm_num
  let x124 : ℝ := x111/x121
  have hx124 : Bounds (-124098595824193 / 250000000000) (518498120186543 / 1000000000000) x124 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx123
  let x125 : ℝ := (4 / 1)*c
  have hx125 : Bounds (8 / 5) (18 / 5) x125 := by
    apply bounds_mul (bounds_const ((4 / 1) : ℝ)) hc <;> norm_num
  let x126 : ℝ := x60⁻¹
  have hx126 : Bounds (297619047619 / 250000000000) (5263157894737 / 1000000000000) x126 := by
    apply bounds_inv hx60 <;> norm_num
  let x127 : ℝ := x125*x126
  have hx127 : Bounds (1904761904761 / 1000000000000) (9473684210527 / 500000000000) x127 := by
    apply bounds_mul hx125 hx126 <;> norm_num
  let x128 : ℝ := x125/x60
  have hx128 : Bounds (1904761904761 / 1000000000000) (9473684210527 / 500000000000) x128 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx127
  let x129 : ℝ := (3 / 1)*c
  have hx129 : Bounds (6 / 5) (27 / 10) x129 := by
    apply bounds_mul (bounds_const ((3 / 1) : ℝ)) hc <;> norm_num
  let x130 : ℝ := x60*x54
  have hx130 : Bounds (29652307193 / 200000000000) (6398753697 / 5000000000) x130 := by
    apply bounds_mul hx60 hx54 <;> norm_num
  let x131 : ℝ := x130⁻¹
  have hx131 : Bounds (195350541557 / 250000000000) (6744837718639 / 1000000000000) x131 := by
    apply bounds_inv hx130 <;> norm_num
  let x132 : ℝ := x129*x131
  have hx132 : Bounds (937682599473 / 1000000000000) (9105530920163 / 500000000000) x132 := by
    apply bounds_mul hx129 hx131 <;> norm_num
  let x133 : ℝ := x129/x130
  have hx133 : Bounds (937682599473 / 1000000000000) (9105530920163 / 500000000000) x133 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx132
  let x134 : ℝ := -x133
  have hx134 : Bounds (-9105530920163 / 500000000000) (-937682599473 / 1000000000000) x134 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx133
  let x135 : ℝ := x128+x134
  have hx135 : Bounds (-3261259987113 / 200000000000) (18009685821581 / 1000000000000) x135 := by
    apply bounds_add hx128 hx134 <;> norm_num
  let x136 : ℝ := x128-x133
  have hx136 : Bounds (-3261259987113 / 200000000000) (18009685821581 / 1000000000000) x136 := by
    exact hx135
  let x137 : ℝ := x92*x136
  have hx137 : Bounds (-1496927948867461 / 500000000000) (103331236098843 / 31250000000) x137 := by
    apply bounds_mul hx92 hx136 <;> norm_num
  let x138 : ℝ := x124+x137
  have hx138 : Bounds (-1745125140515847 / 500000000000) (3825097675349519 / 1000000000000) x138 := by
    apply bounds_add hx124 hx137 <;> norm_num
  let x139 : ℝ := (2 / 1)*x54
  have hx139 : Bounds (1560647747 / 1000000000) (304702557 / 100000000) x139 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx54 <;> norm_num
  let x140 : ℝ := c*(1 / 1)
  have hx140 : Bounds (2 / 5) (9 / 10) x140 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x141 : ℝ := c*x140
  have hx141 : Bounds (4 / 25) (81 / 100) x141 := by
    apply bounds_mul hc hx140 <;> norm_num
  let x142 : ℝ := c^2
  have hx142 : Bounds (4 / 25) (81 / 100) x142 := by
    (convert hx141 using 1; ring)
  let x143 : ℝ := -x142
  have hx143 : Bounds (-81 / 100) (-4 / 25) x143 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx142
  let x144 : ℝ := x139+x143
  have hx144 : Bounds (750647747 / 1000000000) (288702557 / 100000000) x144 := by
    apply bounds_add hx139 hx143 <;> norm_num
  let x145 : ℝ := x139-x142
  have hx145 : Bounds (750647747 / 1000000000) (288702557 / 100000000) x145 := by
    exact hx144
  let x146 : ℝ := c*x145
  have hx146 : Bounds (750647747 / 2500000000) (2598323013 / 1000000000) x146 := by
    apply bounds_mul hc hx145 <;> norm_num
  let x147 : ℝ := x60*(1 / 1)
  have hx147 : Bounds (19 / 100) (21 / 25) x147 := by
    apply bounds_mul hx60 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x148 : ℝ := x60*x147
  have hx148 : Bounds (361 / 10000) (441 / 625) x148 := by
    apply bounds_mul hx60 hx147 <;> norm_num
  let x149 : ℝ := x60^2
  have hx149 : Bounds (361 / 10000) (441 / 625) x149 := by
    (convert hx148 using 1; ring)
  let x150 : ℝ := x54*(1 / 1)
  have hx150 : Bounds (1560647747 / 2000000000) (304702557 / 200000000) x150 := by
    apply bounds_mul hx54 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x151 : ℝ := x54*x150
  have hx151 : Bounds (304452673777 / 500000000000) (2321091206059 / 1000000000000) x151 := by
    apply bounds_mul hx54 hx150 <;> norm_num
  let x152 : ℝ := x54^2
  have hx152 : Bounds (304452673777 / 500000000000) (2321091206059 / 1000000000000) x152 := by
    (convert hx151 using 1; ring)
  let x153 : ℝ := x149*x152
  have hx153 : Bounds (10990741523 / 500000000000) (409440488749 / 250000000000) x153 := by
    apply bounds_mul hx149 hx152 <;> norm_num
  let x154 : ℝ := x153⁻¹
  have hx154 : Bounds (305294672693 / 500000000000) (45492835852219 / 1000000000000) x154 := by
    apply bounds_inv hx153 <;> norm_num
  let x155 : ℝ := x146*x154
  have hx155 : Bounds (91667503291 / 500000000000) (118205082321453 / 1000000000000) x155 := by
    apply bounds_mul hx146 hx154 <;> norm_num
  let x156 : ℝ := x146/x153
  have hx156 : Bounds (91667503291 / 500000000000) (118205082321453 / 1000000000000) x156 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx155
  let x157 : ℝ := x42*(1 / 1)
  have hx157 : Bounds (1985152419 / 10000000000) (610864303 / 1000000000) x157 := by
    apply bounds_mul hx42 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x158 : ℝ := x42*x157
  have hx158 : Bounds (19704150633 / 500000000000) (9328879917 / 25000000000) x158 := by
    apply bounds_mul hx42 hx157 <;> norm_num
  let x159 : ℝ := x42^2
  have hx159 : Bounds (19704150633 / 500000000000) (9328879917 / 25000000000) x159 := by
    (convert hx158 using 1; ring)
  let x160 : ℝ := e*x54
  have hx160 : Bounds (10924534229 / 50000000000) (2132917899 / 4000000000) x160 := by
    apply bounds_mul he hx54 <;> norm_num
  let x161 : ℝ := x160⁻¹
  have hx161 : Bounds (468841299737 / 250000000000) (4576854166219 / 1000000000000) x161 := by
    apply bounds_inv hx160 <;> norm_num
  let x162 : ℝ := x159*x161
  have hx162 : Bounds (73904956743 / 1000000000000) (426969229143 / 250000000000) x162 := by
    apply bounds_mul hx159 hx161 <;> norm_num
  let x163 : ℝ := x159/x160
  have hx163 : Bounds (73904956743 / 1000000000000) (426969229143 / 250000000000) x163 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx162
  let x164 : ℝ := c*(1 / 1)
  have hx164 : Bounds (2 / 5) (9 / 10) x164 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x165 : ℝ := c*x164
  have hx165 : Bounds (4 / 25) (81 / 100) x165 := by
    apply bounds_mul hc hx164 <;> norm_num
  let x166 : ℝ := c^2
  have hx166 : Bounds (4 / 25) (81 / 100) x166 := by
    (convert hx165 using 1; ring)
  let x167 : ℝ := x138*x166
  have hx167 : Bounds (-2827102727635673 / 1000000000000) (3098329117033111 / 1000000000000) x167 := by
    apply bounds_mul hx138 hx166 <;> norm_num
  let x168 : ℝ := (2 / 1)*x92
  have hx168 : Bounds (85316910691 / 500000000000) (91800589636069 / 250000000000) x168 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx92 <;> norm_num
  let x169 : ℝ := x168*c
  have hx169 : Bounds (8531691069 / 125000000000) (330482122689849 / 1000000000000) x169 := by
    apply bounds_mul hx168 hc <;> norm_num
  let x170 : ℝ := x167+x169
  have hx170 : Bounds (-2827034474107121 / 1000000000000) (42860140496537 / 12500000000) x170 := by
    apply bounds_add hx167 hx169 <;> norm_num
  let x171 : ℝ := x163*x170
  have hx171 : Bounds (-301764182542551 / 62500000000) (2927993783802733 / 500000000000) x171 := by
    apply bounds_mul hx163 hx170 <;> norm_num
  let x172 : ℝ := (2 / 1)*x138
  have hx172 : Bounds (-1745125140515847 / 250000000000) (3825097675349519 / 500000000000) x172 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx138 <;> norm_num
  let x173 : ℝ := x172*c
  have hx173 : Bounds (-125649010117141 / 20000000000) (1377035163125827 / 200000000000) x173 := by
    apply bounds_mul hx172 hc <;> norm_num
  let x174 : ℝ := x173*x42
  have hx174 : Bounds (-767544949878473 / 200000000000) (4205908125646749 / 1000000000000) x174 := by
    apply bounds_mul hx173 hx42 <;> norm_num
  let x175 : ℝ := (2 / 1)*x92
  have hx175 : Bounds (85316910691 / 500000000000) (91800589636069 / 250000000000) x175 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx92 <;> norm_num
  let x176 : ℝ := c*x71
  have hx176 : Bounds (847297859 / 5000000000) (26499950829 / 20000000000) x176 := by
    apply bounds_mul hc hx71 <;> norm_num
  let x177 : ℝ := -x176
  have hx177 : Bounds (-26499950829 / 20000000000) (-847297859 / 5000000000) x177 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx176
  let x178 : ℝ := x42+x177
  have hx178 : Bounds (-22529645991 / 20000000000) (275877957 / 625000000) x178 := by
    apply bounds_add hx42 hx177 <;> norm_num
  let x179 : ℝ := x42-x176
  have hx179 : Bounds (-22529645991 / 20000000000) (275877957 / 625000000) x179 := by
    exact hx178
  let x180 : ℝ := x175*x179
  have hx180 : Bounds (-20682347862657 / 50000000000) (162084858369243 / 1000000000000) x180 := by
    apply bounds_mul hx175 hx179 <;> norm_num
  let x181 : ℝ := x174+x180
  have hx181 : Bounds (-850274341329101 / 200000000000) (545999123001999 / 125000000000) x181 := by
    apply bounds_add hx174 hx180 <;> norm_num
  let x182 : ℝ := x163*x181
  have hx182 : Bounds (-7260819601547167 / 1000000000000) (3729997194574681 / 500000000000) x182 := by
    apply bounds_mul hx163 hx181 <;> norm_num
  let x183 : ℝ := x42*(1 / 1)
  have hx183 : Bounds (1985152419 / 10000000000) (610864303 / 1000000000) x183 := by
    apply bounds_mul hx42 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x184 : ℝ := x42*x183
  have hx184 : Bounds (19704150633 / 500000000000) (9328879917 / 25000000000) x184 := by
    apply bounds_mul hx42 hx183 <;> norm_num
  let x185 : ℝ := x42^2
  have hx185 : Bounds (19704150633 / 500000000000) (9328879917 / 25000000000) x185 := by
    (convert hx184 using 1; ring)
  let x186 : ℝ := x138*x185
  have hx186 : Bounds (-162800628760101 / 125000000000) (1427355075365261 / 1000000000000) x186 := by
    apply bounds_mul hx138 hx185 <;> norm_num
  let x187 : ℝ := (2 / 1)*x92
  have hx187 : Bounds (85316910691 / 500000000000) (91800589636069 / 250000000000) x187 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx92 <;> norm_num
  let x188 : ℝ := x187*x42
  have hx188 : Bounds (33873414327 / 1000000000000) (112155406406053 / 500000000000) x188 := by
    apply bounds_mul hx187 hx42 <;> norm_num
  let x189 : ℝ := x188*x71
  have hx189 : Bounds (7175217859 / 500000000000) (8255868763797 / 25000000000) x189 := by
    apply bounds_mul hx188 hx71 <;> norm_num
  let x190 : ℝ := -x189
  have hx190 : Bounds (-8255868763797 / 25000000000) (-7175217859 / 500000000000) x190 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx189
  let x191 : ℝ := x186+x190
  have hx191 : Bounds (-102039986289543 / 62500000000) (1427340724929543 / 1000000000000) x191 := by
    apply bounds_add hx186 hx190 <;> norm_num
  let x192 : ℝ := x186-x189
  have hx192 : Bounds (-102039986289543 / 62500000000) (1427340724929543 / 1000000000000) x192 := by
    exact hx191
  let x193 : ℝ := x163*x192
  have hx193 : Bounds (-1394173897209871 / 500000000000) (304715284523789 / 125000000000) x193 := by
    apply bounds_mul hx163 hx192 <;> norm_num
  let x194 : ℝ := x163*x156
  have hx194 : Bounds (1354936573 / 100000000000) (201879731518303 / 1000000000000) x194 := by
    apply bounds_mul hx163 hx156 <;> norm_num
  refine ⟨?_,?_,?_,?_⟩
  · have hb : x171 ≤ 6000 := le_trans hx171.2 (by norm_num)
    simpa +zetaDelta only [C2,Cs,Kprime,K,Mprime,SmallMean.A,biasB,div_one,pow_two] using hb
  · have hb : x182 ≤ 8000 := le_trans hx182.2 (by norm_num)
    simpa +zetaDelta only [C1,Cs,Kprime,K,Mprime,SmallMean.A,biasB,div_one,pow_two] using hb
  · have hb : x193 ≤ 3000 := le_trans hx193.2 (by norm_num)
    simpa +zetaDelta only [C0,Cs,Kprime,K,Mprime,SmallMean.A,biasB,div_one,pow_two] using hb
  · have hb : x194 ≤ 210 := le_trans hx194.2 (by norm_num)
    simpa +zetaDelta only [Cq,Cs,Kprime,K,Mprime,SmallMean.A,biasB,div_one,pow_two] using hb

end GeneralCK.Certificates.HighBiasCoarse

end


