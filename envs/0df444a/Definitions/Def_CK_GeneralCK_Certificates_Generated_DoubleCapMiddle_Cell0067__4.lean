-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0067__4
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0067__4
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T10:59:22.922215+00:00
-- url     : https://prove2.me/theorems/3774f9fb-718d-4f38-a3a5-1c0f3b8920e4
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0067 (+3 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0068, GeneralCK.Certificates.Gener…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0067 (+3 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0068, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0069, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0070)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0067 (+3 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0068, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0069, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0070)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0067 (+3 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0068, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0069, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0070) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0067 (+3 modules: GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0068, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0069, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0070).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0066Logs__6

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0067 =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0067
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Reflection
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem cell_bias_nonneg (m : ℝ) (hm : Bounds (181 / 640) (1451 / 5120) m) :
    let h := (1 + H (2*m - 1/2))/2
    let x := 1-2*m
    let y := 1-2*entropyInverse h
    let c := regularContact (x/(Real.log 2*h))
    0 ≤ 2*(biasE x-Real.log 2*h)-y*SmallMean.A y+x*SmallMean.A c := by
  have hEq : biasE (2-4*m) = Real.log 2 * H (2*m-1/2) := by
    have hmstrict : 1/4 < m := by
      have hlo : (1/4 : ℝ) < (181 / 640) := by norm_num
      exact lt_of_lt_of_le hlo hm.1
    rw [show 2-4*m = 1-2*(2*m-1/2) by ring,
      GeneralCK.Correction.Natural.biasE_probability (by linarith [hmstrict]) (by linarith [hm.2]),
      GeneralCK.Certificates.Mixed.hn_eq_H_mul_log]
    ring
  have hLh : Real.log 2 * ((1 + H (2*m - 1/2))/2) = (Real.log 2 + biasE (2-4*m))/2 := by
    rw [hEq]
    ring
  let x0 : ℝ := (2 / 1)*m
  have hx0 : Bounds (181 / 320) (1451 / 2560) x0 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hm <;> norm_num
  let x1 : ℝ := -x0
  have hx1 : Bounds (-1451 / 2560) (-181 / 320) x1 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx0
  let x2 : ℝ := (1 / 1)+x1
  have hx2 : Bounds (1109 / 2560) (139 / 320) x2 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx1 <;> norm_num
  let x3 : ℝ := (1 / 1)-x0
  have hx3 : Bounds (1109 / 2560) (139 / 320) x3 := by
    exact hx2
  let x4 : ℝ := (4 / 1)*m
  have hx4 : Bounds (181 / 160) (1451 / 1280) x4 := by
    apply bounds_mul (bounds_const ((4 / 1) : ℝ)) hm <;> norm_num
  let x5 : ℝ := -x4
  have hx5 : Bounds (-1451 / 1280) (-181 / 160) x5 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx4
  let x6 : ℝ := (2 / 1)+x5
  have hx6 : Bounds (1109 / 1280) (139 / 160) x6 := by
    apply bounds_add (bounds_const ((2 / 1) : ℝ)) hx5 <;> norm_num
  let x7 : ℝ := (2 / 1)-x4
  have hx7 : Bounds (1109 / 1280) (139 / 160) x7 := by
    exact hx6
  let x8 : ℝ := Real.log (2 / 1)
  have hx8 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x8 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x9 : ℝ := (1 / 1)+(139 / 320)
  have hx9 : Bounds (459 / 320) (459 / 320) x9 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((139 / 320) : ℝ)) <;> norm_num
  let x10 : ℝ := (1 / 1)+(139 / 320)
  have hx10 : Bounds (459 / 320) (459 / 320) x10 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((139 / 320) : ℝ)) <;> norm_num
  let x11 : ℝ := Real.log x10
  have hx11 : Bounds (180364607 / 500000000) (72145843 / 200000000) x11 := by
    exact bounds_log hx10 (by norm_num) (by simpa only [div_one] using reflection_log_1.1) (by simpa only [div_one] using reflection_log_1.2)
  let x12 : ℝ := x9*x11
  have hx12 : Bounds (517420966331 / 1000000000000) (258710483883 / 500000000000) x12 := by
    apply bounds_mul hx9 hx11 <;> norm_num
  let x13 : ℝ := -(139 / 320)
  have hx13 : Bounds (-139 / 320) (-139 / 320) x13 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((139 / 320) : ℝ))
  let x14 : ℝ := (1 / 1)+x13
  have hx14 : Bounds (181 / 320) (181 / 320) x14 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx13 <;> norm_num
  let x15 : ℝ := (1 / 1)-(139 / 320)
  have hx15 : Bounds (181 / 320) (181 / 320) x15 := by
    exact hx14
  let x16 : ℝ := -(139 / 320)
  have hx16 : Bounds (-139 / 320) (-139 / 320) x16 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((139 / 320) : ℝ))
  let x17 : ℝ := (1 / 1)+x16
  have hx17 : Bounds (181 / 320) (181 / 320) x17 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx16 <;> norm_num
  let x18 : ℝ := (1 / 1)-(139 / 320)
  have hx18 : Bounds (181 / 320) (181 / 320) x18 := by
    exact hx17
  let x19 : ℝ := Real.log x18
  have hx19 : Bounds (-113964793 / 200000000) (-142455991 / 250000000) x19 := by
    exact bounds_log hx18 (by norm_num) (by simpa only [div_one] using reflection_log_2.1) (by simpa only [div_one] using reflection_log_2.2)
  let x20 : ℝ := x15*x19
  have hx20 : Bounds (-80576670051 / 250000000000) (-322306679637 / 1000000000000) x20 := by
    apply bounds_mul hx15 hx19 <;> norm_num
  let x21 : ℝ := x12+x20
  have hx21 : Bounds (195114286127 / 1000000000000) (195114288129 / 1000000000000) x21 := by
    apply bounds_add hx12 hx20 <;> norm_num
  let x22 : ℝ := (2 / 1)⁻¹
  have hx22 : Bounds (1 / 2) (1 / 2) x22 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x23 : ℝ := x21*x22
  have hx23 : Bounds (97557143063 / 1000000000000) (19511428813 / 200000000000) x23 := by
    apply bounds_mul hx21 hx22 <;> norm_num
  let x24 : ℝ := x21/(2 / 1)
  have hx24 : Bounds (97557143063 / 1000000000000) (19511428813 / 200000000000) x24 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx23
  let x25 : ℝ := -x24
  have hx25 : Bounds (-19511428813 / 200000000000) (-97557143063 / 1000000000000) x25 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx24
  let x26 : ℝ := x8+x25
  have hx26 : Bounds (119118007187 / 200000000000) (595590037937 / 1000000000000) x26 := by
    apply bounds_add hx8 hx25 <;> norm_num
  let x27 : ℝ := x8-x24
  have hx27 : Bounds (119118007187 / 200000000000) (595590037937 / 1000000000000) x27 := by
    exact hx26
  let x28 : ℝ := biasE (139 / 320)
  have hx28 : Bounds (119118007187 / 200000000000) (595590037937 / 1000000000000) x28 := by
    simpa +zetaDelta only [biasE, div_one] using hx27
  let x29 : ℝ := Real.log (2 / 1)
  have hx29 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x29 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x30 : ℝ := (1 / 1)+(1109 / 2560)
  have hx30 : Bounds (3669 / 2560) (3669 / 2560) x30 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1109 / 2560) : ℝ)) <;> norm_num
  let x31 : ℝ := (1 / 1)+(1109 / 2560)
  have hx31 : Bounds (3669 / 2560) (3669 / 2560) x31 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1109 / 2560) : ℝ)) <;> norm_num
  let x32 : ℝ := Real.log x31
  have hx32 : Bounds (179955943 / 500000000) (359911887 / 1000000000) x32 := by
    exact bounds_log hx31 (by norm_num) (by simpa only [div_one] using reflection_log_3.1) (by simpa only [div_one] using reflection_log_3.2)
  let x33 : ℝ := x30*x32
  have hx33 : Bounds (515826839739 / 1000000000000) (257913420587 / 500000000000) x33 := by
    apply bounds_mul hx30 hx32 <;> norm_num
  let x34 : ℝ := -(1109 / 2560)
  have hx34 : Bounds (-1109 / 2560) (-1109 / 2560) x34 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1109 / 2560) : ℝ))
  let x35 : ℝ := (1 / 1)+x34
  have hx35 : Bounds (1451 / 2560) (1451 / 2560) x35 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx34 <;> norm_num
  let x36 : ℝ := (1 / 1)-(1109 / 2560)
  have hx36 : Bounds (1451 / 2560) (1451 / 2560) x36 := by
    exact hx35
  let x37 : ℝ := -(1109 / 2560)
  have hx37 : Bounds (-1109 / 2560) (-1109 / 2560) x37 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1109 / 2560) : ℝ))
  let x38 : ℝ := (1 / 1)+x37
  have hx38 : Bounds (1451 / 2560) (1451 / 2560) x38 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx37 <;> norm_num
  let x39 : ℝ := (1 / 1)-(1109 / 2560)
  have hx39 : Bounds (1451 / 2560) (1451 / 2560) x39 := by
    exact hx38
  let x40 : ℝ := Real.log x39
  have hx40 : Bounds (-113550857 / 200000000) (-141938571 / 250000000) x40 := by
    exact bounds_log hx39 (by norm_num) (by simpa only [div_one] using reflection_log_4.1) (by simpa only [div_one] using reflection_log_4.2)
  let x41 : ℝ := x36*x40
  have hx41 : Bounds (-160900677253 / 500000000000) (-321801353939 / 1000000000000) x41 := by
    apply bounds_mul hx36 hx40 <;> norm_num
  let x42 : ℝ := x33+x41
  have hx42 : Bounds (194025485233 / 1000000000000) (38805097447 / 200000000000) x42 := by
    apply bounds_add hx33 hx41 <;> norm_num
  let x43 : ℝ := (2 / 1)⁻¹
  have hx43 : Bounds (1 / 2) (1 / 2) x43 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x44 : ℝ := x42*x43
  have hx44 : Bounds (12126592827 / 125000000000) (48506371809 / 500000000000) x44 := by
    apply bounds_mul hx42 hx43 <;> norm_num
  let x45 : ℝ := x42/(2 / 1)
  have hx45 : Bounds (12126592827 / 125000000000) (48506371809 / 500000000000) x45 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx44
  let x46 : ℝ := -x45
  have hx46 : Bounds (-48506371809 / 500000000000) (-12126592827 / 125000000000) x46 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx45
  let x47 : ℝ := x29+x46
  have hx47 : Bounds (298067218191 / 500000000000) (37258402399 / 62500000000) x47 := by
    apply bounds_add hx29 hx46 <;> norm_num
  let x48 : ℝ := x29-x45
  have hx48 : Bounds (298067218191 / 500000000000) (37258402399 / 62500000000) x48 := by
    exact hx47
  let x49 : ℝ := biasE (1109 / 2560)
  have hx49 : Bounds (298067218191 / 500000000000) (37258402399 / 62500000000) x49 := by
    simpa +zetaDelta only [biasE, div_one] using hx48
  let x50 : ℝ := biasE x3
  have hx50 : Bounds (119118007187 / 200000000000) (37258402399 / 62500000000) x50 := by
    exact bounds_biasE hx3 (by norm_num) (by norm_num) hx28.1 hx49.2
  let x51 : ℝ := Real.log (2 / 1)
  have hx51 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x51 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x52 : ℝ := (1 / 1)+(139 / 160)
  have hx52 : Bounds (299 / 160) (299 / 160) x52 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((139 / 160) : ℝ)) <;> norm_num
  let x53 : ℝ := (1 / 1)+(139 / 160)
  have hx53 : Bounds (299 / 160) (299 / 160) x53 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((139 / 160) : ℝ)) <;> norm_num
  let x54 : ℝ := Real.log x53
  have hx54 : Bounds (312634879 / 500000000) (625269759 / 1000000000) x54 := by
    exact bounds_log hx53 (by norm_num) (by simpa only [div_one] using reflection_log_5.1) (by simpa only [div_one] using reflection_log_5.2)
  let x55 : ℝ := x52*x54
  have hx55 : Bounds (584236430131 / 500000000000) (292118215533 / 250000000000) x55 := by
    apply bounds_mul hx52 hx54 <;> norm_num
  let x56 : ℝ := -(139 / 160)
  have hx56 : Bounds (-139 / 160) (-139 / 160) x56 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((139 / 160) : ℝ))
  let x57 : ℝ := (1 / 1)+x56
  have hx57 : Bounds (21 / 160) (21 / 160) x57 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx56 <;> norm_num
  let x58 : ℝ := (1 / 1)-(139 / 160)
  have hx58 : Bounds (21 / 160) (21 / 160) x58 := by
    exact hx57
  let x59 : ℝ := -(139 / 160)
  have hx59 : Bounds (-139 / 160) (-139 / 160) x59 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((139 / 160) : ℝ))
  let x60 : ℝ := (1 / 1)+x59
  have hx60 : Bounds (21 / 160) (21 / 160) x60 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx59 <;> norm_num
  let x61 : ℝ := (1 / 1)-(139 / 160)
  have hx61 : Bounds (21 / 160) (21 / 160) x61 := by
    exact hx60
  let x62 : ℝ := Real.log x61
  have hx62 : Bounds (-2030651379 / 1000000000) (-126915711 / 62500000) x62 := by
    exact bounds_log hx61 (by norm_num) (by simpa only [div_one] using reflection_log_6.1) (by simpa only [div_one] using reflection_log_6.2)
  let x63 : ℝ := x58*x62
  have hx63 : Bounds (-133261496747 / 500000000000) (-2665229931 / 10000000000) x63 := by
    apply bounds_mul hx58 hx62 <;> norm_num
  let x64 : ℝ := x55+x63
  have hx64 : Bounds (56371866673 / 62500000000) (112743733629 / 125000000000) x64 := by
    apply bounds_add hx55 hx63 <;> norm_num
  let x65 : ℝ := (2 / 1)⁻¹
  have hx65 : Bounds (1 / 2) (1 / 2) x65 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x66 : ℝ := x64*x65
  have hx66 : Bounds (56371866673 / 125000000000) (112743733629 / 250000000000) x66 := by
    apply bounds_mul hx64 hx65 <;> norm_num
  let x67 : ℝ := x64/(2 / 1)
  have hx67 : Bounds (56371866673 / 125000000000) (112743733629 / 250000000000) x67 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx66
  let x68 : ℝ := -x67
  have hx68 : Bounds (-112743733629 / 250000000000) (-56371866673 / 125000000000) x68 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx67
  let x69 : ℝ := x51+x68
  have hx69 : Bounds (60543061371 / 250000000000) (3783941369 / 15625000000) x69 := by
    apply bounds_add hx51 hx68 <;> norm_num
  let x70 : ℝ := x51-x67
  have hx70 : Bounds (60543061371 / 250000000000) (3783941369 / 15625000000) x70 := by
    exact hx69
  let x71 : ℝ := biasE (139 / 160)
  have hx71 : Bounds (60543061371 / 250000000000) (3783941369 / 15625000000) x71 := by
    simpa +zetaDelta only [biasE, div_one] using hx70
  let x72 : ℝ := Real.log (2 / 1)
  have hx72 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x72 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x73 : ℝ := (1 / 1)+(1109 / 1280)
  have hx73 : Bounds (2389 / 1280) (2389 / 1280) x73 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1109 / 1280) : ℝ)) <;> norm_num
  let x74 : ℝ := (1 / 1)+(1109 / 1280)
  have hx74 : Bounds (2389 / 1280) (2389 / 1280) x74 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1109 / 1280) : ℝ)) <;> norm_num
  let x75 : ℝ := Real.log x74
  have hx75 : Bounds (62401479 / 100000000) (624014791 / 1000000000) x75 := by
    exact bounds_log hx74 (by norm_num) (by simpa only [div_one] using reflection_log_7.1) (by simpa only [div_one] using reflection_log_7.2)
  let x76 : ℝ := x73*x75
  have hx76 : Bounds (291166276037 / 250000000000) (232933021203 / 200000000000) x76 := by
    apply bounds_mul hx73 hx75 <;> norm_num
  let x77 : ℝ := -(1109 / 1280)
  have hx77 : Bounds (-1109 / 1280) (-1109 / 1280) x77 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1109 / 1280) : ℝ))
  let x78 : ℝ := (1 / 1)+x77
  have hx78 : Bounds (171 / 1280) (171 / 1280) x78 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx77 <;> norm_num
  let x79 : ℝ := (1 / 1)-(1109 / 1280)
  have hx79 : Bounds (171 / 1280) (171 / 1280) x79 := by
    exact hx78
  let x80 : ℝ := -(1109 / 1280)
  have hx80 : Bounds (-1109 / 1280) (-1109 / 1280) x80 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1109 / 1280) : ℝ))
  let x81 : ℝ := (1 / 1)+x80
  have hx81 : Bounds (171 / 1280) (171 / 1280) x81 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx80 <;> norm_num
  let x82 : ℝ := (1 / 1)-(1109 / 1280)
  have hx82 : Bounds (171 / 1280) (171 / 1280) x82 := by
    exact hx81
  let x83 : ℝ := Real.log x82
  have hx83 : Bounds (-1006475901 / 500000000) (-2012951799 / 1000000000) x83 := by
    exact bounds_log hx82 (by norm_num) (by simpa only [div_one] using reflection_log_8.1) (by simpa only [div_one] using reflection_log_8.2)
  let x84 : ℝ := x79*x83
  have hx84 : Bounds (-268917779799 / 1000000000000) (-268917779397 / 1000000000000) x84 := by
    apply bounds_mul hx79 hx83 <;> norm_num
  let x85 : ℝ := x76+x84
  have hx85 : Bounds (895747324349 / 1000000000000) (447873663309 / 500000000000) x85 := by
    apply bounds_add hx76 hx84 <;> norm_num
  let x86 : ℝ := (2 / 1)⁻¹
  have hx86 : Bounds (1 / 2) (1 / 2) x86 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x87 : ℝ := x85*x86
  have hx87 : Bounds (223936831087 / 500000000000) (447873663309 / 1000000000000) x87 := by
    apply bounds_mul hx85 hx86 <;> norm_num
  let x88 : ℝ := x85/(2 / 1)
  have hx88 : Bounds (223936831087 / 500000000000) (447873663309 / 1000000000000) x88 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx87
  let x89 : ℝ := -x88
  have hx89 : Bounds (-447873663309 / 1000000000000) (-223936831087 / 500000000000) x89 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx88
  let x90 : ℝ := x72+x89
  have hx90 : Bounds (245273516691 / 1000000000000) (122636759413 / 500000000000) x90 := by
    apply bounds_add hx72 hx89 <;> norm_num
  let x91 : ℝ := x72-x88
  have hx91 : Bounds (245273516691 / 1000000000000) (122636759413 / 500000000000) x91 := by
    exact hx90
  let x92 : ℝ := biasE (1109 / 1280)
  have hx92 : Bounds (245273516691 / 1000000000000) (122636759413 / 500000000000) x92 := by
    simpa +zetaDelta only [biasE, div_one] using hx91
  let x93 : ℝ := biasE x7
  have hx93 : Bounds (60543061371 / 250000000000) (122636759413 / 500000000000) x93 := by
    exact bounds_biasE hx7 (by norm_num) (by norm_num) hx71.1 hx92.2
  let x94 : ℝ := Real.log (2 / 1)
  have hx94 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x94 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x95 : ℝ := x94+x93
  have hx95 : Bounds (233829856371 / 250000000000) (469210349913 / 500000000000) x95 := by
    apply bounds_add hx94 hx93 <;> norm_num
  let x96 : ℝ := (2 / 1)⁻¹
  have hx96 : Bounds (1 / 2) (1 / 2) x96 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x97 : ℝ := x95*x96
  have hx97 : Bounds (233829856371 / 500000000000) (469210349913 / 1000000000000) x97 := by
    apply bounds_mul hx95 hx96 <;> norm_num
  let x98 : ℝ := x95/(2 / 1)
  have hx98 : Bounds (233829856371 / 500000000000) (469210349913 / 1000000000000) x98 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx97
  let x99 : ℝ := Real.log (2 / 1)
  have hx99 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x99 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x100 : ℝ := (1 / 1)+(64287 / 100000)
  have hx100 : Bounds (164287 / 100000) (164287 / 100000) x100 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((64287 / 100000) : ℝ)) <;> norm_num
  let x101 : ℝ := (1 / 1)+(64287 / 100000)
  have hx101 : Bounds (164287 / 100000) (164287 / 100000) x101 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((64287 / 100000) : ℝ)) <;> norm_num
  let x102 : ℝ := Real.log x101
  have hx102 : Bounds (62055589 / 125000000) (496444713 / 1000000000) x102 := by
    exact bounds_log hx101 (by norm_num) (by simpa only [div_one] using reflection_log_9.1) (by simpa only [div_one] using reflection_log_9.2)
  let x103 : ℝ := x100*x102
  have hx103 : Bounds (815594124003 / 1000000000000) (815594125647 / 1000000000000) x103 := by
    apply bounds_mul hx100 hx102 <;> norm_num
  let x104 : ℝ := -(64287 / 100000)
  have hx104 : Bounds (-64287 / 100000) (-64287 / 100000) x104 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((64287 / 100000) : ℝ))
  let x105 : ℝ := (1 / 1)+x104
  have hx105 : Bounds (35713 / 100000) (35713 / 100000) x105 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx104 <;> norm_num
  let x106 : ℝ := (1 / 1)-(64287 / 100000)
  have hx106 : Bounds (35713 / 100000) (35713 / 100000) x106 := by
    exact hx105
  let x107 : ℝ := -(64287 / 100000)
  have hx107 : Bounds (-64287 / 100000) (-64287 / 100000) x107 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((64287 / 100000) : ℝ))
  let x108 : ℝ := (1 / 1)+x107
  have hx108 : Bounds (35713 / 100000) (35713 / 100000) x108 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx107 <;> norm_num
  let x109 : ℝ := (1 / 1)-(64287 / 100000)
  have hx109 : Bounds (35713 / 100000) (35713 / 100000) x109 := by
    exact hx108
  let x110 : ℝ := Real.log x109
  have hx110 : Bounds (-1029655419 / 1000000000) (-1029655417 / 1000000000) x110 := by
    exact bounds_log hx109 (by norm_num) (by simpa only [div_one] using reflection_log_10.1) (by simpa only [div_one] using reflection_log_10.2)
  let x111 : ℝ := x106*x110
  have hx111 : Bounds (-91930209947 / 250000000000) (-367720839073 / 1000000000000) x111 := by
    apply bounds_mul hx106 hx110 <;> norm_num
  let x112 : ℝ := x103+x111
  have hx112 : Bounds (89574656843 / 200000000000) (223936643287 / 500000000000) x112 := by
    apply bounds_add hx103 hx111 <;> norm_num
  let x113 : ℝ := (2 / 1)⁻¹
  have hx113 : Bounds (1 / 2) (1 / 2) x113 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x114 : ℝ := x112*x113
  have hx114 : Bounds (223936642107 / 1000000000000) (223936643287 / 1000000000000) x114 := by
    apply bounds_mul hx112 hx113 <;> norm_num
  let x115 : ℝ := x112/(2 / 1)
  have hx115 : Bounds (223936642107 / 1000000000000) (223936643287 / 1000000000000) x115 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx114
  let x116 : ℝ := -x115
  have hx116 : Bounds (-223936643287 / 1000000000000) (-223936642107 / 1000000000000) x116 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx115
  let x117 : ℝ := x99+x116
  have hx117 : Bounds (469210536713 / 1000000000000) (469210538893 / 1000000000000) x117 := by
    apply bounds_add hx99 hx116 <;> norm_num
  let x118 : ℝ := x99-x115
  have hx118 : Bounds (469210536713 / 1000000000000) (469210538893 / 1000000000000) x118 := by
    exact hx117
  let x119 : ℝ := biasE (64287 / 100000)
  have hx119 : Bounds (469210536713 / 1000000000000) (469210538893 / 1000000000000) x119 := by
    simpa +zetaDelta only [biasE, div_one] using hx118
  let x120 : ℝ := Real.log (2 / 1)
  have hx120 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x120 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x121 : ℝ := (1 / 1)+(322449 / 500000)
  have hx121 : Bounds (822449 / 500000) (822449 / 500000) x121 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((322449 / 500000) : ℝ)) <;> norm_num
  let x122 : ℝ := (1 / 1)+(322449 / 500000)
  have hx122 : Bounds (822449 / 500000) (822449 / 500000) x122 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((322449 / 500000) : ℝ)) <;> norm_num
  let x123 : ℝ := Real.log x122
  have hx123 : Bounds (62209797 / 125000000) (497678377 / 1000000000) x123 := by
    exact bounds_log hx122 (by norm_num) (by simpa only [div_one] using reflection_log_11.1) (by simpa only [div_one] using reflection_log_11.2)
  let x124 : ℝ := x121*x123
  have hx124 : Bounds (32745206613 / 40000000000) (818630166971 / 1000000000000) x124 := by
    apply bounds_mul hx121 hx123 <;> norm_num
  let x125 : ℝ := -(322449 / 500000)
  have hx125 : Bounds (-322449 / 500000) (-322449 / 500000) x125 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((322449 / 500000) : ℝ))
  let x126 : ℝ := (1 / 1)+x125
  have hx126 : Bounds (177551 / 500000) (177551 / 500000) x126 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx125 <;> norm_num
  let x127 : ℝ := (1 / 1)-(322449 / 500000)
  have hx127 : Bounds (177551 / 500000) (177551 / 500000) x127 := by
    exact hx126
  let x128 : ℝ := -(322449 / 500000)
  have hx128 : Bounds (-322449 / 500000) (-322449 / 500000) x128 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((322449 / 500000) : ℝ))
  let x129 : ℝ := (1 / 1)+x128
  have hx129 : Bounds (177551 / 500000) (177551 / 500000) x129 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx128 <;> norm_num
  let x130 : ℝ := (1 / 1)-(322449 / 500000)
  have hx130 : Bounds (177551 / 500000) (177551 / 500000) x130 := by
    exact hx129
  let x131 : ℝ := Real.log x130
  have hx131 : Bounds (-16177347 / 15625000) (-517675103 / 500000000) x131 := by
    exact bounds_log hx130 (by norm_num) (by simpa only [div_one] using reflection_log_12.1) (by simpa only [div_one] using reflection_log_12.2)
  let x132 : ℝ := x127*x131
  have hx132 : Bounds (-183827464781 / 500000000000) (-367654928851 / 1000000000000) x132 := by
    apply bounds_mul hx127 hx131 <;> norm_num
  let x133 : ℝ := x124+x132
  have hx133 : Bounds (450975235763 / 1000000000000) (11274380953 / 25000000000) x133 := by
    apply bounds_add hx124 hx132 <;> norm_num
  let x134 : ℝ := (2 / 1)⁻¹
  have hx134 : Bounds (1 / 2) (1 / 2) x134 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x135 : ℝ := x133*x134
  have hx135 : Bounds (225487617881 / 1000000000000) (11274380953 / 50000000000) x135 := by
    apply bounds_mul hx133 hx134 <;> norm_num
  let x136 : ℝ := x133/(2 / 1)
  have hx136 : Bounds (225487617881 / 1000000000000) (11274380953 / 50000000000) x136 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx135
  let x137 : ℝ := -x136
  have hx137 : Bounds (-11274380953 / 50000000000) (-225487617881 / 1000000000000) x137 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx136
  let x138 : ℝ := x120+x137
  have hx138 : Bounds (23382978047 / 50000000000) (467659563119 / 1000000000000) x138 := by
    apply bounds_add hx120 hx137 <;> norm_num
  let x139 : ℝ := x120-x136
  have hx139 : Bounds (23382978047 / 50000000000) (467659563119 / 1000000000000) x139 := by
    exact hx138
  let x140 : ℝ := biasE (322449 / 500000)
  have hx140 : Bounds (23382978047 / 50000000000) (467659563119 / 1000000000000) x140 := by
    simpa +zetaDelta only [biasE, div_one] using hx139
  let y : ℝ := 1 - 2 * entropyInverse ((1 + H (2*m - 1/2))/2)
  have hLh' : Real.log 2 * ((1 + H (2*m - 1/2))/2) = x98 := by
    simpa +zetaDelta only [div_one] using hLh
  have hy : Bounds (64287 / 100000) (322449 / 500000) y := by
    apply entropyInverseBias_bracket
    · exact div_nonneg (add_nonneg zero_le_one
        (H_nonneg (by linarith [hm.1]) (by linarith [hm.2]))) two_pos.le
    · linarith [H_le_one (2*m-1/2)]
    · norm_num
    · norm_num
    · norm_num
    · have h1 : biasE (322449 / 500000) ≤ (467659563119 / 1000000000000) := hx140.2
      have h2 : (233829856371 / 500000000000) ≤ x98 := hx98.1
      linarith [hLh']
    · have h1 : x98 ≤ (469210349913 / 1000000000000) := hx98.2
      have h2 : (469210536713 / 1000000000000) ≤ biasE (64287 / 100000) := hx119.1
      linarith [hLh']
  let x141 : ℝ := x3⁻¹
  have hx141 : Bounds (2302158273381 / 1000000000000) (1154192966637 / 500000000000) x141 := by
    apply bounds_inv hx3 <;> norm_num
  let x142 : ℝ := x98*x141
  have hx142 : Bounds (215325335363 / 200000000000) (541559285743 / 500000000000) x142 := by
    apply bounds_mul hx98 hx141 <;> norm_num
  let x143 : ℝ := x98/x3
  have hx143 : Bounds (215325335363 / 200000000000) (541559285743 / 500000000000) x143 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx142
  let x144 : ℝ := Real.log (2 / 1)
  have hx144 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x144 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x145 : ℝ := (1 / 1)+(512661 / 1000000)
  have hx145 : Bounds (1512661 / 1000000) (1512661 / 1000000) x145 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((512661 / 1000000) : ℝ)) <;> norm_num
  let x146 : ℝ := (1 / 1)+(512661 / 1000000)
  have hx146 : Bounds (1512661 / 1000000) (1512661 / 1000000) x146 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((512661 / 1000000) : ℝ)) <;> norm_num
  let x147 : ℝ := Real.log x146
  have hx147 : Bounds (413870351 / 1000000000) (25866897 / 62500000) x147 := by
    exact bounds_log hx146 (by norm_num) (by simpa only [div_one] using reflection_log_13.1) (by simpa only [div_one] using reflection_log_13.2)
  let x148 : ℝ := x145*x147
  have hx148 : Bounds (313022769507 / 500000000000) (626045540527 / 1000000000000) x148 := by
    apply bounds_mul hx145 hx147 <;> norm_num
  let x149 : ℝ := -(512661 / 1000000)
  have hx149 : Bounds (-512661 / 1000000) (-512661 / 1000000) x149 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((512661 / 1000000) : ℝ))
  let x150 : ℝ := (1 / 1)+x149
  have hx150 : Bounds (487339 / 1000000) (487339 / 1000000) x150 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx149 <;> norm_num
  let x151 : ℝ := (1 / 1)-(512661 / 1000000)
  have hx151 : Bounds (487339 / 1000000) (487339 / 1000000) x151 := by
    exact hx150
  let x152 : ℝ := -(512661 / 1000000)
  have hx152 : Bounds (-512661 / 1000000) (-512661 / 1000000) x152 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((512661 / 1000000) : ℝ))
  let x153 : ℝ := (1 / 1)+x152
  have hx153 : Bounds (487339 / 1000000) (487339 / 1000000) x153 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx152 <;> norm_num
  let x154 : ℝ := (1 / 1)-(512661 / 1000000)
  have hx154 : Bounds (487339 / 1000000) (487339 / 1000000) x154 := by
    exact hx153
  let x155 : ℝ := Real.log x154
  have hx155 : Bounds (-7187953 / 10000000) (-359397649 / 500000000) x155 := by
    exact bounds_log hx154 (by norm_num) (by simpa only [div_one] using reflection_log_14.1) (by simpa only [div_one] using reflection_log_14.2)
  let x156 : ℝ := x151*x155
  have hx156 : Bounds (-350296982707 / 1000000000000) (-87574245433 / 250000000000) x156 := by
    apply bounds_mul hx151 hx155 <;> norm_num
  let x157 : ℝ := x148+x156
  have hx157 : Bounds (275748556307 / 1000000000000) (55149711759 / 200000000000) x157 := by
    apply bounds_add hx148 hx156 <;> norm_num
  let x158 : ℝ := (2 / 1)⁻¹
  have hx158 : Bounds (1 / 2) (1 / 2) x158 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x159 : ℝ := x157*x158
  have hx159 : Bounds (137874278153 / 1000000000000) (68937139699 / 500000000000) x159 := by
    apply bounds_mul hx157 hx158 <;> norm_num
  let x160 : ℝ := x157/(2 / 1)
  have hx160 : Bounds (137874278153 / 1000000000000) (68937139699 / 500000000000) x160 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx159
  let x161 : ℝ := -x160
  have hx161 : Bounds (-68937139699 / 500000000000) (-137874278153 / 1000000000000) x161 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx160
  let x162 : ℝ := x144+x161
  have hx162 : Bounds (277636450301 / 500000000000) (555272902847 / 1000000000000) x162 := by
    apply bounds_add hx144 hx161 <;> norm_num
  let x163 : ℝ := x144-x160
  have hx163 : Bounds (277636450301 / 500000000000) (555272902847 / 1000000000000) x163 := by
    exact hx162
  let x164 : ℝ := biasE (512661 / 1000000)
  have hx164 : Bounds (277636450301 / 500000000000) (555272902847 / 1000000000000) x164 := by
    simpa +zetaDelta only [biasE, div_one] using hx163
  let x165 : ℝ := Real.log (2 / 1)
  have hx165 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x165 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x166 : ℝ := (1 / 1)+(257343 / 500000)
  have hx166 : Bounds (757343 / 500000) (757343 / 500000) x166 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((257343 / 500000) : ℝ)) <;> norm_num
  let x167 : ℝ := (1 / 1)+(257343 / 500000)
  have hx167 : Bounds (757343 / 500000) (757343 / 500000) x167 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((257343 / 500000) : ℝ)) <;> norm_num
  let x168 : ℝ := Real.log x167
  have hx168 : Bounds (103802039 / 250000000) (415208157 / 1000000000) x168 := by
    exact bounds_log hx167 (by norm_num) (by simpa only [div_one] using reflection_log_15.1) (by simpa only [div_one] using reflection_log_15.2)
  let x169 : ℝ := x166*x168
  have hx169 : Bounds (628909980979 / 1000000000000) (314454991247 / 500000000000) x169 := by
    apply bounds_mul hx166 hx168 <;> norm_num
  let x170 : ℝ := -(257343 / 500000)
  have hx170 : Bounds (-257343 / 500000) (-257343 / 500000) x170 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((257343 / 500000) : ℝ))
  let x171 : ℝ := (1 / 1)+x170
  have hx171 : Bounds (242657 / 500000) (242657 / 500000) x171 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx170 <;> norm_num
  let x172 : ℝ := (1 / 1)-(257343 / 500000)
  have hx172 : Bounds (242657 / 500000) (242657 / 500000) x172 := by
    exact hx171
  let x173 : ℝ := -(257343 / 500000)
  have hx173 : Bounds (-257343 / 500000) (-257343 / 500000) x173 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((257343 / 500000) : ℝ))
  let x174 : ℝ := (1 / 1)+x173
  have hx174 : Bounds (242657 / 500000) (242657 / 500000) x174 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx173 <;> norm_num
  let x175 : ℝ := (1 / 1)-(257343 / 500000)
  have hx175 : Bounds (242657 / 500000) (242657 / 500000) x175 := by
    exact hx174
  let x176 : ℝ := Real.log x175
  have hx176 : Bounds (-90369897 / 125000000) (-361479587 / 500000000) x176 := by
    exact bounds_log hx175 (by norm_num) (by simpa only [div_one] using reflection_log_16.1) (by simpa only [div_one] using reflection_log_16.2)
  let x177 : ℝ := x172*x176
  have hx177 : Bounds (-175431104771 / 500000000000) (-35086220857 / 100000000000) x177 := by
    apply bounds_mul hx172 hx176 <;> norm_num
  let x178 : ℝ := x169+x177
  have hx178 : Bounds (278047771437 / 1000000000000) (69511943481 / 250000000000) x178 := by
    apply bounds_add hx169 hx177 <;> norm_num
  let x179 : ℝ := (2 / 1)⁻¹
  have hx179 : Bounds (1 / 2) (1 / 2) x179 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x180 : ℝ := x178*x179
  have hx180 : Bounds (69511942859 / 500000000000) (69511943481 / 500000000000) x180 := by
    apply bounds_mul hx178 hx179 <;> norm_num
  let x181 : ℝ := x178/(2 / 1)
  have hx181 : Bounds (69511942859 / 500000000000) (69511943481 / 500000000000) x181 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx180
  let x182 : ℝ := -x181
  have hx182 : Bounds (-69511943481 / 500000000000) (-69511942859 / 500000000000) x182 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx181
  let x183 : ℝ := x165+x182
  have hx183 : Bounds (277061646519 / 500000000000) (277061647641 / 500000000000) x183 := by
    apply bounds_add hx165 hx182 <;> norm_num
  let x184 : ℝ := x165-x181
  have hx184 : Bounds (277061646519 / 500000000000) (277061647641 / 500000000000) x184 := by
    exact hx183
  let x185 : ℝ := biasE (257343 / 500000)
  have hx185 : Bounds (277061646519 / 500000000000) (277061647641 / 500000000000) x185 := by
    simpa +zetaDelta only [biasE, div_one] using hx184
  let x186 : ℝ := x143*(512661 / 1000000)
  have hx186 : Bounds (275972254381 / 500000000000) (555272649977 / 1000000000000) x186 := by
    apply bounds_mul hx143 (bounds_const ((512661 / 1000000) : ℝ)) <;> norm_num
  let x187 : ℝ := x143*(257343 / 500000)
  have hx187 : Bounds (554124677783 / 1000000000000) (139366491271 / 250000000000) x187 := by
    apply bounds_mul hx143 (bounds_const ((257343 / 500000) : ℝ)) <;> norm_num
  let c : ℝ := Reflection.regularContact (x3 / (Real.log 2 * ((1 + H (2*m - 1/2))/2)))
  have hcMem := Reflection.regularContact_mem
    (x3 / (Real.log 2 * ((1 + H (2*m - 1/2))/2)))
  have hc0 : 0 ≤ c := by
    dsimp only [c]
    apply GeneralCK.Certificates.RegularContactBounds.regularContact_nonneg
    rw [hLh']
    exact div_nonneg (by linarith [hx3.1]) (by linarith [hx98.1])
  have hcEq : biasE c = x143 * c := by
    have he := Reflection.regularContact_equation (x3 / x98)
    have hcdef : c = Reflection.regularContact (x3 / x98) := by
      dsimp only [c]
      rw [hLh']
    rw [← hcdef] at he
    change biasE c = (x98 / x3) * c
    have hx0 : 0 < x3 := by linarith [hx3.1]
    have hh0 : 0 < x98 := by linarith [hx98.1]
    field_simp [hx0.ne', hh0.ne'] at he ⊢
    nlinarith
  have hc : Bounds (512661 / 1000000) (257343 / 500000) c := by
    apply contact_bracket hc0 hcMem.2.le (by norm_num) (by norm_num) (by norm_num)
      (show 0 < x143 by linarith [hx143.1]) hcEq
    · have h1 : x143 * (512661 / 1000000) ≤ (555272649977 / 1000000000000) := hx186.2
      have h2 : (277636450301 / 500000000000) ≤ biasE (512661 / 1000000) := hx164.1
      linarith
    · have h1 : biasE (257343 / 500000) ≤ (277061647641 / 500000000000) := hx185.2
      have h2 : (554124677783 / 1000000000000) ≤ x143 * (257343 / 500000) := hx187.1
      linarith
  let x188 : ℝ := (1 / 1)+y
  have hx188 : Bounds (164287 / 100000) (822449 / 500000) x188 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hy <;> norm_num
  let x189 : ℝ := -y
  have hx189 : Bounds (-322449 / 500000) (-64287 / 100000) x189 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hy
  let x190 : ℝ := (1 / 1)+x189
  have hx190 : Bounds (177551 / 500000) (35713 / 100000) x190 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx189 <;> norm_num
  let x191 : ℝ := (1 / 1)-y
  have hx191 : Bounds (177551 / 500000) (35713 / 100000) x191 := by
    exact hx190
  let x192 : ℝ := x191⁻¹
  have hx192 : Bounds (700025200907 / 250000000000) (176005767357 / 62500000000) x192 := by
    apply bounds_inv hx191 <;> norm_num
  let x193 : ℝ := x188*x192
  have hx193 : Bounds (575025200907 / 125000000000) (144755767357 / 31250000000) x193 := by
    apply bounds_mul hx188 hx192 <;> norm_num
  let x194 : ℝ := x188/x191
  have hx194 : Bounds (575025200907 / 125000000000) (144755767357 / 31250000000) x194 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx193
  let x195 : ℝ := Real.log x194
  have hx195 : Bounds (1526100129 / 1000000000) (191628573 / 125000000) x195 := by
    exact bounds_log hx194 (by norm_num) (by simpa only [div_one] using reflection_log_17.1) (by simpa only [div_one] using reflection_log_18.2)
  let x196 : ℝ := (2 / 1)⁻¹
  have hx196 : Bounds (1 / 2) (1 / 2) x196 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x197 : ℝ := x195*x196
  have hx197 : Bounds (1526100129 / 2000000000) (191628573 / 250000000) x197 := by
    apply bounds_mul hx195 hx196 <;> norm_num
  let x198 : ℝ := x195/(2 / 1)
  have hx198 : Bounds (1526100129 / 2000000000) (191628573 / 250000000) x198 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx197
  let x199 : ℝ := (1 / 1)+c
  have hx199 : Bounds (1512661 / 1000000) (757343 / 500000) x199 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hc <;> norm_num
  let x200 : ℝ := -c
  have hx200 : Bounds (-257343 / 500000) (-512661 / 1000000) x200 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hc
  let x201 : ℝ := (1 / 1)+x200
  have hx201 : Bounds (242657 / 500000) (487339 / 1000000) x201 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx200 <;> norm_num
  let x202 : ℝ := (1 / 1)-c
  have hx202 : Bounds (242657 / 500000) (487339 / 1000000) x202 := by
    exact hx201
  let x203 : ℝ := x202⁻¹
  have hx203 : Bounds (1025979862067 / 500000000000) (2060521641659 / 1000000000000) x203 := by
    apply bounds_inv hx202 <;> norm_num
  let x204 : ℝ := x199*x203
  have hx204 : Bounds (775979862067 / 250000000000) (1560521641659 / 500000000000) x204 := by
    apply bounds_mul hx199 hx203 <;> norm_num
  let x205 : ℝ := x199/x202
  have hx205 : Bounds (775979862067 / 250000000000) (1560521641659 / 500000000000) x205 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx204
  let x206 : ℝ := Real.log x205
  have hx206 : Bounds (22653313 / 20000000) (1138167333 / 1000000000) x206 := by
    exact bounds_log hx205 (by norm_num) (by simpa only [div_one] using reflection_log_19.1) (by simpa only [div_one] using reflection_log_20.2)
  let x207 : ℝ := (2 / 1)⁻¹
  have hx207 : Bounds (1 / 2) (1 / 2) x207 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x208 : ℝ := x206*x207
  have hx208 : Bounds (22653313 / 40000000) (1138167333 / 2000000000) x208 := by
    apply bounds_mul hx206 hx207 <;> norm_num
  let x209 : ℝ := x206/(2 / 1)
  have hx209 : Bounds (22653313 / 40000000) (1138167333 / 2000000000) x209 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx208
  let x210 : ℝ := (2 / 1)*x50
  have hx210 : Bounds (119118007187 / 100000000000) (37258402399 / 31250000000) x210 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx50 <;> norm_num
  let x211 : ℝ := (2 / 1)*x98
  have hx211 : Bounds (233829856371 / 250000000000) (469210349913 / 500000000000) x211 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx98 <;> norm_num
  let x212 : ℝ := -x211
  have hx212 : Bounds (-469210349913 / 500000000000) (-233829856371 / 250000000000) x212 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx211
  let x213 : ℝ := x210+x212
  have hx213 : Bounds (63189843011 / 250000000000) (64237362821 / 250000000000) x213 := by
    apply bounds_add hx210 hx212 <;> norm_num
  let x214 : ℝ := x210-x211
  have hx214 : Bounds (63189843011 / 250000000000) (64237362821 / 250000000000) x214 := by
    exact hx213
  let x215 : ℝ := y*x198
  have hx215 : Bounds (98108398993 / 200000000000) (494323533883 / 1000000000000) x215 := by
    apply bounds_mul hy hx198 <;> norm_num
  let x216 : ℝ := -x215
  have hx216 : Bounds (-494323533883 / 1000000000000) (-98108398993 / 200000000000) x216 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx215
  let x217 : ℝ := x214+x216
  have hx217 : Bounds (-241564161839 / 1000000000000) (-233592543681 / 1000000000000) x217 := by
    apply bounds_add hx214 hx216 <;> norm_num
  let x218 : ℝ := x214-x215
  have hx218 : Bounds (-241564161839 / 1000000000000) (-233592543681 / 1000000000000) x218 := by
    exact hx217
  let x219 : ℝ := x3*x209
  have hx219 : Bounds (12266857479 / 50000000000) (61798929409 / 250000000000) x219 := by
    apply bounds_mul hx3 hx209 <;> norm_num
  let x220 : ℝ := x218+x219
  have hx220 : Bounds (3772987741 / 1000000000000) (2720634791 / 200000000000) x220 := by
    apply bounds_add hx218 hx219 <;> norm_num
  have hpos : 0 < x220 := lt_of_lt_of_le (by norm_num) hx220.1
  have hcert :
      0 ≤ 2 * biasE (1 - 2*m) - 2*(x98)
        - (1 - 2*entropyInverse ((1 + H (2*m - 1/2))/2)) *
            SmallMean.A (1 - 2*entropyInverse ((1 + H (2*m - 1/2))/2))
        + (1 - 2*m) *
            SmallMean.A (regularContact ((1 - 2*m)/(Real.log 2*((1 + H (2*m - 1/2))/2)))) := by
    simpa +zetaDelta only [SmallMean.A, div_one] using hpos.le
  dsimp only
  nlinarith [hcert, hLh]

theorem acceptedCertificate : DoubleCapBiasCellCertificate (181 / 640) (1451 / 5120) (fun m => (1 + H (2*m - 1/2))/2) where
  domain := by norm_num
  sound m hmLo hmHi := by
    exact cell_bias_nonneg m ⟨hmLo, hmHi⟩

theorem accepted_cell :
    ∀ m, (181 / 640) ≤ m → m ≤ (1451 / 5120) → 0 ≤ doubleCapHighResidual m := by
  intro m hmLo hmHi
  unfold doubleCapHighResidual
  apply doubleCapEndpointResidual_nonneg_of_biasCell acceptedCertificate hmLo hmHi
  exact div_pos (by linarith [H_nonneg (by linarith : 0 ≤ 2*m-1/2) (by linarith : 2*m-1/2 ≤ 1)]) two_pos

#print axioms cell_bias_nonneg
#print axioms accepted_cell

end GeneralCK.Certificates.DoubleCapMiddle.Cell0067

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0068 =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0068
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Reflection
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem cell_bias_nonneg (m : ℝ) (hm : Bounds (1451 / 5120) (727 / 2560) m) :
    let h := (1 + H (2*m - 1/2))/2
    let x := 1-2*m
    let y := 1-2*entropyInverse h
    let c := regularContact (x/(Real.log 2*h))
    0 ≤ 2*(biasE x-Real.log 2*h)-y*SmallMean.A y+x*SmallMean.A c := by
  have hEq : biasE (2-4*m) = Real.log 2 * H (2*m-1/2) := by
    have hmstrict : 1/4 < m := by
      have hlo : (1/4 : ℝ) < (1451 / 5120) := by norm_num
      exact lt_of_lt_of_le hlo hm.1
    rw [show 2-4*m = 1-2*(2*m-1/2) by ring,
      GeneralCK.Correction.Natural.biasE_probability (by linarith [hmstrict]) (by linarith [hm.2]),
      GeneralCK.Certificates.Mixed.hn_eq_H_mul_log]
    ring
  have hLh : Real.log 2 * ((1 + H (2*m - 1/2))/2) = (Real.log 2 + biasE (2-4*m))/2 := by
    rw [hEq]
    ring
  let x0 : ℝ := (2 / 1)*m
  have hx0 : Bounds (1451 / 2560) (727 / 1280) x0 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hm <;> norm_num
  let x1 : ℝ := -x0
  have hx1 : Bounds (-727 / 1280) (-1451 / 2560) x1 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx0
  let x2 : ℝ := (1 / 1)+x1
  have hx2 : Bounds (553 / 1280) (1109 / 2560) x2 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx1 <;> norm_num
  let x3 : ℝ := (1 / 1)-x0
  have hx3 : Bounds (553 / 1280) (1109 / 2560) x3 := by
    exact hx2
  let x4 : ℝ := (4 / 1)*m
  have hx4 : Bounds (1451 / 1280) (727 / 640) x4 := by
    apply bounds_mul (bounds_const ((4 / 1) : ℝ)) hm <;> norm_num
  let x5 : ℝ := -x4
  have hx5 : Bounds (-727 / 640) (-1451 / 1280) x5 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx4
  let x6 : ℝ := (2 / 1)+x5
  have hx6 : Bounds (553 / 640) (1109 / 1280) x6 := by
    apply bounds_add (bounds_const ((2 / 1) : ℝ)) hx5 <;> norm_num
  let x7 : ℝ := (2 / 1)-x4
  have hx7 : Bounds (553 / 640) (1109 / 1280) x7 := by
    exact hx6
  let x8 : ℝ := Real.log (2 / 1)
  have hx8 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x8 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x9 : ℝ := (1 / 1)+(1109 / 2560)
  have hx9 : Bounds (3669 / 2560) (3669 / 2560) x9 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1109 / 2560) : ℝ)) <;> norm_num
  let x10 : ℝ := (1 / 1)+(1109 / 2560)
  have hx10 : Bounds (3669 / 2560) (3669 / 2560) x10 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1109 / 2560) : ℝ)) <;> norm_num
  let x11 : ℝ := Real.log x10
  have hx11 : Bounds (179955943 / 500000000) (359911887 / 1000000000) x11 := by
    exact bounds_log hx10 (by norm_num) (by simpa only [div_one] using reflection_log_1.1) (by simpa only [div_one] using reflection_log_1.2)
  let x12 : ℝ := x9*x11
  have hx12 : Bounds (515826839739 / 1000000000000) (257913420587 / 500000000000) x12 := by
    apply bounds_mul hx9 hx11 <;> norm_num
  let x13 : ℝ := -(1109 / 2560)
  have hx13 : Bounds (-1109 / 2560) (-1109 / 2560) x13 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1109 / 2560) : ℝ))
  let x14 : ℝ := (1 / 1)+x13
  have hx14 : Bounds (1451 / 2560) (1451 / 2560) x14 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx13 <;> norm_num
  let x15 : ℝ := (1 / 1)-(1109 / 2560)
  have hx15 : Bounds (1451 / 2560) (1451 / 2560) x15 := by
    exact hx14
  let x16 : ℝ := -(1109 / 2560)
  have hx16 : Bounds (-1109 / 2560) (-1109 / 2560) x16 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1109 / 2560) : ℝ))
  let x17 : ℝ := (1 / 1)+x16
  have hx17 : Bounds (1451 / 2560) (1451 / 2560) x17 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx16 <;> norm_num
  let x18 : ℝ := (1 / 1)-(1109 / 2560)
  have hx18 : Bounds (1451 / 2560) (1451 / 2560) x18 := by
    exact hx17
  let x19 : ℝ := Real.log x18
  have hx19 : Bounds (-113550857 / 200000000) (-141938571 / 250000000) x19 := by
    exact bounds_log hx18 (by norm_num) (by simpa only [div_one] using reflection_log_2.1) (by simpa only [div_one] using reflection_log_2.2)
  let x20 : ℝ := x15*x19
  have hx20 : Bounds (-160900677253 / 500000000000) (-321801353939 / 1000000000000) x20 := by
    apply bounds_mul hx15 hx19 <;> norm_num
  let x21 : ℝ := x12+x20
  have hx21 : Bounds (194025485233 / 1000000000000) (38805097447 / 200000000000) x21 := by
    apply bounds_add hx12 hx20 <;> norm_num
  let x22 : ℝ := (2 / 1)⁻¹
  have hx22 : Bounds (1 / 2) (1 / 2) x22 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x23 : ℝ := x21*x22
  have hx23 : Bounds (12126592827 / 125000000000) (48506371809 / 500000000000) x23 := by
    apply bounds_mul hx21 hx22 <;> norm_num
  let x24 : ℝ := x21/(2 / 1)
  have hx24 : Bounds (12126592827 / 125000000000) (48506371809 / 500000000000) x24 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx23
  let x25 : ℝ := -x24
  have hx25 : Bounds (-48506371809 / 500000000000) (-12126592827 / 125000000000) x25 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx24
  let x26 : ℝ := x8+x25
  have hx26 : Bounds (298067218191 / 500000000000) (37258402399 / 62500000000) x26 := by
    apply bounds_add hx8 hx25 <;> norm_num
  let x27 : ℝ := x8-x24
  have hx27 : Bounds (298067218191 / 500000000000) (37258402399 / 62500000000) x27 := by
    exact hx26
  let x28 : ℝ := biasE (1109 / 2560)
  have hx28 : Bounds (298067218191 / 500000000000) (37258402399 / 62500000000) x28 := by
    simpa +zetaDelta only [biasE, div_one] using hx27
  let x29 : ℝ := Real.log (2 / 1)
  have hx29 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x29 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x30 : ℝ := (1 / 1)+(553 / 1280)
  have hx30 : Bounds (1833 / 1280) (1833 / 1280) x30 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((553 / 1280) : ℝ)) <;> norm_num
  let x31 : ℝ := (1 / 1)+(553 / 1280)
  have hx31 : Bounds (1833 / 1280) (1833 / 1280) x31 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((553 / 1280) : ℝ)) <;> norm_num
  let x32 : ℝ := Real.log x31
  have hx32 : Bounds (35909389 / 100000000) (359093891 / 1000000000) x32 := by
    exact bounds_log hx31 (by norm_num) (by simpa only [div_one] using reflection_log_3.1) (by simpa only [div_one] using reflection_log_3.2)
  let x33 : ℝ := x30*x32
  have hx33 : Bounds (128558418041 / 250000000000) (514233673597 / 1000000000000) x33 := by
    apply bounds_mul hx30 hx32 <;> norm_num
  let x34 : ℝ := -(553 / 1280)
  have hx34 : Bounds (-553 / 1280) (-553 / 1280) x34 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((553 / 1280) : ℝ))
  let x35 : ℝ := (1 / 1)+x34
  have hx35 : Bounds (727 / 1280) (727 / 1280) x35 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx34 <;> norm_num
  let x36 : ℝ := (1 / 1)-(553 / 1280)
  have hx36 : Bounds (727 / 1280) (727 / 1280) x36 := by
    exact hx35
  let x37 : ℝ := -(553 / 1280)
  have hx37 : Bounds (-553 / 1280) (-553 / 1280) x37 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((553 / 1280) : ℝ))
  let x38 : ℝ := (1 / 1)+x37
  have hx38 : Bounds (727 / 1280) (727 / 1280) x38 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx37 <;> norm_num
  let x39 : ℝ := (1 / 1)-(553 / 1280)
  have hx39 : Bounds (727 / 1280) (727 / 1280) x39 := by
    exact hx38
  let x40 : ℝ := Real.log x39
  have hx40 : Bounds (-7071111 / 12500000) (-565688879 / 1000000000) x40 := by
    exact bounds_log hx39 (by norm_num) (by simpa only [div_one] using reflection_log_4.1) (by simpa only [div_one] using reflection_log_4.2)
  let x41 : ℝ := x36*x40
  have hx41 : Bounds (-321293606063 / 1000000000000) (-160646802747 / 500000000000) x41 := by
    apply bounds_mul hx36 hx40 <;> norm_num
  let x42 : ℝ := x33+x41
  have hx42 : Bounds (192940066101 / 1000000000000) (192940068103 / 1000000000000) x42 := by
    apply bounds_add hx33 hx41 <;> norm_num
  let x43 : ℝ := (2 / 1)⁻¹
  have hx43 : Bounds (1 / 2) (1 / 2) x43 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x44 : ℝ := x42*x43
  have hx44 : Bounds (1929400661 / 20000000000) (24117508513 / 250000000000) x44 := by
    apply bounds_mul hx42 hx43 <;> norm_num
  let x45 : ℝ := x42/(2 / 1)
  have hx45 : Bounds (1929400661 / 20000000000) (24117508513 / 250000000000) x45 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx44
  let x46 : ℝ := -x45
  have hx46 : Bounds (-24117508513 / 250000000000) (-1929400661 / 20000000000) x46 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx45
  let x47 : ℝ := x29+x46
  have hx47 : Bounds (149169286487 / 250000000000) (11933542959 / 20000000000) x47 := by
    apply bounds_add hx29 hx46 <;> norm_num
  let x48 : ℝ := x29-x45
  have hx48 : Bounds (149169286487 / 250000000000) (11933542959 / 20000000000) x48 := by
    exact hx47
  let x49 : ℝ := biasE (553 / 1280)
  have hx49 : Bounds (149169286487 / 250000000000) (11933542959 / 20000000000) x49 := by
    simpa +zetaDelta only [biasE, div_one] using hx48
  let x50 : ℝ := biasE x3
  have hx50 : Bounds (298067218191 / 500000000000) (11933542959 / 20000000000) x50 := by
    exact bounds_biasE hx3 (by norm_num) (by norm_num) hx28.1 hx49.2
  let x51 : ℝ := Real.log (2 / 1)
  have hx51 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x51 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x52 : ℝ := (1 / 1)+(1109 / 1280)
  have hx52 : Bounds (2389 / 1280) (2389 / 1280) x52 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1109 / 1280) : ℝ)) <;> norm_num
  let x53 : ℝ := (1 / 1)+(1109 / 1280)
  have hx53 : Bounds (2389 / 1280) (2389 / 1280) x53 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1109 / 1280) : ℝ)) <;> norm_num
  let x54 : ℝ := Real.log x53
  have hx54 : Bounds (62401479 / 100000000) (624014791 / 1000000000) x54 := by
    exact bounds_log hx53 (by norm_num) (by simpa only [div_one] using reflection_log_5.1) (by simpa only [div_one] using reflection_log_5.2)
  let x55 : ℝ := x52*x54
  have hx55 : Bounds (291166276037 / 250000000000) (232933021203 / 200000000000) x55 := by
    apply bounds_mul hx52 hx54 <;> norm_num
  let x56 : ℝ := -(1109 / 1280)
  have hx56 : Bounds (-1109 / 1280) (-1109 / 1280) x56 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1109 / 1280) : ℝ))
  let x57 : ℝ := (1 / 1)+x56
  have hx57 : Bounds (171 / 1280) (171 / 1280) x57 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx56 <;> norm_num
  let x58 : ℝ := (1 / 1)-(1109 / 1280)
  have hx58 : Bounds (171 / 1280) (171 / 1280) x58 := by
    exact hx57
  let x59 : ℝ := -(1109 / 1280)
  have hx59 : Bounds (-1109 / 1280) (-1109 / 1280) x59 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1109 / 1280) : ℝ))
  let x60 : ℝ := (1 / 1)+x59
  have hx60 : Bounds (171 / 1280) (171 / 1280) x60 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx59 <;> norm_num
  let x61 : ℝ := (1 / 1)-(1109 / 1280)
  have hx61 : Bounds (171 / 1280) (171 / 1280) x61 := by
    exact hx60
  let x62 : ℝ := Real.log x61
  have hx62 : Bounds (-1006475901 / 500000000) (-2012951799 / 1000000000) x62 := by
    exact bounds_log hx61 (by norm_num) (by simpa only [div_one] using reflection_log_6.1) (by simpa only [div_one] using reflection_log_6.2)
  let x63 : ℝ := x58*x62
  have hx63 : Bounds (-268917779799 / 1000000000000) (-268917779397 / 1000000000000) x63 := by
    apply bounds_mul hx58 hx62 <;> norm_num
  let x64 : ℝ := x55+x63
  have hx64 : Bounds (895747324349 / 1000000000000) (447873663309 / 500000000000) x64 := by
    apply bounds_add hx55 hx63 <;> norm_num
  let x65 : ℝ := (2 / 1)⁻¹
  have hx65 : Bounds (1 / 2) (1 / 2) x65 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x66 : ℝ := x64*x65
  have hx66 : Bounds (223936831087 / 500000000000) (447873663309 / 1000000000000) x66 := by
    apply bounds_mul hx64 hx65 <;> norm_num
  let x67 : ℝ := x64/(2 / 1)
  have hx67 : Bounds (223936831087 / 500000000000) (447873663309 / 1000000000000) x67 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx66
  let x68 : ℝ := -x67
  have hx68 : Bounds (-447873663309 / 1000000000000) (-223936831087 / 500000000000) x68 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx67
  let x69 : ℝ := x51+x68
  have hx69 : Bounds (245273516691 / 1000000000000) (122636759413 / 500000000000) x69 := by
    apply bounds_add hx51 hx68 <;> norm_num
  let x70 : ℝ := x51-x67
  have hx70 : Bounds (245273516691 / 1000000000000) (122636759413 / 500000000000) x70 := by
    exact hx69
  let x71 : ℝ := biasE (1109 / 1280)
  have hx71 : Bounds (245273516691 / 1000000000000) (122636759413 / 500000000000) x71 := by
    simpa +zetaDelta only [biasE, div_one] using hx70
  let x72 : ℝ := Real.log (2 / 1)
  have hx72 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x72 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x73 : ℝ := (1 / 1)+(553 / 640)
  have hx73 : Bounds (1193 / 640) (1193 / 640) x73 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((553 / 640) : ℝ)) <;> norm_num
  let x74 : ℝ := (1 / 1)+(553 / 640)
  have hx74 : Bounds (1193 / 640) (1193 / 640) x74 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((553 / 640) : ℝ)) <;> norm_num
  let x75 : ℝ := Real.log x74
  have hx75 : Bounds (124551649 / 200000000) (311379123 / 500000000) x75 := by
    exact bounds_log hx74 (by norm_num) (by simpa only [div_one] using reflection_log_7.1) (by simpa only [div_one] using reflection_log_7.2)
  let x76 : ℝ := x73*x75
  have hx76 : Bounds (116086029107 / 100000000000) (232172058587 / 200000000000) x76 := by
    apply bounds_mul hx73 hx75 <;> norm_num
  let x77 : ℝ := -(553 / 640)
  have hx77 : Bounds (-553 / 640) (-553 / 640) x77 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((553 / 640) : ℝ))
  let x78 : ℝ := (1 / 1)+x77
  have hx78 : Bounds (87 / 640) (87 / 640) x78 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx77 <;> norm_num
  let x79 : ℝ := (1 / 1)-(553 / 640)
  have hx79 : Bounds (87 / 640) (87 / 640) x79 := by
    exact hx78
  let x80 : ℝ := -(553 / 640)
  have hx80 : Bounds (-553 / 640) (-553 / 640) x80 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((553 / 640) : ℝ))
  let x81 : ℝ := (1 / 1)+x80
  have hx81 : Bounds (87 / 640) (87 / 640) x81 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx80 <;> norm_num
  let x82 : ℝ := (1 / 1)-(553 / 640)
  have hx82 : Bounds (87 / 640) (87 / 640) x82 := by
    exact hx81
  let x83 : ℝ := Real.log x82
  have hx83 : Bounds (-1995560059 / 1000000000) (-249445007 / 125000000) x83 := by
    exact bounds_log hx82 (by norm_num) (by simpa only [div_one] using reflection_log_8.1) (by simpa only [div_one] using reflection_log_8.2)
  let x84 : ℝ := x79*x83
  have hx84 : Bounds (-271271445521 / 1000000000000) (-33908930639 / 125000000000) x84 := by
    apply bounds_mul hx79 hx83 <;> norm_num
  let x85 : ℝ := x76+x84
  have hx85 : Bounds (889588845549 / 1000000000000) (889588847823 / 1000000000000) x85 := by
    apply bounds_add hx76 hx84 <;> norm_num
  let x86 : ℝ := (2 / 1)⁻¹
  have hx86 : Bounds (1 / 2) (1 / 2) x86 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x87 : ℝ := x85*x86
  have hx87 : Bounds (222397211387 / 500000000000) (55599302989 / 125000000000) x87 := by
    apply bounds_mul hx85 hx86 <;> norm_num
  let x88 : ℝ := x85/(2 / 1)
  have hx88 : Bounds (222397211387 / 500000000000) (55599302989 / 125000000000) x88 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx87
  let x89 : ℝ := -x88
  have hx89 : Bounds (-55599302989 / 125000000000) (-222397211387 / 500000000000) x89 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx88
  let x90 : ℝ := x72+x89
  have hx90 : Bounds (31044094511 / 125000000000) (124176379113 / 500000000000) x90 := by
    apply bounds_add hx72 hx89 <;> norm_num
  let x91 : ℝ := x72-x88
  have hx91 : Bounds (31044094511 / 125000000000) (124176379113 / 500000000000) x91 := by
    exact hx90
  let x92 : ℝ := biasE (553 / 640)
  have hx92 : Bounds (31044094511 / 125000000000) (124176379113 / 500000000000) x92 := by
    simpa +zetaDelta only [biasE, div_one] using hx91
  let x93 : ℝ := biasE x7
  have hx93 : Bounds (245273516691 / 1000000000000) (124176379113 / 500000000000) x93 := by
    exact bounds_biasE hx7 (by norm_num) (by norm_num) hx71.1 hx92.2
  let x94 : ℝ := Real.log (2 / 1)
  have hx94 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x94 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x95 : ℝ := x94+x93
  have hx95 : Bounds (938420696691 / 1000000000000) (470749969613 / 500000000000) x95 := by
    apply bounds_add hx94 hx93 <;> norm_num
  let x96 : ℝ := (2 / 1)⁻¹
  have hx96 : Bounds (1 / 2) (1 / 2) x96 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x97 : ℝ := x95*x96
  have hx97 : Bounds (93842069669 / 200000000000) (470749969613 / 1000000000000) x97 := by
    apply bounds_mul hx95 hx96 <;> norm_num
  let x98 : ℝ := x95/(2 / 1)
  have hx98 : Bounds (93842069669 / 200000000000) (470749969613 / 1000000000000) x98 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx97
  let x99 : ℝ := Real.log (2 / 1)
  have hx99 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x99 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x100 : ℝ := (1 / 1)+(640847 / 1000000)
  have hx100 : Bounds (1640847 / 1000000) (1640847 / 1000000) x100 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((640847 / 1000000) : ℝ)) <;> norm_num
  let x101 : ℝ := (1 / 1)+(640847 / 1000000)
  have hx101 : Bounds (1640847 / 1000000) (1640847 / 1000000) x101 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((640847 / 1000000) : ℝ)) <;> norm_num
  let x102 : ℝ := Real.log x101
  have hx102 : Bounds (495212571 / 1000000000) (123803143 / 250000000) x102 := by
    exact bounds_log hx101 (by norm_num) (by simpa only [div_one] using reflection_log_9.1) (by simpa only [div_one] using reflection_log_9.2)
  let x103 : ℝ := x100*x102
  have hx103 : Bounds (812568061487 / 1000000000000) (812568063129 / 1000000000000) x103 := by
    apply bounds_mul hx100 hx102 <;> norm_num
  let x104 : ℝ := -(640847 / 1000000)
  have hx104 : Bounds (-640847 / 1000000) (-640847 / 1000000) x104 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((640847 / 1000000) : ℝ))
  let x105 : ℝ := (1 / 1)+x104
  have hx105 : Bounds (359153 / 1000000) (359153 / 1000000) x105 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx104 <;> norm_num
  let x106 : ℝ := (1 / 1)-(640847 / 1000000)
  have hx106 : Bounds (359153 / 1000000) (359153 / 1000000) x106 := by
    exact hx105
  let x107 : ℝ := -(640847 / 1000000)
  have hx107 : Bounds (-640847 / 1000000) (-640847 / 1000000) x107 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((640847 / 1000000) : ℝ))
  let x108 : ℝ := (1 / 1)+x107
  have hx108 : Bounds (359153 / 1000000) (359153 / 1000000) x108 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx107 <;> norm_num
  let x109 : ℝ := (1 / 1)-(640847 / 1000000)
  have hx109 : Bounds (359153 / 1000000) (359153 / 1000000) x109 := by
    exact hx108
  let x110 : ℝ := Real.log x109
  have hx110 : Bounds (-512003399 / 500000000) (-256001699 / 250000000) x110 := by
    exact bounds_log hx109 (by norm_num) (by simpa only [div_one] using reflection_log_10.1) (by simpa only [div_one] using reflection_log_10.2)
  let x111 : ℝ := x106*x110
  have hx111 : Bounds (-367775113523 / 1000000000000) (-367775112803 / 1000000000000) x111 := by
    apply bounds_mul hx106 hx110 <;> norm_num
  let x112 : ℝ := x103+x111
  have hx112 : Bounds (111198236991 / 250000000000) (222396475163 / 500000000000) x112 := by
    apply bounds_add hx103 hx111 <;> norm_num
  let x113 : ℝ := (2 / 1)⁻¹
  have hx113 : Bounds (1 / 2) (1 / 2) x113 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x114 : ℝ := x112*x113
  have hx114 : Bounds (111198236991 / 500000000000) (222396475163 / 1000000000000) x114 := by
    apply bounds_mul hx112 hx113 <;> norm_num
  let x115 : ℝ := x112/(2 / 1)
  have hx115 : Bounds (111198236991 / 500000000000) (222396475163 / 1000000000000) x115 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx114
  let x116 : ℝ := -x115
  have hx116 : Bounds (-222396475163 / 1000000000000) (-111198236991 / 500000000000) x116 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx115
  let x117 : ℝ := x99+x116
  have hx117 : Bounds (470750704837 / 1000000000000) (235375353509 / 500000000000) x117 := by
    apply bounds_add hx99 hx116 <;> norm_num
  let x118 : ℝ := x99-x115
  have hx118 : Bounds (470750704837 / 1000000000000) (235375353509 / 500000000000) x118 := by
    exact hx117
  let x119 : ℝ := biasE (640847 / 1000000)
  have hx119 : Bounds (470750704837 / 1000000000000) (235375353509 / 500000000000) x119 := by
    simpa +zetaDelta only [biasE, div_one] using hx118
  let x120 : ℝ := Real.log (2 / 1)
  have hx120 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x120 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x121 : ℝ := (1 / 1)+(642871 / 1000000)
  have hx121 : Bounds (1642871 / 1000000) (1642871 / 1000000) x121 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((642871 / 1000000) : ℝ)) <;> norm_num
  let x122 : ℝ := (1 / 1)+(642871 / 1000000)
  have hx122 : Bounds (1642871 / 1000000) (1642871 / 1000000) x122 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((642871 / 1000000) : ℝ)) <;> norm_num
  let x123 : ℝ := Real.log x122
  have hx123 : Bounds (496445321 / 1000000000) (248222661 / 500000000) x123 := by
    exact bounds_log hx122 (by norm_num) (by simpa only [div_one] using reflection_log_11.1) (by simpa only [div_one] using reflection_log_11.2)
  let x124 : ℝ := x121*x123
  have hx124 : Bounds (203898905239 / 250000000000) (4077978113 / 5000000000) x124 := by
    apply bounds_mul hx121 hx123 <;> norm_num
  let x125 : ℝ := -(642871 / 1000000)
  have hx125 : Bounds (-642871 / 1000000) (-642871 / 1000000) x125 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((642871 / 1000000) : ℝ))
  let x126 : ℝ := (1 / 1)+x125
  have hx126 : Bounds (357129 / 1000000) (357129 / 1000000) x126 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx125 <;> norm_num
  let x127 : ℝ := (1 / 1)-(642871 / 1000000)
  have hx127 : Bounds (357129 / 1000000) (357129 / 1000000) x127 := by
    exact hx126
  let x128 : ℝ := -(642871 / 1000000)
  have hx128 : Bounds (-642871 / 1000000) (-642871 / 1000000) x128 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((642871 / 1000000) : ℝ))
  let x129 : ℝ := (1 / 1)+x128
  have hx129 : Bounds (357129 / 1000000) (357129 / 1000000) x129 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx128 <;> norm_num
  let x130 : ℝ := (1 / 1)-(642871 / 1000000)
  have hx130 : Bounds (357129 / 1000000) (357129 / 1000000) x130 := by
    exact hx129
  let x131 : ℝ := Real.log x130
  have hx131 : Bounds (-1029658219 / 1000000000) (-1029658217 / 1000000000) x131 := by
    exact bounds_log hx130 (by norm_num) (by simpa only [div_one] using reflection_log_12.1) (by simpa only [div_one] using reflection_log_12.2)
  let x132 : ℝ := x127*x131
  have hx132 : Bounds (-183860405047 / 500000000000) (-183860404689 / 500000000000) x132 := by
    apply bounds_mul hx127 hx131 <;> norm_num
  let x133 : ℝ := x124+x132
  have hx133 : Bounds (223937405431 / 500000000000) (223937406611 / 500000000000) x133 := by
    apply bounds_add hx124 hx132 <;> norm_num
  let x134 : ℝ := (2 / 1)⁻¹
  have hx134 : Bounds (1 / 2) (1 / 2) x134 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x135 : ℝ := x133*x134
  have hx135 : Bounds (223937405431 / 1000000000000) (223937406611 / 1000000000000) x135 := by
    apply bounds_mul hx133 hx134 <;> norm_num
  let x136 : ℝ := x133/(2 / 1)
  have hx136 : Bounds (223937405431 / 1000000000000) (223937406611 / 1000000000000) x136 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx135
  let x137 : ℝ := -x136
  have hx137 : Bounds (-223937406611 / 1000000000000) (-223937405431 / 1000000000000) x137 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx136
  let x138 : ℝ := x120+x137
  have hx138 : Bounds (469209773389 / 1000000000000) (469209775569 / 1000000000000) x138 := by
    apply bounds_add hx120 hx137 <;> norm_num
  let x139 : ℝ := x120-x136
  have hx139 : Bounds (469209773389 / 1000000000000) (469209775569 / 1000000000000) x139 := by
    exact hx138
  let x140 : ℝ := biasE (642871 / 1000000)
  have hx140 : Bounds (469209773389 / 1000000000000) (469209775569 / 1000000000000) x140 := by
    simpa +zetaDelta only [biasE, div_one] using hx139
  let y : ℝ := 1 - 2 * entropyInverse ((1 + H (2*m - 1/2))/2)
  have hLh' : Real.log 2 * ((1 + H (2*m - 1/2))/2) = x98 := by
    simpa +zetaDelta only [div_one] using hLh
  have hy : Bounds (640847 / 1000000) (642871 / 1000000) y := by
    apply entropyInverseBias_bracket
    · exact div_nonneg (add_nonneg zero_le_one
        (H_nonneg (by linarith [hm.1]) (by linarith [hm.2]))) two_pos.le
    · linarith [H_le_one (2*m-1/2)]
    · norm_num
    · norm_num
    · norm_num
    · have h1 : biasE (642871 / 1000000) ≤ (469209775569 / 1000000000000) := hx140.2
      have h2 : (93842069669 / 200000000000) ≤ x98 := hx98.1
      linarith [hLh']
    · have h1 : x98 ≤ (470749969613 / 1000000000000) := hx98.2
      have h2 : (470750704837 / 1000000000000) ≤ biasE (640847 / 1000000) := hx119.1
      linarith [hLh']
  let x141 : ℝ := x3⁻¹
  have hx141 : Bounds (2308385933273 / 1000000000000) (2314647377939 / 1000000000000) x141 := by
    apply bounds_inv hx3 <;> norm_num
  let x142 : ℝ := x98*x141
  have hx142 : Bounds (216623713573 / 200000000000) (108962018283 / 100000000000) x142 := by
    apply bounds_mul hx98 hx141 <;> norm_num
  let x143 : ℝ := x98/x3
  have hx143 : Bounds (216623713573 / 200000000000) (108962018283 / 100000000000) x143 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx142
  let x144 : ℝ := Real.log (2 / 1)
  have hx144 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x144 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x145 : ℝ := (1 / 1)+(255323 / 500000)
  have hx145 : Bounds (755323 / 500000) (755323 / 500000) x145 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((255323 / 500000) : ℝ)) <;> norm_num
  let x146 : ℝ := (1 / 1)+(255323 / 500000)
  have hx146 : Bounds (755323 / 500000) (755323 / 500000) x146 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((255323 / 500000) : ℝ)) <;> norm_num
  let x147 : ℝ := Real.log x146
  have hx147 : Bounds (412537373 / 1000000000) (206268687 / 500000000) x147 := by
    exact bounds_log hx146 (by norm_num) (by simpa only [div_one] using reflection_log_13.1) (by simpa only [div_one] using reflection_log_13.2)
  let x148 : ℝ := x145*x147
  have hx148 : Bounds (155799483093 / 250000000000) (155799483471 / 250000000000) x148 := by
    apply bounds_mul hx145 hx147 <;> norm_num
  let x149 : ℝ := -(255323 / 500000)
  have hx149 : Bounds (-255323 / 500000) (-255323 / 500000) x149 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((255323 / 500000) : ℝ))
  let x150 : ℝ := (1 / 1)+x149
  have hx150 : Bounds (244677 / 500000) (244677 / 500000) x150 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx149 <;> norm_num
  let x151 : ℝ := (1 / 1)-(255323 / 500000)
  have hx151 : Bounds (244677 / 500000) (244677 / 500000) x151 := by
    exact hx150
  let x152 : ℝ := -(255323 / 500000)
  have hx152 : Bounds (-255323 / 500000) (-255323 / 500000) x152 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((255323 / 500000) : ℝ))
  let x153 : ℝ := (1 / 1)+x152
  have hx153 : Bounds (244677 / 500000) (244677 / 500000) x153 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx152 <;> norm_num
  let x154 : ℝ := (1 / 1)-(255323 / 500000)
  have hx154 : Bounds (244677 / 500000) (244677 / 500000) x154 := by
    exact hx153
  let x155 : ℝ := Real.log x154
  have hx155 : Bounds (-357334563 / 500000000) (-178667281 / 250000000) x155 := by
    exact bounds_log hx154 (by norm_num) (by simpa only [div_one] using reflection_log_14.1) (by simpa only [div_one] using reflection_log_14.2)
  let x156 : ℝ := x151*x155
  have hx156 : Bounds (-69945239097 / 200000000000) (-69945238901 / 200000000000) x156 := by
    apply bounds_mul hx151 hx155 <;> norm_num
  let x157 : ℝ := x148+x156
  have hx157 : Bounds (273471736887 / 1000000000000) (273471739379 / 1000000000000) x157 := by
    apply bounds_add hx148 hx156 <;> norm_num
  let x158 : ℝ := (2 / 1)⁻¹
  have hx158 : Bounds (1 / 2) (1 / 2) x158 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x159 : ℝ := x157*x158
  have hx159 : Bounds (136735868443 / 1000000000000) (13673586969 / 100000000000) x159 := by
    apply bounds_mul hx157 hx158 <;> norm_num
  let x160 : ℝ := x157/(2 / 1)
  have hx160 : Bounds (136735868443 / 1000000000000) (13673586969 / 100000000000) x160 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx159
  let x161 : ℝ := -x160
  have hx161 : Bounds (-13673586969 / 100000000000) (-136735868443 / 1000000000000) x161 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx160
  let x162 : ℝ := x144+x161
  have hx162 : Bounds (55641131031 / 100000000000) (556411312557 / 1000000000000) x162 := by
    apply bounds_add hx144 hx161 <;> norm_num
  let x163 : ℝ := x144-x160
  have hx163 : Bounds (55641131031 / 100000000000) (556411312557 / 1000000000000) x163 := by
    exact hx162
  let x164 : ℝ := biasE (255323 / 500000)
  have hx164 : Bounds (55641131031 / 100000000000) (556411312557 / 1000000000000) x164 := by
    simpa +zetaDelta only [biasE, div_one] using hx163
  let x165 : ℝ := Real.log (2 / 1)
  have hx165 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x165 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x166 : ℝ := (1 / 1)+(256331 / 500000)
  have hx166 : Bounds (756331 / 500000) (756331 / 500000) x166 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((256331 / 500000) : ℝ)) <;> norm_num
  let x167 : ℝ := (1 / 1)+(256331 / 500000)
  have hx167 : Bounds (756331 / 500000) (756331 / 500000) x167 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((256331 / 500000) : ℝ)) <;> norm_num
  let x168 : ℝ := Real.log x167
  have hx168 : Bounds (103467753 / 250000000) (413871013 / 1000000000) x168 := by
    exact bounds_log hx167 (by norm_num) (by simpa only [div_one] using reflection_log_15.1) (by simpa only [div_one] using reflection_log_15.2)
  let x169 : ℝ := x166*x168
  have hx169 : Bounds (626046952753 / 1000000000000) (626046954267 / 1000000000000) x169 := by
    apply bounds_mul hx166 hx168 <;> norm_num
  let x170 : ℝ := -(256331 / 500000)
  have hx170 : Bounds (-256331 / 500000) (-256331 / 500000) x170 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((256331 / 500000) : ℝ))
  let x171 : ℝ := (1 / 1)+x170
  have hx171 : Bounds (243669 / 500000) (243669 / 500000) x171 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx170 <;> norm_num
  let x172 : ℝ := (1 / 1)-(256331 / 500000)
  have hx172 : Bounds (243669 / 500000) (243669 / 500000) x172 := by
    exact hx171
  let x173 : ℝ := -(256331 / 500000)
  have hx173 : Bounds (-256331 / 500000) (-256331 / 500000) x173 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((256331 / 500000) : ℝ))
  let x174 : ℝ := (1 / 1)+x173
  have hx174 : Bounds (243669 / 500000) (243669 / 500000) x174 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx173 <;> norm_num
  let x175 : ℝ := (1 / 1)-(256331 / 500000)
  have hx175 : Bounds (243669 / 500000) (243669 / 500000) x175 := by
    exact hx174
  let x176 : ℝ := Real.log x175
  have hx176 : Bounds (-89849669 / 125000000) (-14375947 / 20000000) x176 := by
    exact bounds_log hx175 (by norm_num) (by simpa only [div_one] using reflection_log_16.1) (by simpa only [div_one] using reflection_log_16.2)
  let x177 : ℝ := x172*x176
  have hx177 : Bounds (-350297263929 / 1000000000000) (-175148631477 / 500000000000) x177 := by
    apply bounds_mul hx172 hx176 <;> norm_num
  let x178 : ℝ := x169+x177
  have hx178 : Bounds (34468711103 / 125000000000) (275749691313 / 1000000000000) x178 := by
    apply bounds_add hx169 hx177 <;> norm_num
  let x179 : ℝ := (2 / 1)⁻¹
  have hx179 : Bounds (1 / 2) (1 / 2) x179 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x180 : ℝ := x178*x179
  have hx180 : Bounds (34468711103 / 250000000000) (137874845657 / 1000000000000) x180 := by
    apply bounds_mul hx178 hx179 <;> norm_num
  let x181 : ℝ := x178/(2 / 1)
  have hx181 : Bounds (34468711103 / 250000000000) (137874845657 / 1000000000000) x181 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx180
  let x182 : ℝ := -x181
  have hx182 : Bounds (-137874845657 / 1000000000000) (-34468711103 / 250000000000) x182 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx181
  let x183 : ℝ := x165+x182
  have hx183 : Bounds (555272334343 / 1000000000000) (138818084147 / 250000000000) x183 := by
    apply bounds_add hx165 hx182 <;> norm_num
  let x184 : ℝ := x165-x181
  have hx184 : Bounds (555272334343 / 1000000000000) (138818084147 / 250000000000) x184 := by
    exact hx183
  let x185 : ℝ := biasE (256331 / 500000)
  have hx185 : Bounds (555272334343 / 1000000000000) (138818084147 / 250000000000) x185 := by
    simpa +zetaDelta only [biasE, div_one] using hx184
  let x186 : ℝ := x143*(255323 / 500000)
  have hx186 : Bounds (110618032841 / 200000000000) (278205093941 / 500000000000) x186 := by
    apply bounds_mul hx143 (bounds_const ((255323 / 500000) : ℝ)) <;> norm_num
  let x187 : ℝ := x143*(256331 / 500000)
  have hx187 : Bounds (277636865619 / 500000000000) (55860686217 / 100000000000) x187 := by
    apply bounds_mul hx143 (bounds_const ((256331 / 500000) : ℝ)) <;> norm_num
  let c : ℝ := Reflection.regularContact (x3 / (Real.log 2 * ((1 + H (2*m - 1/2))/2)))
  have hcMem := Reflection.regularContact_mem
    (x3 / (Real.log 2 * ((1 + H (2*m - 1/2))/2)))
  have hc0 : 0 ≤ c := by
    dsimp only [c]
    apply GeneralCK.Certificates.RegularContactBounds.regularContact_nonneg
    rw [hLh']
    exact div_nonneg (by linarith [hx3.1]) (by linarith [hx98.1])
  have hcEq : biasE c = x143 * c := by
    have he := Reflection.regularContact_equation (x3 / x98)
    have hcdef : c = Reflection.regularContact (x3 / x98) := by
      dsimp only [c]
      rw [hLh']
    rw [← hcdef] at he
    change biasE c = (x98 / x3) * c
    have hx0 : 0 < x3 := by linarith [hx3.1]
    have hh0 : 0 < x98 := by linarith [hx98.1]
    field_simp [hx0.ne', hh0.ne'] at he ⊢
    nlinarith
  have hc : Bounds (255323 / 500000) (256331 / 500000) c := by
    apply contact_bracket hc0 hcMem.2.le (by norm_num) (by norm_num) (by norm_num)
      (show 0 < x143 by linarith [hx143.1]) hcEq
    · have h1 : x143 * (255323 / 500000) ≤ (278205093941 / 500000000000) := hx186.2
      have h2 : (55641131031 / 100000000000) ≤ biasE (255323 / 500000) := hx164.1
      linarith
    · have h1 : biasE (256331 / 500000) ≤ (138818084147 / 250000000000) := hx185.2
      have h2 : (277636865619 / 500000000000) ≤ x143 * (256331 / 500000) := hx187.1
      linarith
  let x188 : ℝ := (1 / 1)+y
  have hx188 : Bounds (1640847 / 1000000) (1642871 / 1000000) x188 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hy <;> norm_num
  let x189 : ℝ := -y
  have hx189 : Bounds (-642871 / 1000000) (-640847 / 1000000) x189 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hy
  let x190 : ℝ := (1 / 1)+x189
  have hx190 : Bounds (357129 / 1000000) (359153 / 1000000) x190 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx189 <;> norm_num
  let x191 : ℝ := (1 / 1)-y
  have hx191 : Bounds (357129 / 1000000) (359153 / 1000000) x191 := by
    exact hx190
  let x192 : ℝ := x191⁻¹
  have hx192 : Bounds (174020542777 / 62500000000) (350013580527 / 125000000000) x192 := by
    apply bounds_inv hx191 <;> norm_num
  let x193 : ℝ := x188*x192
  have hx193 : Bounds (142770542777 / 31250000000) (287513580527 / 62500000000) x193 := by
    apply bounds_mul hx188 hx192 <;> norm_num
  let x194 : ℝ := x188/x191
  have hx194 : Bounds (142770542777 / 31250000000) (287513580527 / 62500000000) x194 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx193
  let x195 : ℝ := Real.log x194
  have hx195 : Bounds (189902421 / 125000000) (76305177 / 50000000) x195 := by
    exact bounds_log hx194 (by norm_num) (by simpa only [div_one] using reflection_log_17.1) (by simpa only [div_one] using reflection_log_18.2)
  let x196 : ℝ := (2 / 1)⁻¹
  have hx196 : Bounds (1 / 2) (1 / 2) x196 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x197 : ℝ := x195*x196
  have hx197 : Bounds (189902421 / 250000000) (76305177 / 100000000) x197 := by
    apply bounds_mul hx195 hx196 <;> norm_num
  let x198 : ℝ := x195/(2 / 1)
  have hx198 : Bounds (189902421 / 250000000) (76305177 / 100000000) x198 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx197
  let x199 : ℝ := (1 / 1)+c
  have hx199 : Bounds (755323 / 500000) (756331 / 500000) x199 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hc <;> norm_num
  let x200 : ℝ := -c
  have hx200 : Bounds (-256331 / 500000) (-255323 / 500000) x200 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hc
  let x201 : ℝ := (1 / 1)+x200
  have hx201 : Bounds (243669 / 500000) (244677 / 500000) x201 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx200 <;> norm_num
  let x202 : ℝ := (1 / 1)-c
  have hx202 : Bounds (243669 / 500000) (244677 / 500000) x202 := by
    exact hx201
  let x203 : ℝ := x202⁻¹
  have hx203 : Bounds (1021755211973 / 500000000000) (1025981967341 / 500000000000) x203 := by
    apply bounds_inv hx202 <;> norm_num
  let x204 : ℝ := x199*x203
  have hx204 : Bounds (771755211973 / 250000000000) (775981967341 / 250000000000) x204 := by
    apply bounds_mul hx199 hx203 <;> norm_num
  let x205 : ℝ := x199/x202
  have hx205 : Bounds (771755211973 / 250000000000) (775981967341 / 250000000000) x205 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx204
  let x206 : ℝ := Real.log x205
  have hx206 : Bounds (563603249 / 500000000) (226533673 / 200000000) x206 := by
    exact bounds_log hx205 (by norm_num) (by simpa only [div_one] using reflection_log_19.1) (by simpa only [div_one] using reflection_log_20.2)
  let x207 : ℝ := (2 / 1)⁻¹
  have hx207 : Bounds (1 / 2) (1 / 2) x207 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x208 : ℝ := x206*x207
  have hx208 : Bounds (563603249 / 1000000000) (226533673 / 400000000) x208 := by
    apply bounds_mul hx206 hx207 <;> norm_num
  let x209 : ℝ := x206/(2 / 1)
  have hx209 : Bounds (563603249 / 1000000000) (226533673 / 400000000) x209 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx208
  let x210 : ℝ := (2 / 1)*x50
  have hx210 : Bounds (298067218191 / 250000000000) (11933542959 / 10000000000) x210 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx50 <;> norm_num
  let x211 : ℝ := (2 / 1)*x98
  have hx211 : Bounds (93842069669 / 100000000000) (470749969613 / 500000000000) x211 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx98 <;> norm_num
  let x212 : ℝ := -x211
  have hx212 : Bounds (-470749969613 / 500000000000) (-93842069669 / 100000000000) x212 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx211
  let x213 : ℝ := x210+x212
  have hx213 : Bounds (125384466769 / 500000000000) (25493359921 / 100000000000) x213 := by
    apply bounds_add hx210 hx212 <;> norm_num
  let x214 : ℝ := x210-x211
  have hx214 : Bounds (125384466769 / 500000000000) (25493359921 / 100000000000) x214 := by
    exact hx213
  let x215 : ℝ := y*x198
  have hx215 : Bounds (243396793581 / 500000000000) (15329495451 / 31250000000) x215 := by
    apply bounds_mul hy hx198 <;> norm_num
  let x216 : ℝ := -x215
  have hx216 : Bounds (-15329495451 / 31250000000) (-243396793581 / 500000000000) x216 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx215
  let x217 : ℝ := x214+x216
  have hx217 : Bounds (-119887460447 / 500000000000) (-14491249247 / 62500000000) x217 := by
    apply bounds_add hx214 hx216 <;> norm_num
  let x218 : ℝ := x214-x215
  have hx218 : Bounds (-119887460447 / 500000000000) (-14491249247 / 62500000000) x218 := by
    exact hx217
  let x219 : ℝ := x3*x209
  have hx219 : Bounds (243494216169 / 1000000000000) (122668868827 / 500000000000) x219 := by
    apply bounds_mul hx3 hx209 <;> norm_num
  let x220 : ℝ := x218+x219
  have hx220 : Bounds (148771811 / 40000000000) (6738874851 / 500000000000) x220 := by
    apply bounds_add hx218 hx219 <;> norm_num
  have hpos : 0 < x220 := lt_of_lt_of_le (by norm_num) hx220.1
  have hcert :
      0 ≤ 2 * biasE (1 - 2*m) - 2*(x98)
        - (1 - 2*entropyInverse ((1 + H (2*m - 1/2))/2)) *
            SmallMean.A (1 - 2*entropyInverse ((1 + H (2*m - 1/2))/2))
        + (1 - 2*m) *
            SmallMean.A (regularContact ((1 - 2*m)/(Real.log 2*((1 + H (2*m - 1/2))/2)))) := by
    simpa +zetaDelta only [SmallMean.A, div_one] using hpos.le
  dsimp only
  nlinarith [hcert, hLh]

theorem acceptedCertificate : DoubleCapBiasCellCertificate (1451 / 5120) (727 / 2560) (fun m => (1 + H (2*m - 1/2))/2) where
  domain := by norm_num
  sound m hmLo hmHi := by
    exact cell_bias_nonneg m ⟨hmLo, hmHi⟩

theorem accepted_cell :
    ∀ m, (1451 / 5120) ≤ m → m ≤ (727 / 2560) → 0 ≤ doubleCapHighResidual m := by
  intro m hmLo hmHi
  unfold doubleCapHighResidual
  apply doubleCapEndpointResidual_nonneg_of_biasCell acceptedCertificate hmLo hmHi
  exact div_pos (by linarith [H_nonneg (by linarith : 0 ≤ 2*m-1/2) (by linarith : 2*m-1/2 ≤ 1)]) two_pos

#print axioms cell_bias_nonneg
#print axioms accepted_cell

end GeneralCK.Certificates.DoubleCapMiddle.Cell0068

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0069 =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0069
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Reflection
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem cell_bias_nonneg (m : ℝ) (hm : Bounds (727 / 2560) (1457 / 5120) m) :
    let h := (1 + H (2*m - 1/2))/2
    let x := 1-2*m
    let y := 1-2*entropyInverse h
    let c := regularContact (x/(Real.log 2*h))
    0 ≤ 2*(biasE x-Real.log 2*h)-y*SmallMean.A y+x*SmallMean.A c := by
  have hEq : biasE (2-4*m) = Real.log 2 * H (2*m-1/2) := by
    have hmstrict : 1/4 < m := by
      have hlo : (1/4 : ℝ) < (727 / 2560) := by norm_num
      exact lt_of_lt_of_le hlo hm.1
    rw [show 2-4*m = 1-2*(2*m-1/2) by ring,
      GeneralCK.Correction.Natural.biasE_probability (by linarith [hmstrict]) (by linarith [hm.2]),
      GeneralCK.Certificates.Mixed.hn_eq_H_mul_log]
    ring
  have hLh : Real.log 2 * ((1 + H (2*m - 1/2))/2) = (Real.log 2 + biasE (2-4*m))/2 := by
    rw [hEq]
    ring
  let x0 : ℝ := (2 / 1)*m
  have hx0 : Bounds (727 / 1280) (1457 / 2560) x0 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hm <;> norm_num
  let x1 : ℝ := -x0
  have hx1 : Bounds (-1457 / 2560) (-727 / 1280) x1 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx0
  let x2 : ℝ := (1 / 1)+x1
  have hx2 : Bounds (1103 / 2560) (553 / 1280) x2 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx1 <;> norm_num
  let x3 : ℝ := (1 / 1)-x0
  have hx3 : Bounds (1103 / 2560) (553 / 1280) x3 := by
    exact hx2
  let x4 : ℝ := (4 / 1)*m
  have hx4 : Bounds (727 / 640) (1457 / 1280) x4 := by
    apply bounds_mul (bounds_const ((4 / 1) : ℝ)) hm <;> norm_num
  let x5 : ℝ := -x4
  have hx5 : Bounds (-1457 / 1280) (-727 / 640) x5 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx4
  let x6 : ℝ := (2 / 1)+x5
  have hx6 : Bounds (1103 / 1280) (553 / 640) x6 := by
    apply bounds_add (bounds_const ((2 / 1) : ℝ)) hx5 <;> norm_num
  let x7 : ℝ := (2 / 1)-x4
  have hx7 : Bounds (1103 / 1280) (553 / 640) x7 := by
    exact hx6
  let x8 : ℝ := Real.log (2 / 1)
  have hx8 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x8 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x9 : ℝ := (1 / 1)+(553 / 1280)
  have hx9 : Bounds (1833 / 1280) (1833 / 1280) x9 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((553 / 1280) : ℝ)) <;> norm_num
  let x10 : ℝ := (1 / 1)+(553 / 1280)
  have hx10 : Bounds (1833 / 1280) (1833 / 1280) x10 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((553 / 1280) : ℝ)) <;> norm_num
  let x11 : ℝ := Real.log x10
  have hx11 : Bounds (35909389 / 100000000) (359093891 / 1000000000) x11 := by
    exact bounds_log hx10 (by norm_num) (by simpa only [div_one] using reflection_log_1.1) (by simpa only [div_one] using reflection_log_1.2)
  let x12 : ℝ := x9*x11
  have hx12 : Bounds (128558418041 / 250000000000) (514233673597 / 1000000000000) x12 := by
    apply bounds_mul hx9 hx11 <;> norm_num
  let x13 : ℝ := -(553 / 1280)
  have hx13 : Bounds (-553 / 1280) (-553 / 1280) x13 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((553 / 1280) : ℝ))
  let x14 : ℝ := (1 / 1)+x13
  have hx14 : Bounds (727 / 1280) (727 / 1280) x14 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx13 <;> norm_num
  let x15 : ℝ := (1 / 1)-(553 / 1280)
  have hx15 : Bounds (727 / 1280) (727 / 1280) x15 := by
    exact hx14
  let x16 : ℝ := -(553 / 1280)
  have hx16 : Bounds (-553 / 1280) (-553 / 1280) x16 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((553 / 1280) : ℝ))
  let x17 : ℝ := (1 / 1)+x16
  have hx17 : Bounds (727 / 1280) (727 / 1280) x17 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx16 <;> norm_num
  let x18 : ℝ := (1 / 1)-(553 / 1280)
  have hx18 : Bounds (727 / 1280) (727 / 1280) x18 := by
    exact hx17
  let x19 : ℝ := Real.log x18
  have hx19 : Bounds (-7071111 / 12500000) (-565688879 / 1000000000) x19 := by
    exact bounds_log hx18 (by norm_num) (by simpa only [div_one] using reflection_log_2.1) (by simpa only [div_one] using reflection_log_2.2)
  let x20 : ℝ := x15*x19
  have hx20 : Bounds (-321293606063 / 1000000000000) (-160646802747 / 500000000000) x20 := by
    apply bounds_mul hx15 hx19 <;> norm_num
  let x21 : ℝ := x12+x20
  have hx21 : Bounds (192940066101 / 1000000000000) (192940068103 / 1000000000000) x21 := by
    apply bounds_add hx12 hx20 <;> norm_num
  let x22 : ℝ := (2 / 1)⁻¹
  have hx22 : Bounds (1 / 2) (1 / 2) x22 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x23 : ℝ := x21*x22
  have hx23 : Bounds (1929400661 / 20000000000) (24117508513 / 250000000000) x23 := by
    apply bounds_mul hx21 hx22 <;> norm_num
  let x24 : ℝ := x21/(2 / 1)
  have hx24 : Bounds (1929400661 / 20000000000) (24117508513 / 250000000000) x24 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx23
  let x25 : ℝ := -x24
  have hx25 : Bounds (-24117508513 / 250000000000) (-1929400661 / 20000000000) x25 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx24
  let x26 : ℝ := x8+x25
  have hx26 : Bounds (149169286487 / 250000000000) (11933542959 / 20000000000) x26 := by
    apply bounds_add hx8 hx25 <;> norm_num
  let x27 : ℝ := x8-x24
  have hx27 : Bounds (149169286487 / 250000000000) (11933542959 / 20000000000) x27 := by
    exact hx26
  let x28 : ℝ := biasE (553 / 1280)
  have hx28 : Bounds (149169286487 / 250000000000) (11933542959 / 20000000000) x28 := by
    simpa +zetaDelta only [biasE, div_one] using hx27
  let x29 : ℝ := Real.log (2 / 1)
  have hx29 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x29 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x30 : ℝ := (1 / 1)+(1103 / 2560)
  have hx30 : Bounds (3663 / 2560) (3663 / 2560) x30 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1103 / 2560) : ℝ)) <;> norm_num
  let x31 : ℝ := (1 / 1)+(1103 / 2560)
  have hx31 : Bounds (3663 / 2560) (3663 / 2560) x31 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1103 / 2560) : ℝ)) <;> norm_num
  let x32 : ℝ := Real.log x31
  have hx32 : Bounds (14331009 / 40000000) (179137613 / 500000000) x32 := by
    exact bounds_log hx31 (by norm_num) (by simpa only [div_one] using reflection_log_3.1) (by simpa only [div_one] using reflection_log_3.2)
  let x33 : ℝ := x30*x32
  have hx33 : Bounds (512641464521 / 1000000000000) (512641465953 / 1000000000000) x33 := by
    apply bounds_mul hx30 hx32 <;> norm_num
  let x34 : ℝ := -(1103 / 2560)
  have hx34 : Bounds (-1103 / 2560) (-1103 / 2560) x34 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1103 / 2560) : ℝ))
  let x35 : ℝ := (1 / 1)+x34
  have hx35 : Bounds (1457 / 2560) (1457 / 2560) x35 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx34 <;> norm_num
  let x36 : ℝ := (1 / 1)-(1103 / 2560)
  have hx36 : Bounds (1457 / 2560) (1457 / 2560) x36 := by
    exact hx35
  let x37 : ℝ := -(1103 / 2560)
  have hx37 : Bounds (-1103 / 2560) (-1103 / 2560) x37 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1103 / 2560) : ℝ))
  let x38 : ℝ := (1 / 1)+x37
  have hx38 : Bounds (1457 / 2560) (1457 / 2560) x38 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx37 <;> norm_num
  let x39 : ℝ := (1 / 1)-(1103 / 2560)
  have hx39 : Bounds (1457 / 2560) (1457 / 2560) x39 := by
    exact hx38
  let x40 : ℝ := Real.log x39
  have hx40 : Bounds (-140906933 / 250000000) (-563627731 / 1000000000) x40 := by
    exact bounds_log hx39 (by norm_num) (by simpa only [div_one] using reflection_log_4.1) (by simpa only [div_one] using reflection_log_4.2)
  let x41 : ℝ := x36*x40
  have hx41 : Bounds (-160391719829 / 500000000000) (-20048964943 / 62500000000) x41 := by
    apply bounds_mul hx36 hx40 <;> norm_num
  let x42 : ℝ := x33+x41
  have hx42 : Bounds (191858024863 / 1000000000000) (38371605373 / 200000000000) x42 := by
    apply bounds_add hx33 hx41 <;> norm_num
  let x43 : ℝ := (2 / 1)⁻¹
  have hx43 : Bounds (1 / 2) (1 / 2) x43 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x44 : ℝ := x42*x43
  have hx44 : Bounds (95929012431 / 1000000000000) (95929013433 / 1000000000000) x44 := by
    apply bounds_mul hx42 hx43 <;> norm_num
  let x45 : ℝ := x42/(2 / 1)
  have hx45 : Bounds (95929012431 / 1000000000000) (95929013433 / 1000000000000) x45 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx44
  let x46 : ℝ := -x45
  have hx46 : Bounds (-95929013433 / 1000000000000) (-95929012431 / 1000000000000) x46 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx45
  let x47 : ℝ := x29+x46
  have hx47 : Bounds (597218166567 / 1000000000000) (597218168569 / 1000000000000) x47 := by
    apply bounds_add hx29 hx46 <;> norm_num
  let x48 : ℝ := x29-x45
  have hx48 : Bounds (597218166567 / 1000000000000) (597218168569 / 1000000000000) x48 := by
    exact hx47
  let x49 : ℝ := biasE (1103 / 2560)
  have hx49 : Bounds (597218166567 / 1000000000000) (597218168569 / 1000000000000) x49 := by
    simpa +zetaDelta only [biasE, div_one] using hx48
  let x50 : ℝ := biasE x3
  have hx50 : Bounds (149169286487 / 250000000000) (597218168569 / 1000000000000) x50 := by
    exact bounds_biasE hx3 (by norm_num) (by norm_num) hx28.1 hx49.2
  let x51 : ℝ := Real.log (2 / 1)
  have hx51 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x51 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x52 : ℝ := (1 / 1)+(553 / 640)
  have hx52 : Bounds (1193 / 640) (1193 / 640) x52 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((553 / 640) : ℝ)) <;> norm_num
  let x53 : ℝ := (1 / 1)+(553 / 640)
  have hx53 : Bounds (1193 / 640) (1193 / 640) x53 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((553 / 640) : ℝ)) <;> norm_num
  let x54 : ℝ := Real.log x53
  have hx54 : Bounds (124551649 / 200000000) (311379123 / 500000000) x54 := by
    exact bounds_log hx53 (by norm_num) (by simpa only [div_one] using reflection_log_5.1) (by simpa only [div_one] using reflection_log_5.2)
  let x55 : ℝ := x52*x54
  have hx55 : Bounds (116086029107 / 100000000000) (232172058587 / 200000000000) x55 := by
    apply bounds_mul hx52 hx54 <;> norm_num
  let x56 : ℝ := -(553 / 640)
  have hx56 : Bounds (-553 / 640) (-553 / 640) x56 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((553 / 640) : ℝ))
  let x57 : ℝ := (1 / 1)+x56
  have hx57 : Bounds (87 / 640) (87 / 640) x57 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx56 <;> norm_num
  let x58 : ℝ := (1 / 1)-(553 / 640)
  have hx58 : Bounds (87 / 640) (87 / 640) x58 := by
    exact hx57
  let x59 : ℝ := -(553 / 640)
  have hx59 : Bounds (-553 / 640) (-553 / 640) x59 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((553 / 640) : ℝ))
  let x60 : ℝ := (1 / 1)+x59
  have hx60 : Bounds (87 / 640) (87 / 640) x60 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx59 <;> norm_num
  let x61 : ℝ := (1 / 1)-(553 / 640)
  have hx61 : Bounds (87 / 640) (87 / 640) x61 := by
    exact hx60
  let x62 : ℝ := Real.log x61
  have hx62 : Bounds (-1995560059 / 1000000000) (-249445007 / 125000000) x62 := by
    exact bounds_log hx61 (by norm_num) (by simpa only [div_one] using reflection_log_6.1) (by simpa only [div_one] using reflection_log_6.2)
  let x63 : ℝ := x58*x62
  have hx63 : Bounds (-271271445521 / 1000000000000) (-33908930639 / 125000000000) x63 := by
    apply bounds_mul hx58 hx62 <;> norm_num
  let x64 : ℝ := x55+x63
  have hx64 : Bounds (889588845549 / 1000000000000) (889588847823 / 1000000000000) x64 := by
    apply bounds_add hx55 hx63 <;> norm_num
  let x65 : ℝ := (2 / 1)⁻¹
  have hx65 : Bounds (1 / 2) (1 / 2) x65 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x66 : ℝ := x64*x65
  have hx66 : Bounds (222397211387 / 500000000000) (55599302989 / 125000000000) x66 := by
    apply bounds_mul hx64 hx65 <;> norm_num
  let x67 : ℝ := x64/(2 / 1)
  have hx67 : Bounds (222397211387 / 500000000000) (55599302989 / 125000000000) x67 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx66
  let x68 : ℝ := -x67
  have hx68 : Bounds (-55599302989 / 125000000000) (-222397211387 / 500000000000) x68 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx67
  let x69 : ℝ := x51+x68
  have hx69 : Bounds (31044094511 / 125000000000) (124176379113 / 500000000000) x69 := by
    apply bounds_add hx51 hx68 <;> norm_num
  let x70 : ℝ := x51-x67
  have hx70 : Bounds (31044094511 / 125000000000) (124176379113 / 500000000000) x70 := by
    exact hx69
  let x71 : ℝ := biasE (553 / 640)
  have hx71 : Bounds (31044094511 / 125000000000) (124176379113 / 500000000000) x71 := by
    simpa +zetaDelta only [biasE, div_one] using hx70
  let x72 : ℝ := Real.log (2 / 1)
  have hx72 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x72 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x73 : ℝ := (1 / 1)+(1103 / 1280)
  have hx73 : Bounds (2383 / 1280) (2383 / 1280) x73 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1103 / 1280) : ℝ)) <;> norm_num
  let x74 : ℝ := (1 / 1)+(1103 / 1280)
  have hx74 : Bounds (2383 / 1280) (2383 / 1280) x74 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1103 / 1280) : ℝ)) <;> norm_num
  let x75 : ℝ := Real.log x74
  have hx75 : Bounds (15537503 / 25000000) (621500121 / 1000000000) x75 := by
    exact bounds_log hx74 (by norm_num) (by simpa only [div_one] using reflection_log_7.1) (by simpa only [div_one] using reflection_log_7.2)
  let x76 : ℝ := x73*x75
  have hx76 : Bounds (1157058426531 / 1000000000000) (1157058428393 / 1000000000000) x76 := by
    apply bounds_mul hx73 hx75 <;> norm_num
  let x77 : ℝ := -(1103 / 1280)
  have hx77 : Bounds (-1103 / 1280) (-1103 / 1280) x77 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1103 / 1280) : ℝ))
  let x78 : ℝ := (1 / 1)+x77
  have hx78 : Bounds (177 / 1280) (177 / 1280) x78 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx77 <;> norm_num
  let x79 : ℝ := (1 / 1)-(1103 / 1280)
  have hx79 : Bounds (177 / 1280) (177 / 1280) x79 := by
    exact hx78
  let x80 : ℝ := -(1103 / 1280)
  have hx80 : Bounds (-1103 / 1280) (-1103 / 1280) x80 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1103 / 1280) : ℝ))
  let x81 : ℝ := (1 / 1)+x80
  have hx81 : Bounds (177 / 1280) (177 / 1280) x81 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx80 <;> norm_num
  let x82 : ℝ := (1 / 1)-(1103 / 1280)
  have hx82 : Bounds (177 / 1280) (177 / 1280) x82 := by
    exact hx81
  let x83 : ℝ := Real.log x82
  have hx83 : Bounds (-989232813 / 500000000) (-1978465623 / 1000000000) x83 := by
    exact bounds_log hx82 (by norm_num) (by simpa only [div_one] using reflection_log_8.1) (by simpa only [div_one] using reflection_log_8.2)
  let x84 : ℝ := x79*x83
  have hx84 : Bounds (-136792349923 / 500000000000) (-27358469943 / 100000000000) x84 := by
    apply bounds_mul hx79 hx83 <;> norm_num
  let x85 : ℝ := x76+x84
  have hx85 : Bounds (176694745337 / 200000000000) (883473728963 / 1000000000000) x85 := by
    apply bounds_add hx76 hx84 <;> norm_num
  let x86 : ℝ := (2 / 1)⁻¹
  have hx86 : Bounds (1 / 2) (1 / 2) x86 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x87 : ℝ := x85*x86
  have hx87 : Bounds (220868431671 / 500000000000) (220868432241 / 500000000000) x87 := by
    apply bounds_mul hx85 hx86 <;> norm_num
  let x88 : ℝ := x85/(2 / 1)
  have hx88 : Bounds (220868431671 / 500000000000) (220868432241 / 500000000000) x88 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx87
  let x89 : ℝ := -x88
  have hx89 : Bounds (-220868432241 / 500000000000) (-220868431671 / 500000000000) x89 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx88
  let x90 : ℝ := x72+x89
  have hx90 : Bounds (125705157759 / 500000000000) (125705158829 / 500000000000) x90 := by
    apply bounds_add hx72 hx89 <;> norm_num
  let x91 : ℝ := x72-x88
  have hx91 : Bounds (125705157759 / 500000000000) (125705158829 / 500000000000) x91 := by
    exact hx90
  let x92 : ℝ := biasE (1103 / 1280)
  have hx92 : Bounds (125705157759 / 500000000000) (125705158829 / 500000000000) x92 := by
    simpa +zetaDelta only [biasE, div_one] using hx91
  let x93 : ℝ := biasE x7
  have hx93 : Bounds (31044094511 / 125000000000) (125705158829 / 500000000000) x93 := by
    exact bounds_biasE hx7 (by norm_num) (by norm_num) hx71.1 hx92.2
  let x94 : ℝ := Real.log (2 / 1)
  have hx94 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x94 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x95 : ℝ := x94+x93
  have hx95 : Bounds (117687492011 / 125000000000) (472278749329 / 500000000000) x95 := by
    apply bounds_add hx94 hx93 <;> norm_num
  let x96 : ℝ := (2 / 1)⁻¹
  have hx96 : Bounds (1 / 2) (1 / 2) x96 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x97 : ℝ := x95*x96
  have hx97 : Bounds (117687492011 / 250000000000) (472278749329 / 1000000000000) x97 := by
    apply bounds_mul hx95 hx96 <;> norm_num
  let x98 : ℝ := x95/(2 / 1)
  have hx98 : Bounds (117687492011 / 250000000000) (472278749329 / 1000000000000) x98 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx97
  let x99 : ℝ := Real.log (2 / 1)
  have hx99 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x99 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x100 : ℝ := (1 / 1)+(63883 / 100000)
  have hx100 : Bounds (163883 / 100000) (163883 / 100000) x100 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((63883 / 100000) : ℝ)) <;> norm_num
  let x101 : ℝ := (1 / 1)+(63883 / 100000)
  have hx101 : Bounds (163883 / 100000) (163883 / 100000) x101 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((63883 / 100000) : ℝ)) <;> norm_num
  let x102 : ℝ := Real.log x101
  have hx102 : Bounds (123495643 / 250000000) (493982573 / 1000000000) x102 := by
    exact bounds_log hx101 (by norm_num) (by simpa only [div_one] using reflection_log_9.1) (by simpa only [div_one] using reflection_log_9.2)
  let x103 : ℝ := x100*x102
  have hx103 : Bounds (80955345847 / 100000000000) (80955346011 / 100000000000) x103 := by
    apply bounds_mul hx100 hx102 <;> norm_num
  let x104 : ℝ := -(63883 / 100000)
  have hx104 : Bounds (-63883 / 100000) (-63883 / 100000) x104 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((63883 / 100000) : ℝ))
  let x105 : ℝ := (1 / 1)+x104
  have hx105 : Bounds (36117 / 100000) (36117 / 100000) x105 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx104 <;> norm_num
  let x106 : ℝ := (1 / 1)-(63883 / 100000)
  have hx106 : Bounds (36117 / 100000) (36117 / 100000) x106 := by
    exact hx105
  let x107 : ℝ := -(63883 / 100000)
  have hx107 : Bounds (-63883 / 100000) (-63883 / 100000) x107 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((63883 / 100000) : ℝ))
  let x108 : ℝ := (1 / 1)+x107
  have hx108 : Bounds (36117 / 100000) (36117 / 100000) x108 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx107 <;> norm_num
  let x109 : ℝ := (1 / 1)-(63883 / 100000)
  have hx109 : Bounds (36117 / 100000) (36117 / 100000) x109 := by
    exact hx108
  let x110 : ℝ := Real.log x109
  have hx110 : Bounds (-509203259 / 500000000) (-254601629 / 250000000) x110 := by
    exact bounds_log hx109 (by norm_num) (by simpa only [div_one] using reflection_log_10.1) (by simpa only [div_one] using reflection_log_10.2)
  let x111 : ℝ := x106*x110
  have hx111 : Bounds (-367817882107 / 1000000000000) (-367817881383 / 1000000000000) x111 := by
    apply bounds_mul hx106 hx110 <;> norm_num
  let x112 : ℝ := x103+x111
  have hx112 : Bounds (441735576363 / 1000000000000) (441735578727 / 1000000000000) x112 := by
    apply bounds_add hx103 hx111 <;> norm_num
  let x113 : ℝ := (2 / 1)⁻¹
  have hx113 : Bounds (1 / 2) (1 / 2) x113 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x114 : ℝ := x112*x113
  have hx114 : Bounds (220867788181 / 1000000000000) (55216947341 / 250000000000) x114 := by
    apply bounds_mul hx112 hx113 <;> norm_num
  let x115 : ℝ := x112/(2 / 1)
  have hx115 : Bounds (220867788181 / 1000000000000) (55216947341 / 250000000000) x115 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx114
  let x116 : ℝ := -x115
  have hx116 : Bounds (-55216947341 / 250000000000) (-220867788181 / 1000000000000) x116 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx115
  let x117 : ℝ := x99+x116
  have hx117 : Bounds (118069847659 / 250000000000) (472279392819 / 1000000000000) x117 := by
    apply bounds_add hx99 hx116 <;> norm_num
  let x118 : ℝ := x99-x115
  have hx118 : Bounds (118069847659 / 250000000000) (472279392819 / 1000000000000) x118 := by
    exact hx117
  let x119 : ℝ := biasE (63883 / 100000)
  have hx119 : Bounds (118069847659 / 250000000000) (472279392819 / 1000000000000) x119 := by
    simpa +zetaDelta only [biasE, div_one] using hx118
  let x120 : ℝ := Real.log (2 / 1)
  have hx120 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x120 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x121 : ℝ := (1 / 1)+(40053 / 62500)
  have hx121 : Bounds (102553 / 62500) (102553 / 62500) x121 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((40053 / 62500) : ℝ)) <;> norm_num
  let x122 : ℝ := (1 / 1)+(40053 / 62500)
  have hx122 : Bounds (102553 / 62500) (102553 / 62500) x122 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((40053 / 62500) : ℝ)) <;> norm_num
  let x123 : ℝ := Real.log x122
  have hx123 : Bounds (495213181 / 1000000000) (247606591 / 500000000) x123 := by
    exact bounds_log hx122 (by norm_num) (by simpa only [div_one] using reflection_log_11.1) (by simpa only [div_one] using reflection_log_11.2)
  let x124 : ℝ := x121*x123
  have hx124 : Bounds (812569557617 / 1000000000000) (812569559259 / 1000000000000) x124 := by
    apply bounds_mul hx121 hx123 <;> norm_num
  let x125 : ℝ := -(40053 / 62500)
  have hx125 : Bounds (-40053 / 62500) (-40053 / 62500) x125 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((40053 / 62500) : ℝ))
  let x126 : ℝ := (1 / 1)+x125
  have hx126 : Bounds (22447 / 62500) (22447 / 62500) x126 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx125 <;> norm_num
  let x127 : ℝ := (1 / 1)-(40053 / 62500)
  have hx127 : Bounds (22447 / 62500) (22447 / 62500) x127 := by
    exact hx126
  let x128 : ℝ := -(40053 / 62500)
  have hx128 : Bounds (-40053 / 62500) (-40053 / 62500) x128 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((40053 / 62500) : ℝ))
  let x129 : ℝ := (1 / 1)+x128
  have hx129 : Bounds (22447 / 62500) (22447 / 62500) x129 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx128 <;> norm_num
  let x130 : ℝ := (1 / 1)-(40053 / 62500)
  have hx130 : Bounds (22447 / 62500) (22447 / 62500) x130 := by
    exact hx129
  let x131 : ℝ := Real.log x130
  have hx131 : Bounds (-1024009583 / 1000000000) (-1024009581 / 1000000000) x131 := by
    exact bounds_log hx130 (by norm_num) (by simpa only [div_one] using reflection_log_12.1) (by simpa only [div_one] using reflection_log_12.2)
  let x132 : ℝ := x127*x131
  have hx132 : Bounds (-183887544877 / 500000000000) (-73555017807 / 200000000000) x132 := by
    apply bounds_mul hx127 hx131 <;> norm_num
  let x133 : ℝ := x124+x132
  have hx133 : Bounds (444794467863 / 1000000000000) (27799654389 / 62500000000) x133 := by
    apply bounds_add hx124 hx132 <;> norm_num
  let x134 : ℝ := (2 / 1)⁻¹
  have hx134 : Bounds (1 / 2) (1 / 2) x134 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x135 : ℝ := x133*x134
  have hx135 : Bounds (222397233931 / 1000000000000) (27799654389 / 125000000000) x135 := by
    apply bounds_mul hx133 hx134 <;> norm_num
  let x136 : ℝ := x133/(2 / 1)
  have hx136 : Bounds (222397233931 / 1000000000000) (27799654389 / 125000000000) x136 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx135
  let x137 : ℝ := -x136
  have hx137 : Bounds (-27799654389 / 125000000000) (-222397233931 / 1000000000000) x137 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx136
  let x138 : ℝ := x120+x137
  have hx138 : Bounds (58843743111 / 125000000000) (470749947069 / 1000000000000) x138 := by
    apply bounds_add hx120 hx137 <;> norm_num
  let x139 : ℝ := x120-x136
  have hx139 : Bounds (58843743111 / 125000000000) (470749947069 / 1000000000000) x139 := by
    exact hx138
  let x140 : ℝ := biasE (40053 / 62500)
  have hx140 : Bounds (58843743111 / 125000000000) (470749947069 / 1000000000000) x140 := by
    simpa +zetaDelta only [biasE, div_one] using hx139
  let y : ℝ := 1 - 2 * entropyInverse ((1 + H (2*m - 1/2))/2)
  have hLh' : Real.log 2 * ((1 + H (2*m - 1/2))/2) = x98 := by
    simpa +zetaDelta only [div_one] using hLh
  have hy : Bounds (63883 / 100000) (40053 / 62500) y := by
    apply entropyInverseBias_bracket
    · exact div_nonneg (add_nonneg zero_le_one
        (H_nonneg (by linarith [hm.1]) (by linarith [hm.2]))) two_pos.le
    · linarith [H_le_one (2*m-1/2)]
    · norm_num
    · norm_num
    · norm_num
    · have h1 : biasE (40053 / 62500) ≤ (470749947069 / 1000000000000) := hx140.2
      have h2 : (117687492011 / 250000000000) ≤ x98 := hx98.1
      linarith [hLh']
    · have h1 : x98 ≤ (472278749329 / 1000000000000) := hx98.2
      have h2 : (118069847659 / 250000000000) ≤ biasE (63883 / 100000) := hx119.1
      linarith [hLh']
  let x141 : ℝ := x3⁻¹
  have hx141 : Bounds (1157323688969 / 500000000000) (2320942883047 / 1000000000000) x141 := by
    apply bounds_inv hx3 <;> norm_num
  let x142 : ℝ := x98*x141
  have hx142 : Bounds (1089620179197 / 1000000000000) (109613200207 / 100000000000) x142 := by
    apply bounds_mul hx98 hx141 <;> norm_num
  let x143 : ℝ := x98/x3
  have hx143 : Bounds (1089620179197 / 1000000000000) (109613200207 / 100000000000) x143 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx142
  let x144 : ℝ := Real.log (2 / 1)
  have hx144 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x144 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x145 : ℝ := (1 / 1)+(508641 / 1000000)
  have hx145 : Bounds (1508641 / 1000000) (1508641 / 1000000) x145 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((508641 / 1000000) : ℝ)) <;> norm_num
  let x146 : ℝ := (1 / 1)+(508641 / 1000000)
  have hx146 : Bounds (1508641 / 1000000) (1508641 / 1000000) x146 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((508641 / 1000000) : ℝ)) <;> norm_num
  let x147 : ℝ := Real.log x146
  have hx147 : Bounds (82241849 / 200000000) (205604623 / 500000000) x147 := by
    exact bounds_log hx146 (by norm_num) (by simpa only [div_one] using reflection_log_13.1) (by simpa only [div_one] using reflection_log_13.2)
  let x148 : ℝ := x145*x147
  have hx148 : Bounds (310183563293 / 500000000000) (124073425619 / 200000000000) x148 := by
    apply bounds_mul hx145 hx147 <;> norm_num
  let x149 : ℝ := -(508641 / 1000000)
  have hx149 : Bounds (-508641 / 1000000) (-508641 / 1000000) x149 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((508641 / 1000000) : ℝ))
  let x150 : ℝ := (1 / 1)+x149
  have hx150 : Bounds (491359 / 1000000) (491359 / 1000000) x150 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx149 <;> norm_num
  let x151 : ℝ := (1 / 1)-(508641 / 1000000)
  have hx151 : Bounds (491359 / 1000000) (491359 / 1000000) x151 := by
    exact hx150
  let x152 : ℝ := -(508641 / 1000000)
  have hx152 : Bounds (-508641 / 1000000) (-508641 / 1000000) x152 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((508641 / 1000000) : ℝ))
  let x153 : ℝ := (1 / 1)+x152
  have hx153 : Bounds (491359 / 1000000) (491359 / 1000000) x153 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx152 <;> norm_num
  let x154 : ℝ := (1 / 1)-(508641 / 1000000)
  have hx154 : Bounds (491359 / 1000000) (491359 / 1000000) x154 := by
    exact hx153
  let x155 : ℝ := Real.log x154
  have hx155 : Bounds (-355290129 / 500000000) (-22205633 / 31250000) x155 := by
    exact bounds_log hx154 (by norm_num) (by simpa only [div_one] using reflection_log_14.1) (by simpa only [div_one] using reflection_log_14.2)
  let x156 : ℝ := x151*x155
  have hx156 : Bounds (-349150004991 / 1000000000000) (-349150004007 / 1000000000000) x156 := by
    apply bounds_mul hx151 hx155 <;> norm_num
  let x157 : ℝ := x148+x156
  have hx157 : Bounds (54243424319 / 200000000000) (33902140511 / 125000000000) x157 := by
    apply bounds_add hx148 hx156 <;> norm_num
  let x158 : ℝ := (2 / 1)⁻¹
  have hx158 : Bounds (1 / 2) (1 / 2) x158 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x159 : ℝ := x157*x158
  have hx159 : Bounds (135608560797 / 1000000000000) (33902140511 / 250000000000) x159 := by
    apply bounds_mul hx157 hx158 <;> norm_num
  let x160 : ℝ := x157/(2 / 1)
  have hx160 : Bounds (135608560797 / 1000000000000) (33902140511 / 250000000000) x160 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx159
  let x161 : ℝ := -x160
  have hx161 : Bounds (-33902140511 / 250000000000) (-135608560797 / 1000000000000) x161 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx160
  let x162 : ℝ := x144+x161
  have hx162 : Bounds (139384654489 / 250000000000) (557538620203 / 1000000000000) x162 := by
    apply bounds_add hx144 hx161 <;> norm_num
  let x163 : ℝ := x144-x160
  have hx163 : Bounds (139384654489 / 250000000000) (557538620203 / 1000000000000) x163 := by
    exact hx162
  let x164 : ℝ := biasE (508641 / 1000000)
  have hx164 : Bounds (139384654489 / 250000000000) (557538620203 / 1000000000000) x164 := by
    simpa +zetaDelta only [biasE, div_one] using hx163
  let x165 : ℝ := Real.log (2 / 1)
  have hx165 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x165 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x166 : ℝ := (1 / 1)+(510647 / 1000000)
  have hx166 : Bounds (1510647 / 1000000) (1510647 / 1000000) x166 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((510647 / 1000000) : ℝ)) <;> norm_num
  let x167 : ℝ := (1 / 1)+(510647 / 1000000)
  have hx167 : Bounds (1510647 / 1000000) (1510647 / 1000000) x167 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((510647 / 1000000) : ℝ)) <;> norm_num
  let x168 : ℝ := Real.log x167
  have hx168 : Bounds (82507607 / 200000000) (103134509 / 250000000) x168 := by
    exact bounds_log hx167 (by norm_num) (by simpa only [div_one] using reflection_log_15.1) (by simpa only [div_one] using reflection_log_15.2)
  let x169 : ℝ := x166*x168
  have hx169 : Bounds (311599672479 / 500000000000) (62319934647 / 100000000000) x169 := by
    apply bounds_mul hx166 hx168 <;> norm_num
  let x170 : ℝ := -(510647 / 1000000)
  have hx170 : Bounds (-510647 / 1000000) (-510647 / 1000000) x170 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((510647 / 1000000) : ℝ))
  let x171 : ℝ := (1 / 1)+x170
  have hx171 : Bounds (489353 / 1000000) (489353 / 1000000) x171 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx170 <;> norm_num
  let x172 : ℝ := (1 / 1)-(510647 / 1000000)
  have hx172 : Bounds (489353 / 1000000) (489353 / 1000000) x172 := by
    exact hx171
  let x173 : ℝ := -(510647 / 1000000)
  have hx173 : Bounds (-510647 / 1000000) (-510647 / 1000000) x173 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((510647 / 1000000) : ℝ))
  let x174 : ℝ := (1 / 1)+x173
  have hx174 : Bounds (489353 / 1000000) (489353 / 1000000) x174 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx173 <;> norm_num
  let x175 : ℝ := (1 / 1)-(510647 / 1000000)
  have hx175 : Bounds (489353 / 1000000) (489353 / 1000000) x175 := by
    exact hx174
  let x176 : ℝ := Real.log x175
  have hx176 : Bounds (-714671169 / 1000000000) (-714671167 / 1000000000) x176 := by
    exact bounds_log hx175 (by norm_num) (by simpa only [div_one] using reflection_log_16.1) (by simpa only [div_one] using reflection_log_16.2)
  let x177 : ℝ := x172*x176
  have hx177 : Bounds (-87431620141 / 250000000000) (-10928952487 / 31250000000) x177 := by
    apply bounds_mul hx172 hx176 <;> norm_num
  let x178 : ℝ := x169+x177
  have hx178 : Bounds (136736432197 / 500000000000) (136736433443 / 500000000000) x178 := by
    apply bounds_add hx169 hx177 <;> norm_num
  let x179 : ℝ := (2 / 1)⁻¹
  have hx179 : Bounds (1 / 2) (1 / 2) x179 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x180 : ℝ := x178*x179
  have hx180 : Bounds (136736432197 / 1000000000000) (136736433443 / 1000000000000) x180 := by
    apply bounds_mul hx178 hx179 <;> norm_num
  let x181 : ℝ := x178/(2 / 1)
  have hx181 : Bounds (136736432197 / 1000000000000) (136736433443 / 1000000000000) x181 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx180
  let x182 : ℝ := -x181
  have hx182 : Bounds (-136736433443 / 1000000000000) (-136736432197 / 1000000000000) x182 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx181
  let x183 : ℝ := x165+x182
  have hx183 : Bounds (556410746557 / 1000000000000) (556410748803 / 1000000000000) x183 := by
    apply bounds_add hx165 hx182 <;> norm_num
  let x184 : ℝ := x165-x181
  have hx184 : Bounds (556410746557 / 1000000000000) (556410748803 / 1000000000000) x184 := by
    exact hx183
  let x185 : ℝ := biasE (510647 / 1000000)
  have hx185 : Bounds (556410746557 / 1000000000000) (556410748803 / 1000000000000) x185 := by
    simpa +zetaDelta only [biasE, div_one] using hx184
  let x186 : ℝ := x143*(508641 / 1000000)
  have hx186 : Bounds (277112748783 / 500000000000) (111507535533 / 200000000000) x186 := by
    apply bounds_mul hx143 (bounds_const ((508641 / 1000000) : ℝ)) <;> norm_num
  let x187 : ℝ := x143*(510647 / 1000000)
  have hx187 : Bounds (278205637823 / 500000000000) (279868259231 / 500000000000) x187 := by
    apply bounds_mul hx143 (bounds_const ((510647 / 1000000) : ℝ)) <;> norm_num
  let c : ℝ := Reflection.regularContact (x3 / (Real.log 2 * ((1 + H (2*m - 1/2))/2)))
  have hcMem := Reflection.regularContact_mem
    (x3 / (Real.log 2 * ((1 + H (2*m - 1/2))/2)))
  have hc0 : 0 ≤ c := by
    dsimp only [c]
    apply GeneralCK.Certificates.RegularContactBounds.regularContact_nonneg
    rw [hLh']
    exact div_nonneg (by linarith [hx3.1]) (by linarith [hx98.1])
  have hcEq : biasE c = x143 * c := by
    have he := Reflection.regularContact_equation (x3 / x98)
    have hcdef : c = Reflection.regularContact (x3 / x98) := by
      dsimp only [c]
      rw [hLh']
    rw [← hcdef] at he
    change biasE c = (x98 / x3) * c
    have hx0 : 0 < x3 := by linarith [hx3.1]
    have hh0 : 0 < x98 := by linarith [hx98.1]
    field_simp [hx0.ne', hh0.ne'] at he ⊢
    nlinarith
  have hc : Bounds (508641 / 1000000) (510647 / 1000000) c := by
    apply contact_bracket hc0 hcMem.2.le (by norm_num) (by norm_num) (by norm_num)
      (show 0 < x143 by linarith [hx143.1]) hcEq
    · have h1 : x143 * (508641 / 1000000) ≤ (111507535533 / 200000000000) := hx186.2
      have h2 : (139384654489 / 250000000000) ≤ biasE (508641 / 1000000) := hx164.1
      linarith
    · have h1 : biasE (510647 / 1000000) ≤ (556410748803 / 1000000000000) := hx185.2
      have h2 : (278205637823 / 500000000000) ≤ x143 * (510647 / 1000000) := hx187.1
      linarith
  let x188 : ℝ := (1 / 1)+y
  have hx188 : Bounds (163883 / 100000) (102553 / 62500) x188 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hy <;> norm_num
  let x189 : ℝ := -y
  have hx189 : Bounds (-40053 / 62500) (-63883 / 100000) x189 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hy
  let x190 : ℝ := (1 / 1)+x189
  have hx190 : Bounds (22447 / 62500) (36117 / 100000) x190 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx189 <;> norm_num
  let x191 : ℝ := (1 / 1)-y
  have hx191 : Bounds (22447 / 62500) (36117 / 100000) x191 := by
    exact hx190
  let x192 : ℝ := x191⁻¹
  have hx192 : Bounds (276877924523 / 100000000000) (2784336436941 / 1000000000000) x192 := by
    apply bounds_inv hx191 <;> norm_num
  let x193 : ℝ := x188*x192
  have hx193 : Bounds (226877924523 / 50000000000) (2284336436941 / 500000000000) x193 := by
    apply bounds_mul hx188 hx192 <;> norm_num
  let x194 : ℝ := x188/x191
  have hx194 : Bounds (226877924523 / 50000000000) (2284336436941 / 500000000000) x194 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx193
  let x195 : ℝ := Real.log x194
  have hx195 : Bounds (47262159 / 31250000) (303844553 / 200000000) x195 := by
    exact bounds_log hx194 (by norm_num) (by simpa only [div_one] using reflection_log_17.1) (by simpa only [div_one] using reflection_log_18.2)
  let x196 : ℝ := (2 / 1)⁻¹
  have hx196 : Bounds (1 / 2) (1 / 2) x196 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x197 : ℝ := x195*x196
  have hx197 : Bounds (47262159 / 62500000) (303844553 / 400000000) x197 := by
    apply bounds_mul hx195 hx196 <;> norm_num
  let x198 : ℝ := x195/(2 / 1)
  have hx198 : Bounds (47262159 / 62500000) (303844553 / 400000000) x198 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx197
  let x199 : ℝ := (1 / 1)+c
  have hx199 : Bounds (1508641 / 1000000) (1510647 / 1000000) x199 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hc <;> norm_num
  let x200 : ℝ := -c
  have hx200 : Bounds (-510647 / 1000000) (-508641 / 1000000) x200 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hc
  let x201 : ℝ := (1 / 1)+x200
  have hx201 : Bounds (489353 / 1000000) (491359 / 1000000) x201 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx200 <;> norm_num
  let x202 : ℝ := (1 / 1)-c
  have hx202 : Bounds (489353 / 1000000) (491359 / 1000000) x202 := by
    exact hx201
  let x203 : ℝ := x202⁻¹
  have hx203 : Bounds (1017585919867 / 500000000000) (2043514599891 / 1000000000000) x203 := by
    apply bounds_inv hx202 <;> norm_num
  let x204 : ℝ := x199*x203
  have hx204 : Bounds (767585919867 / 250000000000) (1543514599891 / 500000000000) x204 := by
    apply bounds_mul hx199 hx203 <;> norm_num
  let x205 : ℝ := x199/x202
  have hx205 : Bounds (767585919867 / 250000000000) (1543514599891 / 500000000000) x205 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx204
  let x206 : ℝ := Real.log x205
  have hx206 : Bounds (560894751 / 500000000) (225441841 / 200000000) x206 := by
    exact bounds_log hx205 (by norm_num) (by simpa only [div_one] using reflection_log_19.1) (by simpa only [div_one] using reflection_log_20.2)
  let x207 : ℝ := (2 / 1)⁻¹
  have hx207 : Bounds (1 / 2) (1 / 2) x207 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x208 : ℝ := x206*x207
  have hx208 : Bounds (560894751 / 1000000000) (225441841 / 400000000) x208 := by
    apply bounds_mul hx206 hx207 <;> norm_num
  let x209 : ℝ := x206/(2 / 1)
  have hx209 : Bounds (560894751 / 1000000000) (225441841 / 400000000) x209 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx208
  let x210 : ℝ := (2 / 1)*x50
  have hx210 : Bounds (149169286487 / 125000000000) (597218168569 / 500000000000) x210 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx50 <;> norm_num
  let x211 : ℝ := (2 / 1)*x98
  have hx211 : Bounds (117687492011 / 125000000000) (472278749329 / 500000000000) x211 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx98 <;> norm_num
  let x212 : ℝ := -x211
  have hx212 : Bounds (-472278749329 / 500000000000) (-117687492011 / 125000000000) x212 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx211
  let x213 : ℝ := x210+x212
  have hx213 : Bounds (124398396619 / 500000000000) (5058728021 / 20000000000) x213 := by
    apply bounds_add hx210 hx212 <;> norm_num
  let x214 : ℝ := x210-x211
  have hx214 : Bounds (124398396619 / 500000000000) (5058728021 / 20000000000) x214 := by
    exact hx213
  let x215 : ℝ := y*x198
  have hx215 : Bounds (483079760543 / 1000000000000) (486795435253 / 1000000000000) x215 := by
    apply bounds_mul hy hx198 <;> norm_num
  let x216 : ℝ := -x215
  have hx216 : Bounds (-486795435253 / 1000000000000) (-483079760543 / 1000000000000) x216 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx215
  let x217 : ℝ := x214+x216
  have hx217 : Bounds (-47599728403 / 200000000000) (-230143359493 / 1000000000000) x217 := by
    apply bounds_add hx214 hx216 <;> norm_num
  let x218 : ℝ := x214-x215
  have hx218 : Bounds (-47599728403 / 200000000000) (-230143359493 / 1000000000000) x218 := by
    exact hx217
  let x219 : ℝ := x3*x209
  have hx219 : Bounds (1888021577 / 7812500000) (60873700231 / 250000000000) x219 := by
    apply bounds_mul hx3 hx209 <;> norm_num
  let x220 : ℝ := x218+x219
  have hx220 : Bounds (3668119841 / 1000000000000) (13351441431 / 1000000000000) x220 := by
    apply bounds_add hx218 hx219 <;> norm_num
  have hpos : 0 < x220 := lt_of_lt_of_le (by norm_num) hx220.1
  have hcert :
      0 ≤ 2 * biasE (1 - 2*m) - 2*(x98)
        - (1 - 2*entropyInverse ((1 + H (2*m - 1/2))/2)) *
            SmallMean.A (1 - 2*entropyInverse ((1 + H (2*m - 1/2))/2))
        + (1 - 2*m) *
            SmallMean.A (regularContact ((1 - 2*m)/(Real.log 2*((1 + H (2*m - 1/2))/2)))) := by
    simpa +zetaDelta only [SmallMean.A, div_one] using hpos.le
  dsimp only
  nlinarith [hcert, hLh]

theorem acceptedCertificate : DoubleCapBiasCellCertificate (727 / 2560) (1457 / 5120) (fun m => (1 + H (2*m - 1/2))/2) where
  domain := by norm_num
  sound m hmLo hmHi := by
    exact cell_bias_nonneg m ⟨hmLo, hmHi⟩

theorem accepted_cell :
    ∀ m, (727 / 2560) ≤ m → m ≤ (1457 / 5120) → 0 ≤ doubleCapHighResidual m := by
  intro m hmLo hmHi
  unfold doubleCapHighResidual
  apply doubleCapEndpointResidual_nonneg_of_biasCell acceptedCertificate hmLo hmHi
  exact div_pos (by linarith [H_nonneg (by linarith : 0 ≤ 2*m-1/2) (by linarith : 2*m-1/2 ≤ 1)]) two_pos

#print axioms cell_bias_nonneg
#print axioms accepted_cell

end GeneralCK.Certificates.DoubleCapMiddle.Cell0069

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0070 =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0070
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Reflection
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem cell_bias_nonneg (m : ℝ) (hm : Bounds (1457 / 5120) (73 / 256) m) :
    let h := (1 + H (2*m - 1/2))/2
    let x := 1-2*m
    let y := 1-2*entropyInverse h
    let c := regularContact (x/(Real.log 2*h))
    0 ≤ 2*(biasE x-Real.log 2*h)-y*SmallMean.A y+x*SmallMean.A c := by
  have hEq : biasE (2-4*m) = Real.log 2 * H (2*m-1/2) := by
    have hmstrict : 1/4 < m := by
      have hlo : (1/4 : ℝ) < (1457 / 5120) := by norm_num
      exact lt_of_lt_of_le hlo hm.1
    rw [show 2-4*m = 1-2*(2*m-1/2) by ring,
      GeneralCK.Correction.Natural.biasE_probability (by linarith [hmstrict]) (by linarith [hm.2]),
      GeneralCK.Certificates.Mixed.hn_eq_H_mul_log]
    ring
  have hLh : Real.log 2 * ((1 + H (2*m - 1/2))/2) = (Real.log 2 + biasE (2-4*m))/2 := by
    rw [hEq]
    ring
  let x0 : ℝ := (2 / 1)*m
  have hx0 : Bounds (1457 / 2560) (73 / 128) x0 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hm <;> norm_num
  let x1 : ℝ := -x0
  have hx1 : Bounds (-73 / 128) (-1457 / 2560) x1 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx0
  let x2 : ℝ := (1 / 1)+x1
  have hx2 : Bounds (55 / 128) (1103 / 2560) x2 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx1 <;> norm_num
  let x3 : ℝ := (1 / 1)-x0
  have hx3 : Bounds (55 / 128) (1103 / 2560) x3 := by
    exact hx2
  let x4 : ℝ := (4 / 1)*m
  have hx4 : Bounds (1457 / 1280) (73 / 64) x4 := by
    apply bounds_mul (bounds_const ((4 / 1) : ℝ)) hm <;> norm_num
  let x5 : ℝ := -x4
  have hx5 : Bounds (-73 / 64) (-1457 / 1280) x5 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx4
  let x6 : ℝ := (2 / 1)+x5
  have hx6 : Bounds (55 / 64) (1103 / 1280) x6 := by
    apply bounds_add (bounds_const ((2 / 1) : ℝ)) hx5 <;> norm_num
  let x7 : ℝ := (2 / 1)-x4
  have hx7 : Bounds (55 / 64) (1103 / 1280) x7 := by
    exact hx6
  let x8 : ℝ := Real.log (2 / 1)
  have hx8 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x8 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x9 : ℝ := (1 / 1)+(1103 / 2560)
  have hx9 : Bounds (3663 / 2560) (3663 / 2560) x9 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1103 / 2560) : ℝ)) <;> norm_num
  let x10 : ℝ := (1 / 1)+(1103 / 2560)
  have hx10 : Bounds (3663 / 2560) (3663 / 2560) x10 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1103 / 2560) : ℝ)) <;> norm_num
  let x11 : ℝ := Real.log x10
  have hx11 : Bounds (14331009 / 40000000) (179137613 / 500000000) x11 := by
    exact bounds_log hx10 (by norm_num) (by simpa only [div_one] using reflection_log_1.1) (by simpa only [div_one] using reflection_log_1.2)
  let x12 : ℝ := x9*x11
  have hx12 : Bounds (512641464521 / 1000000000000) (512641465953 / 1000000000000) x12 := by
    apply bounds_mul hx9 hx11 <;> norm_num
  let x13 : ℝ := -(1103 / 2560)
  have hx13 : Bounds (-1103 / 2560) (-1103 / 2560) x13 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1103 / 2560) : ℝ))
  let x14 : ℝ := (1 / 1)+x13
  have hx14 : Bounds (1457 / 2560) (1457 / 2560) x14 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx13 <;> norm_num
  let x15 : ℝ := (1 / 1)-(1103 / 2560)
  have hx15 : Bounds (1457 / 2560) (1457 / 2560) x15 := by
    exact hx14
  let x16 : ℝ := -(1103 / 2560)
  have hx16 : Bounds (-1103 / 2560) (-1103 / 2560) x16 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1103 / 2560) : ℝ))
  let x17 : ℝ := (1 / 1)+x16
  have hx17 : Bounds (1457 / 2560) (1457 / 2560) x17 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx16 <;> norm_num
  let x18 : ℝ := (1 / 1)-(1103 / 2560)
  have hx18 : Bounds (1457 / 2560) (1457 / 2560) x18 := by
    exact hx17
  let x19 : ℝ := Real.log x18
  have hx19 : Bounds (-140906933 / 250000000) (-563627731 / 1000000000) x19 := by
    exact bounds_log hx18 (by norm_num) (by simpa only [div_one] using reflection_log_2.1) (by simpa only [div_one] using reflection_log_2.2)
  let x20 : ℝ := x15*x19
  have hx20 : Bounds (-160391719829 / 500000000000) (-20048964943 / 62500000000) x20 := by
    apply bounds_mul hx15 hx19 <;> norm_num
  let x21 : ℝ := x12+x20
  have hx21 : Bounds (191858024863 / 1000000000000) (38371605373 / 200000000000) x21 := by
    apply bounds_add hx12 hx20 <;> norm_num
  let x22 : ℝ := (2 / 1)⁻¹
  have hx22 : Bounds (1 / 2) (1 / 2) x22 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x23 : ℝ := x21*x22
  have hx23 : Bounds (95929012431 / 1000000000000) (95929013433 / 1000000000000) x23 := by
    apply bounds_mul hx21 hx22 <;> norm_num
  let x24 : ℝ := x21/(2 / 1)
  have hx24 : Bounds (95929012431 / 1000000000000) (95929013433 / 1000000000000) x24 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx23
  let x25 : ℝ := -x24
  have hx25 : Bounds (-95929013433 / 1000000000000) (-95929012431 / 1000000000000) x25 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx24
  let x26 : ℝ := x8+x25
  have hx26 : Bounds (597218166567 / 1000000000000) (597218168569 / 1000000000000) x26 := by
    apply bounds_add hx8 hx25 <;> norm_num
  let x27 : ℝ := x8-x24
  have hx27 : Bounds (597218166567 / 1000000000000) (597218168569 / 1000000000000) x27 := by
    exact hx26
  let x28 : ℝ := biasE (1103 / 2560)
  have hx28 : Bounds (597218166567 / 1000000000000) (597218168569 / 1000000000000) x28 := by
    simpa +zetaDelta only [biasE, div_one] using hx27
  let x29 : ℝ := Real.log (2 / 1)
  have hx29 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x29 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x30 : ℝ := (1 / 1)+(55 / 128)
  have hx30 : Bounds (183 / 128) (183 / 128) x30 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((55 / 128) : ℝ)) <;> norm_num
  let x31 : ℝ := (1 / 1)+(55 / 128)
  have hx31 : Bounds (183 / 128) (183 / 128) x31 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((55 / 128) : ℝ)) <;> norm_num
  let x32 : ℝ := Real.log x31
  have hx32 : Bounds (22340993 / 62500000) (357455889 / 1000000000) x32 := by
    exact bounds_log hx31 (by norm_num) (by simpa only [div_one] using reflection_log_3.1) (by simpa only [div_one] using reflection_log_3.2)
  let x33 : ℝ := x30*x32
  have hx33 : Bounds (4088401719 / 8000000000) (102210043261 / 200000000000) x33 := by
    apply bounds_mul hx30 hx32 <;> norm_num
  let x34 : ℝ := -(55 / 128)
  have hx34 : Bounds (-55 / 128) (-55 / 128) x34 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((55 / 128) : ℝ))
  let x35 : ℝ := (1 / 1)+x34
  have hx35 : Bounds (73 / 128) (73 / 128) x35 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx34 <;> norm_num
  let x36 : ℝ := (1 / 1)-(55 / 128)
  have hx36 : Bounds (73 / 128) (73 / 128) x36 := by
    exact hx35
  let x37 : ℝ := -(55 / 128)
  have hx37 : Bounds (-55 / 128) (-55 / 128) x37 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((55 / 128) : ℝ))
  let x38 : ℝ := (1 / 1)+x37
  have hx38 : Bounds (73 / 128) (73 / 128) x38 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx37 <;> norm_num
  let x39 : ℝ := (1 / 1)-(55 / 128)
  have hx39 : Bounds (73 / 128) (73 / 128) x39 := by
    exact hx38
  let x40 : ℝ := Real.log x39
  have hx40 : Bounds (-561570823 / 1000000000) (-280785411 / 500000000) x40 := by
    exact bounds_log hx39 (by norm_num) (by simpa only [div_one] using reflection_log_4.1) (by simpa only [div_one] using reflection_log_4.2)
  let x41 : ℝ := x36*x40
  have hx41 : Bounds (-320270859993 / 1000000000000) (-320270859421 / 1000000000000) x41 := by
    apply bounds_mul hx36 hx40 <;> norm_num
  let x42 : ℝ := x33+x41
  have hx42 : Bounds (95389677441 / 500000000000) (47694839221 / 250000000000) x42 := by
    apply bounds_add hx33 hx41 <;> norm_num
  let x43 : ℝ := (2 / 1)⁻¹
  have hx43 : Bounds (1 / 2) (1 / 2) x43 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x44 : ℝ := x42*x43
  have hx44 : Bounds (95389677441 / 1000000000000) (47694839221 / 500000000000) x44 := by
    apply bounds_mul hx42 hx43 <;> norm_num
  let x45 : ℝ := x42/(2 / 1)
  have hx45 : Bounds (95389677441 / 1000000000000) (47694839221 / 500000000000) x45 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx44
  let x46 : ℝ := -x45
  have hx46 : Bounds (-47694839221 / 500000000000) (-95389677441 / 1000000000000) x46 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx45
  let x47 : ℝ := x29+x46
  have hx47 : Bounds (298878750779 / 500000000000) (597757503559 / 1000000000000) x47 := by
    apply bounds_add hx29 hx46 <;> norm_num
  let x48 : ℝ := x29-x45
  have hx48 : Bounds (298878750779 / 500000000000) (597757503559 / 1000000000000) x48 := by
    exact hx47
  let x49 : ℝ := biasE (55 / 128)
  have hx49 : Bounds (298878750779 / 500000000000) (597757503559 / 1000000000000) x49 := by
    simpa +zetaDelta only [biasE, div_one] using hx48
  let x50 : ℝ := biasE x3
  have hx50 : Bounds (597218166567 / 1000000000000) (597757503559 / 1000000000000) x50 := by
    exact bounds_biasE hx3 (by norm_num) (by norm_num) hx28.1 hx49.2
  let x51 : ℝ := Real.log (2 / 1)
  have hx51 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x51 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x52 : ℝ := (1 / 1)+(1103 / 1280)
  have hx52 : Bounds (2383 / 1280) (2383 / 1280) x52 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1103 / 1280) : ℝ)) <;> norm_num
  let x53 : ℝ := (1 / 1)+(1103 / 1280)
  have hx53 : Bounds (2383 / 1280) (2383 / 1280) x53 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1103 / 1280) : ℝ)) <;> norm_num
  let x54 : ℝ := Real.log x53
  have hx54 : Bounds (15537503 / 25000000) (621500121 / 1000000000) x54 := by
    exact bounds_log hx53 (by norm_num) (by simpa only [div_one] using reflection_log_5.1) (by simpa only [div_one] using reflection_log_5.2)
  let x55 : ℝ := x52*x54
  have hx55 : Bounds (1157058426531 / 1000000000000) (1157058428393 / 1000000000000) x55 := by
    apply bounds_mul hx52 hx54 <;> norm_num
  let x56 : ℝ := -(1103 / 1280)
  have hx56 : Bounds (-1103 / 1280) (-1103 / 1280) x56 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1103 / 1280) : ℝ))
  let x57 : ℝ := (1 / 1)+x56
  have hx57 : Bounds (177 / 1280) (177 / 1280) x57 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx56 <;> norm_num
  let x58 : ℝ := (1 / 1)-(1103 / 1280)
  have hx58 : Bounds (177 / 1280) (177 / 1280) x58 := by
    exact hx57
  let x59 : ℝ := -(1103 / 1280)
  have hx59 : Bounds (-1103 / 1280) (-1103 / 1280) x59 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1103 / 1280) : ℝ))
  let x60 : ℝ := (1 / 1)+x59
  have hx60 : Bounds (177 / 1280) (177 / 1280) x60 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx59 <;> norm_num
  let x61 : ℝ := (1 / 1)-(1103 / 1280)
  have hx61 : Bounds (177 / 1280) (177 / 1280) x61 := by
    exact hx60
  let x62 : ℝ := Real.log x61
  have hx62 : Bounds (-989232813 / 500000000) (-1978465623 / 1000000000) x62 := by
    exact bounds_log hx61 (by norm_num) (by simpa only [div_one] using reflection_log_6.1) (by simpa only [div_one] using reflection_log_6.2)
  let x63 : ℝ := x58*x62
  have hx63 : Bounds (-136792349923 / 500000000000) (-27358469943 / 100000000000) x63 := by
    apply bounds_mul hx58 hx62 <;> norm_num
  let x64 : ℝ := x55+x63
  have hx64 : Bounds (176694745337 / 200000000000) (883473728963 / 1000000000000) x64 := by
    apply bounds_add hx55 hx63 <;> norm_num
  let x65 : ℝ := (2 / 1)⁻¹
  have hx65 : Bounds (1 / 2) (1 / 2) x65 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x66 : ℝ := x64*x65
  have hx66 : Bounds (220868431671 / 500000000000) (220868432241 / 500000000000) x66 := by
    apply bounds_mul hx64 hx65 <;> norm_num
  let x67 : ℝ := x64/(2 / 1)
  have hx67 : Bounds (220868431671 / 500000000000) (220868432241 / 500000000000) x67 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx66
  let x68 : ℝ := -x67
  have hx68 : Bounds (-220868432241 / 500000000000) (-220868431671 / 500000000000) x68 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx67
  let x69 : ℝ := x51+x68
  have hx69 : Bounds (125705157759 / 500000000000) (125705158829 / 500000000000) x69 := by
    apply bounds_add hx51 hx68 <;> norm_num
  let x70 : ℝ := x51-x67
  have hx70 : Bounds (125705157759 / 500000000000) (125705158829 / 500000000000) x70 := by
    exact hx69
  let x71 : ℝ := biasE (1103 / 1280)
  have hx71 : Bounds (125705157759 / 500000000000) (125705158829 / 500000000000) x71 := by
    simpa +zetaDelta only [biasE, div_one] using hx70
  let x72 : ℝ := Real.log (2 / 1)
  have hx72 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x72 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x73 : ℝ := (1 / 1)+(55 / 64)
  have hx73 : Bounds (119 / 64) (119 / 64) x73 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((55 / 64) : ℝ)) <;> norm_num
  let x74 : ℝ := (1 / 1)+(55 / 64)
  have hx74 : Bounds (119 / 64) (119 / 64) x74 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((55 / 64) : ℝ)) <;> norm_num
  let x75 : ℝ := Real.log x74
  have hx75 : Bounds (620240409 / 1000000000) (62024041 / 100000000) x75 := by
    exact bounds_log hx74 (by norm_num) (by simpa only [div_one] using reflection_log_7.1) (by simpa only [div_one] using reflection_log_7.2)
  let x76 : ℝ := x73*x75
  have hx76 : Bounds (288314877621 / 250000000000) (144157439043 / 125000000000) x76 := by
    apply bounds_mul hx73 hx75 <;> norm_num
  let x77 : ℝ := -(55 / 64)
  have hx77 : Bounds (-55 / 64) (-55 / 64) x77 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((55 / 64) : ℝ))
  let x78 : ℝ := (1 / 1)+x77
  have hx78 : Bounds (9 / 64) (9 / 64) x78 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx77 <;> norm_num
  let x79 : ℝ := (1 / 1)-(55 / 64)
  have hx79 : Bounds (9 / 64) (9 / 64) x79 := by
    exact hx78
  let x80 : ℝ := -(55 / 64)
  have hx80 : Bounds (-55 / 64) (-55 / 64) x80 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((55 / 64) : ℝ))
  let x81 : ℝ := (1 / 1)+x80
  have hx81 : Bounds (9 / 64) (9 / 64) x81 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx80 <;> norm_num
  let x82 : ℝ := (1 / 1)-(55 / 64)
  have hx82 : Bounds (9 / 64) (9 / 64) x82 := by
    exact hx81
  let x83 : ℝ := Real.log x82
  have hx83 : Bounds (-1961658507 / 1000000000) (-245207313 / 125000000) x83 := by
    exact bounds_log hx82 (by norm_num) (by simpa only [div_one] using reflection_log_8.1) (by simpa only [div_one] using reflection_log_8.2)
  let x84 : ℝ := x79*x83
  have hx84 : Bounds (-275858227547 / 1000000000000) (-2206865817 / 8000000000) x84 := by
    apply bounds_mul hx79 hx83 <;> norm_num
  let x85 : ℝ := x76+x84
  have hx85 : Bounds (877401282937 / 1000000000000) (877401285219 / 1000000000000) x85 := by
    apply bounds_add hx76 hx84 <;> norm_num
  let x86 : ℝ := (2 / 1)⁻¹
  have hx86 : Bounds (1 / 2) (1 / 2) x86 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x87 : ℝ := x85*x86
  have hx87 : Bounds (109675160367 / 250000000000) (43870064261 / 100000000000) x87 := by
    apply bounds_mul hx85 hx86 <;> norm_num
  let x88 : ℝ := x85/(2 / 1)
  have hx88 : Bounds (109675160367 / 250000000000) (43870064261 / 100000000000) x88 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx87
  let x89 : ℝ := -x88
  have hx89 : Bounds (-43870064261 / 100000000000) (-109675160367 / 250000000000) x89 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx88
  let x90 : ℝ := x72+x89
  have hx90 : Bounds (25444653739 / 100000000000) (63611634883 / 250000000000) x90 := by
    apply bounds_add hx72 hx89 <;> norm_num
  let x91 : ℝ := x72-x88
  have hx91 : Bounds (25444653739 / 100000000000) (63611634883 / 250000000000) x91 := by
    exact hx90
  let x92 : ℝ := biasE (55 / 64)
  have hx92 : Bounds (25444653739 / 100000000000) (63611634883 / 250000000000) x92 := by
    simpa +zetaDelta only [biasE, div_one] using hx91
  let x93 : ℝ := biasE x7
  have hx93 : Bounds (125705157759 / 500000000000) (63611634883 / 250000000000) x93 := by
    exact bounds_biasE hx7 (by norm_num) (by norm_num) hx71.1 hx92.2
  let x94 : ℝ := Real.log (2 / 1)
  have hx94 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x94 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x95 : ℝ := x94+x93
  have hx95 : Bounds (472278747759 / 500000000000) (236898430133 / 250000000000) x95 := by
    apply bounds_add hx94 hx93 <;> norm_num
  let x96 : ℝ := (2 / 1)⁻¹
  have hx96 : Bounds (1 / 2) (1 / 2) x96 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x97 : ℝ := x95*x96
  have hx97 : Bounds (472278747759 / 1000000000000) (236898430133 / 500000000000) x97 := by
    apply bounds_mul hx95 hx96 <;> norm_num
  let x98 : ℝ := x95/(2 / 1)
  have hx98 : Bounds (472278747759 / 1000000000000) (236898430133 / 500000000000) x98 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx97
  let x99 : ℝ := Real.log (2 / 1)
  have hx99 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x99 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x100 : ℝ := (1 / 1)+(318409 / 500000)
  have hx100 : Bounds (818409 / 500000) (818409 / 500000) x100 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((318409 / 500000) : ℝ)) <;> norm_num
  let x101 : ℝ := (1 / 1)+(318409 / 500000)
  have hx101 : Bounds (818409 / 500000) (818409 / 500000) x101 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((318409 / 500000) : ℝ)) <;> norm_num
  let x102 : ℝ := Real.log x101
  have hx102 : Bounds (492754113 / 1000000000) (246377057 / 500000000) x102 := by
    exact bounds_log hx101 (by norm_num) (by simpa only [div_one] using reflection_log_9.1) (by simpa only [div_one] using reflection_log_9.2)
  let x103 : ℝ := x100*x102
  have hx103 : Bounds (201637200433 / 250000000000) (80654880337 / 100000000000) x103 := by
    apply bounds_mul hx100 hx102 <;> norm_num
  let x104 : ℝ := -(318409 / 500000)
  have hx104 : Bounds (-318409 / 500000) (-318409 / 500000) x104 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((318409 / 500000) : ℝ))
  let x105 : ℝ := (1 / 1)+x104
  have hx105 : Bounds (181591 / 500000) (181591 / 500000) x105 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx104 <;> norm_num
  let x106 : ℝ := (1 / 1)-(318409 / 500000)
  have hx106 : Bounds (181591 / 500000) (181591 / 500000) x106 := by
    exact hx105
  let x107 : ℝ := -(318409 / 500000)
  have hx107 : Bounds (-318409 / 500000) (-318409 / 500000) x107 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((318409 / 500000) : ℝ))
  let x108 : ℝ := (1 / 1)+x107
  have hx108 : Bounds (181591 / 500000) (181591 / 500000) x108 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx107 <;> norm_num
  let x109 : ℝ := (1 / 1)-(318409 / 500000)
  have hx109 : Bounds (181591 / 500000) (181591 / 500000) x109 := by
    exact hx108
  let x110 : ℝ := Real.log x109
  have hx110 : Bounds (-506425597 / 500000000) (-126606399 / 125000000) x110 := by
    exact bounds_log hx109 (by norm_num) (by simpa only [div_one] using reflection_log_10.1) (by simpa only [div_one] using reflection_log_10.2)
  let x111 : ℝ := x106*x110
  have hx111 : Bounds (-18392466117 / 50000000000) (-91962330403 / 250000000000) x111 := by
    apply bounds_mul hx106 hx110 <;> norm_num
  let x112 : ℝ := x103+x111
  have hx112 : Bounds (13709358731 / 31250000000) (219349740879 / 500000000000) x112 := by
    apply bounds_add hx103 hx111 <;> norm_num
  let x113 : ℝ := (2 / 1)⁻¹
  have hx113 : Bounds (1 / 2) (1 / 2) x113 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x114 : ℝ := x112*x113
  have hx114 : Bounds (13709358731 / 62500000000) (219349740879 / 1000000000000) x114 := by
    apply bounds_mul hx112 hx113 <;> norm_num
  let x115 : ℝ := x112/(2 / 1)
  have hx115 : Bounds (13709358731 / 62500000000) (219349740879 / 1000000000000) x115 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx114
  let x116 : ℝ := -x115
  have hx116 : Bounds (-219349740879 / 1000000000000) (-13709358731 / 62500000000) x116 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx115
  let x117 : ℝ := x99+x116
  have hx117 : Bounds (473797439121 / 1000000000000) (59224680163 / 125000000000) x117 := by
    apply bounds_add hx99 hx116 <;> norm_num
  let x118 : ℝ := x99-x115
  have hx118 : Bounds (473797439121 / 1000000000000) (59224680163 / 125000000000) x118 := by
    exact hx117
  let x119 : ℝ := biasE (318409 / 500000)
  have hx119 : Bounds (473797439121 / 1000000000000) (59224680163 / 125000000000) x119 := by
    simpa +zetaDelta only [biasE, div_one] using hx118
  let x120 : ℝ := Real.log (2 / 1)
  have hx120 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x120 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x121 : ℝ := (1 / 1)+(638831 / 1000000)
  have hx121 : Bounds (1638831 / 1000000) (1638831 / 1000000) x121 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((638831 / 1000000) : ℝ)) <;> norm_num
  let x122 : ℝ := (1 / 1)+(638831 / 1000000)
  have hx122 : Bounds (1638831 / 1000000) (1638831 / 1000000) x122 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((638831 / 1000000) : ℝ)) <;> norm_num
  let x123 : ℝ := Real.log x122
  have hx123 : Bounds (246991591 / 500000000) (493983183 / 1000000000) x123 := by
    exact bounds_log hx122 (by norm_num) (by simpa only [div_one] using reflection_log_11.1) (by simpa only [div_one] using reflection_log_11.2)
  let x124 : ℝ := x121*x123
  have hx124 : Bounds (40477747607 / 50000000000) (40477747689 / 50000000000) x124 := by
    apply bounds_mul hx121 hx123 <;> norm_num
  let x125 : ℝ := -(638831 / 1000000)
  have hx125 : Bounds (-638831 / 1000000) (-638831 / 1000000) x125 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((638831 / 1000000) : ℝ))
  let x126 : ℝ := (1 / 1)+x125
  have hx126 : Bounds (361169 / 1000000) (361169 / 1000000) x126 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx125 <;> norm_num
  let x127 : ℝ := (1 / 1)-(638831 / 1000000)
  have hx127 : Bounds (361169 / 1000000) (361169 / 1000000) x127 := by
    exact hx126
  let x128 : ℝ := -(638831 / 1000000)
  have hx128 : Bounds (-638831 / 1000000) (-638831 / 1000000) x128 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((638831 / 1000000) : ℝ))
  let x129 : ℝ := (1 / 1)+x128
  have hx129 : Bounds (361169 / 1000000) (361169 / 1000000) x129 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx128 <;> norm_num
  let x130 : ℝ := (1 / 1)-(638831 / 1000000)
  have hx130 : Bounds (361169 / 1000000) (361169 / 1000000) x130 := by
    exact hx129
  let x131 : ℝ := Real.log x130
  have hx131 : Bounds (-1018409287 / 1000000000) (-203681857 / 200000000) x131 := by
    exact bounds_log hx130 (by norm_num) (by simpa only [div_one] using reflection_log_12.1) (by simpa only [div_one] using reflection_log_12.2)
  let x132 : ℝ := x127*x131
  have hx132 : Bounds (-367817863777 / 1000000000000) (-183908931527 / 500000000000) x132 := by
    apply bounds_mul hx127 hx131 <;> norm_num
  let x133 : ℝ := x124+x132
  have hx133 : Bounds (441737088363 / 1000000000000) (220868545363 / 500000000000) x133 := by
    apply bounds_add hx124 hx132 <;> norm_num
  let x134 : ℝ := (2 / 1)⁻¹
  have hx134 : Bounds (1 / 2) (1 / 2) x134 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x135 : ℝ := x133*x134
  have hx135 : Bounds (220868544181 / 1000000000000) (220868545363 / 1000000000000) x135 := by
    apply bounds_mul hx133 hx134 <;> norm_num
  let x136 : ℝ := x133/(2 / 1)
  have hx136 : Bounds (220868544181 / 1000000000000) (220868545363 / 1000000000000) x136 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx135
  let x137 : ℝ := -x136
  have hx137 : Bounds (-220868545363 / 1000000000000) (-220868544181 / 1000000000000) x137 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx136
  let x138 : ℝ := x120+x137
  have hx138 : Bounds (472278634637 / 1000000000000) (472278636819 / 1000000000000) x138 := by
    apply bounds_add hx120 hx137 <;> norm_num
  let x139 : ℝ := x120-x136
  have hx139 : Bounds (472278634637 / 1000000000000) (472278636819 / 1000000000000) x139 := by
    exact hx138
  let x140 : ℝ := biasE (638831 / 1000000)
  have hx140 : Bounds (472278634637 / 1000000000000) (472278636819 / 1000000000000) x140 := by
    simpa +zetaDelta only [biasE, div_one] using hx139
  let y : ℝ := 1 - 2 * entropyInverse ((1 + H (2*m - 1/2))/2)
  have hLh' : Real.log 2 * ((1 + H (2*m - 1/2))/2) = x98 := by
    simpa +zetaDelta only [div_one] using hLh
  have hy : Bounds (318409 / 500000) (638831 / 1000000) y := by
    apply entropyInverseBias_bracket
    · exact div_nonneg (add_nonneg zero_le_one
        (H_nonneg (by linarith [hm.1]) (by linarith [hm.2]))) two_pos.le
    · linarith [H_le_one (2*m-1/2)]
    · norm_num
    · norm_num
    · norm_num
    · have h1 : biasE (638831 / 1000000) ≤ (472278636819 / 1000000000000) := hx140.2
      have h2 : (472278747759 / 1000000000000) ≤ x98 := hx98.1
      linarith [hLh']
    · have h1 : x98 ≤ (236898430133 / 500000000000) := hx98.2
      have h2 : (473797439121 / 1000000000000) ≤ biasE (318409 / 500000) := hx119.1
      linarith [hLh']
  let x141 : ℝ := x3⁻¹
  have hx141 : Bounds (1160471441523 / 500000000000) (2327272727273 / 1000000000000) x141 := by
    apply bounds_inv hx3 <;> norm_num
  let x142 : ℝ := x98*x141
  have hx142 : Bounds (43845279937 / 40000000000) (220530902233 / 200000000000) x142 := by
    apply bounds_mul hx98 hx141 <;> norm_num
  let x143 : ℝ := x98/x3
  have hx143 : Bounds (43845279937 / 40000000000) (220530902233 / 200000000000) x143 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx142
  let x144 : ℝ := Real.log (2 / 1)
  have hx144 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x144 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x145 : ℝ := (1 / 1)+(101329 / 200000)
  have hx145 : Bounds (301329 / 200000) (301329 / 200000) x145 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((101329 / 200000) : ℝ)) <;> norm_num
  let x146 : ℝ := (1 / 1)+(101329 / 200000)
  have hx146 : Bounds (301329 / 200000) (301329 / 200000) x146 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((101329 / 200000) : ℝ)) <;> norm_num
  let x147 : ℝ := Real.log x146
  have hx147 : Bounds (102471331 / 250000000) (16395413 / 40000000) x147 := by
    exact bounds_log hx146 (by norm_num) (by simpa only [div_one] using reflection_log_13.1) (by simpa only [div_one] using reflection_log_13.2)
  let x148 : ℝ := x145*x147
  have hx148 : Bounds (617551673977 / 1000000000000) (123510335097 / 200000000000) x148 := by
    apply bounds_mul hx145 hx147 <;> norm_num
  let x149 : ℝ := -(101329 / 200000)
  have hx149 : Bounds (-101329 / 200000) (-101329 / 200000) x149 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((101329 / 200000) : ℝ))
  let x150 : ℝ := (1 / 1)+x149
  have hx150 : Bounds (98671 / 200000) (98671 / 200000) x150 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx149 <;> norm_num
  let x151 : ℝ := (1 / 1)-(101329 / 200000)
  have hx151 : Bounds (98671 / 200000) (98671 / 200000) x151 := by
    exact hx150
  let x152 : ℝ := -(101329 / 200000)
  have hx152 : Bounds (-101329 / 200000) (-101329 / 200000) x152 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((101329 / 200000) : ℝ))
  let x153 : ℝ := (1 / 1)+x152
  have hx153 : Bounds (98671 / 200000) (98671 / 200000) x153 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx152 <;> norm_num
  let x154 : ℝ := (1 / 1)-(101329 / 200000)
  have hx154 : Bounds (98671 / 200000) (98671 / 200000) x154 := by
    exact hx153
  let x155 : ℝ := Real.log x154
  have hx155 : Bounds (-176631571 / 250000000) (-353263141 / 500000000) x155 := by
    exact bounds_log hx154 (by norm_num) (by simpa only [div_one] using reflection_log_14.1) (by simpa only [div_one] using reflection_log_14.2)
  let x156 : ℝ := x151*x155
  have hx156 : Bounds (-348568274843 / 1000000000000) (-5446379279 / 15625000000) x156 := by
    apply bounds_mul hx151 hx155 <;> norm_num
  let x157 : ℝ := x148+x156
  have hx157 : Bounds (134491699567 / 500000000000) (268983401629 / 1000000000000) x157 := by
    apply bounds_add hx148 hx156 <;> norm_num
  let x158 : ℝ := (2 / 1)⁻¹
  have hx158 : Bounds (1 / 2) (1 / 2) x158 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x159 : ℝ := x157*x158
  have hx159 : Bounds (134491699567 / 1000000000000) (26898340163 / 200000000000) x159 := by
    apply bounds_mul hx157 hx158 <;> norm_num
  let x160 : ℝ := x157/(2 / 1)
  have hx160 : Bounds (134491699567 / 1000000000000) (26898340163 / 200000000000) x160 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx159
  let x161 : ℝ := -x160
  have hx161 : Bounds (-26898340163 / 200000000000) (-134491699567 / 1000000000000) x161 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx160
  let x162 : ℝ := x144+x161
  have hx162 : Bounds (111731095837 / 200000000000) (558655481433 / 1000000000000) x162 := by
    apply bounds_add hx144 hx161 <;> norm_num
  let x163 : ℝ := x144-x160
  have hx163 : Bounds (111731095837 / 200000000000) (558655481433 / 1000000000000) x163 := by
    exact hx162
  let x164 : ℝ := biasE (101329 / 200000)
  have hx164 : Bounds (111731095837 / 200000000000) (558655481433 / 1000000000000) x164 := by
    simpa +zetaDelta only [biasE, div_one] using hx163
  let x165 : ℝ := Real.log (2 / 1)
  have hx165 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x165 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x166 : ℝ := (1 / 1)+(254321 / 500000)
  have hx166 : Bounds (754321 / 500000) (754321 / 500000) x166 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((254321 / 500000) : ℝ)) <;> norm_num
  let x167 : ℝ := (1 / 1)+(254321 / 500000)
  have hx167 : Bounds (754321 / 500000) (754321 / 500000) x167 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((254321 / 500000) : ℝ)) <;> norm_num
  let x168 : ℝ := Real.log x167
  have hx168 : Bounds (102802477 / 250000000) (411209909 / 1000000000) x168 := by
    exact bounds_log hx167 (by norm_num) (by simpa only [div_one] using reflection_log_15.1) (by simpa only [div_one] using reflection_log_15.2)
  let x169 : ℝ := x166*x168
  have hx169 : Bounds (77546067253 / 125000000000) (310184269767 / 500000000000) x169 := by
    apply bounds_mul hx166 hx168 <;> norm_num
  let x170 : ℝ := -(254321 / 500000)
  have hx170 : Bounds (-254321 / 500000) (-254321 / 500000) x170 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((254321 / 500000) : ℝ))
  let x171 : ℝ := (1 / 1)+x170
  have hx171 : Bounds (245679 / 500000) (245679 / 500000) x171 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx170 <;> norm_num
  let x172 : ℝ := (1 / 1)-(254321 / 500000)
  have hx172 : Bounds (245679 / 500000) (245679 / 500000) x172 := by
    exact hx171
  let x173 : ℝ := -(254321 / 500000)
  have hx173 : Bounds (-254321 / 500000) (-254321 / 500000) x173 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((254321 / 500000) : ℝ))
  let x174 : ℝ := (1 / 1)+x173
  have hx174 : Bounds (245679 / 500000) (245679 / 500000) x174 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx173 <;> norm_num
  let x175 : ℝ := (1 / 1)-(254321 / 500000)
  have hx175 : Bounds (245679 / 500000) (245679 / 500000) x175 := by
    exact hx174
  let x176 : ℝ := Real.log x175
  have hx176 : Bounds (-355291147 / 500000000) (-177645573 / 250000000) x176 := by
    exact bounds_log hx175 (by norm_num) (by simpa only [div_one] using reflection_log_16.1) (by simpa only [div_one] using reflection_log_16.2)
  let x177 : ℝ := x172*x176
  have hx177 : Bounds (-10910946713 / 31250000000) (-43643786729 / 125000000000) x177 := by
    apply bounds_mul hx172 hx176 <;> norm_num
  let x178 : ℝ := x169+x177
  have hx178 : Bounds (33902280401 / 125000000000) (135609122851 / 500000000000) x178 := by
    apply bounds_add hx169 hx177 <;> norm_num
  let x179 : ℝ := (2 / 1)⁻¹
  have hx179 : Bounds (1 / 2) (1 / 2) x179 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x180 : ℝ := x178*x179
  have hx180 : Bounds (33902280401 / 250000000000) (135609122851 / 1000000000000) x180 := by
    apply bounds_mul hx178 hx179 <;> norm_num
  let x181 : ℝ := x178/(2 / 1)
  have hx181 : Bounds (33902280401 / 250000000000) (135609122851 / 1000000000000) x181 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx180
  let x182 : ℝ := -x181
  have hx182 : Bounds (-135609122851 / 1000000000000) (-33902280401 / 250000000000) x182 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx181
  let x183 : ℝ := x165+x182
  have hx183 : Bounds (557538057149 / 1000000000000) (139384514849 / 250000000000) x183 := by
    apply bounds_add hx165 hx182 <;> norm_num
  let x184 : ℝ := x165-x181
  have hx184 : Bounds (557538057149 / 1000000000000) (139384514849 / 250000000000) x184 := by
    exact hx183
  let x185 : ℝ := biasE (254321 / 500000)
  have hx185 : Bounds (557538057149 / 1000000000000) (139384514849 / 250000000000) x185 := by
    simpa +zetaDelta only [biasE, div_one] using hx184
  let x186 : ℝ := x143*(101329 / 200000)
  have hx186 : Bounds (277674898171 / 500000000000) (55865439481 / 100000000000) x186 := by
    apply bounds_mul hx143 (bounds_const ((101329 / 200000) : ℝ)) <;> norm_num
  let x187 : ℝ := x143*(254321 / 500000)
  have hx187 : Bounds (278769385971 / 500000000000) (140214098967 / 250000000000) x187 := by
    apply bounds_mul hx143 (bounds_const ((254321 / 500000) : ℝ)) <;> norm_num
  let c : ℝ := Reflection.regularContact (x3 / (Real.log 2 * ((1 + H (2*m - 1/2))/2)))
  have hcMem := Reflection.regularContact_mem
    (x3 / (Real.log 2 * ((1 + H (2*m - 1/2))/2)))
  have hc0 : 0 ≤ c := by
    dsimp only [c]
    apply GeneralCK.Certificates.RegularContactBounds.regularContact_nonneg
    rw [hLh']
    exact div_nonneg (by linarith [hx3.1]) (by linarith [hx98.1])
  have hcEq : biasE c = x143 * c := by
    have he := Reflection.regularContact_equation (x3 / x98)
    have hcdef : c = Reflection.regularContact (x3 / x98) := by
      dsimp only [c]
      rw [hLh']
    rw [← hcdef] at he
    change biasE c = (x98 / x3) * c
    have hx0 : 0 < x3 := by linarith [hx3.1]
    have hh0 : 0 < x98 := by linarith [hx98.1]
    field_simp [hx0.ne', hh0.ne'] at he ⊢
    nlinarith
  have hc : Bounds (101329 / 200000) (254321 / 500000) c := by
    apply contact_bracket hc0 hcMem.2.le (by norm_num) (by norm_num) (by norm_num)
      (show 0 < x143 by linarith [hx143.1]) hcEq
    · have h1 : x143 * (101329 / 200000) ≤ (55865439481 / 100000000000) := hx186.2
      have h2 : (111731095837 / 200000000000) ≤ biasE (101329 / 200000) := hx164.1
      linarith
    · have h1 : biasE (254321 / 500000) ≤ (139384514849 / 250000000000) := hx185.2
      have h2 : (278769385971 / 500000000000) ≤ x143 * (254321 / 500000) := hx187.1
      linarith
  let x188 : ℝ := (1 / 1)+y
  have hx188 : Bounds (818409 / 500000) (1638831 / 1000000) x188 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hy <;> norm_num
  let x189 : ℝ := -y
  have hx189 : Bounds (-638831 / 1000000) (-318409 / 500000) x189 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hy
  let x190 : ℝ := (1 / 1)+x189
  have hx190 : Bounds (361169 / 1000000) (181591 / 500000) x190 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx189 <;> norm_num
  let x191 : ℝ := (1 / 1)-y
  have hx191 : Bounds (361169 / 1000000) (181591 / 500000) x191 := by
    exact hx190
  let x192 : ℝ := x191⁻¹
  have hx192 : Bounds (2753440423809 / 1000000000000) (2768786911391 / 1000000000000) x192 := by
    apply bounds_inv hx191 <;> norm_num
  let x193 : ℝ := x188*x192
  have hx193 : Bounds (2253440423809 / 500000000000) (2268786911391 / 500000000000) x193 := by
    apply bounds_mul hx188 hx192 <;> norm_num
  let x194 : ℝ := x188/x191
  have hx194 : Bounds (2253440423809 / 500000000000) (2268786911391 / 500000000000) x194 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx193
  let x195 : ℝ := Real.log x194
  have hx195 : Bounds (301121061 / 200000000) (151239247 / 100000000) x195 := by
    exact bounds_log hx194 (by norm_num) (by simpa only [div_one] using reflection_log_17.1) (by simpa only [div_one] using reflection_log_18.2)
  let x196 : ℝ := (2 / 1)⁻¹
  have hx196 : Bounds (1 / 2) (1 / 2) x196 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x197 : ℝ := x195*x196
  have hx197 : Bounds (301121061 / 400000000) (151239247 / 200000000) x197 := by
    apply bounds_mul hx195 hx196 <;> norm_num
  let x198 : ℝ := x195/(2 / 1)
  have hx198 : Bounds (301121061 / 400000000) (151239247 / 200000000) x198 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx197
  let x199 : ℝ := (1 / 1)+c
  have hx199 : Bounds (301329 / 200000) (754321 / 500000) x199 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hc <;> norm_num
  let x200 : ℝ := -c
  have hx200 : Bounds (-254321 / 500000) (-101329 / 200000) x200 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hc
  let x201 : ℝ := (1 / 1)+x200
  have hx201 : Bounds (245679 / 500000) (98671 / 200000) x201 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx200 <;> norm_num
  let x202 : ℝ := (1 / 1)-c
  have hx202 : Bounds (245679 / 500000) (98671 / 200000) x202 := by
    exact hx201
  let x203 : ℝ := x202⁻¹
  have hx203 : Bounds (2026938006101 / 1000000000000) (508793995417 / 250000000000) x203 := by
    apply bounds_inv hx202 <;> norm_num
  let x204 : ℝ := x199*x203
  have hx204 : Bounds (1526938006101 / 500000000000) (383793995417 / 125000000000) x204 := by
    apply bounds_mul hx199 hx203 <;> norm_num
  let x205 : ℝ := x199/x202
  have hx205 : Bounds (1526938006101 / 500000000000) (383793995417 / 125000000000) x205 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx204
  let x206 : ℝ := Real.log x205
  have hx206 : Bounds (558205803 / 500000000) (560896101 / 500000000) x206 := by
    exact bounds_log hx205 (by norm_num) (by simpa only [div_one] using reflection_log_19.1) (by simpa only [div_one] using reflection_log_20.2)
  let x207 : ℝ := (2 / 1)⁻¹
  have hx207 : Bounds (1 / 2) (1 / 2) x207 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x208 : ℝ := x206*x207
  have hx208 : Bounds (558205803 / 1000000000) (560896101 / 1000000000) x208 := by
    apply bounds_mul hx206 hx207 <;> norm_num
  let x209 : ℝ := x206/(2 / 1)
  have hx209 : Bounds (558205803 / 1000000000) (560896101 / 1000000000) x209 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx208
  let x210 : ℝ := (2 / 1)*x50
  have hx210 : Bounds (597218166567 / 500000000000) (597757503559 / 500000000000) x210 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx50 <;> norm_num
  let x211 : ℝ := (2 / 1)*x98
  have hx211 : Bounds (472278747759 / 500000000000) (236898430133 / 250000000000) x211 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx98 <;> norm_num
  let x212 : ℝ := -x211
  have hx212 : Bounds (-236898430133 / 250000000000) (-472278747759 / 500000000000) x212 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx211
  let x213 : ℝ := x210+x212
  have hx213 : Bounds (123421306301 / 500000000000) (627393779 / 2500000000) x213 := by
    apply bounds_add hx210 hx212 <;> norm_num
  let x214 : ℝ := x210-x211
  have hx214 : Bounds (123421306301 / 500000000000) (627393779 / 2500000000) x214 := by
    exact hx213
  let x215 : ℝ := y*x198
  have hx215 : Bounds (479398279559 / 1000000000000) (241540798501 / 500000000000) x215 := by
    apply bounds_mul hy hx198 <;> norm_num
  let x216 : ℝ := -x215
  have hx216 : Bounds (-241540798501 / 500000000000) (-479398279559 / 1000000000000) x216 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx215
  let x217 : ℝ := x214+x216
  have hx217 : Bounds (-590597461 / 2500000000) (-228440767959 / 1000000000000) x217 := by
    apply bounds_add hx214 hx216 <;> norm_num
  let x218 : ℝ := x214-x215
  have hx218 : Bounds (-590597461 / 2500000000) (-228440767959 / 1000000000000) x218 := by
    exact hx217
  let x219 : ℝ := x3*x209
  have hx219 : Bounds (29981756997 / 125000000000) (241667343517 / 1000000000000) x219 := by
    apply bounds_mul hx3 hx209 <;> norm_num
  let x220 : ℝ := x218+x219
  have hx220 : Bounds (451883947 / 125000000000) (6613287779 / 500000000000) x220 := by
    apply bounds_add hx218 hx219 <;> norm_num
  have hpos : 0 < x220 := lt_of_lt_of_le (by norm_num) hx220.1
  have hcert :
      0 ≤ 2 * biasE (1 - 2*m) - 2*(x98)
        - (1 - 2*entropyInverse ((1 + H (2*m - 1/2))/2)) *
            SmallMean.A (1 - 2*entropyInverse ((1 + H (2*m - 1/2))/2))
        + (1 - 2*m) *
            SmallMean.A (regularContact ((1 - 2*m)/(Real.log 2*((1 + H (2*m - 1/2))/2)))) := by
    simpa +zetaDelta only [SmallMean.A, div_one] using hpos.le
  dsimp only
  nlinarith [hcert, hLh]

theorem acceptedCertificate : DoubleCapBiasCellCertificate (1457 / 5120) (73 / 256) (fun m => (1 + H (2*m - 1/2))/2) where
  domain := by norm_num
  sound m hmLo hmHi := by
    exact cell_bias_nonneg m ⟨hmLo, hmHi⟩

theorem accepted_cell :
    ∀ m, (1457 / 5120) ≤ m → m ≤ (73 / 256) → 0 ≤ doubleCapHighResidual m := by
  intro m hmLo hmHi
  unfold doubleCapHighResidual
  apply doubleCapEndpointResidual_nonneg_of_biasCell acceptedCertificate hmLo hmHi
  exact div_pos (by linarith [H_nonneg (by linarith : 0 ≤ 2*m-1/2) (by linarith : 2*m-1/2 ≤ 1)]) two_pos

#print axioms cell_bias_nonneg
#print axioms accepted_cell

end GeneralCK.Certificates.DoubleCapMiddle.Cell0070

end


