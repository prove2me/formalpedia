-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0113__7_q02
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0113__7_q02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T09:11:45.675832+00:00
-- url     : https://prove2.me/theorems/063a6d9e-7174-4d06-b153-90dbdcb382fa
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0113 (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0114, GeneralCK.Certificates.Gener…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0113 (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0114, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0115, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0116, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0117, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0118, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0119) (piece 3 of 7)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0113 (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0114, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0115, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0116, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0117, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0118, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0119) (piece 3 of 7)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0113 (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0114, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0115, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0116, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0117, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0118, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0119) (piece 3 of 7) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0113 (+6 modules: GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0114, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0115, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0116, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0117, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0118, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0119) (piece 3 of 7).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0113__7_q01

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0115 =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0115
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Reflection
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem cell_bias_nonneg (m : ℝ) (hm : Bounds (199 / 640) (319 / 1024) m) :
    let h := (1 + H (2*m - 1/2))/2
    let x := 1-2*m
    let y := 1-2*entropyInverse h
    let c := regularContact (x/(Real.log 2*h))
    0 ≤ 2*(biasE x-Real.log 2*h)-y*SmallMean.A y+x*SmallMean.A c := by
  have hEq : biasE (2-4*m) = Real.log 2 * H (2*m-1/2) := by
    have hmstrict : 1/4 < m := by
      have hlo : (1/4 : ℝ) < (199 / 640) := by norm_num
      exact lt_of_lt_of_le hlo hm.1
    rw [show 2-4*m = 1-2*(2*m-1/2) by ring,
      GeneralCK.Correction.Natural.biasE_probability (by linarith [hmstrict]) (by linarith [hm.2]),
      GeneralCK.Certificates.Mixed.hn_eq_H_mul_log]
    ring
  have hLh : Real.log 2 * ((1 + H (2*m - 1/2))/2) = (Real.log 2 + biasE (2-4*m))/2 := by
    rw [hEq]
    ring
  let x0 : ℝ := (2 / 1)*m
  have hx0 : Bounds (199 / 320) (319 / 512) x0 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hm <;> norm_num
  let x1 : ℝ := -x0
  have hx1 : Bounds (-319 / 512) (-199 / 320) x1 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx0
  let x2 : ℝ := (1 / 1)+x1
  have hx2 : Bounds (193 / 512) (121 / 320) x2 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx1 <;> norm_num
  let x3 : ℝ := (1 / 1)-x0
  have hx3 : Bounds (193 / 512) (121 / 320) x3 := by
    exact hx2
  let x4 : ℝ := (4 / 1)*m
  have hx4 : Bounds (199 / 160) (319 / 256) x4 := by
    apply bounds_mul (bounds_const ((4 / 1) : ℝ)) hm <;> norm_num
  let x5 : ℝ := -x4
  have hx5 : Bounds (-319 / 256) (-199 / 160) x5 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx4
  let x6 : ℝ := (2 / 1)+x5
  have hx6 : Bounds (193 / 256) (121 / 160) x6 := by
    apply bounds_add (bounds_const ((2 / 1) : ℝ)) hx5 <;> norm_num
  let x7 : ℝ := (2 / 1)-x4
  have hx7 : Bounds (193 / 256) (121 / 160) x7 := by
    exact hx6
  let x8 : ℝ := Real.log (2 / 1)
  have hx8 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x8 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x9 : ℝ := (1 / 1)+(121 / 320)
  have hx9 : Bounds (441 / 320) (441 / 320) x9 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((121 / 320) : ℝ)) <;> norm_num
  let x10 : ℝ := (1 / 1)+(121 / 320)
  have hx10 : Bounds (441 / 320) (441 / 320) x10 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((121 / 320) : ℝ)) <;> norm_num
  let x11 : ℝ := Real.log x10
  have hx11 : Bounds (320723879 / 1000000000) (8018097 / 25000000) x11 := by
    exact bounds_log hx10 (by norm_num) (by simpa only [div_one] using reflection_log_1.1) (by simpa only [div_one] using reflection_log_1.2)
  let x12 : ℝ := x9*x11
  have hx12 : Bounds (220998797873 / 500000000000) (3535980777 / 8000000000) x12 := by
    apply bounds_mul hx9 hx11 <;> norm_num
  let x13 : ℝ := -(121 / 320)
  have hx13 : Bounds (-121 / 320) (-121 / 320) x13 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((121 / 320) : ℝ))
  let x14 : ℝ := (1 / 1)+x13
  have hx14 : Bounds (199 / 320) (199 / 320) x14 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx13 <;> norm_num
  let x15 : ℝ := (1 / 1)-(121 / 320)
  have hx15 : Bounds (199 / 320) (199 / 320) x15 := by
    exact hx14
  let x16 : ℝ := -(121 / 320)
  have hx16 : Bounds (-121 / 320) (-121 / 320) x16 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((121 / 320) : ℝ))
  let x17 : ℝ := (1 / 1)+x16
  have hx17 : Bounds (199 / 320) (199 / 320) x17 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx16 <;> norm_num
  let x18 : ℝ := (1 / 1)-(121 / 320)
  have hx18 : Bounds (199 / 320) (199 / 320) x18 := by
    exact hx17
  let x19 : ℝ := Real.log x18
  have hx19 : Bounds (-118754043 / 250000000) (-475016171 / 1000000000) x19 := by
    exact bounds_log hx18 (by norm_num) (by simpa only [div_one] using reflection_log_2.1) (by simpa only [div_one] using reflection_log_2.2)
  let x20 : ℝ := x15*x19
  have hx20 : Bounds (-295400681963 / 1000000000000) (-14770034067 / 50000000000) x20 := by
    apply bounds_mul hx15 hx19 <;> norm_num
  let x21 : ℝ := x12+x20
  have hx21 : Bounds (146596913783 / 1000000000000) (29319383157 / 200000000000) x21 := by
    apply bounds_add hx12 hx20 <;> norm_num
  let x22 : ℝ := (2 / 1)⁻¹
  have hx22 : Bounds (1 / 2) (1 / 2) x22 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x23 : ℝ := x21*x22
  have hx23 : Bounds (73298456891 / 1000000000000) (73298457893 / 1000000000000) x23 := by
    apply bounds_mul hx21 hx22 <;> norm_num
  let x24 : ℝ := x21/(2 / 1)
  have hx24 : Bounds (73298456891 / 1000000000000) (73298457893 / 1000000000000) x24 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx23
  let x25 : ℝ := -x24
  have hx25 : Bounds (-73298457893 / 1000000000000) (-73298456891 / 1000000000000) x25 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx24
  let x26 : ℝ := x8+x25
  have hx26 : Bounds (619848722107 / 1000000000000) (619848724109 / 1000000000000) x26 := by
    apply bounds_add hx8 hx25 <;> norm_num
  let x27 : ℝ := x8-x24
  have hx27 : Bounds (619848722107 / 1000000000000) (619848724109 / 1000000000000) x27 := by
    exact hx26
  let x28 : ℝ := biasE (121 / 320)
  have hx28 : Bounds (619848722107 / 1000000000000) (619848724109 / 1000000000000) x28 := by
    simpa +zetaDelta only [biasE, div_one] using hx27
  let x29 : ℝ := Real.log (2 / 1)
  have hx29 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x29 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x30 : ℝ := (1 / 1)+(193 / 512)
  have hx30 : Bounds (705 / 512) (705 / 512) x30 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((193 / 512) : ℝ)) <;> norm_num
  let x31 : ℝ := (1 / 1)+(193 / 512)
  have hx31 : Bounds (705 / 512) (705 / 512) x31 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((193 / 512) : ℝ)) <;> norm_num
  let x32 : ℝ := Real.log x31
  have hx32 : Bounds (319873177 / 1000000000) (159936589 / 500000000) x32 := by
    exact bounds_log hx31 (by norm_num) (by simpa only [div_one] using reflection_log_3.1) (by simpa only [div_one] using reflection_log_3.2)
  let x33 : ℝ := x30*x32
  have hx33 : Bounds (440450370673 / 1000000000000) (440450372051 / 1000000000000) x33 := by
    apply bounds_mul hx30 hx32 <;> norm_num
  let x34 : ℝ := -(193 / 512)
  have hx34 : Bounds (-193 / 512) (-193 / 512) x34 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((193 / 512) : ℝ))
  let x35 : ℝ := (1 / 1)+x34
  have hx35 : Bounds (319 / 512) (319 / 512) x35 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx34 <;> norm_num
  let x36 : ℝ := (1 / 1)-(193 / 512)
  have hx36 : Bounds (319 / 512) (319 / 512) x36 := by
    exact hx35
  let x37 : ℝ := -(193 / 512)
  have hx37 : Bounds (-193 / 512) (-193 / 512) x37 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((193 / 512) : ℝ))
  let x38 : ℝ := (1 / 1)+x37
  have hx38 : Bounds (319 / 512) (319 / 512) x38 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx37 <;> norm_num
  let x39 : ℝ := (1 / 1)-(193 / 512)
  have hx39 : Bounds (319 / 512) (319 / 512) x39 := by
    exact hx38
  let x40 : ℝ := Real.log x39
  have hx40 : Bounds (-473133523 / 1000000000) (-236566761 / 500000000) x40 := by
    exact bounds_log hx39 (by norm_num) (by simpa only [div_one] using reflection_log_4.1) (by simpa only [div_one] using reflection_log_4.2)
  let x41 : ℝ := x36*x40
  have hx41 : Bounds (-294784362963 / 1000000000000) (-294784362339 / 1000000000000) x41 := by
    apply bounds_mul hx36 hx40 <;> norm_num
  let x42 : ℝ := x33+x41
  have hx42 : Bounds (14566600771 / 100000000000) (9104125607 / 62500000000) x42 := by
    apply bounds_add hx33 hx41 <;> norm_num
  let x43 : ℝ := (2 / 1)⁻¹
  have hx43 : Bounds (1 / 2) (1 / 2) x43 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x44 : ℝ := x42*x43
  have hx44 : Bounds (14566600771 / 200000000000) (9104125607 / 125000000000) x44 := by
    apply bounds_mul hx42 hx43 <;> norm_num
  let x45 : ℝ := x42/(2 / 1)
  have hx45 : Bounds (14566600771 / 200000000000) (9104125607 / 125000000000) x45 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx44
  let x46 : ℝ := -x45
  have hx46 : Bounds (-9104125607 / 125000000000) (-14566600771 / 200000000000) x46 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx45
  let x47 : ℝ := x29+x46
  have hx47 : Bounds (77539271893 / 125000000000) (124062835429 / 200000000000) x47 := by
    apply bounds_add hx29 hx46 <;> norm_num
  let x48 : ℝ := x29-x45
  have hx48 : Bounds (77539271893 / 125000000000) (124062835429 / 200000000000) x48 := by
    exact hx47
  let x49 : ℝ := biasE (193 / 512)
  have hx49 : Bounds (77539271893 / 125000000000) (124062835429 / 200000000000) x49 := by
    simpa +zetaDelta only [biasE, div_one] using hx48
  let x50 : ℝ := biasE x3
  have hx50 : Bounds (619848722107 / 1000000000000) (124062835429 / 200000000000) x50 := by
    exact bounds_biasE hx3 (by norm_num) (by norm_num) hx28.1 hx49.2
  let x51 : ℝ := Real.log (2 / 1)
  have hx51 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x51 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x52 : ℝ := (1 / 1)+(121 / 160)
  have hx52 : Bounds (281 / 160) (281 / 160) x52 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((121 / 160) : ℝ)) <;> norm_num
  let x53 : ℝ := (1 / 1)+(121 / 160)
  have hx53 : Bounds (281 / 160) (281 / 160) x53 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((121 / 160) : ℝ)) <;> norm_num
  let x54 : ℝ := Real.log x53
  have hx54 : Bounds (281590427 / 500000000) (112636171 / 200000000) x54 := by
    exact bounds_log hx53 (by norm_num) (by simpa only [div_one] using reflection_log_5.1) (by simpa only [div_one] using reflection_log_5.2)
  let x55 : ℝ := x52*x54
  have hx55 : Bounds (989086374837 / 1000000000000) (494543188297 / 500000000000) x55 := by
    apply bounds_mul hx52 hx54 <;> norm_num
  let x56 : ℝ := -(121 / 160)
  have hx56 : Bounds (-121 / 160) (-121 / 160) x56 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((121 / 160) : ℝ))
  let x57 : ℝ := (1 / 1)+x56
  have hx57 : Bounds (39 / 160) (39 / 160) x57 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx56 <;> norm_num
  let x58 : ℝ := (1 / 1)-(121 / 160)
  have hx58 : Bounds (39 / 160) (39 / 160) x58 := by
    exact hx57
  let x59 : ℝ := -(121 / 160)
  have hx59 : Bounds (-121 / 160) (-121 / 160) x59 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((121 / 160) : ℝ))
  let x60 : ℝ := (1 / 1)+x59
  have hx60 : Bounds (39 / 160) (39 / 160) x60 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx59 <;> norm_num
  let x61 : ℝ := (1 / 1)-(121 / 160)
  have hx61 : Bounds (39 / 160) (39 / 160) x61 := by
    exact hx60
  let x62 : ℝ := Real.log x61
  have hx62 : Bounds (-141161217 / 100000000) (-1411612167 / 1000000000) x62 := by
    exact bounds_log hx61 (by norm_num) (by simpa only [div_one] using reflection_log_6.1) (by simpa only [div_one] using reflection_log_6.2)
  let x63 : ℝ := x58*x62
  have hx63 : Bounds (-172040233219 / 500000000000) (-172040232853 / 500000000000) x63 := by
    apply bounds_mul hx58 hx62 <;> norm_num
  let x64 : ℝ := x55+x63
  have hx64 : Bounds (645005908399 / 1000000000000) (80625738861 / 125000000000) x64 := by
    apply bounds_add hx55 hx63 <;> norm_num
  let x65 : ℝ := (2 / 1)⁻¹
  have hx65 : Bounds (1 / 2) (1 / 2) x65 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x66 : ℝ := x64*x65
  have hx66 : Bounds (322502954199 / 1000000000000) (80625738861 / 250000000000) x66 := by
    apply bounds_mul hx64 hx65 <;> norm_num
  let x67 : ℝ := x64/(2 / 1)
  have hx67 : Bounds (322502954199 / 1000000000000) (80625738861 / 250000000000) x67 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx66
  let x68 : ℝ := -x67
  have hx68 : Bounds (-80625738861 / 250000000000) (-322502954199 / 1000000000000) x68 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx67
  let x69 : ℝ := x51+x68
  have hx69 : Bounds (92661056139 / 250000000000) (370644226801 / 1000000000000) x69 := by
    apply bounds_add hx51 hx68 <;> norm_num
  let x70 : ℝ := x51-x67
  have hx70 : Bounds (92661056139 / 250000000000) (370644226801 / 1000000000000) x70 := by
    exact hx69
  let x71 : ℝ := biasE (121 / 160)
  have hx71 : Bounds (92661056139 / 250000000000) (370644226801 / 1000000000000) x71 := by
    simpa +zetaDelta only [biasE, div_one] using hx70
  let x72 : ℝ := Real.log (2 / 1)
  have hx72 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x72 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x73 : ℝ := (1 / 1)+(193 / 256)
  have hx73 : Bounds (449 / 256) (449 / 256) x73 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((193 / 256) : ℝ)) <;> norm_num
  let x74 : ℝ := (1 / 1)+(193 / 256)
  have hx74 : Bounds (449 / 256) (449 / 256) x74 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((193 / 256) : ℝ)) <;> norm_num
  let x75 : ℝ := Real.log x74
  have hx75 : Bounds (561845443 / 1000000000) (140461361 / 250000000) x75 := by
    exact bounds_log hx74 (by norm_num) (by simpa only [div_one] using reflection_log_7.1) (by simpa only [div_one] using reflection_log_7.2)
  let x76 : ℝ := x73*x75
  have hx76 : Bounds (985424234011 / 1000000000000) (492712117883 / 500000000000) x76 := by
    apply bounds_mul hx73 hx75 <;> norm_num
  let x77 : ℝ := -(193 / 256)
  have hx77 : Bounds (-193 / 256) (-193 / 256) x77 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((193 / 256) : ℝ))
  let x78 : ℝ := (1 / 1)+x77
  have hx78 : Bounds (63 / 256) (63 / 256) x78 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx77 <;> norm_num
  let x79 : ℝ := (1 / 1)-(193 / 256)
  have hx79 : Bounds (63 / 256) (63 / 256) x79 := by
    exact hx78
  let x80 : ℝ := -(193 / 256)
  have hx80 : Bounds (-193 / 256) (-193 / 256) x80 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((193 / 256) : ℝ))
  let x81 : ℝ := (1 / 1)+x80
  have hx81 : Bounds (63 / 256) (63 / 256) x81 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx80 <;> norm_num
  let x82 : ℝ := (1 / 1)-(193 / 256)
  have hx82 : Bounds (63 / 256) (63 / 256) x82 := by
    exact hx81
  let x83 : ℝ := Real.log x82
  have hx83 : Bounds (-1402042719 / 1000000000) (-350510679 / 250000000) x83 := by
    exact bounds_log hx82 (by norm_num) (by simpa only [div_one] using reflection_log_8.1) (by simpa only [div_one] using reflection_log_8.2)
  let x84 : ℝ := x79*x83
  have hx84 : Bounds (-345033950379 / 1000000000000) (-8625848741 / 25000000000) x84 := by
    apply bounds_mul hx79 hx83 <;> norm_num
  let x85 : ℝ := x76+x84
  have hx85 : Bounds (40024392727 / 62500000000) (320195143063 / 500000000000) x85 := by
    apply bounds_add hx76 hx84 <;> norm_num
  let x86 : ℝ := (2 / 1)⁻¹
  have hx86 : Bounds (1 / 2) (1 / 2) x86 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x87 : ℝ := x85*x86
  have hx87 : Bounds (40024392727 / 125000000000) (320195143063 / 1000000000000) x87 := by
    apply bounds_mul hx85 hx86 <;> norm_num
  let x88 : ℝ := x85/(2 / 1)
  have hx88 : Bounds (40024392727 / 125000000000) (320195143063 / 1000000000000) x88 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx87
  let x89 : ℝ := -x88
  have hx89 : Bounds (-320195143063 / 1000000000000) (-40024392727 / 125000000000) x89 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx88
  let x90 : ℝ := x72+x89
  have hx90 : Bounds (372952036937 / 1000000000000) (23309502449 / 62500000000) x90 := by
    apply bounds_add hx72 hx89 <;> norm_num
  let x91 : ℝ := x72-x88
  have hx91 : Bounds (372952036937 / 1000000000000) (23309502449 / 62500000000) x91 := by
    exact hx90
  let x92 : ℝ := biasE (193 / 256)
  have hx92 : Bounds (372952036937 / 1000000000000) (23309502449 / 62500000000) x92 := by
    simpa +zetaDelta only [biasE, div_one] using hx91
  let x93 : ℝ := biasE x7
  have hx93 : Bounds (92661056139 / 250000000000) (23309502449 / 62500000000) x93 := by
    exact bounds_biasE hx7 (by norm_num) (by norm_num) hx71.1 hx92.2
  let x94 : ℝ := Real.log (2 / 1)
  have hx94 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x94 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x95 : ℝ := x94+x93
  have hx95 : Bounds (265947851139 / 250000000000) (133262402523 / 125000000000) x95 := by
    apply bounds_add hx94 hx93 <;> norm_num
  let x96 : ℝ := (2 / 1)⁻¹
  have hx96 : Bounds (1 / 2) (1 / 2) x96 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x97 : ℝ := x95*x96
  have hx97 : Bounds (265947851139 / 500000000000) (133262402523 / 250000000000) x97 := by
    apply bounds_mul hx95 hx96 <;> norm_num
  let x98 : ℝ := x95/(2 / 1)
  have hx98 : Bounds (265947851139 / 500000000000) (133262402523 / 250000000000) x98 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx97
  let x99 : ℝ := Real.log (2 / 1)
  have hx99 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x99 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x100 : ℝ := (1 / 1)+(68773 / 125000)
  have hx100 : Bounds (193773 / 125000) (193773 / 125000) x100 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((68773 / 125000) : ℝ)) <;> norm_num
  let x101 : ℝ := (1 / 1)+(68773 / 125000)
  have hx101 : Bounds (193773 / 125000) (193773 / 125000) x101 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((68773 / 125000) : ℝ)) <;> norm_num
  let x102 : ℝ := Real.log x101
  have hx102 : Bounds (438373633 / 1000000000) (219186817 / 500000000) x102 := by
    exact bounds_log hx101 (by norm_num) (by simpa only [div_one] using reflection_log_9.1) (by simpa only [div_one] using reflection_log_9.2)
  let x103 : ℝ := x100*x102
  have hx103 : Bounds (339779895949 / 500000000000) (679559793449 / 1000000000000) x103 := by
    apply bounds_mul hx100 hx102 <;> norm_num
  let x104 : ℝ := -(68773 / 125000)
  have hx104 : Bounds (-68773 / 125000) (-68773 / 125000) x104 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((68773 / 125000) : ℝ))
  let x105 : ℝ := (1 / 1)+x104
  have hx105 : Bounds (56227 / 125000) (56227 / 125000) x105 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx104 <;> norm_num
  let x106 : ℝ := (1 / 1)-(68773 / 125000)
  have hx106 : Bounds (56227 / 125000) (56227 / 125000) x106 := by
    exact hx105
  let x107 : ℝ := -(68773 / 125000)
  have hx107 : Bounds (-68773 / 125000) (-68773 / 125000) x107 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((68773 / 125000) : ℝ))
  let x108 : ℝ := (1 / 1)+x107
  have hx108 : Bounds (56227 / 125000) (56227 / 125000) x108 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx107 <;> norm_num
  let x109 : ℝ := (1 / 1)-(68773 / 125000)
  have hx109 : Bounds (56227 / 125000) (56227 / 125000) x109 := by
    exact hx108
  let x110 : ℝ := Real.log x109
  have hx110 : Bounds (-79891667 / 100000000) (-199729167 / 250000000) x110 := by
    exact bounds_log hx109 (by norm_num) (by simpa only [div_one] using reflection_log_10.1) (by simpa only [div_one] using reflection_log_10.2)
  let x111 : ℝ := x106*x110
  have hx111 : Bounds (-359365500833 / 1000000000000) (-359365499933 / 1000000000000) x111 := by
    apply bounds_mul hx106 hx110 <;> norm_num
  let x112 : ℝ := x103+x111
  have hx112 : Bounds (64038858213 / 200000000000) (80048573379 / 250000000000) x112 := by
    apply bounds_add hx103 hx111 <;> norm_num
  let x113 : ℝ := (2 / 1)⁻¹
  have hx113 : Bounds (1 / 2) (1 / 2) x113 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x114 : ℝ := x112*x113
  have hx114 : Bounds (40024286383 / 250000000000) (80048573379 / 500000000000) x114 := by
    apply bounds_mul hx112 hx113 <;> norm_num
  let x115 : ℝ := x112/(2 / 1)
  have hx115 : Bounds (40024286383 / 250000000000) (80048573379 / 500000000000) x115 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx114
  let x116 : ℝ := -x115
  have hx116 : Bounds (-80048573379 / 500000000000) (-40024286383 / 250000000000) x116 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx115
  let x117 : ℝ := x99+x116
  have hx117 : Bounds (266525016621 / 500000000000) (133262508867 / 250000000000) x117 := by
    apply bounds_add hx99 hx116 <;> norm_num
  let x118 : ℝ := x99-x115
  have hx118 : Bounds (266525016621 / 500000000000) (133262508867 / 250000000000) x118 := by
    exact hx117
  let x119 : ℝ := biasE (68773 / 125000)
  have hx119 : Bounds (266525016621 / 500000000000) (133262508867 / 250000000000) x119 := by
    simpa +zetaDelta only [biasE, div_one] using hx118
  let x120 : ℝ := Real.log (2 / 1)
  have hx120 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x120 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x121 : ℝ := (1 / 1)+(276023 / 500000)
  have hx121 : Bounds (776023 / 500000) (776023 / 500000) x121 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((276023 / 500000) : ℝ)) <;> norm_num
  let x122 : ℝ := (1 / 1)+(276023 / 500000)
  have hx122 : Bounds (776023 / 500000) (776023 / 500000) x122 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((276023 / 500000) : ℝ)) <;> norm_num
  let x123 : ℝ := Real.log x122
  have hx123 : Bounds (21978703 / 50000000) (439574061 / 1000000000) x123 := by
    exact bounds_log hx122 (by norm_num) (by simpa only [div_one] using reflection_log_11.1) (by simpa only [div_one] using reflection_log_11.2)
  let x124 : ℝ := x121*x123
  have hx124 : Bounds (341119580763 / 500000000000) (682239163079 / 1000000000000) x124 := by
    apply bounds_mul hx121 hx123 <;> norm_num
  let x125 : ℝ := -(276023 / 500000)
  have hx125 : Bounds (-276023 / 500000) (-276023 / 500000) x125 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((276023 / 500000) : ℝ))
  let x126 : ℝ := (1 / 1)+x125
  have hx126 : Bounds (223977 / 500000) (223977 / 500000) x126 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx125 <;> norm_num
  let x127 : ℝ := (1 / 1)-(276023 / 500000)
  have hx127 : Bounds (223977 / 500000) (223977 / 500000) x127 := by
    exact hx126
  let x128 : ℝ := -(276023 / 500000)
  have hx128 : Bounds (-276023 / 500000) (-276023 / 500000) x128 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((276023 / 500000) : ℝ))
  let x129 : ℝ := (1 / 1)+x128
  have hx129 : Bounds (223977 / 500000) (223977 / 500000) x129 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx128 <;> norm_num
  let x130 : ℝ := (1 / 1)-(276023 / 500000)
  have hx130 : Bounds (223977 / 500000) (223977 / 500000) x130 := by
    exact hx129
  let x131 : ℝ := Real.log x130
  have hx131 : Bounds (-803064731 / 1000000000) (-803064729 / 1000000000) x131 := by
    exact bounds_log hx130 (by norm_num) (by simpa only [div_one] using reflection_log_12.1) (by simpa only [div_one] using reflection_log_12.2)
  let x132 : ℝ := x127*x131
  have hx132 : Bounds (-359736058511 / 1000000000000) (-179868028807 / 500000000000) x132 := by
    apply bounds_mul hx127 hx131 <;> norm_num
  let x133 : ℝ := x124+x132
  have hx133 : Bounds (64500620603 / 200000000000) (64500621093 / 200000000000) x133 := by
    apply bounds_add hx124 hx132 <;> norm_num
  let x134 : ℝ := (2 / 1)⁻¹
  have hx134 : Bounds (1 / 2) (1 / 2) x134 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x135 : ℝ := x133*x134
  have hx135 : Bounds (161251551507 / 1000000000000) (161251552733 / 1000000000000) x135 := by
    apply bounds_mul hx133 hx134 <;> norm_num
  let x136 : ℝ := x133/(2 / 1)
  have hx136 : Bounds (161251551507 / 1000000000000) (161251552733 / 1000000000000) x136 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx135
  let x137 : ℝ := -x136
  have hx137 : Bounds (-161251552733 / 1000000000000) (-161251551507 / 1000000000000) x137 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx136
  let x138 : ℝ := x120+x137
  have hx138 : Bounds (531895627267 / 1000000000000) (531895629493 / 1000000000000) x138 := by
    apply bounds_add hx120 hx137 <;> norm_num
  let x139 : ℝ := x120-x136
  have hx139 : Bounds (531895627267 / 1000000000000) (531895629493 / 1000000000000) x139 := by
    exact hx138
  let x140 : ℝ := biasE (276023 / 500000)
  have hx140 : Bounds (531895627267 / 1000000000000) (531895629493 / 1000000000000) x140 := by
    simpa +zetaDelta only [biasE, div_one] using hx139
  let y : ℝ := 1 - 2 * entropyInverse ((1 + H (2*m - 1/2))/2)
  have hLh' : Real.log 2 * ((1 + H (2*m - 1/2))/2) = x98 := by
    simpa +zetaDelta only [div_one] using hLh
  have hy : Bounds (68773 / 125000) (276023 / 500000) y := by
    apply entropyInverseBias_bracket
    · exact div_nonneg (add_nonneg zero_le_one
        (H_nonneg (by linarith [hm.1]) (by linarith [hm.2]))) two_pos.le
    · linarith [H_le_one (2*m-1/2)]
    · norm_num
    · norm_num
    · norm_num
    · have h1 : biasE (276023 / 500000) ≤ (531895629493 / 1000000000000) := hx140.2
      have h2 : (265947851139 / 500000000000) ≤ x98 := hx98.1
      linarith [hLh']
    · have h1 : x98 ≤ (133262402523 / 250000000000) := hx98.2
      have h2 : (266525016621 / 500000000000) ≤ biasE (68773 / 125000) := hx119.1
      linarith [hLh']
  let x141 : ℝ := x3⁻¹
  have hx141 : Bounds (2644628099173 / 1000000000000) (2652849740933 / 1000000000000) x141 := by
    apply bounds_inv hx3 <;> norm_num
  let x142 : ℝ := x98*x141
  have hx142 : Bounds (1406666320073 / 1000000000000) (1414100520037 / 1000000000000) x142 := by
    apply bounds_mul hx98 hx141 <;> norm_num
  let x143 : ℝ := x98/x3
  have hx143 : Bounds (1406666320073 / 1000000000000) (1414100520037 / 1000000000000) x143 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx142
  let x144 : ℝ := Real.log (2 / 1)
  have hx144 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x144 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x145 : ℝ := (1 / 1)+(424413 / 1000000)
  have hx145 : Bounds (1424413 / 1000000) (1424413 / 1000000) x145 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((424413 / 1000000) : ℝ)) <;> norm_num
  let x146 : ℝ := (1 / 1)+(424413 / 1000000)
  have hx146 : Bounds (1424413 / 1000000) (1424413 / 1000000) x146 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((424413 / 1000000) : ℝ)) <;> norm_num
  let x147 : ℝ := Real.log x146
  have hx147 : Bounds (353759799 / 1000000000) (1768799 / 5000000) x147 := by
    exact bounds_log hx146 (by norm_num) (by simpa only [div_one] using reflection_log_13.1) (by simpa only [div_one] using reflection_log_13.2)
  let x148 : ℝ := x145*x147
  have hx148 : Bounds (125975014143 / 250000000000) (251950028999 / 500000000000) x148 := by
    apply bounds_mul hx145 hx147 <;> norm_num
  let x149 : ℝ := -(424413 / 1000000)
  have hx149 : Bounds (-424413 / 1000000) (-424413 / 1000000) x149 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((424413 / 1000000) : ℝ))
  let x150 : ℝ := (1 / 1)+x149
  have hx150 : Bounds (575587 / 1000000) (575587 / 1000000) x150 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx149 <;> norm_num
  let x151 : ℝ := (1 / 1)-(424413 / 1000000)
  have hx151 : Bounds (575587 / 1000000) (575587 / 1000000) x151 := by
    exact hx150
  let x152 : ℝ := -(424413 / 1000000)
  have hx152 : Bounds (-424413 / 1000000) (-424413 / 1000000) x152 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((424413 / 1000000) : ℝ))
  let x153 : ℝ := (1 / 1)+x152
  have hx153 : Bounds (575587 / 1000000) (575587 / 1000000) x153 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx152 <;> norm_num
  let x154 : ℝ := (1 / 1)-(424413 / 1000000)
  have hx154 : Bounds (575587 / 1000000) (575587 / 1000000) x154 := by
    exact hx153
  let x155 : ℝ := Real.log x154
  have hx155 : Bounds (-55236489 / 100000000) (-552364889 / 1000000000) x155 := by
    exact bounds_log hx154 (by norm_num) (by simpa only [div_one] using reflection_log_14.1) (by simpa only [div_one] using reflection_log_14.2)
  let x156 : ℝ := x151*x155
  have hx156 : Bounds (-317934049941 / 1000000000000) (-79483512341 / 250000000000) x156 := by
    apply bounds_mul hx151 hx155 <;> norm_num
  let x157 : ℝ := x148+x156
  have hx157 : Bounds (185966006631 / 1000000000000) (92983004317 / 500000000000) x157 := by
    apply bounds_add hx148 hx156 <;> norm_num
  let x158 : ℝ := (2 / 1)⁻¹
  have hx158 : Bounds (1 / 2) (1 / 2) x158 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x159 : ℝ := x157*x158
  have hx159 : Bounds (18596600663 / 200000000000) (92983004317 / 1000000000000) x159 := by
    apply bounds_mul hx157 hx158 <;> norm_num
  let x160 : ℝ := x157/(2 / 1)
  have hx160 : Bounds (18596600663 / 200000000000) (92983004317 / 1000000000000) x160 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx159
  let x161 : ℝ := -x160
  have hx161 : Bounds (-92983004317 / 1000000000000) (-18596600663 / 200000000000) x161 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx160
  let x162 : ℝ := x144+x161
  have hx162 : Bounds (600164175683 / 1000000000000) (120032835537 / 200000000000) x162 := by
    apply bounds_add hx144 hx161 <;> norm_num
  let x163 : ℝ := x144-x160
  have hx163 : Bounds (600164175683 / 1000000000000) (120032835537 / 200000000000) x163 := by
    exact hx162
  let x164 : ℝ := biasE (424413 / 1000000)
  have hx164 : Bounds (600164175683 / 1000000000000) (120032835537 / 200000000000) x164 := by
    simpa +zetaDelta only [biasE, div_one] using hx163
  let x165 : ℝ := Real.log (2 / 1)
  have hx165 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x165 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x166 : ℝ := (1 / 1)+(42611 / 100000)
  have hx166 : Bounds (142611 / 100000) (142611 / 100000) x166 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((42611 / 100000) : ℝ)) <;> norm_num
  let x167 : ℝ := (1 / 1)+(42611 / 100000)
  have hx167 : Bounds (142611 / 100000) (142611 / 100000) x167 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((42611 / 100000) : ℝ)) <;> norm_num
  let x168 : ℝ := Real.log x167
  have hx168 : Bounds (354950457 / 1000000000) (177475229 / 500000000) x168 := by
    exact bounds_log hx167 (by norm_num) (by simpa only [div_one] using reflection_log_15.1) (by simpa only [div_one] using reflection_log_15.2)
  let x169 : ℝ := x166*x168
  have hx169 : Bounds (63274799529 / 125000000000) (506198397659 / 1000000000000) x169 := by
    apply bounds_mul hx166 hx168 <;> norm_num
  let x170 : ℝ := -(42611 / 100000)
  have hx170 : Bounds (-42611 / 100000) (-42611 / 100000) x170 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((42611 / 100000) : ℝ))
  let x171 : ℝ := (1 / 1)+x170
  have hx171 : Bounds (57389 / 100000) (57389 / 100000) x171 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx170 <;> norm_num
  let x172 : ℝ := (1 / 1)-(42611 / 100000)
  have hx172 : Bounds (57389 / 100000) (57389 / 100000) x172 := by
    exact hx171
  let x173 : ℝ := -(42611 / 100000)
  have hx173 : Bounds (-42611 / 100000) (-42611 / 100000) x173 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((42611 / 100000) : ℝ))
  let x174 : ℝ := (1 / 1)+x173
  have hx174 : Bounds (57389 / 100000) (57389 / 100000) x174 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx173 <;> norm_num
  let x175 : ℝ := (1 / 1)-(42611 / 100000)
  have hx175 : Bounds (57389 / 100000) (57389 / 100000) x175 := by
    exact hx174
  let x176 : ℝ := Real.log x175
  have hx176 : Bounds (-555317539 / 1000000000) (-277658769 / 500000000) x176 := by
    exact bounds_log hx175 (by norm_num) (by simpa only [div_one] using reflection_log_16.1) (by simpa only [div_one] using reflection_log_16.2)
  let x177 : ℝ := x172*x176
  have hx177 : Bounds (-318691182457 / 1000000000000) (-159345590941 / 500000000000) x177 := by
    apply bounds_mul hx172 hx176 <;> norm_num
  let x178 : ℝ := x169+x177
  have hx178 : Bounds (7500288551 / 40000000000) (187507215777 / 1000000000000) x178 := by
    apply bounds_add hx169 hx177 <;> norm_num
  let x179 : ℝ := (2 / 1)⁻¹
  have hx179 : Bounds (1 / 2) (1 / 2) x179 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x180 : ℝ := x178*x179
  have hx180 : Bounds (93753606887 / 1000000000000) (93753607889 / 1000000000000) x180 := by
    apply bounds_mul hx178 hx179 <;> norm_num
  let x181 : ℝ := x178/(2 / 1)
  have hx181 : Bounds (93753606887 / 1000000000000) (93753607889 / 1000000000000) x181 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx180
  let x182 : ℝ := -x181
  have hx182 : Bounds (-93753607889 / 1000000000000) (-93753606887 / 1000000000000) x182 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx181
  let x183 : ℝ := x165+x182
  have hx183 : Bounds (599393572111 / 1000000000000) (599393574113 / 1000000000000) x183 := by
    apply bounds_add hx165 hx182 <;> norm_num
  let x184 : ℝ := x165-x181
  have hx184 : Bounds (599393572111 / 1000000000000) (599393574113 / 1000000000000) x184 := by
    exact hx183
  let x185 : ℝ := biasE (42611 / 100000)
  have hx185 : Bounds (599393572111 / 1000000000000) (599393574113 / 1000000000000) x185 := by
    simpa +zetaDelta only [biasE, div_one] using hx184
  let x186 : ℝ := x143*(424413 / 1000000)
  have hx186 : Bounds (597007472901 / 1000000000000) (600162644011 / 1000000000000) x186 := by
    apply bounds_mul hx143 (bounds_const ((424413 / 1000000) : ℝ)) <;> norm_num
  let x187 : ℝ := x143*(42611 / 100000)
  have hx187 : Bounds (299697292823 / 500000000000) (602562372593 / 1000000000000) x187 := by
    apply bounds_mul hx143 (bounds_const ((42611 / 100000) : ℝ)) <;> norm_num
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
  have hc : Bounds (424413 / 1000000) (42611 / 100000) c := by
    apply contact_bracket hc0 hcMem.2.le (by norm_num) (by norm_num) (by norm_num)
      (show 0 < x143 by linarith [hx143.1]) hcEq
    · have h1 : x143 * (424413 / 1000000) ≤ (600162644011 / 1000000000000) := hx186.2
      have h2 : (600164175683 / 1000000000000) ≤ biasE (424413 / 1000000) := hx164.1
      linarith
    · have h1 : biasE (42611 / 100000) ≤ (599393574113 / 1000000000000) := hx185.2
      have h2 : (299697292823 / 500000000000) ≤ x143 * (42611 / 100000) := hx187.1
      linarith
  let x188 : ℝ := (1 / 1)+y
  have hx188 : Bounds (193773 / 125000) (776023 / 500000) x188 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hy <;> norm_num
  let x189 : ℝ := -y
  have hx189 : Bounds (-276023 / 500000) (-68773 / 125000) x189 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hy
  let x190 : ℝ := (1 / 1)+x189
  have hx190 : Bounds (223977 / 500000) (56227 / 125000) x190 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx189 <;> norm_num
  let x191 : ℝ := (1 / 1)-y
  have hx191 : Bounds (223977 / 500000) (56227 / 125000) x191 := by
    exact hx190
  let x192 : ℝ := x191⁻¹
  have hx192 : Bounds (2223131235883 / 1000000000000) (2232372073919 / 1000000000000) x192 := by
    apply bounds_inv hx191 <;> norm_num
  let x193 : ℝ := x188*x192
  have hx193 : Bounds (1723131235883 / 500000000000) (1732372073919 / 500000000000) x193 := by
    apply bounds_mul hx188 hx192 <;> norm_num
  let x194 : ℝ := x188/x191
  have hx194 : Bounds (1723131235883 / 500000000000) (1732372073919 / 500000000000) x194 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx193
  let x195 : ℝ := Real.log x194
  have hx195 : Bounds (1237290301 / 1000000000) (155329849 / 125000000) x195 := by
    exact bounds_log hx194 (by norm_num) (by simpa only [div_one] using reflection_log_17.1) (by simpa only [div_one] using reflection_log_18.2)
  let x196 : ℝ := (2 / 1)⁻¹
  have hx196 : Bounds (1 / 2) (1 / 2) x196 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x197 : ℝ := x195*x196
  have hx197 : Bounds (1237290301 / 2000000000) (155329849 / 250000000) x197 := by
    apply bounds_mul hx195 hx196 <;> norm_num
  let x198 : ℝ := x195/(2 / 1)
  have hx198 : Bounds (1237290301 / 2000000000) (155329849 / 250000000) x198 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx197
  let x199 : ℝ := (1 / 1)+c
  have hx199 : Bounds (1424413 / 1000000) (142611 / 100000) x199 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hc <;> norm_num
  let x200 : ℝ := -c
  have hx200 : Bounds (-42611 / 100000) (-424413 / 1000000) x200 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hc
  let x201 : ℝ := (1 / 1)+x200
  have hx201 : Bounds (57389 / 100000) (575587 / 1000000) x201 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx200 <;> norm_num
  let x202 : ℝ := (1 / 1)-c
  have hx202 : Bounds (57389 / 100000) (575587 / 1000000) x202 := by
    exact hx201
  let x203 : ℝ := x202⁻¹
  have hx203 : Bounds (1737356820081 / 1000000000000) (1742494206207 / 1000000000000) x203 := by
    apply bounds_inv hx202 <;> norm_num
  let x204 : ℝ := x199*x203
  have hx204 : Bounds (1237356820081 / 500000000000) (1242494206207 / 500000000000) x204 := by
    apply bounds_mul hx199 hx203 <;> norm_num
  let x205 : ℝ := x199/x202
  have hx205 : Bounds (1237356820081 / 500000000000) (1242494206207 / 500000000000) x205 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx204
  let x206 : ℝ := Real.log x205
  have hx206 : Bounds (906124687 / 1000000000) (910267997 / 1000000000) x206 := by
    exact bounds_log hx205 (by norm_num) (by simpa only [div_one] using reflection_log_19.1) (by simpa only [div_one] using reflection_log_20.2)
  let x207 : ℝ := (2 / 1)⁻¹
  have hx207 : Bounds (1 / 2) (1 / 2) x207 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x208 : ℝ := x206*x207
  have hx208 : Bounds (906124687 / 2000000000) (910267997 / 2000000000) x208 := by
    apply bounds_mul hx206 hx207 <;> norm_num
  let x209 : ℝ := x206/(2 / 1)
  have hx209 : Bounds (906124687 / 2000000000) (910267997 / 2000000000) x209 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx208
  let x210 : ℝ := (2 / 1)*x50
  have hx210 : Bounds (619848722107 / 500000000000) (124062835429 / 100000000000) x210 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx50 <;> norm_num
  let x211 : ℝ := (2 / 1)*x98
  have hx211 : Bounds (265947851139 / 250000000000) (133262402523 / 125000000000) x211 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx98 <;> norm_num
  let x212 : ℝ := -x211
  have hx212 : Bounds (-133262402523 / 125000000000) (-265947851139 / 250000000000) x212 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx211
  let x213 : ℝ := x210+x212
  have hx213 : Bounds (17359822403 / 100000000000) (88418474867 / 500000000000) x213 := by
    apply bounds_add hx210 hx212 <;> norm_num
  let x214 : ℝ := x210-x211
  have hx214 : Bounds (17359822403 / 100000000000) (88418474867 / 500000000000) x214 := by
    exact hx213
  let x215 : ℝ := y*x198
  have hx215 : Bounds (170184331741 / 500000000000) (68599377457 / 200000000000) x215 := by
    apply bounds_mul hy hx198 <;> norm_num
  let x216 : ℝ := -x215
  have hx216 : Bounds (-68599377457 / 200000000000) (-170184331741 / 500000000000) x216 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx215
  let x217 : ℝ := x214+x216
  have hx217 : Bounds (-33879732651 / 200000000000) (-40882928437 / 250000000000) x217 := by
    apply bounds_add hx214 hx216 <;> norm_num
  let x218 : ℝ := x214-x215
  have hx218 : Bounds (-33879732651 / 200000000000) (-40882928437 / 250000000000) x218 := by
    exact hx217
  let x219 : ℝ := x3*x209
  have hx219 : Bounds (85391633101 / 500000000000) (172097543183 / 1000000000000) x219 := by
    apply bounds_mul hx3 hx209 <;> norm_num
  let x220 : ℝ := x218+x219
  have hx220 : Bounds (1384602947 / 1000000000000) (1713165887 / 200000000000) x220 := by
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

theorem acceptedCertificate : DoubleCapBiasCellCertificate (199 / 640) (319 / 1024) (fun m => (1 + H (2*m - 1/2))/2) where
  domain := by norm_num
  sound m hmLo hmHi := by
    exact cell_bias_nonneg m ⟨hmLo, hmHi⟩

theorem accepted_cell :
    ∀ m, (199 / 640) ≤ m → m ≤ (319 / 1024) → 0 ≤ doubleCapHighResidual m := by
  intro m hmLo hmHi
  unfold doubleCapHighResidual
  apply doubleCapEndpointResidual_nonneg_of_biasCell acceptedCertificate hmLo hmHi
  exact div_pos (by linarith [H_nonneg (by linarith : 0 ≤ 2*m-1/2) (by linarith : 2*m-1/2 ≤ 1)]) two_pos

#print axioms cell_bias_nonneg
#print axioms accepted_cell

end GeneralCK.Certificates.DoubleCapMiddle.Cell0115

end


