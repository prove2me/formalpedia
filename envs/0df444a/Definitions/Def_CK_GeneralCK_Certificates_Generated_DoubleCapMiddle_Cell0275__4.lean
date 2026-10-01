-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0275__4
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0275__4
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T11:12:04.849838+00:00
-- url     : https://prove2.me/theorems/17efad91-a28c-4139-800a-dde498f27acc
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0275 (+3 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0276, GeneralCK.Certificates.Gener…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0275 (+3 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0276, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0277, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0278)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0275 (+3 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0276, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0277, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0278)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0275 (+3 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0276, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0277, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0278) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0275 (+3 modules: GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0276, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0277, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0278).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0274Logs__7

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0275 =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0275
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Reflection
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem cell_bias_nonneg (m : ℝ) (hm : Bounds (3787 / 10240) (379 / 1024) m) :
    let h := (1 + H (2*m - 1/2))/2
    let x := 1-2*m
    let y := 1-2*entropyInverse h
    let c := regularContact (x/(Real.log 2*h))
    0 ≤ 2*(biasE x-Real.log 2*h)-y*SmallMean.A y+x*SmallMean.A c := by
  have hEq : biasE (2-4*m) = Real.log 2 * H (2*m-1/2) := by
    have hmstrict : 1/4 < m := by
      have hlo : (1/4 : ℝ) < (3787 / 10240) := by norm_num
      exact lt_of_lt_of_le hlo hm.1
    rw [show 2-4*m = 1-2*(2*m-1/2) by ring,
      GeneralCK.Correction.Natural.biasE_probability (by linarith [hmstrict]) (by linarith [hm.2]),
      GeneralCK.Certificates.Mixed.hn_eq_H_mul_log]
    ring
  have hLh : Real.log 2 * ((1 + H (2*m - 1/2))/2) = (Real.log 2 + biasE (2-4*m))/2 := by
    rw [hEq]
    ring
  let x0 : ℝ := (2 / 1)*m
  have hx0 : Bounds (3787 / 5120) (379 / 512) x0 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hm <;> norm_num
  let x1 : ℝ := -x0
  have hx1 : Bounds (-379 / 512) (-3787 / 5120) x1 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx0
  let x2 : ℝ := (1 / 1)+x1
  have hx2 : Bounds (133 / 512) (1333 / 5120) x2 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx1 <;> norm_num
  let x3 : ℝ := (1 / 1)-x0
  have hx3 : Bounds (133 / 512) (1333 / 5120) x3 := by
    exact hx2
  let x4 : ℝ := (4 / 1)*m
  have hx4 : Bounds (3787 / 2560) (379 / 256) x4 := by
    apply bounds_mul (bounds_const ((4 / 1) : ℝ)) hm <;> norm_num
  let x5 : ℝ := -x4
  have hx5 : Bounds (-379 / 256) (-3787 / 2560) x5 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx4
  let x6 : ℝ := (2 / 1)+x5
  have hx6 : Bounds (133 / 256) (1333 / 2560) x6 := by
    apply bounds_add (bounds_const ((2 / 1) : ℝ)) hx5 <;> norm_num
  let x7 : ℝ := (2 / 1)-x4
  have hx7 : Bounds (133 / 256) (1333 / 2560) x7 := by
    exact hx6
  let x8 : ℝ := Real.log (2 / 1)
  have hx8 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x8 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x9 : ℝ := (1 / 1)+(1333 / 5120)
  have hx9 : Bounds (6453 / 5120) (6453 / 5120) x9 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1333 / 5120) : ℝ)) <;> norm_num
  let x10 : ℝ := (1 / 1)+(1333 / 5120)
  have hx10 : Bounds (6453 / 5120) (6453 / 5120) x10 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1333 / 5120) : ℝ)) <;> norm_num
  let x11 : ℝ := Real.log x10
  have hx11 : Bounds (231390699 / 1000000000) (2313907 / 10000000) x11 := by
    exact bounds_log hx10 (by norm_num) (by simpa only [div_one] using reflection_log_1.1) (by simpa only [div_one] using reflection_log_1.2)
  let x12 : ℝ := x9*x11
  have hx12 : Bounds (36454203629 / 125000000000) (291633630293 / 1000000000000) x12 := by
    apply bounds_mul hx9 hx11 <;> norm_num
  let x13 : ℝ := -(1333 / 5120)
  have hx13 : Bounds (-1333 / 5120) (-1333 / 5120) x13 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1333 / 5120) : ℝ))
  let x14 : ℝ := (1 / 1)+x13
  have hx14 : Bounds (3787 / 5120) (3787 / 5120) x14 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx13 <;> norm_num
  let x15 : ℝ := (1 / 1)-(1333 / 5120)
  have hx15 : Bounds (3787 / 5120) (3787 / 5120) x15 := by
    exact hx14
  let x16 : ℝ := -(1333 / 5120)
  have hx16 : Bounds (-1333 / 5120) (-1333 / 5120) x16 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1333 / 5120) : ℝ))
  let x17 : ℝ := (1 / 1)+x16
  have hx17 : Bounds (3787 / 5120) (3787 / 5120) x17 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx16 <;> norm_num
  let x18 : ℝ := (1 / 1)-(1333 / 5120)
  have hx18 : Bounds (3787 / 5120) (3787 / 5120) x18 := by
    exact hx17
  let x19 : ℝ := Real.log x18
  have hx19 : Bounds (-301580291 / 1000000000) (-30158029 / 100000000) x19 := by
    exact bounds_log hx18 (by norm_num) (by simpa only [div_one] using reflection_log_2.1) (by simpa only [div_one] using reflection_log_2.2)
  let x20 : ℝ := x15*x19
  have hx20 : Bounds (-223063391019 / 1000000000000) (-223063390279 / 1000000000000) x20 := by
    apply bounds_mul hx15 hx19 <;> norm_num
  let x21 : ℝ := x12+x20
  have hx21 : Bounds (68570238013 / 1000000000000) (34285120007 / 500000000000) x21 := by
    apply bounds_add hx12 hx20 <;> norm_num
  let x22 : ℝ := (2 / 1)⁻¹
  have hx22 : Bounds (1 / 2) (1 / 2) x22 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x23 : ℝ := x21*x22
  have hx23 : Bounds (17142559503 / 500000000000) (34285120007 / 1000000000000) x23 := by
    apply bounds_mul hx21 hx22 <;> norm_num
  let x24 : ℝ := x21/(2 / 1)
  have hx24 : Bounds (17142559503 / 500000000000) (34285120007 / 1000000000000) x24 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx23
  let x25 : ℝ := -x24
  have hx25 : Bounds (-34285120007 / 1000000000000) (-17142559503 / 500000000000) x25 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx24
  let x26 : ℝ := x8+x25
  have hx26 : Bounds (658862059993 / 1000000000000) (329431030997 / 500000000000) x26 := by
    apply bounds_add hx8 hx25 <;> norm_num
  let x27 : ℝ := x8-x24
  have hx27 : Bounds (658862059993 / 1000000000000) (329431030997 / 500000000000) x27 := by
    exact hx26
  let x28 : ℝ := biasE (1333 / 5120)
  have hx28 : Bounds (658862059993 / 1000000000000) (329431030997 / 500000000000) x28 := by
    simpa +zetaDelta only [biasE, div_one] using hx27
  let x29 : ℝ := Real.log (2 / 1)
  have hx29 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x29 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x30 : ℝ := (1 / 1)+(133 / 512)
  have hx30 : Bounds (645 / 512) (645 / 512) x30 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((133 / 512) : ℝ)) <;> norm_num
  let x31 : ℝ := (1 / 1)+(133 / 512)
  have hx31 : Bounds (645 / 512) (645 / 512) x31 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((133 / 512) : ℝ)) <;> norm_num
  let x32 : ℝ := Real.log x31
  have hx32 : Bounds (230925691 / 1000000000) (57731423 / 250000000) x32 := by
    exact bounds_log hx31 (by norm_num) (by simpa only [div_one] using reflection_log_3.1) (by simpa only [div_one] using reflection_log_3.2)
  let x33 : ℝ := x30*x32
  have hx33 : Bounds (290912247451 / 1000000000000) (290912248711 / 1000000000000) x33 := by
    apply bounds_mul hx30 hx32 <;> norm_num
  let x34 : ℝ := -(133 / 512)
  have hx34 : Bounds (-133 / 512) (-133 / 512) x34 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((133 / 512) : ℝ))
  let x35 : ℝ := (1 / 1)+x34
  have hx35 : Bounds (379 / 512) (379 / 512) x35 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx34 <;> norm_num
  let x36 : ℝ := (1 / 1)-(133 / 512)
  have hx36 : Bounds (379 / 512) (379 / 512) x36 := by
    exact hx35
  let x37 : ℝ := -(133 / 512)
  have hx37 : Bounds (-133 / 512) (-133 / 512) x37 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((133 / 512) : ℝ))
  let x38 : ℝ := (1 / 1)+x37
  have hx38 : Bounds (379 / 512) (379 / 512) x38 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx37 <;> norm_num
  let x39 : ℝ := (1 / 1)-(133 / 512)
  have hx39 : Bounds (379 / 512) (379 / 512) x39 := by
    exact hx38
  let x40 : ℝ := Real.log x39
  have hx40 : Bounds (-15039421 / 50000000) (-300788419 / 1000000000) x40 := by
    exact bounds_log hx39 (by norm_num) (by simpa only [div_one] using reflection_log_4.1) (by simpa only [div_one] using reflection_log_4.2)
  let x41 : ℝ := x36*x40
  have hx41 : Bounds (-111326964043 / 500000000000) (-44530785469 / 200000000000) x41 := by
    apply bounds_mul hx36 hx40 <;> norm_num
  let x42 : ℝ := x33+x41
  have hx42 : Bounds (13651663873 / 200000000000) (34129160683 / 500000000000) x42 := by
    apply bounds_add hx33 hx41 <;> norm_num
  let x43 : ℝ := (2 / 1)⁻¹
  have hx43 : Bounds (1 / 2) (1 / 2) x43 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x44 : ℝ := x42*x43
  have hx44 : Bounds (17064579841 / 500000000000) (34129160683 / 1000000000000) x44 := by
    apply bounds_mul hx42 hx43 <;> norm_num
  let x45 : ℝ := x42/(2 / 1)
  have hx45 : Bounds (17064579841 / 500000000000) (34129160683 / 1000000000000) x45 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx44
  let x46 : ℝ := -x45
  have hx46 : Bounds (-34129160683 / 1000000000000) (-17064579841 / 500000000000) x46 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx45
  let x47 : ℝ := x29+x46
  have hx47 : Bounds (659018019317 / 1000000000000) (329509010659 / 500000000000) x47 := by
    apply bounds_add hx29 hx46 <;> norm_num
  let x48 : ℝ := x29-x45
  have hx48 : Bounds (659018019317 / 1000000000000) (329509010659 / 500000000000) x48 := by
    exact hx47
  let x49 : ℝ := biasE (133 / 512)
  have hx49 : Bounds (659018019317 / 1000000000000) (329509010659 / 500000000000) x49 := by
    simpa +zetaDelta only [biasE, div_one] using hx48
  let x50 : ℝ := biasE x3
  have hx50 : Bounds (658862059993 / 1000000000000) (329509010659 / 500000000000) x50 := by
    exact bounds_biasE hx3 (by norm_num) (by norm_num) hx28.1 hx49.2
  let x51 : ℝ := Real.log (2 / 1)
  have hx51 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x51 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x52 : ℝ := (1 / 1)+(1333 / 2560)
  have hx52 : Bounds (3893 / 2560) (3893 / 2560) x52 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1333 / 2560) : ℝ)) <;> norm_num
  let x53 : ℝ := (1 / 1)+(1333 / 2560)
  have hx53 : Bounds (3893 / 2560) (3893 / 2560) x53 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1333 / 2560) : ℝ)) <;> norm_num
  let x54 : ℝ := Real.log x53
  have hx54 : Bounds (41917281 / 100000000) (419172811 / 1000000000) x54 := by
    exact bounds_log hx53 (by norm_num) (by simpa only [div_one] using reflection_log_5.1) (by simpa only [div_one] using reflection_log_5.2)
  let x55 : ℝ := x52*x54
  have hx55 : Bounds (318718701041 / 500000000000) (637437403603 / 1000000000000) x55 := by
    apply bounds_mul hx52 hx54 <;> norm_num
  let x56 : ℝ := -(1333 / 2560)
  have hx56 : Bounds (-1333 / 2560) (-1333 / 2560) x56 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1333 / 2560) : ℝ))
  let x57 : ℝ := (1 / 1)+x56
  have hx57 : Bounds (1227 / 2560) (1227 / 2560) x57 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx56 <;> norm_num
  let x58 : ℝ := (1 / 1)-(1333 / 2560)
  have hx58 : Bounds (1227 / 2560) (1227 / 2560) x58 := by
    exact hx57
  let x59 : ℝ := -(1333 / 2560)
  have hx59 : Bounds (-1333 / 2560) (-1333 / 2560) x59 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1333 / 2560) : ℝ))
  let x60 : ℝ := (1 / 1)+x59
  have hx60 : Bounds (1227 / 2560) (1227 / 2560) x60 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx59 <;> norm_num
  let x61 : ℝ := (1 / 1)-(1333 / 2560)
  have hx61 : Bounds (1227 / 2560) (1227 / 2560) x61 := by
    exact hx60
  let x62 : ℝ := Real.log x61
  have hx62 : Bounds (-367717547 / 500000000) (-183858773 / 250000000) x62 := by
    exact bounds_log hx61 (by norm_num) (by simpa only [div_one] using reflection_log_6.1) (by simpa only [div_one] using reflection_log_6.2)
  let x63 : ℝ := x58*x62
  have hx63 : Bounds (-4406146779 / 12500000000) (-4406146767 / 12500000000) x63 := by
    apply bounds_mul hx58 hx62 <;> norm_num
  let x64 : ℝ := x55+x63
  have hx64 : Bounds (142472829881 / 500000000000) (284945662243 / 1000000000000) x64 := by
    apply bounds_add hx55 hx63 <;> norm_num
  let x65 : ℝ := (2 / 1)⁻¹
  have hx65 : Bounds (1 / 2) (1 / 2) x65 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x66 : ℝ := x64*x65
  have hx66 : Bounds (142472829881 / 1000000000000) (71236415561 / 500000000000) x66 := by
    apply bounds_mul hx64 hx65 <;> norm_num
  let x67 : ℝ := x64/(2 / 1)
  have hx67 : Bounds (142472829881 / 1000000000000) (71236415561 / 500000000000) x67 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx66
  let x68 : ℝ := -x67
  have hx68 : Bounds (-71236415561 / 500000000000) (-142472829881 / 1000000000000) x68 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx67
  let x69 : ℝ := x51+x68
  have hx69 : Bounds (275337174439 / 500000000000) (550674351119 / 1000000000000) x69 := by
    apply bounds_add hx51 hx68 <;> norm_num
  let x70 : ℝ := x51-x67
  have hx70 : Bounds (275337174439 / 500000000000) (550674351119 / 1000000000000) x70 := by
    exact hx69
  let x71 : ℝ := biasE (1333 / 2560)
  have hx71 : Bounds (275337174439 / 500000000000) (550674351119 / 1000000000000) x71 := by
    simpa +zetaDelta only [biasE, div_one] using hx70
  let x72 : ℝ := Real.log (2 / 1)
  have hx72 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x72 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x73 : ℝ := (1 / 1)+(133 / 256)
  have hx73 : Bounds (389 / 256) (389 / 256) x73 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((133 / 256) : ℝ)) <;> norm_num
  let x74 : ℝ := (1 / 1)+(133 / 256)
  have hx74 : Bounds (389 / 256) (389 / 256) x74 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((133 / 256) : ℝ)) <;> norm_num
  let x75 : ℝ := Real.log x74
  have hx75 : Bounds (418401899 / 1000000000) (4184019 / 10000000) x75 := by
    exact bounds_log hx74 (by norm_num) (by simpa only [div_one] using reflection_log_7.1) (by simpa only [div_one] using reflection_log_7.2)
  let x76 : ℝ := x73*x75
  have hx76 : Bounds (635774760589 / 1000000000000) (63577476211 / 100000000000) x76 := by
    apply bounds_mul hx73 hx75 <;> norm_num
  let x77 : ℝ := -(133 / 256)
  have hx77 : Bounds (-133 / 256) (-133 / 256) x77 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((133 / 256) : ℝ))
  let x78 : ℝ := (1 / 1)+x77
  have hx78 : Bounds (123 / 256) (123 / 256) x78 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx77 <;> norm_num
  let x79 : ℝ := (1 / 1)-(133 / 256)
  have hx79 : Bounds (123 / 256) (123 / 256) x79 := by
    exact hx78
  let x80 : ℝ := -(133 / 256)
  have hx80 : Bounds (-133 / 256) (-133 / 256) x80 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((133 / 256) : ℝ))
  let x81 : ℝ := (1 / 1)+x80
  have hx81 : Bounds (123 / 256) (123 / 256) x81 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx80 <;> norm_num
  let x82 : ℝ := (1 / 1)-(133 / 256)
  have hx82 : Bounds (123 / 256) (123 / 256) x82 := by
    exact hx81
  let x83 : ℝ := Real.log x82
  have hx83 : Bounds (-73299309 / 100000000) (-11453017 / 15625000) x83 := by
    exact bounds_log hx82 (by norm_num) (by simpa only [div_one] using reflection_log_8.1) (by simpa only [div_one] using reflection_log_8.2)
  let x84 : ℝ := x79*x83
  have hx84 : Bounds (-352180273711 / 1000000000000) (-1408721091 / 4000000000) x84 := by
    apply bounds_mul hx79 hx83 <;> norm_num
  let x85 : ℝ := x76+x84
  have hx85 : Bounds (141797243439 / 500000000000) (3544931117 / 12500000000) x85 := by
    apply bounds_add hx76 hx84 <;> norm_num
  let x86 : ℝ := (2 / 1)⁻¹
  have hx86 : Bounds (1 / 2) (1 / 2) x86 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x87 : ℝ := x85*x86
  have hx87 : Bounds (141797243439 / 1000000000000) (3544931117 / 25000000000) x87 := by
    apply bounds_mul hx85 hx86 <;> norm_num
  let x88 : ℝ := x85/(2 / 1)
  have hx88 : Bounds (141797243439 / 1000000000000) (3544931117 / 25000000000) x88 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx87
  let x89 : ℝ := -x88
  have hx89 : Bounds (-3544931117 / 25000000000) (-141797243439 / 1000000000000) x89 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx88
  let x90 : ℝ := x72+x89
  have hx90 : Bounds (13783748383 / 25000000000) (551349937561 / 1000000000000) x90 := by
    apply bounds_add hx72 hx89 <;> norm_num
  let x91 : ℝ := x72-x88
  have hx91 : Bounds (13783748383 / 25000000000) (551349937561 / 1000000000000) x91 := by
    exact hx90
  let x92 : ℝ := biasE (133 / 256)
  have hx92 : Bounds (13783748383 / 25000000000) (551349937561 / 1000000000000) x92 := by
    simpa +zetaDelta only [biasE, div_one] using hx91
  let x93 : ℝ := biasE x7
  have hx93 : Bounds (275337174439 / 500000000000) (551349937561 / 1000000000000) x93 := by
    exact bounds_biasE hx7 (by norm_num) (by norm_num) hx71.1 hx92.2
  let x94 : ℝ := Real.log (2 / 1)
  have hx94 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x94 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x95 : ℝ := x94+x93
  have hx95 : Bounds (621910764439 / 500000000000) (1244497118561 / 1000000000000) x95 := by
    apply bounds_add hx94 hx93 <;> norm_num
  let x96 : ℝ := (2 / 1)⁻¹
  have hx96 : Bounds (1 / 2) (1 / 2) x96 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x97 : ℝ := x95*x96
  have hx97 : Bounds (621910764439 / 1000000000000) (622248559281 / 1000000000000) x97 := by
    apply bounds_mul hx95 hx96 <;> norm_num
  let x98 : ℝ := x95/(2 / 1)
  have hx98 : Bounds (621910764439 / 1000000000000) (622248559281 / 1000000000000) x98 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx97
  let x99 : ℝ := Real.log (2 / 1)
  have hx99 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x99 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x100 : ℝ := (1 / 1)+(372039 / 1000000)
  have hx100 : Bounds (1372039 / 1000000) (1372039 / 1000000) x100 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((372039 / 1000000) : ℝ)) <;> norm_num
  let x101 : ℝ := (1 / 1)+(372039 / 1000000)
  have hx101 : Bounds (1372039 / 1000000) (1372039 / 1000000) x101 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((372039 / 1000000) : ℝ)) <;> norm_num
  let x102 : ℝ := Real.log x101
  have hx102 : Bounds (158148977 / 500000000) (63259591 / 200000000) x102 := by
    exact bounds_log hx101 (by norm_num) (by simpa only [div_one] using reflection_log_9.1) (by simpa only [div_one] using reflection_log_9.2)
  let x103 : ℝ := x100*x102
  have hx103 : Bounds (108493282127 / 250000000000) (433973129881 / 1000000000000) x103 := by
    apply bounds_mul hx100 hx102 <;> norm_num
  let x104 : ℝ := -(372039 / 1000000)
  have hx104 : Bounds (-372039 / 1000000) (-372039 / 1000000) x104 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((372039 / 1000000) : ℝ))
  let x105 : ℝ := (1 / 1)+x104
  have hx105 : Bounds (627961 / 1000000) (627961 / 1000000) x105 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx104 <;> norm_num
  let x106 : ℝ := (1 / 1)-(372039 / 1000000)
  have hx106 : Bounds (627961 / 1000000) (627961 / 1000000) x106 := by
    exact hx105
  let x107 : ℝ := -(372039 / 1000000)
  have hx107 : Bounds (-372039 / 1000000) (-372039 / 1000000) x107 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((372039 / 1000000) : ℝ))
  let x108 : ℝ := (1 / 1)+x107
  have hx108 : Bounds (627961 / 1000000) (627961 / 1000000) x108 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx107 <;> norm_num
  let x109 : ℝ := (1 / 1)-(372039 / 1000000)
  have hx109 : Bounds (627961 / 1000000) (627961 / 1000000) x109 := by
    exact hx108
  let x110 : ℝ := Real.log x109
  have hx110 : Bounds (-465277217 / 1000000000) (-14539913 / 31250000) x110 := by
    exact bounds_log hx109 (by norm_num) (by simpa only [div_one] using reflection_log_10.1) (by simpa only [div_one] using reflection_log_10.2)
  let x111 : ℝ := x106*x110
  have hx111 : Bounds (-58435189293 / 200000000000) (-73043986459 / 250000000000) x111 := by
    apply bounds_mul hx106 hx110 <;> norm_num
  let x112 : ℝ := x103+x111
  have hx112 : Bounds (141797182043 / 1000000000000) (28359436809 / 200000000000) x112 := by
    apply bounds_add hx103 hx111 <;> norm_num
  let x113 : ℝ := (2 / 1)⁻¹
  have hx113 : Bounds (1 / 2) (1 / 2) x113 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x114 : ℝ := x112*x113
  have hx114 : Bounds (70898591021 / 1000000000000) (70898592023 / 1000000000000) x114 := by
    apply bounds_mul hx112 hx113 <;> norm_num
  let x115 : ℝ := x112/(2 / 1)
  have hx115 : Bounds (70898591021 / 1000000000000) (70898592023 / 1000000000000) x115 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx114
  let x116 : ℝ := -x115
  have hx116 : Bounds (-70898592023 / 1000000000000) (-70898591021 / 1000000000000) x116 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx115
  let x117 : ℝ := x99+x116
  have hx117 : Bounds (622248587977 / 1000000000000) (622248589979 / 1000000000000) x117 := by
    apply bounds_add hx99 hx116 <;> norm_num
  let x118 : ℝ := x99-x115
  have hx118 : Bounds (622248587977 / 1000000000000) (622248589979 / 1000000000000) x118 := by
    exact hx117
  let x119 : ℝ := biasE (372039 / 1000000)
  have hx119 : Bounds (622248587977 / 1000000000000) (622248589979 / 1000000000000) x119 := by
    simpa +zetaDelta only [biasE, div_one] using hx118
  let x120 : ℝ := Real.log (2 / 1)
  have hx120 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x120 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x121 : ℝ := (1 / 1)+(372903 / 1000000)
  have hx121 : Bounds (1372903 / 1000000) (1372903 / 1000000) x121 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((372903 / 1000000) : ℝ)) <;> norm_num
  let x122 : ℝ := (1 / 1)+(372903 / 1000000)
  have hx122 : Bounds (1372903 / 1000000) (1372903 / 1000000) x122 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((372903 / 1000000) : ℝ)) <;> norm_num
  let x123 : ℝ := Real.log x122
  have hx123 : Bounds (79231869 / 250000000) (316927477 / 1000000000) x123 := by
    exact bounds_log hx122 (by norm_num) (by simpa only [div_one] using reflection_log_11.1) (by simpa only [div_one] using reflection_log_11.2)
  let x124 : ℝ := x121*x123
  have hx124 : Bounds (217555341291 / 500000000000) (108777670989 / 250000000000) x124 := by
    apply bounds_mul hx121 hx123 <;> norm_num
  let x125 : ℝ := -(372903 / 1000000)
  have hx125 : Bounds (-372903 / 1000000) (-372903 / 1000000) x125 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((372903 / 1000000) : ℝ))
  let x126 : ℝ := (1 / 1)+x125
  have hx126 : Bounds (627097 / 1000000) (627097 / 1000000) x126 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx125 <;> norm_num
  let x127 : ℝ := (1 / 1)-(372903 / 1000000)
  have hx127 : Bounds (627097 / 1000000) (627097 / 1000000) x127 := by
    exact hx126
  let x128 : ℝ := -(372903 / 1000000)
  have hx128 : Bounds (-372903 / 1000000) (-372903 / 1000000) x128 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((372903 / 1000000) : ℝ))
  let x129 : ℝ := (1 / 1)+x128
  have hx129 : Bounds (627097 / 1000000) (627097 / 1000000) x129 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx128 <;> norm_num
  let x130 : ℝ := (1 / 1)-(372903 / 1000000)
  have hx130 : Bounds (627097 / 1000000) (627097 / 1000000) x130 := by
    exact hx129
  let x131 : ℝ := Real.log x130
  have hx131 : Bounds (-233327023 / 500000000) (-93330809 / 200000000) x131 := by
    exact bounds_log hx130 (by norm_num) (by simpa only [div_one] using reflection_log_12.1) (by simpa only [div_one] using reflection_log_12.2)
  let x132 : ℝ := x127*x131
  have hx132 : Bounds (-58527470457 / 200000000000) (-292637351657 / 1000000000000) x132 := by
    apply bounds_mul hx127 hx131 <;> norm_num
  let x133 : ℝ := x124+x132
  have hx133 : Bounds (142473330297 / 1000000000000) (142473332299 / 1000000000000) x133 := by
    apply bounds_add hx124 hx132 <;> norm_num
  let x134 : ℝ := (2 / 1)⁻¹
  have hx134 : Bounds (1 / 2) (1 / 2) x134 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x135 : ℝ := x133*x134
  have hx135 : Bounds (17809166287 / 250000000000) (1424733323 / 20000000000) x135 := by
    apply bounds_mul hx133 hx134 <;> norm_num
  let x136 : ℝ := x133/(2 / 1)
  have hx136 : Bounds (17809166287 / 250000000000) (1424733323 / 20000000000) x136 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx135
  let x137 : ℝ := -x136
  have hx137 : Bounds (-1424733323 / 20000000000) (-17809166287 / 250000000000) x137 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx136
  let x138 : ℝ := x120+x137
  have hx138 : Bounds (12438210277 / 20000000000) (155477628963 / 250000000000) x138 := by
    apply bounds_add hx120 hx137 <;> norm_num
  let x139 : ℝ := x120-x136
  have hx139 : Bounds (12438210277 / 20000000000) (155477628963 / 250000000000) x139 := by
    exact hx138
  let x140 : ℝ := biasE (372903 / 1000000)
  have hx140 : Bounds (12438210277 / 20000000000) (155477628963 / 250000000000) x140 := by
    simpa +zetaDelta only [biasE, div_one] using hx139
  let y : ℝ := 1 - 2 * entropyInverse ((1 + H (2*m - 1/2))/2)
  have hLh' : Real.log 2 * ((1 + H (2*m - 1/2))/2) = x98 := by
    simpa +zetaDelta only [div_one] using hLh
  have hy : Bounds (372039 / 1000000) (372903 / 1000000) y := by
    apply entropyInverseBias_bracket
    · exact div_nonneg (add_nonneg zero_le_one
        (H_nonneg (by linarith [hm.1]) (by linarith [hm.2]))) two_pos.le
    · linarith [H_le_one (2*m-1/2)]
    · norm_num
    · norm_num
    · norm_num
    · have h1 : biasE (372903 / 1000000) ≤ (155477628963 / 250000000000) := hx140.2
      have h2 : (621910764439 / 1000000000000) ≤ x98 := hx98.1
      linarith [hLh']
    · have h1 : x98 ≤ (622248559281 / 1000000000000) := hx98.2
      have h2 : (622248587977 / 1000000000000) ≤ biasE (372039 / 1000000) := hx119.1
      linarith [hLh']
  let x141 : ℝ := x3⁻¹
  have hx141 : Bounds (192048012003 / 50000000000) (3849624060151 / 1000000000000) x141 := by
    apply bounds_inv hx3 <;> norm_num
  let x142 : ℝ := x98*x141
  have hx142 : Bounds (95549380763 / 40000000000) (2395423025203 / 1000000000000) x142 := by
    apply bounds_mul hx98 hx141 <;> norm_num
  let x143 : ℝ := x98/x3
  have hx143 : Bounds (95549380763 / 40000000000) (2395423025203 / 1000000000000) x143 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx142
  let x144 : ℝ := Real.log (2 / 1)
  have hx144 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x144 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x145 : ℝ := (1 / 1)+(273543 / 1000000)
  have hx145 : Bounds (1273543 / 1000000) (1273543 / 1000000) x145 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((273543 / 1000000) : ℝ)) <;> norm_num
  let x146 : ℝ := (1 / 1)+(273543 / 1000000)
  have hx146 : Bounds (1273543 / 1000000) (1273543 / 1000000) x146 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((273543 / 1000000) : ℝ)) <;> norm_num
  let x147 : ℝ := Real.log x146
  have hx147 : Bounds (12090139 / 50000000) (241802781 / 1000000000) x147 := by
    exact bounds_log hx146 (by norm_num) (by simpa only [div_one] using reflection_log_13.1) (by simpa only [div_one] using reflection_log_13.2)
  let x148 : ℝ := x145*x147
  have hx148 : Bounds (307946237849 / 1000000000000) (76986559781 / 250000000000) x148 := by
    apply bounds_mul hx145 hx147 <;> norm_num
  let x149 : ℝ := -(273543 / 1000000)
  have hx149 : Bounds (-273543 / 1000000) (-273543 / 1000000) x149 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((273543 / 1000000) : ℝ))
  let x150 : ℝ := (1 / 1)+x149
  have hx150 : Bounds (726457 / 1000000) (726457 / 1000000) x150 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx149 <;> norm_num
  let x151 : ℝ := (1 / 1)-(273543 / 1000000)
  have hx151 : Bounds (726457 / 1000000) (726457 / 1000000) x151 := by
    exact hx150
  let x152 : ℝ := -(273543 / 1000000)
  have hx152 : Bounds (-273543 / 1000000) (-273543 / 1000000) x152 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((273543 / 1000000) : ℝ))
  let x153 : ℝ := (1 / 1)+x152
  have hx153 : Bounds (726457 / 1000000) (726457 / 1000000) x153 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx152 <;> norm_num
  let x154 : ℝ := (1 / 1)-(273543 / 1000000)
  have hx154 : Bounds (726457 / 1000000) (726457 / 1000000) x154 := by
    exact hx153
  let x155 : ℝ := Real.log x154
  have hx155 : Bounds (-159787993 / 500000000) (-63915197 / 200000000) x155 := by
    exact bounds_log hx154 (by norm_num) (by simpa only [div_one] using reflection_log_14.1) (by simpa only [div_one] using reflection_log_14.2)
  let x156 : ℝ := x151*x155
  have hx156 : Bounds (-116079106031 / 500000000000) (-46431642267 / 200000000000) x156 := by
    apply bounds_mul hx151 hx155 <;> norm_num
  let x157 : ℝ := x148+x156
  have hx157 : Bounds (75788025787 / 1000000000000) (75788027789 / 1000000000000) x157 := by
    apply bounds_add hx148 hx156 <;> norm_num
  let x158 : ℝ := (2 / 1)⁻¹
  have hx158 : Bounds (1 / 2) (1 / 2) x158 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x159 : ℝ := x157*x158
  have hx159 : Bounds (37894012893 / 1000000000000) (7578802779 / 200000000000) x159 := by
    apply bounds_mul hx157 hx158 <;> norm_num
  let x160 : ℝ := x157/(2 / 1)
  have hx160 : Bounds (37894012893 / 1000000000000) (7578802779 / 200000000000) x160 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx159
  let x161 : ℝ := -x160
  have hx161 : Bounds (-7578802779 / 200000000000) (-37894012893 / 1000000000000) x161 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx160
  let x162 : ℝ := x144+x161
  have hx162 : Bounds (131050633221 / 200000000000) (655253168107 / 1000000000000) x162 := by
    apply bounds_add hx144 hx161 <;> norm_num
  let x163 : ℝ := x144-x160
  have hx163 : Bounds (131050633221 / 200000000000) (655253168107 / 1000000000000) x163 := by
    exact hx162
  let x164 : ℝ := biasE (273543 / 1000000)
  have hx164 : Bounds (131050633221 / 200000000000) (655253168107 / 1000000000000) x164 := by
    simpa +zetaDelta only [biasE, div_one] using hx163
  let x165 : ℝ := Real.log (2 / 1)
  have hx165 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x165 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x166 : ℝ := (1 / 1)+(27423 / 100000)
  have hx166 : Bounds (127423 / 100000) (127423 / 100000) x166 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((27423 / 100000) : ℝ)) <;> norm_num
  let x167 : ℝ := (1 / 1)+(27423 / 100000)
  have hx167 : Bounds (127423 / 100000) (127423 / 100000) x167 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((27423 / 100000) : ℝ)) <;> norm_num
  let x168 : ℝ := Real.log x167
  have hx168 : Bounds (121171037 / 500000000) (9693683 / 40000000) x168 := by
    exact bounds_log hx167 (by norm_num) (by simpa only [div_one] using reflection_log_15.1) (by simpa only [div_one] using reflection_log_15.2)
  let x169 : ℝ := x166*x168
  have hx169 : Bounds (308799540953 / 1000000000000) (77199885557 / 250000000000) x169 := by
    apply bounds_mul hx166 hx168 <;> norm_num
  let x170 : ℝ := -(27423 / 100000)
  have hx170 : Bounds (-27423 / 100000) (-27423 / 100000) x170 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((27423 / 100000) : ℝ))
  let x171 : ℝ := (1 / 1)+x170
  have hx171 : Bounds (72577 / 100000) (72577 / 100000) x171 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx170 <;> norm_num
  let x172 : ℝ := (1 / 1)-(27423 / 100000)
  have hx172 : Bounds (72577 / 100000) (72577 / 100000) x172 := by
    exact hx171
  let x173 : ℝ := -(27423 / 100000)
  have hx173 : Bounds (-27423 / 100000) (-27423 / 100000) x173 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((27423 / 100000) : ℝ))
  let x174 : ℝ := (1 / 1)+x173
  have hx174 : Bounds (72577 / 100000) (72577 / 100000) x174 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx173 <;> norm_num
  let x175 : ℝ := (1 / 1)-(27423 / 100000)
  have hx175 : Bounds (72577 / 100000) (72577 / 100000) x175 := by
    exact hx174
  let x176 : ℝ := Real.log x175
  have hx176 : Bounds (-320522119 / 1000000000) (-160261059 / 500000000) x176 := by
    exact bounds_log hx175 (by norm_num) (by simpa only [div_one] using reflection_log_16.1) (by simpa only [div_one] using reflection_log_16.2)
  let x177 : ℝ := x172*x176
  have hx177 : Bounds (-232625338307 / 1000000000000) (-11631266879 / 50000000000) x177 := by
    apply bounds_mul hx172 hx176 <;> norm_num
  let x178 : ℝ := x169+x177
  have hx178 : Bounds (38087101323 / 500000000000) (9521775581 / 125000000000) x178 := by
    apply bounds_add hx169 hx177 <;> norm_num
  let x179 : ℝ := (2 / 1)⁻¹
  have hx179 : Bounds (1 / 2) (1 / 2) x179 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x180 : ℝ := x178*x179
  have hx180 : Bounds (38087101323 / 1000000000000) (9521775581 / 250000000000) x180 := by
    apply bounds_mul hx178 hx179 <;> norm_num
  let x181 : ℝ := x178/(2 / 1)
  have hx181 : Bounds (38087101323 / 1000000000000) (9521775581 / 250000000000) x181 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx180
  let x182 : ℝ := -x181
  have hx182 : Bounds (-9521775581 / 250000000000) (-38087101323 / 1000000000000) x182 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx181
  let x183 : ℝ := x165+x182
  have hx183 : Bounds (163765019419 / 250000000000) (655060079677 / 1000000000000) x183 := by
    apply bounds_add hx165 hx182 <;> norm_num
  let x184 : ℝ := x165-x181
  have hx184 : Bounds (163765019419 / 250000000000) (655060079677 / 1000000000000) x184 := by
    exact hx183
  let x185 : ℝ := biasE (27423 / 100000)
  have hx185 : Bounds (163765019419 / 250000000000) (655060079677 / 1000000000000) x185 := by
    simpa +zetaDelta only [biasE, div_one] using hx184
  let x186 : ℝ := x143*(273543 / 1000000)
  have hx186 : Bounds (653421606551 / 1000000000000) (81906400073 / 125000000000) x186 := by
    apply bounds_mul hx143 (bounds_const ((273543 / 1000000) : ℝ)) <;> norm_num
  let x187 : ℝ := x143*(27423 / 100000)
  have hx187 : Bounds (131012533433 / 200000000000) (328448428101 / 500000000000) x187 := by
    apply bounds_mul hx143 (bounds_const ((27423 / 100000) : ℝ)) <;> norm_num
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
  have hc : Bounds (273543 / 1000000) (27423 / 100000) c := by
    apply contact_bracket hc0 hcMem.2.le (by norm_num) (by norm_num) (by norm_num)
      (show 0 < x143 by linarith [hx143.1]) hcEq
    · have h1 : x143 * (273543 / 1000000) ≤ (81906400073 / 125000000000) := hx186.2
      have h2 : (131050633221 / 200000000000) ≤ biasE (273543 / 1000000) := hx164.1
      linarith
    · have h1 : biasE (27423 / 100000) ≤ (655060079677 / 1000000000000) := hx185.2
      have h2 : (131012533433 / 200000000000) ≤ x143 * (27423 / 100000) := hx187.1
      linarith
  let x188 : ℝ := (1 / 1)+y
  have hx188 : Bounds (1372039 / 1000000) (1372903 / 1000000) x188 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hy <;> norm_num
  let x189 : ℝ := -y
  have hx189 : Bounds (-372903 / 1000000) (-372039 / 1000000) x189 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hy
  let x190 : ℝ := (1 / 1)+x189
  have hx190 : Bounds (627097 / 1000000) (627961 / 1000000) x190 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx189 <;> norm_num
  let x191 : ℝ := (1 / 1)-y
  have hx191 : Bounds (627097 / 1000000) (627961 / 1000000) x191 := by
    exact hx190
  let x192 : ℝ := x191⁻¹
  have hx192 : Bounds (49764236951 / 31250000000) (1594649631557 / 1000000000000) x192 := by
    apply bounds_inv hx191 <;> norm_num
  let x193 : ℝ := x188*x192
  have hx193 : Bounds (34139236951 / 15625000000) (1094649631557 / 500000000000) x193 := by
    apply bounds_mul hx188 hx192 <;> norm_num
  let x194 : ℝ := x188/x191
  have hx194 : Bounds (34139236951 / 15625000000) (1094649631557 / 500000000000) x194 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx193
  let x195 : ℝ := Real.log x194
  have hx195 : Bounds (78157517 / 100000000) (391790761 / 500000000) x195 := by
    exact bounds_log hx194 (by norm_num) (by simpa only [div_one] using reflection_log_17.1) (by simpa only [div_one] using reflection_log_18.2)
  let x196 : ℝ := (2 / 1)⁻¹
  have hx196 : Bounds (1 / 2) (1 / 2) x196 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x197 : ℝ := x195*x196
  have hx197 : Bounds (78157517 / 200000000) (391790761 / 1000000000) x197 := by
    apply bounds_mul hx195 hx196 <;> norm_num
  let x198 : ℝ := x195/(2 / 1)
  have hx198 : Bounds (78157517 / 200000000) (391790761 / 1000000000) x198 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx197
  let x199 : ℝ := (1 / 1)+c
  have hx199 : Bounds (1273543 / 1000000) (127423 / 100000) x199 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hc <;> norm_num
  let x200 : ℝ := -c
  have hx200 : Bounds (-27423 / 100000) (-273543 / 1000000) x200 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hc
  let x201 : ℝ := (1 / 1)+x200
  have hx201 : Bounds (72577 / 100000) (726457 / 1000000) x201 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx200 <;> norm_num
  let x202 : ℝ := (1 / 1)-c
  have hx202 : Bounds (72577 / 100000) (726457 / 1000000) x202 := by
    exact hx201
  let x203 : ℝ := x202⁻¹
  have hx203 : Bounds (688271983063 / 500000000000) (275569395263 / 200000000000) x203 := by
    apply bounds_inv hx202 <;> norm_num
  let x204 : ℝ := x199*x203
  have hx204 : Bounds (438271983063 / 250000000000) (175569395263 / 100000000000) x204 := by
    apply bounds_mul hx199 hx203 <;> norm_num
  let x205 : ℝ := x199/x202
  have hx205 : Bounds (438271983063 / 250000000000) (175569395263 / 100000000000) x205 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx204
  let x206 : ℝ := Real.log x205
  have hx206 : Bounds (112275753 / 200000000) (281432097 / 500000000) x206 := by
    exact bounds_log hx205 (by norm_num) (by simpa only [div_one] using reflection_log_19.1) (by simpa only [div_one] using reflection_log_20.2)
  let x207 : ℝ := (2 / 1)⁻¹
  have hx207 : Bounds (1 / 2) (1 / 2) x207 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x208 : ℝ := x206*x207
  have hx208 : Bounds (112275753 / 400000000) (281432097 / 1000000000) x208 := by
    apply bounds_mul hx206 hx207 <;> norm_num
  let x209 : ℝ := x206/(2 / 1)
  have hx209 : Bounds (112275753 / 400000000) (281432097 / 1000000000) x209 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx208
  let x210 : ℝ := (2 / 1)*x50
  have hx210 : Bounds (658862059993 / 500000000000) (329509010659 / 250000000000) x210 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx50 <;> norm_num
  let x211 : ℝ := (2 / 1)*x98
  have hx211 : Bounds (621910764439 / 500000000000) (622248559281 / 500000000000) x211 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx98 <;> norm_num
  let x212 : ℝ := -x211
  have hx212 : Bounds (-622248559281 / 500000000000) (-621910764439 / 500000000000) x212 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx211
  let x213 : ℝ := x210+x212
  have hx213 : Bounds (4576687589 / 62500000000) (37107256879 / 500000000000) x213 := by
    apply bounds_add hx210 hx212 <;> norm_num
  let x214 : ℝ := x210-x211
  have hx214 : Bounds (4576687589 / 62500000000) (37107256879 / 500000000000) x214 := by
    exact hx213
  let x215 : ℝ := y*x198
  have hx215 : Bounds (29077644467 / 200000000000) (2921999003 / 20000000000) x215 := by
    apply bounds_mul hy hx198 <;> norm_num
  let x216 : ℝ := -x215
  have hx216 : Bounds (-2921999003 / 20000000000) (-29077644467 / 200000000000) x216 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx215
  let x217 : ℝ := x214+x216
  have hx217 : Bounds (-36436474363 / 500000000000) (-71173708577 / 1000000000000) x217 := by
    apply bounds_add hx214 hx216 <;> norm_num
  let x218 : ℝ := x214-x215
  have hx218 : Bounds (-36436474363 / 500000000000) (-71173708577 / 1000000000000) x218 := by
    exact hx217
  let x219 : ℝ := x3*x209
  have hx219 : Bounds (583307623 / 8000000000) (4579455387 / 62500000000) x219 := by
    apply bounds_mul hx3 hx209 <;> norm_num
  let x220 : ℝ := x218+x219
  have hx220 : Bounds (40504149 / 1000000000000) (419515523 / 200000000000) x220 := by
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

theorem acceptedCertificate : DoubleCapBiasCellCertificate (3787 / 10240) (379 / 1024) (fun m => (1 + H (2*m - 1/2))/2) where
  domain := by norm_num
  sound m hmLo hmHi := by
    exact cell_bias_nonneg m ⟨hmLo, hmHi⟩

theorem accepted_cell :
    ∀ m, (3787 / 10240) ≤ m → m ≤ (379 / 1024) → 0 ≤ doubleCapHighResidual m := by
  intro m hmLo hmHi
  unfold doubleCapHighResidual
  apply doubleCapEndpointResidual_nonneg_of_biasCell acceptedCertificate hmLo hmHi
  exact div_pos (by linarith [H_nonneg (by linarith : 0 ≤ 2*m-1/2) (by linarith : 2*m-1/2 ≤ 1)]) two_pos

#print axioms cell_bias_nonneg
#print axioms accepted_cell

end GeneralCK.Certificates.DoubleCapMiddle.Cell0275

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0276 =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0276
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Reflection
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem cell_bias_nonneg (m : ℝ) (hm : Bounds (379 / 1024) (3793 / 10240) m) :
    let h := (1 + H (2*m - 1/2))/2
    let x := 1-2*m
    let y := 1-2*entropyInverse h
    let c := regularContact (x/(Real.log 2*h))
    0 ≤ 2*(biasE x-Real.log 2*h)-y*SmallMean.A y+x*SmallMean.A c := by
  have hEq : biasE (2-4*m) = Real.log 2 * H (2*m-1/2) := by
    have hmstrict : 1/4 < m := by
      have hlo : (1/4 : ℝ) < (379 / 1024) := by norm_num
      exact lt_of_lt_of_le hlo hm.1
    rw [show 2-4*m = 1-2*(2*m-1/2) by ring,
      GeneralCK.Correction.Natural.biasE_probability (by linarith [hmstrict]) (by linarith [hm.2]),
      GeneralCK.Certificates.Mixed.hn_eq_H_mul_log]
    ring
  have hLh : Real.log 2 * ((1 + H (2*m - 1/2))/2) = (Real.log 2 + biasE (2-4*m))/2 := by
    rw [hEq]
    ring
  let x0 : ℝ := (2 / 1)*m
  have hx0 : Bounds (379 / 512) (3793 / 5120) x0 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hm <;> norm_num
  let x1 : ℝ := -x0
  have hx1 : Bounds (-3793 / 5120) (-379 / 512) x1 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx0
  let x2 : ℝ := (1 / 1)+x1
  have hx2 : Bounds (1327 / 5120) (133 / 512) x2 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx1 <;> norm_num
  let x3 : ℝ := (1 / 1)-x0
  have hx3 : Bounds (1327 / 5120) (133 / 512) x3 := by
    exact hx2
  let x4 : ℝ := (4 / 1)*m
  have hx4 : Bounds (379 / 256) (3793 / 2560) x4 := by
    apply bounds_mul (bounds_const ((4 / 1) : ℝ)) hm <;> norm_num
  let x5 : ℝ := -x4
  have hx5 : Bounds (-3793 / 2560) (-379 / 256) x5 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx4
  let x6 : ℝ := (2 / 1)+x5
  have hx6 : Bounds (1327 / 2560) (133 / 256) x6 := by
    apply bounds_add (bounds_const ((2 / 1) : ℝ)) hx5 <;> norm_num
  let x7 : ℝ := (2 / 1)-x4
  have hx7 : Bounds (1327 / 2560) (133 / 256) x7 := by
    exact hx6
  let x8 : ℝ := Real.log (2 / 1)
  have hx8 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x8 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x9 : ℝ := (1 / 1)+(133 / 512)
  have hx9 : Bounds (645 / 512) (645 / 512) x9 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((133 / 512) : ℝ)) <;> norm_num
  let x10 : ℝ := (1 / 1)+(133 / 512)
  have hx10 : Bounds (645 / 512) (645 / 512) x10 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((133 / 512) : ℝ)) <;> norm_num
  let x11 : ℝ := Real.log x10
  have hx11 : Bounds (230925691 / 1000000000) (57731423 / 250000000) x11 := by
    exact bounds_log hx10 (by norm_num) (by simpa only [div_one] using reflection_log_1.1) (by simpa only [div_one] using reflection_log_1.2)
  let x12 : ℝ := x9*x11
  have hx12 : Bounds (290912247451 / 1000000000000) (290912248711 / 1000000000000) x12 := by
    apply bounds_mul hx9 hx11 <;> norm_num
  let x13 : ℝ := -(133 / 512)
  have hx13 : Bounds (-133 / 512) (-133 / 512) x13 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((133 / 512) : ℝ))
  let x14 : ℝ := (1 / 1)+x13
  have hx14 : Bounds (379 / 512) (379 / 512) x14 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx13 <;> norm_num
  let x15 : ℝ := (1 / 1)-(133 / 512)
  have hx15 : Bounds (379 / 512) (379 / 512) x15 := by
    exact hx14
  let x16 : ℝ := -(133 / 512)
  have hx16 : Bounds (-133 / 512) (-133 / 512) x16 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((133 / 512) : ℝ))
  let x17 : ℝ := (1 / 1)+x16
  have hx17 : Bounds (379 / 512) (379 / 512) x17 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx16 <;> norm_num
  let x18 : ℝ := (1 / 1)-(133 / 512)
  have hx18 : Bounds (379 / 512) (379 / 512) x18 := by
    exact hx17
  let x19 : ℝ := Real.log x18
  have hx19 : Bounds (-15039421 / 50000000) (-300788419 / 1000000000) x19 := by
    exact bounds_log hx18 (by norm_num) (by simpa only [div_one] using reflection_log_2.1) (by simpa only [div_one] using reflection_log_2.2)
  let x20 : ℝ := x15*x19
  have hx20 : Bounds (-111326964043 / 500000000000) (-44530785469 / 200000000000) x20 := by
    apply bounds_mul hx15 hx19 <;> norm_num
  let x21 : ℝ := x12+x20
  have hx21 : Bounds (13651663873 / 200000000000) (34129160683 / 500000000000) x21 := by
    apply bounds_add hx12 hx20 <;> norm_num
  let x22 : ℝ := (2 / 1)⁻¹
  have hx22 : Bounds (1 / 2) (1 / 2) x22 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x23 : ℝ := x21*x22
  have hx23 : Bounds (17064579841 / 500000000000) (34129160683 / 1000000000000) x23 := by
    apply bounds_mul hx21 hx22 <;> norm_num
  let x24 : ℝ := x21/(2 / 1)
  have hx24 : Bounds (17064579841 / 500000000000) (34129160683 / 1000000000000) x24 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx23
  let x25 : ℝ := -x24
  have hx25 : Bounds (-34129160683 / 1000000000000) (-17064579841 / 500000000000) x25 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx24
  let x26 : ℝ := x8+x25
  have hx26 : Bounds (659018019317 / 1000000000000) (329509010659 / 500000000000) x26 := by
    apply bounds_add hx8 hx25 <;> norm_num
  let x27 : ℝ := x8-x24
  have hx27 : Bounds (659018019317 / 1000000000000) (329509010659 / 500000000000) x27 := by
    exact hx26
  let x28 : ℝ := biasE (133 / 512)
  have hx28 : Bounds (659018019317 / 1000000000000) (329509010659 / 500000000000) x28 := by
    simpa +zetaDelta only [biasE, div_one] using hx27
  let x29 : ℝ := Real.log (2 / 1)
  have hx29 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x29 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x30 : ℝ := (1 / 1)+(1327 / 5120)
  have hx30 : Bounds (6447 / 5120) (6447 / 5120) x30 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1327 / 5120) : ℝ)) <;> norm_num
  let x31 : ℝ := (1 / 1)+(1327 / 5120)
  have hx31 : Bounds (6447 / 5120) (6447 / 5120) x31 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1327 / 5120) : ℝ)) <;> norm_num
  let x32 : ℝ := Real.log x31
  have hx32 : Bounds (230460467 / 1000000000) (57615117 / 250000000) x32 := by
    exact bounds_log hx31 (by norm_num) (by simpa only [div_one] using reflection_log_3.1) (by simpa only [div_one] using reflection_log_3.2)
  let x33 : ℝ := x30*x32
  have hx33 : Bounds (145095569409 / 500000000000) (145095570039 / 500000000000) x33 := by
    apply bounds_mul hx30 hx32 <;> norm_num
  let x34 : ℝ := -(1327 / 5120)
  have hx34 : Bounds (-1327 / 5120) (-1327 / 5120) x34 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1327 / 5120) : ℝ))
  let x35 : ℝ := (1 / 1)+x34
  have hx35 : Bounds (3793 / 5120) (3793 / 5120) x35 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx34 <;> norm_num
  let x36 : ℝ := (1 / 1)-(1327 / 5120)
  have hx36 : Bounds (3793 / 5120) (3793 / 5120) x36 := by
    exact hx35
  let x37 : ℝ := -(1327 / 5120)
  have hx37 : Bounds (-1327 / 5120) (-1327 / 5120) x37 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1327 / 5120) : ℝ))
  let x38 : ℝ := (1 / 1)+x37
  have hx38 : Bounds (3793 / 5120) (3793 / 5120) x38 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx37 <;> norm_num
  let x39 : ℝ := (1 / 1)-(1327 / 5120)
  have hx39 : Bounds (3793 / 5120) (3793 / 5120) x39 := by
    exact hx38
  let x40 : ℝ := Real.log x39
  have hx40 : Bounds (-299997177 / 1000000000) (-37499647 / 125000000) x40 := by
    exact bounds_log hx39 (by norm_num) (by simpa only [div_one] using reflection_log_4.1) (by simpa only [div_one] using reflection_log_4.2)
  let x41 : ℝ := x36*x40
  have hx41 : Bounds (-44448800483 / 200000000000) (-222244001673 / 1000000000000) x41 := by
    apply bounds_mul hx36 hx40 <;> norm_num
  let x42 : ℝ := x33+x41
  have hx42 : Bounds (67947136403 / 1000000000000) (13589427681 / 200000000000) x42 := by
    apply bounds_add hx33 hx41 <;> norm_num
  let x43 : ℝ := (2 / 1)⁻¹
  have hx43 : Bounds (1 / 2) (1 / 2) x43 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x44 : ℝ := x42*x43
  have hx44 : Bounds (33973568201 / 1000000000000) (33973569203 / 1000000000000) x44 := by
    apply bounds_mul hx42 hx43 <;> norm_num
  let x45 : ℝ := x42/(2 / 1)
  have hx45 : Bounds (33973568201 / 1000000000000) (33973569203 / 1000000000000) x45 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx44
  let x46 : ℝ := -x45
  have hx46 : Bounds (-33973569203 / 1000000000000) (-33973568201 / 1000000000000) x46 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx45
  let x47 : ℝ := x29+x46
  have hx47 : Bounds (659173610797 / 1000000000000) (659173612799 / 1000000000000) x47 := by
    apply bounds_add hx29 hx46 <;> norm_num
  let x48 : ℝ := x29-x45
  have hx48 : Bounds (659173610797 / 1000000000000) (659173612799 / 1000000000000) x48 := by
    exact hx47
  let x49 : ℝ := biasE (1327 / 5120)
  have hx49 : Bounds (659173610797 / 1000000000000) (659173612799 / 1000000000000) x49 := by
    simpa +zetaDelta only [biasE, div_one] using hx48
  let x50 : ℝ := biasE x3
  have hx50 : Bounds (659018019317 / 1000000000000) (659173612799 / 1000000000000) x50 := by
    exact bounds_biasE hx3 (by norm_num) (by norm_num) hx28.1 hx49.2
  let x51 : ℝ := Real.log (2 / 1)
  have hx51 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x51 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x52 : ℝ := (1 / 1)+(133 / 256)
  have hx52 : Bounds (389 / 256) (389 / 256) x52 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((133 / 256) : ℝ)) <;> norm_num
  let x53 : ℝ := (1 / 1)+(133 / 256)
  have hx53 : Bounds (389 / 256) (389 / 256) x53 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((133 / 256) : ℝ)) <;> norm_num
  let x54 : ℝ := Real.log x53
  have hx54 : Bounds (418401899 / 1000000000) (4184019 / 10000000) x54 := by
    exact bounds_log hx53 (by norm_num) (by simpa only [div_one] using reflection_log_5.1) (by simpa only [div_one] using reflection_log_5.2)
  let x55 : ℝ := x52*x54
  have hx55 : Bounds (635774760589 / 1000000000000) (63577476211 / 100000000000) x55 := by
    apply bounds_mul hx52 hx54 <;> norm_num
  let x56 : ℝ := -(133 / 256)
  have hx56 : Bounds (-133 / 256) (-133 / 256) x56 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((133 / 256) : ℝ))
  let x57 : ℝ := (1 / 1)+x56
  have hx57 : Bounds (123 / 256) (123 / 256) x57 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx56 <;> norm_num
  let x58 : ℝ := (1 / 1)-(133 / 256)
  have hx58 : Bounds (123 / 256) (123 / 256) x58 := by
    exact hx57
  let x59 : ℝ := -(133 / 256)
  have hx59 : Bounds (-133 / 256) (-133 / 256) x59 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((133 / 256) : ℝ))
  let x60 : ℝ := (1 / 1)+x59
  have hx60 : Bounds (123 / 256) (123 / 256) x60 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx59 <;> norm_num
  let x61 : ℝ := (1 / 1)-(133 / 256)
  have hx61 : Bounds (123 / 256) (123 / 256) x61 := by
    exact hx60
  let x62 : ℝ := Real.log x61
  have hx62 : Bounds (-73299309 / 100000000) (-11453017 / 15625000) x62 := by
    exact bounds_log hx61 (by norm_num) (by simpa only [div_one] using reflection_log_6.1) (by simpa only [div_one] using reflection_log_6.2)
  let x63 : ℝ := x58*x62
  have hx63 : Bounds (-352180273711 / 1000000000000) (-1408721091 / 4000000000) x63 := by
    apply bounds_mul hx58 hx62 <;> norm_num
  let x64 : ℝ := x55+x63
  have hx64 : Bounds (141797243439 / 500000000000) (3544931117 / 12500000000) x64 := by
    apply bounds_add hx55 hx63 <;> norm_num
  let x65 : ℝ := (2 / 1)⁻¹
  have hx65 : Bounds (1 / 2) (1 / 2) x65 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x66 : ℝ := x64*x65
  have hx66 : Bounds (141797243439 / 1000000000000) (3544931117 / 25000000000) x66 := by
    apply bounds_mul hx64 hx65 <;> norm_num
  let x67 : ℝ := x64/(2 / 1)
  have hx67 : Bounds (141797243439 / 1000000000000) (3544931117 / 25000000000) x67 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx66
  let x68 : ℝ := -x67
  have hx68 : Bounds (-3544931117 / 25000000000) (-141797243439 / 1000000000000) x68 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx67
  let x69 : ℝ := x51+x68
  have hx69 : Bounds (13783748383 / 25000000000) (551349937561 / 1000000000000) x69 := by
    apply bounds_add hx51 hx68 <;> norm_num
  let x70 : ℝ := x51-x67
  have hx70 : Bounds (13783748383 / 25000000000) (551349937561 / 1000000000000) x70 := by
    exact hx69
  let x71 : ℝ := biasE (133 / 256)
  have hx71 : Bounds (13783748383 / 25000000000) (551349937561 / 1000000000000) x71 := by
    simpa +zetaDelta only [biasE, div_one] using hx70
  let x72 : ℝ := Real.log (2 / 1)
  have hx72 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x72 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x73 : ℝ := (1 / 1)+(1327 / 2560)
  have hx73 : Bounds (3887 / 2560) (3887 / 2560) x73 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1327 / 2560) : ℝ)) <;> norm_num
  let x74 : ℝ := (1 / 1)+(1327 / 2560)
  have hx74 : Bounds (3887 / 2560) (3887 / 2560) x74 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1327 / 2560) : ℝ)) <;> norm_num
  let x75 : ℝ := Real.log x74
  have hx75 : Bounds (417630393 / 1000000000) (208815197 / 500000000) x75 := by
    exact bounds_log hx74 (by norm_num) (by simpa only [div_one] using reflection_log_7.1) (by simpa only [div_one] using reflection_log_7.2)
  let x76 : ℝ := x73*x75
  have hx76 : Bounds (19816031953 / 31250000000) (126822604803 / 200000000000) x76 := by
    apply bounds_mul hx73 hx75 <;> norm_num
  let x77 : ℝ := -(1327 / 2560)
  have hx77 : Bounds (-1327 / 2560) (-1327 / 2560) x77 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1327 / 2560) : ℝ))
  let x78 : ℝ := (1 / 1)+x77
  have hx78 : Bounds (1233 / 2560) (1233 / 2560) x78 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx77 <;> norm_num
  let x79 : ℝ := (1 / 1)-(1327 / 2560)
  have hx79 : Bounds (1233 / 2560) (1233 / 2560) x79 := by
    exact hx78
  let x80 : ℝ := -(1327 / 2560)
  have hx80 : Bounds (-1327 / 2560) (-1327 / 2560) x80 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1327 / 2560) : ℝ))
  let x81 : ℝ := (1 / 1)+x80
  have hx81 : Bounds (1233 / 2560) (1233 / 2560) x81 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx80 <;> norm_num
  let x82 : ℝ := (1 / 1)-(1327 / 2560)
  have hx82 : Bounds (1233 / 2560) (1233 / 2560) x82 := by
    exact hx81
  let x83 : ℝ := Real.log x82
  have hx83 : Bounds (-146111407 / 200000000) (-730557033 / 1000000000) x83 := by
    exact bounds_log hx82 (by norm_num) (by simpa only [div_one] using reflection_log_8.1) (by simpa only [div_one] using reflection_log_8.2)
  let x84 : ℝ := x79*x83
  have hx84 : Bounds (-43983243367 / 125000000000) (-87966486493 / 250000000000) x84 := by
    apply bounds_mul hx79 hx83 <;> norm_num
  let x85 : ℝ := x76+x84
  have hx85 : Bounds (7056176889 / 25000000000) (282247078043 / 1000000000000) x85 := by
    apply bounds_add hx76 hx84 <;> norm_num
  let x86 : ℝ := (2 / 1)⁻¹
  have hx86 : Bounds (1 / 2) (1 / 2) x86 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x87 : ℝ := x85*x86
  have hx87 : Bounds (7056176889 / 50000000000) (70561769511 / 500000000000) x87 := by
    apply bounds_mul hx85 hx86 <;> norm_num
  let x88 : ℝ := x85/(2 / 1)
  have hx88 : Bounds (7056176889 / 50000000000) (70561769511 / 500000000000) x88 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx87
  let x89 : ℝ := -x88
  have hx89 : Bounds (-70561769511 / 500000000000) (-7056176889 / 50000000000) x89 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx88
  let x90 : ℝ := x72+x89
  have hx90 : Bounds (276011820489 / 500000000000) (27601182161 / 50000000000) x90 := by
    apply bounds_add hx72 hx89 <;> norm_num
  let x91 : ℝ := x72-x88
  have hx91 : Bounds (276011820489 / 500000000000) (27601182161 / 50000000000) x91 := by
    exact hx90
  let x92 : ℝ := biasE (1327 / 2560)
  have hx92 : Bounds (276011820489 / 500000000000) (27601182161 / 50000000000) x92 := by
    simpa +zetaDelta only [biasE, div_one] using hx91
  let x93 : ℝ := biasE x7
  have hx93 : Bounds (13783748383 / 25000000000) (27601182161 / 50000000000) x93 := by
    exact bounds_biasE hx7 (by norm_num) (by norm_num) hx71.1 hx92.2
  let x94 : ℝ := Real.log (2 / 1)
  have hx94 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x94 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x95 : ℝ := x94+x93
  have hx95 : Bounds (31112427883 / 25000000000) (62258541211 / 50000000000) x95 := by
    apply bounds_add hx94 hx93 <;> norm_num
  let x96 : ℝ := (2 / 1)⁻¹
  have hx96 : Bounds (1 / 2) (1 / 2) x96 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x97 : ℝ := x95*x96
  have hx97 : Bounds (31112427883 / 50000000000) (62258541211 / 100000000000) x97 := by
    apply bounds_mul hx95 hx96 <;> norm_num
  let x98 : ℝ := x95/(2 / 1)
  have hx98 : Bounds (31112427883 / 50000000000) (62258541211 / 100000000000) x98 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx97
  let x99 : ℝ := Real.log (2 / 1)
  have hx99 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x99 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x100 : ℝ := (1 / 1)+(14847 / 40000)
  have hx100 : Bounds (54847 / 40000) (54847 / 40000) x100 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((14847 / 40000) : ℝ)) <;> norm_num
  let x101 : ℝ := (1 / 1)+(14847 / 40000)
  have hx101 : Bounds (54847 / 40000) (54847 / 40000) x101 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((14847 / 40000) : ℝ)) <;> norm_num
  let x102 : ℝ := Real.log x101
  have hx102 : Bounds (78917009 / 250000000) (315668037 / 1000000000) x102 := by
    exact bounds_log hx101 (by norm_num) (by simpa only [div_one] using reflection_log_9.1) (by simpa only [div_one] using reflection_log_9.2)
  let x103 : ℝ := x100*x102
  have hx103 : Bounds (216418059631 / 500000000000) (216418060317 / 500000000000) x103 := by
    apply bounds_mul hx100 hx102 <;> norm_num
  let x104 : ℝ := -(14847 / 40000)
  have hx104 : Bounds (-14847 / 40000) (-14847 / 40000) x104 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((14847 / 40000) : ℝ))
  let x105 : ℝ := (1 / 1)+x104
  have hx105 : Bounds (25153 / 40000) (25153 / 40000) x105 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx104 <;> norm_num
  let x106 : ℝ := (1 / 1)-(14847 / 40000)
  have hx106 : Bounds (25153 / 40000) (25153 / 40000) x106 := by
    exact hx105
  let x107 : ℝ := -(14847 / 40000)
  have hx107 : Bounds (-14847 / 40000) (-14847 / 40000) x107 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((14847 / 40000) : ℝ))
  let x108 : ℝ := (1 / 1)+x107
  have hx108 : Bounds (25153 / 40000) (25153 / 40000) x108 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx107 <;> norm_num
  let x109 : ℝ := (1 / 1)-(14847 / 40000)
  have hx109 : Bounds (25153 / 40000) (25153 / 40000) x109 := by
    exact hx108
  let x110 : ℝ := Real.log x109
  have hx110 : Bounds (-463902281 / 1000000000) (-11597557 / 25000000) x110 := by
    exact bounds_log hx109 (by norm_num) (by simpa only [div_one] using reflection_log_10.1) (by simpa only [div_one] using reflection_log_10.2)
  let x111 : ℝ := x106*x110
  have hx111 : Bounds (-5834267037 / 20000000000) (-291713351221 / 1000000000000) x111 := by
    apply bounds_mul hx106 hx110 <;> norm_num
  let x112 : ℝ := x103+x111
  have hx112 : Bounds (35280691853 / 250000000000) (141122769413 / 1000000000000) x112 := by
    apply bounds_add hx103 hx111 <;> norm_num
  let x113 : ℝ := (2 / 1)⁻¹
  have hx113 : Bounds (1 / 2) (1 / 2) x113 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x114 : ℝ := x112*x113
  have hx114 : Bounds (35280691853 / 500000000000) (70561384707 / 1000000000000) x114 := by
    apply bounds_mul hx112 hx113 <;> norm_num
  let x115 : ℝ := x112/(2 / 1)
  have hx115 : Bounds (35280691853 / 500000000000) (70561384707 / 1000000000000) x115 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx114
  let x116 : ℝ := -x115
  have hx116 : Bounds (-70561384707 / 1000000000000) (-35280691853 / 500000000000) x116 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx115
  let x117 : ℝ := x99+x116
  have hx117 : Bounds (622585795293 / 1000000000000) (311292898647 / 500000000000) x117 := by
    apply bounds_add hx99 hx116 <;> norm_num
  let x118 : ℝ := x99-x115
  have hx118 : Bounds (622585795293 / 1000000000000) (311292898647 / 500000000000) x118 := by
    exact hx117
  let x119 : ℝ := biasE (14847 / 40000)
  have hx119 : Bounds (622585795293 / 1000000000000) (311292898647 / 500000000000) x119 := by
    simpa +zetaDelta only [biasE, div_one] using hx118
  let x120 : ℝ := Real.log (2 / 1)
  have hx120 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x120 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x121 : ℝ := (1 / 1)+(9301 / 25000)
  have hx121 : Bounds (34301 / 25000) (34301 / 25000) x121 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((9301 / 25000) : ℝ)) <;> norm_num
  let x122 : ℝ := (1 / 1)+(9301 / 25000)
  have hx122 : Bounds (34301 / 25000) (34301 / 25000) x122 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((9301 / 25000) : ℝ)) <;> norm_num
  let x123 : ℝ := Real.log x122
  have hx123 : Bounds (316298683 / 1000000000) (79074671 / 250000000) x123 := by
    exact bounds_log hx122 (by norm_num) (by simpa only [div_one] using reflection_log_11.1) (by simpa only [div_one] using reflection_log_11.2)
  let x124 : ℝ := x121*x123
  have hx124 : Bounds (433974445023 / 1000000000000) (108493611599 / 250000000000) x124 := by
    apply bounds_mul hx121 hx123 <;> norm_num
  let x125 : ℝ := -(9301 / 25000)
  have hx125 : Bounds (-9301 / 25000) (-9301 / 25000) x125 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((9301 / 25000) : ℝ))
  let x126 : ℝ := (1 / 1)+x125
  have hx126 : Bounds (15699 / 25000) (15699 / 25000) x126 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx125 <;> norm_num
  let x127 : ℝ := (1 / 1)-(9301 / 25000)
  have hx127 : Bounds (15699 / 25000) (15699 / 25000) x127 := by
    exact hx126
  let x128 : ℝ := -(9301 / 25000)
  have hx128 : Bounds (-9301 / 25000) (-9301 / 25000) x128 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((9301 / 25000) : ℝ))
  let x129 : ℝ := (1 / 1)+x128
  have hx129 : Bounds (15699 / 25000) (15699 / 25000) x129 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx128 <;> norm_num
  let x130 : ℝ := (1 / 1)-(9301 / 25000)
  have hx130 : Bounds (15699 / 25000) (15699 / 25000) x130 := by
    exact hx129
  let x131 : ℝ := Real.log x130
  have hx131 : Bounds (-465278809 / 1000000000) (-58159851 / 125000000) x131 := by
    exact bounds_log hx130 (by norm_num) (by simpa only [div_one] using reflection_log_12.1) (by simpa only [div_one] using reflection_log_12.2)
  let x132 : ℝ := x127*x131
  have hx132 : Bounds (-2921764809 / 10000000000) (-292176480271 / 1000000000000) x132 := by
    apply bounds_mul hx127 hx131 <;> norm_num
  let x133 : ℝ := x124+x132
  have hx133 : Bounds (141797964123 / 1000000000000) (1134383729 / 8000000000) x133 := by
    apply bounds_add hx124 hx132 <;> norm_num
  let x134 : ℝ := (2 / 1)⁻¹
  have hx134 : Bounds (1 / 2) (1 / 2) x134 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x135 : ℝ := x133*x134
  have hx135 : Bounds (70898982061 / 1000000000000) (70898983063 / 1000000000000) x135 := by
    apply bounds_mul hx133 hx134 <;> norm_num
  let x136 : ℝ := x133/(2 / 1)
  have hx136 : Bounds (70898982061 / 1000000000000) (70898983063 / 1000000000000) x136 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx135
  let x137 : ℝ := -x136
  have hx137 : Bounds (-70898983063 / 1000000000000) (-70898982061 / 1000000000000) x137 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx136
  let x138 : ℝ := x120+x137
  have hx138 : Bounds (622248196937 / 1000000000000) (622248198939 / 1000000000000) x138 := by
    apply bounds_add hx120 hx137 <;> norm_num
  let x139 : ℝ := x120-x136
  have hx139 : Bounds (622248196937 / 1000000000000) (622248198939 / 1000000000000) x139 := by
    exact hx138
  let x140 : ℝ := biasE (9301 / 25000)
  have hx140 : Bounds (622248196937 / 1000000000000) (622248198939 / 1000000000000) x140 := by
    simpa +zetaDelta only [biasE, div_one] using hx139
  let y : ℝ := 1 - 2 * entropyInverse ((1 + H (2*m - 1/2))/2)
  have hLh' : Real.log 2 * ((1 + H (2*m - 1/2))/2) = x98 := by
    simpa +zetaDelta only [div_one] using hLh
  have hy : Bounds (14847 / 40000) (9301 / 25000) y := by
    apply entropyInverseBias_bracket
    · exact div_nonneg (add_nonneg zero_le_one
        (H_nonneg (by linarith [hm.1]) (by linarith [hm.2]))) two_pos.le
    · linarith [H_le_one (2*m-1/2)]
    · norm_num
    · norm_num
    · norm_num
    · have h1 : biasE (9301 / 25000) ≤ (622248198939 / 1000000000000) := hx140.2
      have h2 : (31112427883 / 50000000000) ≤ x98 := hx98.1
      linarith [hLh']
    · have h1 : x98 ≤ (62258541211 / 100000000000) := hx98.2
      have h2 : (622585795293 / 1000000000000) ≤ biasE (14847 / 40000) := hx119.1
      linarith [hLh']
  let x141 : ℝ := x3⁻¹
  have hx141 : Bounds (76992481203 / 20000000000) (771665410701 / 200000000000) x141 := by
    apply bounds_inv hx3 <;> norm_num
  let x142 : ℝ := x98*x141
  have hx142 : Bounds (2395423018961 / 1000000000000) (1201069069331 / 500000000000) x142 := by
    apply bounds_mul hx98 hx141 <;> norm_num
  let x143 : ℝ := x98/x3
  have hx143 : Bounds (2395423018961 / 1000000000000) (1201069069331 / 500000000000) x143 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx142
  let x144 : ℝ := Real.log (2 / 1)
  have hx144 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x144 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x145 : ℝ := (1 / 1)+(136429 / 500000)
  have hx145 : Bounds (636429 / 500000) (636429 / 500000) x145 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((136429 / 500000) : ℝ)) <;> norm_num
  let x146 : ℝ := (1 / 1)+(136429 / 500000)
  have hx146 : Bounds (636429 / 500000) (636429 / 500000) x146 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((136429 / 500000) : ℝ)) <;> norm_num
  let x147 : ℝ := Real.log x146
  have hx147 : Bounds (48252953 / 200000000) (120632383 / 500000000) x147 := by
    exact bounds_log hx146 (by norm_num) (by simpa only [div_one] using reflection_log_13.1) (by simpa only [div_one] using reflection_log_13.2)
  let x148 : ℝ := x145*x147
  have hx148 : Bounds (38386973281 / 125000000000) (153547893761 / 500000000000) x148 := by
    apply bounds_mul hx145 hx147 <;> norm_num
  let x149 : ℝ := -(136429 / 500000)
  have hx149 : Bounds (-136429 / 500000) (-136429 / 500000) x149 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((136429 / 500000) : ℝ))
  let x150 : ℝ := (1 / 1)+x149
  have hx150 : Bounds (363571 / 500000) (363571 / 500000) x150 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx149 <;> norm_num
  let x151 : ℝ := (1 / 1)-(136429 / 500000)
  have hx151 : Bounds (363571 / 500000) (363571 / 500000) x151 := by
    exact hx150
  let x152 : ℝ := -(136429 / 500000)
  have hx152 : Bounds (-136429 / 500000) (-136429 / 500000) x152 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((136429 / 500000) : ℝ))
  let x153 : ℝ := (1 / 1)+x152
  have hx153 : Bounds (363571 / 500000) (363571 / 500000) x153 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx152 <;> norm_num
  let x154 : ℝ := (1 / 1)-(136429 / 500000)
  have hx154 : Bounds (363571 / 500000) (363571 / 500000) x154 := by
    exact hx153
  let x155 : ℝ := Real.log x154
  have hx155 : Bounds (-159316749 / 500000000) (-318633497 / 1000000000) x155 := by
    exact bounds_log hx154 (by norm_num) (by simpa only [div_one] using reflection_log_14.1) (by simpa only [div_one] using reflection_log_14.2)
  let x156 : ℝ := x151*x155
  have hx156 : Bounds (-231691799003 / 1000000000000) (-9267671931 / 40000000000) x156 := by
    apply bounds_mul hx151 hx155 <;> norm_num
  let x157 : ℝ := x148+x156
  have hx157 : Bounds (15080797449 / 200000000000) (75403989247 / 1000000000000) x157 := by
    apply bounds_add hx148 hx156 <;> norm_num
  let x158 : ℝ := (2 / 1)⁻¹
  have hx158 : Bounds (1 / 2) (1 / 2) x158 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x159 : ℝ := x157*x158
  have hx159 : Bounds (18850996811 / 500000000000) (294546833 / 7812500000) x159 := by
    apply bounds_mul hx157 hx158 <;> norm_num
  let x160 : ℝ := x157/(2 / 1)
  have hx160 : Bounds (18850996811 / 500000000000) (294546833 / 7812500000) x160 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx159
  let x161 : ℝ := -x160
  have hx161 : Bounds (-294546833 / 7812500000) (-18850996811 / 500000000000) x161 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx160
  let x162 : ℝ := x144+x161
  have hx162 : Bounds (20482662043 / 31250000000) (327722593689 / 500000000000) x162 := by
    apply bounds_add hx144 hx161 <;> norm_num
  let x163 : ℝ := x144-x160
  have hx163 : Bounds (20482662043 / 31250000000) (327722593689 / 500000000000) x163 := by
    exact hx162
  let x164 : ℝ := biasE (136429 / 500000)
  have hx164 : Bounds (20482662043 / 31250000000) (327722593689 / 500000000000) x164 := by
    simpa +zetaDelta only [biasE, div_one] using hx163
  let x165 : ℝ := Real.log (2 / 1)
  have hx165 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x165 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x166 : ℝ := (1 / 1)+(34193 / 125000)
  have hx166 : Bounds (159193 / 125000) (159193 / 125000) x166 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((34193 / 125000) : ℝ)) <;> norm_num
  let x167 : ℝ := (1 / 1)+(34193 / 125000)
  have hx167 : Bounds (159193 / 125000) (159193 / 125000) x167 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((34193 / 125000) : ℝ)) <;> norm_num
  let x168 : ℝ := Real.log x167
  have hx168 : Bounds (48360713 / 200000000) (120901783 / 500000000) x168 := by
    exact bounds_log hx167 (by norm_num) (by simpa only [div_one] using reflection_log_15.1) (by simpa only [div_one] using reflection_log_15.2)
  let x169 : ℝ := x166*x168
  have hx169 : Bounds (38493434923 / 125000000000) (153973740329 / 500000000000) x169 := by
    apply bounds_mul hx166 hx168 <;> norm_num
  let x170 : ℝ := -(34193 / 125000)
  have hx170 : Bounds (-34193 / 125000) (-34193 / 125000) x170 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((34193 / 125000) : ℝ))
  let x171 : ℝ := (1 / 1)+x170
  have hx171 : Bounds (90807 / 125000) (90807 / 125000) x171 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx170 <;> norm_num
  let x172 : ℝ := (1 / 1)-(34193 / 125000)
  have hx172 : Bounds (90807 / 125000) (90807 / 125000) x172 := by
    exact hx171
  let x173 : ℝ := -(34193 / 125000)
  have hx173 : Bounds (-34193 / 125000) (-34193 / 125000) x173 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((34193 / 125000) : ℝ))
  let x174 : ℝ := (1 / 1)+x173
  have hx174 : Bounds (90807 / 125000) (90807 / 125000) x174 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx173 <;> norm_num
  let x175 : ℝ := (1 / 1)-(34193 / 125000)
  have hx175 : Bounds (90807 / 125000) (90807 / 125000) x175 := by
    exact hx174
  let x176 : ℝ := Real.log x175
  have hx176 : Bounds (-319577363 / 1000000000) (-159788681 / 500000000) x176 := by
    exact bounds_log hx175 (by norm_num) (by simpa only [div_one] using reflection_log_16.1) (by simpa only [div_one] using reflection_log_16.2)
  let x177 : ℝ := x172*x176
  have hx177 : Bounds (-14509930801 / 62500000000) (-232158892089 / 1000000000000) x177 := by
    apply bounds_mul hx172 hx176 <;> norm_num
  let x178 : ℝ := x169+x177
  have hx178 : Bounds (9473573321 / 125000000000) (75788588569 / 1000000000000) x178 := by
    apply bounds_add hx169 hx177 <;> norm_num
  let x179 : ℝ := (2 / 1)⁻¹
  have hx179 : Bounds (1 / 2) (1 / 2) x179 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x180 : ℝ := x178*x179
  have hx180 : Bounds (9473573321 / 250000000000) (7578858857 / 200000000000) x180 := by
    apply bounds_mul hx178 hx179 <;> norm_num
  let x181 : ℝ := x178/(2 / 1)
  have hx181 : Bounds (9473573321 / 250000000000) (7578858857 / 200000000000) x181 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx180
  let x182 : ℝ := -x181
  have hx182 : Bounds (-7578858857 / 200000000000) (-9473573321 / 250000000000) x182 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx181
  let x183 : ℝ := x165+x182
  have hx183 : Bounds (131050577143 / 200000000000) (163813221929 / 250000000000) x183 := by
    apply bounds_add hx165 hx182 <;> norm_num
  let x184 : ℝ := x165-x181
  have hx184 : Bounds (131050577143 / 200000000000) (163813221929 / 250000000000) x184 := by
    exact hx183
  let x185 : ℝ := biasE (34193 / 125000)
  have hx185 : Bounds (131050577143 / 200000000000) (163813221929 / 250000000000) x185 := by
    simpa +zetaDelta only [biasE, div_one] using hx184
  let x186 : ℝ := x143*(136429 / 500000)
  have hx186 : Bounds (653610334107 / 1000000000000) (8193032603 / 12500000000) x186 := by
    apply bounds_mul hx143 (bounds_const ((136429 / 500000) : ℝ)) <;> norm_num
  let x187 : ℝ := x143*(34193 / 125000)
  have hx187 : Bounds (327626797149 / 500000000000) (657090475003 / 1000000000000) x187 := by
    apply bounds_mul hx143 (bounds_const ((34193 / 125000) : ℝ)) <;> norm_num
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
  have hc : Bounds (136429 / 500000) (34193 / 125000) c := by
    apply contact_bracket hc0 hcMem.2.le (by norm_num) (by norm_num) (by norm_num)
      (show 0 < x143 by linarith [hx143.1]) hcEq
    · have h1 : x143 * (136429 / 500000) ≤ (8193032603 / 12500000000) := hx186.2
      have h2 : (20482662043 / 31250000000) ≤ biasE (136429 / 500000) := hx164.1
      linarith
    · have h1 : biasE (34193 / 125000) ≤ (163813221929 / 250000000000) := hx185.2
      have h2 : (327626797149 / 500000000000) ≤ x143 * (34193 / 125000) := hx187.1
      linarith
  let x188 : ℝ := (1 / 1)+y
  have hx188 : Bounds (54847 / 40000) (34301 / 25000) x188 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hy <;> norm_num
  let x189 : ℝ := -y
  have hx189 : Bounds (-9301 / 25000) (-14847 / 40000) x189 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hy
  let x190 : ℝ := (1 / 1)+x189
  have hx190 : Bounds (15699 / 25000) (25153 / 40000) x190 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx189 <;> norm_num
  let x191 : ℝ := (1 / 1)-y
  have hx191 : Bounds (15699 / 25000) (25153 / 40000) x191 := by
    exact hx190
  let x192 : ℝ := x191⁻¹
  have hx192 : Bounds (1590267562517 / 1000000000000) (99528632397 / 62500000000) x192 := by
    apply bounds_inv hx191 <;> norm_num
  let x193 : ℝ := x188*x192
  have hx193 : Bounds (1090267562517 / 500000000000) (68278632397 / 31250000000) x193 := by
    apply bounds_mul hx188 hx192 <;> norm_num
  let x194 : ℝ := x188/x191
  have hx194 : Bounds (1090267562517 / 500000000000) (68278632397 / 31250000000) x194 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx193
  let x195 : ℝ := Real.log x194
  have hx195 : Bounds (194892579 / 250000000) (781577493 / 1000000000) x195 := by
    exact bounds_log hx194 (by norm_num) (by simpa only [div_one] using reflection_log_17.1) (by simpa only [div_one] using reflection_log_18.2)
  let x196 : ℝ := (2 / 1)⁻¹
  have hx196 : Bounds (1 / 2) (1 / 2) x196 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x197 : ℝ := x195*x196
  have hx197 : Bounds (194892579 / 500000000) (781577493 / 2000000000) x197 := by
    apply bounds_mul hx195 hx196 <;> norm_num
  let x198 : ℝ := x195/(2 / 1)
  have hx198 : Bounds (194892579 / 500000000) (781577493 / 2000000000) x198 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx197
  let x199 : ℝ := (1 / 1)+c
  have hx199 : Bounds (636429 / 500000) (159193 / 125000) x199 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hc <;> norm_num
  let x200 : ℝ := -c
  have hx200 : Bounds (-34193 / 125000) (-136429 / 500000) x200 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hc
  let x201 : ℝ := (1 / 1)+x200
  have hx201 : Bounds (90807 / 125000) (363571 / 500000) x201 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx200 <;> norm_num
  let x202 : ℝ := (1 / 1)-c
  have hx202 : Bounds (90807 / 125000) (363571 / 500000) x202 := by
    exact hx201
  let x203 : ℝ := x202⁻¹
  have hx203 : Bounds (343811800171 / 250000000000) (688272930501 / 500000000000) x203 := by
    apply bounds_inv hx202 <;> norm_num
  let x204 : ℝ := x199*x203
  have hx204 : Bounds (218811800171 / 125000000000) (438272930501 / 250000000000) x204 := by
    apply bounds_mul hx199 hx203 <;> norm_num
  let x205 : ℝ := x199/x202
  have hx205 : Bounds (218811800171 / 125000000000) (438272930501 / 250000000000) x205 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx204
  let x206 : ℝ := Real.log x205
  have hx206 : Bounds (559898263 / 1000000000) (8771577 / 15625000) x206 := by
    exact bounds_log hx205 (by norm_num) (by simpa only [div_one] using reflection_log_19.1) (by simpa only [div_one] using reflection_log_20.2)
  let x207 : ℝ := (2 / 1)⁻¹
  have hx207 : Bounds (1 / 2) (1 / 2) x207 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x208 : ℝ := x206*x207
  have hx208 : Bounds (559898263 / 2000000000) (8771577 / 31250000) x208 := by
    apply bounds_mul hx206 hx207 <;> norm_num
  let x209 : ℝ := x206/(2 / 1)
  have hx209 : Bounds (559898263 / 2000000000) (8771577 / 31250000) x209 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx208
  let x210 : ℝ := (2 / 1)*x50
  have hx210 : Bounds (659018019317 / 500000000000) (659173612799 / 500000000000) x210 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx50 <;> norm_num
  let x211 : ℝ := (2 / 1)*x98
  have hx211 : Bounds (31112427883 / 25000000000) (62258541211 / 50000000000) x211 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx98 <;> norm_num
  let x212 : ℝ := -x211
  have hx212 : Bounds (-62258541211 / 50000000000) (-31112427883 / 25000000000) x212 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx211
  let x213 : ℝ := x210+x212
  have hx213 : Bounds (36432607207 / 500000000000) (36925055139 / 500000000000) x213 := by
    apply bounds_add hx210 hx212 <;> norm_num
  let x214 : ℝ := x210-x211
  have hx214 : Bounds (36432607207 / 500000000000) (36925055139 / 500000000000) x214 := by
    exact hx213
  let x215 : ℝ := y*x198
  have hx215 : Bounds (7233925301 / 50000000000) (283962979 / 1953125000) x215 := by
    apply bounds_mul hy hx198 <;> norm_num
  let x216 : ℝ := -x215
  have hx216 : Bounds (-283962979 / 1953125000) (-7233925301 / 50000000000) x216 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx215
  let x217 : ℝ := x214+x216
  have hx217 : Bounds (-36261915417 / 500000000000) (-35414197871 / 500000000000) x217 := by
    apply bounds_add hx214 hx216 <;> norm_num
  let x218 : ℝ := x214-x215
  have hx218 : Bounds (-36261915417 / 500000000000) (-35414197871 / 500000000000) x218 := by
    exact hx217
  let x219 : ℝ := x3*x209
  have hx219 : Bounds (36278564209 / 500000000000) (72913733813 / 1000000000000) x219 := by
    apply bounds_mul hx3 hx209 <;> norm_num
  let x220 : ℝ := x218+x219
  have hx220 : Bounds (2081099 / 62500000000) (2085338071 / 1000000000000) x220 := by
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

theorem acceptedCertificate : DoubleCapBiasCellCertificate (379 / 1024) (3793 / 10240) (fun m => (1 + H (2*m - 1/2))/2) where
  domain := by norm_num
  sound m hmLo hmHi := by
    exact cell_bias_nonneg m ⟨hmLo, hmHi⟩

theorem accepted_cell :
    ∀ m, (379 / 1024) ≤ m → m ≤ (3793 / 10240) → 0 ≤ doubleCapHighResidual m := by
  intro m hmLo hmHi
  unfold doubleCapHighResidual
  apply doubleCapEndpointResidual_nonneg_of_biasCell acceptedCertificate hmLo hmHi
  exact div_pos (by linarith [H_nonneg (by linarith : 0 ≤ 2*m-1/2) (by linarith : 2*m-1/2 ≤ 1)]) two_pos

#print axioms cell_bias_nonneg
#print axioms accepted_cell

end GeneralCK.Certificates.DoubleCapMiddle.Cell0276

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0277 =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0277
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Reflection
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem cell_bias_nonneg (m : ℝ) (hm : Bounds (3793 / 10240) (949 / 2560) m) :
    let h := (1 + H (2*m - 1/2))/2
    let x := 1-2*m
    let y := 1-2*entropyInverse h
    let c := regularContact (x/(Real.log 2*h))
    0 ≤ 2*(biasE x-Real.log 2*h)-y*SmallMean.A y+x*SmallMean.A c := by
  have hEq : biasE (2-4*m) = Real.log 2 * H (2*m-1/2) := by
    have hmstrict : 1/4 < m := by
      have hlo : (1/4 : ℝ) < (3793 / 10240) := by norm_num
      exact lt_of_lt_of_le hlo hm.1
    rw [show 2-4*m = 1-2*(2*m-1/2) by ring,
      GeneralCK.Correction.Natural.biasE_probability (by linarith [hmstrict]) (by linarith [hm.2]),
      GeneralCK.Certificates.Mixed.hn_eq_H_mul_log]
    ring
  have hLh : Real.log 2 * ((1 + H (2*m - 1/2))/2) = (Real.log 2 + biasE (2-4*m))/2 := by
    rw [hEq]
    ring
  let x0 : ℝ := (2 / 1)*m
  have hx0 : Bounds (3793 / 5120) (949 / 1280) x0 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hm <;> norm_num
  let x1 : ℝ := -x0
  have hx1 : Bounds (-949 / 1280) (-3793 / 5120) x1 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx0
  let x2 : ℝ := (1 / 1)+x1
  have hx2 : Bounds (331 / 1280) (1327 / 5120) x2 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx1 <;> norm_num
  let x3 : ℝ := (1 / 1)-x0
  have hx3 : Bounds (331 / 1280) (1327 / 5120) x3 := by
    exact hx2
  let x4 : ℝ := (4 / 1)*m
  have hx4 : Bounds (3793 / 2560) (949 / 640) x4 := by
    apply bounds_mul (bounds_const ((4 / 1) : ℝ)) hm <;> norm_num
  let x5 : ℝ := -x4
  have hx5 : Bounds (-949 / 640) (-3793 / 2560) x5 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx4
  let x6 : ℝ := (2 / 1)+x5
  have hx6 : Bounds (331 / 640) (1327 / 2560) x6 := by
    apply bounds_add (bounds_const ((2 / 1) : ℝ)) hx5 <;> norm_num
  let x7 : ℝ := (2 / 1)-x4
  have hx7 : Bounds (331 / 640) (1327 / 2560) x7 := by
    exact hx6
  let x8 : ℝ := Real.log (2 / 1)
  have hx8 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x8 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x9 : ℝ := (1 / 1)+(1327 / 5120)
  have hx9 : Bounds (6447 / 5120) (6447 / 5120) x9 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1327 / 5120) : ℝ)) <;> norm_num
  let x10 : ℝ := (1 / 1)+(1327 / 5120)
  have hx10 : Bounds (6447 / 5120) (6447 / 5120) x10 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1327 / 5120) : ℝ)) <;> norm_num
  let x11 : ℝ := Real.log x10
  have hx11 : Bounds (230460467 / 1000000000) (57615117 / 250000000) x11 := by
    exact bounds_log hx10 (by norm_num) (by simpa only [div_one] using reflection_log_1.1) (by simpa only [div_one] using reflection_log_1.2)
  let x12 : ℝ := x9*x11
  have hx12 : Bounds (145095569409 / 500000000000) (145095570039 / 500000000000) x12 := by
    apply bounds_mul hx9 hx11 <;> norm_num
  let x13 : ℝ := -(1327 / 5120)
  have hx13 : Bounds (-1327 / 5120) (-1327 / 5120) x13 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1327 / 5120) : ℝ))
  let x14 : ℝ := (1 / 1)+x13
  have hx14 : Bounds (3793 / 5120) (3793 / 5120) x14 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx13 <;> norm_num
  let x15 : ℝ := (1 / 1)-(1327 / 5120)
  have hx15 : Bounds (3793 / 5120) (3793 / 5120) x15 := by
    exact hx14
  let x16 : ℝ := -(1327 / 5120)
  have hx16 : Bounds (-1327 / 5120) (-1327 / 5120) x16 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1327 / 5120) : ℝ))
  let x17 : ℝ := (1 / 1)+x16
  have hx17 : Bounds (3793 / 5120) (3793 / 5120) x17 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx16 <;> norm_num
  let x18 : ℝ := (1 / 1)-(1327 / 5120)
  have hx18 : Bounds (3793 / 5120) (3793 / 5120) x18 := by
    exact hx17
  let x19 : ℝ := Real.log x18
  have hx19 : Bounds (-299997177 / 1000000000) (-37499647 / 125000000) x19 := by
    exact bounds_log hx18 (by norm_num) (by simpa only [div_one] using reflection_log_2.1) (by simpa only [div_one] using reflection_log_2.2)
  let x20 : ℝ := x15*x19
  have hx20 : Bounds (-44448800483 / 200000000000) (-222244001673 / 1000000000000) x20 := by
    apply bounds_mul hx15 hx19 <;> norm_num
  let x21 : ℝ := x12+x20
  have hx21 : Bounds (67947136403 / 1000000000000) (13589427681 / 200000000000) x21 := by
    apply bounds_add hx12 hx20 <;> norm_num
  let x22 : ℝ := (2 / 1)⁻¹
  have hx22 : Bounds (1 / 2) (1 / 2) x22 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x23 : ℝ := x21*x22
  have hx23 : Bounds (33973568201 / 1000000000000) (33973569203 / 1000000000000) x23 := by
    apply bounds_mul hx21 hx22 <;> norm_num
  let x24 : ℝ := x21/(2 / 1)
  have hx24 : Bounds (33973568201 / 1000000000000) (33973569203 / 1000000000000) x24 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx23
  let x25 : ℝ := -x24
  have hx25 : Bounds (-33973569203 / 1000000000000) (-33973568201 / 1000000000000) x25 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx24
  let x26 : ℝ := x8+x25
  have hx26 : Bounds (659173610797 / 1000000000000) (659173612799 / 1000000000000) x26 := by
    apply bounds_add hx8 hx25 <;> norm_num
  let x27 : ℝ := x8-x24
  have hx27 : Bounds (659173610797 / 1000000000000) (659173612799 / 1000000000000) x27 := by
    exact hx26
  let x28 : ℝ := biasE (1327 / 5120)
  have hx28 : Bounds (659173610797 / 1000000000000) (659173612799 / 1000000000000) x28 := by
    simpa +zetaDelta only [biasE, div_one] using hx27
  let x29 : ℝ := Real.log (2 / 1)
  have hx29 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x29 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x30 : ℝ := (1 / 1)+(331 / 1280)
  have hx30 : Bounds (1611 / 1280) (1611 / 1280) x30 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((331 / 1280) : ℝ)) <;> norm_num
  let x31 : ℝ := (1 / 1)+(331 / 1280)
  have hx31 : Bounds (1611 / 1280) (1611 / 1280) x31 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((331 / 1280) : ℝ)) <;> norm_num
  let x32 : ℝ := Real.log x31
  have hx32 : Bounds (114997513 / 500000000) (229995027 / 1000000000) x32 := by
    exact bounds_log hx31 (by norm_num) (by simpa only [div_one] using reflection_log_3.1) (by simpa only [div_one] using reflection_log_3.2)
  let x33 : ℝ := x30*x32
  have hx33 : Bounds (144735151127 / 500000000000) (144735151757 / 500000000000) x33 := by
    apply bounds_mul hx30 hx32 <;> norm_num
  let x34 : ℝ := -(331 / 1280)
  have hx34 : Bounds (-331 / 1280) (-331 / 1280) x34 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((331 / 1280) : ℝ))
  let x35 : ℝ := (1 / 1)+x34
  have hx35 : Bounds (949 / 1280) (949 / 1280) x35 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx34 <;> norm_num
  let x36 : ℝ := (1 / 1)-(331 / 1280)
  have hx36 : Bounds (949 / 1280) (949 / 1280) x36 := by
    exact hx35
  let x37 : ℝ := -(331 / 1280)
  have hx37 : Bounds (-331 / 1280) (-331 / 1280) x37 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((331 / 1280) : ℝ))
  let x38 : ℝ := (1 / 1)+x37
  have hx38 : Bounds (949 / 1280) (949 / 1280) x38 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx37 <;> norm_num
  let x39 : ℝ := (1 / 1)-(331 / 1280)
  have hx39 : Bounds (949 / 1280) (949 / 1280) x39 := by
    exact hx38
  let x40 : ℝ := Real.log x39
  have hx40 : Bounds (-299206559 / 1000000000) (-149603279 / 500000000) x40 := by
    exact bounds_log hx39 (by norm_num) (by simpa only [div_one] using reflection_log_4.1) (by simpa only [div_one] using reflection_log_4.2)
  let x41 : ℝ := x36*x40
  have hx41 : Bounds (-55458403221 / 250000000000) (-110916806071 / 500000000000) x41 := by
    apply bounds_mul hx36 hx40 <;> norm_num
  let x42 : ℝ := x33+x41
  have hx42 : Bounds (6763668937 / 100000000000) (16909172843 / 250000000000) x42 := by
    apply bounds_add hx33 hx41 <;> norm_num
  let x43 : ℝ := (2 / 1)⁻¹
  have hx43 : Bounds (1 / 2) (1 / 2) x43 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x44 : ℝ := x42*x43
  have hx44 : Bounds (6763668937 / 200000000000) (16909172843 / 500000000000) x44 := by
    apply bounds_mul hx42 hx43 <;> norm_num
  let x45 : ℝ := x42/(2 / 1)
  have hx45 : Bounds (6763668937 / 200000000000) (16909172843 / 500000000000) x45 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx44
  let x46 : ℝ := -x45
  have hx46 : Bounds (-16909172843 / 500000000000) (-6763668937 / 200000000000) x46 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx45
  let x47 : ℝ := x29+x46
  have hx47 : Bounds (329664417157 / 500000000000) (131865767263 / 200000000000) x47 := by
    apply bounds_add hx29 hx46 <;> norm_num
  let x48 : ℝ := x29-x45
  have hx48 : Bounds (329664417157 / 500000000000) (131865767263 / 200000000000) x48 := by
    exact hx47
  let x49 : ℝ := biasE (331 / 1280)
  have hx49 : Bounds (329664417157 / 500000000000) (131865767263 / 200000000000) x49 := by
    simpa +zetaDelta only [biasE, div_one] using hx48
  let x50 : ℝ := biasE x3
  have hx50 : Bounds (659173610797 / 1000000000000) (131865767263 / 200000000000) x50 := by
    exact bounds_biasE hx3 (by norm_num) (by norm_num) hx28.1 hx49.2
  let x51 : ℝ := Real.log (2 / 1)
  have hx51 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x51 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x52 : ℝ := (1 / 1)+(1327 / 2560)
  have hx52 : Bounds (3887 / 2560) (3887 / 2560) x52 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1327 / 2560) : ℝ)) <;> norm_num
  let x53 : ℝ := (1 / 1)+(1327 / 2560)
  have hx53 : Bounds (3887 / 2560) (3887 / 2560) x53 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1327 / 2560) : ℝ)) <;> norm_num
  let x54 : ℝ := Real.log x53
  have hx54 : Bounds (417630393 / 1000000000) (208815197 / 500000000) x54 := by
    exact bounds_log hx53 (by norm_num) (by simpa only [div_one] using reflection_log_5.1) (by simpa only [div_one] using reflection_log_5.2)
  let x55 : ℝ := x52*x54
  have hx55 : Bounds (19816031953 / 31250000000) (126822604803 / 200000000000) x55 := by
    apply bounds_mul hx52 hx54 <;> norm_num
  let x56 : ℝ := -(1327 / 2560)
  have hx56 : Bounds (-1327 / 2560) (-1327 / 2560) x56 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1327 / 2560) : ℝ))
  let x57 : ℝ := (1 / 1)+x56
  have hx57 : Bounds (1233 / 2560) (1233 / 2560) x57 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx56 <;> norm_num
  let x58 : ℝ := (1 / 1)-(1327 / 2560)
  have hx58 : Bounds (1233 / 2560) (1233 / 2560) x58 := by
    exact hx57
  let x59 : ℝ := -(1327 / 2560)
  have hx59 : Bounds (-1327 / 2560) (-1327 / 2560) x59 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1327 / 2560) : ℝ))
  let x60 : ℝ := (1 / 1)+x59
  have hx60 : Bounds (1233 / 2560) (1233 / 2560) x60 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx59 <;> norm_num
  let x61 : ℝ := (1 / 1)-(1327 / 2560)
  have hx61 : Bounds (1233 / 2560) (1233 / 2560) x61 := by
    exact hx60
  let x62 : ℝ := Real.log x61
  have hx62 : Bounds (-146111407 / 200000000) (-730557033 / 1000000000) x62 := by
    exact bounds_log hx61 (by norm_num) (by simpa only [div_one] using reflection_log_6.1) (by simpa only [div_one] using reflection_log_6.2)
  let x63 : ℝ := x58*x62
  have hx63 : Bounds (-43983243367 / 125000000000) (-87966486493 / 250000000000) x63 := by
    apply bounds_mul hx58 hx62 <;> norm_num
  let x64 : ℝ := x55+x63
  have hx64 : Bounds (7056176889 / 25000000000) (282247078043 / 1000000000000) x64 := by
    apply bounds_add hx55 hx63 <;> norm_num
  let x65 : ℝ := (2 / 1)⁻¹
  have hx65 : Bounds (1 / 2) (1 / 2) x65 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x66 : ℝ := x64*x65
  have hx66 : Bounds (7056176889 / 50000000000) (70561769511 / 500000000000) x66 := by
    apply bounds_mul hx64 hx65 <;> norm_num
  let x67 : ℝ := x64/(2 / 1)
  have hx67 : Bounds (7056176889 / 50000000000) (70561769511 / 500000000000) x67 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx66
  let x68 : ℝ := -x67
  have hx68 : Bounds (-70561769511 / 500000000000) (-7056176889 / 50000000000) x68 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx67
  let x69 : ℝ := x51+x68
  have hx69 : Bounds (276011820489 / 500000000000) (27601182161 / 50000000000) x69 := by
    apply bounds_add hx51 hx68 <;> norm_num
  let x70 : ℝ := x51-x67
  have hx70 : Bounds (276011820489 / 500000000000) (27601182161 / 50000000000) x70 := by
    exact hx69
  let x71 : ℝ := biasE (1327 / 2560)
  have hx71 : Bounds (276011820489 / 500000000000) (27601182161 / 50000000000) x71 := by
    simpa +zetaDelta only [biasE, div_one] using hx70
  let x72 : ℝ := Real.log (2 / 1)
  have hx72 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x72 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x73 : ℝ := (1 / 1)+(331 / 640)
  have hx73 : Bounds (971 / 640) (971 / 640) x73 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((331 / 640) : ℝ)) <;> norm_num
  let x74 : ℝ := (1 / 1)+(331 / 640)
  have hx74 : Bounds (971 / 640) (971 / 640) x74 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((331 / 640) : ℝ)) <;> norm_num
  let x75 : ℝ := Real.log x74
  have hx75 : Bounds (416858291 / 1000000000) (104214573 / 250000000) x75 := by
    exact bounds_log hx74 (by norm_num) (by simpa only [div_one] using reflection_log_7.1) (by simpa only [div_one] using reflection_log_7.2)
  let x76 : ℝ := x73*x75
  have hx76 : Bounds (79056523547 / 125000000000) (316226094947 / 500000000000) x76 := by
    apply bounds_mul hx73 hx75 <;> norm_num
  let x77 : ℝ := -(331 / 640)
  have hx77 : Bounds (-331 / 640) (-331 / 640) x77 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((331 / 640) : ℝ))
  let x78 : ℝ := (1 / 1)+x77
  have hx78 : Bounds (309 / 640) (309 / 640) x78 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx77 <;> norm_num
  let x79 : ℝ := (1 / 1)-(331 / 640)
  have hx79 : Bounds (309 / 640) (309 / 640) x79 := by
    exact hx78
  let x80 : ℝ := -(331 / 640)
  have hx80 : Bounds (-331 / 640) (-331 / 640) x80 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((331 / 640) : ℝ))
  let x81 : ℝ := (1 / 1)+x80
  have hx81 : Bounds (309 / 640) (309 / 640) x81 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx80 <;> norm_num
  let x82 : ℝ := (1 / 1)-(331 / 640)
  have hx82 : Bounds (309 / 640) (309 / 640) x82 := by
    exact hx81
  let x83 : ℝ := Real.log x82
  have hx83 : Bounds (-7281269 / 10000000) (-364063449 / 500000000) x83 := by
    exact bounds_log hx82 (by norm_num) (by simpa only [div_one] using reflection_log_8.1) (by simpa only [div_one] using reflection_log_8.2)
  let x84 : ℝ := x79*x83
  have hx84 : Bounds (-351548768907 / 1000000000000) (-17577438397 / 50000000000) x84 := by
    apply bounds_mul hx79 hx83 <;> norm_num
  let x85 : ℝ := x76+x84
  have hx85 : Bounds (280903419469 / 1000000000000) (140451710977 / 500000000000) x85 := by
    apply bounds_add hx76 hx84 <;> norm_num
  let x86 : ℝ := (2 / 1)⁻¹
  have hx86 : Bounds (1 / 2) (1 / 2) x86 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x87 : ℝ := x85*x86
  have hx87 : Bounds (70225854867 / 500000000000) (140451710977 / 1000000000000) x87 := by
    apply bounds_mul hx85 hx86 <;> norm_num
  let x88 : ℝ := x85/(2 / 1)
  have hx88 : Bounds (70225854867 / 500000000000) (140451710977 / 1000000000000) x88 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx87
  let x89 : ℝ := -x88
  have hx89 : Bounds (-140451710977 / 1000000000000) (-70225854867 / 500000000000) x89 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx88
  let x90 : ℝ := x72+x89
  have hx90 : Bounds (552695469023 / 1000000000000) (276347735633 / 500000000000) x90 := by
    apply bounds_add hx72 hx89 <;> norm_num
  let x91 : ℝ := x72-x88
  have hx91 : Bounds (552695469023 / 1000000000000) (276347735633 / 500000000000) x91 := by
    exact hx90
  let x92 : ℝ := biasE (331 / 640)
  have hx92 : Bounds (552695469023 / 1000000000000) (276347735633 / 500000000000) x92 := by
    simpa +zetaDelta only [biasE, div_one] using hx91
  let x93 : ℝ := biasE x7
  have hx93 : Bounds (276011820489 / 500000000000) (276347735633 / 500000000000) x93 := by
    exact bounds_biasE hx7 (by norm_num) (by norm_num) hx71.1 hx92.2
  let x94 : ℝ := Real.log (2 / 1)
  have hx94 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x94 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x95 : ℝ := x94+x93
  have hx95 : Bounds (622585410489 / 500000000000) (622921326133 / 500000000000) x95 := by
    apply bounds_add hx94 hx93 <;> norm_num
  let x96 : ℝ := (2 / 1)⁻¹
  have hx96 : Bounds (1 / 2) (1 / 2) x96 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x97 : ℝ := x95*x96
  have hx97 : Bounds (622585410489 / 1000000000000) (622921326133 / 1000000000000) x97 := by
    apply bounds_mul hx95 hx96 <;> norm_num
  let x98 : ℝ := x95/(2 / 1)
  have hx98 : Bounds (622585410489 / 1000000000000) (622921326133 / 1000000000000) x98 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx97
  let x99 : ℝ := Real.log (2 / 1)
  have hx99 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x99 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x100 : ℝ := (1 / 1)+(370313 / 1000000)
  have hx100 : Bounds (1370313 / 1000000) (1370313 / 1000000) x100 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((370313 / 1000000) : ℝ)) <;> norm_num
  let x101 : ℝ := (1 / 1)+(370313 / 1000000)
  have hx101 : Bounds (1370313 / 1000000) (1370313 / 1000000) x101 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((370313 / 1000000) : ℝ)) <;> norm_num
  let x102 : ℝ := Real.log x101
  have hx102 : Bounds (15751959 / 50000000) (315039181 / 1000000000) x102 := by
    exact bounds_log hx101 (by norm_num) (by simpa only [div_one] using reflection_log_9.1) (by simpa only [div_one] using reflection_log_9.2)
  let x103 : ℝ := x100*x102
  have hx103 : Bounds (431702283863 / 1000000000000) (215851142617 / 500000000000) x103 := by
    apply bounds_mul hx100 hx102 <;> norm_num
  let x104 : ℝ := -(370313 / 1000000)
  have hx104 : Bounds (-370313 / 1000000) (-370313 / 1000000) x104 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((370313 / 1000000) : ℝ))
  let x105 : ℝ := (1 / 1)+x104
  have hx105 : Bounds (629687 / 1000000) (629687 / 1000000) x105 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx104 <;> norm_num
  let x106 : ℝ := (1 / 1)-(370313 / 1000000)
  have hx106 : Bounds (629687 / 1000000) (629687 / 1000000) x106 := by
    exact hx105
  let x107 : ℝ := -(370313 / 1000000)
  have hx107 : Bounds (-370313 / 1000000) (-370313 / 1000000) x107 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((370313 / 1000000) : ℝ))
  let x108 : ℝ := (1 / 1)+x107
  have hx108 : Bounds (629687 / 1000000) (629687 / 1000000) x108 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx107 <;> norm_num
  let x109 : ℝ := (1 / 1)-(370313 / 1000000)
  have hx109 : Bounds (629687 / 1000000) (629687 / 1000000) x109 := by
    exact hx108
  let x110 : ℝ := Real.log x109
  have hx110 : Bounds (-462532409 / 1000000000) (-57816551 / 125000000) x110 := by
    exact bounds_log hx109 (by norm_num) (by simpa only [div_one] using reflection_log_10.1) (by simpa only [div_one] using reflection_log_10.2)
  let x111 : ℝ := x106*x110
  have hx111 : Bounds (-145625322513 / 500000000000) (-72812661099 / 250000000000) x111 := by
    apply bounds_mul hx106 hx110 <;> norm_num
  let x112 : ℝ := x103+x111
  have hx112 : Bounds (140451638837 / 1000000000000) (70225820419 / 500000000000) x112 := by
    apply bounds_add hx103 hx111 <;> norm_num
  let x113 : ℝ := (2 / 1)⁻¹
  have hx113 : Bounds (1 / 2) (1 / 2) x113 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x114 : ℝ := x112*x113
  have hx114 : Bounds (35112909709 / 500000000000) (70225820419 / 1000000000000) x114 := by
    apply bounds_mul hx112 hx113 <;> norm_num
  let x115 : ℝ := x112/(2 / 1)
  have hx115 : Bounds (35112909709 / 500000000000) (70225820419 / 1000000000000) x115 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx114
  let x116 : ℝ := -x115
  have hx116 : Bounds (-70225820419 / 1000000000000) (-35112909709 / 500000000000) x116 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx115
  let x117 : ℝ := x99+x116
  have hx117 : Bounds (622921359581 / 1000000000000) (311460680791 / 500000000000) x117 := by
    apply bounds_add hx99 hx116 <;> norm_num
  let x118 : ℝ := x99-x115
  have hx118 : Bounds (622921359581 / 1000000000000) (311460680791 / 500000000000) x118 := by
    exact hx117
  let x119 : ℝ := biasE (370313 / 1000000)
  have hx119 : Bounds (622921359581 / 1000000000000) (311460680791 / 500000000000) x119 := by
    simpa +zetaDelta only [biasE, div_one] using hx118
  let x120 : ℝ := Real.log (2 / 1)
  have hx120 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x120 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x121 : ℝ := (1 / 1)+(371177 / 1000000)
  have hx121 : Bounds (1371177 / 1000000) (1371177 / 1000000) x121 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((371177 / 1000000) : ℝ)) <;> norm_num
  let x122 : ℝ := (1 / 1)+(371177 / 1000000)
  have hx122 : Bounds (1371177 / 1000000) (1371177 / 1000000) x122 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((371177 / 1000000) : ℝ)) <;> norm_num
  let x123 : ℝ := Real.log x122
  have hx123 : Bounds (63133899 / 200000000) (39458687 / 125000000) x123 := by
    exact bounds_log hx122 (by norm_num) (by simpa only [div_one] using reflection_log_11.1) (by simpa only [div_one] using reflection_log_11.2)
  let x124 : ℝ := x121*x123
  have hx124 : Bounds (86567750229 / 200000000000) (432838752517 / 1000000000000) x124 := by
    apply bounds_mul hx121 hx123 <;> norm_num
  let x125 : ℝ := -(371177 / 1000000)
  have hx125 : Bounds (-371177 / 1000000) (-371177 / 1000000) x125 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((371177 / 1000000) : ℝ))
  let x126 : ℝ := (1 / 1)+x125
  have hx126 : Bounds (628823 / 1000000) (628823 / 1000000) x126 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx125 <;> norm_num
  let x127 : ℝ := (1 / 1)-(371177 / 1000000)
  have hx127 : Bounds (628823 / 1000000) (628823 / 1000000) x127 := by
    exact hx126
  let x128 : ℝ := -(371177 / 1000000)
  have hx128 : Bounds (-371177 / 1000000) (-371177 / 1000000) x128 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((371177 / 1000000) : ℝ))
  let x129 : ℝ := (1 / 1)+x128
  have hx129 : Bounds (628823 / 1000000) (628823 / 1000000) x129 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx128 <;> norm_num
  let x130 : ℝ := (1 / 1)-(371177 / 1000000)
  have hx130 : Bounds (628823 / 1000000) (628823 / 1000000) x130 := by
    exact hx129
  let x131 : ℝ := Real.log x130
  have hx131 : Bounds (-463905461 / 1000000000) (-23195273 / 50000000) x131 := by
    exact bounds_log hx130 (by norm_num) (by simpa only [div_one] using reflection_log_12.1) (by simpa only [div_one] using reflection_log_12.2)
  let x132 : ℝ := x127*x131
  have hx132 : Bounds (-291714423703 / 1000000000000) (-291714423073 / 1000000000000) x132 := by
    apply bounds_mul hx127 hx131 <;> norm_num
  let x133 : ℝ := x124+x132
  have hx133 : Bounds (70562163721 / 500000000000) (35281082361 / 250000000000) x133 := by
    apply bounds_add hx124 hx132 <;> norm_num
  let x134 : ℝ := (2 / 1)⁻¹
  have hx134 : Bounds (1 / 2) (1 / 2) x134 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x135 : ℝ := x133*x134
  have hx135 : Bounds (70562163721 / 1000000000000) (35281082361 / 500000000000) x135 := by
    apply bounds_mul hx133 hx134 <;> norm_num
  let x136 : ℝ := x133/(2 / 1)
  have hx136 : Bounds (70562163721 / 1000000000000) (35281082361 / 500000000000) x136 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx135
  let x137 : ℝ := -x136
  have hx137 : Bounds (-35281082361 / 500000000000) (-70562163721 / 1000000000000) x137 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx136
  let x138 : ℝ := x120+x137
  have hx138 : Bounds (311292507639 / 500000000000) (622585017279 / 1000000000000) x138 := by
    apply bounds_add hx120 hx137 <;> norm_num
  let x139 : ℝ := x120-x136
  have hx139 : Bounds (311292507639 / 500000000000) (622585017279 / 1000000000000) x139 := by
    exact hx138
  let x140 : ℝ := biasE (371177 / 1000000)
  have hx140 : Bounds (311292507639 / 500000000000) (622585017279 / 1000000000000) x140 := by
    simpa +zetaDelta only [biasE, div_one] using hx139
  let y : ℝ := 1 - 2 * entropyInverse ((1 + H (2*m - 1/2))/2)
  have hLh' : Real.log 2 * ((1 + H (2*m - 1/2))/2) = x98 := by
    simpa +zetaDelta only [div_one] using hLh
  have hy : Bounds (370313 / 1000000) (371177 / 1000000) y := by
    apply entropyInverseBias_bracket
    · exact div_nonneg (add_nonneg zero_le_one
        (H_nonneg (by linarith [hm.1]) (by linarith [hm.2]))) two_pos.le
    · linarith [H_le_one (2*m-1/2)]
    · norm_num
    · norm_num
    · norm_num
    · have h1 : biasE (371177 / 1000000) ≤ (622585017279 / 1000000000000) := hx140.2
      have h2 : (622585410489 / 1000000000000) ≤ x98 := hx98.1
      linarith [hLh']
    · have h1 : x98 ≤ (622921326133 / 1000000000000) := hx98.2
      have h2 : (622921359581 / 1000000000000) ≤ biasE (370313 / 1000000) := hx119.1
      linarith [hLh']
  let x141 : ℝ := x3⁻¹
  have hx141 : Bounds (60286360211 / 15625000000) (773413897281 / 200000000000) x141 := by
    apply bounds_inv hx3 <;> norm_num
  let x142 : ℝ := x98*x141
  have hx142 : Bounds (1201069066203 / 500000000000) (30111000659 / 12500000000) x142 := by
    apply bounds_mul hx98 hx141 <;> norm_num
  let x143 : ℝ := x98/x3
  have hx143 : Bounds (1201069066203 / 500000000000) (30111000659 / 12500000000) x143 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx142
  let x144 : ℝ := Real.log (2 / 1)
  have hx144 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x144 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x145 : ℝ := (1 / 1)+(136087 / 500000)
  have hx145 : Bounds (636087 / 500000) (636087 / 500000) x145 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((136087 / 500000) : ℝ)) <;> norm_num
  let x146 : ℝ := (1 / 1)+(136087 / 500000)
  have hx146 : Bounds (636087 / 500000) (636087 / 500000) x146 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((136087 / 500000) : ℝ)) <;> norm_num
  let x147 : ℝ := Real.log x146
  have hx147 : Bounds (15045453 / 62500000) (240727249 / 1000000000) x147 := by
    exact bounds_log hx146 (by norm_num) (by simpa only [div_one] using reflection_log_13.1) (by simpa only [div_one] using reflection_log_13.2)
  let x148 : ℝ := x145*x147
  have hx148 : Bounds (306246945997 / 1000000000000) (30624694727 / 100000000000) x148 := by
    apply bounds_mul hx145 hx147 <;> norm_num
  let x149 : ℝ := -(136087 / 500000)
  have hx149 : Bounds (-136087 / 500000) (-136087 / 500000) x149 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((136087 / 500000) : ℝ))
  let x150 : ℝ := (1 / 1)+x149
  have hx150 : Bounds (363913 / 500000) (363913 / 500000) x150 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx149 <;> norm_num
  let x151 : ℝ := (1 / 1)-(136087 / 500000)
  have hx151 : Bounds (363913 / 500000) (363913 / 500000) x151 := by
    exact hx150
  let x152 : ℝ := -(136087 / 500000)
  have hx152 : Bounds (-136087 / 500000) (-136087 / 500000) x152 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((136087 / 500000) : ℝ))
  let x153 : ℝ := (1 / 1)+x152
  have hx153 : Bounds (363913 / 500000) (363913 / 500000) x153 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx152 <;> norm_num
  let x154 : ℝ := (1 / 1)-(136087 / 500000)
  have hx154 : Bounds (363913 / 500000) (363913 / 500000) x154 := by
    exact hx153
  let x155 : ℝ := Real.log x154
  have hx155 : Bounds (-317693271 / 1000000000) (-31769327 / 100000000) x155 := by
    exact bounds_log hx154 (by norm_num) (by simpa only [div_one] using reflection_log_14.1) (by simpa only [div_one] using reflection_log_14.2)
  let x156 : ℝ := x151*x155
  have hx156 : Bounds (-231225422659 / 1000000000000) (-231225421931 / 1000000000000) x156 := by
    apply bounds_mul hx151 hx155 <;> norm_num
  let x157 : ℝ := x148+x156
  have hx157 : Bounds (37510761669 / 500000000000) (75021525339 / 1000000000000) x157 := by
    apply bounds_add hx148 hx156 <;> norm_num
  let x158 : ℝ := (2 / 1)⁻¹
  have hx158 : Bounds (1 / 2) (1 / 2) x158 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x159 : ℝ := x157*x158
  have hx159 : Bounds (37510761669 / 1000000000000) (3751076267 / 100000000000) x159 := by
    apply bounds_mul hx157 hx158 <;> norm_num
  let x160 : ℝ := x157/(2 / 1)
  have hx160 : Bounds (37510761669 / 1000000000000) (3751076267 / 100000000000) x160 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx159
  let x161 : ℝ := -x160
  have hx161 : Bounds (-3751076267 / 100000000000) (-37510761669 / 1000000000000) x161 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx160
  let x162 : ℝ := x144+x161
  have hx162 : Bounds (65563641733 / 100000000000) (655636419331 / 1000000000000) x162 := by
    apply bounds_add hx144 hx161 <;> norm_num
  let x163 : ℝ := x144-x160
  have hx163 : Bounds (65563641733 / 100000000000) (655636419331 / 1000000000000) x163 := by
    exact hx162
  let x164 : ℝ := biasE (136087 / 500000)
  have hx164 : Bounds (65563641733 / 100000000000) (655636419331 / 1000000000000) x164 := by
    simpa +zetaDelta only [biasE, div_one] using hx163
  let x165 : ℝ := Real.log (2 / 1)
  have hx165 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x165 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x166 : ℝ := (1 / 1)+(272859 / 1000000)
  have hx166 : Bounds (1272859 / 1000000) (1272859 / 1000000) x166 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((272859 / 1000000) : ℝ)) <;> norm_num
  let x167 : ℝ := (1 / 1)+(272859 / 1000000)
  have hx167 : Bounds (1272859 / 1000000) (1272859 / 1000000) x167 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((272859 / 1000000) : ℝ)) <;> norm_num
  let x168 : ℝ := Real.log x167
  have hx168 : Bounds (241265551 / 1000000000) (15079097 / 62500000) x168 := by
    exact bounds_log hx167 (by norm_num) (by simpa only [div_one] using reflection_log_15.1) (by simpa only [div_one] using reflection_log_15.2)
  let x169 : ℝ := x166*x168
  have hx169 : Bounds (15354851399 / 50000000000) (153548514627 / 500000000000) x169 := by
    apply bounds_mul hx166 hx168 <;> norm_num
  let x170 : ℝ := -(272859 / 1000000)
  have hx170 : Bounds (-272859 / 1000000) (-272859 / 1000000) x170 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((272859 / 1000000) : ℝ))
  let x171 : ℝ := (1 / 1)+x170
  have hx171 : Bounds (727141 / 1000000) (727141 / 1000000) x171 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx170 <;> norm_num
  let x172 : ℝ := (1 / 1)-(272859 / 1000000)
  have hx172 : Bounds (727141 / 1000000) (727141 / 1000000) x172 := by
    exact hx171
  let x173 : ℝ := -(272859 / 1000000)
  have hx173 : Bounds (-272859 / 1000000) (-272859 / 1000000) x173 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((272859 / 1000000) : ℝ))
  let x174 : ℝ := (1 / 1)+x173
  have hx174 : Bounds (727141 / 1000000) (727141 / 1000000) x174 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx173 <;> norm_num
  let x175 : ℝ := (1 / 1)-(272859 / 1000000)
  have hx175 : Bounds (727141 / 1000000) (727141 / 1000000) x175 := by
    exact hx174
  let x176 : ℝ := Real.log x175
  have hx176 : Bounds (-318634873 / 1000000000) (-39829359 / 125000000) x176 := by
    exact bounds_log hx175 (by norm_num) (by simpa only [div_one] using reflection_log_16.1) (by simpa only [div_one] using reflection_log_16.2)
  let x177 : ℝ := x172*x176
  have hx177 : Bounds (-231692480189 / 1000000000000) (-11584623973 / 50000000000) x177 := by
    apply bounds_mul hx172 hx176 <;> norm_num
  let x178 : ℝ := x169+x177
  have hx178 : Bounds (75404547791 / 1000000000000) (37702274897 / 500000000000) x178 := by
    apply bounds_add hx169 hx177 <;> norm_num
  let x179 : ℝ := (2 / 1)⁻¹
  have hx179 : Bounds (1 / 2) (1 / 2) x179 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x180 : ℝ := x178*x179
  have hx180 : Bounds (7540454779 / 200000000000) (37702274897 / 1000000000000) x180 := by
    apply bounds_mul hx178 hx179 <;> norm_num
  let x181 : ℝ := x178/(2 / 1)
  have hx181 : Bounds (7540454779 / 200000000000) (37702274897 / 1000000000000) x181 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx180
  let x182 : ℝ := -x181
  have hx182 : Bounds (-37702274897 / 1000000000000) (-7540454779 / 200000000000) x182 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx181
  let x183 : ℝ := x165+x182
  have hx183 : Bounds (655444905103 / 1000000000000) (131088981421 / 200000000000) x183 := by
    apply bounds_add hx165 hx182 <;> norm_num
  let x184 : ℝ := x165-x181
  have hx184 : Bounds (655444905103 / 1000000000000) (131088981421 / 200000000000) x184 := by
    exact hx183
  let x185 : ℝ := biasE (272859 / 1000000)
  have hx185 : Bounds (655444905103 / 1000000000000) (131088981421 / 200000000000) x185 := by
    simpa +zetaDelta only [biasE, div_one] using hx184
  let x186 : ℝ := x143*(136087 / 500000)
  have hx186 : Bounds (653799544049 / 1000000000000) (65563451947 / 100000000000) x186 := by
    apply bounds_mul hx143 (bounds_const ((136087 / 500000) : ℝ)) <;> norm_num
  let x187 : ℝ := x143*(272859 / 1000000)
  have hx187 : Bounds (65544500867 / 100000000000) (328642301153 / 500000000000) x187 := by
    apply bounds_mul hx143 (bounds_const ((272859 / 1000000) : ℝ)) <;> norm_num
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
  have hc : Bounds (136087 / 500000) (272859 / 1000000) c := by
    apply contact_bracket hc0 hcMem.2.le (by norm_num) (by norm_num) (by norm_num)
      (show 0 < x143 by linarith [hx143.1]) hcEq
    · have h1 : x143 * (136087 / 500000) ≤ (65563451947 / 100000000000) := hx186.2
      have h2 : (65563641733 / 100000000000) ≤ biasE (136087 / 500000) := hx164.1
      linarith
    · have h1 : biasE (272859 / 1000000) ≤ (131088981421 / 200000000000) := hx185.2
      have h2 : (65544500867 / 100000000000) ≤ x143 * (272859 / 1000000) := hx187.1
      linarith
  let x188 : ℝ := (1 / 1)+y
  have hx188 : Bounds (1370313 / 1000000) (1371177 / 1000000) x188 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hy <;> norm_num
  let x189 : ℝ := -y
  have hx189 : Bounds (-371177 / 1000000) (-370313 / 1000000) x189 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hy
  let x190 : ℝ := (1 / 1)+x189
  have hx190 : Bounds (628823 / 1000000) (629687 / 1000000) x190 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx189 <;> norm_num
  let x191 : ℝ := (1 / 1)-y
  have hx191 : Bounds (628823 / 1000000) (629687 / 1000000) x191 := by
    exact hx190
  let x192 : ℝ := x191⁻¹
  have hx192 : Bounds (1588090591039 / 1000000000000) (397568155109 / 250000000000) x192 := by
    apply bounds_inv hx191 <;> norm_num
  let x193 : ℝ := x188*x192
  have hx193 : Bounds (1088090591039 / 500000000000) (272568155109 / 125000000000) x193 := by
    apply bounds_mul hx188 hx192 <;> norm_num
  let x194 : ℝ := x188/x191
  have hx194 : Bounds (1088090591039 / 500000000000) (272568155109 / 125000000000) x194 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx193
  let x195 : ℝ := Real.log x194
  have hx195 : Bounds (194392897 / 250000000) (779574957 / 1000000000) x195 := by
    exact bounds_log hx194 (by norm_num) (by simpa only [div_one] using reflection_log_17.1) (by simpa only [div_one] using reflection_log_18.2)
  let x196 : ℝ := (2 / 1)⁻¹
  have hx196 : Bounds (1 / 2) (1 / 2) x196 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x197 : ℝ := x195*x196
  have hx197 : Bounds (194392897 / 500000000) (779574957 / 2000000000) x197 := by
    apply bounds_mul hx195 hx196 <;> norm_num
  let x198 : ℝ := x195/(2 / 1)
  have hx198 : Bounds (194392897 / 500000000) (779574957 / 2000000000) x198 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx197
  let x199 : ℝ := (1 / 1)+c
  have hx199 : Bounds (636087 / 500000) (1272859 / 1000000) x199 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hc <;> norm_num
  let x200 : ℝ := -c
  have hx200 : Bounds (-272859 / 1000000) (-136087 / 500000) x200 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hc
  let x201 : ℝ := (1 / 1)+x200
  have hx201 : Bounds (727141 / 1000000) (363913 / 500000) x201 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx200 <;> norm_num
  let x202 : ℝ := (1 / 1)-c
  have hx202 : Bounds (727141 / 1000000) (363913 / 500000) x202 := by
    exact hx201
  let x203 : ℝ := x202⁻¹
  have hx203 : Bounds (1373954763913 / 1000000000000) (171906136499 / 125000000000) x203 := by
    apply bounds_inv hx202 <;> norm_num
  let x204 : ℝ := x199*x203
  have hx204 : Bounds (873954763913 / 500000000000) (109406136499 / 62500000000) x204 := by
    apply bounds_mul hx199 hx203 <;> norm_num
  let x205 : ℝ := x199/x202
  have hx205 : Bounds (873954763913 / 500000000000) (109406136499 / 62500000000) x205 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx204
  let x206 : ℝ := Real.log x205
  have hx206 : Bounds (279210259 / 500000000) (69987553 / 125000000) x206 := by
    exact bounds_log hx205 (by norm_num) (by simpa only [div_one] using reflection_log_19.1) (by simpa only [div_one] using reflection_log_20.2)
  let x207 : ℝ := (2 / 1)⁻¹
  have hx207 : Bounds (1 / 2) (1 / 2) x207 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x208 : ℝ := x206*x207
  have hx208 : Bounds (279210259 / 1000000000) (69987553 / 250000000) x208 := by
    apply bounds_mul hx206 hx207 <;> norm_num
  let x209 : ℝ := x206/(2 / 1)
  have hx209 : Bounds (279210259 / 1000000000) (69987553 / 250000000) x209 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx208
  let x210 : ℝ := (2 / 1)*x50
  have hx210 : Bounds (659173610797 / 500000000000) (131865767263 / 100000000000) x210 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx50 <;> norm_num
  let x211 : ℝ := (2 / 1)*x98
  have hx211 : Bounds (622585410489 / 500000000000) (622921326133 / 500000000000) x211 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx98 <;> norm_num
  let x212 : ℝ := -x211
  have hx212 : Bounds (-622921326133 / 500000000000) (-622585410489 / 500000000000) x212 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx211
  let x213 : ℝ := x210+x212
  have hx213 : Bounds (4531535583 / 62500000000) (18371712913 / 250000000000) x213 := by
    apply bounds_add hx210 hx212 <;> norm_num
  let x214 : ℝ := x210-x211
  have hx214 : Bounds (4531535583 / 62500000000) (18371712913 / 250000000000) x214 := by
    exact hx213
  let x215 : ℝ := y*x198
  have hx215 : Bounds (143972433733 / 1000000000000) (36170036727 / 250000000000) x215 := by
    apply bounds_mul hy hx198 <;> norm_num
  let x216 : ℝ := -x215
  have hx216 : Bounds (-36170036727 / 250000000000) (-143972433733 / 1000000000000) x216 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx215
  let x217 : ℝ := x214+x216
  have hx217 : Bounds (-3608778879 / 50000000000) (-70485582081 / 1000000000000) x217 := by
    apply bounds_add hx214 hx216 <;> norm_num
  let x218 : ℝ := x214-x215
  have hx218 : Bounds (-3608778879 / 50000000000) (-70485582081 / 1000000000000) x218 := by
    exact hx217
  let x219 : ℝ := x3*x209
  have hx219 : Bounds (72202027913 / 1000000000000) (36278704231 / 500000000000) x219 := by
    apply bounds_mul hx3 hx209 <;> norm_num
  let x220 : ℝ := x218+x219
  have hx220 : Bounds (26450333 / 1000000000000) (2071826381 / 1000000000000) x220 := by
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

theorem acceptedCertificate : DoubleCapBiasCellCertificate (3793 / 10240) (949 / 2560) (fun m => (1 + H (2*m - 1/2))/2) where
  domain := by norm_num
  sound m hmLo hmHi := by
    exact cell_bias_nonneg m ⟨hmLo, hmHi⟩

theorem accepted_cell :
    ∀ m, (3793 / 10240) ≤ m → m ≤ (949 / 2560) → 0 ≤ doubleCapHighResidual m := by
  intro m hmLo hmHi
  unfold doubleCapHighResidual
  apply doubleCapEndpointResidual_nonneg_of_biasCell acceptedCertificate hmLo hmHi
  exact div_pos (by linarith [H_nonneg (by linarith : 0 ≤ 2*m-1/2) (by linarith : 2*m-1/2 ≤ 1)]) two_pos

#print axioms cell_bias_nonneg
#print axioms accepted_cell

end GeneralCK.Certificates.DoubleCapMiddle.Cell0277

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0278 =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0278
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Reflection
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem cell_bias_nonneg (m : ℝ) (hm : Bounds (949 / 2560) (3799 / 10240) m) :
    let h := (1 + H (2*m - 1/2))/2
    let x := 1-2*m
    let y := 1-2*entropyInverse h
    let c := regularContact (x/(Real.log 2*h))
    0 ≤ 2*(biasE x-Real.log 2*h)-y*SmallMean.A y+x*SmallMean.A c := by
  have hEq : biasE (2-4*m) = Real.log 2 * H (2*m-1/2) := by
    have hmstrict : 1/4 < m := by
      have hlo : (1/4 : ℝ) < (949 / 2560) := by norm_num
      exact lt_of_lt_of_le hlo hm.1
    rw [show 2-4*m = 1-2*(2*m-1/2) by ring,
      GeneralCK.Correction.Natural.biasE_probability (by linarith [hmstrict]) (by linarith [hm.2]),
      GeneralCK.Certificates.Mixed.hn_eq_H_mul_log]
    ring
  have hLh : Real.log 2 * ((1 + H (2*m - 1/2))/2) = (Real.log 2 + biasE (2-4*m))/2 := by
    rw [hEq]
    ring
  let x0 : ℝ := (2 / 1)*m
  have hx0 : Bounds (949 / 1280) (3799 / 5120) x0 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hm <;> norm_num
  let x1 : ℝ := -x0
  have hx1 : Bounds (-3799 / 5120) (-949 / 1280) x1 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx0
  let x2 : ℝ := (1 / 1)+x1
  have hx2 : Bounds (1321 / 5120) (331 / 1280) x2 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx1 <;> norm_num
  let x3 : ℝ := (1 / 1)-x0
  have hx3 : Bounds (1321 / 5120) (331 / 1280) x3 := by
    exact hx2
  let x4 : ℝ := (4 / 1)*m
  have hx4 : Bounds (949 / 640) (3799 / 2560) x4 := by
    apply bounds_mul (bounds_const ((4 / 1) : ℝ)) hm <;> norm_num
  let x5 : ℝ := -x4
  have hx5 : Bounds (-3799 / 2560) (-949 / 640) x5 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx4
  let x6 : ℝ := (2 / 1)+x5
  have hx6 : Bounds (1321 / 2560) (331 / 640) x6 := by
    apply bounds_add (bounds_const ((2 / 1) : ℝ)) hx5 <;> norm_num
  let x7 : ℝ := (2 / 1)-x4
  have hx7 : Bounds (1321 / 2560) (331 / 640) x7 := by
    exact hx6
  let x8 : ℝ := Real.log (2 / 1)
  have hx8 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x8 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x9 : ℝ := (1 / 1)+(331 / 1280)
  have hx9 : Bounds (1611 / 1280) (1611 / 1280) x9 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((331 / 1280) : ℝ)) <;> norm_num
  let x10 : ℝ := (1 / 1)+(331 / 1280)
  have hx10 : Bounds (1611 / 1280) (1611 / 1280) x10 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((331 / 1280) : ℝ)) <;> norm_num
  let x11 : ℝ := Real.log x10
  have hx11 : Bounds (114997513 / 500000000) (229995027 / 1000000000) x11 := by
    exact bounds_log hx10 (by norm_num) (by simpa only [div_one] using reflection_log_1.1) (by simpa only [div_one] using reflection_log_1.2)
  let x12 : ℝ := x9*x11
  have hx12 : Bounds (144735151127 / 500000000000) (144735151757 / 500000000000) x12 := by
    apply bounds_mul hx9 hx11 <;> norm_num
  let x13 : ℝ := -(331 / 1280)
  have hx13 : Bounds (-331 / 1280) (-331 / 1280) x13 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((331 / 1280) : ℝ))
  let x14 : ℝ := (1 / 1)+x13
  have hx14 : Bounds (949 / 1280) (949 / 1280) x14 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx13 <;> norm_num
  let x15 : ℝ := (1 / 1)-(331 / 1280)
  have hx15 : Bounds (949 / 1280) (949 / 1280) x15 := by
    exact hx14
  let x16 : ℝ := -(331 / 1280)
  have hx16 : Bounds (-331 / 1280) (-331 / 1280) x16 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((331 / 1280) : ℝ))
  let x17 : ℝ := (1 / 1)+x16
  have hx17 : Bounds (949 / 1280) (949 / 1280) x17 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx16 <;> norm_num
  let x18 : ℝ := (1 / 1)-(331 / 1280)
  have hx18 : Bounds (949 / 1280) (949 / 1280) x18 := by
    exact hx17
  let x19 : ℝ := Real.log x18
  have hx19 : Bounds (-299206559 / 1000000000) (-149603279 / 500000000) x19 := by
    exact bounds_log hx18 (by norm_num) (by simpa only [div_one] using reflection_log_2.1) (by simpa only [div_one] using reflection_log_2.2)
  let x20 : ℝ := x15*x19
  have hx20 : Bounds (-55458403221 / 250000000000) (-110916806071 / 500000000000) x20 := by
    apply bounds_mul hx15 hx19 <;> norm_num
  let x21 : ℝ := x12+x20
  have hx21 : Bounds (6763668937 / 100000000000) (16909172843 / 250000000000) x21 := by
    apply bounds_add hx12 hx20 <;> norm_num
  let x22 : ℝ := (2 / 1)⁻¹
  have hx22 : Bounds (1 / 2) (1 / 2) x22 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x23 : ℝ := x21*x22
  have hx23 : Bounds (6763668937 / 200000000000) (16909172843 / 500000000000) x23 := by
    apply bounds_mul hx21 hx22 <;> norm_num
  let x24 : ℝ := x21/(2 / 1)
  have hx24 : Bounds (6763668937 / 200000000000) (16909172843 / 500000000000) x24 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx23
  let x25 : ℝ := -x24
  have hx25 : Bounds (-16909172843 / 500000000000) (-6763668937 / 200000000000) x25 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx24
  let x26 : ℝ := x8+x25
  have hx26 : Bounds (329664417157 / 500000000000) (131865767263 / 200000000000) x26 := by
    apply bounds_add hx8 hx25 <;> norm_num
  let x27 : ℝ := x8-x24
  have hx27 : Bounds (329664417157 / 500000000000) (131865767263 / 200000000000) x27 := by
    exact hx26
  let x28 : ℝ := biasE (331 / 1280)
  have hx28 : Bounds (329664417157 / 500000000000) (131865767263 / 200000000000) x28 := by
    simpa +zetaDelta only [biasE, div_one] using hx27
  let x29 : ℝ := Real.log (2 / 1)
  have hx29 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x29 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x30 : ℝ := (1 / 1)+(1321 / 5120)
  have hx30 : Bounds (6441 / 5120) (6441 / 5120) x30 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1321 / 5120) : ℝ)) <;> norm_num
  let x31 : ℝ := (1 / 1)+(1321 / 5120)
  have hx31 : Bounds (6441 / 5120) (6441 / 5120) x31 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1321 / 5120) : ℝ)) <;> norm_num
  let x32 : ℝ := Real.log x31
  have hx32 : Bounds (28691171 / 125000000) (229529369 / 1000000000) x32 := by
    exact bounds_log hx31 (by norm_num) (by simpa only [div_one] using reflection_log_3.1) (by simpa only [div_one] using reflection_log_3.2)
  let x33 : ℝ := x30*x32
  have hx33 : Bounds (144374869071 / 500000000000) (288749739401 / 1000000000000) x33 := by
    apply bounds_mul hx30 hx32 <;> norm_num
  let x34 : ℝ := -(1321 / 5120)
  have hx34 : Bounds (-1321 / 5120) (-1321 / 5120) x34 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1321 / 5120) : ℝ))
  let x35 : ℝ := (1 / 1)+x34
  have hx35 : Bounds (3799 / 5120) (3799 / 5120) x35 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx34 <;> norm_num
  let x36 : ℝ := (1 / 1)-(1321 / 5120)
  have hx36 : Bounds (3799 / 5120) (3799 / 5120) x36 := by
    exact hx35
  let x37 : ℝ := -(1321 / 5120)
  have hx37 : Bounds (-1321 / 5120) (-1321 / 5120) x37 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1321 / 5120) : ℝ))
  let x38 : ℝ := (1 / 1)+x37
  have hx38 : Bounds (3799 / 5120) (3799 / 5120) x38 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx37 <;> norm_num
  let x39 : ℝ := (1 / 1)-(1321 / 5120)
  have hx39 : Bounds (3799 / 5120) (3799 / 5120) x39 := by
    exact hx38
  let x40 : ℝ := Real.log x39
  have hx40 : Bounds (-59683313 / 200000000) (-74604141 / 250000000) x40 := by
    exact bounds_log hx39 (by norm_num) (by simpa only [div_one] using reflection_log_4.1) (by simpa only [div_one] using reflection_log_4.2)
  let x41 : ℝ := x36*x40
  have hx41 : Bounds (-221422759851 / 1000000000000) (-55355689777 / 250000000000) x41 := by
    apply bounds_mul hx36 hx40 <;> norm_num
  let x42 : ℝ := x33+x41
  have hx42 : Bounds (67326978291 / 1000000000000) (67326980293 / 1000000000000) x42 := by
    apply bounds_add hx33 hx41 <;> norm_num
  let x43 : ℝ := (2 / 1)⁻¹
  have hx43 : Bounds (1 / 2) (1 / 2) x43 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x44 : ℝ := x42*x43
  have hx44 : Bounds (6732697829 / 200000000000) (33663490147 / 1000000000000) x44 := by
    apply bounds_mul hx42 hx43 <;> norm_num
  let x45 : ℝ := x42/(2 / 1)
  have hx45 : Bounds (6732697829 / 200000000000) (33663490147 / 1000000000000) x45 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx44
  let x46 : ℝ := -x45
  have hx46 : Bounds (-33663490147 / 1000000000000) (-6732697829 / 200000000000) x46 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx45
  let x47 : ℝ := x29+x46
  have hx47 : Bounds (659483689853 / 1000000000000) (131896738371 / 200000000000) x47 := by
    apply bounds_add hx29 hx46 <;> norm_num
  let x48 : ℝ := x29-x45
  have hx48 : Bounds (659483689853 / 1000000000000) (131896738371 / 200000000000) x48 := by
    exact hx47
  let x49 : ℝ := biasE (1321 / 5120)
  have hx49 : Bounds (659483689853 / 1000000000000) (131896738371 / 200000000000) x49 := by
    simpa +zetaDelta only [biasE, div_one] using hx48
  let x50 : ℝ := biasE x3
  have hx50 : Bounds (329664417157 / 500000000000) (131896738371 / 200000000000) x50 := by
    exact bounds_biasE hx3 (by norm_num) (by norm_num) hx28.1 hx49.2
  let x51 : ℝ := Real.log (2 / 1)
  have hx51 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x51 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x52 : ℝ := (1 / 1)+(331 / 640)
  have hx52 : Bounds (971 / 640) (971 / 640) x52 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((331 / 640) : ℝ)) <;> norm_num
  let x53 : ℝ := (1 / 1)+(331 / 640)
  have hx53 : Bounds (971 / 640) (971 / 640) x53 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((331 / 640) : ℝ)) <;> norm_num
  let x54 : ℝ := Real.log x53
  have hx54 : Bounds (416858291 / 1000000000) (104214573 / 250000000) x54 := by
    exact bounds_log hx53 (by norm_num) (by simpa only [div_one] using reflection_log_5.1) (by simpa only [div_one] using reflection_log_5.2)
  let x55 : ℝ := x52*x54
  have hx55 : Bounds (79056523547 / 125000000000) (316226094947 / 500000000000) x55 := by
    apply bounds_mul hx52 hx54 <;> norm_num
  let x56 : ℝ := -(331 / 640)
  have hx56 : Bounds (-331 / 640) (-331 / 640) x56 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((331 / 640) : ℝ))
  let x57 : ℝ := (1 / 1)+x56
  have hx57 : Bounds (309 / 640) (309 / 640) x57 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx56 <;> norm_num
  let x58 : ℝ := (1 / 1)-(331 / 640)
  have hx58 : Bounds (309 / 640) (309 / 640) x58 := by
    exact hx57
  let x59 : ℝ := -(331 / 640)
  have hx59 : Bounds (-331 / 640) (-331 / 640) x59 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((331 / 640) : ℝ))
  let x60 : ℝ := (1 / 1)+x59
  have hx60 : Bounds (309 / 640) (309 / 640) x60 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx59 <;> norm_num
  let x61 : ℝ := (1 / 1)-(331 / 640)
  have hx61 : Bounds (309 / 640) (309 / 640) x61 := by
    exact hx60
  let x62 : ℝ := Real.log x61
  have hx62 : Bounds (-7281269 / 10000000) (-364063449 / 500000000) x62 := by
    exact bounds_log hx61 (by norm_num) (by simpa only [div_one] using reflection_log_6.1) (by simpa only [div_one] using reflection_log_6.2)
  let x63 : ℝ := x58*x62
  have hx63 : Bounds (-351548768907 / 1000000000000) (-17577438397 / 50000000000) x63 := by
    apply bounds_mul hx58 hx62 <;> norm_num
  let x64 : ℝ := x55+x63
  have hx64 : Bounds (280903419469 / 1000000000000) (140451710977 / 500000000000) x64 := by
    apply bounds_add hx55 hx63 <;> norm_num
  let x65 : ℝ := (2 / 1)⁻¹
  have hx65 : Bounds (1 / 2) (1 / 2) x65 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x66 : ℝ := x64*x65
  have hx66 : Bounds (70225854867 / 500000000000) (140451710977 / 1000000000000) x66 := by
    apply bounds_mul hx64 hx65 <;> norm_num
  let x67 : ℝ := x64/(2 / 1)
  have hx67 : Bounds (70225854867 / 500000000000) (140451710977 / 1000000000000) x67 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx66
  let x68 : ℝ := -x67
  have hx68 : Bounds (-140451710977 / 1000000000000) (-70225854867 / 500000000000) x68 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx67
  let x69 : ℝ := x51+x68
  have hx69 : Bounds (552695469023 / 1000000000000) (276347735633 / 500000000000) x69 := by
    apply bounds_add hx51 hx68 <;> norm_num
  let x70 : ℝ := x51-x67
  have hx70 : Bounds (552695469023 / 1000000000000) (276347735633 / 500000000000) x70 := by
    exact hx69
  let x71 : ℝ := biasE (331 / 640)
  have hx71 : Bounds (552695469023 / 1000000000000) (276347735633 / 500000000000) x71 := by
    simpa +zetaDelta only [biasE, div_one] using hx70
  let x72 : ℝ := Real.log (2 / 1)
  have hx72 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x72 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x73 : ℝ := (1 / 1)+(1321 / 2560)
  have hx73 : Bounds (3881 / 2560) (3881 / 2560) x73 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1321 / 2560) : ℝ)) <;> norm_num
  let x74 : ℝ := (1 / 1)+(1321 / 2560)
  have hx74 : Bounds (3881 / 2560) (3881 / 2560) x74 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1321 / 2560) : ℝ)) <;> norm_num
  let x75 : ℝ := Real.log x74
  have hx75 : Bounds (416085593 / 1000000000) (208042797 / 500000000) x75 := by
    exact bounds_log hx74 (by norm_num) (by simpa only [div_one] using reflection_log_7.1) (by simpa only [div_one] using reflection_log_7.2)
  let x76 : ℝ := x73*x75
  have hx76 : Bounds (25231690413 / 40000000000) (315396130921 / 500000000000) x76 := by
    apply bounds_mul hx73 hx75 <;> norm_num
  let x77 : ℝ := -(1321 / 2560)
  have hx77 : Bounds (-1321 / 2560) (-1321 / 2560) x77 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1321 / 2560) : ℝ))
  let x78 : ℝ := (1 / 1)+x77
  have hx78 : Bounds (1239 / 2560) (1239 / 2560) x78 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx77 <;> norm_num
  let x79 : ℝ := (1 / 1)-(1321 / 2560)
  have hx79 : Bounds (1239 / 2560) (1239 / 2560) x79 := by
    exact hx78
  let x80 : ℝ := -(1321 / 2560)
  have hx80 : Bounds (-1321 / 2560) (-1321 / 2560) x80 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1321 / 2560) : ℝ))
  let x81 : ℝ := (1 / 1)+x80
  have hx81 : Bounds (1239 / 2560) (1239 / 2560) x81 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx80 <;> norm_num
  let x82 : ℝ := (1 / 1)-(1321 / 2560)
  have hx82 : Bounds (1239 / 2560) (1239 / 2560) x82 := by
    exact hx81
  let x83 : ℝ := Real.log x82
  have hx83 : Bounds (-725702657 / 1000000000) (-145140531 / 200000000) x83 := by
    exact bounds_log hx82 (by norm_num) (by simpa only [div_one] using reflection_log_8.1) (by simpa only [div_one] using reflection_log_8.2)
  let x84 : ℝ := x79*x83
  have hx84 : Bounds (-87807186721 / 250000000000) (-87807186479 / 250000000000) x84 := by
    apply bounds_mul hx79 hx83 <;> norm_num
  let x85 : ℝ := x76+x84
  have hx85 : Bounds (279563513441 / 1000000000000) (139781757963 / 500000000000) x85 := by
    apply bounds_add hx76 hx84 <;> norm_num
  let x86 : ℝ := (2 / 1)⁻¹
  have hx86 : Bounds (1 / 2) (1 / 2) x86 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x87 : ℝ := x85*x86
  have hx87 : Bounds (1747271959 / 12500000000) (139781757963 / 1000000000000) x87 := by
    apply bounds_mul hx85 hx86 <;> norm_num
  let x88 : ℝ := x85/(2 / 1)
  have hx88 : Bounds (1747271959 / 12500000000) (139781757963 / 1000000000000) x88 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx87
  let x89 : ℝ := -x88
  have hx89 : Bounds (-139781757963 / 1000000000000) (-1747271959 / 12500000000) x89 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx88
  let x90 : ℝ := x72+x89
  have hx90 : Bounds (553365422037 / 1000000000000) (13834135607 / 25000000000) x90 := by
    apply bounds_add hx72 hx89 <;> norm_num
  let x91 : ℝ := x72-x88
  have hx91 : Bounds (553365422037 / 1000000000000) (13834135607 / 25000000000) x91 := by
    exact hx90
  let x92 : ℝ := biasE (1321 / 2560)
  have hx92 : Bounds (553365422037 / 1000000000000) (13834135607 / 25000000000) x92 := by
    simpa +zetaDelta only [biasE, div_one] using hx91
  let x93 : ℝ := biasE x7
  have hx93 : Bounds (552695469023 / 1000000000000) (13834135607 / 25000000000) x93 := by
    exact bounds_biasE hx7 (by norm_num) (by norm_num) hx71.1 hx92.2
  let x94 : ℝ := Real.log (2 / 1)
  have hx94 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x94 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x95 : ℝ := x94+x93
  have hx95 : Bounds (1245842649023 / 1000000000000) (7790703783 / 6250000000) x95 := by
    apply bounds_add hx94 hx93 <;> norm_num
  let x96 : ℝ := (2 / 1)⁻¹
  have hx96 : Bounds (1 / 2) (1 / 2) x96 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x97 : ℝ := x95*x96
  have hx97 : Bounds (622921324511 / 1000000000000) (7790703783 / 12500000000) x97 := by
    apply bounds_mul hx95 hx96 <;> norm_num
  let x98 : ℝ := x95/(2 / 1)
  have hx98 : Bounds (622921324511 / 1000000000000) (7790703783 / 12500000000) x98 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx97
  let x99 : ℝ := Real.log (2 / 1)
  have hx99 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x99 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x100 : ℝ := (1 / 1)+(7389 / 20000)
  have hx100 : Bounds (27389 / 20000) (27389 / 20000) x100 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((7389 / 20000) : ℝ)) <;> norm_num
  let x101 : ℝ := (1 / 1)+(7389 / 20000)
  have hx101 : Bounds (27389 / 20000) (27389 / 20000) x101 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((7389 / 20000) : ℝ)) <;> norm_num
  let x102 : ℝ := Real.log x101
  have hx102 : Bounds (314409199 / 1000000000) (786023 / 2500000) x102 := by
    exact bounds_log hx101 (by norm_num) (by simpa only [div_one] using reflection_log_9.1) (by simpa only [div_one] using reflection_log_9.2)
  let x103 : ℝ := x100*x102
  have hx103 : Bounds (43056767757 / 100000000000) (21528383947 / 50000000000) x103 := by
    apply bounds_mul hx100 hx102 <;> norm_num
  let x104 : ℝ := -(7389 / 20000)
  have hx104 : Bounds (-7389 / 20000) (-7389 / 20000) x104 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((7389 / 20000) : ℝ))
  let x105 : ℝ := (1 / 1)+x104
  have hx105 : Bounds (12611 / 20000) (12611 / 20000) x105 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx104 <;> norm_num
  let x106 : ℝ := (1 / 1)-(7389 / 20000)
  have hx106 : Bounds (12611 / 20000) (12611 / 20000) x106 := by
    exact hx105
  let x107 : ℝ := -(7389 / 20000)
  have hx107 : Bounds (-7389 / 20000) (-7389 / 20000) x107 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((7389 / 20000) : ℝ))
  let x108 : ℝ := (1 / 1)+x107
  have hx108 : Bounds (12611 / 20000) (12611 / 20000) x108 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx107 <;> norm_num
  let x109 : ℝ := (1 / 1)-(7389 / 20000)
  have hx109 : Bounds (12611 / 20000) (12611 / 20000) x109 := by
    exact hx108
  let x110 : ℝ := Real.log x109
  have hx110 : Bounds (-18446513 / 40000000) (-57645353 / 125000000) x110 := by
    exact bounds_log hx109 (by norm_num) (by simpa only [div_one] using reflection_log_10.1) (by simpa only [div_one] using reflection_log_10.2)
  let x111 : ℝ := x106*x110
  have hx111 : Bounds (-36348277413 / 125000000000) (-290786218673 / 1000000000000) x111 := by
    apply bounds_mul hx106 hx110 <;> norm_num
  let x112 : ℝ := x103+x111
  have hx112 : Bounds (69890729133 / 500000000000) (139781460267 / 1000000000000) x112 := by
    apply bounds_add hx103 hx111 <;> norm_num
  let x113 : ℝ := (2 / 1)⁻¹
  have hx113 : Bounds (1 / 2) (1 / 2) x113 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x114 : ℝ := x112*x113
  have hx114 : Bounds (69890729133 / 1000000000000) (34945365067 / 500000000000) x114 := by
    apply bounds_mul hx112 hx113 <;> norm_num
  let x115 : ℝ := x112/(2 / 1)
  have hx115 : Bounds (69890729133 / 1000000000000) (34945365067 / 500000000000) x115 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx114
  let x116 : ℝ := -x115
  have hx116 : Bounds (-34945365067 / 500000000000) (-69890729133 / 1000000000000) x116 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx115
  let x117 : ℝ := x99+x116
  have hx117 : Bounds (311628224933 / 500000000000) (623256451867 / 1000000000000) x117 := by
    apply bounds_add hx99 hx116 <;> norm_num
  let x118 : ℝ := x99-x115
  have hx118 : Bounds (311628224933 / 500000000000) (623256451867 / 1000000000000) x118 := by
    exact hx117
  let x119 : ℝ := biasE (7389 / 20000)
  have hx119 : Bounds (311628224933 / 500000000000) (623256451867 / 1000000000000) x119 := by
    simpa +zetaDelta only [biasE, div_one] using hx118
  let x120 : ℝ := Real.log (2 / 1)
  have hx120 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x120 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x121 : ℝ := (1 / 1)+(185157 / 500000)
  have hx121 : Bounds (685157 / 500000) (685157 / 500000) x121 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((185157 / 500000) : ℝ)) <;> norm_num
  let x122 : ℝ := (1 / 1)+(185157 / 500000)
  have hx122 : Bounds (685157 / 500000) (685157 / 500000) x122 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((185157 / 500000) : ℝ)) <;> norm_num
  let x123 : ℝ := Real.log x122
  have hx123 : Bounds (31503991 / 100000000) (315039911 / 1000000000) x123 := by
    exact bounds_log hx122 (by norm_num) (by simpa only [div_one] using reflection_log_11.1) (by simpa only [div_one] using reflection_log_11.2)
  let x124 : ℝ := x121*x123
  have hx124 : Bounds (431703599231 / 1000000000000) (431703600603 / 1000000000000) x124 := by
    apply bounds_mul hx121 hx123 <;> norm_num
  let x125 : ℝ := -(185157 / 500000)
  have hx125 : Bounds (-185157 / 500000) (-185157 / 500000) x125 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((185157 / 500000) : ℝ))
  let x126 : ℝ := (1 / 1)+x125
  have hx126 : Bounds (314843 / 500000) (314843 / 500000) x126 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx125 <;> norm_num
  let x127 : ℝ := (1 / 1)-(185157 / 500000)
  have hx127 : Bounds (314843 / 500000) (314843 / 500000) x127 := by
    exact hx126
  let x128 : ℝ := -(185157 / 500000)
  have hx128 : Bounds (-185157 / 500000) (-185157 / 500000) x128 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((185157 / 500000) : ℝ))
  let x129 : ℝ := (1 / 1)+x128
  have hx129 : Bounds (314843 / 500000) (314843 / 500000) x129 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx128 <;> norm_num
  let x130 : ℝ := (1 / 1)-(185157 / 500000)
  have hx130 : Bounds (314843 / 500000) (314843 / 500000) x130 := by
    exact hx129
  let x131 : ℝ := Real.log x130
  have hx131 : Bounds (-462533997 / 1000000000) (-115633499 / 250000000) x131 := by
    exact bounds_log hx130 (by norm_num) (by simpa only [div_one] using reflection_log_12.1) (by simpa only [div_one] using reflection_log_12.2)
  let x132 : ℝ := x127*x131
  have hx132 : Bounds (-58250236487 / 200000000000) (-58250236361 / 200000000000) x132 := by
    apply bounds_mul hx127 hx131 <;> norm_num
  let x133 : ℝ := x124+x132
  have hx133 : Bounds (35113104199 / 250000000000) (70226209399 / 500000000000) x133 := by
    apply bounds_add hx124 hx132 <;> norm_num
  let x134 : ℝ := (2 / 1)⁻¹
  have hx134 : Bounds (1 / 2) (1 / 2) x134 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x135 : ℝ := x133*x134
  have hx135 : Bounds (35113104199 / 500000000000) (70226209399 / 1000000000000) x135 := by
    apply bounds_mul hx133 hx134 <;> norm_num
  let x136 : ℝ := x133/(2 / 1)
  have hx136 : Bounds (35113104199 / 500000000000) (70226209399 / 1000000000000) x136 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx135
  let x137 : ℝ := -x136
  have hx137 : Bounds (-70226209399 / 1000000000000) (-35113104199 / 500000000000) x137 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx136
  let x138 : ℝ := x120+x137
  have hx138 : Bounds (622920970601 / 1000000000000) (311460486301 / 500000000000) x138 := by
    apply bounds_add hx120 hx137 <;> norm_num
  let x139 : ℝ := x120-x136
  have hx139 : Bounds (622920970601 / 1000000000000) (311460486301 / 500000000000) x139 := by
    exact hx138
  let x140 : ℝ := biasE (185157 / 500000)
  have hx140 : Bounds (622920970601 / 1000000000000) (311460486301 / 500000000000) x140 := by
    simpa +zetaDelta only [biasE, div_one] using hx139
  let y : ℝ := 1 - 2 * entropyInverse ((1 + H (2*m - 1/2))/2)
  have hLh' : Real.log 2 * ((1 + H (2*m - 1/2))/2) = x98 := by
    simpa +zetaDelta only [div_one] using hLh
  have hy : Bounds (7389 / 20000) (185157 / 500000) y := by
    apply entropyInverseBias_bracket
    · exact div_nonneg (add_nonneg zero_le_one
        (H_nonneg (by linarith [hm.1]) (by linarith [hm.2]))) two_pos.le
    · linarith [H_le_one (2*m-1/2)]
    · norm_num
    · norm_num
    · norm_num
    · have h1 : biasE (185157 / 500000) ≤ (311460486301 / 500000000000) := hx140.2
      have h2 : (622921324511 / 1000000000000) ≤ x98 := hx98.1
      linarith [hLh']
    · have h1 : x98 ≤ (7790703783 / 12500000000) := hx98.2
      have h2 : (311628224933 / 500000000000) ≤ biasE (7389 / 20000) := hx119.1
      linarith [hLh']
  let x141 : ℝ := x3⁻¹
  have hx141 : Bounds (966767371601 / 250000000000) (775170325511 / 200000000000) x141 := by
    apply bounds_inv hx3 <;> norm_num
  let x142 : ℝ := x98*x141
  have hx142 : Bounds (1204440023223 / 500000000000) (603912238743 / 250000000000) x142 := by
    apply bounds_mul hx98 hx141 <;> norm_num
  let x143 : ℝ := x98/x3
  have hx143 : Bounds (1204440023223 / 500000000000) (603912238743 / 250000000000) x143 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx142
  let x144 : ℝ := Real.log (2 / 1)
  have hx144 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x144 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x145 : ℝ := (1 / 1)+(27149 / 100000)
  have hx145 : Bounds (127149 / 100000) (127149 / 100000) x145 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((27149 / 100000) : ℝ)) <;> norm_num
  let x146 : ℝ := (1 / 1)+(27149 / 100000)
  have hx146 : Bounds (127149 / 100000) (127149 / 100000) x146 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((27149 / 100000) : ℝ)) <;> norm_num
  let x147 : ℝ := Real.log x146
  have hx147 : Bounds (240189441 / 1000000000) (120094721 / 500000000) x147 := by
    exact bounds_log hx146 (by norm_num) (by simpa only [div_one] using reflection_log_13.1) (by simpa only [div_one] using reflection_log_13.2)
  let x148 : ℝ := x145*x147
  have hx148 : Bounds (305398472337 / 1000000000000) (305398473609 / 1000000000000) x148 := by
    apply bounds_mul hx145 hx147 <;> norm_num
  let x149 : ℝ := -(27149 / 100000)
  have hx149 : Bounds (-27149 / 100000) (-27149 / 100000) x149 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((27149 / 100000) : ℝ))
  let x150 : ℝ := (1 / 1)+x149
  have hx150 : Bounds (72851 / 100000) (72851 / 100000) x150 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx149 <;> norm_num
  let x151 : ℝ := (1 / 1)-(27149 / 100000)
  have hx151 : Bounds (72851 / 100000) (72851 / 100000) x151 := by
    exact hx150
  let x152 : ℝ := -(27149 / 100000)
  have hx152 : Bounds (-27149 / 100000) (-27149 / 100000) x152 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((27149 / 100000) : ℝ))
  let x153 : ℝ := (1 / 1)+x152
  have hx153 : Bounds (72851 / 100000) (72851 / 100000) x153 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx152 <;> norm_num
  let x154 : ℝ := (1 / 1)-(27149 / 100000)
  have hx154 : Bounds (72851 / 100000) (72851 / 100000) x154 := by
    exact hx153
  let x155 : ℝ := Real.log x154
  have hx155 : Bounds (-316753927 / 1000000000) (-158376963 / 500000000) x155 := by
    exact bounds_log hx154 (by norm_num) (by simpa only [div_one] using reflection_log_14.1) (by simpa only [div_one] using reflection_log_14.2)
  let x156 : ℝ := x151*x155
  have hx156 : Bounds (-230758403359 / 1000000000000) (-23075840263 / 100000000000) x156 := by
    apply bounds_mul hx151 hx155 <;> norm_num
  let x157 : ℝ := x148+x156
  have hx157 : Bounds (37320034489 / 500000000000) (74640070979 / 1000000000000) x157 := by
    apply bounds_add hx148 hx156 <;> norm_num
  let x158 : ℝ := (2 / 1)⁻¹
  have hx158 : Bounds (1 / 2) (1 / 2) x158 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x159 : ℝ := x157*x158
  have hx159 : Bounds (37320034489 / 1000000000000) (3732003549 / 100000000000) x159 := by
    apply bounds_mul hx157 hx158 <;> norm_num
  let x160 : ℝ := x157/(2 / 1)
  have hx160 : Bounds (37320034489 / 1000000000000) (3732003549 / 100000000000) x160 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx159
  let x161 : ℝ := -x160
  have hx161 : Bounds (-3732003549 / 100000000000) (-37320034489 / 1000000000000) x161 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx160
  let x162 : ℝ := x144+x161
  have hx162 : Bounds (65582714451 / 100000000000) (655827146511 / 1000000000000) x162 := by
    apply bounds_add hx144 hx161 <;> norm_num
  let x163 : ℝ := x144-x160
  have hx163 : Bounds (65582714451 / 100000000000) (655827146511 / 1000000000000) x163 := by
    exact hx162
  let x164 : ℝ := biasE (27149 / 100000)
  have hx164 : Bounds (65582714451 / 100000000000) (655827146511 / 1000000000000) x164 := by
    simpa +zetaDelta only [biasE, div_one] using hx163
  let x165 : ℝ := Real.log (2 / 1)
  have hx165 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x165 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x166 : ℝ := (1 / 1)+(10887 / 40000)
  have hx166 : Bounds (50887 / 40000) (50887 / 40000) x166 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((10887 / 40000) : ℝ)) <;> norm_num
  let x167 : ℝ := (1 / 1)+(10887 / 40000)
  have hx167 : Bounds (50887 / 40000) (50887 / 40000) x167 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((10887 / 40000) : ℝ)) <;> norm_num
  let x168 : ℝ := Real.log x167
  have hx168 : Bounds (120364017 / 500000000) (48145607 / 200000000) x168 := by
    exact bounds_log hx167 (by norm_num) (by simpa only [div_one] using reflection_log_15.1) (by simpa only [div_one] using reflection_log_15.2)
  let x169 : ℝ := x166*x168
  have hx169 : Bounds (306248186653 / 1000000000000) (306248187927 / 1000000000000) x169 := by
    apply bounds_mul hx166 hx168 <;> norm_num
  let x170 : ℝ := -(10887 / 40000)
  have hx170 : Bounds (-10887 / 40000) (-10887 / 40000) x170 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((10887 / 40000) : ℝ))
  let x171 : ℝ := (1 / 1)+x170
  have hx171 : Bounds (29113 / 40000) (29113 / 40000) x171 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx170 <;> norm_num
  let x172 : ℝ := (1 / 1)-(10887 / 40000)
  have hx172 : Bounds (29113 / 40000) (29113 / 40000) x172 := by
    exact hx171
  let x173 : ℝ := -(10887 / 40000)
  have hx173 : Bounds (-10887 / 40000) (-10887 / 40000) x173 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((10887 / 40000) : ℝ))
  let x174 : ℝ := (1 / 1)+x173
  have hx174 : Bounds (29113 / 40000) (29113 / 40000) x174 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx173 <;> norm_num
  let x175 : ℝ := (1 / 1)-(10887 / 40000)
  have hx175 : Bounds (29113 / 40000) (29113 / 40000) x175 := by
    exact hx174
  let x176 : ℝ := Real.log x175
  have hx176 : Bounds (-63538929 / 200000000) (-79423661 / 250000000) x176 := by
    exact bounds_log hx175 (by norm_num) (by simpa only [div_one] using reflection_log_16.1) (by simpa only [div_one] using reflection_log_16.2)
  let x177 : ℝ := x172*x176
  have hx177 : Bounds (-115613052499 / 500000000000) (-231226104269 / 1000000000000) x177 := by
    apply bounds_mul hx172 hx176 <;> norm_num
  let x178 : ℝ := x169+x177
  have hx178 : Bounds (15004416331 / 200000000000) (37511041829 / 500000000000) x178 := by
    apply bounds_add hx169 hx177 <;> norm_num
  let x179 : ℝ := (2 / 1)⁻¹
  have hx179 : Bounds (1 / 2) (1 / 2) x179 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x180 : ℝ := x178*x179
  have hx180 : Bounds (37511040827 / 1000000000000) (37511041829 / 1000000000000) x180 := by
    apply bounds_mul hx178 hx179 <;> norm_num
  let x181 : ℝ := x178/(2 / 1)
  have hx181 : Bounds (37511040827 / 1000000000000) (37511041829 / 1000000000000) x181 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx180
  let x182 : ℝ := -x181
  have hx182 : Bounds (-37511041829 / 1000000000000) (-37511040827 / 1000000000000) x182 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx181
  let x183 : ℝ := x165+x182
  have hx183 : Bounds (655636138171 / 1000000000000) (655636140173 / 1000000000000) x183 := by
    apply bounds_add hx165 hx182 <;> norm_num
  let x184 : ℝ := x165-x181
  have hx184 : Bounds (655636138171 / 1000000000000) (655636140173 / 1000000000000) x184 := by
    exact hx183
  let x185 : ℝ := biasE (10887 / 40000)
  have hx185 : Bounds (655636138171 / 1000000000000) (655636140173 / 1000000000000) x185 := by
    simpa +zetaDelta only [biasE, div_one] using hx184
  let x186 : ℝ := x143*(27149 / 100000)
  have hx186 : Bounds (653986843809 / 1000000000000) (327912267393 / 500000000000) x186 := by
    apply bounds_mul hx143 (bounds_const ((27149 / 100000) : ℝ)) <;> norm_num
  let x187 : ℝ := x143*(10887 / 40000)
  have hx187 : Bounds (655636926641 / 1000000000000) (8218490679 / 12500000000) x187 := by
    apply bounds_mul hx143 (bounds_const ((10887 / 40000) : ℝ)) <;> norm_num
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
  have hc : Bounds (27149 / 100000) (10887 / 40000) c := by
    apply contact_bracket hc0 hcMem.2.le (by norm_num) (by norm_num) (by norm_num)
      (show 0 < x143 by linarith [hx143.1]) hcEq
    · have h1 : x143 * (27149 / 100000) ≤ (327912267393 / 500000000000) := hx186.2
      have h2 : (65582714451 / 100000000000) ≤ biasE (27149 / 100000) := hx164.1
      linarith
    · have h1 : biasE (10887 / 40000) ≤ (655636140173 / 1000000000000) := hx185.2
      have h2 : (655636926641 / 1000000000000) ≤ x143 * (10887 / 40000) := hx187.1
      linarith
  let x188 : ℝ := (1 / 1)+y
  have hx188 : Bounds (27389 / 20000) (685157 / 500000) x188 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hy <;> norm_num
  let x189 : ℝ := -y
  have hx189 : Bounds (-185157 / 500000) (-7389 / 20000) x189 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hy
  let x190 : ℝ := (1 / 1)+x189
  have hx190 : Bounds (314843 / 500000) (12611 / 20000) x190 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx189 <;> norm_num
  let x191 : ℝ := (1 / 1)-y
  have hx191 : Bounds (314843 / 500000) (12611 / 20000) x191 := by
    exact hx190
  let x192 : ℝ := x191⁻¹
  have hx192 : Bounds (1585917056537 / 1000000000000) (397023278269 / 250000000000) x192 := by
    apply bounds_inv hx191 <;> norm_num
  let x193 : ℝ := x188*x192
  have hx193 : Bounds (1085917056537 / 500000000000) (272023278269 / 125000000000) x193 := by
    apply bounds_mul hx188 hx192 <;> norm_num
  let x194 : ℝ := x188/x191
  have hx194 : Bounds (1085917056537 / 500000000000) (272023278269 / 125000000000) x194 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx193
  let x195 : ℝ := Real.log x194
  have hx195 : Bounds (775572023 / 1000000000) (194393477 / 250000000) x195 := by
    exact bounds_log hx194 (by norm_num) (by simpa only [div_one] using reflection_log_17.1) (by simpa only [div_one] using reflection_log_18.2)
  let x196 : ℝ := (2 / 1)⁻¹
  have hx196 : Bounds (1 / 2) (1 / 2) x196 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x197 : ℝ := x195*x196
  have hx197 : Bounds (775572023 / 2000000000) (194393477 / 500000000) x197 := by
    apply bounds_mul hx195 hx196 <;> norm_num
  let x198 : ℝ := x195/(2 / 1)
  have hx198 : Bounds (775572023 / 2000000000) (194393477 / 500000000) x198 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx197
  let x199 : ℝ := (1 / 1)+c
  have hx199 : Bounds (127149 / 100000) (50887 / 40000) x199 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hc <;> norm_num
  let x200 : ℝ := -c
  have hx200 : Bounds (-10887 / 40000) (-27149 / 100000) x200 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hc
  let x201 : ℝ := (1 / 1)+x200
  have hx201 : Bounds (29113 / 40000) (72851 / 100000) x201 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx200 <;> norm_num
  let x202 : ℝ := (1 / 1)-c
  have hx202 : Bounds (29113 / 40000) (72851 / 100000) x202 := by
    exact hx201
  let x203 : ℝ := x202⁻¹
  have hx203 : Bounds (1372664754087 / 1000000000000) (343489162917 / 250000000000) x203 := by
    apply bounds_inv hx202 <;> norm_num
  let x204 : ℝ := x199*x203
  have hx204 : Bounds (872664754087 / 500000000000) (218489162917 / 125000000000) x204 := by
    apply bounds_mul hx199 hx203 <;> norm_num
  let x205 : ℝ := x199/x202
  have hx205 : Bounds (872664754087 / 500000000000) (218489162917 / 125000000000) x205 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx204
  let x206 : ℝ := Real.log x205
  have hx206 : Bounds (556943367 / 1000000000) (558422679 / 1000000000) x206 := by
    exact bounds_log hx205 (by norm_num) (by simpa only [div_one] using reflection_log_19.1) (by simpa only [div_one] using reflection_log_20.2)
  let x207 : ℝ := (2 / 1)⁻¹
  have hx207 : Bounds (1 / 2) (1 / 2) x207 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x208 : ℝ := x206*x207
  have hx208 : Bounds (556943367 / 2000000000) (558422679 / 2000000000) x208 := by
    apply bounds_mul hx206 hx207 <;> norm_num
  let x209 : ℝ := x206/(2 / 1)
  have hx209 : Bounds (556943367 / 2000000000) (558422679 / 2000000000) x209 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx208
  let x210 : ℝ := (2 / 1)*x50
  have hx210 : Bounds (329664417157 / 250000000000) (131896738371 / 100000000000) x210 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx50 <;> norm_num
  let x211 : ℝ := (2 / 1)*x98
  have hx211 : Bounds (622921324511 / 500000000000) (7790703783 / 6250000000) x211 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx98 <;> norm_num
  let x212 : ℝ := -x211
  have hx212 : Bounds (-7790703783 / 6250000000) (-622921324511 / 500000000000) x212 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx211
  let x213 : ℝ := x210+x212
  have hx213 : Bounds (18036265837 / 250000000000) (2285147959 / 31250000000) x213 := by
    apply bounds_add hx210 hx212 <;> norm_num
  let x214 : ℝ := x210-x211
  have hx214 : Bounds (18036265837 / 250000000000) (2285147959 / 31250000000) x214 := by
    exact hx213
  let x215 : ℝ := y*x198
  have hx215 : Bounds (35816885487 / 250000000000) (35993313021 / 250000000000) x215 := by
    apply bounds_mul hy hx198 <;> norm_num
  let x216 : ℝ := -x215
  have hx216 : Bounds (-35993313021 / 250000000000) (-35816885487 / 250000000000) x216 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx215
  let x217 : ℝ := x214+x216
  have hx217 : Bounds (-1122315449 / 15625000000) (-3507140363 / 50000000000) x217 := by
    apply bounds_add hx214 hx216 <;> norm_num
  let x218 : ℝ := x214-x215
  have hx218 : Bounds (-1122315449 / 15625000000) (-3507140363 / 50000000000) x218 := by
    exact hx217
  let x219 : ℝ := x3*x209
  have hx219 : Bounds (71847869903 / 1000000000000) (18050576831 / 250000000000) x219 := by
    apply bounds_mul hx3 hx209 <;> norm_num
  let x220 : ℝ := x218+x219
  have hx220 : Bounds (19681167 / 1000000000000) (64359377 / 31250000000) x220 := by
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

theorem acceptedCertificate : DoubleCapBiasCellCertificate (949 / 2560) (3799 / 10240) (fun m => (1 + H (2*m - 1/2))/2) where
  domain := by norm_num
  sound m hmLo hmHi := by
    exact cell_bias_nonneg m ⟨hmLo, hmHi⟩

theorem accepted_cell :
    ∀ m, (949 / 2560) ≤ m → m ≤ (3799 / 10240) → 0 ≤ doubleCapHighResidual m := by
  intro m hmLo hmHi
  unfold doubleCapHighResidual
  apply doubleCapEndpointResidual_nonneg_of_biasCell acceptedCertificate hmLo hmHi
  exact div_pos (by linarith [H_nonneg (by linarith : 0 ≤ 2*m-1/2) (by linarith : 2*m-1/2 ≤ 1)]) two_pos

#print axioms cell_bias_nonneg
#print axioms accepted_cell

end GeneralCK.Certificates.DoubleCapMiddle.Cell0278

end


