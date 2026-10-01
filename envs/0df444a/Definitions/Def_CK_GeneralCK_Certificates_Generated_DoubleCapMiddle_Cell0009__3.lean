-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0009__3
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0009__3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T11:17:52.510833+00:00
-- url     : https://prove2.me/theorems/ca73bedf-5d87-4efe-85b6-978fa19a48c6
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0009 (+2 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0010, GeneralCK.Certificates.Gener…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0009 (+2 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0010, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0011)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0009 (+2 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0010, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0011)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0009 (+2 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0010, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0011) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0009 (+2 modules: GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0010, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0011).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0007Logs__3
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0010Logs__6

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0009 =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0009
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Reflection
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem cell_bias_nonneg (m : ℝ) (hm : Bounds (79 / 320) (1 / 4) m) :
    let h := H (2*m)/2
    let x := 1-2*m
    let y := 1-2*entropyInverse h
    let c := regularContact (x/(Real.log 2*h))
    0 ≤ 2*(biasE x-Real.log 2*h)-y*SmallMean.A y+x*SmallMean.A c := by
  have hEq : biasE (1-4*m) = Real.log 2 * H (2*m) := by
    rw [show 1-4*m = 1-2*(2*m) by ring,
      GeneralCK.Correction.Natural.biasE_probability (by linarith [hm.1]) (by linarith [hm.2]),
      GeneralCK.Certificates.Mixed.hn_eq_H_mul_log]
    ring
  have hLh : Real.log 2 * (H (2*m)/2) = biasE (1-4*m)/2 := by
    rw [hEq]
    ring
  let x0 : ℝ := (2 / 1)*m
  have hx0 : Bounds (79 / 160) (1 / 2) x0 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hm <;> norm_num
  let x1 : ℝ := -x0
  have hx1 : Bounds (-1 / 2) (-79 / 160) x1 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx0
  let x2 : ℝ := (1 / 1)+x1
  have hx2 : Bounds (1 / 2) (81 / 160) x2 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx1 <;> norm_num
  let x3 : ℝ := (1 / 1)-x0
  have hx3 : Bounds (1 / 2) (81 / 160) x3 := by
    exact hx2
  let x4 : ℝ := (4 / 1)*m
  have hx4 : Bounds (79 / 80) (1 / 1) x4 := by
    apply bounds_mul (bounds_const ((4 / 1) : ℝ)) hm <;> norm_num
  let x5 : ℝ := -x4
  have hx5 : Bounds (-1 / 1) (-79 / 80) x5 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx4
  let x6 : ℝ := (1 / 1)+x5
  have hx6 : Bounds (0 / 1) (1 / 80) x6 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx5 <;> norm_num
  let x7 : ℝ := (1 / 1)-x4
  have hx7 : Bounds (0 / 1) (1 / 80) x7 := by
    exact hx6
  let x8 : ℝ := Real.log (2 / 1)
  have hx8 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x8 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x9 : ℝ := (1 / 1)+(81 / 160)
  have hx9 : Bounds (241 / 160) (241 / 160) x9 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((81 / 160) : ℝ)) <;> norm_num
  let x10 : ℝ := (1 / 1)+(81 / 160)
  have hx10 : Bounds (241 / 160) (241 / 160) x10 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((81 / 160) : ℝ)) <;> norm_num
  let x11 : ℝ := Real.log x10
  have hx11 : Bounds (204811559 / 500000000) (409623119 / 1000000000) x11 := by
    exact bounds_log hx10 (by norm_num) (by simpa only [div_one] using reflection_log_1.1) (by simpa only [div_one] using reflection_log_1.2)
  let x12 : ℝ := x9*x11
  have hx12 : Bounds (616994821487 / 1000000000000) (308497411497 / 500000000000) x12 := by
    apply bounds_mul hx9 hx11 <;> norm_num
  let x13 : ℝ := -(81 / 160)
  have hx13 : Bounds (-81 / 160) (-81 / 160) x13 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((81 / 160) : ℝ))
  let x14 : ℝ := (1 / 1)+x13
  have hx14 : Bounds (79 / 160) (79 / 160) x14 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx13 <;> norm_num
  let x15 : ℝ := (1 / 1)-(81 / 160)
  have hx15 : Bounds (79 / 160) (79 / 160) x15 := by
    exact hx14
  let x16 : ℝ := -(81 / 160)
  have hx16 : Bounds (-81 / 160) (-81 / 160) x16 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((81 / 160) : ℝ))
  let x17 : ℝ := (1 / 1)+x16
  have hx17 : Bounds (79 / 160) (79 / 160) x17 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx16 <;> norm_num
  let x18 : ℝ := (1 / 1)-(81 / 160)
  have hx18 : Bounds (79 / 160) (79 / 160) x18 := by
    exact hx17
  let x19 : ℝ := Real.log x18
  have hx19 : Bounds (-176431491 / 250000000) (-352862981 / 500000000) x19 := by
    exact bounds_log hx18 (by norm_num) (by simpa only [div_one] using reflection_log_2.1) (by simpa only [div_one] using reflection_log_2.2)
  let x20 : ℝ := x15*x19
  have hx20 : Bounds (-13938087789 / 40000000000) (-348452193737 / 1000000000000) x20 := by
    apply bounds_mul hx15 hx19 <;> norm_num
  let x21 : ℝ := x12+x20
  have hx21 : Bounds (134271313381 / 500000000000) (268542629257 / 1000000000000) x21 := by
    apply bounds_add hx12 hx20 <;> norm_num
  let x22 : ℝ := (2 / 1)⁻¹
  have hx22 : Bounds (1 / 2) (1 / 2) x22 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x23 : ℝ := x21*x22
  have hx23 : Bounds (134271313381 / 1000000000000) (134271314629 / 1000000000000) x23 := by
    apply bounds_mul hx21 hx22 <;> norm_num
  let x24 : ℝ := x21/(2 / 1)
  have hx24 : Bounds (134271313381 / 1000000000000) (134271314629 / 1000000000000) x24 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx23
  let x25 : ℝ := -x24
  have hx25 : Bounds (-134271314629 / 1000000000000) (-134271313381 / 1000000000000) x25 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx24
  let x26 : ℝ := x8+x25
  have hx26 : Bounds (558875865371 / 1000000000000) (558875867619 / 1000000000000) x26 := by
    apply bounds_add hx8 hx25 <;> norm_num
  let x27 : ℝ := x8-x24
  have hx27 : Bounds (558875865371 / 1000000000000) (558875867619 / 1000000000000) x27 := by
    exact hx26
  let x28 : ℝ := biasE (81 / 160)
  have hx28 : Bounds (558875865371 / 1000000000000) (558875867619 / 1000000000000) x28 := by
    simpa +zetaDelta only [biasE, div_one] using hx27
  let x29 : ℝ := Real.log (2 / 1)
  have hx29 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x29 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x30 : ℝ := (1 / 1)+(1 / 2)
  have hx30 : Bounds (3 / 2) (3 / 2) x30 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1 / 2) : ℝ)) <;> norm_num
  let x31 : ℝ := (1 / 1)+(1 / 2)
  have hx31 : Bounds (3 / 2) (3 / 2) x31 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1 / 2) : ℝ)) <;> norm_num
  let x32 : ℝ := Real.log x31
  have hx32 : Bounds (101366277 / 250000000) (405465109 / 1000000000) x32 := by
    exact bounds_log hx31 (by norm_num) (by simpa only [div_one] using reflection_log_3.1) (by simpa only [div_one] using reflection_log_3.2)
  let x33 : ℝ := x30*x32
  have hx33 : Bounds (304098831 / 500000000) (1216395327 / 2000000000) x33 := by
    apply bounds_mul hx30 hx32 <;> norm_num
  let x34 : ℝ := -(1 / 2)
  have hx34 : Bounds (-1 / 2) (-1 / 2) x34 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1 / 2) : ℝ))
  let x35 : ℝ := (1 / 1)+x34
  have hx35 : Bounds (1 / 2) (1 / 2) x35 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx34 <;> norm_num
  let x36 : ℝ := (1 / 1)-(1 / 2)
  have hx36 : Bounds (1 / 2) (1 / 2) x36 := by
    exact hx35
  let x37 : ℝ := -(1 / 2)
  have hx37 : Bounds (-1 / 2) (-1 / 2) x37 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1 / 2) : ℝ))
  let x38 : ℝ := (1 / 1)+x37
  have hx38 : Bounds (1 / 2) (1 / 2) x38 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx37 <;> norm_num
  let x39 : ℝ := (1 / 1)-(1 / 2)
  have hx39 : Bounds (1 / 2) (1 / 2) x39 := by
    exact hx38
  let x40 : ℝ := Real.log x39
  have hx40 : Bounds (-693147181 / 1000000000) (-34657359 / 50000000) x40 := by
    exact bounds_log hx39 (by norm_num) (by simpa only [div_one] using reflection_log_4.1) (by simpa only [div_one] using reflection_log_4.2)
  let x41 : ℝ := x36*x40
  have hx41 : Bounds (-693147181 / 2000000000) (-34657359 / 100000000) x41 := by
    apply bounds_mul hx36 hx40 <;> norm_num
  let x42 : ℝ := x33+x41
  have hx42 : Bounds (523248143 / 2000000000) (523248147 / 2000000000) x42 := by
    apply bounds_add hx33 hx41 <;> norm_num
  let x43 : ℝ := (2 / 1)⁻¹
  have hx43 : Bounds (1 / 2) (1 / 2) x43 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x44 : ℝ := x42*x43
  have hx44 : Bounds (523248143 / 4000000000) (523248147 / 4000000000) x44 := by
    apply bounds_mul hx42 hx43 <;> norm_num
  let x45 : ℝ := x42/(2 / 1)
  have hx45 : Bounds (523248143 / 4000000000) (523248147 / 4000000000) x45 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx44
  let x46 : ℝ := -x45
  have hx46 : Bounds (-523248147 / 4000000000) (-523248143 / 4000000000) x46 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx45
  let x47 : ℝ := x29+x46
  have hx47 : Bounds (2249340573 / 4000000000) (2249340581 / 4000000000) x47 := by
    apply bounds_add hx29 hx46 <;> norm_num
  let x48 : ℝ := x29-x45
  have hx48 : Bounds (2249340573 / 4000000000) (2249340581 / 4000000000) x48 := by
    exact hx47
  let x49 : ℝ := biasE (1 / 2)
  have hx49 : Bounds (2249340573 / 4000000000) (2249340581 / 4000000000) x49 := by
    simpa +zetaDelta only [biasE, div_one] using hx48
  let x50 : ℝ := biasE x3
  have hx50 : Bounds (558875865371 / 1000000000000) (2249340581 / 4000000000) x50 := by
    exact bounds_biasE hx3 (by norm_num) (by norm_num) hx28.1 hx49.2
  let x51 : ℝ := Real.log (2 / 1)
  have hx51 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x51 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x52 : ℝ := (1 / 1)+(1 / 80)
  have hx52 : Bounds (81 / 80) (81 / 80) x52 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1 / 80) : ℝ)) <;> norm_num
  let x53 : ℝ := (1 / 1)+(1 / 80)
  have hx53 : Bounds (81 / 80) (81 / 80) x53 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1 / 80) : ℝ)) <;> norm_num
  let x54 : ℝ := Real.log x53
  have hx54 : Bounds (12422519 / 1000000000) (310563 / 25000000) x54 := by
    exact bounds_log hx53 (by norm_num) (by simpa only [div_one] using reflection_log_5.1) (by simpa only [div_one] using reflection_log_5.2)
  let x55 : ℝ := x52*x54
  have hx55 : Bounds (12577800487 / 1000000000000) (25155603 / 2000000000) x55 := by
    apply bounds_mul hx52 hx54 <;> norm_num
  let x56 : ℝ := -(1 / 80)
  have hx56 : Bounds (-1 / 80) (-1 / 80) x56 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1 / 80) : ℝ))
  let x57 : ℝ := (1 / 1)+x56
  have hx57 : Bounds (79 / 80) (79 / 80) x57 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx56 <;> norm_num
  let x58 : ℝ := (1 / 1)-(1 / 80)
  have hx58 : Bounds (79 / 80) (79 / 80) x58 := by
    exact hx57
  let x59 : ℝ := -(1 / 80)
  have hx59 : Bounds (-1 / 80) (-1 / 80) x59 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1 / 80) : ℝ))
  let x60 : ℝ := (1 / 1)+x59
  have hx60 : Bounds (79 / 80) (79 / 80) x60 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx59 <;> norm_num
  let x61 : ℝ := (1 / 1)-(1 / 80)
  have hx61 : Bounds (79 / 80) (79 / 80) x61 := by
    exact hx60
  let x62 : ℝ := Real.log x61
  have hx62 : Bounds (-12578783 / 1000000000) (-6289391 / 500000000) x62 := by
    exact bounds_log hx61 (by norm_num) (by simpa only [div_one] using reflection_log_6.1) (by simpa only [div_one] using reflection_log_6.2)
  let x63 : ℝ := x58*x62
  have hx63 : Bounds (-12421548213 / 1000000000000) (-496861889 / 40000000000) x63 := by
    apply bounds_mul hx58 hx62 <;> norm_num
  let x64 : ℝ := x55+x63
  have hx64 : Bounds (78126137 / 500000000000) (6250171 / 40000000000) x64 := by
    apply bounds_add hx55 hx63 <;> norm_num
  let x65 : ℝ := (2 / 1)⁻¹
  have hx65 : Bounds (1 / 2) (1 / 2) x65 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x66 : ℝ := x64*x65
  have hx66 : Bounds (78126137 / 1000000000000) (39063569 / 500000000000) x66 := by
    apply bounds_mul hx64 hx65 <;> norm_num
  let x67 : ℝ := x64/(2 / 1)
  have hx67 : Bounds (78126137 / 1000000000000) (39063569 / 500000000000) x67 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx66
  let x68 : ℝ := -x67
  have hx68 : Bounds (-39063569 / 500000000000) (-78126137 / 1000000000000) x68 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx67
  let x69 : ℝ := x51+x68
  have hx69 : Bounds (346534526431 / 500000000000) (693069054863 / 1000000000000) x69 := by
    apply bounds_add hx51 hx68 <;> norm_num
  let x70 : ℝ := x51-x67
  have hx70 : Bounds (346534526431 / 500000000000) (693069054863 / 1000000000000) x70 := by
    exact hx69
  let x71 : ℝ := biasE (1 / 80)
  have hx71 : Bounds (346534526431 / 500000000000) (693069054863 / 1000000000000) x71 := by
    simpa +zetaDelta only [biasE, div_one] using hx70
  let x72 : ℝ := Real.log (2 / 1)
  have hx72 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x72 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x73 : ℝ := (1 / 1)+(0 / 1)
  have hx73 : Bounds (1 / 1) (1 / 1) x73 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((0 / 1) : ℝ)) <;> norm_num
  let x74 : ℝ := (1 / 1)+(0 / 1)
  have hx74 : Bounds (1 / 1) (1 / 1) x74 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((0 / 1) : ℝ)) <;> norm_num
  let x75 : ℝ := Real.log x74
  have hx75 : Bounds (0 / 1) (0 / 1) x75 := by
    exact bounds_log hx74 (by norm_num) (by simpa only [div_one] using reflection_log_7.1) (by simpa only [div_one] using reflection_log_7.2)
  let x76 : ℝ := x73*x75
  have hx76 : Bounds (0 / 1) (0 / 1) x76 := by
    apply bounds_mul hx73 hx75 <;> norm_num
  let x77 : ℝ := -(0 / 1)
  have hx77 : Bounds (0 / 1) (0 / 1) x77 := by
    simpa +zetaDelta only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((0 / 1) : ℝ))
  let x78 : ℝ := (1 / 1)+x77
  have hx78 : Bounds (1 / 1) (1 / 1) x78 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx77 <;> norm_num
  let x79 : ℝ := (1 / 1)-(0 / 1)
  have hx79 : Bounds (1 / 1) (1 / 1) x79 := by
    exact hx78
  let x80 : ℝ := -(0 / 1)
  have hx80 : Bounds (0 / 1) (0 / 1) x80 := by
    simpa +zetaDelta only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((0 / 1) : ℝ))
  let x81 : ℝ := (1 / 1)+x80
  have hx81 : Bounds (1 / 1) (1 / 1) x81 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx80 <;> norm_num
  let x82 : ℝ := (1 / 1)-(0 / 1)
  have hx82 : Bounds (1 / 1) (1 / 1) x82 := by
    exact hx81
  let x83 : ℝ := Real.log x82
  have hx83 : Bounds (0 / 1) (0 / 1) x83 := by
    exact bounds_log hx82 (by norm_num) (by simpa only [div_one] using reflection_log_7.1) (by simpa only [div_one] using reflection_log_7.2)
  let x84 : ℝ := x79*x83
  have hx84 : Bounds (0 / 1) (0 / 1) x84 := by
    apply bounds_mul hx79 hx83 <;> norm_num
  let x85 : ℝ := x76+x84
  have hx85 : Bounds (0 / 1) (0 / 1) x85 := by
    apply bounds_add hx76 hx84 <;> norm_num
  let x86 : ℝ := (2 / 1)⁻¹
  have hx86 : Bounds (1 / 2) (1 / 2) x86 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x87 : ℝ := x85*x86
  have hx87 : Bounds (0 / 1) (0 / 1) x87 := by
    apply bounds_mul hx85 hx86 <;> norm_num
  let x88 : ℝ := x85/(2 / 1)
  have hx88 : Bounds (0 / 1) (0 / 1) x88 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx87
  let x89 : ℝ := -x88
  have hx89 : Bounds (0 / 1) (0 / 1) x89 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx88
  let x90 : ℝ := x72+x89
  have hx90 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x90 := by
    apply bounds_add hx72 hx89 <;> norm_num
  let x91 : ℝ := x72-x88
  have hx91 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x91 := by
    exact hx90
  let x92 : ℝ := biasE (0 / 1)
  have hx92 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x92 := by
    simpa +zetaDelta only [biasE, div_one] using hx91
  let x93 : ℝ := biasE x7
  have hx93 : Bounds (346534526431 / 500000000000) (693147181 / 1000000000) x93 := by
    exact bounds_biasE hx7 (by norm_num) (by norm_num) hx71.1 hx92.2
  let x94 : ℝ := (2 / 1)⁻¹
  have hx94 : Bounds (1 / 2) (1 / 2) x94 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x95 : ℝ := x93*x94
  have hx95 : Bounds (346534526431 / 1000000000000) (693147181 / 2000000000) x95 := by
    apply bounds_mul hx93 hx94 <;> norm_num
  let x96 : ℝ := x93/(2 / 1)
  have hx96 : Bounds (346534526431 / 1000000000000) (693147181 / 2000000000) x96 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx95
  let x97 : ℝ := Real.log (2 / 1)
  have hx97 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x97 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x98 : ℝ := (1 / 1)+(97493 / 125000)
  have hx98 : Bounds (222493 / 125000) (222493 / 125000) x98 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((97493 / 125000) : ℝ)) <;> norm_num
  let x99 : ℝ := (1 / 1)+(97493 / 125000)
  have hx99 : Bounds (222493 / 125000) (222493 / 125000) x99 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((97493 / 125000) : ℝ)) <;> norm_num
  let x100 : ℝ := Real.log x99
  have hx100 : Bounds (576581903 / 1000000000) (36036369 / 62500000) x100 := by
    exact bounds_log hx99 (by norm_num) (by simpa only [div_one] using reflection_log_8.1) (by simpa only [div_one] using reflection_log_8.2)
  let x101 : ℝ := x98*x100
  have hx101 : Bounds (1026283498753 / 1000000000000) (513141750267 / 500000000000) x101 := by
    apply bounds_mul hx98 hx100 <;> norm_num
  let x102 : ℝ := -(97493 / 125000)
  have hx102 : Bounds (-97493 / 125000) (-97493 / 125000) x102 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((97493 / 125000) : ℝ))
  let x103 : ℝ := (1 / 1)+x102
  have hx103 : Bounds (27507 / 125000) (27507 / 125000) x103 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx102 <;> norm_num
  let x104 : ℝ := (1 / 1)-(97493 / 125000)
  have hx104 : Bounds (27507 / 125000) (27507 / 125000) x104 := by
    exact hx103
  let x105 : ℝ := -(97493 / 125000)
  have hx105 : Bounds (-97493 / 125000) (-97493 / 125000) x105 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((97493 / 125000) : ℝ))
  let x106 : ℝ := (1 / 1)+x105
  have hx106 : Bounds (27507 / 125000) (27507 / 125000) x106 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx105 <;> norm_num
  let x107 : ℝ := (1 / 1)-(97493 / 125000)
  have hx107 : Bounds (27507 / 125000) (27507 / 125000) x107 := by
    exact hx106
  let x108 : ℝ := Real.log x107
  have hx108 : Bounds (-1513873221 / 1000000000) (-756936609 / 500000000) x108 := by
    exact bounds_log hx107 (by norm_num) (by simpa only [div_one] using reflection_log_9.1) (by simpa only [div_one] using reflection_log_9.2)
  let x109 : ℝ := x104*x108
  have hx109 : Bounds (-333136885521 / 1000000000000) (-16656844243 / 50000000000) x109 := by
    apply bounds_mul hx104 hx108 <;> norm_num
  let x110 : ℝ := x101+x109
  have hx110 : Bounds (43321663327 / 62500000000) (346573307837 / 500000000000) x110 := by
    apply bounds_add hx101 hx109 <;> norm_num
  let x111 : ℝ := (2 / 1)⁻¹
  have hx111 : Bounds (1 / 2) (1 / 2) x111 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x112 : ℝ := x110*x111
  have hx112 : Bounds (43321663327 / 125000000000) (346573307837 / 1000000000000) x112 := by
    apply bounds_mul hx110 hx111 <;> norm_num
  let x113 : ℝ := x110/(2 / 1)
  have hx113 : Bounds (43321663327 / 125000000000) (346573307837 / 1000000000000) x113 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx112
  let x114 : ℝ := -x113
  have hx114 : Bounds (-346573307837 / 1000000000000) (-43321663327 / 125000000000) x114 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx113
  let x115 : ℝ := x97+x114
  have hx115 : Bounds (346573872163 / 1000000000000) (21660867149 / 62500000000) x115 := by
    apply bounds_add hx97 hx114 <;> norm_num
  let x116 : ℝ := x97-x113
  have hx116 : Bounds (346573872163 / 1000000000000) (21660867149 / 62500000000) x116 := by
    exact hx115
  let x117 : ℝ := biasE (97493 / 125000)
  have hx117 : Bounds (346573872163 / 1000000000000) (21660867149 / 62500000000) x117 := by
    simpa +zetaDelta only [biasE, div_one] using hx116
  let x118 : ℝ := Real.log (2 / 1)
  have hx118 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x118 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x119 : ℝ := (1 / 1)+(389991 / 500000)
  have hx119 : Bounds (889991 / 500000) (889991 / 500000) x119 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((389991 / 500000) : ℝ)) <;> norm_num
  let x120 : ℝ := (1 / 1)+(389991 / 500000)
  have hx120 : Bounds (889991 / 500000) (889991 / 500000) x120 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((389991 / 500000) : ℝ)) <;> norm_num
  let x121 : ℝ := Real.log x120
  have hx121 : Bounds (576603251 / 1000000000) (144150813 / 250000000) x121 := by
    exact bounds_log hx120 (by norm_num) (by simpa only [div_one] using reflection_log_10.1) (by simpa only [div_one] using reflection_log_10.2)
  let x122 : ℝ := x119*x121
  have hx122 : Bounds (1026343407921 / 1000000000000) (513171704851 / 500000000000) x122 := by
    apply bounds_mul hx119 hx121 <;> norm_num
  let x123 : ℝ := -(389991 / 500000)
  have hx123 : Bounds (-389991 / 500000) (-389991 / 500000) x123 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((389991 / 500000) : ℝ))
  let x124 : ℝ := (1 / 1)+x123
  have hx124 : Bounds (110009 / 500000) (110009 / 500000) x124 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx123 <;> norm_num
  let x125 : ℝ := (1 / 1)-(389991 / 500000)
  have hx125 : Bounds (110009 / 500000) (110009 / 500000) x125 := by
    exact hx124
  let x126 : ℝ := -(389991 / 500000)
  have hx126 : Bounds (-389991 / 500000) (-389991 / 500000) x126 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((389991 / 500000) : ℝ))
  let x127 : ℝ := (1 / 1)+x126
  have hx127 : Bounds (110009 / 500000) (110009 / 500000) x127 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx126 <;> norm_num
  let x128 : ℝ := (1 / 1)-(389991 / 500000)
  have hx128 : Bounds (110009 / 500000) (110009 / 500000) x128 := by
    exact hx127
  let x129 : ℝ := Real.log x128
  have hx129 : Bounds (-1514045919 / 1000000000) (-378511479 / 250000000) x129 := by
    exact bounds_log hx128 (by norm_num) (by simpa only [div_one] using reflection_log_11.1) (by simpa only [div_one] using reflection_log_11.2)
  let x130 : ℝ := x125*x129
  have hx130 : Bounds (-333117355007 / 1000000000000) (-166558677173 / 500000000000) x130 := by
    apply bounds_mul hx125 hx129 <;> norm_num
  let x131 : ℝ := x122+x130
  have hx131 : Bounds (346613026457 / 500000000000) (173306513839 / 250000000000) x131 := by
    apply bounds_add hx122 hx130 <;> norm_num
  let x132 : ℝ := (2 / 1)⁻¹
  have hx132 : Bounds (1 / 2) (1 / 2) x132 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x133 : ℝ := x131*x132
  have hx133 : Bounds (346613026457 / 1000000000000) (173306513839 / 500000000000) x133 := by
    apply bounds_mul hx131 hx132 <;> norm_num
  let x134 : ℝ := x131/(2 / 1)
  have hx134 : Bounds (346613026457 / 1000000000000) (173306513839 / 500000000000) x134 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx133
  let x135 : ℝ := -x134
  have hx135 : Bounds (-173306513839 / 500000000000) (-346613026457 / 1000000000000) x135 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx134
  let x136 : ℝ := x118+x135
  have hx136 : Bounds (173267076161 / 500000000000) (346534154543 / 1000000000000) x136 := by
    apply bounds_add hx118 hx135 <;> norm_num
  let x137 : ℝ := x118-x134
  have hx137 : Bounds (173267076161 / 500000000000) (346534154543 / 1000000000000) x137 := by
    exact hx136
  let x138 : ℝ := biasE (389991 / 500000)
  have hx138 : Bounds (173267076161 / 500000000000) (346534154543 / 1000000000000) x138 := by
    simpa +zetaDelta only [biasE, div_one] using hx137
  let y : ℝ := 1 - 2 * entropyInverse (H (2*m)/2)
  have hLh' : Real.log 2 * (H (2*m)/2) = x96 := by
    simpa +zetaDelta only [div_one] using hLh
  have hy : Bounds (97493 / 125000) (389991 / 500000) y := by
    apply entropyInverseBias_bracket
    · exact (div_nonneg (H_nonneg (by linarith [hm.1]) (by linarith [hm.2])) two_pos.le)
    · linarith [H_le_one (2*m)]
    · norm_num
    · norm_num
    · norm_num
    · have h1 : biasE (389991 / 500000) ≤ (346534154543 / 1000000000000) := hx138.2
      have h2 : (346534526431 / 1000000000000) ≤ x96 := hx96.1
      linarith [hLh']
    · have h1 : x96 ≤ (693147181 / 2000000000) := hx96.2
      have h2 : (346573872163 / 1000000000000) ≤ biasE (97493 / 125000) := hx117.1
      linarith [hLh']
  let x139 : ℝ := x3⁻¹
  have hx139 : Bounds (79012345679 / 40000000000) (2 / 1) x139 := by
    apply bounds_inv hx3 <;> norm_num
  let x140 : ℝ := x96*x139
  have hx140 : Bounds (684512644801 / 1000000000000) (693147181 / 1000000000) x140 := by
    apply bounds_mul hx96 hx139 <;> norm_num
  let x141 : ℝ := x96/x3
  have hx141 : Bounds (684512644801 / 1000000000000) (693147181 / 1000000000) x141 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx140
  let x142 : ℝ := Real.log (2 / 1)
  have hx142 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x142 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x143 : ℝ := (1 / 1)+(41183 / 62500)
  have hx143 : Bounds (103683 / 62500) (103683 / 62500) x143 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((41183 / 62500) : ℝ)) <;> norm_num
  let x144 : ℝ := (1 / 1)+(41183 / 62500)
  have hx144 : Bounds (103683 / 62500) (103683 / 62500) x144 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((41183 / 62500) : ℝ)) <;> norm_num
  let x145 : ℝ := Real.log x144
  have hx145 : Bounds (50617161 / 100000000) (506171611 / 1000000000) x145 := by
    exact bounds_log hx144 (by norm_num) (by simpa only [div_one] using reflection_log_12.1) (by simpa only [div_one] using reflection_log_12.2)
  let x146 : ℝ := x143*x145
  have hx146 : Bounds (419851128317 / 500000000000) (419851129147 / 500000000000) x146 := by
    apply bounds_mul hx143 hx145 <;> norm_num
  let x147 : ℝ := -(41183 / 62500)
  have hx147 : Bounds (-41183 / 62500) (-41183 / 62500) x147 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((41183 / 62500) : ℝ))
  let x148 : ℝ := (1 / 1)+x147
  have hx148 : Bounds (21317 / 62500) (21317 / 62500) x148 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx147 <;> norm_num
  let x149 : ℝ := (1 / 1)-(41183 / 62500)
  have hx149 : Bounds (21317 / 62500) (21317 / 62500) x149 := by
    exact hx148
  let x150 : ℝ := -(41183 / 62500)
  have hx150 : Bounds (-41183 / 62500) (-41183 / 62500) x150 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((41183 / 62500) : ℝ))
  let x151 : ℝ := (1 / 1)+x150
  have hx151 : Bounds (21317 / 62500) (21317 / 62500) x151 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx150 <;> norm_num
  let x152 : ℝ := (1 / 1)-(41183 / 62500)
  have hx152 : Bounds (21317 / 62500) (21317 / 62500) x152 := by
    exact hx151
  let x153 : ℝ := Real.log x152
  have hx153 : Bounds (-1075661681 / 1000000000) (-1075661679 / 1000000000) x153 := by
    exact bounds_log hx152 (by norm_num) (by simpa only [div_one] using reflection_log_13.1) (by simpa only [div_one] using reflection_log_13.2)
  let x154 : ℝ := x149*x153
  have hx154 : Bounds (-366878080863 / 1000000000000) (-366878080179 / 1000000000000) x154 := by
    apply bounds_mul hx149 hx153 <;> norm_num
  let x155 : ℝ := x146+x154
  have hx155 : Bounds (472824175771 / 1000000000000) (94564835623 / 200000000000) x155 := by
    apply bounds_add hx146 hx154 <;> norm_num
  let x156 : ℝ := (2 / 1)⁻¹
  have hx156 : Bounds (1 / 2) (1 / 2) x156 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x157 : ℝ := x155*x156
  have hx157 : Bounds (47282417577 / 200000000000) (118206044529 / 500000000000) x157 := by
    apply bounds_mul hx155 hx156 <;> norm_num
  let x158 : ℝ := x155/(2 / 1)
  have hx158 : Bounds (47282417577 / 200000000000) (118206044529 / 500000000000) x158 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx157
  let x159 : ℝ := -x158
  have hx159 : Bounds (-118206044529 / 500000000000) (-47282417577 / 200000000000) x159 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx158
  let x160 : ℝ := x142+x159
  have hx160 : Bounds (228367545471 / 500000000000) (91347018623 / 200000000000) x160 := by
    apply bounds_add hx142 hx159 <;> norm_num
  let x161 : ℝ := x142-x158
  have hx161 : Bounds (228367545471 / 500000000000) (91347018623 / 200000000000) x161 := by
    exact hx160
  let x162 : ℝ := biasE (41183 / 62500)
  have hx162 : Bounds (228367545471 / 500000000000) (91347018623 / 200000000000) x162 := by
    simpa +zetaDelta only [biasE, div_one] using hx161
  let x163 : ℝ := Real.log (2 / 1)
  have hx163 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x163 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x164 : ℝ := (1 / 1)+(82847 / 125000)
  have hx164 : Bounds (207847 / 125000) (207847 / 125000) x164 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((82847 / 125000) : ℝ)) <;> norm_num
  let x165 : ℝ := (1 / 1)+(82847 / 125000)
  have hx165 : Bounds (207847 / 125000) (207847 / 125000) x165 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((82847 / 125000) : ℝ)) <;> norm_num
  let x166 : ℝ := Real.log x165
  have hx166 : Bounds (254244247 / 500000000) (101697699 / 200000000) x166 := by
    exact bounds_log hx165 (by norm_num) (by simpa only [div_one] using reflection_log_14.1) (by simpa only [div_one] using reflection_log_14.2)
  let x167 : ℝ := x164*x166
  have hx167 : Bounds (845502464099 / 1000000000000) (845502465763 / 1000000000000) x167 := by
    apply bounds_mul hx164 hx166 <;> norm_num
  let x168 : ℝ := -(82847 / 125000)
  have hx168 : Bounds (-82847 / 125000) (-82847 / 125000) x168 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((82847 / 125000) : ℝ))
  let x169 : ℝ := (1 / 1)+x168
  have hx169 : Bounds (42153 / 125000) (42153 / 125000) x169 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx168 <;> norm_num
  let x170 : ℝ := (1 / 1)-(82847 / 125000)
  have hx170 : Bounds (42153 / 125000) (42153 / 125000) x170 := by
    exact hx169
  let x171 : ℝ := -(82847 / 125000)
  have hx171 : Bounds (-82847 / 125000) (-82847 / 125000) x171 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((82847 / 125000) : ℝ))
  let x172 : ℝ := (1 / 1)+x171
  have hx172 : Bounds (42153 / 125000) (42153 / 125000) x172 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx171 <;> norm_num
  let x173 : ℝ := (1 / 1)-(82847 / 125000)
  have hx173 : Bounds (42153 / 125000) (42153 / 125000) x173 := by
    exact hx172
  let x174 : ℝ := Real.log x173
  have hx174 : Bounds (-543503941 / 500000000) (-27175197 / 25000000) x174 := by
    exact bounds_log hx173 (by norm_num) (by simpa only [div_one] using reflection_log_15.1) (by simpa only [div_one] using reflection_log_15.2)
  let x175 : ℝ := x170*x174
  have hx175 : Bounds (-183282573 / 500000000) (-14662605813 / 40000000000) x175 := by
    apply bounds_mul hx170 hx174 <;> norm_num
  let x176 : ℝ := x167+x175
  have hx176 : Bounds (478937318099 / 1000000000000) (239468660219 / 500000000000) x176 := by
    apply bounds_add hx167 hx175 <;> norm_num
  let x177 : ℝ := (2 / 1)⁻¹
  have hx177 : Bounds (1 / 2) (1 / 2) x177 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x178 : ℝ := x176*x177
  have hx178 : Bounds (239468659049 / 1000000000000) (239468660219 / 1000000000000) x178 := by
    apply bounds_mul hx176 hx177 <;> norm_num
  let x179 : ℝ := x176/(2 / 1)
  have hx179 : Bounds (239468659049 / 1000000000000) (239468660219 / 1000000000000) x179 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx178
  let x180 : ℝ := -x179
  have hx180 : Bounds (-239468660219 / 1000000000000) (-239468659049 / 1000000000000) x180 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx179
  let x181 : ℝ := x163+x180
  have hx181 : Bounds (453678519781 / 1000000000000) (453678521951 / 1000000000000) x181 := by
    apply bounds_add hx163 hx180 <;> norm_num
  let x182 : ℝ := x163-x179
  have hx182 : Bounds (453678519781 / 1000000000000) (453678521951 / 1000000000000) x182 := by
    exact hx181
  let x183 : ℝ := biasE (82847 / 125000)
  have hx183 : Bounds (453678519781 / 1000000000000) (453678521951 / 1000000000000) x183 := by
    simpa +zetaDelta only [biasE, div_one] using hx182
  let x184 : ℝ := x141*(41183 / 62500)
  have hx184 : Bounds (451044548013 / 1000000000000) (228367042841 / 500000000000) x184 := by
    apply bounds_mul hx141 (bounds_const ((41183 / 62500) : ℝ)) <;> norm_num
  let x185 : ℝ := x141*(82847 / 125000)
  have hx185 : Bounds (45367855267 / 100000000000) (91880263207 / 200000000000) x185 := by
    apply bounds_mul hx141 (bounds_const ((82847 / 125000) : ℝ)) <;> norm_num
  let c : ℝ := Reflection.regularContact (x3 / (Real.log 2 * (H (2*m)/2)))
  have hcMem := Reflection.regularContact_mem
    (x3 / (Real.log 2 * (H (2*m)/2)))
  have hc0 : 0 ≤ c := by
    dsimp only [c]
    apply GeneralCK.Certificates.RegularContactBounds.regularContact_nonneg
    rw [hLh']
    exact div_nonneg (by linarith [hx3.1]) (by linarith [hx96.1])
  have hcEq : biasE c = x141 * c := by
    have he := Reflection.regularContact_equation (x3 / x96)
    have hcdef : c = Reflection.regularContact (x3 / x96) := by
      dsimp only [c]
      rw [hLh']
    rw [← hcdef] at he
    change biasE c = (x96 / x3) * c
    have hx0 : 0 < x3 := by linarith [hx3.1]
    have hh0 : 0 < x96 := by linarith [hx96.1]
    field_simp [hx0.ne', hh0.ne'] at he ⊢
    nlinarith
  have hc : Bounds (41183 / 62500) (82847 / 125000) c := by
    apply contact_bracket hc0 hcMem.2.le (by norm_num) (by norm_num) (by norm_num)
      (show 0 < x141 by linarith [hx141.1]) hcEq
    · have h1 : x141 * (41183 / 62500) ≤ (228367042841 / 500000000000) := hx184.2
      have h2 : (228367545471 / 500000000000) ≤ biasE (41183 / 62500) := hx162.1
      linarith
    · have h1 : biasE (82847 / 125000) ≤ (453678521951 / 1000000000000) := hx183.2
      have h2 : (45367855267 / 100000000000) ≤ x141 * (82847 / 125000) := hx185.1
      linarith
  let x186 : ℝ := (1 / 1)+y
  have hx186 : Bounds (222493 / 125000) (889991 / 500000) x186 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hy <;> norm_num
  let x187 : ℝ := -y
  have hx187 : Bounds (-389991 / 500000) (-97493 / 125000) x187 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hy
  let x188 : ℝ := (1 / 1)+x187
  have hx188 : Bounds (110009 / 500000) (27507 / 125000) x188 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx187 <;> norm_num
  let x189 : ℝ := (1 / 1)-y
  have hx189 : Bounds (110009 / 500000) (27507 / 125000) x189 := by
    exact hx188
  let x190 : ℝ := x189⁻¹
  have hx190 : Bounds (4544297815101 / 1000000000000) (2272541337527 / 500000000000) x190 := by
    apply bounds_inv hx189 <;> norm_num
  let x191 : ℝ := x186*x190
  have hx191 : Bounds (4044297815101 / 500000000000) (2022541337527 / 250000000000) x191 := by
    apply bounds_mul hx186 hx190 <;> norm_num
  let x192 : ℝ := x186/x189
  have hx192 : Bounds (4044297815101 / 500000000000) (2022541337527 / 250000000000) x192 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx191
  let x193 : ℝ := Real.log x192
  have hx193 : Bounds (2090455121 / 1000000000) (522662293 / 250000000) x193 := by
    exact bounds_log hx192 (by norm_num) (by simpa only [div_one] using reflection_log_16.1) (by simpa only [div_one] using reflection_log_17.2)
  let x194 : ℝ := (2 / 1)⁻¹
  have hx194 : Bounds (1 / 2) (1 / 2) x194 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x195 : ℝ := x193*x194
  have hx195 : Bounds (2090455121 / 2000000000) (522662293 / 500000000) x195 := by
    apply bounds_mul hx193 hx194 <;> norm_num
  let x196 : ℝ := x193/(2 / 1)
  have hx196 : Bounds (2090455121 / 2000000000) (522662293 / 500000000) x196 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx195
  let x197 : ℝ := (1 / 1)+c
  have hx197 : Bounds (103683 / 62500) (207847 / 125000) x197 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hc <;> norm_num
  let x198 : ℝ := -c
  have hx198 : Bounds (-82847 / 125000) (-41183 / 62500) x198 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hc
  let x199 : ℝ := (1 / 1)+x198
  have hx199 : Bounds (42153 / 125000) (21317 / 62500) x199 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx198 <;> norm_num
  let x200 : ℝ := (1 / 1)-c
  have hx200 : Bounds (42153 / 125000) (21317 / 62500) x200 := by
    exact hx199
  let x201 : ℝ := x200⁻¹
  have hx201 : Bounds (2931932260637 / 1000000000000) (593077598273 / 200000000000) x201 := by
    apply bounds_inv hx200 <;> norm_num
  let x202 : ℝ := x197*x201
  have hx202 : Bounds (2431932260637 / 500000000000) (493077598273 / 100000000000) x202 := by
    apply bounds_mul hx197 hx201 <;> norm_num
  let x203 : ℝ := x197/x200
  have hx203 : Bounds (2431932260637 / 500000000000) (493077598273 / 100000000000) x203 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx202
  let x204 : ℝ := Real.log x203
  have hx204 : Bounds (1581833289 / 1000000000) (1595496377 / 1000000000) x204 := by
    exact bounds_log hx203 (by norm_num) (by simpa only [div_one] using reflection_log_18.1) (by simpa only [div_one] using reflection_log_19.2)
  let x205 : ℝ := (2 / 1)⁻¹
  have hx205 : Bounds (1 / 2) (1 / 2) x205 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x206 : ℝ := x204*x205
  have hx206 : Bounds (1581833289 / 2000000000) (1595496377 / 2000000000) x206 := by
    apply bounds_mul hx204 hx205 <;> norm_num
  let x207 : ℝ := x204/(2 / 1)
  have hx207 : Bounds (1581833289 / 2000000000) (1595496377 / 2000000000) x207 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx206
  let x208 : ℝ := (2 / 1)*x50
  have hx208 : Bounds (558875865371 / 500000000000) (2249340581 / 2000000000) x208 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx50 <;> norm_num
  let x209 : ℝ := (2 / 1)*x96
  have hx209 : Bounds (346534526431 / 500000000000) (693147181 / 1000000000) x209 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx96 <;> norm_num
  let x210 : ℝ := -x209
  have hx210 : Bounds (-693147181 / 1000000000) (-346534526431 / 500000000000) x210 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx209
  let x211 : ℝ := x208+x210
  have hx211 : Bounds (212302274871 / 500000000000) (215800618819 / 500000000000) x211 := by
    apply bounds_add hx208 hx210 <;> norm_num
  let x212 : ℝ := x208-x209
  have hx212 : Bounds (212302274871 / 500000000000) (215800618819 / 500000000000) x212 := by
    exact hx211
  let x213 : ℝ := y*x196
  have hx213 : Bounds (407609482223 / 500000000000) (407667180619 / 500000000000) x213 := by
    apply bounds_mul hy hx196 <;> norm_num
  let x214 : ℝ := -x213
  have hx214 : Bounds (-407667180619 / 500000000000) (-407609482223 / 500000000000) x214 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx213
  let x215 : ℝ := x212+x214
  have hx215 : Bounds (-48841226437 / 125000000000) (-47952215851 / 125000000000) x215 := by
    apply bounds_add hx212 hx214 <;> norm_num
  let x216 : ℝ := x212-x213
  have hx216 : Bounds (-48841226437 / 125000000000) (-47952215851 / 125000000000) x216 := by
    exact hx215
  let x217 : ℝ := x3*x207
  have hx217 : Bounds (1581833289 / 4000000000) (403860020429 / 1000000000000) x217 := by
    apply bounds_mul hx3 hx207 <;> norm_num
  let x218 : ℝ := x216+x217
  have hx218 : Bounds (2364255377 / 500000000000) (20242293621 / 1000000000000) x218 := by
    apply bounds_add hx216 hx217 <;> norm_num
  have hpos : 0 < x218 := lt_of_lt_of_le (by norm_num) hx218.1
  have hcert :
      0 ≤ 2 * biasE (1 - 2*m) - 2*(x96)
        - (1 - 2*entropyInverse (H (2*m)/2)) *
            SmallMean.A (1 - 2*entropyInverse (H (2*m)/2))
        + (1 - 2*m) *
            SmallMean.A (regularContact ((1 - 2*m)/(Real.log 2*(H (2*m)/2)))) := by
    simpa +zetaDelta only [SmallMean.A, div_one] using hpos.le
  dsimp only
  nlinarith [hcert, hLh]

theorem acceptedCertificate : DoubleCapBiasCellCertificate (79 / 320) (1 / 4) (fun m => H (2*m)/2) where
  domain := by norm_num
  sound m hmLo hmHi := by
    exact cell_bias_nonneg m ⟨hmLo, hmHi⟩

theorem accepted_cell :
    ∀ m, (79 / 320) ≤ m → m ≤ (1 / 4) → 0 ≤ doubleCapLowResidual m := by
  intro m hmLo hmHi
  unfold doubleCapLowResidual
  apply doubleCapEndpointResidual_nonneg_of_biasCell acceptedCertificate hmLo hmHi
  exact div_pos (H_pos (by linarith) (by linarith)) two_pos

#print axioms cell_bias_nonneg
#print axioms accepted_cell

end GeneralCK.Certificates.DoubleCapMiddle.Cell0009

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0010 =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0010
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Reflection
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem cell_bias_nonneg (m : ℝ) (hm : Bounds (1 / 4) (2563 / 10240) m) :
    let h := (1 + H (2*m - 1/2))/2
    let x := 1-2*m
    let y := 1-2*entropyInverse h
    let c := regularContact (x/(Real.log 2*h))
    0 ≤ 2*(biasE x-Real.log 2*h)-y*SmallMean.A y+x*SmallMean.A c := by
  have hEq : biasE (2-4*m) = Real.log 2 * H (2*m-1/2) := by
    by_cases hquarter : m = 1/4
    · subst m
      norm_num [biasE, H_zero]
    · have hmstrict : 1/4 < m := lt_of_le_of_ne hm.1 (Ne.symm hquarter)
      rw [show 2-4*m = 1-2*(2*m-1/2) by ring,
        GeneralCK.Correction.Natural.biasE_probability (by linarith [hmstrict]) (by linarith [hm.2]),
        GeneralCK.Certificates.Mixed.hn_eq_H_mul_log]
      ring
  have hLh : Real.log 2 * ((1 + H (2*m - 1/2))/2) = (Real.log 2 + biasE (2-4*m))/2 := by
    rw [hEq]
    ring
  let x0 : ℝ := (2 / 1)*m
  have hx0 : Bounds (1 / 2) (2563 / 5120) x0 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hm <;> norm_num
  let x1 : ℝ := -x0
  have hx1 : Bounds (-2563 / 5120) (-1 / 2) x1 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx0
  let x2 : ℝ := (1 / 1)+x1
  have hx2 : Bounds (2557 / 5120) (1 / 2) x2 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx1 <;> norm_num
  let x3 : ℝ := (1 / 1)-x0
  have hx3 : Bounds (2557 / 5120) (1 / 2) x3 := by
    exact hx2
  let x4 : ℝ := (4 / 1)*m
  have hx4 : Bounds (1 / 1) (2563 / 2560) x4 := by
    apply bounds_mul (bounds_const ((4 / 1) : ℝ)) hm <;> norm_num
  let x5 : ℝ := -x4
  have hx5 : Bounds (-2563 / 2560) (-1 / 1) x5 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx4
  let x6 : ℝ := (2 / 1)+x5
  have hx6 : Bounds (2557 / 2560) (1 / 1) x6 := by
    apply bounds_add (bounds_const ((2 / 1) : ℝ)) hx5 <;> norm_num
  let x7 : ℝ := (2 / 1)-x4
  have hx7 : Bounds (2557 / 2560) (1 / 1) x7 := by
    exact hx6
  let x8 : ℝ := Real.log (2 / 1)
  have hx8 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x8 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x9 : ℝ := (1 / 1)+(1 / 2)
  have hx9 : Bounds (3 / 2) (3 / 2) x9 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1 / 2) : ℝ)) <;> norm_num
  let x10 : ℝ := (1 / 1)+(1 / 2)
  have hx10 : Bounds (3 / 2) (3 / 2) x10 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1 / 2) : ℝ)) <;> norm_num
  let x11 : ℝ := Real.log x10
  have hx11 : Bounds (101366277 / 250000000) (405465109 / 1000000000) x11 := by
    exact bounds_log hx10 (by norm_num) (by simpa only [div_one] using reflection_log_1.1) (by simpa only [div_one] using reflection_log_1.2)
  let x12 : ℝ := x9*x11
  have hx12 : Bounds (304098831 / 500000000) (1216395327 / 2000000000) x12 := by
    apply bounds_mul hx9 hx11 <;> norm_num
  let x13 : ℝ := -(1 / 2)
  have hx13 : Bounds (-1 / 2) (-1 / 2) x13 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1 / 2) : ℝ))
  let x14 : ℝ := (1 / 1)+x13
  have hx14 : Bounds (1 / 2) (1 / 2) x14 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx13 <;> norm_num
  let x15 : ℝ := (1 / 1)-(1 / 2)
  have hx15 : Bounds (1 / 2) (1 / 2) x15 := by
    exact hx14
  let x16 : ℝ := -(1 / 2)
  have hx16 : Bounds (-1 / 2) (-1 / 2) x16 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1 / 2) : ℝ))
  let x17 : ℝ := (1 / 1)+x16
  have hx17 : Bounds (1 / 2) (1 / 2) x17 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx16 <;> norm_num
  let x18 : ℝ := (1 / 1)-(1 / 2)
  have hx18 : Bounds (1 / 2) (1 / 2) x18 := by
    exact hx17
  let x19 : ℝ := Real.log x18
  have hx19 : Bounds (-693147181 / 1000000000) (-34657359 / 50000000) x19 := by
    exact bounds_log hx18 (by norm_num) (by simpa only [div_one] using reflection_log_2.1) (by simpa only [div_one] using reflection_log_2.2)
  let x20 : ℝ := x15*x19
  have hx20 : Bounds (-693147181 / 2000000000) (-34657359 / 100000000) x20 := by
    apply bounds_mul hx15 hx19 <;> norm_num
  let x21 : ℝ := x12+x20
  have hx21 : Bounds (523248143 / 2000000000) (523248147 / 2000000000) x21 := by
    apply bounds_add hx12 hx20 <;> norm_num
  let x22 : ℝ := (2 / 1)⁻¹
  have hx22 : Bounds (1 / 2) (1 / 2) x22 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x23 : ℝ := x21*x22
  have hx23 : Bounds (523248143 / 4000000000) (523248147 / 4000000000) x23 := by
    apply bounds_mul hx21 hx22 <;> norm_num
  let x24 : ℝ := x21/(2 / 1)
  have hx24 : Bounds (523248143 / 4000000000) (523248147 / 4000000000) x24 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx23
  let x25 : ℝ := -x24
  have hx25 : Bounds (-523248147 / 4000000000) (-523248143 / 4000000000) x25 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx24
  let x26 : ℝ := x8+x25
  have hx26 : Bounds (2249340573 / 4000000000) (2249340581 / 4000000000) x26 := by
    apply bounds_add hx8 hx25 <;> norm_num
  let x27 : ℝ := x8-x24
  have hx27 : Bounds (2249340573 / 4000000000) (2249340581 / 4000000000) x27 := by
    exact hx26
  let x28 : ℝ := biasE (1 / 2)
  have hx28 : Bounds (2249340573 / 4000000000) (2249340581 / 4000000000) x28 := by
    simpa +zetaDelta only [biasE, div_one] using hx27
  let x29 : ℝ := Real.log (2 / 1)
  have hx29 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x29 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x30 : ℝ := (1 / 1)+(2557 / 5120)
  have hx30 : Bounds (7677 / 5120) (7677 / 5120) x30 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((2557 / 5120) : ℝ)) <;> norm_num
  let x31 : ℝ := (1 / 1)+(2557 / 5120)
  have hx31 : Bounds (7677 / 5120) (7677 / 5120) x31 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((2557 / 5120) : ℝ)) <;> norm_num
  let x32 : ℝ := Real.log x31
  have hx32 : Bounds (202537203 / 500000000) (405074407 / 1000000000) x32 := by
    exact bounds_log hx31 (by norm_num) (by simpa only [div_one] using reflection_log_3.1) (by simpa only [div_one] using reflection_log_3.2)
  let x33 : ℝ := x30*x32
  have hx33 : Bounds (121474852143 / 200000000000) (121474852443 / 200000000000) x33 := by
    apply bounds_mul hx30 hx32 <;> norm_num
  let x34 : ℝ := -(2557 / 5120)
  have hx34 : Bounds (-2557 / 5120) (-2557 / 5120) x34 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((2557 / 5120) : ℝ))
  let x35 : ℝ := (1 / 1)+x34
  have hx35 : Bounds (2563 / 5120) (2563 / 5120) x35 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx34 <;> norm_num
  let x36 : ℝ := (1 / 1)-(2557 / 5120)
  have hx36 : Bounds (2563 / 5120) (2563 / 5120) x36 := by
    exact hx35
  let x37 : ℝ := -(2557 / 5120)
  have hx37 : Bounds (-2557 / 5120) (-2557 / 5120) x37 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((2557 / 5120) : ℝ))
  let x38 : ℝ := (1 / 1)+x37
  have hx38 : Bounds (2563 / 5120) (2563 / 5120) x38 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx37 <;> norm_num
  let x39 : ℝ := (1 / 1)-(2557 / 5120)
  have hx39 : Bounds (2563 / 5120) (2563 / 5120) x39 := by
    exact hx38
  let x40 : ℝ := Real.log x39
  have hx40 : Bounds (-86496999 / 125000000) (-691975991 / 1000000000) x40 := by
    exact bounds_log hx39 (by norm_num) (by simpa only [div_one] using reflection_log_4.1) (by simpa only [div_one] using reflection_log_4.2)
  let x41 : ℝ := x36*x40
  have hx41 : Bounds (-346393450683 / 1000000000000) (-173196725091 / 500000000000) x41 := by
    apply bounds_mul hx36 hx40 <;> norm_num
  let x42 : ℝ := x33+x41
  have hx42 : Bounds (16311300627 / 62500000000) (260980812033 / 1000000000000) x42 := by
    apply bounds_add hx33 hx41 <;> norm_num
  let x43 : ℝ := (2 / 1)⁻¹
  have hx43 : Bounds (1 / 2) (1 / 2) x43 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x44 : ℝ := x42*x43
  have hx44 : Bounds (16311300627 / 125000000000) (130490406017 / 1000000000000) x44 := by
    apply bounds_mul hx42 hx43 <;> norm_num
  let x45 : ℝ := x42/(2 / 1)
  have hx45 : Bounds (16311300627 / 125000000000) (130490406017 / 1000000000000) x45 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx44
  let x46 : ℝ := -x45
  have hx46 : Bounds (-130490406017 / 1000000000000) (-16311300627 / 125000000000) x46 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx45
  let x47 : ℝ := x29+x46
  have hx47 : Bounds (562656773983 / 1000000000000) (35166048499 / 62500000000) x47 := by
    apply bounds_add hx29 hx46 <;> norm_num
  let x48 : ℝ := x29-x45
  have hx48 : Bounds (562656773983 / 1000000000000) (35166048499 / 62500000000) x48 := by
    exact hx47
  let x49 : ℝ := biasE (2557 / 5120)
  have hx49 : Bounds (562656773983 / 1000000000000) (35166048499 / 62500000000) x49 := by
    simpa +zetaDelta only [biasE, div_one] using hx48
  let x50 : ℝ := biasE x3
  have hx50 : Bounds (2249340573 / 4000000000) (35166048499 / 62500000000) x50 := by
    exact bounds_biasE hx3 (by norm_num) (by norm_num) hx28.1 hx49.2
  let x51 : ℝ := Real.log (2 / 1)
  have hx51 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x51 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x52 : ℝ := (1 / 1)+(2557 / 2560)
  have hx52 : Bounds (5117 / 2560) (5117 / 2560) x52 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((2557 / 2560) : ℝ)) <;> norm_num
  let x53 : ℝ := (1 / 1)+(2557 / 2560)
  have hx53 : Bounds (5117 / 2560) (5117 / 2560) x53 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((2557 / 2560) : ℝ)) <;> norm_num
  let x54 : ℝ := Real.log x53
  have hx54 : Bounds (692561071 / 1000000000) (43285067 / 62500000) x54 := by
    exact bounds_log hx53 (by norm_num) (by simpa only [div_one] using reflection_log_5.1) (by simpa only [div_one] using reflection_log_5.2)
  let x55 : ℝ := x52*x54
  have hx55 : Bounds (692155273497 / 500000000000) (692155274497 / 500000000000) x55 := by
    apply bounds_mul hx52 hx54 <;> norm_num
  let x56 : ℝ := -(2557 / 2560)
  have hx56 : Bounds (-2557 / 2560) (-2557 / 2560) x56 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((2557 / 2560) : ℝ))
  let x57 : ℝ := (1 / 1)+x56
  have hx57 : Bounds (3 / 2560) (3 / 2560) x57 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx56 <;> norm_num
  let x58 : ℝ := (1 / 1)-(2557 / 2560)
  have hx58 : Bounds (3 / 2560) (3 / 2560) x58 := by
    exact hx57
  let x59 : ℝ := -(2557 / 2560)
  have hx59 : Bounds (-2557 / 2560) (-2557 / 2560) x59 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((2557 / 2560) : ℝ))
  let x60 : ℝ := (1 / 1)+x59
  have hx60 : Bounds (3 / 2560) (3 / 2560) x60 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx59 <;> norm_num
  let x61 : ℝ := (1 / 1)-(2557 / 2560)
  have hx61 : Bounds (3 / 2560) (3 / 2560) x61 := by
    exact hx60
  let x62 : ℝ := Real.log x61
  have hx62 : Bounds (-6749150253 / 1000000000) (-6749150243 / 1000000000) x62 := by
    exact bounds_log hx61 (by norm_num) (by simpa only [div_one] using reflection_log_6.1) (by simpa only [div_one] using reflection_log_6.2)
  let x63 : ℝ := x58*x62
  have hx63 : Bounds (-7909160453 / 1000000000000) (-7909160441 / 1000000000000) x63 := by
    apply bounds_mul hx58 hx62 <;> norm_num
  let x64 : ℝ := x55+x63
  have hx64 : Bounds (1376401386541 / 1000000000000) (1376401388553 / 1000000000000) x64 := by
    apply bounds_add hx55 hx63 <;> norm_num
  let x65 : ℝ := (2 / 1)⁻¹
  have hx65 : Bounds (1 / 2) (1 / 2) x65 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x66 : ℝ := x64*x65
  have hx66 : Bounds (68820069327 / 100000000000) (688200694277 / 1000000000000) x66 := by
    apply bounds_mul hx64 hx65 <;> norm_num
  let x67 : ℝ := x64/(2 / 1)
  have hx67 : Bounds (68820069327 / 100000000000) (688200694277 / 1000000000000) x67 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx66
  let x68 : ℝ := -x67
  have hx68 : Bounds (-688200694277 / 1000000000000) (-68820069327 / 100000000000) x68 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx67
  let x69 : ℝ := x51+x68
  have hx69 : Bounds (4946485723 / 1000000000000) (494648773 / 100000000000) x69 := by
    apply bounds_add hx51 hx68 <;> norm_num
  let x70 : ℝ := x51-x67
  have hx70 : Bounds (4946485723 / 1000000000000) (494648773 / 100000000000) x70 := by
    exact hx69
  let x71 : ℝ := biasE (2557 / 2560)
  have hx71 : Bounds (4946485723 / 1000000000000) (494648773 / 100000000000) x71 := by
    simpa +zetaDelta only [biasE, div_one] using hx70
  let x72 : ℝ := biasE x7
  have hx72 : Bounds (0 / 1) (494648773 / 100000000000) x72 := by
    exact bounds_biasE hx7 (by norm_num) (by norm_num) (by norm_num [biasE]) hx71.2
  let x73 : ℝ := Real.log (2 / 1)
  have hx73 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x73 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x74 : ℝ := x73+x72
  have hx74 : Bounds (34657359 / 50000000) (69809366873 / 100000000000) x74 := by
    apply bounds_add hx73 hx72 <;> norm_num
  let x75 : ℝ := (2 / 1)⁻¹
  have hx75 : Bounds (1 / 2) (1 / 2) x75 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x76 : ℝ := x74*x75
  have hx76 : Bounds (34657359 / 100000000) (69809366873 / 200000000000) x76 := by
    apply bounds_mul hx74 hx75 <;> norm_num
  let x77 : ℝ := x74/(2 / 1)
  have hx77 : Bounds (34657359 / 100000000) (69809366873 / 200000000000) x77 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx76
  let x78 : ℝ := Real.log (2 / 1)
  have hx78 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x78 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x79 : ℝ := (1 / 1)+(777571 / 1000000)
  have hx79 : Bounds (1777571 / 1000000) (1777571 / 1000000) x79 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((777571 / 1000000) : ℝ)) <;> norm_num
  let x80 : ℝ := (1 / 1)+(777571 / 1000000)
  have hx80 : Bounds (1777571 / 1000000) (1777571 / 1000000) x80 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((777571 / 1000000) : ℝ)) <;> norm_num
  let x81 : ℝ := Real.log x80
  have hx81 : Bounds (23009913 / 40000000) (287623913 / 500000000) x81 := by
    exact bounds_log hx80 (by norm_num) (by simpa only [div_one] using reflection_log_7.1) (by simpa only [div_one] using reflection_log_7.2)
  let x82 : ℝ := x79*x81
  have hx82 : Bounds (1022543851533 / 1000000000000) (1022543853311 / 1000000000000) x82 := by
    apply bounds_mul hx79 hx81 <;> norm_num
  let x83 : ℝ := -(777571 / 1000000)
  have hx83 : Bounds (-777571 / 1000000) (-777571 / 1000000) x83 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((777571 / 1000000) : ℝ))
  let x84 : ℝ := (1 / 1)+x83
  have hx84 : Bounds (222429 / 1000000) (222429 / 1000000) x84 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx83 <;> norm_num
  let x85 : ℝ := (1 / 1)-(777571 / 1000000)
  have hx85 : Bounds (222429 / 1000000) (222429 / 1000000) x85 := by
    exact hx84
  let x86 : ℝ := -(777571 / 1000000)
  have hx86 : Bounds (-777571 / 1000000) (-777571 / 1000000) x86 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((777571 / 1000000) : ℝ))
  let x87 : ℝ := (1 / 1)+x86
  have hx87 : Bounds (222429 / 1000000) (222429 / 1000000) x87 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx86 <;> norm_num
  let x88 : ℝ := (1 / 1)-(777571 / 1000000)
  have hx88 : Bounds (222429 / 1000000) (222429 / 1000000) x88 := by
    exact hx87
  let x89 : ℝ := Real.log x88
  have hx89 : Bounds (-1503147331 / 1000000000) (-23486677 / 15625000) x89 := by
    exact bounds_log hx88 (by norm_num) (by simpa only [div_one] using reflection_log_8.1) (by simpa only [div_one] using reflection_log_8.2)
  let x90 : ℝ := x85*x89
  have hx90 : Bounds (-334343557687 / 1000000000000) (-334343557019 / 1000000000000) x90 := by
    apply bounds_mul hx85 hx89 <;> norm_num
  let x91 : ℝ := x82+x90
  have hx91 : Bounds (344100146923 / 500000000000) (172050074073 / 250000000000) x91 := by
    apply bounds_add hx82 hx90 <;> norm_num
  let x92 : ℝ := (2 / 1)⁻¹
  have hx92 : Bounds (1 / 2) (1 / 2) x92 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x93 : ℝ := x91*x92
  have hx93 : Bounds (344100146923 / 1000000000000) (172050074073 / 500000000000) x93 := by
    apply bounds_mul hx91 hx92 <;> norm_num
  let x94 : ℝ := x91/(2 / 1)
  have hx94 : Bounds (344100146923 / 1000000000000) (172050074073 / 500000000000) x94 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx93
  let x95 : ℝ := -x94
  have hx95 : Bounds (-172050074073 / 500000000000) (-344100146923 / 1000000000000) x95 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx94
  let x96 : ℝ := x78+x95
  have hx96 : Bounds (174523515927 / 500000000000) (349047034077 / 1000000000000) x96 := by
    apply bounds_add hx78 hx95 <;> norm_num
  let x97 : ℝ := x78-x94
  have hx97 : Bounds (174523515927 / 500000000000) (349047034077 / 1000000000000) x97 := by
    exact hx96
  let x98 : ℝ := biasE (777571 / 1000000)
  have hx98 : Bounds (174523515927 / 500000000000) (349047034077 / 1000000000000) x98 := by
    simpa +zetaDelta only [biasE, div_one] using hx97
  let x99 : ℝ := Real.log (2 / 1)
  have hx99 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x99 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x100 : ℝ := (1 / 1)+(155989 / 200000)
  have hx100 : Bounds (355989 / 200000) (355989 / 200000) x100 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((155989 / 200000) : ℝ)) <;> norm_num
  let x101 : ℝ := (1 / 1)+(155989 / 200000)
  have hx101 : Bounds (355989 / 200000) (355989 / 200000) x101 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((155989 / 200000) : ℝ)) <;> norm_num
  let x102 : ℝ := Real.log x101
  have hx102 : Bounds (9009101 / 15625000) (115316493 / 200000000) x102 := by
    exact bounds_log hx101 (by norm_num) (by simpa only [div_one] using reflection_log_9.1) (by simpa only [div_one] using reflection_log_9.2)
  let x103 : ℝ := x100*x102
  have hx103 : Bounds (256571268471 / 250000000000) (205257015133 / 200000000000) x103 := by
    apply bounds_mul hx100 hx102 <;> norm_num
  let x104 : ℝ := -(155989 / 200000)
  have hx104 : Bounds (-155989 / 200000) (-155989 / 200000) x104 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((155989 / 200000) : ℝ))
  let x105 : ℝ := (1 / 1)+x104
  have hx105 : Bounds (44011 / 200000) (44011 / 200000) x105 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx104 <;> norm_num
  let x106 : ℝ := (1 / 1)-(155989 / 200000)
  have hx106 : Bounds (44011 / 200000) (44011 / 200000) x106 := by
    exact hx105
  let x107 : ℝ := -(155989 / 200000)
  have hx107 : Bounds (-155989 / 200000) (-155989 / 200000) x107 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((155989 / 200000) : ℝ))
  let x108 : ℝ := (1 / 1)+x107
  have hx108 : Bounds (44011 / 200000) (44011 / 200000) x108 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx107 <;> norm_num
  let x109 : ℝ := (1 / 1)-(155989 / 200000)
  have hx109 : Bounds (44011 / 200000) (44011 / 200000) x109 := by
    exact hx108
  let x110 : ℝ := Real.log x109
  have hx110 : Bounds (-302775553 / 200000000) (-756938881 / 500000000) x110 := by
    exact bounds_log hx109 (by norm_num) (by simpa only [div_one] using reflection_log_10.1) (by simpa only [div_one] using reflection_log_10.2)
  let x111 : ℝ := x106*x110
  have hx111 : Bounds (-166568185789 / 500000000000) (-83284092729 / 250000000000) x111 := by
    apply bounds_mul hx106 hx110 <;> norm_num
  let x112 : ℝ := x103+x111
  have hx112 : Bounds (346574351153 / 500000000000) (693148704749 / 1000000000000) x112 := by
    apply bounds_add hx103 hx111 <;> norm_num
  let x113 : ℝ := (2 / 1)⁻¹
  have hx113 : Bounds (1 / 2) (1 / 2) x113 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x114 : ℝ := x112*x113
  have hx114 : Bounds (346574351153 / 1000000000000) (2772594819 / 8000000000) x114 := by
    apply bounds_mul hx112 hx113 <;> norm_num
  let x115 : ℝ := x112/(2 / 1)
  have hx115 : Bounds (346574351153 / 1000000000000) (2772594819 / 8000000000) x115 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx114
  let x116 : ℝ := -x115
  have hx116 : Bounds (-2772594819 / 8000000000) (-346574351153 / 1000000000000) x116 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx115
  let x117 : ℝ := x99+x116
  have hx117 : Bounds (2772582621 / 8000000000) (346572829847 / 1000000000000) x117 := by
    apply bounds_add hx99 hx116 <;> norm_num
  let x118 : ℝ := x99-x115
  have hx118 : Bounds (2772582621 / 8000000000) (346572829847 / 1000000000000) x118 := by
    exact hx117
  let x119 : ℝ := biasE (155989 / 200000)
  have hx119 : Bounds (2772582621 / 8000000000) (346572829847 / 1000000000000) x119 := by
    simpa +zetaDelta only [biasE, div_one] using hx118
  let y : ℝ := 1 - 2 * entropyInverse ((1 + H (2*m - 1/2))/2)
  have hLh' : Real.log 2 * ((1 + H (2*m - 1/2))/2) = x77 := by
    simpa +zetaDelta only [div_one] using hLh
  have hy : Bounds (777571 / 1000000) (155989 / 200000) y := by
    apply entropyInverseBias_bracket
    · exact div_nonneg (add_nonneg zero_le_one
        (H_nonneg (by linarith [hm.1]) (by linarith [hm.2]))) two_pos.le
    · linarith [H_le_one (2*m-1/2)]
    · norm_num
    · norm_num
    · norm_num
    · have h1 : biasE (155989 / 200000) ≤ (346572829847 / 1000000000000) := hx119.2
      have h2 : (34657359 / 100000000) ≤ x77 := hx77.1
      linarith [hLh']
    · have h1 : x77 ≤ (69809366873 / 200000000000) := hx77.2
      have h2 : (174523515927 / 500000000000) ≤ biasE (777571 / 1000000) := hx98.1
      linarith [hLh']
  let x120 : ℝ := x3⁻¹
  have hx120 : Bounds (2 / 1) (400469299961 / 200000000000) x120 := by
    apply bounds_inv hx3 <;> norm_num
  let x121 : ℝ := x77*x120
  have hx121 : Bounds (34657359 / 50000000) (698912707059 / 1000000000000) x121 := by
    apply bounds_mul hx77 hx120 <;> norm_num
  let x122 : ℝ := x77/x3
  have hx122 : Bounds (34657359 / 50000000) (698912707059 / 1000000000000) x122 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx121
  let x123 : ℝ := Real.log (2 / 1)
  have hx123 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x123 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x124 : ℝ := (1 / 1)+(328187 / 500000)
  have hx124 : Bounds (828187 / 500000) (828187 / 500000) x124 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((328187 / 500000) : ℝ)) <;> norm_num
  let x125 : ℝ := (1 / 1)+(328187 / 500000)
  have hx125 : Bounds (828187 / 500000) (828187 / 500000) x125 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((328187 / 500000) : ℝ)) <;> norm_num
  let x126 : ℝ := Real.log x125
  have hx126 : Bounds (4037047 / 8000000) (126157719 / 250000000) x126 := by
    exact bounds_log hx125 (by norm_num) (by simpa only [div_one] using reflection_log_11.1) (by simpa only [div_one] using reflection_log_11.2)
  let x127 : ℝ := x124*x126
  have hx127 : Bounds (835857460947 / 1000000000000) (208964365651 / 250000000000) x127 := by
    apply bounds_mul hx124 hx126 <;> norm_num
  let x128 : ℝ := -(328187 / 500000)
  have hx128 : Bounds (-328187 / 500000) (-328187 / 500000) x128 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((328187 / 500000) : ℝ))
  let x129 : ℝ := (1 / 1)+x128
  have hx129 : Bounds (171813 / 500000) (171813 / 500000) x129 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx128 <;> norm_num
  let x130 : ℝ := (1 / 1)-(328187 / 500000)
  have hx130 : Bounds (171813 / 500000) (171813 / 500000) x130 := by
    exact hx129
  let x131 : ℝ := -(328187 / 500000)
  have hx131 : Bounds (-328187 / 500000) (-328187 / 500000) x131 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((328187 / 500000) : ℝ))
  let x132 : ℝ := (1 / 1)+x131
  have hx132 : Bounds (171813 / 500000) (171813 / 500000) x132 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx131 <;> norm_num
  let x133 : ℝ := (1 / 1)-(328187 / 500000)
  have hx133 : Bounds (171813 / 500000) (171813 / 500000) x133 := by
    exact hx132
  let x134 : ℝ := Real.log x133
  have hx134 : Bounds (-1068201423 / 1000000000) (-1068201421 / 1000000000) x134 := by
    exact bounds_log hx133 (by norm_num) (by simpa only [div_one] using reflection_log_12.1) (by simpa only [div_one] using reflection_log_12.2)
  let x135 : ℝ := x130*x134
  have hx135 : Bounds (-18353089109 / 50000000000) (-91765445373 / 250000000000) x135 := by
    apply bounds_mul hx130 hx134 <;> norm_num
  let x136 : ℝ := x127+x135
  have hx136 : Bounds (468795678767 / 1000000000000) (58599460139 / 125000000000) x136 := by
    apply bounds_add hx127 hx135 <;> norm_num
  let x137 : ℝ := (2 / 1)⁻¹
  have hx137 : Bounds (1 / 2) (1 / 2) x137 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x138 : ℝ := x136*x137
  have hx138 : Bounds (234397839383 / 1000000000000) (58599460139 / 250000000000) x138 := by
    apply bounds_mul hx136 hx137 <;> norm_num
  let x139 : ℝ := x136/(2 / 1)
  have hx139 : Bounds (234397839383 / 1000000000000) (58599460139 / 250000000000) x139 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx138
  let x140 : ℝ := -x139
  have hx140 : Bounds (-58599460139 / 250000000000) (-234397839383 / 1000000000000) x140 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx139
  let x141 : ℝ := x123+x140
  have hx141 : Bounds (114687334861 / 250000000000) (458749341617 / 1000000000000) x141 := by
    apply bounds_add hx123 hx140 <;> norm_num
  let x142 : ℝ := x123-x139
  have hx142 : Bounds (114687334861 / 250000000000) (458749341617 / 1000000000000) x142 := by
    exact hx141
  let x143 : ℝ := biasE (328187 / 500000)
  have hx143 : Bounds (114687334861 / 250000000000) (458749341617 / 1000000000000) x143 := by
    simpa +zetaDelta only [biasE, div_one] using hx142
  let x144 : ℝ := Real.log (2 / 1)
  have hx144 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x144 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x145 : ℝ := (1 / 1)+(658929 / 1000000)
  have hx145 : Bounds (1658929 / 1000000) (1658929 / 1000000) x145 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((658929 / 1000000) : ℝ)) <;> norm_num
  let x146 : ℝ := (1 / 1)+(658929 / 1000000)
  have hx146 : Bounds (1658929 / 1000000) (1658929 / 1000000) x146 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((658929 / 1000000) : ℝ)) <;> norm_num
  let x147 : ℝ := Real.log x146
  have hx147 : Bounds (506172213 / 1000000000) (253086107 / 500000000) x147 := by
    exact bounds_log hx146 (by norm_num) (by simpa only [div_one] using reflection_log_13.1) (by simpa only [div_one] using reflection_log_13.2)
  let x148 : ℝ := x145*x147
  have hx148 : Bounds (839703763139 / 1000000000000) (839703764799 / 1000000000000) x148 := by
    apply bounds_mul hx145 hx147 <;> norm_num
  let x149 : ℝ := -(658929 / 1000000)
  have hx149 : Bounds (-658929 / 1000000) (-658929 / 1000000) x149 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((658929 / 1000000) : ℝ))
  let x150 : ℝ := (1 / 1)+x149
  have hx150 : Bounds (341071 / 1000000) (341071 / 1000000) x150 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx149 <;> norm_num
  let x151 : ℝ := (1 / 1)-(658929 / 1000000)
  have hx151 : Bounds (341071 / 1000000) (341071 / 1000000) x151 := by
    exact hx150
  let x152 : ℝ := -(658929 / 1000000)
  have hx152 : Bounds (-658929 / 1000000) (-658929 / 1000000) x152 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((658929 / 1000000) : ℝ))
  let x153 : ℝ := (1 / 1)+x152
  have hx153 : Bounds (341071 / 1000000) (341071 / 1000000) x153 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx152 <;> norm_num
  let x154 : ℝ := (1 / 1)-(658929 / 1000000)
  have hx154 : Bounds (341071 / 1000000) (341071 / 1000000) x154 := by
    exact hx153
  let x155 : ℝ := Real.log x154
  have hx155 : Bounds (-1075664613 / 1000000000) (-1075664611 / 1000000000) x155 := by
    exact bounds_log hx154 (by norm_num) (by simpa only [div_one] using reflection_log_14.1) (by simpa only [div_one] using reflection_log_14.2)
  let x156 : ℝ := x151*x155
  have hx156 : Bounds (-366878005221 / 1000000000000) (-183439002269 / 500000000000) x156 := by
    apply bounds_mul hx151 hx155 <;> norm_num
  let x157 : ℝ := x148+x156
  have hx157 : Bounds (236412878959 / 500000000000) (472825760261 / 1000000000000) x157 := by
    apply bounds_add hx148 hx156 <;> norm_num
  let x158 : ℝ := (2 / 1)⁻¹
  have hx158 : Bounds (1 / 2) (1 / 2) x158 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x159 : ℝ := x157*x158
  have hx159 : Bounds (236412878959 / 1000000000000) (236412880131 / 1000000000000) x159 := by
    apply bounds_mul hx157 hx158 <;> norm_num
  let x160 : ℝ := x157/(2 / 1)
  have hx160 : Bounds (236412878959 / 1000000000000) (236412880131 / 1000000000000) x160 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx159
  let x161 : ℝ := -x160
  have hx161 : Bounds (-236412880131 / 1000000000000) (-236412878959 / 1000000000000) x161 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx160
  let x162 : ℝ := x144+x161
  have hx162 : Bounds (456734299869 / 1000000000000) (456734302041 / 1000000000000) x162 := by
    apply bounds_add hx144 hx161 <;> norm_num
  let x163 : ℝ := x144-x160
  have hx163 : Bounds (456734299869 / 1000000000000) (456734302041 / 1000000000000) x163 := by
    exact hx162
  let x164 : ℝ := biasE (658929 / 1000000)
  have hx164 : Bounds (456734299869 / 1000000000000) (456734302041 / 1000000000000) x164 := by
    simpa +zetaDelta only [biasE, div_one] using hx163
  let x165 : ℝ := x122*(328187 / 500000)
  have hx165 : Bounds (3639710297 / 8000000000) (14335879037 / 31250000000) x165 := by
    apply bounds_mul hx122 (bounds_const ((328187 / 500000) : ℝ)) <;> norm_num
  let x166 : ℝ := x122*(658929 / 1000000)
  have hx166 : Bounds (45673477817 / 100000000000) (9210677023 / 20000000000) x166 := by
    apply bounds_mul hx122 (bounds_const ((658929 / 1000000) : ℝ)) <;> norm_num
  let c : ℝ := Reflection.regularContact (x3 / (Real.log 2 * ((1 + H (2*m - 1/2))/2)))
  have hcMem := Reflection.regularContact_mem
    (x3 / (Real.log 2 * ((1 + H (2*m - 1/2))/2)))
  have hc0 : 0 ≤ c := by
    dsimp only [c]
    apply GeneralCK.Certificates.RegularContactBounds.regularContact_nonneg
    rw [hLh']
    exact div_nonneg (by linarith [hx3.1]) (by linarith [hx77.1])
  have hcEq : biasE c = x122 * c := by
    have he := Reflection.regularContact_equation (x3 / x77)
    have hcdef : c = Reflection.regularContact (x3 / x77) := by
      dsimp only [c]
      rw [hLh']
    rw [← hcdef] at he
    change biasE c = (x77 / x3) * c
    have hx0 : 0 < x3 := by linarith [hx3.1]
    have hh0 : 0 < x77 := by linarith [hx77.1]
    field_simp [hx0.ne', hh0.ne'] at he ⊢
    nlinarith
  have hc : Bounds (328187 / 500000) (658929 / 1000000) c := by
    apply contact_bracket hc0 hcMem.2.le (by norm_num) (by norm_num) (by norm_num)
      (show 0 < x122 by linarith [hx122.1]) hcEq
    · have h1 : x122 * (328187 / 500000) ≤ (14335879037 / 31250000000) := hx165.2
      have h2 : (114687334861 / 250000000000) ≤ biasE (328187 / 500000) := hx143.1
      linarith
    · have h1 : biasE (658929 / 1000000) ≤ (456734302041 / 1000000000000) := hx164.2
      have h2 : (45673477817 / 100000000000) ≤ x122 * (658929 / 1000000) := hx166.1
      linarith
  let x167 : ℝ := (1 / 1)+y
  have hx167 : Bounds (1777571 / 1000000) (355989 / 200000) x167 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hy <;> norm_num
  let x168 : ℝ := -y
  have hx168 : Bounds (-155989 / 200000) (-777571 / 1000000) x168 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hy
  let x169 : ℝ := (1 / 1)+x168
  have hx169 : Bounds (44011 / 200000) (222429 / 1000000) x169 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx168 <;> norm_num
  let x170 : ℝ := (1 / 1)-y
  have hx170 : Bounds (44011 / 200000) (222429 / 1000000) x170 := by
    exact hx169
  let x171 : ℝ := x170⁻¹
  have hx171 : Bounds (2247908321307 / 500000000000) (4544318465839 / 1000000000000) x171 := by
    apply bounds_inv hx170 <;> norm_num
  let x172 : ℝ := x167*x171
  have hx172 : Bounds (1997908321307 / 250000000000) (4044318465839 / 500000000000) x172 := by
    apply bounds_mul hx167 hx171 <;> norm_num
  let x173 : ℝ := x167/x170
  have hx173 : Bounds (1997908321307 / 250000000000) (4044318465839 / 500000000000) x173 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx172
  let x174 : ℝ := Real.log x173
  have hx174 : Bounds (2078395153 / 1000000000) (2090460231 / 1000000000) x174 := by
    exact bounds_log hx173 (by norm_num) (by simpa only [div_one] using reflection_log_15.1) (by simpa only [div_one] using reflection_log_16.2)
  let x175 : ℝ := (2 / 1)⁻¹
  have hx175 : Bounds (1 / 2) (1 / 2) x175 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x176 : ℝ := x174*x175
  have hx176 : Bounds (2078395153 / 2000000000) (2090460231 / 2000000000) x176 := by
    apply bounds_mul hx174 hx175 <;> norm_num
  let x177 : ℝ := x174/(2 / 1)
  have hx177 : Bounds (2078395153 / 2000000000) (2090460231 / 2000000000) x177 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx176
  let x178 : ℝ := (1 / 1)+c
  have hx178 : Bounds (828187 / 500000) (1658929 / 1000000) x178 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hc <;> norm_num
  let x179 : ℝ := -c
  have hx179 : Bounds (-658929 / 1000000) (-328187 / 500000) x179 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hc
  let x180 : ℝ := (1 / 1)+x179
  have hx180 : Bounds (341071 / 1000000) (171813 / 500000) x180 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx179 <;> norm_num
  let x181 : ℝ := (1 / 1)-c
  have hx181 : Bounds (341071 / 1000000) (171813 / 500000) x181 := by
    exact hx180
  let x182 : ℝ := x181⁻¹
  have hx182 : Bounds (14550703381 / 5000000000) (293194085689 / 100000000000) x182 := by
    apply bounds_inv hx181 <;> norm_num
  let x183 : ℝ := x178*x182
  have hx183 : Bounds (12050703381 / 2500000000) (243194085689 / 50000000000) x183 := by
    apply bounds_mul hx178 hx182 <;> norm_num
  let x184 : ℝ := x178/x181
  have hx184 : Bounds (12050703381 / 2500000000) (243194085689 / 50000000000) x184 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx183
  let x185 : ℝ := Real.log x184
  have hx185 : Bounds (1572832297 / 1000000000) (1581836827 / 1000000000) x185 := by
    exact bounds_log hx184 (by norm_num) (by simpa only [div_one] using reflection_log_17.1) (by simpa only [div_one] using reflection_log_18.2)
  let x186 : ℝ := (2 / 1)⁻¹
  have hx186 : Bounds (1 / 2) (1 / 2) x186 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x187 : ℝ := x185*x186
  have hx187 : Bounds (1572832297 / 2000000000) (1581836827 / 2000000000) x187 := by
    apply bounds_mul hx185 hx186 <;> norm_num
  let x188 : ℝ := x185/(2 / 1)
  have hx188 : Bounds (1572832297 / 2000000000) (1581836827 / 2000000000) x188 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx187
  let x189 : ℝ := (2 / 1)*x50
  have hx189 : Bounds (2249340573 / 2000000000) (35166048499 / 31250000000) x189 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx50 <;> norm_num
  let x190 : ℝ := (2 / 1)*x77
  have hx190 : Bounds (34657359 / 50000000) (69809366873 / 100000000000) x190 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx77 <;> norm_num
  let x191 : ℝ := -x190
  have hx191 : Bounds (-69809366873 / 100000000000) (-34657359 / 50000000) x191 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx190
  let x192 : ℝ := x189+x191
  have hx192 : Bounds (42657661777 / 100000000000) (3376299781 / 7812500000) x192 := by
    apply bounds_add hx189 hx191 <;> norm_num
  let x193 : ℝ := x189-x190
  have hx193 : Bounds (42657661777 / 100000000000) (3376299781 / 7812500000) x193 := by
    exact hx192
  let x194 : ℝ := y*x177
  have hx194 : Bounds (202012474689 / 250000000000) (407611001217 / 500000000000) x194 := by
    apply bounds_mul hy hx177 <;> norm_num
  let x195 : ℝ := -x194
  have hx195 : Bounds (-407611001217 / 500000000000) (-202012474689 / 250000000000) x195 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx194
  let x196 : ℝ := x193+x195
  have hx196 : Bounds (-48580673083 / 125000000000) (-93970881697 / 250000000000) x196 := by
    apply bounds_add hx193 hx195 <;> norm_num
  let x197 : ℝ := x193-x194
  have hx197 : Bounds (-48580673083 / 125000000000) (-93970881697 / 250000000000) x197 := by
    exact hx196
  let x198 : ℝ := x3*x188
  have hx198 : Bounds (392747283537 / 1000000000000) (1581836827 / 4000000000) x198 := by
    apply bounds_mul hx3 hx188 <;> norm_num
  let x199 : ℝ := x197+x198
  have hx199 : Bounds (4101898873 / 1000000000000) (9787839981 / 500000000000) x199 := by
    apply bounds_add hx197 hx198 <;> norm_num
  have hpos : 0 < x199 := lt_of_lt_of_le (by norm_num) hx199.1
  have hcert :
      0 ≤ 2 * biasE (1 - 2*m) - 2*(x77)
        - (1 - 2*entropyInverse ((1 + H (2*m - 1/2))/2)) *
            SmallMean.A (1 - 2*entropyInverse ((1 + H (2*m - 1/2))/2))
        + (1 - 2*m) *
            SmallMean.A (regularContact ((1 - 2*m)/(Real.log 2*((1 + H (2*m - 1/2))/2)))) := by
    simpa +zetaDelta only [SmallMean.A, div_one] using hpos.le
  dsimp only
  nlinarith [hcert, hLh]

theorem acceptedCertificate : DoubleCapBiasCellCertificate (1 / 4) (2563 / 10240) (fun m => (1 + H (2*m - 1/2))/2) where
  domain := by norm_num
  sound m hmLo hmHi := by
    exact cell_bias_nonneg m ⟨hmLo, hmHi⟩

theorem accepted_cell :
    ∀ m, (1 / 4) ≤ m → m ≤ (2563 / 10240) → 0 ≤ doubleCapHighResidual m := by
  intro m hmLo hmHi
  unfold doubleCapHighResidual
  apply doubleCapEndpointResidual_nonneg_of_biasCell acceptedCertificate hmLo hmHi
  exact div_pos (by linarith [H_nonneg (by linarith : 0 ≤ 2*m-1/2) (by linarith : 2*m-1/2 ≤ 1)]) two_pos

#print axioms cell_bias_nonneg
#print axioms accepted_cell

end GeneralCK.Certificates.DoubleCapMiddle.Cell0010

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0011 =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0011
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Reflection
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem cell_bias_nonneg (m : ℝ) (hm : Bounds (2563 / 10240) (1283 / 5120) m) :
    let h := (1 + H (2*m - 1/2))/2
    let x := 1-2*m
    let y := 1-2*entropyInverse h
    let c := regularContact (x/(Real.log 2*h))
    0 ≤ 2*(biasE x-Real.log 2*h)-y*SmallMean.A y+x*SmallMean.A c := by
  have hEq : biasE (2-4*m) = Real.log 2 * H (2*m-1/2) := by
    have hmstrict : 1/4 < m := by
      have hlo : (1/4 : ℝ) < (2563 / 10240) := by norm_num
      exact lt_of_lt_of_le hlo hm.1
    rw [show 2-4*m = 1-2*(2*m-1/2) by ring,
      GeneralCK.Correction.Natural.biasE_probability (by linarith [hmstrict]) (by linarith [hm.2]),
      GeneralCK.Certificates.Mixed.hn_eq_H_mul_log]
    ring
  have hLh : Real.log 2 * ((1 + H (2*m - 1/2))/2) = (Real.log 2 + biasE (2-4*m))/2 := by
    rw [hEq]
    ring
  let x0 : ℝ := (2 / 1)*m
  have hx0 : Bounds (2563 / 5120) (1283 / 2560) x0 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hm <;> norm_num
  let x1 : ℝ := -x0
  have hx1 : Bounds (-1283 / 2560) (-2563 / 5120) x1 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx0
  let x2 : ℝ := (1 / 1)+x1
  have hx2 : Bounds (1277 / 2560) (2557 / 5120) x2 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx1 <;> norm_num
  let x3 : ℝ := (1 / 1)-x0
  have hx3 : Bounds (1277 / 2560) (2557 / 5120) x3 := by
    exact hx2
  let x4 : ℝ := (4 / 1)*m
  have hx4 : Bounds (2563 / 2560) (1283 / 1280) x4 := by
    apply bounds_mul (bounds_const ((4 / 1) : ℝ)) hm <;> norm_num
  let x5 : ℝ := -x4
  have hx5 : Bounds (-1283 / 1280) (-2563 / 2560) x5 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx4
  let x6 : ℝ := (2 / 1)+x5
  have hx6 : Bounds (1277 / 1280) (2557 / 2560) x6 := by
    apply bounds_add (bounds_const ((2 / 1) : ℝ)) hx5 <;> norm_num
  let x7 : ℝ := (2 / 1)-x4
  have hx7 : Bounds (1277 / 1280) (2557 / 2560) x7 := by
    exact hx6
  let x8 : ℝ := Real.log (2 / 1)
  have hx8 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x8 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x9 : ℝ := (1 / 1)+(2557 / 5120)
  have hx9 : Bounds (7677 / 5120) (7677 / 5120) x9 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((2557 / 5120) : ℝ)) <;> norm_num
  let x10 : ℝ := (1 / 1)+(2557 / 5120)
  have hx10 : Bounds (7677 / 5120) (7677 / 5120) x10 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((2557 / 5120) : ℝ)) <;> norm_num
  let x11 : ℝ := Real.log x10
  have hx11 : Bounds (202537203 / 500000000) (405074407 / 1000000000) x11 := by
    exact bounds_log hx10 (by norm_num) (by simpa only [div_one] using reflection_log_1.1) (by simpa only [div_one] using reflection_log_1.2)
  let x12 : ℝ := x9*x11
  have hx12 : Bounds (121474852143 / 200000000000) (121474852443 / 200000000000) x12 := by
    apply bounds_mul hx9 hx11 <;> norm_num
  let x13 : ℝ := -(2557 / 5120)
  have hx13 : Bounds (-2557 / 5120) (-2557 / 5120) x13 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((2557 / 5120) : ℝ))
  let x14 : ℝ := (1 / 1)+x13
  have hx14 : Bounds (2563 / 5120) (2563 / 5120) x14 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx13 <;> norm_num
  let x15 : ℝ := (1 / 1)-(2557 / 5120)
  have hx15 : Bounds (2563 / 5120) (2563 / 5120) x15 := by
    exact hx14
  let x16 : ℝ := -(2557 / 5120)
  have hx16 : Bounds (-2557 / 5120) (-2557 / 5120) x16 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((2557 / 5120) : ℝ))
  let x17 : ℝ := (1 / 1)+x16
  have hx17 : Bounds (2563 / 5120) (2563 / 5120) x17 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx16 <;> norm_num
  let x18 : ℝ := (1 / 1)-(2557 / 5120)
  have hx18 : Bounds (2563 / 5120) (2563 / 5120) x18 := by
    exact hx17
  let x19 : ℝ := Real.log x18
  have hx19 : Bounds (-86496999 / 125000000) (-691975991 / 1000000000) x19 := by
    exact bounds_log hx18 (by norm_num) (by simpa only [div_one] using reflection_log_2.1) (by simpa only [div_one] using reflection_log_2.2)
  let x20 : ℝ := x15*x19
  have hx20 : Bounds (-346393450683 / 1000000000000) (-173196725091 / 500000000000) x20 := by
    apply bounds_mul hx15 hx19 <;> norm_num
  let x21 : ℝ := x12+x20
  have hx21 : Bounds (16311300627 / 62500000000) (260980812033 / 1000000000000) x21 := by
    apply bounds_add hx12 hx20 <;> norm_num
  let x22 : ℝ := (2 / 1)⁻¹
  have hx22 : Bounds (1 / 2) (1 / 2) x22 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x23 : ℝ := x21*x22
  have hx23 : Bounds (16311300627 / 125000000000) (130490406017 / 1000000000000) x23 := by
    apply bounds_mul hx21 hx22 <;> norm_num
  let x24 : ℝ := x21/(2 / 1)
  have hx24 : Bounds (16311300627 / 125000000000) (130490406017 / 1000000000000) x24 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx23
  let x25 : ℝ := -x24
  have hx25 : Bounds (-130490406017 / 1000000000000) (-16311300627 / 125000000000) x25 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx24
  let x26 : ℝ := x8+x25
  have hx26 : Bounds (562656773983 / 1000000000000) (35166048499 / 62500000000) x26 := by
    apply bounds_add hx8 hx25 <;> norm_num
  let x27 : ℝ := x8-x24
  have hx27 : Bounds (562656773983 / 1000000000000) (35166048499 / 62500000000) x27 := by
    exact hx26
  let x28 : ℝ := biasE (2557 / 5120)
  have hx28 : Bounds (562656773983 / 1000000000000) (35166048499 / 62500000000) x28 := by
    simpa +zetaDelta only [biasE, div_one] using hx27
  let x29 : ℝ := Real.log (2 / 1)
  have hx29 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x29 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x30 : ℝ := (1 / 1)+(1277 / 2560)
  have hx30 : Bounds (3837 / 2560) (3837 / 2560) x30 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1277 / 2560) : ℝ)) <;> norm_num
  let x31 : ℝ := (1 / 1)+(1277 / 2560)
  have hx31 : Bounds (3837 / 2560) (3837 / 2560) x31 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1277 / 2560) : ℝ)) <;> norm_num
  let x32 : ℝ := Real.log x31
  have hx32 : Bounds (12646361 / 31250000) (404683553 / 1000000000) x32 := by
    exact bounds_log hx31 (by norm_num) (by simpa only [div_one] using reflection_log_3.1) (by simpa only [div_one] using reflection_log_3.2)
  let x33 : ℝ := x30*x32
  have hx33 : Bounds (303275544731 / 500000000000) (303275545481 / 500000000000) x33 := by
    apply bounds_mul hx30 hx32 <;> norm_num
  let x34 : ℝ := -(1277 / 2560)
  have hx34 : Bounds (-1277 / 2560) (-1277 / 2560) x34 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1277 / 2560) : ℝ))
  let x35 : ℝ := (1 / 1)+x34
  have hx35 : Bounds (1283 / 2560) (1283 / 2560) x35 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx34 <;> norm_num
  let x36 : ℝ := (1 / 1)-(1277 / 2560)
  have hx36 : Bounds (1283 / 2560) (1283 / 2560) x36 := by
    exact hx35
  let x37 : ℝ := -(1277 / 2560)
  have hx37 : Bounds (-1277 / 2560) (-1277 / 2560) x37 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1277 / 2560) : ℝ))
  let x38 : ℝ := (1 / 1)+x37
  have hx38 : Bounds (1283 / 2560) (1283 / 2560) x38 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx37 <;> norm_num
  let x39 : ℝ := (1 / 1)-(1277 / 2560)
  have hx39 : Bounds (1283 / 2560) (1283 / 2560) x39 := by
    exact hx38
  let x40 : ℝ := Real.log x39
  have hx40 : Bounds (-690806173 / 1000000000) (-172701543 / 250000000) x40 := by
    exact bounds_log hx39 (by norm_num) (by simpa only [div_one] using reflection_log_4.1) (by simpa only [div_one] using reflection_log_4.2)
  let x41 : ℝ := x36*x40
  have hx41 : Bounds (-43276578123 / 125000000000) (-173106312241 / 500000000000) x41 := by
    apply bounds_mul hx36 hx40 <;> norm_num
  let x42 : ℝ := x33+x41
  have hx42 : Bounds (130169232239 / 500000000000) (3254230831 / 12500000000) x42 := by
    apply bounds_add hx33 hx41 <;> norm_num
  let x43 : ℝ := (2 / 1)⁻¹
  have hx43 : Bounds (1 / 2) (1 / 2) x43 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x44 : ℝ := x42*x43
  have hx44 : Bounds (130169232239 / 1000000000000) (3254230831 / 25000000000) x44 := by
    apply bounds_mul hx42 hx43 <;> norm_num
  let x45 : ℝ := x42/(2 / 1)
  have hx45 : Bounds (130169232239 / 1000000000000) (3254230831 / 25000000000) x45 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx44
  let x46 : ℝ := -x45
  have hx46 : Bounds (-3254230831 / 25000000000) (-130169232239 / 1000000000000) x46 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx45
  let x47 : ℝ := x29+x46
  have hx47 : Bounds (14074448669 / 25000000000) (562977948761 / 1000000000000) x47 := by
    apply bounds_add hx29 hx46 <;> norm_num
  let x48 : ℝ := x29-x45
  have hx48 : Bounds (14074448669 / 25000000000) (562977948761 / 1000000000000) x48 := by
    exact hx47
  let x49 : ℝ := biasE (1277 / 2560)
  have hx49 : Bounds (14074448669 / 25000000000) (562977948761 / 1000000000000) x49 := by
    simpa +zetaDelta only [biasE, div_one] using hx48
  let x50 : ℝ := biasE x3
  have hx50 : Bounds (562656773983 / 1000000000000) (562977948761 / 1000000000000) x50 := by
    exact bounds_biasE hx3 (by norm_num) (by norm_num) hx28.1 hx49.2
  let x51 : ℝ := Real.log (2 / 1)
  have hx51 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x51 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x52 : ℝ := (1 / 1)+(2557 / 2560)
  have hx52 : Bounds (5117 / 2560) (5117 / 2560) x52 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((2557 / 2560) : ℝ)) <;> norm_num
  let x53 : ℝ := (1 / 1)+(2557 / 2560)
  have hx53 : Bounds (5117 / 2560) (5117 / 2560) x53 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((2557 / 2560) : ℝ)) <;> norm_num
  let x54 : ℝ := Real.log x53
  have hx54 : Bounds (692561071 / 1000000000) (43285067 / 62500000) x54 := by
    exact bounds_log hx53 (by norm_num) (by simpa only [div_one] using reflection_log_5.1) (by simpa only [div_one] using reflection_log_5.2)
  let x55 : ℝ := x52*x54
  have hx55 : Bounds (692155273497 / 500000000000) (692155274497 / 500000000000) x55 := by
    apply bounds_mul hx52 hx54 <;> norm_num
  let x56 : ℝ := -(2557 / 2560)
  have hx56 : Bounds (-2557 / 2560) (-2557 / 2560) x56 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((2557 / 2560) : ℝ))
  let x57 : ℝ := (1 / 1)+x56
  have hx57 : Bounds (3 / 2560) (3 / 2560) x57 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx56 <;> norm_num
  let x58 : ℝ := (1 / 1)-(2557 / 2560)
  have hx58 : Bounds (3 / 2560) (3 / 2560) x58 := by
    exact hx57
  let x59 : ℝ := -(2557 / 2560)
  have hx59 : Bounds (-2557 / 2560) (-2557 / 2560) x59 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((2557 / 2560) : ℝ))
  let x60 : ℝ := (1 / 1)+x59
  have hx60 : Bounds (3 / 2560) (3 / 2560) x60 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx59 <;> norm_num
  let x61 : ℝ := (1 / 1)-(2557 / 2560)
  have hx61 : Bounds (3 / 2560) (3 / 2560) x61 := by
    exact hx60
  let x62 : ℝ := Real.log x61
  have hx62 : Bounds (-6749150253 / 1000000000) (-6749150243 / 1000000000) x62 := by
    exact bounds_log hx61 (by norm_num) (by simpa only [div_one] using reflection_log_6.1) (by simpa only [div_one] using reflection_log_6.2)
  let x63 : ℝ := x58*x62
  have hx63 : Bounds (-7909160453 / 1000000000000) (-7909160441 / 1000000000000) x63 := by
    apply bounds_mul hx58 hx62 <;> norm_num
  let x64 : ℝ := x55+x63
  have hx64 : Bounds (1376401386541 / 1000000000000) (1376401388553 / 1000000000000) x64 := by
    apply bounds_add hx55 hx63 <;> norm_num
  let x65 : ℝ := (2 / 1)⁻¹
  have hx65 : Bounds (1 / 2) (1 / 2) x65 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x66 : ℝ := x64*x65
  have hx66 : Bounds (68820069327 / 100000000000) (688200694277 / 1000000000000) x66 := by
    apply bounds_mul hx64 hx65 <;> norm_num
  let x67 : ℝ := x64/(2 / 1)
  have hx67 : Bounds (68820069327 / 100000000000) (688200694277 / 1000000000000) x67 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx66
  let x68 : ℝ := -x67
  have hx68 : Bounds (-688200694277 / 1000000000000) (-68820069327 / 100000000000) x68 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx67
  let x69 : ℝ := x51+x68
  have hx69 : Bounds (4946485723 / 1000000000000) (494648773 / 100000000000) x69 := by
    apply bounds_add hx51 hx68 <;> norm_num
  let x70 : ℝ := x51-x67
  have hx70 : Bounds (4946485723 / 1000000000000) (494648773 / 100000000000) x70 := by
    exact hx69
  let x71 : ℝ := biasE (2557 / 2560)
  have hx71 : Bounds (4946485723 / 1000000000000) (494648773 / 100000000000) x71 := by
    simpa +zetaDelta only [biasE, div_one] using hx70
  let x72 : ℝ := Real.log (2 / 1)
  have hx72 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x72 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x73 : ℝ := (1 / 1)+(1277 / 1280)
  have hx73 : Bounds (2557 / 1280) (2557 / 1280) x73 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1277 / 1280) : ℝ)) <;> norm_num
  let x74 : ℝ := (1 / 1)+(1277 / 1280)
  have hx74 : Bounds (2557 / 1280) (2557 / 1280) x74 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1277 / 1280) : ℝ)) <;> norm_num
  let x75 : ℝ := Real.log x74
  have hx75 : Bounds (345987309 / 500000000) (691974619 / 1000000000) x75 := by
    exact bounds_log hx74 (by norm_num) (by simpa only [div_one] using reflection_log_7.1) (by simpa only [div_one] using reflection_log_7.2)
  let x76 : ℝ := x73*x75
  have hx76 : Bounds (1382327420489 / 1000000000000) (1382327422487 / 1000000000000) x76 := by
    apply bounds_mul hx73 hx75 <;> norm_num
  let x77 : ℝ := -(1277 / 1280)
  have hx77 : Bounds (-1277 / 1280) (-1277 / 1280) x77 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1277 / 1280) : ℝ))
  let x78 : ℝ := (1 / 1)+x77
  have hx78 : Bounds (3 / 1280) (3 / 1280) x78 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx77 <;> norm_num
  let x79 : ℝ := (1 / 1)-(1277 / 1280)
  have hx79 : Bounds (3 / 1280) (3 / 1280) x79 := by
    exact hx78
  let x80 : ℝ := -(1277 / 1280)
  have hx80 : Bounds (-1277 / 1280) (-1277 / 1280) x80 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1277 / 1280) : ℝ))
  let x81 : ℝ := (1 / 1)+x80
  have hx81 : Bounds (3 / 1280) (3 / 1280) x81 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx80 <;> norm_num
  let x82 : ℝ := (1 / 1)-(1277 / 1280)
  have hx82 : Bounds (3 / 1280) (3 / 1280) x82 := by
    exact hx81
  let x83 : ℝ := Real.log x82
  have hx83 : Bounds (-11828131 / 1953125) (-6056003063 / 1000000000) x83 := by
    exact bounds_log hx82 (by norm_num) (by simpa only [div_one] using reflection_log_8.1) (by simpa only [div_one] using reflection_log_8.2)
  let x84 : ℝ := x79*x83
  have hx84 : Bounds (-35484393 / 2500000000) (-7096878589 / 500000000000) x84 := by
    apply bounds_mul hx79 hx83 <;> norm_num
  let x85 : ℝ := x76+x84
  have hx85 : Bounds (1368133663289 / 1000000000000) (1368133665309 / 1000000000000) x85 := by
    apply bounds_add hx76 hx84 <;> norm_num
  let x86 : ℝ := (2 / 1)⁻¹
  have hx86 : Bounds (1 / 2) (1 / 2) x86 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x87 : ℝ := x85*x86
  have hx87 : Bounds (171016707911 / 250000000000) (136813366531 / 200000000000) x87 := by
    apply bounds_mul hx85 hx86 <;> norm_num
  let x88 : ℝ := x85/(2 / 1)
  have hx88 : Bounds (171016707911 / 250000000000) (136813366531 / 200000000000) x88 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx87
  let x89 : ℝ := -x88
  have hx89 : Bounds (-136813366531 / 200000000000) (-171016707911 / 250000000000) x89 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx88
  let x90 : ℝ := x72+x89
  have hx90 : Bounds (1816069469 / 200000000000) (2270087339 / 250000000000) x90 := by
    apply bounds_add hx72 hx89 <;> norm_num
  let x91 : ℝ := x72-x88
  have hx91 : Bounds (1816069469 / 200000000000) (2270087339 / 250000000000) x91 := by
    exact hx90
  let x92 : ℝ := biasE (1277 / 1280)
  have hx92 : Bounds (1816069469 / 200000000000) (2270087339 / 250000000000) x92 := by
    simpa +zetaDelta only [biasE, div_one] using hx91
  let x93 : ℝ := biasE x7
  have hx93 : Bounds (4946485723 / 1000000000000) (2270087339 / 250000000000) x93 := by
    exact bounds_biasE hx7 (by norm_num) (by norm_num) hx71.1 hx92.2
  let x94 : ℝ := Real.log (2 / 1)
  have hx94 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x94 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x95 : ℝ := x94+x93
  have hx95 : Bounds (698093665723 / 1000000000000) (175556882589 / 250000000000) x95 := by
    apply bounds_add hx94 hx93 <;> norm_num
  let x96 : ℝ := (2 / 1)⁻¹
  have hx96 : Bounds (1 / 2) (1 / 2) x96 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x97 : ℝ := x95*x96
  have hx97 : Bounds (349046832861 / 1000000000000) (175556882589 / 500000000000) x97 := by
    apply bounds_mul hx95 hx96 <;> norm_num
  let x98 : ℝ := x95/(2 / 1)
  have hx98 : Bounds (349046832861 / 1000000000000) (175556882589 / 500000000000) x98 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx97
  let x99 : ℝ := Real.log (2 / 1)
  have hx99 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x99 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x100 : ℝ := (1 / 1)+(775577 / 1000000)
  have hx100 : Bounds (1775577 / 1000000) (1775577 / 1000000) x100 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((775577 / 1000000) : ℝ)) <;> norm_num
  let x101 : ℝ := (1 / 1)+(775577 / 1000000)
  have hx101 : Bounds (1775577 / 1000000) (1775577 / 1000000) x101 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((775577 / 1000000) : ℝ)) <;> norm_num
  let x102 : ℝ := Real.log x101
  have hx102 : Bounds (897071 / 1562500) (574125441 / 1000000000) x102 := by
    exact bounds_log hx101 (by norm_num) (by simpa only [div_one] using reflection_log_9.1) (by simpa only [div_one] using reflection_log_9.2)
  let x103 : ℝ := x100*x102
  have hx103 : Bounds (509701963189 / 500000000000) (203880785631 / 200000000000) x103 := by
    apply bounds_mul hx100 hx102 <;> norm_num
  let x104 : ℝ := -(775577 / 1000000)
  have hx104 : Bounds (-775577 / 1000000) (-775577 / 1000000) x104 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((775577 / 1000000) : ℝ))
  let x105 : ℝ := (1 / 1)+x104
  have hx105 : Bounds (224423 / 1000000) (224423 / 1000000) x105 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx104 <;> norm_num
  let x106 : ℝ := (1 / 1)-(775577 / 1000000)
  have hx106 : Bounds (224423 / 1000000) (224423 / 1000000) x106 := by
    exact hx105
  let x107 : ℝ := -(775577 / 1000000)
  have hx107 : Bounds (-775577 / 1000000) (-775577 / 1000000) x107 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((775577 / 1000000) : ℝ))
  let x108 : ℝ := (1 / 1)+x107
  have hx108 : Bounds (224423 / 1000000) (224423 / 1000000) x108 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx107 <;> norm_num
  let x109 : ℝ := (1 / 1)-(775577 / 1000000)
  have hx109 : Bounds (224423 / 1000000) (224423 / 1000000) x109 := by
    exact hx108
  let x110 : ℝ := Real.log x109
  have hx110 : Bounds (-186777827 / 125000000) (-1494222613 / 1000000000) x110 := by
    exact bounds_log hx109 (by norm_num) (by simpa only [div_one] using reflection_log_10.1) (by simpa only [div_one] using reflection_log_10.2)
  let x111 : ℝ := x106*x110
  have hx111 : Bounds (-335337922151 / 1000000000000) (-335337921477 / 1000000000000) x111 := by
    apply bounds_mul hx106 hx110 <;> norm_num
  let x112 : ℝ := x103+x111
  have hx112 : Bounds (684066004227 / 1000000000000) (342033003339 / 500000000000) x112 := by
    apply bounds_add hx103 hx111 <;> norm_num
  let x113 : ℝ := (2 / 1)⁻¹
  have hx113 : Bounds (1 / 2) (1 / 2) x113 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x114 : ℝ := x112*x113
  have hx114 : Bounds (342033002113 / 1000000000000) (342033003339 / 1000000000000) x114 := by
    apply bounds_mul hx112 hx113 <;> norm_num
  let x115 : ℝ := x112/(2 / 1)
  have hx115 : Bounds (342033002113 / 1000000000000) (342033003339 / 1000000000000) x115 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx114
  let x116 : ℝ := -x115
  have hx116 : Bounds (-342033003339 / 1000000000000) (-342033002113 / 1000000000000) x116 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx115
  let x117 : ℝ := x99+x116
  have hx117 : Bounds (351114176661 / 1000000000000) (351114178887 / 1000000000000) x117 := by
    apply bounds_add hx99 hx116 <;> norm_num
  let x118 : ℝ := x99-x115
  have hx118 : Bounds (351114176661 / 1000000000000) (351114178887 / 1000000000000) x118 := by
    exact hx117
  let x119 : ℝ := biasE (775577 / 1000000)
  have hx119 : Bounds (351114176661 / 1000000000000) (351114178887 / 1000000000000) x119 := by
    simpa +zetaDelta only [biasE, div_one] using hx118
  let x120 : ℝ := Real.log (2 / 1)
  have hx120 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x120 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x121 : ℝ := (1 / 1)+(194393 / 250000)
  have hx121 : Bounds (444393 / 250000) (444393 / 250000) x121 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((194393 / 250000) : ℝ)) <;> norm_num
  let x122 : ℝ := (1 / 1)+(194393 / 250000)
  have hx122 : Bounds (444393 / 250000) (444393 / 250000) x122 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((194393 / 250000) : ℝ)) <;> norm_num
  let x123 : ℝ := Real.log x122
  have hx123 : Bounds (143812097 / 250000000) (575248389 / 1000000000) x123 := by
    exact bounds_log hx122 (by norm_num) (by simpa only [div_one] using reflection_log_11.1) (by simpa only [div_one] using reflection_log_11.2)
  let x124 : ℝ := x121*x123
  have hx124 : Bounds (1022545427553 / 1000000000000) (255636357333 / 250000000000) x124 := by
    apply bounds_mul hx121 hx123 <;> norm_num
  let x125 : ℝ := -(194393 / 250000)
  have hx125 : Bounds (-194393 / 250000) (-194393 / 250000) x125 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((194393 / 250000) : ℝ))
  let x126 : ℝ := (1 / 1)+x125
  have hx126 : Bounds (55607 / 250000) (55607 / 250000) x126 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx125 <;> norm_num
  let x127 : ℝ := (1 / 1)-(194393 / 250000)
  have hx127 : Bounds (55607 / 250000) (55607 / 250000) x127 := by
    exact hx126
  let x128 : ℝ := -(194393 / 250000)
  have hx128 : Bounds (-194393 / 250000) (-194393 / 250000) x128 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((194393 / 250000) : ℝ))
  let x129 : ℝ := (1 / 1)+x128
  have hx129 : Bounds (55607 / 250000) (55607 / 250000) x129 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx128 <;> norm_num
  let x130 : ℝ := (1 / 1)-(194393 / 250000)
  have hx130 : Bounds (55607 / 250000) (55607 / 250000) x130 := by
    exact hx129
  let x131 : ℝ := Real.log x130
  have hx131 : Bounds (-1503151827 / 1000000000) (-93946989 / 62500000) x131 := by
    exact bounds_log hx130 (by norm_num) (by simpa only [div_one] using reflection_log_12.1) (by simpa only [div_one] using reflection_log_12.2)
  let x132 : ℝ := x127*x131
  have hx132 : Bounds (-20896440911 / 62500000000) (-83585763477 / 250000000000) x132 := by
    apply bounds_mul hx127 hx131 <;> norm_num
  let x133 : ℝ := x124+x132
  have hx133 : Bounds (688202372977 / 1000000000000) (2688290529 / 3906250000) x133 := by
    apply bounds_add hx124 hx132 <;> norm_num
  let x134 : ℝ := (2 / 1)⁻¹
  have hx134 : Bounds (1 / 2) (1 / 2) x134 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x135 : ℝ := x133*x134
  have hx135 : Bounds (43012648311 / 125000000000) (2688290529 / 7812500000) x135 := by
    apply bounds_mul hx133 hx134 <;> norm_num
  let x136 : ℝ := x133/(2 / 1)
  have hx136 : Bounds (43012648311 / 125000000000) (2688290529 / 7812500000) x136 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx135
  let x137 : ℝ := -x136
  have hx137 : Bounds (-2688290529 / 7812500000) (-43012648311 / 125000000000) x137 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx136
  let x138 : ℝ := x120+x137
  have hx138 : Bounds (10907687259 / 31250000000) (21815374657 / 62500000000) x138 := by
    apply bounds_add hx120 hx137 <;> norm_num
  let x139 : ℝ := x120-x136
  have hx139 : Bounds (10907687259 / 31250000000) (21815374657 / 62500000000) x139 := by
    exact hx138
  let x140 : ℝ := biasE (194393 / 250000)
  have hx140 : Bounds (10907687259 / 31250000000) (21815374657 / 62500000000) x140 := by
    simpa +zetaDelta only [biasE, div_one] using hx139
  let y : ℝ := 1 - 2 * entropyInverse ((1 + H (2*m - 1/2))/2)
  have hLh' : Real.log 2 * ((1 + H (2*m - 1/2))/2) = x98 := by
    simpa +zetaDelta only [div_one] using hLh
  have hy : Bounds (775577 / 1000000) (194393 / 250000) y := by
    apply entropyInverseBias_bracket
    · exact div_nonneg (add_nonneg zero_le_one
        (H_nonneg (by linarith [hm.1]) (by linarith [hm.2]))) two_pos.le
    · linarith [H_le_one (2*m-1/2)]
    · norm_num
    · norm_num
    · norm_num
    · have h1 : biasE (194393 / 250000) ≤ (21815374657 / 62500000000) := hx140.2
      have h2 : (349046832861 / 1000000000000) ≤ x98 := hx98.1
      linarith [hLh']
    · have h1 : x98 ≤ (175556882589 / 500000000000) := hx98.2
      have h2 : (351114176661 / 1000000000000) ≤ biasE (775577 / 1000000) := hx119.1
      linarith [hLh']
  let x141 : ℝ := x3⁻¹
  have hx141 : Bounds (500586624951 / 250000000000) (1002349256069 / 500000000000) x141 := by
    apply bounds_inv hx3 <;> norm_num
  let x142 : ℝ := x98*x141
  have hx142 : Bounds (349456352023 / 500000000000) (175969310661 / 250000000000) x142 := by
    apply bounds_mul hx98 hx141 <;> norm_num
  let x143 : ℝ := x98/x3
  have hx143 : Bounds (349456352023 / 500000000000) (175969310661 / 250000000000) x143 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx142
  let x144 : ℝ := Real.log (2 / 1)
  have hx144 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x144 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x145 : ℝ := (1 / 1)+(130837 / 200000)
  have hx145 : Bounds (330837 / 200000) (330837 / 200000) x145 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((130837 / 200000) : ℝ)) <;> norm_num
  let x146 : ℝ := (1 / 1)+(130837 / 200000)
  have hx146 : Bounds (330837 / 200000) (330837 / 200000) x146 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((130837 / 200000) : ℝ)) <;> norm_num
  let x147 : ℝ := Real.log x146
  have hx147 : Bounds (12582711 / 25000000) (503308441 / 1000000000) x147 := by
    exact bounds_log hx146 (by norm_num) (by simpa only [div_one] using reflection_log_13.1) (by simpa only [div_one] using reflection_log_13.2)
  let x148 : ℝ := x145*x147
  have hx148 : Bounds (832565271821 / 1000000000000) (208141318369 / 250000000000) x148 := by
    apply bounds_mul hx145 hx147 <;> norm_num
  let x149 : ℝ := -(130837 / 200000)
  have hx149 : Bounds (-130837 / 200000) (-130837 / 200000) x149 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((130837 / 200000) : ℝ))
  let x150 : ℝ := (1 / 1)+x149
  have hx150 : Bounds (69163 / 200000) (69163 / 200000) x150 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx149 <;> norm_num
  let x151 : ℝ := (1 / 1)-(130837 / 200000)
  have hx151 : Bounds (69163 / 200000) (69163 / 200000) x151 := by
    exact hx150
  let x152 : ℝ := -(130837 / 200000)
  have hx152 : Bounds (-130837 / 200000) (-130837 / 200000) x152 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((130837 / 200000) : ℝ))
  let x153 : ℝ := (1 / 1)+x152
  have hx153 : Bounds (69163 / 200000) (69163 / 200000) x153 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx152 <;> norm_num
  let x154 : ℝ := (1 / 1)-(130837 / 200000)
  have hx154 : Bounds (69163 / 200000) (69163 / 200000) x154 := by
    exact hx153
  let x155 : ℝ := Real.log x154
  have hx155 : Bounds (-106185133 / 100000000) (-16591427 / 15625000) x155 := by
    exact bounds_log hx154 (by norm_num) (by simpa only [div_one] using reflection_log_14.1) (by simpa only [div_one] using reflection_log_14.2)
  let x156 : ℝ := x151*x155
  have hx156 : Bounds (-91801029421 / 250000000000) (-717195541 / 1953125000) x156 := by
    apply bounds_mul hx151 hx155 <;> norm_num
  let x157 : ℝ := x148+x156
  have hx157 : Bounds (465361154137 / 1000000000000) (116340289121 / 250000000000) x157 := by
    apply bounds_add hx148 hx156 <;> norm_num
  let x158 : ℝ := (2 / 1)⁻¹
  have hx158 : Bounds (1 / 2) (1 / 2) x158 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x159 : ℝ := x157*x158
  have hx159 : Bounds (58170144267 / 250000000000) (116340289121 / 500000000000) x159 := by
    apply bounds_mul hx157 hx158 <;> norm_num
  let x160 : ℝ := x157/(2 / 1)
  have hx160 : Bounds (58170144267 / 250000000000) (116340289121 / 500000000000) x160 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx159
  let x161 : ℝ := -x160
  have hx161 : Bounds (-116340289121 / 500000000000) (-58170144267 / 250000000000) x161 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx160
  let x162 : ℝ := x144+x161
  have hx162 : Bounds (230233300879 / 500000000000) (115116650983 / 250000000000) x162 := by
    apply bounds_add hx144 hx161 <;> norm_num
  let x163 : ℝ := x144-x160
  have hx163 : Bounds (230233300879 / 500000000000) (115116650983 / 250000000000) x163 := by
    exact hx162
  let x164 : ℝ := biasE (130837 / 200000)
  have hx164 : Bounds (230233300879 / 500000000000) (115116650983 / 250000000000) x164 := by
    simpa +zetaDelta only [biasE, div_one] using hx163
  let x165 : ℝ := Real.log (2 / 1)
  have hx165 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x165 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x166 : ℝ := (1 / 1)+(5251 / 8000)
  have hx166 : Bounds (13251 / 8000) (13251 / 8000) x166 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((5251 / 8000) : ℝ)) <;> norm_num
  let x167 : ℝ := (1 / 1)+(5251 / 8000)
  have hx167 : Bounds (13251 / 8000) (13251 / 8000) x167 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((5251 / 8000) : ℝ)) <;> norm_num
  let x168 : ℝ := Real.log x167
  have hx168 : Bounds (504631479 / 1000000000) (12615787 / 25000000) x168 := by
    exact bounds_log hx167 (by norm_num) (by simpa only [div_one] using reflection_log_15.1) (by simpa only [div_one] using reflection_log_15.2)
  let x169 : ℝ := x166*x168
  have hx169 : Bounds (208964741507 / 250000000000) (167171793537 / 200000000000) x169 := by
    apply bounds_mul hx166 hx168 <;> norm_num
  let x170 : ℝ := -(5251 / 8000)
  have hx170 : Bounds (-5251 / 8000) (-5251 / 8000) x170 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((5251 / 8000) : ℝ))
  let x171 : ℝ := (1 / 1)+x170
  have hx171 : Bounds (2749 / 8000) (2749 / 8000) x171 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx170 <;> norm_num
  let x172 : ℝ := (1 / 1)-(5251 / 8000)
  have hx172 : Bounds (2749 / 8000) (2749 / 8000) x172 := by
    exact hx171
  let x173 : ℝ := -(5251 / 8000)
  have hx173 : Bounds (-5251 / 8000) (-5251 / 8000) x173 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((5251 / 8000) : ℝ))
  let x174 : ℝ := (1 / 1)+x173
  have hx174 : Bounds (2749 / 8000) (2749 / 8000) x174 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx173 <;> norm_num
  let x175 : ℝ := (1 / 1)-(5251 / 8000)
  have hx175 : Bounds (2749 / 8000) (2749 / 8000) x175 := by
    exact hx174
  let x176 : ℝ := Real.log x175
  have hx176 : Bounds (-1068204333 / 1000000000) (-1068204331 / 1000000000) x176 := by
    exact bounds_log hx175 (by norm_num) (by simpa only [div_one] using reflection_log_16.1) (by simpa only [div_one] using reflection_log_16.2)
  let x177 : ℝ := x172*x176
  have hx177 : Bounds (-45882714241 / 125000000000) (-367061713239 / 1000000000000) x177 := by
    apply bounds_mul hx172 hx176 <;> norm_num
  let x178 : ℝ := x169+x177
  have hx178 : Bounds (4687972521 / 10000000000) (234398627223 / 500000000000) x178 := by
    apply bounds_add hx169 hx177 <;> norm_num
  let x179 : ℝ := (2 / 1)⁻¹
  have hx179 : Bounds (1 / 2) (1 / 2) x179 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x180 : ℝ := x178*x179
  have hx180 : Bounds (4687972521 / 20000000000) (234398627223 / 1000000000000) x180 := by
    apply bounds_mul hx178 hx179 <;> norm_num
  let x181 : ℝ := x178/(2 / 1)
  have hx181 : Bounds (4687972521 / 20000000000) (234398627223 / 1000000000000) x181 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx180
  let x182 : ℝ := -x181
  have hx182 : Bounds (-234398627223 / 1000000000000) (-4687972521 / 20000000000) x182 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx181
  let x183 : ℝ := x165+x182
  have hx183 : Bounds (458748552777 / 1000000000000) (9174971099 / 20000000000) x183 := by
    apply bounds_add hx165 hx182 <;> norm_num
  let x184 : ℝ := x165-x181
  have hx184 : Bounds (458748552777 / 1000000000000) (9174971099 / 20000000000) x184 := by
    exact hx183
  let x185 : ℝ := biasE (5251 / 8000)
  have hx185 : Bounds (458748552777 / 1000000000000) (9174971099 / 20000000000) x185 := by
    simpa +zetaDelta only [biasE, div_one] using hx184
  let x186 : ℝ := x143*(130837 / 200000)
  have hx186 : Bounds (7144034489 / 15625000000) (23023296699 / 50000000000) x186 := by
    apply bounds_mul hx143 (bounds_const ((130837 / 200000) : ℝ)) <;> norm_num
  let x187 : ℝ := x143*(5251 / 8000)
  have hx187 : Bounds (229374413059 / 500000000000) (462007425141 / 1000000000000) x187 := by
    apply bounds_mul hx143 (bounds_const ((5251 / 8000) : ℝ)) <;> norm_num
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
  have hc : Bounds (130837 / 200000) (5251 / 8000) c := by
    apply contact_bracket hc0 hcMem.2.le (by norm_num) (by norm_num) (by norm_num)
      (show 0 < x143 by linarith [hx143.1]) hcEq
    · have h1 : x143 * (130837 / 200000) ≤ (23023296699 / 50000000000) := hx186.2
      have h2 : (230233300879 / 500000000000) ≤ biasE (130837 / 200000) := hx164.1
      linarith
    · have h1 : biasE (5251 / 8000) ≤ (9174971099 / 20000000000) := hx185.2
      have h2 : (229374413059 / 500000000000) ≤ x143 * (5251 / 8000) := hx187.1
      linarith
  let x188 : ℝ := (1 / 1)+y
  have hx188 : Bounds (1775577 / 1000000) (444393 / 250000) x188 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hy <;> norm_num
  let x189 : ℝ := -y
  have hx189 : Bounds (-194393 / 250000) (-775577 / 1000000) x189 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hy
  let x190 : ℝ := (1 / 1)+x189
  have hx190 : Bounds (55607 / 250000) (224423 / 1000000) x190 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx189 <;> norm_num
  let x191 : ℝ := (1 / 1)-y
  have hx191 : Bounds (55607 / 250000) (224423 / 1000000) x191 := by
    exact hx190
  let x192 : ℝ := x191⁻¹
  have hx192 : Bounds (445587127879 / 100000000000) (4495836855073 / 1000000000000) x192 := by
    apply bounds_inv hx191 <;> norm_num
  let x193 : ℝ := x188*x192
  have hx193 : Bounds (395587127879 / 50000000000) (3995836855073 / 500000000000) x193 := by
    apply bounds_mul hx188 hx192 <;> norm_num
  let x194 : ℝ := x188/x191
  have hx194 : Bounds (395587127879 / 50000000000) (3995836855073 / 500000000000) x194 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx193
  let x195 : ℝ := Real.log x194
  have hx195 : Bounds (1034174027 / 500000000) (415680043 / 200000000) x195 := by
    exact bounds_log hx194 (by norm_num) (by simpa only [div_one] using reflection_log_17.1) (by simpa only [div_one] using reflection_log_18.2)
  let x196 : ℝ := (2 / 1)⁻¹
  have hx196 : Bounds (1 / 2) (1 / 2) x196 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x197 : ℝ := x195*x196
  have hx197 : Bounds (1034174027 / 1000000000) (415680043 / 400000000) x197 := by
    apply bounds_mul hx195 hx196 <;> norm_num
  let x198 : ℝ := x195/(2 / 1)
  have hx198 : Bounds (1034174027 / 1000000000) (415680043 / 400000000) x198 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx197
  let x199 : ℝ := (1 / 1)+c
  have hx199 : Bounds (330837 / 200000) (13251 / 8000) x199 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hc <;> norm_num
  let x200 : ℝ := -c
  have hx200 : Bounds (-5251 / 8000) (-130837 / 200000) x200 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hc
  let x201 : ℝ := (1 / 1)+x200
  have hx201 : Bounds (2749 / 8000) (69163 / 200000) x201 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx200 <;> norm_num
  let x202 : ℝ := (1 / 1)-c
  have hx202 : Bounds (2749 / 8000) (69163 / 200000) x202 := by
    exact hx201
  let x203 : ℝ := x202⁻¹
  have hx203 : Bounds (722929890259 / 250000000000) (363768643143 / 125000000000) x203 := by
    apply bounds_inv hx202 <;> norm_num
  let x204 : ℝ := x199*x203
  have hx204 : Bounds (597929890259 / 125000000000) (301268643143 / 62500000000) x204 := by
    apply bounds_mul hx199 hx203 <;> norm_num
  let x205 : ℝ := x199/x202
  have hx205 : Bounds (597929890259 / 125000000000) (301268643143 / 62500000000) x205 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx204
  let x206 : ℝ := Real.log x205
  have hx206 : Bounds (195644971 / 125000000) (1572835813 / 1000000000) x206 := by
    exact bounds_log hx205 (by norm_num) (by simpa only [div_one] using reflection_log_19.1) (by simpa only [div_one] using reflection_log_20.2)
  let x207 : ℝ := (2 / 1)⁻¹
  have hx207 : Bounds (1 / 2) (1 / 2) x207 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x208 : ℝ := x206*x207
  have hx208 : Bounds (195644971 / 250000000) (1572835813 / 2000000000) x208 := by
    apply bounds_mul hx206 hx207 <;> norm_num
  let x209 : ℝ := x206/(2 / 1)
  have hx209 : Bounds (195644971 / 250000000) (1572835813 / 2000000000) x209 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx208
  let x210 : ℝ := (2 / 1)*x50
  have hx210 : Bounds (562656773983 / 500000000000) (562977948761 / 500000000000) x210 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx50 <;> norm_num
  let x211 : ℝ := (2 / 1)*x98
  have hx211 : Bounds (349046832861 / 500000000000) (175556882589 / 250000000000) x211 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx98 <;> norm_num
  let x212 : ℝ := -x211
  have hx212 : Bounds (-175556882589 / 250000000000) (-349046832861 / 500000000000) x212 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx211
  let x213 : ℝ := x210+x212
  have hx213 : Bounds (42308601761 / 100000000000) (2139311159 / 5000000000) x213 := by
    apply bounds_add hx210 hx212 <;> norm_num
  let x214 : ℝ := x210-x211
  have hx214 : Bounds (42308601761 / 100000000000) (2139311159 / 5000000000) x214 := by
    exact hx213
  let x215 : ℝ := y*x198
  have hx215 : Bounds (401040794669 / 500000000000) (808052905989 / 1000000000000) x215 := by
    apply bounds_mul hy hx198 <;> norm_num
  let x216 : ℝ := -x215
  have hx216 : Bounds (-808052905989 / 1000000000000) (-401040794669 / 500000000000) x216 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx215
  let x217 : ℝ := x214+x216
  have hx217 : Bounds (-384966888379 / 1000000000000) (-187109678769 / 500000000000) x217 := by
    apply bounds_add hx214 hx216 <;> norm_num
  let x218 : ℝ := x214-x215
  have hx218 : Bounds (-384966888379 / 1000000000000) (-187109678769 / 500000000000) x218 := by
    exact hx217
  let x219 : ℝ := x3*x209
  have hx219 : Bounds (195186428099 / 500000000000) (98187040377 / 250000000000) x219 := by
    apply bounds_mul hx3 hx209 <;> norm_num
  let x220 : ℝ := x218+x219
  have hx220 : Bounds (5405967819 / 1000000000000) (1852880397 / 100000000000) x220 := by
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

theorem acceptedCertificate : DoubleCapBiasCellCertificate (2563 / 10240) (1283 / 5120) (fun m => (1 + H (2*m - 1/2))/2) where
  domain := by norm_num
  sound m hmLo hmHi := by
    exact cell_bias_nonneg m ⟨hmLo, hmHi⟩

theorem accepted_cell :
    ∀ m, (2563 / 10240) ≤ m → m ≤ (1283 / 5120) → 0 ≤ doubleCapHighResidual m := by
  intro m hmLo hmHi
  unfold doubleCapHighResidual
  apply doubleCapEndpointResidual_nonneg_of_biasCell acceptedCertificate hmLo hmHi
  exact div_pos (by linarith [H_nonneg (by linarith : 0 ≤ 2*m-1/2) (by linarith : 2*m-1/2 ≤ 1)]) two_pos

#print axioms cell_bias_nonneg
#print axioms accepted_cell

end GeneralCK.Certificates.DoubleCapMiddle.Cell0011

end


