-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0395__5
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0395__5
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T10:40:10.821809+00:00
-- url     : https://prove2.me/theorems/6e80bb9e-c98d-4f6e-954d-3a23d7dc8553
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0395 (+4 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0396, GeneralCK.Certificates.Gener…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0395 (+4 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0396, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0397, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0398, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0399)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0395 (+4 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0396, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0397, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0398, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0399)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0395 (+4 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0396, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0397, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0398, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0399) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0395 (+4 modules: GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0396, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0397, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0398, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0399).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0390Logs__8
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0398Logs__4

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0395 =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0395
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Reflection
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem cell_bias_nonneg (m : ℝ) (hm : Bounds (1591 / 4096) (3979 / 10240) m) :
    let h := (1 + H (2*m - 1/2))/2
    let x := 1-2*m
    let y := 1-2*entropyInverse h
    let c := regularContact (x/(Real.log 2*h))
    0 ≤ 2*(biasE x-Real.log 2*h)-y*SmallMean.A y+x*SmallMean.A c := by
  have hEq : biasE (2-4*m) = Real.log 2 * H (2*m-1/2) := by
    have hmstrict : 1/4 < m := by
      have hlo : (1/4 : ℝ) < (1591 / 4096) := by norm_num
      exact lt_of_lt_of_le hlo hm.1
    rw [show 2-4*m = 1-2*(2*m-1/2) by ring,
      GeneralCK.Correction.Natural.biasE_probability (by linarith [hmstrict]) (by linarith [hm.2]),
      GeneralCK.Certificates.Mixed.hn_eq_H_mul_log]
    ring
  have hLh : Real.log 2 * ((1 + H (2*m - 1/2))/2) = (Real.log 2 + biasE (2-4*m))/2 := by
    rw [hEq]
    ring
  let x0 : ℝ := (2 / 1)*m
  have hx0 : Bounds (1591 / 2048) (3979 / 5120) x0 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hm <;> norm_num
  let x1 : ℝ := -x0
  have hx1 : Bounds (-3979 / 5120) (-1591 / 2048) x1 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx0
  let x2 : ℝ := (1 / 1)+x1
  have hx2 : Bounds (1141 / 5120) (457 / 2048) x2 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx1 <;> norm_num
  let x3 : ℝ := (1 / 1)-x0
  have hx3 : Bounds (1141 / 5120) (457 / 2048) x3 := by
    exact hx2
  let x4 : ℝ := (4 / 1)*m
  have hx4 : Bounds (1591 / 1024) (3979 / 2560) x4 := by
    apply bounds_mul (bounds_const ((4 / 1) : ℝ)) hm <;> norm_num
  let x5 : ℝ := -x4
  have hx5 : Bounds (-3979 / 2560) (-1591 / 1024) x5 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx4
  let x6 : ℝ := (2 / 1)+x5
  have hx6 : Bounds (1141 / 2560) (457 / 1024) x6 := by
    apply bounds_add (bounds_const ((2 / 1) : ℝ)) hx5 <;> norm_num
  let x7 : ℝ := (2 / 1)-x4
  have hx7 : Bounds (1141 / 2560) (457 / 1024) x7 := by
    exact hx6
  let x8 : ℝ := Real.log (2 / 1)
  have hx8 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x8 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x9 : ℝ := (1 / 1)+(457 / 2048)
  have hx9 : Bounds (2505 / 2048) (2505 / 2048) x9 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((457 / 2048) : ℝ)) <;> norm_num
  let x10 : ℝ := (1 / 1)+(457 / 2048)
  have hx10 : Bounds (2505 / 2048) (2505 / 2048) x10 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((457 / 2048) : ℝ)) <;> norm_num
  let x11 : ℝ := Real.log x10
  have hx11 : Bounds (201425027 / 1000000000) (50356257 / 250000000) x11 := by
    exact bounds_log hx10 (by norm_num) (by simpa only [div_one] using reflection_log_1.1) (by simpa only [div_one] using reflection_log_1.2)
  let x12 : ℝ := x9*x11
  have hx12 : Bounds (246371920231 / 1000000000000) (15398245091 / 62500000000) x12 := by
    apply bounds_mul hx9 hx11 <;> norm_num
  let x13 : ℝ := -(457 / 2048)
  have hx13 : Bounds (-457 / 2048) (-457 / 2048) x13 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((457 / 2048) : ℝ))
  let x14 : ℝ := (1 / 1)+x13
  have hx14 : Bounds (1591 / 2048) (1591 / 2048) x14 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx13 <;> norm_num
  let x15 : ℝ := (1 / 1)-(457 / 2048)
  have hx15 : Bounds (1591 / 2048) (1591 / 2048) x15 := by
    exact hx14
  let x16 : ℝ := -(457 / 2048)
  have hx16 : Bounds (-457 / 2048) (-457 / 2048) x16 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((457 / 2048) : ℝ))
  let x17 : ℝ := (1 / 1)+x16
  have hx17 : Bounds (1591 / 2048) (1591 / 2048) x17 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx16 <;> norm_num
  let x18 : ℝ := (1 / 1)-(457 / 2048)
  have hx18 : Bounds (1591 / 2048) (1591 / 2048) x18 := by
    exact hx17
  let x19 : ℝ := Real.log x18
  have hx19 : Bounds (-126250479 / 500000000) (-252500957 / 1000000000) x19 := by
    exact bounds_log hx18 (by norm_num) (by simpa only [div_one] using reflection_log_2.1) (by simpa only [div_one] using reflection_log_2.2)
  let x20 : ℝ := x15*x19
  have hx20 : Bounds (-196156750087 / 1000000000000) (-19615674931 / 100000000000) x20 := by
    apply bounds_mul hx15 hx19 <;> norm_num
  let x21 : ℝ := x12+x20
  have hx21 : Bounds (1569224067 / 31250000000) (25107586073 / 500000000000) x21 := by
    apply bounds_add hx12 hx20 <;> norm_num
  let x22 : ℝ := (2 / 1)⁻¹
  have hx22 : Bounds (1 / 2) (1 / 2) x22 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x23 : ℝ := x21*x22
  have hx23 : Bounds (1569224067 / 62500000000) (25107586073 / 1000000000000) x23 := by
    apply bounds_mul hx21 hx22 <;> norm_num
  let x24 : ℝ := x21/(2 / 1)
  have hx24 : Bounds (1569224067 / 62500000000) (25107586073 / 1000000000000) x24 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx23
  let x25 : ℝ := -x24
  have hx25 : Bounds (-25107586073 / 1000000000000) (-1569224067 / 62500000000) x25 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx24
  let x26 : ℝ := x8+x25
  have hx26 : Bounds (668039593927 / 1000000000000) (83504949491 / 125000000000) x26 := by
    apply bounds_add hx8 hx25 <;> norm_num
  let x27 : ℝ := x8-x24
  have hx27 : Bounds (668039593927 / 1000000000000) (83504949491 / 125000000000) x27 := by
    exact hx26
  let x28 : ℝ := biasE (457 / 2048)
  have hx28 : Bounds (668039593927 / 1000000000000) (83504949491 / 125000000000) x28 := by
    simpa +zetaDelta only [biasE, div_one] using hx27
  let x29 : ℝ := Real.log (2 / 1)
  have hx29 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x29 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x30 : ℝ := (1 / 1)+(1141 / 5120)
  have hx30 : Bounds (6261 / 5120) (6261 / 5120) x30 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1141 / 5120) : ℝ)) <;> norm_num
  let x31 : ℝ := (1 / 1)+(1141 / 5120)
  have hx31 : Bounds (6261 / 5120) (6261 / 5120) x31 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1141 / 5120) : ℝ)) <;> norm_num
  let x32 : ℝ := Real.log x31
  have hx32 : Bounds (201185477 / 1000000000) (100592739 / 500000000) x32 := by
    exact bounds_log hx31 (by norm_num) (by simpa only [div_one] using reflection_log_3.1) (by simpa only [div_one] using reflection_log_3.2)
  let x33 : ℝ := x30*x32
  have hx33 : Bounds (246019974901 / 1000000000000) (1968159809 / 8000000000) x33 := by
    apply bounds_mul hx30 hx32 <;> norm_num
  let x34 : ℝ := -(1141 / 5120)
  have hx34 : Bounds (-1141 / 5120) (-1141 / 5120) x34 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1141 / 5120) : ℝ))
  let x35 : ℝ := (1 / 1)+x34
  have hx35 : Bounds (3979 / 5120) (3979 / 5120) x35 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx34 <;> norm_num
  let x36 : ℝ := (1 / 1)-(1141 / 5120)
  have hx36 : Bounds (3979 / 5120) (3979 / 5120) x36 := by
    exact hx35
  let x37 : ℝ := -(1141 / 5120)
  have hx37 : Bounds (-1141 / 5120) (-1141 / 5120) x37 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1141 / 5120) : ℝ))
  let x38 : ℝ := (1 / 1)+x37
  have hx38 : Bounds (3979 / 5120) (3979 / 5120) x38 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx37 <;> norm_num
  let x39 : ℝ := (1 / 1)-(1141 / 5120)
  have hx39 : Bounds (3979 / 5120) (3979 / 5120) x39 := by
    exact hx38
  let x40 : ℝ := Real.log x39
  have hx40 : Bounds (-63030977 / 250000000) (-252123907 / 1000000000) x40 := by
    exact bounds_log hx39 (by norm_num) (by simpa only [div_one] using reflection_log_4.1) (by simpa only [div_one] using reflection_log_4.2)
  let x41 : ℝ := x36*x40
  have hx41 : Bounds (-195937701159 / 1000000000000) (-195937700381 / 1000000000000) x41 := by
    apply bounds_mul hx36 hx40 <;> norm_num
  let x42 : ℝ := x33+x41
  have hx42 : Bounds (25041136871 / 500000000000) (1565071117 / 31250000000) x42 := by
    apply bounds_add hx33 hx41 <;> norm_num
  let x43 : ℝ := (2 / 1)⁻¹
  have hx43 : Bounds (1 / 2) (1 / 2) x43 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x44 : ℝ := x42*x43
  have hx44 : Bounds (25041136871 / 1000000000000) (1565071117 / 62500000000) x44 := by
    apply bounds_mul hx42 hx43 <;> norm_num
  let x45 : ℝ := x42/(2 / 1)
  have hx45 : Bounds (25041136871 / 1000000000000) (1565071117 / 62500000000) x45 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx44
  let x46 : ℝ := -x45
  have hx46 : Bounds (-1565071117 / 62500000000) (-25041136871 / 1000000000000) x46 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx45
  let x47 : ℝ := x29+x46
  have hx47 : Bounds (41756627633 / 62500000000) (668106044129 / 1000000000000) x47 := by
    apply bounds_add hx29 hx46 <;> norm_num
  let x48 : ℝ := x29-x45
  have hx48 : Bounds (41756627633 / 62500000000) (668106044129 / 1000000000000) x48 := by
    exact hx47
  let x49 : ℝ := biasE (1141 / 5120)
  have hx49 : Bounds (41756627633 / 62500000000) (668106044129 / 1000000000000) x49 := by
    simpa +zetaDelta only [biasE, div_one] using hx48
  let x50 : ℝ := biasE x3
  have hx50 : Bounds (668039593927 / 1000000000000) (668106044129 / 1000000000000) x50 := by
    exact bounds_biasE hx3 (by norm_num) (by norm_num) hx28.1 hx49.2
  let x51 : ℝ := Real.log (2 / 1)
  have hx51 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x51 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x52 : ℝ := (1 / 1)+(457 / 1024)
  have hx52 : Bounds (1481 / 1024) (1481 / 1024) x52 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((457 / 1024) : ℝ)) <;> norm_num
  let x53 : ℝ := (1 / 1)+(457 / 1024)
  have hx53 : Bounds (1481 / 1024) (1481 / 1024) x53 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((457 / 1024) : ℝ)) <;> norm_num
  let x54 : ℝ := Real.log x53
  have hx54 : Bounds (23062563 / 62500000) (369001009 / 1000000000) x54 := by
    exact bounds_log hx53 (by norm_num) (by simpa only [div_one] using reflection_log_5.1) (by simpa only [div_one] using reflection_log_5.2)
  let x55 : ℝ := x52*x54
  have hx55 : Bounds (533682121921 / 1000000000000) (533682123369 / 1000000000000) x55 := by
    apply bounds_mul hx52 hx54 <;> norm_num
  let x56 : ℝ := -(457 / 1024)
  have hx56 : Bounds (-457 / 1024) (-457 / 1024) x56 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((457 / 1024) : ℝ))
  let x57 : ℝ := (1 / 1)+x56
  have hx57 : Bounds (567 / 1024) (567 / 1024) x57 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx56 <;> norm_num
  let x58 : ℝ := (1 / 1)-(457 / 1024)
  have hx58 : Bounds (567 / 1024) (567 / 1024) x58 := by
    exact hx57
  let x59 : ℝ := -(457 / 1024)
  have hx59 : Bounds (-457 / 1024) (-457 / 1024) x59 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((457 / 1024) : ℝ))
  let x60 : ℝ := (1 / 1)+x59
  have hx60 : Bounds (567 / 1024) (567 / 1024) x60 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx59 <;> norm_num
  let x61 : ℝ := (1 / 1)-(457 / 1024)
  have hx61 : Bounds (567 / 1024) (567 / 1024) x61 := by
    exact hx60
  let x62 : ℝ := Real.log x61
  have hx62 : Bounds (-295556251 / 500000000) (-591112501 / 1000000000) x62 := by
    exact bounds_log hx61 (by norm_num) (by simpa only [div_one] using reflection_log_6.1) (by simpa only [div_one] using reflection_log_6.2)
  let x63 : ℝ := x58*x62
  have hx63 : Bounds (-327305457651 / 1000000000000) (-40913182137 / 125000000000) x63 := by
    apply bounds_mul hx58 hx62 <;> norm_num
  let x64 : ℝ := x55+x63
  have hx64 : Bounds (20637666427 / 100000000000) (206376666273 / 1000000000000) x64 := by
    apply bounds_add hx55 hx63 <;> norm_num
  let x65 : ℝ := (2 / 1)⁻¹
  have hx65 : Bounds (1 / 2) (1 / 2) x65 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x66 : ℝ := x64*x65
  have hx66 : Bounds (20637666427 / 200000000000) (103188333137 / 1000000000000) x66 := by
    apply bounds_mul hx64 hx65 <;> norm_num
  let x67 : ℝ := x64/(2 / 1)
  have hx67 : Bounds (20637666427 / 200000000000) (103188333137 / 1000000000000) x67 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx66
  let x68 : ℝ := -x67
  have hx68 : Bounds (-103188333137 / 1000000000000) (-20637666427 / 200000000000) x68 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx67
  let x69 : ℝ := x51+x68
  have hx69 : Bounds (589958846863 / 1000000000000) (117991769773 / 200000000000) x69 := by
    apply bounds_add hx51 hx68 <;> norm_num
  let x70 : ℝ := x51-x67
  have hx70 : Bounds (589958846863 / 1000000000000) (117991769773 / 200000000000) x70 := by
    exact hx69
  let x71 : ℝ := biasE (457 / 1024)
  have hx71 : Bounds (589958846863 / 1000000000000) (117991769773 / 200000000000) x71 := by
    simpa +zetaDelta only [biasE, div_one] using hx70
  let x72 : ℝ := Real.log (2 / 1)
  have hx72 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x72 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x73 : ℝ := (1 / 1)+(1141 / 2560)
  have hx73 : Bounds (3701 / 2560) (3701 / 2560) x73 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1141 / 2560) : ℝ)) <;> norm_num
  let x74 : ℝ := (1 / 1)+(1141 / 2560)
  have hx74 : Bounds (3701 / 2560) (3701 / 2560) x74 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1141 / 2560) : ℝ)) <;> norm_num
  let x75 : ℝ := Real.log x74
  have hx75 : Bounds (184297897 / 500000000) (73719159 / 200000000) x75 := by
    exact bounds_log hx74 (by norm_num) (by simpa only [div_one] using reflection_log_7.1) (by simpa only [div_one] using reflection_log_7.2)
  let x76 : ℝ := x73*x75
  have hx76 : Bounds (532880091247 / 1000000000000) (266440046347 / 500000000000) x76 := by
    apply bounds_mul hx73 hx75 <;> norm_num
  let x77 : ℝ := -(1141 / 2560)
  have hx77 : Bounds (-1141 / 2560) (-1141 / 2560) x77 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1141 / 2560) : ℝ))
  let x78 : ℝ := (1 / 1)+x77
  have hx78 : Bounds (1419 / 2560) (1419 / 2560) x78 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx77 <;> norm_num
  let x79 : ℝ := (1 / 1)-(1141 / 2560)
  have hx79 : Bounds (1419 / 2560) (1419 / 2560) x79 := by
    exact hx78
  let x80 : ℝ := -(1141 / 2560)
  have hx80 : Bounds (-1141 / 2560) (-1141 / 2560) x80 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1141 / 2560) : ℝ))
  let x81 : ℝ := (1 / 1)+x80
  have hx81 : Bounds (1419 / 2560) (1419 / 2560) x81 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx80 <;> norm_num
  let x82 : ℝ := (1 / 1)-(1141 / 2560)
  have hx82 : Bounds (1419 / 2560) (1419 / 2560) x82 := by
    exact hx81
  let x83 : ℝ := Real.log x82
  have hx83 : Bounds (-590054861 / 1000000000) (-29502743 / 50000000) x83 := by
    exact bounds_log hx82 (by norm_num) (by simpa only [div_one] using reflection_log_8.1) (by simpa only [div_one] using reflection_log_8.2)
  let x84 : ℝ := x79*x83
  have hx84 : Bounds (-327065565531 / 1000000000000) (-20441597811 / 62500000000) x84 := by
    apply bounds_mul hx79 hx83 <;> norm_num
  let x85 : ℝ := x76+x84
  have hx85 : Bounds (51453631429 / 250000000000) (102907263859 / 500000000000) x85 := by
    apply bounds_add hx76 hx84 <;> norm_num
  let x86 : ℝ := (2 / 1)⁻¹
  have hx86 : Bounds (1 / 2) (1 / 2) x86 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x87 : ℝ := x85*x86
  have hx87 : Bounds (51453631429 / 500000000000) (102907263859 / 1000000000000) x87 := by
    apply bounds_mul hx85 hx86 <;> norm_num
  let x88 : ℝ := x85/(2 / 1)
  have hx88 : Bounds (51453631429 / 500000000000) (102907263859 / 1000000000000) x88 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx87
  let x89 : ℝ := -x88
  have hx89 : Bounds (-102907263859 / 1000000000000) (-51453631429 / 500000000000) x89 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx88
  let x90 : ℝ := x72+x89
  have hx90 : Bounds (590239916141 / 1000000000000) (295119959071 / 500000000000) x90 := by
    apply bounds_add hx72 hx89 <;> norm_num
  let x91 : ℝ := x72-x88
  have hx91 : Bounds (590239916141 / 1000000000000) (295119959071 / 500000000000) x91 := by
    exact hx90
  let x92 : ℝ := biasE (1141 / 2560)
  have hx92 : Bounds (590239916141 / 1000000000000) (295119959071 / 500000000000) x92 := by
    simpa +zetaDelta only [biasE, div_one] using hx91
  let x93 : ℝ := biasE x7
  have hx93 : Bounds (589958846863 / 1000000000000) (295119959071 / 500000000000) x93 := by
    exact bounds_biasE hx7 (by norm_num) (by norm_num) hx71.1 hx92.2
  let x94 : ℝ := Real.log (2 / 1)
  have hx94 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x94 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x95 : ℝ := x94+x93
  have hx95 : Bounds (1283106026863 / 1000000000000) (641693549571 / 500000000000) x95 := by
    apply bounds_add hx94 hx93 <;> norm_num
  let x96 : ℝ := (2 / 1)⁻¹
  have hx96 : Bounds (1 / 2) (1 / 2) x96 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x97 : ℝ := x95*x96
  have hx97 : Bounds (641553013431 / 1000000000000) (641693549571 / 1000000000000) x97 := by
    apply bounds_mul hx95 hx96 <;> norm_num
  let x98 : ℝ := x95/(2 / 1)
  have hx98 : Bounds (641553013431 / 1000000000000) (641693549571 / 1000000000000) x98 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx97
  let x99 : ℝ := Real.log (2 / 1)
  have hx99 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x99 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x100 : ℝ := (1 / 1)+(318009 / 1000000)
  have hx100 : Bounds (1318009 / 1000000) (1318009 / 1000000) x100 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((318009 / 1000000) : ℝ)) <;> norm_num
  let x101 : ℝ := (1 / 1)+(318009 / 1000000)
  have hx101 : Bounds (1318009 / 1000000) (1318009 / 1000000) x101 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((318009 / 1000000) : ℝ)) <;> norm_num
  let x102 : ℝ := Real.log x101
  have hx102 : Bounds (34515283 / 125000000) (55224453 / 200000000) x102 := by
    exact bounds_log hx101 (by norm_num) (by simpa only [div_one] using reflection_log_9.1) (by simpa only [div_one] using reflection_log_9.2)
  let x103 : ℝ := x100*x102
  have hx103 : Bounds (90982907263 / 250000000000) (363931630371 / 1000000000000) x103 := by
    apply bounds_mul hx100 hx102 <;> norm_num
  let x104 : ℝ := -(318009 / 1000000)
  have hx104 : Bounds (-318009 / 1000000) (-318009 / 1000000) x104 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((318009 / 1000000) : ℝ))
  let x105 : ℝ := (1 / 1)+x104
  have hx105 : Bounds (681991 / 1000000) (681991 / 1000000) x105 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx104 <;> norm_num
  let x106 : ℝ := (1 / 1)-(318009 / 1000000)
  have hx106 : Bounds (681991 / 1000000) (681991 / 1000000) x106 := by
    exact hx105
  let x107 : ℝ := -(318009 / 1000000)
  have hx107 : Bounds (-318009 / 1000000) (-318009 / 1000000) x107 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((318009 / 1000000) : ℝ))
  let x108 : ℝ := (1 / 1)+x107
  have hx108 : Bounds (681991 / 1000000) (681991 / 1000000) x108 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx107 <;> norm_num
  let x109 : ℝ := (1 / 1)-(318009 / 1000000)
  have hx109 : Bounds (681991 / 1000000) (681991 / 1000000) x109 := by
    exact hx108
  let x110 : ℝ := Real.log x109
  have hx110 : Bounds (-191369409 / 500000000) (-382738817 / 1000000000) x110 := by
    exact bounds_log hx109 (by norm_num) (by simpa only [div_one] using reflection_log_10.1) (by simpa only [div_one] using reflection_log_10.2)
  let x111 : ℝ := x106*x110
  have hx111 : Bounds (-261024429227 / 1000000000000) (-509813337 / 1953125000) x111 := by
    apply bounds_mul hx106 hx110 <;> norm_num
  let x112 : ℝ := x103+x111
  have hx112 : Bounds (4116287993 / 40000000000) (102907201827 / 1000000000000) x112 := by
    apply bounds_add hx103 hx111 <;> norm_num
  let x113 : ℝ := (2 / 1)⁻¹
  have hx113 : Bounds (1 / 2) (1 / 2) x113 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x114 : ℝ := x112*x113
  have hx114 : Bounds (6431699989 / 125000000000) (25726800457 / 500000000000) x114 := by
    apply bounds_mul hx112 hx113 <;> norm_num
  let x115 : ℝ := x112/(2 / 1)
  have hx115 : Bounds (6431699989 / 125000000000) (25726800457 / 500000000000) x115 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx114
  let x116 : ℝ := -x115
  have hx116 : Bounds (-25726800457 / 500000000000) (-6431699989 / 125000000000) x116 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx115
  let x117 : ℝ := x99+x116
  have hx117 : Bounds (320846789543 / 500000000000) (20052924409 / 31250000000) x117 := by
    apply bounds_add hx99 hx116 <;> norm_num
  let x118 : ℝ := x99-x115
  have hx118 : Bounds (320846789543 / 500000000000) (20052924409 / 31250000000) x118 := by
    exact hx117
  let x119 : ℝ := biasE (318009 / 1000000)
  have hx119 : Bounds (320846789543 / 500000000000) (20052924409 / 31250000000) x119 := by
    simpa +zetaDelta only [biasE, div_one] using hx118
  let x120 : ℝ := Real.log (2 / 1)
  have hx120 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x120 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x121 : ℝ := (1 / 1)+(79609 / 250000)
  have hx121 : Bounds (329609 / 250000) (329609 / 250000) x121 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((79609 / 250000) : ℝ)) <;> norm_num
  let x122 : ℝ := (1 / 1)+(79609 / 250000)
  have hx122 : Bounds (329609 / 250000) (329609 / 250000) x122 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((79609 / 250000) : ℝ)) <;> norm_num
  let x123 : ℝ := Real.log x122
  have hx123 : Bounds (55289237 / 200000000) (138223093 / 500000000) x123 := by
    exact bounds_log hx122 (by norm_num) (by simpa only [div_one] using reflection_log_11.1) (by simpa only [div_one] using reflection_log_11.2)
  let x124 : ℝ := x121*x123
  have hx124 : Bounds (182238301183 / 500000000000) (182238301843 / 500000000000) x124 := by
    apply bounds_mul hx121 hx123 <;> norm_num
  let x125 : ℝ := -(79609 / 250000)
  have hx125 : Bounds (-79609 / 250000) (-79609 / 250000) x125 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((79609 / 250000) : ℝ))
  let x126 : ℝ := (1 / 1)+x125
  have hx126 : Bounds (170391 / 250000) (170391 / 250000) x126 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx125 <;> norm_num
  let x127 : ℝ := (1 / 1)-(79609 / 250000)
  have hx127 : Bounds (170391 / 250000) (170391 / 250000) x127 := by
    exact hx126
  let x128 : ℝ := -(79609 / 250000)
  have hx128 : Bounds (-79609 / 250000) (-79609 / 250000) x128 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((79609 / 250000) : ℝ))
  let x129 : ℝ := (1 / 1)+x128
  have hx129 : Bounds (170391 / 250000) (170391 / 250000) x129 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx128 <;> norm_num
  let x130 : ℝ := (1 / 1)-(79609 / 250000)
  have hx130 : Bounds (170391 / 250000) (170391 / 250000) x130 := by
    exact hx129
  let x131 : ℝ := Real.log x130
  have hx131 : Bounds (-191682561 / 500000000) (-383365121 / 1000000000) x131 := by
    exact bounds_log hx130 (by norm_num) (by simpa only [div_one] using reflection_log_12.1) (by simpa only [div_one] using reflection_log_12.2)
  let x132 : ℝ := x127*x131
  have hx132 : Bounds (-261287866011 / 1000000000000) (-261287865329 / 1000000000000) x132 := by
    apply bounds_mul hx127 hx131 <;> norm_num
  let x133 : ℝ := x124+x132
  have hx133 : Bounds (20637747271 / 200000000000) (103188738357 / 1000000000000) x133 := by
    apply bounds_add hx124 hx132 <;> norm_num
  let x134 : ℝ := (2 / 1)⁻¹
  have hx134 : Bounds (1 / 2) (1 / 2) x134 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x135 : ℝ := x133*x134
  have hx135 : Bounds (51594368177 / 1000000000000) (51594369179 / 1000000000000) x135 := by
    apply bounds_mul hx133 hx134 <;> norm_num
  let x136 : ℝ := x133/(2 / 1)
  have hx136 : Bounds (51594368177 / 1000000000000) (51594369179 / 1000000000000) x136 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx135
  let x137 : ℝ := -x136
  have hx137 : Bounds (-51594369179 / 1000000000000) (-51594368177 / 1000000000000) x137 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx136
  let x138 : ℝ := x120+x137
  have hx138 : Bounds (641552810821 / 1000000000000) (641552812823 / 1000000000000) x138 := by
    apply bounds_add hx120 hx137 <;> norm_num
  let x139 : ℝ := x120-x136
  have hx139 : Bounds (641552810821 / 1000000000000) (641552812823 / 1000000000000) x139 := by
    exact hx138
  let x140 : ℝ := biasE (79609 / 250000)
  have hx140 : Bounds (641552810821 / 1000000000000) (641552812823 / 1000000000000) x140 := by
    simpa +zetaDelta only [biasE, div_one] using hx139
  let y : ℝ := 1 - 2 * entropyInverse ((1 + H (2*m - 1/2))/2)
  have hLh' : Real.log 2 * ((1 + H (2*m - 1/2))/2) = x98 := by
    simpa +zetaDelta only [div_one] using hLh
  have hy : Bounds (318009 / 1000000) (79609 / 250000) y := by
    apply entropyInverseBias_bracket
    · exact div_nonneg (add_nonneg zero_le_one
        (H_nonneg (by linarith [hm.1]) (by linarith [hm.2]))) two_pos.le
    · linarith [H_le_one (2*m-1/2)]
    · norm_num
    · norm_num
    · norm_num
    · have h1 : biasE (79609 / 250000) ≤ (641552812823 / 1000000000000) := hx140.2
      have h2 : (641553013431 / 1000000000000) ≤ x98 := hx98.1
      linarith [hLh']
    · have h1 : x98 ≤ (641693549571 / 1000000000000) := hx98.2
      have h2 : (320846789543 / 500000000000) ≤ biasE (318009 / 1000000) := hx119.1
      linarith [hLh']
  let x141 : ℝ := x3⁻¹
  have hx141 : Bounds (1120350109409 / 250000000000) (560911481157 / 125000000000) x141 := by
    apply bounds_inv hx3 <;> norm_num
  let x142 : ℝ := x98*x141
  have hx142 : Bounds (718763988789 / 250000000000) (2879466234711 / 1000000000000) x142 := by
    apply bounds_mul hx98 hx141 <;> norm_num
  let x143 : ℝ := x98/x3
  have hx143 : Bounds (718763988789 / 250000000000) (2879466234711 / 1000000000000) x143 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx142
  let x144 : ℝ := Real.log (2 / 1)
  have hx144 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x144 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x145 : ℝ := (1 / 1)+(115671 / 500000)
  have hx145 : Bounds (615671 / 500000) (615671 / 500000) x145 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((115671 / 500000) : ℝ)) <;> norm_num
  let x146 : ℝ := (1 / 1)+(115671 / 500000)
  have hx146 : Bounds (615671 / 500000) (615671 / 500000) x146 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((115671 / 500000) : ℝ)) <;> norm_num
  let x147 : ℝ := Real.log x146
  have hx147 : Bounds (208104631 / 1000000000) (26013079 / 125000000) x147 := by
    exact bounds_log hx146 (by norm_num) (by simpa only [div_one] using reflection_log_13.1) (by simpa only [div_one] using reflection_log_13.2)
  let x148 : ℝ := x145*x147
  have hx148 : Bounds (4003874571 / 15625000000) (256247973777 / 1000000000000) x148 := by
    apply bounds_mul hx145 hx147 <;> norm_num
  let x149 : ℝ := -(115671 / 500000)
  have hx149 : Bounds (-115671 / 500000) (-115671 / 500000) x149 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((115671 / 500000) : ℝ))
  let x150 : ℝ := (1 / 1)+x149
  have hx150 : Bounds (384329 / 500000) (384329 / 500000) x150 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx149 <;> norm_num
  let x151 : ℝ := (1 / 1)-(115671 / 500000)
  have hx151 : Bounds (384329 / 500000) (384329 / 500000) x151 := by
    exact hx150
  let x152 : ℝ := -(115671 / 500000)
  have hx152 : Bounds (-115671 / 500000) (-115671 / 500000) x152 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((115671 / 500000) : ℝ))
  let x153 : ℝ := (1 / 1)+x152
  have hx153 : Bounds (384329 / 500000) (384329 / 500000) x153 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx152 <;> norm_num
  let x154 : ℝ := (1 / 1)-(115671 / 500000)
  have hx154 : Bounds (384329 / 500000) (384329 / 500000) x154 := by
    exact hx153
  let x155 : ℝ := Real.log x154
  have hx155 : Bounds (-131554571 / 500000000) (-263109141 / 1000000000) x155 := by
    exact bounds_log hx154 (by norm_num) (by simpa only [div_one] using reflection_log_14.1) (by simpa only [div_one] using reflection_log_14.2)
  let x156 : ℝ := x151*x155
  have hx156 : Bounds (-25280118359 / 125000000000) (-101120473051 / 500000000000) x156 := by
    apply bounds_mul hx151 hx155 <;> norm_num
  let x157 : ℝ := x148+x156
  have hx157 : Bounds (6750878209 / 125000000000) (2160281107 / 40000000000) x157 := by
    apply bounds_add hx148 hx156 <;> norm_num
  let x158 : ℝ := (2 / 1)⁻¹
  have hx158 : Bounds (1 / 2) (1 / 2) x158 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x159 : ℝ := x157*x158
  have hx159 : Bounds (6750878209 / 250000000000) (13501756919 / 500000000000) x159 := by
    apply bounds_mul hx157 hx158 <;> norm_num
  let x160 : ℝ := x157/(2 / 1)
  have hx160 : Bounds (6750878209 / 250000000000) (13501756919 / 500000000000) x160 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx159
  let x161 : ℝ := -x160
  have hx161 : Bounds (-13501756919 / 500000000000) (-6750878209 / 250000000000) x161 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx160
  let x162 : ℝ := x144+x161
  have hx162 : Bounds (333071833081 / 500000000000) (166535917041 / 250000000000) x162 := by
    apply bounds_add hx144 hx161 <;> norm_num
  let x163 : ℝ := x144-x160
  have hx163 : Bounds (333071833081 / 500000000000) (166535917041 / 250000000000) x163 := by
    exact hx162
  let x164 : ℝ := biasE (115671 / 500000)
  have hx164 : Bounds (333071833081 / 500000000000) (166535917041 / 250000000000) x164 := by
    simpa +zetaDelta only [biasE, div_one] using hx163
  let x165 : ℝ := Real.log (2 / 1)
  have hx165 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x165 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x166 : ℝ := (1 / 1)+(231671 / 1000000)
  have hx166 : Bounds (1231671 / 1000000) (1231671 / 1000000) x166 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((231671 / 1000000) : ℝ)) <;> norm_num
  let x167 : ℝ := (1 / 1)+(231671 / 1000000)
  have hx167 : Bounds (1231671 / 1000000) (1231671 / 1000000) x167 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((231671 / 1000000) : ℝ)) <;> norm_num
  let x168 : ℝ := Real.log x167
  have hx168 : Bounds (208371783 / 1000000000) (26046473 / 125000000) x168 := by
    exact bounds_log hx167 (by norm_num) (by simpa only [div_one] using reflection_log_15.1) (by simpa only [div_one] using reflection_log_15.2)
  let x169 : ℝ := x166*x168
  have hx169 : Bounds (256645482339 / 1000000000000) (64161370893 / 250000000000) x169 := by
    apply bounds_mul hx166 hx168 <;> norm_num
  let x170 : ℝ := -(231671 / 1000000)
  have hx170 : Bounds (-231671 / 1000000) (-231671 / 1000000) x170 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((231671 / 1000000) : ℝ))
  let x171 : ℝ := (1 / 1)+x170
  have hx171 : Bounds (768329 / 1000000) (768329 / 1000000) x171 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx170 <;> norm_num
  let x172 : ℝ := (1 / 1)-(231671 / 1000000)
  have hx172 : Bounds (768329 / 1000000) (768329 / 1000000) x172 := by
    exact hx171
  let x173 : ℝ := -(231671 / 1000000)
  have hx173 : Bounds (-231671 / 1000000) (-231671 / 1000000) x173 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((231671 / 1000000) : ℝ))
  let x174 : ℝ := (1 / 1)+x173
  have hx174 : Bounds (768329 / 1000000) (768329 / 1000000) x174 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx173 <;> norm_num
  let x175 : ℝ := (1 / 1)-(231671 / 1000000)
  have hx175 : Bounds (768329 / 1000000) (768329 / 1000000) x175 := by
    exact hx174
  let x176 : ℝ := Real.log x175
  have hx176 : Bounds (-263537253 / 1000000000) (-65884313 / 250000000) x176 := by
    exact bounds_log hx175 (by norm_num) (by simpa only [div_one] using reflection_log_16.1) (by simpa only [div_one] using reflection_log_16.2)
  let x177 : ℝ := x172*x176
  have hx177 : Bounds (-202483314061 / 1000000000000) (-202483313291 / 1000000000000) x177 := by
    apply bounds_mul hx172 hx176 <;> norm_num
  let x178 : ℝ := x169+x177
  have hx178 : Bounds (27081084139 / 500000000000) (54162170281 / 1000000000000) x178 := by
    apply bounds_add hx169 hx177 <;> norm_num
  let x179 : ℝ := (2 / 1)⁻¹
  have hx179 : Bounds (1 / 2) (1 / 2) x179 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x180 : ℝ := x178*x179
  have hx180 : Bounds (27081084139 / 1000000000000) (27081085141 / 1000000000000) x180 := by
    apply bounds_mul hx178 hx179 <;> norm_num
  let x181 : ℝ := x178/(2 / 1)
  have hx181 : Bounds (27081084139 / 1000000000000) (27081085141 / 1000000000000) x181 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx180
  let x182 : ℝ := -x181
  have hx182 : Bounds (-27081085141 / 1000000000000) (-27081084139 / 1000000000000) x182 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx181
  let x183 : ℝ := x165+x182
  have hx183 : Bounds (666066094859 / 1000000000000) (666066096861 / 1000000000000) x183 := by
    apply bounds_add hx165 hx182 <;> norm_num
  let x184 : ℝ := x165-x181
  have hx184 : Bounds (666066094859 / 1000000000000) (666066096861 / 1000000000000) x184 := by
    exact hx183
  let x185 : ℝ := biasE (231671 / 1000000)
  have hx185 : Bounds (666066094859 / 1000000000000) (666066096861 / 1000000000000) x185 := by
    simpa +zetaDelta only [biasE, div_one] using hx184
  let x186 : ℝ := x143*(115671 / 500000)
  have hx186 : Bounds (665121194777 / 1000000000000) (666141477671 / 1000000000000) x186 := by
    apply bounds_mul hx143 (bounds_const ((115671 / 500000) : ℝ)) <;> norm_num
  let x187 : ℝ := x143*(231671 / 1000000)
  have hx187 : Bounds (333033544093 / 500000000000) (333544411031 / 500000000000) x187 := by
    apply bounds_mul hx143 (bounds_const ((231671 / 1000000) : ℝ)) <;> norm_num
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
  have hc : Bounds (115671 / 500000) (231671 / 1000000) c := by
    apply contact_bracket hc0 hcMem.2.le (by norm_num) (by norm_num) (by norm_num)
      (show 0 < x143 by linarith [hx143.1]) hcEq
    · have h1 : x143 * (115671 / 500000) ≤ (666141477671 / 1000000000000) := hx186.2
      have h2 : (333071833081 / 500000000000) ≤ biasE (115671 / 500000) := hx164.1
      linarith
    · have h1 : biasE (231671 / 1000000) ≤ (666066096861 / 1000000000000) := hx185.2
      have h2 : (333033544093 / 500000000000) ≤ x143 * (231671 / 1000000) := hx187.1
      linarith
  let x188 : ℝ := (1 / 1)+y
  have hx188 : Bounds (1318009 / 1000000) (329609 / 250000) x188 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hy <;> norm_num
  let x189 : ℝ := -y
  have hx189 : Bounds (-79609 / 250000) (-318009 / 1000000) x189 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hy
  let x190 : ℝ := (1 / 1)+x189
  have hx190 : Bounds (170391 / 250000) (681991 / 1000000) x190 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx189 <;> norm_num
  let x191 : ℝ := (1 / 1)-y
  have hx191 : Bounds (170391 / 250000) (681991 / 1000000) x191 := by
    exact hx190
  let x192 : ℝ := x191⁻¹
  have hx192 : Bounds (733147504879 / 500000000000) (733606821957 / 500000000000) x192 := by
    apply bounds_inv hx191 <;> norm_num
  let x193 : ℝ := x188*x192
  have hx193 : Bounds (483147504879 / 250000000000) (483606821957 / 250000000000) x193 := by
    apply bounds_mul hx188 hx192 <;> norm_num
  let x194 : ℝ := x188/x191
  have hx194 : Bounds (483147504879 / 250000000000) (483606821957 / 250000000000) x194 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx193
  let x195 : ℝ := Real.log x194
  have hx195 : Bounds (329430541 / 500000000) (164952827 / 250000000) x195 := by
    exact bounds_log hx194 (by norm_num) (by simpa only [div_one] using reflection_log_17.1) (by simpa only [div_one] using reflection_log_18.2)
  let x196 : ℝ := (2 / 1)⁻¹
  have hx196 : Bounds (1 / 2) (1 / 2) x196 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x197 : ℝ := x195*x196
  have hx197 : Bounds (329430541 / 1000000000) (164952827 / 500000000) x197 := by
    apply bounds_mul hx195 hx196 <;> norm_num
  let x198 : ℝ := x195/(2 / 1)
  have hx198 : Bounds (329430541 / 1000000000) (164952827 / 500000000) x198 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx197
  let x199 : ℝ := (1 / 1)+c
  have hx199 : Bounds (615671 / 500000) (1231671 / 1000000) x199 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hc <;> norm_num
  let x200 : ℝ := -c
  have hx200 : Bounds (-231671 / 1000000) (-115671 / 500000) x200 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hc
  let x201 : ℝ := (1 / 1)+x200
  have hx201 : Bounds (768329 / 1000000) (384329 / 500000) x201 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx200 <;> norm_num
  let x202 : ℝ := (1 / 1)-c
  have hx202 : Bounds (768329 / 1000000) (384329 / 500000) x202 := by
    exact hx201
  let x203 : ℝ := x202⁻¹
  have hx203 : Bounds (650484350647 / 500000000000) (1301525778671 / 1000000000000) x203 := by
    apply bounds_inv hx202 <;> norm_num
  let x204 : ℝ := x199*x203
  have hx204 : Bounds (400484350647 / 250000000000) (801525778671 / 500000000000) x204 := by
    apply bounds_mul hx199 hx203 <;> norm_num
  let x205 : ℝ := x199/x202
  have hx205 : Bounds (400484350647 / 250000000000) (801525778671 / 500000000000) x205 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx204
  let x206 : ℝ := Real.log x205
  have hx206 : Bounds (471213773 / 1000000000) (471909037 / 1000000000) x206 := by
    exact bounds_log hx205 (by norm_num) (by simpa only [div_one] using reflection_log_19.1) (by simpa only [div_one] using reflection_log_20.2)
  let x207 : ℝ := (2 / 1)⁻¹
  have hx207 : Bounds (1 / 2) (1 / 2) x207 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x208 : ℝ := x206*x207
  have hx208 : Bounds (471213773 / 2000000000) (471909037 / 2000000000) x208 := by
    apply bounds_mul hx206 hx207 <;> norm_num
  let x209 : ℝ := x206/(2 / 1)
  have hx209 : Bounds (471213773 / 2000000000) (471909037 / 2000000000) x209 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx208
  let x210 : ℝ := (2 / 1)*x50
  have hx210 : Bounds (668039593927 / 500000000000) (668106044129 / 500000000000) x210 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx50 <;> norm_num
  let x211 : ℝ := (2 / 1)*x98
  have hx211 : Bounds (641553013431 / 500000000000) (641693549571 / 500000000000) x211 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx98 <;> norm_num
  let x212 : ℝ := -x211
  have hx212 : Bounds (-641693549571 / 500000000000) (-641553013431 / 500000000000) x212 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx211
  let x213 : ℝ := x210+x212
  have hx213 : Bounds (6586511089 / 125000000000) (13276515349 / 250000000000) x213 := by
    apply bounds_add hx210 hx212 <;> norm_num
  let x214 : ℝ := x210-x211
  have hx214 : Bounds (6586511089 / 125000000000) (13276515349 / 250000000000) x214 := by
    exact hx213
  let x215 : ℝ := y*x198
  have hx215 : Bounds (6547617307 / 62500000000) (52526918419 / 500000000000) x215 := by
    apply bounds_mul hy hx198 <;> norm_num
  let x216 : ℝ := -x215
  have hx216 : Bounds (-52526918419 / 500000000000) (-6547617307 / 62500000000) x216 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx215
  let x217 : ℝ := x214+x216
  have hx217 : Bounds (-26180874063 / 500000000000) (-12913953879 / 250000000000) x217 := by
    apply bounds_add hx214 hx216 <;> norm_num
  let x218 : ℝ := x214-x215
  have hx218 : Bounds (-26180874063 / 500000000000) (-12913953879 / 250000000000) x218 := by
    exact hx217
  let x219 : ℝ := x3*x209
  have hx219 : Bounds (6563170349 / 125000000000) (13162990107 / 250000000000) x219 := by
    apply bounds_mul hx3 hx209 <;> norm_num
  let x220 : ℝ := x218+x219
  have hx220 : Bounds (71807333 / 500000000000) (62259057 / 62500000000) x220 := by
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

theorem acceptedCertificate : DoubleCapBiasCellCertificate (1591 / 4096) (3979 / 10240) (fun m => (1 + H (2*m - 1/2))/2) where
  domain := by norm_num
  sound m hmLo hmHi := by
    exact cell_bias_nonneg m ⟨hmLo, hmHi⟩

theorem accepted_cell :
    ∀ m, (1591 / 4096) ≤ m → m ≤ (3979 / 10240) → 0 ≤ doubleCapHighResidual m := by
  intro m hmLo hmHi
  unfold doubleCapHighResidual
  apply doubleCapEndpointResidual_nonneg_of_biasCell acceptedCertificate hmLo hmHi
  exact div_pos (by linarith [H_nonneg (by linarith : 0 ≤ 2*m-1/2) (by linarith : 2*m-1/2 ≤ 1)]) two_pos

#print axioms cell_bias_nonneg
#print axioms accepted_cell

end GeneralCK.Certificates.DoubleCapMiddle.Cell0395

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0396 =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0396
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Reflection
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem cell_bias_nonneg (m : ℝ) (hm : Bounds (3979 / 10240) (7961 / 20480) m) :
    let h := (1 + H (2*m - 1/2))/2
    let x := 1-2*m
    let y := 1-2*entropyInverse h
    let c := regularContact (x/(Real.log 2*h))
    0 ≤ 2*(biasE x-Real.log 2*h)-y*SmallMean.A y+x*SmallMean.A c := by
  have hEq : biasE (2-4*m) = Real.log 2 * H (2*m-1/2) := by
    have hmstrict : 1/4 < m := by
      have hlo : (1/4 : ℝ) < (3979 / 10240) := by norm_num
      exact lt_of_lt_of_le hlo hm.1
    rw [show 2-4*m = 1-2*(2*m-1/2) by ring,
      GeneralCK.Correction.Natural.biasE_probability (by linarith [hmstrict]) (by linarith [hm.2]),
      GeneralCK.Certificates.Mixed.hn_eq_H_mul_log]
    ring
  have hLh : Real.log 2 * ((1 + H (2*m - 1/2))/2) = (Real.log 2 + biasE (2-4*m))/2 := by
    rw [hEq]
    ring
  let x0 : ℝ := (2 / 1)*m
  have hx0 : Bounds (3979 / 5120) (7961 / 10240) x0 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hm <;> norm_num
  let x1 : ℝ := -x0
  have hx1 : Bounds (-7961 / 10240) (-3979 / 5120) x1 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx0
  let x2 : ℝ := (1 / 1)+x1
  have hx2 : Bounds (2279 / 10240) (1141 / 5120) x2 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx1 <;> norm_num
  let x3 : ℝ := (1 / 1)-x0
  have hx3 : Bounds (2279 / 10240) (1141 / 5120) x3 := by
    exact hx2
  let x4 : ℝ := (4 / 1)*m
  have hx4 : Bounds (3979 / 2560) (7961 / 5120) x4 := by
    apply bounds_mul (bounds_const ((4 / 1) : ℝ)) hm <;> norm_num
  let x5 : ℝ := -x4
  have hx5 : Bounds (-7961 / 5120) (-3979 / 2560) x5 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx4
  let x6 : ℝ := (2 / 1)+x5
  have hx6 : Bounds (2279 / 5120) (1141 / 2560) x6 := by
    apply bounds_add (bounds_const ((2 / 1) : ℝ)) hx5 <;> norm_num
  let x7 : ℝ := (2 / 1)-x4
  have hx7 : Bounds (2279 / 5120) (1141 / 2560) x7 := by
    exact hx6
  let x8 : ℝ := Real.log (2 / 1)
  have hx8 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x8 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x9 : ℝ := (1 / 1)+(1141 / 5120)
  have hx9 : Bounds (6261 / 5120) (6261 / 5120) x9 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1141 / 5120) : ℝ)) <;> norm_num
  let x10 : ℝ := (1 / 1)+(1141 / 5120)
  have hx10 : Bounds (6261 / 5120) (6261 / 5120) x10 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1141 / 5120) : ℝ)) <;> norm_num
  let x11 : ℝ := Real.log x10
  have hx11 : Bounds (201185477 / 1000000000) (100592739 / 500000000) x11 := by
    exact bounds_log hx10 (by norm_num) (by simpa only [div_one] using reflection_log_1.1) (by simpa only [div_one] using reflection_log_1.2)
  let x12 : ℝ := x9*x11
  have hx12 : Bounds (246019974901 / 1000000000000) (1968159809 / 8000000000) x12 := by
    apply bounds_mul hx9 hx11 <;> norm_num
  let x13 : ℝ := -(1141 / 5120)
  have hx13 : Bounds (-1141 / 5120) (-1141 / 5120) x13 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1141 / 5120) : ℝ))
  let x14 : ℝ := (1 / 1)+x13
  have hx14 : Bounds (3979 / 5120) (3979 / 5120) x14 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx13 <;> norm_num
  let x15 : ℝ := (1 / 1)-(1141 / 5120)
  have hx15 : Bounds (3979 / 5120) (3979 / 5120) x15 := by
    exact hx14
  let x16 : ℝ := -(1141 / 5120)
  have hx16 : Bounds (-1141 / 5120) (-1141 / 5120) x16 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1141 / 5120) : ℝ))
  let x17 : ℝ := (1 / 1)+x16
  have hx17 : Bounds (3979 / 5120) (3979 / 5120) x17 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx16 <;> norm_num
  let x18 : ℝ := (1 / 1)-(1141 / 5120)
  have hx18 : Bounds (3979 / 5120) (3979 / 5120) x18 := by
    exact hx17
  let x19 : ℝ := Real.log x18
  have hx19 : Bounds (-63030977 / 250000000) (-252123907 / 1000000000) x19 := by
    exact bounds_log hx18 (by norm_num) (by simpa only [div_one] using reflection_log_2.1) (by simpa only [div_one] using reflection_log_2.2)
  let x20 : ℝ := x15*x19
  have hx20 : Bounds (-195937701159 / 1000000000000) (-195937700381 / 1000000000000) x20 := by
    apply bounds_mul hx15 hx19 <;> norm_num
  let x21 : ℝ := x12+x20
  have hx21 : Bounds (25041136871 / 500000000000) (1565071117 / 31250000000) x21 := by
    apply bounds_add hx12 hx20 <;> norm_num
  let x22 : ℝ := (2 / 1)⁻¹
  have hx22 : Bounds (1 / 2) (1 / 2) x22 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x23 : ℝ := x21*x22
  have hx23 : Bounds (25041136871 / 1000000000000) (1565071117 / 62500000000) x23 := by
    apply bounds_mul hx21 hx22 <;> norm_num
  let x24 : ℝ := x21/(2 / 1)
  have hx24 : Bounds (25041136871 / 1000000000000) (1565071117 / 62500000000) x24 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx23
  let x25 : ℝ := -x24
  have hx25 : Bounds (-1565071117 / 62500000000) (-25041136871 / 1000000000000) x25 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx24
  let x26 : ℝ := x8+x25
  have hx26 : Bounds (41756627633 / 62500000000) (668106044129 / 1000000000000) x26 := by
    apply bounds_add hx8 hx25 <;> norm_num
  let x27 : ℝ := x8-x24
  have hx27 : Bounds (41756627633 / 62500000000) (668106044129 / 1000000000000) x27 := by
    exact hx26
  let x28 : ℝ := biasE (1141 / 5120)
  have hx28 : Bounds (41756627633 / 62500000000) (668106044129 / 1000000000000) x28 := by
    simpa +zetaDelta only [biasE, div_one] using hx27
  let x29 : ℝ := Real.log (2 / 1)
  have hx29 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x29 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x30 : ℝ := (1 / 1)+(2279 / 10240)
  have hx30 : Bounds (12519 / 10240) (12519 / 10240) x30 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((2279 / 10240) : ℝ)) <;> norm_num
  let x31 : ℝ := (1 / 1)+(2279 / 10240)
  have hx31 : Bounds (12519 / 10240) (12519 / 10240) x31 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((2279 / 10240) : ℝ)) <;> norm_num
  let x32 : ℝ := Real.log x31
  have hx32 : Bounds (20094587 / 100000000) (200945871 / 1000000000) x32 := by
    exact bounds_log hx31 (by norm_num) (by simpa only [div_one] using reflection_log_3.1) (by simpa only [div_one] using reflection_log_3.2)
  let x33 : ℝ := x30*x32
  have hx33 : Bounds (245668100247 / 1000000000000) (24566810147 / 100000000000) x33 := by
    apply bounds_mul hx30 hx32 <;> norm_num
  let x34 : ℝ := -(2279 / 10240)
  have hx34 : Bounds (-2279 / 10240) (-2279 / 10240) x34 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((2279 / 10240) : ℝ))
  let x35 : ℝ := (1 / 1)+x34
  have hx35 : Bounds (7961 / 10240) (7961 / 10240) x35 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx34 <;> norm_num
  let x36 : ℝ := (1 / 1)-(2279 / 10240)
  have hx36 : Bounds (7961 / 10240) (7961 / 10240) x36 := by
    exact hx35
  let x37 : ℝ := -(2279 / 10240)
  have hx37 : Bounds (-2279 / 10240) (-2279 / 10240) x37 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((2279 / 10240) : ℝ))
  let x38 : ℝ := (1 / 1)+x37
  have hx38 : Bounds (7961 / 10240) (7961 / 10240) x38 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx37 <;> norm_num
  let x39 : ℝ := (1 / 1)-(2279 / 10240)
  have hx39 : Bounds (7961 / 10240) (7961 / 10240) x39 := by
    exact hx38
  let x40 : ℝ := Real.log x39
  have hx40 : Bounds (-251747 / 1000000) (-251746999 / 1000000000) x40 := by
    exact bounds_log hx39 (by norm_num) (by simpa only [div_one] using reflection_log_4.1) (by simpa only [div_one] using reflection_log_4.2)
  let x41 : ℝ := x36*x40
  have hx41 : Bounds (-1957185417 / 10000000000) (-195718540921 / 1000000000000) x41 := by
    apply bounds_mul hx36 hx40 <;> norm_num
  let x42 : ℝ := x33+x41
  have hx42 : Bounds (49949558547 / 1000000000000) (49949560549 / 1000000000000) x42 := by
    apply bounds_add hx33 hx41 <;> norm_num
  let x43 : ℝ := (2 / 1)⁻¹
  have hx43 : Bounds (1 / 2) (1 / 2) x43 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x44 : ℝ := x42*x43
  have hx44 : Bounds (24974779273 / 1000000000000) (998991211 / 40000000000) x44 := by
    apply bounds_mul hx42 hx43 <;> norm_num
  let x45 : ℝ := x42/(2 / 1)
  have hx45 : Bounds (24974779273 / 1000000000000) (998991211 / 40000000000) x45 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx44
  let x46 : ℝ := -x45
  have hx46 : Bounds (-998991211 / 40000000000) (-24974779273 / 1000000000000) x46 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx45
  let x47 : ℝ := x29+x46
  have hx47 : Bounds (26726895989 / 40000000000) (668172401727 / 1000000000000) x47 := by
    apply bounds_add hx29 hx46 <;> norm_num
  let x48 : ℝ := x29-x45
  have hx48 : Bounds (26726895989 / 40000000000) (668172401727 / 1000000000000) x48 := by
    exact hx47
  let x49 : ℝ := biasE (2279 / 10240)
  have hx49 : Bounds (26726895989 / 40000000000) (668172401727 / 1000000000000) x49 := by
    simpa +zetaDelta only [biasE, div_one] using hx48
  let x50 : ℝ := biasE x3
  have hx50 : Bounds (41756627633 / 62500000000) (668172401727 / 1000000000000) x50 := by
    exact bounds_biasE hx3 (by norm_num) (by norm_num) hx28.1 hx49.2
  let x51 : ℝ := Real.log (2 / 1)
  have hx51 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x51 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x52 : ℝ := (1 / 1)+(1141 / 2560)
  have hx52 : Bounds (3701 / 2560) (3701 / 2560) x52 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1141 / 2560) : ℝ)) <;> norm_num
  let x53 : ℝ := (1 / 1)+(1141 / 2560)
  have hx53 : Bounds (3701 / 2560) (3701 / 2560) x53 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1141 / 2560) : ℝ)) <;> norm_num
  let x54 : ℝ := Real.log x53
  have hx54 : Bounds (184297897 / 500000000) (73719159 / 200000000) x54 := by
    exact bounds_log hx53 (by norm_num) (by simpa only [div_one] using reflection_log_5.1) (by simpa only [div_one] using reflection_log_5.2)
  let x55 : ℝ := x52*x54
  have hx55 : Bounds (532880091247 / 1000000000000) (266440046347 / 500000000000) x55 := by
    apply bounds_mul hx52 hx54 <;> norm_num
  let x56 : ℝ := -(1141 / 2560)
  have hx56 : Bounds (-1141 / 2560) (-1141 / 2560) x56 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1141 / 2560) : ℝ))
  let x57 : ℝ := (1 / 1)+x56
  have hx57 : Bounds (1419 / 2560) (1419 / 2560) x57 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx56 <;> norm_num
  let x58 : ℝ := (1 / 1)-(1141 / 2560)
  have hx58 : Bounds (1419 / 2560) (1419 / 2560) x58 := by
    exact hx57
  let x59 : ℝ := -(1141 / 2560)
  have hx59 : Bounds (-1141 / 2560) (-1141 / 2560) x59 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1141 / 2560) : ℝ))
  let x60 : ℝ := (1 / 1)+x59
  have hx60 : Bounds (1419 / 2560) (1419 / 2560) x60 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx59 <;> norm_num
  let x61 : ℝ := (1 / 1)-(1141 / 2560)
  have hx61 : Bounds (1419 / 2560) (1419 / 2560) x61 := by
    exact hx60
  let x62 : ℝ := Real.log x61
  have hx62 : Bounds (-590054861 / 1000000000) (-29502743 / 50000000) x62 := by
    exact bounds_log hx61 (by norm_num) (by simpa only [div_one] using reflection_log_6.1) (by simpa only [div_one] using reflection_log_6.2)
  let x63 : ℝ := x58*x62
  have hx63 : Bounds (-327065565531 / 1000000000000) (-20441597811 / 62500000000) x63 := by
    apply bounds_mul hx58 hx62 <;> norm_num
  let x64 : ℝ := x55+x63
  have hx64 : Bounds (51453631429 / 250000000000) (102907263859 / 500000000000) x64 := by
    apply bounds_add hx55 hx63 <;> norm_num
  let x65 : ℝ := (2 / 1)⁻¹
  have hx65 : Bounds (1 / 2) (1 / 2) x65 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x66 : ℝ := x64*x65
  have hx66 : Bounds (51453631429 / 500000000000) (102907263859 / 1000000000000) x66 := by
    apply bounds_mul hx64 hx65 <;> norm_num
  let x67 : ℝ := x64/(2 / 1)
  have hx67 : Bounds (51453631429 / 500000000000) (102907263859 / 1000000000000) x67 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx66
  let x68 : ℝ := -x67
  have hx68 : Bounds (-102907263859 / 1000000000000) (-51453631429 / 500000000000) x68 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx67
  let x69 : ℝ := x51+x68
  have hx69 : Bounds (590239916141 / 1000000000000) (295119959071 / 500000000000) x69 := by
    apply bounds_add hx51 hx68 <;> norm_num
  let x70 : ℝ := x51-x67
  have hx70 : Bounds (590239916141 / 1000000000000) (295119959071 / 500000000000) x70 := by
    exact hx69
  let x71 : ℝ := biasE (1141 / 2560)
  have hx71 : Bounds (590239916141 / 1000000000000) (295119959071 / 500000000000) x71 := by
    simpa +zetaDelta only [biasE, div_one] using hx70
  let x72 : ℝ := Real.log (2 / 1)
  have hx72 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x72 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x73 : ℝ := (1 / 1)+(2279 / 5120)
  have hx73 : Bounds (7399 / 5120) (7399 / 5120) x73 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((2279 / 5120) : ℝ)) <;> norm_num
  let x74 : ℝ := (1 / 1)+(2279 / 5120)
  have hx74 : Bounds (7399 / 5120) (7399 / 5120) x74 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((2279 / 5120) : ℝ)) <;> norm_num
  let x75 : ℝ := Real.log x74
  have hx75 : Bounds (23011901 / 62500000) (368190417 / 1000000000) x75 := by
    exact bounds_log hx74 (by norm_num) (by simpa only [div_one] using reflection_log_7.1) (by simpa only [div_one] using reflection_log_7.2)
  let x76 : ℝ := x73*x75
  have hx76 : Bounds (266039149217 / 500000000000) (13301957497 / 25000000000) x76 := by
    apply bounds_mul hx73 hx75 <;> norm_num
  let x77 : ℝ := -(2279 / 5120)
  have hx77 : Bounds (-2279 / 5120) (-2279 / 5120) x77 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((2279 / 5120) : ℝ))
  let x78 : ℝ := (1 / 1)+x77
  have hx78 : Bounds (2841 / 5120) (2841 / 5120) x78 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx77 <;> norm_num
  let x79 : ℝ := (1 / 1)-(2279 / 5120)
  have hx79 : Bounds (2841 / 5120) (2841 / 5120) x79 := by
    exact hx78
  let x80 : ℝ := -(2279 / 5120)
  have hx80 : Bounds (-2279 / 5120) (-2279 / 5120) x80 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((2279 / 5120) : ℝ))
  let x81 : ℝ := (1 / 1)+x80
  have hx81 : Bounds (2841 / 5120) (2841 / 5120) x81 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx80 <;> norm_num
  let x82 : ℝ := (1 / 1)-(2279 / 5120)
  have hx82 : Bounds (2841 / 5120) (2841 / 5120) x82 := by
    exact hx81
  let x83 : ℝ := Real.log x82
  have hx83 : Bounds (-588998337 / 1000000000) (-9203099 / 15625000) x83 := by
    exact bounds_log hx82 (by norm_num) (by simpa only [div_one] using reflection_log_8.1) (by simpa only [div_one] using reflection_log_8.2)
  let x84 : ℝ := x79*x83
  have hx84 : Bounds (-326825053793 / 1000000000000) (-326825053237 / 1000000000000) x84 := by
    apply bounds_mul hx79 hx83 <;> norm_num
  let x85 : ℝ := x76+x84
  have hx85 : Bounds (205253244641 / 1000000000000) (205253246643 / 1000000000000) x85 := by
    apply bounds_add hx76 hx84 <;> norm_num
  let x86 : ℝ := (2 / 1)⁻¹
  have hx86 : Bounds (1 / 2) (1 / 2) x86 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x87 : ℝ := x85*x86
  have hx87 : Bounds (1282832779 / 12500000000) (51313311661 / 500000000000) x87 := by
    apply bounds_mul hx85 hx86 <;> norm_num
  let x88 : ℝ := x85/(2 / 1)
  have hx88 : Bounds (1282832779 / 12500000000) (51313311661 / 500000000000) x88 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx87
  let x89 : ℝ := -x88
  have hx89 : Bounds (-51313311661 / 500000000000) (-1282832779 / 12500000000) x89 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx88
  let x90 : ℝ := x72+x89
  have hx90 : Bounds (295260278339 / 500000000000) (14763013967 / 25000000000) x90 := by
    apply bounds_add hx72 hx89 <;> norm_num
  let x91 : ℝ := x72-x88
  have hx91 : Bounds (295260278339 / 500000000000) (14763013967 / 25000000000) x91 := by
    exact hx90
  let x92 : ℝ := biasE (2279 / 5120)
  have hx92 : Bounds (295260278339 / 500000000000) (14763013967 / 25000000000) x92 := by
    simpa +zetaDelta only [biasE, div_one] using hx91
  let x93 : ℝ := biasE x7
  have hx93 : Bounds (590239916141 / 1000000000000) (14763013967 / 25000000000) x93 := by
    exact bounds_biasE hx7 (by norm_num) (by norm_num) hx71.1 hx92.2
  let x94 : ℝ := Real.log (2 / 1)
  have hx94 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x94 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x95 : ℝ := x94+x93
  have hx95 : Bounds (1283387096141 / 1000000000000) (8022923373 / 6250000000) x95 := by
    apply bounds_add hx94 hx93 <;> norm_num
  let x96 : ℝ := (2 / 1)⁻¹
  have hx96 : Bounds (1 / 2) (1 / 2) x96 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x97 : ℝ := x95*x96
  have hx97 : Bounds (64169354807 / 100000000000) (8022923373 / 12500000000) x97 := by
    apply bounds_mul hx95 hx96 <;> norm_num
  let x98 : ℝ := x95/(2 / 1)
  have hx98 : Bounds (64169354807 / 100000000000) (8022923373 / 12500000000) x98 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx97
  let x99 : ℝ := Real.log (2 / 1)
  have hx99 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x99 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x100 : ℝ := (1 / 1)+(158791 / 500000)
  have hx100 : Bounds (658791 / 500000) (658791 / 500000) x100 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((158791 / 500000) : ℝ)) <;> norm_num
  let x101 : ℝ := (1 / 1)+(158791 / 500000)
  have hx101 : Bounds (658791 / 500000) (658791 / 500000) x101 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((158791 / 500000) : ℝ)) <;> norm_num
  let x102 : ℝ := Real.log x101
  have hx102 : Bounds (137899119 / 500000000) (275798239 / 1000000000) x102 := by
    exact bounds_log hx101 (by norm_num) (by simpa only [div_one] using reflection_log_9.1) (by simpa only [div_one] using reflection_log_9.2)
  let x103 : ℝ := x100*x102
  have hx103 : Bounds (18169339701 / 50000000000) (363386795339 / 1000000000000) x103 := by
    apply bounds_mul hx100 hx102 <;> norm_num
  let x104 : ℝ := -(158791 / 500000)
  have hx104 : Bounds (-158791 / 500000) (-158791 / 500000) x104 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((158791 / 500000) : ℝ))
  let x105 : ℝ := (1 / 1)+x104
  have hx105 : Bounds (341209 / 500000) (341209 / 500000) x105 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx104 <;> norm_num
  let x106 : ℝ := (1 / 1)-(158791 / 500000)
  have hx106 : Bounds (341209 / 500000) (341209 / 500000) x106 := by
    exact hx105
  let x107 : ℝ := -(158791 / 500000)
  have hx107 : Bounds (-158791 / 500000) (-158791 / 500000) x107 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((158791 / 500000) : ℝ))
  let x108 : ℝ := (1 / 1)+x107
  have hx108 : Bounds (341209 / 500000) (341209 / 500000) x108 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx107 <;> norm_num
  let x109 : ℝ := (1 / 1)-(158791 / 500000)
  have hx109 : Bounds (341209 / 500000) (341209 / 500000) x109 := by
    exact hx108
  let x110 : ℝ := Real.log x109
  have hx110 : Bounds (-191056453 / 500000000) (-76422581 / 200000000) x110 := by
    exact bounds_log hx109 (by norm_num) (by simpa only [div_one] using reflection_log_10.1) (by simpa only [div_one] using reflection_log_10.2)
  let x111 : ℝ := x106*x110
  have hx111 : Bounds (-260760725087 / 1000000000000) (-65190181101 / 250000000000) x111 := by
    apply bounds_mul hx106 hx110 <;> norm_num
  let x112 : ℝ := x103+x111
  have hx112 : Bounds (102626068933 / 1000000000000) (20525214187 / 200000000000) x112 := by
    apply bounds_add hx103 hx111 <;> norm_num
  let x113 : ℝ := (2 / 1)⁻¹
  have hx113 : Bounds (1 / 2) (1 / 2) x113 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x114 : ℝ := x112*x113
  have hx114 : Bounds (25656517233 / 500000000000) (12828258867 / 250000000000) x114 := by
    apply bounds_mul hx112 hx113 <;> norm_num
  let x115 : ℝ := x112/(2 / 1)
  have hx115 : Bounds (25656517233 / 500000000000) (12828258867 / 250000000000) x115 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx114
  let x116 : ℝ := -x115
  have hx116 : Bounds (-12828258867 / 250000000000) (-25656517233 / 500000000000) x116 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx115
  let x117 : ℝ := x99+x116
  have hx117 : Bounds (160458536133 / 250000000000) (320917073267 / 500000000000) x117 := by
    apply bounds_add hx99 hx116 <;> norm_num
  let x118 : ℝ := x99-x115
  have hx118 : Bounds (160458536133 / 250000000000) (320917073267 / 500000000000) x118 := by
    exact hx117
  let x119 : ℝ := biasE (158791 / 500000)
  have hx119 : Bounds (160458536133 / 250000000000) (320917073267 / 500000000000) x119 := by
    simpa +zetaDelta only [biasE, div_one] using hx118
  let x120 : ℝ := Real.log (2 / 1)
  have hx120 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x120 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x121 : ℝ := (1 / 1)+(31801 / 100000)
  have hx121 : Bounds (131801 / 100000) (131801 / 100000) x121 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((31801 / 100000) : ℝ)) <;> norm_num
  let x122 : ℝ := (1 / 1)+(31801 / 100000)
  have hx122 : Bounds (131801 / 100000) (131801 / 100000) x122 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((31801 / 100000) : ℝ)) <;> norm_num
  let x123 : ℝ := Real.log x122
  have hx123 : Bounds (276123023 / 1000000000) (17257689 / 62500000) x123 := by
    exact bounds_log hx122 (by norm_num) (by simpa only [div_one] using reflection_log_11.1) (by simpa only [div_one] using reflection_log_11.2)
  let x124 : ℝ := x121*x123
  have hx124 : Bounds (45491613193 / 125000000000) (363932906863 / 1000000000000) x124 := by
    apply bounds_mul hx121 hx123 <;> norm_num
  let x125 : ℝ := -(31801 / 100000)
  have hx125 : Bounds (-31801 / 100000) (-31801 / 100000) x125 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((31801 / 100000) : ℝ))
  let x126 : ℝ := (1 / 1)+x125
  have hx126 : Bounds (68199 / 100000) (68199 / 100000) x126 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx125 <;> norm_num
  let x127 : ℝ := (1 / 1)-(31801 / 100000)
  have hx127 : Bounds (68199 / 100000) (68199 / 100000) x127 := by
    exact hx126
  let x128 : ℝ := -(31801 / 100000)
  have hx128 : Bounds (-31801 / 100000) (-31801 / 100000) x128 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((31801 / 100000) : ℝ))
  let x129 : ℝ := (1 / 1)+x128
  have hx129 : Bounds (68199 / 100000) (68199 / 100000) x129 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx128 <;> norm_num
  let x130 : ℝ := (1 / 1)-(31801 / 100000)
  have hx130 : Bounds (68199 / 100000) (68199 / 100000) x130 := by
    exact hx129
  let x131 : ℝ := Real.log x130
  have hx131 : Bounds (-76548057 / 200000000) (-95685071 / 250000000) x131 := by
    exact bounds_log hx130 (by norm_num) (by simpa only [div_one] using reflection_log_12.1) (by simpa only [div_one] using reflection_log_12.2)
  let x132 : ℝ := x127*x131
  have hx132 : Bounds (-32628130871 / 125000000000) (-52205009257 / 200000000000) x132 := by
    apply bounds_mul hx127 hx131 <;> norm_num
  let x133 : ℝ := x124+x132
  have hx133 : Bounds (6431741161 / 62500000000) (51453930289 / 500000000000) x133 := by
    apply bounds_add hx124 hx132 <;> norm_num
  let x134 : ℝ := (2 / 1)⁻¹
  have hx134 : Bounds (1 / 2) (1 / 2) x134 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x135 : ℝ := x133*x134
  have hx135 : Bounds (6431741161 / 125000000000) (51453930289 / 1000000000000) x135 := by
    apply bounds_mul hx133 hx134 <;> norm_num
  let x136 : ℝ := x133/(2 / 1)
  have hx136 : Bounds (6431741161 / 125000000000) (51453930289 / 1000000000000) x136 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx135
  let x137 : ℝ := -x136
  have hx137 : Bounds (-51453930289 / 1000000000000) (-6431741161 / 125000000000) x137 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx136
  let x138 : ℝ := x120+x137
  have hx138 : Bounds (641693249711 / 1000000000000) (5013228529 / 7812500000) x138 := by
    apply bounds_add hx120 hx137 <;> norm_num
  let x139 : ℝ := x120-x136
  have hx139 : Bounds (641693249711 / 1000000000000) (5013228529 / 7812500000) x139 := by
    exact hx138
  let x140 : ℝ := biasE (31801 / 100000)
  have hx140 : Bounds (641693249711 / 1000000000000) (5013228529 / 7812500000) x140 := by
    simpa +zetaDelta only [biasE, div_one] using hx139
  let y : ℝ := 1 - 2 * entropyInverse ((1 + H (2*m - 1/2))/2)
  have hLh' : Real.log 2 * ((1 + H (2*m - 1/2))/2) = x98 := by
    simpa +zetaDelta only [div_one] using hLh
  have hy : Bounds (158791 / 500000) (31801 / 100000) y := by
    apply entropyInverseBias_bracket
    · exact div_nonneg (add_nonneg zero_le_one
        (H_nonneg (by linarith [hm.1]) (by linarith [hm.2]))) two_pos.le
    · linarith [H_le_one (2*m-1/2)]
    · norm_num
    · norm_num
    · norm_num
    · have h1 : biasE (31801 / 100000) ≤ (5013228529 / 7812500000) := hx140.2
      have h2 : (64169354807 / 100000000000) ≤ x98 := hx98.1
      linarith [hLh']
    · have h1 : x98 ≤ (8022923373 / 12500000000) := hx98.2
      have h2 : (160458536133 / 250000000000) ≤ biasE (158791 / 500000) := hx119.1
      linarith [hLh']
  let x141 : ℝ := x3⁻¹
  have hx141 : Bounds (897458369851 / 200000000000) (4493198771391 / 1000000000000) x141 := by
    apply bounds_inv hx3 <;> norm_num
  let x142 : ℝ := x98*x141
  have hx142 : Bounds (1439733113987 / 500000000000) (2883887155403 / 1000000000000) x142 := by
    apply bounds_mul hx98 hx141 <;> norm_num
  let x143 : ℝ := x98/x3
  have hx143 : Bounds (1439733113987 / 500000000000) (2883887155403 / 1000000000000) x143 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx142
  let x144 : ℝ := Real.log (2 / 1)
  have hx144 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x144 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x145 : ℝ := (1 / 1)+(115507 / 500000)
  have hx145 : Bounds (615507 / 500000) (615507 / 500000) x145 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((115507 / 500000) : ℝ)) <;> norm_num
  let x146 : ℝ := (1 / 1)+(115507 / 500000)
  have hx146 : Bounds (615507 / 500000) (615507 / 500000) x146 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((115507 / 500000) : ℝ)) <;> norm_num
  let x147 : ℝ := Real.log x146
  have hx147 : Bounds (10391911 / 50000000) (207838221 / 1000000000) x147 := by
    exact bounds_log hx146 (by norm_num) (by simpa only [div_one] using reflection_log_13.1) (by simpa only [div_one] using reflection_log_13.2)
  let x148 : ℝ := x145*x147
  have hx148 : Bounds (51170351711 / 200000000000) (255851759787 / 1000000000000) x148 := by
    apply bounds_mul hx145 hx147 <;> norm_num
  let x149 : ℝ := -(115507 / 500000)
  have hx149 : Bounds (-115507 / 500000) (-115507 / 500000) x149 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((115507 / 500000) : ℝ))
  let x150 : ℝ := (1 / 1)+x149
  have hx150 : Bounds (384493 / 500000) (384493 / 500000) x150 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx149 <;> norm_num
  let x151 : ℝ := (1 / 1)-(115507 / 500000)
  have hx151 : Bounds (384493 / 500000) (384493 / 500000) x151 := by
    exact hx150
  let x152 : ℝ := -(115507 / 500000)
  have hx152 : Bounds (-115507 / 500000) (-115507 / 500000) x152 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((115507 / 500000) : ℝ))
  let x153 : ℝ := (1 / 1)+x152
  have hx153 : Bounds (384493 / 500000) (384493 / 500000) x153 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx152 <;> norm_num
  let x154 : ℝ := (1 / 1)-(115507 / 500000)
  have hx154 : Bounds (384493 / 500000) (384493 / 500000) x154 := by
    exact hx153
  let x155 : ℝ := Real.log x154
  have hx155 : Bounds (-65670629 / 250000000) (-52536503 / 200000000) x155 := by
    exact bounds_log hx154 (by norm_num) (by simpa only [div_one] using reflection_log_14.1) (by simpa only [div_one] using reflection_log_14.2)
  let x156 : ℝ := x151*x155
  have hx156 : Bounds (-201999177249 / 1000000000000) (-201999176479 / 1000000000000) x156 := by
    apply bounds_mul hx151 hx155 <;> norm_num
  let x157 : ℝ := x148+x156
  have hx157 : Bounds (26926290653 / 500000000000) (13463145827 / 250000000000) x157 := by
    apply bounds_add hx148 hx156 <;> norm_num
  let x158 : ℝ := (2 / 1)⁻¹
  have hx158 : Bounds (1 / 2) (1 / 2) x158 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x159 : ℝ := x157*x158
  have hx159 : Bounds (26926290653 / 1000000000000) (13463145827 / 500000000000) x159 := by
    apply bounds_mul hx157 hx158 <;> norm_num
  let x160 : ℝ := x157/(2 / 1)
  have hx160 : Bounds (26926290653 / 1000000000000) (13463145827 / 500000000000) x160 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx159
  let x161 : ℝ := -x160
  have hx161 : Bounds (-13463145827 / 500000000000) (-26926290653 / 1000000000000) x161 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx160
  let x162 : ℝ := x144+x161
  have hx162 : Bounds (333110444173 / 500000000000) (666220890347 / 1000000000000) x162 := by
    apply bounds_add hx144 hx161 <;> norm_num
  let x163 : ℝ := x144-x160
  have hx163 : Bounds (333110444173 / 500000000000) (666220890347 / 1000000000000) x163 := by
    exact hx162
  let x164 : ℝ := biasE (115507 / 500000)
  have hx164 : Bounds (333110444173 / 500000000000) (666220890347 / 1000000000000) x164 := by
    simpa +zetaDelta only [biasE, div_one] using hx163
  let x165 : ℝ := Real.log (2 / 1)
  have hx165 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x165 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x166 : ℝ := (1 / 1)+(231343 / 1000000)
  have hx166 : Bounds (1231343 / 1000000) (1231343 / 1000000) x166 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((231343 / 1000000) : ℝ)) <;> norm_num
  let x167 : ℝ := (1 / 1)+(231343 / 1000000)
  have hx167 : Bounds (1231343 / 1000000) (1231343 / 1000000) x167 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((231343 / 1000000) : ℝ)) <;> norm_num
  let x168 : ℝ := Real.log x167
  have hx168 : Bounds (208105443 / 1000000000) (52026361 / 250000000) x168 := by
    exact bounds_log hx167 (by norm_num) (by simpa only [div_one] using reflection_log_15.1) (by simpa only [div_one] using reflection_log_15.2)
  let x169 : ℝ := x166*x168
  have hx169 : Bounds (256249180499 / 1000000000000) (64062295433 / 250000000000) x169 := by
    apply bounds_mul hx166 hx168 <;> norm_num
  let x170 : ℝ := -(231343 / 1000000)
  have hx170 : Bounds (-231343 / 1000000) (-231343 / 1000000) x170 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((231343 / 1000000) : ℝ))
  let x171 : ℝ := (1 / 1)+x170
  have hx171 : Bounds (768657 / 1000000) (768657 / 1000000) x171 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx170 <;> norm_num
  let x172 : ℝ := (1 / 1)-(231343 / 1000000)
  have hx172 : Bounds (768657 / 1000000) (768657 / 1000000) x172 := by
    exact hx171
  let x173 : ℝ := -(231343 / 1000000)
  have hx173 : Bounds (-231343 / 1000000) (-231343 / 1000000) x173 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((231343 / 1000000) : ℝ))
  let x174 : ℝ := (1 / 1)+x173
  have hx174 : Bounds (768657 / 1000000) (768657 / 1000000) x174 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx173 <;> norm_num
  let x175 : ℝ := (1 / 1)-(231343 / 1000000)
  have hx175 : Bounds (768657 / 1000000) (768657 / 1000000) x175 := by
    exact hx174
  let x176 : ℝ := Real.log x175
  have hx176 : Bounds (-263110443 / 1000000000) (-131555221 / 500000000) x176 := by
    exact bounds_log hx175 (by norm_num) (by simpa only [div_one] using reflection_log_16.1) (by simpa only [div_one] using reflection_log_16.2)
  let x177 : ℝ := x172*x176
  have hx177 : Bounds (-101120841893 / 500000000000) (-25280210377 / 125000000000) x177 := by
    apply bounds_mul hx172 hx176 <;> norm_num
  let x178 : ℝ := x169+x177
  have hx178 : Bounds (54007496713 / 1000000000000) (13501874679 / 250000000000) x178 := by
    apply bounds_add hx169 hx177 <;> norm_num
  let x179 : ℝ := (2 / 1)⁻¹
  have hx179 : Bounds (1 / 2) (1 / 2) x179 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x180 : ℝ := x178*x179
  have hx180 : Bounds (6750937089 / 250000000000) (13501874679 / 500000000000) x180 := by
    apply bounds_mul hx178 hx179 <;> norm_num
  let x181 : ℝ := x178/(2 / 1)
  have hx181 : Bounds (6750937089 / 250000000000) (13501874679 / 500000000000) x181 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx180
  let x182 : ℝ := -x181
  have hx182 : Bounds (-13501874679 / 500000000000) (-6750937089 / 250000000000) x182 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx181
  let x183 : ℝ := x165+x182
  have hx183 : Bounds (333071715321 / 500000000000) (166535858161 / 250000000000) x183 := by
    apply bounds_add hx165 hx182 <;> norm_num
  let x184 : ℝ := x165-x181
  have hx184 : Bounds (333071715321 / 500000000000) (166535858161 / 250000000000) x184 := by
    exact hx183
  let x185 : ℝ := biasE (231343 / 1000000)
  have hx185 : Bounds (333071715321 / 500000000000) (166535858161 / 250000000000) x185 := by
    simpa +zetaDelta only [biasE, div_one] using hx184
  let x186 : ℝ := x143*(115507 / 500000)
  have hx186 : Bounds (665197011189 / 1000000000000) (666218307319 / 1000000000000) x186 := by
    apply bounds_mul hx143 (bounds_const ((115507 / 500000) : ℝ)) <;> norm_num
  let x187 : ℝ := x143*(231343 / 1000000)
  have hx187 : Bounds (333072177789 / 500000000000) (667167106193 / 1000000000000) x187 := by
    apply bounds_mul hx143 (bounds_const ((231343 / 1000000) : ℝ)) <;> norm_num
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
  have hc : Bounds (115507 / 500000) (231343 / 1000000) c := by
    apply contact_bracket hc0 hcMem.2.le (by norm_num) (by norm_num) (by norm_num)
      (show 0 < x143 by linarith [hx143.1]) hcEq
    · have h1 : x143 * (115507 / 500000) ≤ (666218307319 / 1000000000000) := hx186.2
      have h2 : (333110444173 / 500000000000) ≤ biasE (115507 / 500000) := hx164.1
      linarith
    · have h1 : biasE (231343 / 1000000) ≤ (166535858161 / 250000000000) := hx185.2
      have h2 : (333072177789 / 500000000000) ≤ x143 * (231343 / 1000000) := hx187.1
      linarith
  let x188 : ℝ := (1 / 1)+y
  have hx188 : Bounds (658791 / 500000) (131801 / 100000) x188 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hy <;> norm_num
  let x189 : ℝ := -y
  have hx189 : Bounds (-31801 / 100000) (-158791 / 500000) x189 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hy
  let x190 : ℝ := (1 / 1)+x189
  have hx190 : Bounds (68199 / 100000) (341209 / 500000) x190 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx189 <;> norm_num
  let x191 : ℝ := (1 / 1)-y
  have hx191 : Bounds (68199 / 100000) (341209 / 500000) x191 := by
    exact hx190
  let x192 : ℝ := x191⁻¹
  have hx192 : Bounds (1465377525211 / 1000000000000) (1466297159783 / 1000000000000) x192 := by
    apply bounds_inv hx191 <;> norm_num
  let x193 : ℝ := x188*x192
  have hx193 : Bounds (965377525211 / 500000000000) (966297159783 / 500000000000) x193 := by
    apply bounds_mul hx188 hx192 <;> norm_num
  let x194 : ℝ := x188/x191
  have hx194 : Bounds (965377525211 / 500000000000) (966297159783 / 500000000000) x194 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx193
  let x195 : ℝ := Real.log x194
  have hx195 : Bounds (82238893 / 125000000) (164715827 / 250000000) x195 := by
    exact bounds_log hx194 (by norm_num) (by simpa only [div_one] using reflection_log_17.1) (by simpa only [div_one] using reflection_log_18.2)
  let x196 : ℝ := (2 / 1)⁻¹
  have hx196 : Bounds (1 / 2) (1 / 2) x196 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x197 : ℝ := x195*x196
  have hx197 : Bounds (82238893 / 250000000) (164715827 / 500000000) x197 := by
    apply bounds_mul hx195 hx196 <;> norm_num
  let x198 : ℝ := x195/(2 / 1)
  have hx198 : Bounds (82238893 / 250000000) (164715827 / 500000000) x198 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx197
  let x199 : ℝ := (1 / 1)+c
  have hx199 : Bounds (615507 / 500000) (1231343 / 1000000) x199 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hc <;> norm_num
  let x200 : ℝ := -c
  have hx200 : Bounds (-231343 / 1000000) (-115507 / 500000) x200 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hc
  let x201 : ℝ := (1 / 1)+x200
  have hx201 : Bounds (768657 / 1000000) (384493 / 500000) x201 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx200 <;> norm_num
  let x202 : ℝ := (1 / 1)-c
  have hx202 : Bounds (768657 / 1000000) (384493 / 500000) x202 := by
    exact hx201
  let x203 : ℝ := x202⁻¹
  have hx203 : Bounds (325103447917 / 250000000000) (1300970393817 / 1000000000000) x203 := by
    apply bounds_inv hx202 <;> norm_num
  let x204 : ℝ := x199*x203
  have hx204 : Bounds (200103447917 / 125000000000) (800970393817 / 500000000000) x204 := by
    apply bounds_mul hx199 hx203 <;> norm_num
  let x205 : ℝ := x199/x202
  have hx205 : Bounds (200103447917 / 125000000000) (800970393817 / 500000000000) x205 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx204
  let x206 : ℝ := Real.log x205
  have hx206 : Bounds (94104147 / 200000000) (471215887 / 1000000000) x206 := by
    exact bounds_log hx205 (by norm_num) (by simpa only [div_one] using reflection_log_19.1) (by simpa only [div_one] using reflection_log_20.2)
  let x207 : ℝ := (2 / 1)⁻¹
  have hx207 : Bounds (1 / 2) (1 / 2) x207 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x208 : ℝ := x206*x207
  have hx208 : Bounds (94104147 / 400000000) (471215887 / 2000000000) x208 := by
    apply bounds_mul hx206 hx207 <;> norm_num
  let x209 : ℝ := x206/(2 / 1)
  have hx209 : Bounds (94104147 / 400000000) (471215887 / 2000000000) x209 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx208
  let x210 : ℝ := (2 / 1)*x50
  have hx210 : Bounds (41756627633 / 31250000000) (668172401727 / 500000000000) x210 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx50 <;> norm_num
  let x211 : ℝ := (2 / 1)*x98
  have hx211 : Bounds (64169354807 / 50000000000) (8022923373 / 6250000000) x211 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx98 <;> norm_num
  let x212 : ℝ := -x211
  have hx212 : Bounds (-8022923373 / 6250000000) (-64169354807 / 50000000000) x212 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx211
  let x213 : ℝ := x210+x212
  have hx213 : Bounds (102625673 / 1953125000) (26478853657 / 500000000000) x213 := by
    apply bounds_add hx210 hx212 <;> norm_num
  let x214 : ℝ := x210-x211
  have hx214 : Bounds (102625673 / 1953125000) (26478853657 / 500000000000) x214 := by
    exact hx213
  let x215 : ℝ := y*x198
  have hx215 : Bounds (52235184233 / 500000000000) (104762560289 / 1000000000000) x215 := by
    apply bounds_mul hy hx198 <;> norm_num
  let x216 : ℝ := -x215
  have hx216 : Bounds (-104762560289 / 1000000000000) (-52235184233 / 500000000000) x216 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx215
  let x217 : ℝ := x214+x216
  have hx217 : Bounds (-52218215713 / 1000000000000) (-1609770661 / 31250000000) x217 := by
    apply bounds_add hx214 hx216 <;> norm_num
  let x218 : ℝ := x214-x215
  have hx218 : Bounds (-52218215713 / 1000000000000) (-1609770661 / 31250000000) x218 := by
    exact hx217
  let x219 : ℝ := x3*x209
  have hx219 : Bounds (10471843311 / 200000000000) (52505598347 / 1000000000000) x219 := by
    apply bounds_mul hx3 hx209 <;> norm_num
  let x220 : ℝ := x218+x219
  have hx220 : Bounds (70500421 / 500000000000) (198587439 / 200000000000) x220 := by
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

theorem acceptedCertificate : DoubleCapBiasCellCertificate (3979 / 10240) (7961 / 20480) (fun m => (1 + H (2*m - 1/2))/2) where
  domain := by norm_num
  sound m hmLo hmHi := by
    exact cell_bias_nonneg m ⟨hmLo, hmHi⟩

theorem accepted_cell :
    ∀ m, (3979 / 10240) ≤ m → m ≤ (7961 / 20480) → 0 ≤ doubleCapHighResidual m := by
  intro m hmLo hmHi
  unfold doubleCapHighResidual
  apply doubleCapEndpointResidual_nonneg_of_biasCell acceptedCertificate hmLo hmHi
  exact div_pos (by linarith [H_nonneg (by linarith : 0 ≤ 2*m-1/2) (by linarith : 2*m-1/2 ≤ 1)]) two_pos

#print axioms cell_bias_nonneg
#print axioms accepted_cell

end GeneralCK.Certificates.DoubleCapMiddle.Cell0396

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0397 =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0397
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Reflection
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem cell_bias_nonneg (m : ℝ) (hm : Bounds (7961 / 20480) (1991 / 5120) m) :
    let h := (1 + H (2*m - 1/2))/2
    let x := 1-2*m
    let y := 1-2*entropyInverse h
    let c := regularContact (x/(Real.log 2*h))
    0 ≤ 2*(biasE x-Real.log 2*h)-y*SmallMean.A y+x*SmallMean.A c := by
  have hEq : biasE (2-4*m) = Real.log 2 * H (2*m-1/2) := by
    have hmstrict : 1/4 < m := by
      have hlo : (1/4 : ℝ) < (7961 / 20480) := by norm_num
      exact lt_of_lt_of_le hlo hm.1
    rw [show 2-4*m = 1-2*(2*m-1/2) by ring,
      GeneralCK.Correction.Natural.biasE_probability (by linarith [hmstrict]) (by linarith [hm.2]),
      GeneralCK.Certificates.Mixed.hn_eq_H_mul_log]
    ring
  have hLh : Real.log 2 * ((1 + H (2*m - 1/2))/2) = (Real.log 2 + biasE (2-4*m))/2 := by
    rw [hEq]
    ring
  let x0 : ℝ := (2 / 1)*m
  have hx0 : Bounds (7961 / 10240) (1991 / 2560) x0 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hm <;> norm_num
  let x1 : ℝ := -x0
  have hx1 : Bounds (-1991 / 2560) (-7961 / 10240) x1 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx0
  let x2 : ℝ := (1 / 1)+x1
  have hx2 : Bounds (569 / 2560) (2279 / 10240) x2 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx1 <;> norm_num
  let x3 : ℝ := (1 / 1)-x0
  have hx3 : Bounds (569 / 2560) (2279 / 10240) x3 := by
    exact hx2
  let x4 : ℝ := (4 / 1)*m
  have hx4 : Bounds (7961 / 5120) (1991 / 1280) x4 := by
    apply bounds_mul (bounds_const ((4 / 1) : ℝ)) hm <;> norm_num
  let x5 : ℝ := -x4
  have hx5 : Bounds (-1991 / 1280) (-7961 / 5120) x5 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx4
  let x6 : ℝ := (2 / 1)+x5
  have hx6 : Bounds (569 / 1280) (2279 / 5120) x6 := by
    apply bounds_add (bounds_const ((2 / 1) : ℝ)) hx5 <;> norm_num
  let x7 : ℝ := (2 / 1)-x4
  have hx7 : Bounds (569 / 1280) (2279 / 5120) x7 := by
    exact hx6
  let x8 : ℝ := Real.log (2 / 1)
  have hx8 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x8 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x9 : ℝ := (1 / 1)+(2279 / 10240)
  have hx9 : Bounds (12519 / 10240) (12519 / 10240) x9 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((2279 / 10240) : ℝ)) <;> norm_num
  let x10 : ℝ := (1 / 1)+(2279 / 10240)
  have hx10 : Bounds (12519 / 10240) (12519 / 10240) x10 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((2279 / 10240) : ℝ)) <;> norm_num
  let x11 : ℝ := Real.log x10
  have hx11 : Bounds (20094587 / 100000000) (200945871 / 1000000000) x11 := by
    exact bounds_log hx10 (by norm_num) (by simpa only [div_one] using reflection_log_1.1) (by simpa only [div_one] using reflection_log_1.2)
  let x12 : ℝ := x9*x11
  have hx12 : Bounds (245668100247 / 1000000000000) (24566810147 / 100000000000) x12 := by
    apply bounds_mul hx9 hx11 <;> norm_num
  let x13 : ℝ := -(2279 / 10240)
  have hx13 : Bounds (-2279 / 10240) (-2279 / 10240) x13 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((2279 / 10240) : ℝ))
  let x14 : ℝ := (1 / 1)+x13
  have hx14 : Bounds (7961 / 10240) (7961 / 10240) x14 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx13 <;> norm_num
  let x15 : ℝ := (1 / 1)-(2279 / 10240)
  have hx15 : Bounds (7961 / 10240) (7961 / 10240) x15 := by
    exact hx14
  let x16 : ℝ := -(2279 / 10240)
  have hx16 : Bounds (-2279 / 10240) (-2279 / 10240) x16 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((2279 / 10240) : ℝ))
  let x17 : ℝ := (1 / 1)+x16
  have hx17 : Bounds (7961 / 10240) (7961 / 10240) x17 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx16 <;> norm_num
  let x18 : ℝ := (1 / 1)-(2279 / 10240)
  have hx18 : Bounds (7961 / 10240) (7961 / 10240) x18 := by
    exact hx17
  let x19 : ℝ := Real.log x18
  have hx19 : Bounds (-251747 / 1000000) (-251746999 / 1000000000) x19 := by
    exact bounds_log hx18 (by norm_num) (by simpa only [div_one] using reflection_log_2.1) (by simpa only [div_one] using reflection_log_2.2)
  let x20 : ℝ := x15*x19
  have hx20 : Bounds (-1957185417 / 10000000000) (-195718540921 / 1000000000000) x20 := by
    apply bounds_mul hx15 hx19 <;> norm_num
  let x21 : ℝ := x12+x20
  have hx21 : Bounds (49949558547 / 1000000000000) (49949560549 / 1000000000000) x21 := by
    apply bounds_add hx12 hx20 <;> norm_num
  let x22 : ℝ := (2 / 1)⁻¹
  have hx22 : Bounds (1 / 2) (1 / 2) x22 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x23 : ℝ := x21*x22
  have hx23 : Bounds (24974779273 / 1000000000000) (998991211 / 40000000000) x23 := by
    apply bounds_mul hx21 hx22 <;> norm_num
  let x24 : ℝ := x21/(2 / 1)
  have hx24 : Bounds (24974779273 / 1000000000000) (998991211 / 40000000000) x24 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx23
  let x25 : ℝ := -x24
  have hx25 : Bounds (-998991211 / 40000000000) (-24974779273 / 1000000000000) x25 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx24
  let x26 : ℝ := x8+x25
  have hx26 : Bounds (26726895989 / 40000000000) (668172401727 / 1000000000000) x26 := by
    apply bounds_add hx8 hx25 <;> norm_num
  let x27 : ℝ := x8-x24
  have hx27 : Bounds (26726895989 / 40000000000) (668172401727 / 1000000000000) x27 := by
    exact hx26
  let x28 : ℝ := biasE (2279 / 10240)
  have hx28 : Bounds (26726895989 / 40000000000) (668172401727 / 1000000000000) x28 := by
    simpa +zetaDelta only [biasE, div_one] using hx27
  let x29 : ℝ := Real.log (2 / 1)
  have hx29 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x29 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x30 : ℝ := (1 / 1)+(569 / 2560)
  have hx30 : Bounds (3129 / 2560) (3129 / 2560) x30 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((569 / 2560) : ℝ)) <;> norm_num
  let x31 : ℝ := (1 / 1)+(569 / 2560)
  have hx31 : Bounds (3129 / 2560) (3129 / 2560) x31 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((569 / 2560) : ℝ)) <;> norm_num
  let x32 : ℝ := Real.log x31
  have hx32 : Bounds (100353103 / 500000000) (200706207 / 1000000000) x32 := by
    exact bounds_log hx31 (by norm_num) (by simpa only [div_one] using reflection_log_3.1) (by simpa only [div_one] using reflection_log_3.2)
  let x33 : ℝ := x30*x32
  have hx33 : Bounds (245316296317 / 1000000000000) (245316297541 / 1000000000000) x33 := by
    apply bounds_mul hx30 hx32 <;> norm_num
  let x34 : ℝ := -(569 / 2560)
  have hx34 : Bounds (-569 / 2560) (-569 / 2560) x34 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((569 / 2560) : ℝ))
  let x35 : ℝ := (1 / 1)+x34
  have hx35 : Bounds (1991 / 2560) (1991 / 2560) x35 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx34 <;> norm_num
  let x36 : ℝ := (1 / 1)-(569 / 2560)
  have hx36 : Bounds (1991 / 2560) (1991 / 2560) x36 := by
    exact hx35
  let x37 : ℝ := -(569 / 2560)
  have hx37 : Bounds (-569 / 2560) (-569 / 2560) x37 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((569 / 2560) : ℝ))
  let x38 : ℝ := (1 / 1)+x37
  have hx38 : Bounds (1991 / 2560) (1991 / 2560) x38 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx37 <;> norm_num
  let x39 : ℝ := (1 / 1)-(569 / 2560)
  have hx39 : Bounds (1991 / 2560) (1991 / 2560) x39 := by
    exact hx38
  let x40 : ℝ := Real.log x39
  have hx40 : Bounds (-125685117 / 500000000) (-251370233 / 1000000000) x40 := by
    exact bounds_log hx39 (by norm_num) (by simpa only [div_one] using reflection_log_4.1) (by simpa only [div_one] using reflection_log_4.2)
  let x41 : ℝ := x36*x40
  have hx41 : Bounds (-97749635917 / 500000000000) (-39099854211 / 200000000000) x41 := by
    apply bounds_mul hx36 hx40 <;> norm_num
  let x42 : ℝ := x33+x41
  have hx42 : Bounds (49817024483 / 1000000000000) (24908513243 / 500000000000) x42 := by
    apply bounds_add hx33 hx41 <;> norm_num
  let x43 : ℝ := (2 / 1)⁻¹
  have hx43 : Bounds (1 / 2) (1 / 2) x43 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x44 : ℝ := x42*x43
  have hx44 : Bounds (24908512241 / 1000000000000) (24908513243 / 1000000000000) x44 := by
    apply bounds_mul hx42 hx43 <;> norm_num
  let x45 : ℝ := x42/(2 / 1)
  have hx45 : Bounds (24908512241 / 1000000000000) (24908513243 / 1000000000000) x45 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx44
  let x46 : ℝ := -x45
  have hx46 : Bounds (-24908513243 / 1000000000000) (-24908512241 / 1000000000000) x46 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx45
  let x47 : ℝ := x29+x46
  have hx47 : Bounds (668238666757 / 1000000000000) (668238668759 / 1000000000000) x47 := by
    apply bounds_add hx29 hx46 <;> norm_num
  let x48 : ℝ := x29-x45
  have hx48 : Bounds (668238666757 / 1000000000000) (668238668759 / 1000000000000) x48 := by
    exact hx47
  let x49 : ℝ := biasE (569 / 2560)
  have hx49 : Bounds (668238666757 / 1000000000000) (668238668759 / 1000000000000) x49 := by
    simpa +zetaDelta only [biasE, div_one] using hx48
  let x50 : ℝ := biasE x3
  have hx50 : Bounds (26726895989 / 40000000000) (668238668759 / 1000000000000) x50 := by
    exact bounds_biasE hx3 (by norm_num) (by norm_num) hx28.1 hx49.2
  let x51 : ℝ := Real.log (2 / 1)
  have hx51 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x51 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x52 : ℝ := (1 / 1)+(2279 / 5120)
  have hx52 : Bounds (7399 / 5120) (7399 / 5120) x52 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((2279 / 5120) : ℝ)) <;> norm_num
  let x53 : ℝ := (1 / 1)+(2279 / 5120)
  have hx53 : Bounds (7399 / 5120) (7399 / 5120) x53 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((2279 / 5120) : ℝ)) <;> norm_num
  let x54 : ℝ := Real.log x53
  have hx54 : Bounds (23011901 / 62500000) (368190417 / 1000000000) x54 := by
    exact bounds_log hx53 (by norm_num) (by simpa only [div_one] using reflection_log_5.1) (by simpa only [div_one] using reflection_log_5.2)
  let x55 : ℝ := x52*x54
  have hx55 : Bounds (266039149217 / 500000000000) (13301957497 / 25000000000) x55 := by
    apply bounds_mul hx52 hx54 <;> norm_num
  let x56 : ℝ := -(2279 / 5120)
  have hx56 : Bounds (-2279 / 5120) (-2279 / 5120) x56 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((2279 / 5120) : ℝ))
  let x57 : ℝ := (1 / 1)+x56
  have hx57 : Bounds (2841 / 5120) (2841 / 5120) x57 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx56 <;> norm_num
  let x58 : ℝ := (1 / 1)-(2279 / 5120)
  have hx58 : Bounds (2841 / 5120) (2841 / 5120) x58 := by
    exact hx57
  let x59 : ℝ := -(2279 / 5120)
  have hx59 : Bounds (-2279 / 5120) (-2279 / 5120) x59 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((2279 / 5120) : ℝ))
  let x60 : ℝ := (1 / 1)+x59
  have hx60 : Bounds (2841 / 5120) (2841 / 5120) x60 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx59 <;> norm_num
  let x61 : ℝ := (1 / 1)-(2279 / 5120)
  have hx61 : Bounds (2841 / 5120) (2841 / 5120) x61 := by
    exact hx60
  let x62 : ℝ := Real.log x61
  have hx62 : Bounds (-588998337 / 1000000000) (-9203099 / 15625000) x62 := by
    exact bounds_log hx61 (by norm_num) (by simpa only [div_one] using reflection_log_6.1) (by simpa only [div_one] using reflection_log_6.2)
  let x63 : ℝ := x58*x62
  have hx63 : Bounds (-326825053793 / 1000000000000) (-326825053237 / 1000000000000) x63 := by
    apply bounds_mul hx58 hx62 <;> norm_num
  let x64 : ℝ := x55+x63
  have hx64 : Bounds (205253244641 / 1000000000000) (205253246643 / 1000000000000) x64 := by
    apply bounds_add hx55 hx63 <;> norm_num
  let x65 : ℝ := (2 / 1)⁻¹
  have hx65 : Bounds (1 / 2) (1 / 2) x65 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x66 : ℝ := x64*x65
  have hx66 : Bounds (1282832779 / 12500000000) (51313311661 / 500000000000) x66 := by
    apply bounds_mul hx64 hx65 <;> norm_num
  let x67 : ℝ := x64/(2 / 1)
  have hx67 : Bounds (1282832779 / 12500000000) (51313311661 / 500000000000) x67 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx66
  let x68 : ℝ := -x67
  have hx68 : Bounds (-51313311661 / 500000000000) (-1282832779 / 12500000000) x68 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx67
  let x69 : ℝ := x51+x68
  have hx69 : Bounds (295260278339 / 500000000000) (14763013967 / 25000000000) x69 := by
    apply bounds_add hx51 hx68 <;> norm_num
  let x70 : ℝ := x51-x67
  have hx70 : Bounds (295260278339 / 500000000000) (14763013967 / 25000000000) x70 := by
    exact hx69
  let x71 : ℝ := biasE (2279 / 5120)
  have hx71 : Bounds (295260278339 / 500000000000) (14763013967 / 25000000000) x71 := by
    simpa +zetaDelta only [biasE, div_one] using hx70
  let x72 : ℝ := Real.log (2 / 1)
  have hx72 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x72 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x73 : ℝ := (1 / 1)+(569 / 1280)
  have hx73 : Bounds (1849 / 1280) (1849 / 1280) x73 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((569 / 1280) : ℝ)) <;> norm_num
  let x74 : ℝ := (1 / 1)+(569 / 1280)
  have hx74 : Bounds (1849 / 1280) (1849 / 1280) x74 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((569 / 1280) : ℝ)) <;> norm_num
  let x75 : ℝ := Real.log x74
  have hx75 : Bounds (183892437 / 500000000) (2942279 / 8000000) x75 := by
    exact bounds_log hx74 (by norm_num) (by simpa only [div_one] using reflection_log_7.1) (by simpa only [div_one] using reflection_log_7.2)
  let x76 : ℝ := x73*x75
  have hx76 : Bounds (53127674377 / 100000000000) (106255349043 / 200000000000) x76 := by
    apply bounds_mul hx73 hx75 <;> norm_num
  let x77 : ℝ := -(569 / 1280)
  have hx77 : Bounds (-569 / 1280) (-569 / 1280) x77 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((569 / 1280) : ℝ))
  let x78 : ℝ := (1 / 1)+x77
  have hx78 : Bounds (711 / 1280) (711 / 1280) x78 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx77 <;> norm_num
  let x79 : ℝ := (1 / 1)-(569 / 1280)
  have hx79 : Bounds (711 / 1280) (711 / 1280) x79 := by
    exact hx78
  let x80 : ℝ := -(569 / 1280)
  have hx80 : Bounds (-569 / 1280) (-569 / 1280) x80 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((569 / 1280) : ℝ))
  let x81 : ℝ := (1 / 1)+x80
  have hx81 : Bounds (711 / 1280) (711 / 1280) x81 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx80 <;> norm_num
  let x82 : ℝ := (1 / 1)-(569 / 1280)
  have hx82 : Bounds (711 / 1280) (711 / 1280) x82 := by
    exact hx81
  let x83 : ℝ := Real.log x82
  have hx83 : Bounds (-36746433 / 62500000) (-587942927 / 1000000000) x83 := by
    exact bounds_log hx82 (by norm_num) (by simpa only [div_one] using reflection_log_8.1) (by simpa only [div_one] using reflection_log_8.2)
  let x84 : ℝ := x79*x83
  have hx84 : Bounds (-40822990411 / 125000000000) (-81645980683 / 250000000000) x84 := by
    apply bounds_mul hx79 hx83 <;> norm_num
  let x85 : ℝ := x76+x84
  have hx85 : Bounds (102346410241 / 500000000000) (204692822483 / 1000000000000) x85 := by
    apply bounds_add hx76 hx84 <;> norm_num
  let x86 : ℝ := (2 / 1)⁻¹
  have hx86 : Bounds (1 / 2) (1 / 2) x86 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x87 : ℝ := x85*x86
  have hx87 : Bounds (102346410241 / 1000000000000) (51173205621 / 500000000000) x87 := by
    apply bounds_mul hx85 hx86 <;> norm_num
  let x88 : ℝ := x85/(2 / 1)
  have hx88 : Bounds (102346410241 / 1000000000000) (51173205621 / 500000000000) x88 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx87
  let x89 : ℝ := -x88
  have hx89 : Bounds (-51173205621 / 500000000000) (-102346410241 / 1000000000000) x89 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx88
  let x90 : ℝ := x72+x89
  have hx90 : Bounds (295400384379 / 500000000000) (590800770759 / 1000000000000) x90 := by
    apply bounds_add hx72 hx89 <;> norm_num
  let x91 : ℝ := x72-x88
  have hx91 : Bounds (295400384379 / 500000000000) (590800770759 / 1000000000000) x91 := by
    exact hx90
  let x92 : ℝ := biasE (569 / 1280)
  have hx92 : Bounds (295400384379 / 500000000000) (590800770759 / 1000000000000) x92 := by
    simpa +zetaDelta only [biasE, div_one] using hx91
  let x93 : ℝ := biasE x7
  have hx93 : Bounds (295260278339 / 500000000000) (590800770759 / 1000000000000) x93 := by
    exact bounds_biasE hx7 (by norm_num) (by norm_num) hx71.1 hx92.2
  let x94 : ℝ := Real.log (2 / 1)
  have hx94 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x94 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x95 : ℝ := x94+x93
  have hx95 : Bounds (641833868339 / 500000000000) (1283947951759 / 1000000000000) x95 := by
    apply bounds_add hx94 hx93 <;> norm_num
  let x96 : ℝ := (2 / 1)⁻¹
  have hx96 : Bounds (1 / 2) (1 / 2) x96 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x97 : ℝ := x95*x96
  have hx97 : Bounds (641833868339 / 1000000000000) (16049349397 / 25000000000) x97 := by
    apply bounds_mul hx95 hx96 <;> norm_num
  let x98 : ℝ := x95/(2 / 1)
  have hx98 : Bounds (641833868339 / 1000000000000) (16049349397 / 25000000000) x98 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx97
  let x99 : ℝ := Real.log (2 / 1)
  have hx99 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x99 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x100 : ℝ := (1 / 1)+(79289 / 250000)
  have hx100 : Bounds (329289 / 250000) (329289 / 250000) x100 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((79289 / 250000) : ℝ)) <;> norm_num
  let x101 : ℝ := (1 / 1)+(79289 / 250000)
  have hx101 : Bounds (329289 / 250000) (329289 / 250000) x101 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((79289 / 250000) : ℝ)) <;> norm_num
  let x102 : ℝ := Real.log x101
  have hx102 : Bounds (137737433 / 500000000) (275474867 / 1000000000) x102 := by
    exact bounds_log hx101 (by norm_num) (by simpa only [div_one] using reflection_log_9.1) (by simpa only [div_one] using reflection_log_9.2)
  let x103 : ℝ := x100*x102
  have hx103 : Bounds (362843372601 / 1000000000000) (362843373919 / 1000000000000) x103 := by
    apply bounds_mul hx100 hx102 <;> norm_num
  let x104 : ℝ := -(79289 / 250000)
  have hx104 : Bounds (-79289 / 250000) (-79289 / 250000) x104 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((79289 / 250000) : ℝ))
  let x105 : ℝ := (1 / 1)+x104
  have hx105 : Bounds (170711 / 250000) (170711 / 250000) x105 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx104 <;> norm_num
  let x106 : ℝ := (1 / 1)-(79289 / 250000)
  have hx106 : Bounds (170711 / 250000) (170711 / 250000) x106 := by
    exact hx105
  let x107 : ℝ := -(79289 / 250000)
  have hx107 : Bounds (-79289 / 250000) (-79289 / 250000) x107 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((79289 / 250000) : ℝ))
  let x108 : ℝ := (1 / 1)+x107
  have hx108 : Bounds (170711 / 250000) (170711 / 250000) x108 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx107 <;> norm_num
  let x109 : ℝ := (1 / 1)-(79289 / 250000)
  have hx109 : Bounds (170711 / 250000) (170711 / 250000) x109 := by
    exact hx108
  let x110 : ℝ := Real.log x109
  have hx110 : Bounds (-7629777 / 20000000) (-381488849 / 1000000000) x110 := by
    exact bounds_log hx109 (by norm_num) (by simpa only [div_one] using reflection_log_10.1) (by simpa only [div_one] using reflection_log_10.2)
  let x111 : ℝ := x106*x110
  have hx111 : Bounds (-26049737229 / 100000000000) (-130248685803 / 500000000000) x111 := by
    apply bounds_mul hx106 hx110 <;> norm_num
  let x112 : ℝ := x103+x111
  have hx112 : Bounds (102346000311 / 1000000000000) (102346002313 / 1000000000000) x112 := by
    apply bounds_add hx103 hx111 <;> norm_num
  let x113 : ℝ := (2 / 1)⁻¹
  have hx113 : Bounds (1 / 2) (1 / 2) x113 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x114 : ℝ := x112*x113
  have hx114 : Bounds (10234600031 / 200000000000) (51173001157 / 1000000000000) x114 := by
    apply bounds_mul hx112 hx113 <;> norm_num
  let x115 : ℝ := x112/(2 / 1)
  have hx115 : Bounds (10234600031 / 200000000000) (51173001157 / 1000000000000) x115 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx114
  let x116 : ℝ := -x115
  have hx116 : Bounds (-51173001157 / 1000000000000) (-10234600031 / 200000000000) x116 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx115
  let x117 : ℝ := x99+x116
  have hx117 : Bounds (641974178843 / 1000000000000) (128394836169 / 200000000000) x117 := by
    apply bounds_add hx99 hx116 <;> norm_num
  let x118 : ℝ := x99-x115
  have hx118 : Bounds (641974178843 / 1000000000000) (128394836169 / 200000000000) x118 := by
    exact hx117
  let x119 : ℝ := biasE (79289 / 250000)
  have hx119 : Bounds (641974178843 / 1000000000000) (128394836169 / 200000000000) x119 := by
    simpa +zetaDelta only [biasE, div_one] using hx118
  let x120 : ℝ := Real.log (2 / 1)
  have hx120 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x120 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x121 : ℝ := (1 / 1)+(317583 / 1000000)
  have hx121 : Bounds (1317583 / 1000000) (1317583 / 1000000) x121 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((317583 / 1000000) : ℝ)) <;> norm_num
  let x122 : ℝ := (1 / 1)+(317583 / 1000000)
  have hx122 : Bounds (1317583 / 1000000) (1317583 / 1000000) x122 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((317583 / 1000000) : ℝ)) <;> norm_num
  let x123 : ℝ := Real.log x122
  have hx123 : Bounds (275798997 / 1000000000) (137899499 / 500000000) x123 := by
    exact bounds_log hx122 (by norm_num) (by simpa only [div_one] using reflection_log_11.1) (by simpa only [div_one] using reflection_log_11.2)
  let x124 : ℝ := x121*x123
  have hx124 : Bounds (45423508733 / 125000000000) (181694035591 / 500000000000) x124 := by
    apply bounds_mul hx121 hx123 <;> norm_num
  let x125 : ℝ := -(317583 / 1000000)
  have hx125 : Bounds (-317583 / 1000000) (-317583 / 1000000) x125 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((317583 / 1000000) : ℝ))
  let x126 : ℝ := (1 / 1)+x125
  have hx126 : Bounds (682417 / 1000000) (682417 / 1000000) x126 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx125 <;> norm_num
  let x127 : ℝ := (1 / 1)-(317583 / 1000000)
  have hx127 : Bounds (682417 / 1000000) (682417 / 1000000) x127 := by
    exact hx126
  let x128 : ℝ := -(317583 / 1000000)
  have hx128 : Bounds (-317583 / 1000000) (-317583 / 1000000) x128 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((317583 / 1000000) : ℝ))
  let x129 : ℝ := (1 / 1)+x128
  have hx129 : Bounds (682417 / 1000000) (682417 / 1000000) x129 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx128 <;> norm_num
  let x130 : ℝ := (1 / 1)-(317583 / 1000000)
  have hx130 : Bounds (682417 / 1000000) (682417 / 1000000) x130 := by
    exact hx129
  let x131 : ℝ := Real.log x130
  have hx131 : Bounds (-95528593 / 250000000) (-382114371 / 1000000000) x131 := by
    exact bounds_log hx130 (by norm_num) (by simpa only [div_one] using reflection_log_12.1) (by simpa only [div_one] using reflection_log_12.2)
  let x132 : ℝ := x127*x131
  have hx132 : Bounds (-130380671699 / 500000000000) (-130380671357 / 500000000000) x132 := by
    apply bounds_mul hx127 hx131 <;> norm_num
  let x133 : ℝ := x124+x132
  have hx133 : Bounds (51313363233 / 500000000000) (25656682117 / 250000000000) x133 := by
    apply bounds_add hx124 hx132 <;> norm_num
  let x134 : ℝ := (2 / 1)⁻¹
  have hx134 : Bounds (1 / 2) (1 / 2) x134 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x135 : ℝ := x133*x134
  have hx135 : Bounds (51313363233 / 1000000000000) (25656682117 / 500000000000) x135 := by
    apply bounds_mul hx133 hx134 <;> norm_num
  let x136 : ℝ := x133/(2 / 1)
  have hx136 : Bounds (51313363233 / 1000000000000) (25656682117 / 500000000000) x136 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx135
  let x137 : ℝ := -x136
  have hx137 : Bounds (-25656682117 / 500000000000) (-51313363233 / 1000000000000) x137 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx136
  let x138 : ℝ := x120+x137
  have hx138 : Bounds (320916907883 / 500000000000) (641833817767 / 1000000000000) x138 := by
    apply bounds_add hx120 hx137 <;> norm_num
  let x139 : ℝ := x120-x136
  have hx139 : Bounds (320916907883 / 500000000000) (641833817767 / 1000000000000) x139 := by
    exact hx138
  let x140 : ℝ := biasE (317583 / 1000000)
  have hx140 : Bounds (320916907883 / 500000000000) (641833817767 / 1000000000000) x140 := by
    simpa +zetaDelta only [biasE, div_one] using hx139
  let y : ℝ := 1 - 2 * entropyInverse ((1 + H (2*m - 1/2))/2)
  have hLh' : Real.log 2 * ((1 + H (2*m - 1/2))/2) = x98 := by
    simpa +zetaDelta only [div_one] using hLh
  have hy : Bounds (79289 / 250000) (317583 / 1000000) y := by
    apply entropyInverseBias_bracket
    · exact div_nonneg (add_nonneg zero_le_one
        (H_nonneg (by linarith [hm.1]) (by linarith [hm.2]))) two_pos.le
    · linarith [H_le_one (2*m-1/2)]
    · norm_num
    · norm_num
    · norm_num
    · have h1 : biasE (317583 / 1000000) ≤ (641833817767 / 1000000000000) := hx140.2
      have h2 : (641833868339 / 1000000000000) ≤ x98 := hx98.1
      linarith [hLh']
    · have h1 : x98 ≤ (16049349397 / 25000000000) := hx98.2
      have h2 : (641974178843 / 1000000000000) ≤ biasE (79289 / 250000) := hx119.1
      linarith [hLh']
  let x141 : ℝ := x3⁻¹
  have hx141 : Bounds (449319877139 / 100000000000) (2249560632689 / 500000000000) x141 := by
    apply bounds_inv hx3 <;> norm_num
  let x142 : ℝ := x98*x141
  have hx142 : Bounds (2883887148657 / 1000000000000) (2888318766701 / 1000000000000) x142 := by
    apply bounds_mul hx98 hx141 <;> norm_num
  let x143 : ℝ := x98/x3
  have hx143 : Bounds (2883887148657 / 1000000000000) (2888318766701 / 1000000000000) x143 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx142
  let x144 : ℝ := Real.log (2 / 1)
  have hx144 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x144 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x145 : ℝ := (1 / 1)+(230687 / 1000000)
  have hx145 : Bounds (1230687 / 1000000) (1230687 / 1000000) x145 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((230687 / 1000000) : ℝ)) <;> norm_num
  let x146 : ℝ := (1 / 1)+(230687 / 1000000)
  have hx146 : Bounds (1230687 / 1000000) (1230687 / 1000000) x146 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((230687 / 1000000) : ℝ)) <;> norm_num
  let x147 : ℝ := Real.log x146
  have hx147 : Bounds (4151451 / 20000000) (207572551 / 1000000000) x147 := by
    exact bounds_log hx146 (by norm_num) (by simpa only [div_one] using reflection_log_13.1) (by simpa only [div_one] using reflection_log_13.2)
  let x148 : ℝ := x145*x147
  have hx148 : Bounds (255456838841 / 1000000000000) (255456840073 / 1000000000000) x148 := by
    apply bounds_mul hx145 hx147 <;> norm_num
  let x149 : ℝ := -(230687 / 1000000)
  have hx149 : Bounds (-230687 / 1000000) (-230687 / 1000000) x149 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((230687 / 1000000) : ℝ))
  let x150 : ℝ := (1 / 1)+x149
  have hx150 : Bounds (769313 / 1000000) (769313 / 1000000) x150 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx149 <;> norm_num
  let x151 : ℝ := (1 / 1)-(230687 / 1000000)
  have hx151 : Bounds (769313 / 1000000) (769313 / 1000000) x151 := by
    exact hx150
  let x152 : ℝ := -(230687 / 1000000)
  have hx152 : Bounds (-230687 / 1000000) (-230687 / 1000000) x152 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((230687 / 1000000) : ℝ))
  let x153 : ℝ := (1 / 1)+x152
  have hx153 : Bounds (769313 / 1000000) (769313 / 1000000) x153 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx152 <;> norm_num
  let x154 : ℝ := (1 / 1)-(230687 / 1000000)
  have hx154 : Bounds (769313 / 1000000) (769313 / 1000000) x154 := by
    exact hx153
  let x155 : ℝ := Real.log x154
  have hx155 : Bounds (-262257371 / 1000000000) (-26225737 / 100000000) x155 := by
    exact bounds_log hx154 (by norm_num) (by simpa only [div_one] using reflection_log_14.1) (by simpa only [div_one] using reflection_log_14.2)
  let x156 : ℝ := x151*x155
  have hx156 : Bounds (-201758004857 / 1000000000000) (-100879002043 / 500000000000) x156 := by
    apply bounds_mul hx151 hx155 <;> norm_num
  let x157 : ℝ := x148+x156
  have hx157 : Bounds (839044281 / 15625000000) (53698835987 / 1000000000000) x157 := by
    apply bounds_add hx148 hx156 <;> norm_num
  let x158 : ℝ := (2 / 1)⁻¹
  have hx158 : Bounds (1 / 2) (1 / 2) x158 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x159 : ℝ := x157*x158
  have hx159 : Bounds (839044281 / 31250000000) (13424708997 / 500000000000) x159 := by
    apply bounds_mul hx157 hx158 <;> norm_num
  let x160 : ℝ := x157/(2 / 1)
  have hx160 : Bounds (839044281 / 31250000000) (13424708997 / 500000000000) x160 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx159
  let x161 : ℝ := -x160
  have hx161 : Bounds (-13424708997 / 500000000000) (-839044281 / 31250000000) x161 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx160
  let x162 : ℝ := x144+x161
  have hx162 : Bounds (333148881003 / 500000000000) (83287220501 / 125000000000) x162 := by
    apply bounds_add hx144 hx161 <;> norm_num
  let x163 : ℝ := x144-x160
  have hx163 : Bounds (333148881003 / 500000000000) (83287220501 / 125000000000) x163 := by
    exact hx162
  let x164 : ℝ := biasE (230687 / 1000000)
  have hx164 : Bounds (333148881003 / 500000000000) (83287220501 / 125000000000) x164 := by
    simpa +zetaDelta only [biasE, div_one] using hx163
  let x165 : ℝ := Real.log (2 / 1)
  have hx165 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x165 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x166 : ℝ := (1 / 1)+(46203 / 200000)
  have hx166 : Bounds (246203 / 200000) (246203 / 200000) x166 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((46203 / 200000) : ℝ)) <;> norm_num
  let x167 : ℝ := (1 / 1)+(46203 / 200000)
  have hx167 : Bounds (246203 / 200000) (246203 / 200000) x167 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((46203 / 200000) : ℝ)) <;> norm_num
  let x168 : ℝ := Real.log x167
  have hx168 : Bounds (25979879 / 125000000) (207839033 / 1000000000) x168 := by
    exact bounds_log hx167 (by norm_num) (by simpa only [div_one] using reflection_log_15.1) (by simpa only [div_one] using reflection_log_15.2)
  let x169 : ℝ := x166*x168
  have hx169 : Bounds (255852965977 / 1000000000000) (255852967209 / 1000000000000) x169 := by
    apply bounds_mul hx166 hx168 <;> norm_num
  let x170 : ℝ := -(46203 / 200000)
  have hx170 : Bounds (-46203 / 200000) (-46203 / 200000) x170 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((46203 / 200000) : ℝ))
  let x171 : ℝ := (1 / 1)+x170
  have hx171 : Bounds (153797 / 200000) (153797 / 200000) x171 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx170 <;> norm_num
  let x172 : ℝ := (1 / 1)-(46203 / 200000)
  have hx172 : Bounds (153797 / 200000) (153797 / 200000) x172 := by
    exact hx171
  let x173 : ℝ := -(46203 / 200000)
  have hx173 : Bounds (-46203 / 200000) (-46203 / 200000) x173 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((46203 / 200000) : ℝ))
  let x174 : ℝ := (1 / 1)+x173
  have hx174 : Bounds (153797 / 200000) (153797 / 200000) x174 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx173 <;> norm_num
  let x175 : ℝ := (1 / 1)-(46203 / 200000)
  have hx175 : Bounds (153797 / 200000) (153797 / 200000) x175 := by
    exact hx174
  let x176 : ℝ := Real.log x175
  have hx176 : Bounds (-32835477 / 125000000) (-52536763 / 200000000) x176 := by
    exact bounds_log hx175 (by norm_num) (by simpa only [div_one] using reflection_log_16.1) (by simpa only [div_one] using reflection_log_16.2)
  let x177 : ℝ := x172*x176
  have hx177 : Bounds (-201999914247 / 1000000000000) (-201999913477 / 1000000000000) x177 := by
    apply bounds_mul hx172 hx176 <;> norm_num
  let x178 : ℝ := x169+x177
  have hx178 : Bounds (5385305173 / 100000000000) (13463263433 / 250000000000) x178 := by
    apply bounds_add hx169 hx177 <;> norm_num
  let x179 : ℝ := (2 / 1)⁻¹
  have hx179 : Bounds (1 / 2) (1 / 2) x179 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x180 : ℝ := x178*x179
  have hx180 : Bounds (5385305173 / 200000000000) (13463263433 / 500000000000) x180 := by
    apply bounds_mul hx178 hx179 <;> norm_num
  let x181 : ℝ := x178/(2 / 1)
  have hx181 : Bounds (5385305173 / 200000000000) (13463263433 / 500000000000) x181 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx180
  let x182 : ℝ := -x181
  have hx182 : Bounds (-13463263433 / 500000000000) (-5385305173 / 200000000000) x182 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx181
  let x183 : ℝ := x165+x182
  have hx183 : Bounds (333110326567 / 500000000000) (133244131027 / 200000000000) x183 := by
    apply bounds_add hx165 hx182 <;> norm_num
  let x184 : ℝ := x165-x181
  have hx184 : Bounds (333110326567 / 500000000000) (133244131027 / 200000000000) x184 := by
    exact hx183
  let x185 : ℝ := biasE (46203 / 200000)
  have hx185 : Bounds (333110326567 / 500000000000) (133244131027 / 200000000000) x185 := by
    simpa +zetaDelta only [biasE, div_one] using hx184
  let x186 : ℝ := x143*(230687 / 1000000)
  have hx186 : Bounds (332637637331 / 500000000000) (333148795667 / 500000000000) x186 := by
    apply bounds_mul hx143 (bounds_const ((230687 / 1000000) : ℝ)) <;> norm_num
  let x187 : ℝ := x143*(46203 / 200000)
  have hx187 : Bounds (333110594823 / 500000000000) (66724495989 / 100000000000) x187 := by
    apply bounds_mul hx143 (bounds_const ((46203 / 200000) : ℝ)) <;> norm_num
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
  have hc : Bounds (230687 / 1000000) (46203 / 200000) c := by
    apply contact_bracket hc0 hcMem.2.le (by norm_num) (by norm_num) (by norm_num)
      (show 0 < x143 by linarith [hx143.1]) hcEq
    · have h1 : x143 * (230687 / 1000000) ≤ (333148795667 / 500000000000) := hx186.2
      have h2 : (333148881003 / 500000000000) ≤ biasE (230687 / 1000000) := hx164.1
      linarith
    · have h1 : biasE (46203 / 200000) ≤ (133244131027 / 200000000000) := hx185.2
      have h2 : (333110594823 / 500000000000) ≤ x143 * (46203 / 200000) := hx187.1
      linarith
  let x188 : ℝ := (1 / 1)+y
  have hx188 : Bounds (329289 / 250000) (1317583 / 1000000) x188 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hy <;> norm_num
  let x189 : ℝ := -y
  have hx189 : Bounds (-317583 / 1000000) (-79289 / 250000) x189 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hy
  let x190 : ℝ := (1 / 1)+x189
  have hx190 : Bounds (682417 / 1000000) (170711 / 250000) x190 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx189 <;> norm_num
  let x191 : ℝ := (1 / 1)-y
  have hx191 : Bounds (682417 / 1000000) (170711 / 250000) x191 := by
    exact hx190
  let x192 : ℝ := x191⁻¹
  have hx192 : Bounds (1464463332767 / 1000000000000) (1465379672547 / 1000000000000) x192 := by
    apply bounds_inv hx191 <;> norm_num
  let x193 : ℝ := x188*x192
  have hx193 : Bounds (964463332767 / 500000000000) (965379672547 / 500000000000) x193 := by
    apply bounds_mul hx188 hx192 <;> norm_num
  let x194 : ℝ := x188/x191
  have hx194 : Bounds (964463332767 / 500000000000) (965379672547 / 500000000000) x194 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx193
  let x195 : ℝ := Real.log x194
  have hx195 : Bounds (164240929 / 250000000) (657913369 / 1000000000) x195 := by
    exact bounds_log hx194 (by norm_num) (by simpa only [div_one] using reflection_log_17.1) (by simpa only [div_one] using reflection_log_18.2)
  let x196 : ℝ := (2 / 1)⁻¹
  have hx196 : Bounds (1 / 2) (1 / 2) x196 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x197 : ℝ := x195*x196
  have hx197 : Bounds (164240929 / 500000000) (657913369 / 2000000000) x197 := by
    apply bounds_mul hx195 hx196 <;> norm_num
  let x198 : ℝ := x195/(2 / 1)
  have hx198 : Bounds (164240929 / 500000000) (657913369 / 2000000000) x198 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx197
  let x199 : ℝ := (1 / 1)+c
  have hx199 : Bounds (1230687 / 1000000) (246203 / 200000) x199 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hc <;> norm_num
  let x200 : ℝ := -c
  have hx200 : Bounds (-46203 / 200000) (-230687 / 1000000) x200 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hc
  let x201 : ℝ := (1 / 1)+x200
  have hx201 : Bounds (153797 / 200000) (769313 / 1000000) x201 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx200 <;> norm_num
  let x202 : ℝ := (1 / 1)-c
  have hx202 : Bounds (153797 / 200000) (769313 / 1000000) x202 := by
    exact hx201
  let x203 : ℝ := x202⁻¹
  have hx203 : Bounds (649930522427 / 500000000000) (1300415482747 / 1000000000000) x203 := by
    apply bounds_inv hx202 <;> norm_num
  let x204 : ℝ := x199*x203
  have hx204 : Bounds (399930522427 / 250000000000) (800415482747 / 500000000000) x204 := by
    apply bounds_mul hx199 hx203 <;> norm_num
  let x205 : ℝ := x199/x202
  have hx205 : Bounds (399930522427 / 250000000000) (800415482747 / 500000000000) x205 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx204
  let x206 : ℝ := Real.log x205
  have hx206 : Bounds (2936437 / 6250000) (14703839 / 31250000) x206 := by
    exact bounds_log hx205 (by norm_num) (by simpa only [div_one] using reflection_log_19.1) (by simpa only [div_one] using reflection_log_20.2)
  let x207 : ℝ := (2 / 1)⁻¹
  have hx207 : Bounds (1 / 2) (1 / 2) x207 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x208 : ℝ := x206*x207
  have hx208 : Bounds (2936437 / 12500000) (14703839 / 62500000) x208 := by
    apply bounds_mul hx206 hx207 <;> norm_num
  let x209 : ℝ := x206/(2 / 1)
  have hx209 : Bounds (2936437 / 12500000) (14703839 / 62500000) x209 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx208
  let x210 : ℝ := (2 / 1)*x50
  have hx210 : Bounds (26726895989 / 20000000000) (668238668759 / 500000000000) x210 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx50 <;> norm_num
  let x211 : ℝ := (2 / 1)*x98
  have hx211 : Bounds (641833868339 / 500000000000) (16049349397 / 12500000000) x211 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx98 <;> norm_num
  let x212 : ℝ := -x211
  have hx212 : Bounds (-16049349397 / 12500000000) (-641833868339 / 500000000000) x212 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx211
  let x213 : ℝ := x210+x212
  have hx213 : Bounds (5239684769 / 100000000000) (1320240021 / 25000000000) x213 := by
    apply bounds_add hx210 hx212 <;> norm_num
  let x214 : ℝ := x210-x211
  have hx214 : Bounds (5239684769 / 100000000000) (1320240021 / 25000000000) x214 := by
    exact hx213
  let x215 : ℝ := y*x198
  have hx215 : Bounds (20835998431 / 200000000000) (52235525367 / 500000000000) x215 := by
    apply bounds_mul hy hx198 <;> norm_num
  let x216 : ℝ := -x215
  have hx216 : Bounds (-52235525367 / 500000000000) (-20835998431 / 200000000000) x216 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx215
  let x217 : ℝ := x214+x216
  have hx217 : Bounds (-13018550761 / 250000000000) (-10274078263 / 200000000000) x217 := by
    apply bounds_add hx214 hx216 <;> norm_num
  let x218 : ℝ := x214-x215
  have hx218 : Bounds (-13018550761 / 250000000000) (-10274078263 / 200000000000) x218 := by
    exact hx217
  let x219 : ℝ := x3*x209
  have hx219 : Bounds (26106760203 / 500000000000) (5235945169 / 100000000000) x219 := by
    apply bounds_mul hx3 hx209 <;> norm_num
  let x220 : ℝ := x218+x219
  have hx220 : Bounds (69658681 / 500000000000) (7912483 / 8000000000) x220 := by
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

theorem acceptedCertificate : DoubleCapBiasCellCertificate (7961 / 20480) (1991 / 5120) (fun m => (1 + H (2*m - 1/2))/2) where
  domain := by norm_num
  sound m hmLo hmHi := by
    exact cell_bias_nonneg m ⟨hmLo, hmHi⟩

theorem accepted_cell :
    ∀ m, (7961 / 20480) ≤ m → m ≤ (1991 / 5120) → 0 ≤ doubleCapHighResidual m := by
  intro m hmLo hmHi
  unfold doubleCapHighResidual
  apply doubleCapEndpointResidual_nonneg_of_biasCell acceptedCertificate hmLo hmHi
  exact div_pos (by linarith [H_nonneg (by linarith : 0 ≤ 2*m-1/2) (by linarith : 2*m-1/2 ≤ 1)]) two_pos

#print axioms cell_bias_nonneg
#print axioms accepted_cell

end GeneralCK.Certificates.DoubleCapMiddle.Cell0397

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0398 =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0398
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Reflection
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem cell_bias_nonneg (m : ℝ) (hm : Bounds (1991 / 5120) (7967 / 20480) m) :
    let h := (1 + H (2*m - 1/2))/2
    let x := 1-2*m
    let y := 1-2*entropyInverse h
    let c := regularContact (x/(Real.log 2*h))
    0 ≤ 2*(biasE x-Real.log 2*h)-y*SmallMean.A y+x*SmallMean.A c := by
  have hEq : biasE (2-4*m) = Real.log 2 * H (2*m-1/2) := by
    have hmstrict : 1/4 < m := by
      have hlo : (1/4 : ℝ) < (1991 / 5120) := by norm_num
      exact lt_of_lt_of_le hlo hm.1
    rw [show 2-4*m = 1-2*(2*m-1/2) by ring,
      GeneralCK.Correction.Natural.biasE_probability (by linarith [hmstrict]) (by linarith [hm.2]),
      GeneralCK.Certificates.Mixed.hn_eq_H_mul_log]
    ring
  have hLh : Real.log 2 * ((1 + H (2*m - 1/2))/2) = (Real.log 2 + biasE (2-4*m))/2 := by
    rw [hEq]
    ring
  let x0 : ℝ := (2 / 1)*m
  have hx0 : Bounds (1991 / 2560) (7967 / 10240) x0 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hm <;> norm_num
  let x1 : ℝ := -x0
  have hx1 : Bounds (-7967 / 10240) (-1991 / 2560) x1 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx0
  let x2 : ℝ := (1 / 1)+x1
  have hx2 : Bounds (2273 / 10240) (569 / 2560) x2 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx1 <;> norm_num
  let x3 : ℝ := (1 / 1)-x0
  have hx3 : Bounds (2273 / 10240) (569 / 2560) x3 := by
    exact hx2
  let x4 : ℝ := (4 / 1)*m
  have hx4 : Bounds (1991 / 1280) (7967 / 5120) x4 := by
    apply bounds_mul (bounds_const ((4 / 1) : ℝ)) hm <;> norm_num
  let x5 : ℝ := -x4
  have hx5 : Bounds (-7967 / 5120) (-1991 / 1280) x5 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx4
  let x6 : ℝ := (2 / 1)+x5
  have hx6 : Bounds (2273 / 5120) (569 / 1280) x6 := by
    apply bounds_add (bounds_const ((2 / 1) : ℝ)) hx5 <;> norm_num
  let x7 : ℝ := (2 / 1)-x4
  have hx7 : Bounds (2273 / 5120) (569 / 1280) x7 := by
    exact hx6
  let x8 : ℝ := Real.log (2 / 1)
  have hx8 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x8 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x9 : ℝ := (1 / 1)+(569 / 2560)
  have hx9 : Bounds (3129 / 2560) (3129 / 2560) x9 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((569 / 2560) : ℝ)) <;> norm_num
  let x10 : ℝ := (1 / 1)+(569 / 2560)
  have hx10 : Bounds (3129 / 2560) (3129 / 2560) x10 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((569 / 2560) : ℝ)) <;> norm_num
  let x11 : ℝ := Real.log x10
  have hx11 : Bounds (100353103 / 500000000) (200706207 / 1000000000) x11 := by
    exact bounds_log hx10 (by norm_num) (by simpa only [div_one] using reflection_log_1.1) (by simpa only [div_one] using reflection_log_1.2)
  let x12 : ℝ := x9*x11
  have hx12 : Bounds (245316296317 / 1000000000000) (245316297541 / 1000000000000) x12 := by
    apply bounds_mul hx9 hx11 <;> norm_num
  let x13 : ℝ := -(569 / 2560)
  have hx13 : Bounds (-569 / 2560) (-569 / 2560) x13 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((569 / 2560) : ℝ))
  let x14 : ℝ := (1 / 1)+x13
  have hx14 : Bounds (1991 / 2560) (1991 / 2560) x14 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx13 <;> norm_num
  let x15 : ℝ := (1 / 1)-(569 / 2560)
  have hx15 : Bounds (1991 / 2560) (1991 / 2560) x15 := by
    exact hx14
  let x16 : ℝ := -(569 / 2560)
  have hx16 : Bounds (-569 / 2560) (-569 / 2560) x16 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((569 / 2560) : ℝ))
  let x17 : ℝ := (1 / 1)+x16
  have hx17 : Bounds (1991 / 2560) (1991 / 2560) x17 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx16 <;> norm_num
  let x18 : ℝ := (1 / 1)-(569 / 2560)
  have hx18 : Bounds (1991 / 2560) (1991 / 2560) x18 := by
    exact hx17
  let x19 : ℝ := Real.log x18
  have hx19 : Bounds (-125685117 / 500000000) (-251370233 / 1000000000) x19 := by
    exact bounds_log hx18 (by norm_num) (by simpa only [div_one] using reflection_log_2.1) (by simpa only [div_one] using reflection_log_2.2)
  let x20 : ℝ := x15*x19
  have hx20 : Bounds (-97749635917 / 500000000000) (-39099854211 / 200000000000) x20 := by
    apply bounds_mul hx15 hx19 <;> norm_num
  let x21 : ℝ := x12+x20
  have hx21 : Bounds (49817024483 / 1000000000000) (24908513243 / 500000000000) x21 := by
    apply bounds_add hx12 hx20 <;> norm_num
  let x22 : ℝ := (2 / 1)⁻¹
  have hx22 : Bounds (1 / 2) (1 / 2) x22 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x23 : ℝ := x21*x22
  have hx23 : Bounds (24908512241 / 1000000000000) (24908513243 / 1000000000000) x23 := by
    apply bounds_mul hx21 hx22 <;> norm_num
  let x24 : ℝ := x21/(2 / 1)
  have hx24 : Bounds (24908512241 / 1000000000000) (24908513243 / 1000000000000) x24 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx23
  let x25 : ℝ := -x24
  have hx25 : Bounds (-24908513243 / 1000000000000) (-24908512241 / 1000000000000) x25 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx24
  let x26 : ℝ := x8+x25
  have hx26 : Bounds (668238666757 / 1000000000000) (668238668759 / 1000000000000) x26 := by
    apply bounds_add hx8 hx25 <;> norm_num
  let x27 : ℝ := x8-x24
  have hx27 : Bounds (668238666757 / 1000000000000) (668238668759 / 1000000000000) x27 := by
    exact hx26
  let x28 : ℝ := biasE (569 / 2560)
  have hx28 : Bounds (668238666757 / 1000000000000) (668238668759 / 1000000000000) x28 := by
    simpa +zetaDelta only [biasE, div_one] using hx27
  let x29 : ℝ := Real.log (2 / 1)
  have hx29 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x29 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x30 : ℝ := (1 / 1)+(2273 / 10240)
  have hx30 : Bounds (12513 / 10240) (12513 / 10240) x30 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((2273 / 10240) : ℝ)) <;> norm_num
  let x31 : ℝ := (1 / 1)+(2273 / 10240)
  have hx31 : Bounds (12513 / 10240) (12513 / 10240) x31 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((2273 / 10240) : ℝ)) <;> norm_num
  let x32 : ℝ := Real.log x31
  have hx32 : Bounds (50116621 / 250000000) (40093297 / 200000000) x32 := by
    exact bounds_log hx31 (by norm_num) (by simpa only [div_one] using reflection_log_3.1) (by simpa only [div_one] using reflection_log_3.2)
  let x33 : ℝ := x30*x32
  have hx33 : Bounds (122482280971 / 500000000000) (48992912633 / 200000000000) x33 := by
    apply bounds_mul hx30 hx32 <;> norm_num
  let x34 : ℝ := -(2273 / 10240)
  have hx34 : Bounds (-2273 / 10240) (-2273 / 10240) x34 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((2273 / 10240) : ℝ))
  let x35 : ℝ := (1 / 1)+x34
  have hx35 : Bounds (7967 / 10240) (7967 / 10240) x35 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx34 <;> norm_num
  let x36 : ℝ := (1 / 1)-(2273 / 10240)
  have hx36 : Bounds (7967 / 10240) (7967 / 10240) x36 := by
    exact hx35
  let x37 : ℝ := -(2273 / 10240)
  have hx37 : Bounds (-2273 / 10240) (-2273 / 10240) x37 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((2273 / 10240) : ℝ))
  let x38 : ℝ := (1 / 1)+x37
  have hx38 : Bounds (7967 / 10240) (7967 / 10240) x38 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx37 <;> norm_num
  let x39 : ℝ := (1 / 1)-(2273 / 10240)
  have hx39 : Bounds (7967 / 10240) (7967 / 10240) x39 := by
    exact hx38
  let x40 : ℝ := Real.log x39
  have hx40 : Bounds (-25099361 / 100000000) (-250993609 / 1000000000) x40 := by
    exact bounds_log hx39 (by norm_num) (by simpa only [div_one] using reflection_log_4.1) (by simpa only [div_one] using reflection_log_4.2)
  let x41 : ℝ := x36*x40
  have hx41 : Bounds (-195279891687 / 1000000000000) (-48819972727 / 250000000000) x41 := by
    apply bounds_mul hx36 hx40 <;> norm_num
  let x42 : ℝ := x33+x41
  have hx42 : Bounds (9936934051 / 200000000000) (49684672257 / 1000000000000) x42 := by
    apply bounds_add hx33 hx41 <;> norm_num
  let x43 : ℝ := (2 / 1)⁻¹
  have hx43 : Bounds (1 / 2) (1 / 2) x43 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x44 : ℝ := x42*x43
  have hx44 : Bounds (24842335127 / 1000000000000) (24842336129 / 1000000000000) x44 := by
    apply bounds_mul hx42 hx43 <;> norm_num
  let x45 : ℝ := x42/(2 / 1)
  have hx45 : Bounds (24842335127 / 1000000000000) (24842336129 / 1000000000000) x45 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx44
  let x46 : ℝ := -x45
  have hx46 : Bounds (-24842336129 / 1000000000000) (-24842335127 / 1000000000000) x46 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx45
  let x47 : ℝ := x29+x46
  have hx47 : Bounds (668304843871 / 1000000000000) (668304845873 / 1000000000000) x47 := by
    apply bounds_add hx29 hx46 <;> norm_num
  let x48 : ℝ := x29-x45
  have hx48 : Bounds (668304843871 / 1000000000000) (668304845873 / 1000000000000) x48 := by
    exact hx47
  let x49 : ℝ := biasE (2273 / 10240)
  have hx49 : Bounds (668304843871 / 1000000000000) (668304845873 / 1000000000000) x49 := by
    simpa +zetaDelta only [biasE, div_one] using hx48
  let x50 : ℝ := biasE x3
  have hx50 : Bounds (668238666757 / 1000000000000) (668304845873 / 1000000000000) x50 := by
    exact bounds_biasE hx3 (by norm_num) (by norm_num) hx28.1 hx49.2
  let x51 : ℝ := Real.log (2 / 1)
  have hx51 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x51 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x52 : ℝ := (1 / 1)+(569 / 1280)
  have hx52 : Bounds (1849 / 1280) (1849 / 1280) x52 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((569 / 1280) : ℝ)) <;> norm_num
  let x53 : ℝ := (1 / 1)+(569 / 1280)
  have hx53 : Bounds (1849 / 1280) (1849 / 1280) x53 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((569 / 1280) : ℝ)) <;> norm_num
  let x54 : ℝ := Real.log x53
  have hx54 : Bounds (183892437 / 500000000) (2942279 / 8000000) x54 := by
    exact bounds_log hx53 (by norm_num) (by simpa only [div_one] using reflection_log_5.1) (by simpa only [div_one] using reflection_log_5.2)
  let x55 : ℝ := x52*x54
  have hx55 : Bounds (53127674377 / 100000000000) (106255349043 / 200000000000) x55 := by
    apply bounds_mul hx52 hx54 <;> norm_num
  let x56 : ℝ := -(569 / 1280)
  have hx56 : Bounds (-569 / 1280) (-569 / 1280) x56 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((569 / 1280) : ℝ))
  let x57 : ℝ := (1 / 1)+x56
  have hx57 : Bounds (711 / 1280) (711 / 1280) x57 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx56 <;> norm_num
  let x58 : ℝ := (1 / 1)-(569 / 1280)
  have hx58 : Bounds (711 / 1280) (711 / 1280) x58 := by
    exact hx57
  let x59 : ℝ := -(569 / 1280)
  have hx59 : Bounds (-569 / 1280) (-569 / 1280) x59 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((569 / 1280) : ℝ))
  let x60 : ℝ := (1 / 1)+x59
  have hx60 : Bounds (711 / 1280) (711 / 1280) x60 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx59 <;> norm_num
  let x61 : ℝ := (1 / 1)-(569 / 1280)
  have hx61 : Bounds (711 / 1280) (711 / 1280) x61 := by
    exact hx60
  let x62 : ℝ := Real.log x61
  have hx62 : Bounds (-36746433 / 62500000) (-587942927 / 1000000000) x62 := by
    exact bounds_log hx61 (by norm_num) (by simpa only [div_one] using reflection_log_6.1) (by simpa only [div_one] using reflection_log_6.2)
  let x63 : ℝ := x58*x62
  have hx63 : Bounds (-40822990411 / 125000000000) (-81645980683 / 250000000000) x63 := by
    apply bounds_mul hx58 hx62 <;> norm_num
  let x64 : ℝ := x55+x63
  have hx64 : Bounds (102346410241 / 500000000000) (204692822483 / 1000000000000) x64 := by
    apply bounds_add hx55 hx63 <;> norm_num
  let x65 : ℝ := (2 / 1)⁻¹
  have hx65 : Bounds (1 / 2) (1 / 2) x65 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x66 : ℝ := x64*x65
  have hx66 : Bounds (102346410241 / 1000000000000) (51173205621 / 500000000000) x66 := by
    apply bounds_mul hx64 hx65 <;> norm_num
  let x67 : ℝ := x64/(2 / 1)
  have hx67 : Bounds (102346410241 / 1000000000000) (51173205621 / 500000000000) x67 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx66
  let x68 : ℝ := -x67
  have hx68 : Bounds (-51173205621 / 500000000000) (-102346410241 / 1000000000000) x68 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx67
  let x69 : ℝ := x51+x68
  have hx69 : Bounds (295400384379 / 500000000000) (590800770759 / 1000000000000) x69 := by
    apply bounds_add hx51 hx68 <;> norm_num
  let x70 : ℝ := x51-x67
  have hx70 : Bounds (295400384379 / 500000000000) (590800770759 / 1000000000000) x70 := by
    exact hx69
  let x71 : ℝ := biasE (569 / 1280)
  have hx71 : Bounds (295400384379 / 500000000000) (590800770759 / 1000000000000) x71 := by
    simpa +zetaDelta only [biasE, div_one] using hx70
  let x72 : ℝ := Real.log (2 / 1)
  have hx72 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x72 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x73 : ℝ := (1 / 1)+(2273 / 5120)
  have hx73 : Bounds (7393 / 5120) (7393 / 5120) x73 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((2273 / 5120) : ℝ)) <;> norm_num
  let x74 : ℝ := (1 / 1)+(2273 / 5120)
  have hx74 : Bounds (7393 / 5120) (7393 / 5120) x74 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((2273 / 5120) : ℝ)) <;> norm_num
  let x75 : ℝ := Real.log x74
  have hx75 : Bounds (367379167 / 1000000000) (11480599 / 31250000) x75 := by
    exact bounds_log hx74 (by norm_num) (by simpa only [div_one] using reflection_log_7.1) (by simpa only [div_one] using reflection_log_7.2)
  let x76 : ℝ := x73*x75
  have hx76 : Bounds (530475426099 / 1000000000000) (66309428443 / 125000000000) x76 := by
    apply bounds_mul hx73 hx75 <;> norm_num
  let x77 : ℝ := -(2273 / 5120)
  have hx77 : Bounds (-2273 / 5120) (-2273 / 5120) x77 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((2273 / 5120) : ℝ))
  let x78 : ℝ := (1 / 1)+x77
  have hx78 : Bounds (2847 / 5120) (2847 / 5120) x78 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx77 <;> norm_num
  let x79 : ℝ := (1 / 1)-(2273 / 5120)
  have hx79 : Bounds (2847 / 5120) (2847 / 5120) x79 := by
    exact hx78
  let x80 : ℝ := -(2273 / 5120)
  have hx80 : Bounds (-2273 / 5120) (-2273 / 5120) x80 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((2273 / 5120) : ℝ))
  let x81 : ℝ := (1 / 1)+x80
  have hx81 : Bounds (2847 / 5120) (2847 / 5120) x81 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx80 <;> norm_num
  let x82 : ℝ := (1 / 1)-(2273 / 5120)
  have hx82 : Bounds (2847 / 5120) (2847 / 5120) x82 := by
    exact hx81
  let x83 : ℝ := Real.log x82
  have hx83 : Bounds (-586888631 / 1000000000) (-58688863 / 100000000) x83 := by
    exact bounds_log hx82 (by norm_num) (by simpa only [div_one] using reflection_log_8.1) (by simpa only [div_one] using reflection_log_8.2)
  let x84 : ℝ := x79*x83
  have hx84 : Bounds (-326342174309 / 1000000000000) (-326342173751 / 1000000000000) x84 := by
    apply bounds_mul hx79 hx83 <;> norm_num
  let x85 : ℝ := x76+x84
  have hx85 : Bounds (20413325179 / 100000000000) (204133253793 / 1000000000000) x85 := by
    apply bounds_add hx76 hx84 <;> norm_num
  let x86 : ℝ := (2 / 1)⁻¹
  have hx86 : Bounds (1 / 2) (1 / 2) x86 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x87 : ℝ := x85*x86
  have hx87 : Bounds (20413325179 / 200000000000) (102066626897 / 1000000000000) x87 := by
    apply bounds_mul hx85 hx86 <;> norm_num
  let x88 : ℝ := x85/(2 / 1)
  have hx88 : Bounds (20413325179 / 200000000000) (102066626897 / 1000000000000) x88 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx87
  let x89 : ℝ := -x88
  have hx89 : Bounds (-102066626897 / 1000000000000) (-20413325179 / 200000000000) x89 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx88
  let x90 : ℝ := x72+x89
  have hx90 : Bounds (591080553103 / 1000000000000) (118216111021 / 200000000000) x90 := by
    apply bounds_add hx72 hx89 <;> norm_num
  let x91 : ℝ := x72-x88
  have hx91 : Bounds (591080553103 / 1000000000000) (118216111021 / 200000000000) x91 := by
    exact hx90
  let x92 : ℝ := biasE (2273 / 5120)
  have hx92 : Bounds (591080553103 / 1000000000000) (118216111021 / 200000000000) x92 := by
    simpa +zetaDelta only [biasE, div_one] using hx91
  let x93 : ℝ := biasE x7
  have hx93 : Bounds (295400384379 / 500000000000) (118216111021 / 200000000000) x93 := by
    exact bounds_biasE hx7 (by norm_num) (by norm_num) hx71.1 hx92.2
  let x94 : ℝ := Real.log (2 / 1)
  have hx94 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x94 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x95 : ℝ := x94+x93
  have hx95 : Bounds (641973974379 / 500000000000) (256845547221 / 200000000000) x95 := by
    apply bounds_add hx94 hx93 <;> norm_num
  let x96 : ℝ := (2 / 1)⁻¹
  have hx96 : Bounds (1 / 2) (1 / 2) x96 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x97 : ℝ := x95*x96
  have hx97 : Bounds (641973974379 / 1000000000000) (642113868053 / 1000000000000) x97 := by
    apply bounds_mul hx95 hx96 <;> norm_num
  let x98 : ℝ := x95/(2 / 1)
  have hx98 : Bounds (641973974379 / 1000000000000) (642113868053 / 1000000000000) x98 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx97
  let x99 : ℝ := Real.log (2 / 1)
  have hx99 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x99 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x100 : ℝ := (1 / 1)+(31673 / 100000)
  have hx100 : Bounds (131673 / 100000) (131673 / 100000) x100 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((31673 / 100000) : ℝ)) <;> norm_num
  let x101 : ℝ := (1 / 1)+(31673 / 100000)
  have hx101 : Bounds (131673 / 100000) (131673 / 100000) x101 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((31673 / 100000) : ℝ)) <;> norm_num
  let x102 : ℝ := Real.log x101
  have hx102 : Bounds (27515139 / 100000000) (275151391 / 1000000000) x102 := by
    exact bounds_log hx101 (by norm_num) (by simpa only [div_one] using reflection_log_9.1) (by simpa only [div_one] using reflection_log_9.2)
  let x103 : ℝ := x100*x102
  have hx103 : Bounds (181150044877 / 500000000000) (5660938923 / 15625000000) x103 := by
    apply bounds_mul hx100 hx102 <;> norm_num
  let x104 : ℝ := -(31673 / 100000)
  have hx104 : Bounds (-31673 / 100000) (-31673 / 100000) x104 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((31673 / 100000) : ℝ))
  let x105 : ℝ := (1 / 1)+x104
  have hx105 : Bounds (68327 / 100000) (68327 / 100000) x105 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx104 <;> norm_num
  let x106 : ℝ := (1 / 1)-(31673 / 100000)
  have hx106 : Bounds (68327 / 100000) (68327 / 100000) x106 := by
    exact hx105
  let x107 : ℝ := -(31673 / 100000)
  have hx107 : Bounds (-31673 / 100000) (-31673 / 100000) x107 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((31673 / 100000) : ℝ))
  let x108 : ℝ := (1 / 1)+x107
  have hx108 : Bounds (68327 / 100000) (68327 / 100000) x108 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx107 <;> norm_num
  let x109 : ℝ := (1 / 1)-(31673 / 100000)
  have hx109 : Bounds (68327 / 100000) (68327 / 100000) x109 := by
    exact hx108
  let x110 : ℝ := Real.log x109
  have hx110 : Bounds (-380865183 / 1000000000) (-190432591 / 500000000) x110 := by
    exact bounds_log hx109 (by norm_num) (by simpa only [div_one] using reflection_log_10.1) (by simpa only [div_one] using reflection_log_10.2)
  let x111 : ℝ := x106*x110
  have hx111 : Bounds (-260233753589 / 1000000000000) (-52046750581 / 200000000000) x111 := by
    apply bounds_mul hx106 hx110 <;> norm_num
  let x112 : ℝ := x103+x111
  have hx112 : Bounds (20413267233 / 200000000000) (102066338167 / 1000000000000) x112 := by
    apply bounds_add hx103 hx111 <;> norm_num
  let x113 : ℝ := (2 / 1)⁻¹
  have hx113 : Bounds (1 / 2) (1 / 2) x113 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x114 : ℝ := x112*x113
  have hx114 : Bounds (25516584041 / 500000000000) (12758292271 / 250000000000) x114 := by
    apply bounds_mul hx112 hx113 <;> norm_num
  let x115 : ℝ := x112/(2 / 1)
  have hx115 : Bounds (25516584041 / 500000000000) (12758292271 / 250000000000) x115 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx114
  let x116 : ℝ := -x115
  have hx116 : Bounds (-12758292271 / 250000000000) (-25516584041 / 500000000000) x116 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx115
  let x117 : ℝ := x99+x116
  have hx117 : Bounds (160528502729 / 250000000000) (321057006459 / 500000000000) x117 := by
    apply bounds_add hx99 hx116 <;> norm_num
  let x118 : ℝ := x99-x115
  have hx118 : Bounds (160528502729 / 250000000000) (321057006459 / 500000000000) x118 := by
    exact hx117
  let x119 : ℝ := biasE (31673 / 100000)
  have hx119 : Bounds (160528502729 / 250000000000) (321057006459 / 500000000000) x119 := by
    simpa +zetaDelta only [biasE, div_one] using hx118
  let x120 : ℝ := Real.log (2 / 1)
  have hx120 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x120 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x121 : ℝ := (1 / 1)+(317157 / 1000000)
  have hx121 : Bounds (1317157 / 1000000) (1317157 / 1000000) x121 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((317157 / 1000000) : ℝ)) <;> norm_num
  let x122 : ℝ := (1 / 1)+(317157 / 1000000)
  have hx122 : Bounds (1317157 / 1000000) (1317157 / 1000000) x122 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((317157 / 1000000) : ℝ)) <;> norm_num
  let x123 : ℝ := Real.log x122
  have hx123 : Bounds (440761 / 1600000) (137737813 / 500000000) x123 := by
    exact bounds_log hx122 (by norm_num) (by simpa only [div_one] using reflection_log_11.1) (by simpa only [div_one] using reflection_log_11.2)
  let x124 : ℝ := x121*x123
  have hx124 : Bounds (181422323899 / 500000000000) (90711162279 / 250000000000) x124 := by
    apply bounds_mul hx121 hx123 <;> norm_num
  let x125 : ℝ := -(317157 / 1000000)
  have hx125 : Bounds (-317157 / 1000000) (-317157 / 1000000) x125 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((317157 / 1000000) : ℝ))
  let x126 : ℝ := (1 / 1)+x125
  have hx126 : Bounds (682843 / 1000000) (682843 / 1000000) x126 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx125 <;> norm_num
  let x127 : ℝ := (1 / 1)-(317157 / 1000000)
  have hx127 : Bounds (682843 / 1000000) (682843 / 1000000) x127 := by
    exact hx126
  let x128 : ℝ := -(317157 / 1000000)
  have hx128 : Bounds (-317157 / 1000000) (-317157 / 1000000) x128 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((317157 / 1000000) : ℝ))
  let x129 : ℝ := (1 / 1)+x128
  have hx129 : Bounds (682843 / 1000000) (682843 / 1000000) x129 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx128 <;> norm_num
  let x130 : ℝ := (1 / 1)-(317157 / 1000000)
  have hx130 : Bounds (682843 / 1000000) (682843 / 1000000) x130 := by
    exact hx129
  let x131 : ℝ := Real.log x130
  have hx131 : Bounds (-76298063 / 200000000) (-190745157 / 500000000) x131 := by
    exact bounds_log hx130 (by norm_num) (by simpa only [div_one] using reflection_log_12.1) (by simpa only [div_one] using reflection_log_12.2)
  let x132 : ℝ := x127*x131
  have hx132 : Bounds (-130248995583 / 500000000000) (-130248995241 / 500000000000) x132 := by
    apply bounds_mul hx127 hx131 <;> norm_num
  let x133 : ℝ := x124+x132
  have hx133 : Bounds (12793332079 / 125000000000) (51173329317 / 500000000000) x133 := by
    apply bounds_add hx124 hx132 <;> norm_num
  let x134 : ℝ := (2 / 1)⁻¹
  have hx134 : Bounds (1 / 2) (1 / 2) x134 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x135 : ℝ := x133*x134
  have hx135 : Bounds (12793332079 / 250000000000) (51173329317 / 1000000000000) x135 := by
    apply bounds_mul hx133 hx134 <;> norm_num
  let x136 : ℝ := x133/(2 / 1)
  have hx136 : Bounds (12793332079 / 250000000000) (51173329317 / 1000000000000) x136 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx135
  let x137 : ℝ := -x136
  have hx137 : Bounds (-51173329317 / 1000000000000) (-12793332079 / 250000000000) x137 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx136
  let x138 : ℝ := x120+x137
  have hx138 : Bounds (641973850683 / 1000000000000) (160493463171 / 250000000000) x138 := by
    apply bounds_add hx120 hx137 <;> norm_num
  let x139 : ℝ := x120-x136
  have hx139 : Bounds (641973850683 / 1000000000000) (160493463171 / 250000000000) x139 := by
    exact hx138
  let x140 : ℝ := biasE (317157 / 1000000)
  have hx140 : Bounds (641973850683 / 1000000000000) (160493463171 / 250000000000) x140 := by
    simpa +zetaDelta only [biasE, div_one] using hx139
  let y : ℝ := 1 - 2 * entropyInverse ((1 + H (2*m - 1/2))/2)
  have hLh' : Real.log 2 * ((1 + H (2*m - 1/2))/2) = x98 := by
    simpa +zetaDelta only [div_one] using hLh
  have hy : Bounds (31673 / 100000) (317157 / 1000000) y := by
    apply entropyInverseBias_bracket
    · exact div_nonneg (add_nonneg zero_le_one
        (H_nonneg (by linarith [hm.1]) (by linarith [hm.2]))) two_pos.le
    · linarith [H_le_one (2*m-1/2)]
    · norm_num
    · norm_num
    · norm_num
    · have h1 : biasE (317157 / 1000000) ≤ (160493463171 / 250000000000) := hx140.2
      have h2 : (641973974379 / 1000000000000) ≤ x98 := hx98.1
      linarith [hLh']
    · have h1 : x98 ≤ (642113868053 / 1000000000000) := hx98.2
      have h2 : (160528502729 / 250000000000) ≤ biasE (31673 / 100000) := hx119.1
      linarith [hLh']
  let x141 : ℝ := x3⁻¹
  have hx141 : Bounds (4499121265377 / 1000000000000) (4505059392873 / 1000000000000) x141 := by
    apply bounds_inv hx3 <;> norm_num
  let x142 : ℝ := x98*x141
  have hx142 : Bounds (2888318759947 / 1000000000000) (2892761112567 / 1000000000000) x142 := by
    apply bounds_mul hx98 hx141 <;> norm_num
  let x143 : ℝ := x98/x3
  have hx143 : Bounds (2888318759947 / 1000000000000) (2892761112567 / 1000000000000) x143 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx142
  let x144 : ℝ := Real.log (2 / 1)
  have hx144 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x144 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x145 : ℝ := (1 / 1)+(230359 / 1000000)
  have hx145 : Bounds (1230359 / 1000000) (1230359 / 1000000) x145 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((230359 / 1000000) : ℝ)) <;> norm_num
  let x146 : ℝ := (1 / 1)+(230359 / 1000000)
  have hx146 : Bounds (1230359 / 1000000) (1230359 / 1000000) x146 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((230359 / 1000000) : ℝ)) <;> norm_num
  let x147 : ℝ := Real.log x146
  have hx147 : Bounds (51826499 / 250000000) (207305997 / 1000000000) x147 := by
    exact bounds_log hx146 (by norm_num) (by simpa only [div_one] using reflection_log_13.1) (by simpa only [div_one] using reflection_log_13.2)
  let x148 : ℝ := x145*x147
  have hx148 : Bounds (63765199483 / 250000000000) (255060799163 / 1000000000000) x148 := by
    apply bounds_mul hx145 hx147 <;> norm_num
  let x149 : ℝ := -(230359 / 1000000)
  have hx149 : Bounds (-230359 / 1000000) (-230359 / 1000000) x149 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((230359 / 1000000) : ℝ))
  let x150 : ℝ := (1 / 1)+x149
  have hx150 : Bounds (769641 / 1000000) (769641 / 1000000) x150 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx149 <;> norm_num
  let x151 : ℝ := (1 / 1)-(230359 / 1000000)
  have hx151 : Bounds (769641 / 1000000) (769641 / 1000000) x151 := by
    exact hx150
  let x152 : ℝ := -(230359 / 1000000)
  have hx152 : Bounds (-230359 / 1000000) (-230359 / 1000000) x152 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((230359 / 1000000) : ℝ))
  let x153 : ℝ := (1 / 1)+x152
  have hx153 : Bounds (769641 / 1000000) (769641 / 1000000) x153 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx152 <;> norm_num
  let x154 : ℝ := (1 / 1)-(230359 / 1000000)
  have hx154 : Bounds (769641 / 1000000) (769641 / 1000000) x154 := by
    exact hx153
  let x155 : ℝ := Real.log x154
  have hx155 : Bounds (-261831107 / 1000000000) (-130915553 / 500000000) x155 := by
    exact bounds_log hx154 (by norm_num) (by simpa only [div_one] using reflection_log_14.1) (by simpa only [div_one] using reflection_log_14.2)
  let x156 : ℝ := x151*x155
  have hx156 : Bounds (-201515955023 / 1000000000000) (-50378988563 / 250000000000) x156 := by
    apply bounds_mul hx151 hx155 <;> norm_num
  let x157 : ℝ := x148+x156
  have hx157 : Bounds (53544842909 / 1000000000000) (53544844911 / 1000000000000) x157 := by
    apply bounds_add hx148 hx156 <;> norm_num
  let x158 : ℝ := (2 / 1)⁻¹
  have hx158 : Bounds (1 / 2) (1 / 2) x158 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x159 : ℝ := x157*x158
  have hx159 : Bounds (13386210727 / 500000000000) (3346552807 / 125000000000) x159 := by
    apply bounds_mul hx157 hx158 <;> norm_num
  let x160 : ℝ := x157/(2 / 1)
  have hx160 : Bounds (13386210727 / 500000000000) (3346552807 / 125000000000) x160 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx159
  let x161 : ℝ := -x160
  have hx161 : Bounds (-3346552807 / 125000000000) (-13386210727 / 500000000000) x161 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx160
  let x162 : ℝ := x144+x161
  have hx162 : Bounds (83296844693 / 125000000000) (333187379773 / 500000000000) x162 := by
    apply bounds_add hx144 hx161 <;> norm_num
  let x163 : ℝ := x144-x160
  have hx163 : Bounds (83296844693 / 125000000000) (333187379773 / 500000000000) x163 := by
    exact hx162
  let x164 : ℝ := biasE (230359 / 1000000)
  have hx164 : Bounds (83296844693 / 125000000000) (333187379773 / 500000000000) x164 := by
    simpa +zetaDelta only [biasE, div_one] using hx163
  let x165 : ℝ := Real.log (2 / 1)
  have hx165 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x165 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x166 : ℝ := (1 / 1)+(7209 / 31250)
  have hx166 : Bounds (38459 / 31250) (38459 / 31250) x166 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((7209 / 31250) : ℝ)) <;> norm_num
  let x167 : ℝ := (1 / 1)+(7209 / 31250)
  have hx167 : Bounds (38459 / 31250) (38459 / 31250) x167 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((7209 / 31250) : ℝ)) <;> norm_num
  let x168 : ℝ := Real.log x167
  have hx168 : Bounds (103786681 / 500000000) (207573363 / 1000000000) x168 := by
    exact bounds_log hx167 (by norm_num) (by simpa only [div_one] using reflection_log_15.1) (by simpa only [div_one] using reflection_log_15.2)
  let x169 : ℝ := x166*x168
  have hx169 : Bounds (255458045733 / 1000000000000) (63864511741 / 250000000000) x169 := by
    apply bounds_mul hx166 hx168 <;> norm_num
  let x170 : ℝ := -(7209 / 31250)
  have hx170 : Bounds (-7209 / 31250) (-7209 / 31250) x170 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((7209 / 31250) : ℝ))
  let x171 : ℝ := (1 / 1)+x170
  have hx171 : Bounds (24041 / 31250) (24041 / 31250) x171 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx170 <;> norm_num
  let x172 : ℝ := (1 / 1)-(7209 / 31250)
  have hx172 : Bounds (24041 / 31250) (24041 / 31250) x172 := by
    exact hx171
  let x173 : ℝ := -(7209 / 31250)
  have hx173 : Bounds (-7209 / 31250) (-7209 / 31250) x173 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((7209 / 31250) : ℝ))
  let x174 : ℝ := (1 / 1)+x173
  have hx174 : Bounds (24041 / 31250) (24041 / 31250) x174 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx173 <;> norm_num
  let x175 : ℝ := (1 / 1)-(7209 / 31250)
  have hx175 : Bounds (24041 / 31250) (24041 / 31250) x175 := by
    exact hx174
  let x176 : ℝ := Real.log x175
  have hx176 : Bounds (-262258671 / 1000000000) (-26225867 / 100000000) x176 := by
    exact bounds_log hx175 (by norm_num) (by simpa only [div_one] using reflection_log_16.1) (by simpa only [div_one] using reflection_log_16.2)
  let x177 : ℝ := x172*x176
  have hx177 : Bounds (-40351748541 / 200000000000) (-40351748387 / 200000000000) x177 := by
    apply bounds_mul hx172 hx176 <;> norm_num
  let x178 : ℝ := x169+x177
  have hx178 : Bounds (13424825757 / 250000000000) (53699305029 / 1000000000000) x178 := by
    apply bounds_add hx169 hx177 <;> norm_num
  let x179 : ℝ := (2 / 1)⁻¹
  have hx179 : Bounds (1 / 2) (1 / 2) x179 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x180 : ℝ := x178*x179
  have hx180 : Bounds (13424825757 / 500000000000) (5369930503 / 200000000000) x180 := by
    apply bounds_mul hx178 hx179 <;> norm_num
  let x181 : ℝ := x178/(2 / 1)
  have hx181 : Bounds (13424825757 / 500000000000) (5369930503 / 200000000000) x181 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx180
  let x182 : ℝ := -x181
  have hx182 : Bounds (-5369930503 / 200000000000) (-13424825757 / 500000000000) x182 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx181
  let x183 : ℝ := x165+x182
  have hx183 : Bounds (133259505497 / 200000000000) (333148764743 / 500000000000) x183 := by
    apply bounds_add hx165 hx182 <;> norm_num
  let x184 : ℝ := x165-x181
  have hx184 : Bounds (133259505497 / 200000000000) (333148764743 / 500000000000) x184 := by
    exact hx183
  let x185 : ℝ := biasE (7209 / 31250)
  have hx185 : Bounds (133259505497 / 200000000000) (333148764743 / 500000000000) x185 := by
    simpa +zetaDelta only [biasE, div_one] using hx184
  let x186 : ℝ := x143*(230359 / 1000000)
  have hx186 : Bounds (332675110611 / 500000000000) (66637355713 / 100000000000) x186 := by
    apply bounds_mul hx143 (bounds_const ((230359 / 1000000) : ℝ)) <;> norm_num
  let x187 : ℝ := x143*(7209 / 31250)
  have hx187 : Bounds (333150239047 / 500000000000) (41707829721 / 62500000000) x187 := by
    apply bounds_mul hx143 (bounds_const ((7209 / 31250) : ℝ)) <;> norm_num
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
  have hc : Bounds (230359 / 1000000) (7209 / 31250) c := by
    apply contact_bracket hc0 hcMem.2.le (by norm_num) (by norm_num) (by norm_num)
      (show 0 < x143 by linarith [hx143.1]) hcEq
    · have h1 : x143 * (230359 / 1000000) ≤ (66637355713 / 100000000000) := hx186.2
      have h2 : (83296844693 / 125000000000) ≤ biasE (230359 / 1000000) := hx164.1
      linarith
    · have h1 : biasE (7209 / 31250) ≤ (333148764743 / 500000000000) := hx185.2
      have h2 : (333150239047 / 500000000000) ≤ x143 * (7209 / 31250) := hx187.1
      linarith
  let x188 : ℝ := (1 / 1)+y
  have hx188 : Bounds (131673 / 100000) (1317157 / 1000000) x188 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hy <;> norm_num
  let x189 : ℝ := -y
  have hx189 : Bounds (-317157 / 1000000) (-31673 / 100000) x189 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hy
  let x190 : ℝ := (1 / 1)+x189
  have hx190 : Bounds (682843 / 1000000) (68327 / 100000) x190 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx189 <;> norm_num
  let x191 : ℝ := (1 / 1)-y
  have hx191 : Bounds (682843 / 1000000) (68327 / 100000) x191 := by
    exact hx190
  let x192 : ℝ := x191⁻¹
  have hx192 : Bounds (1463550280269 / 1000000000000) (91529092339 / 62500000000) x192 := by
    apply bounds_inv hx191 <;> norm_num
  let x193 : ℝ := x188*x192
  have hx193 : Bounds (963550280269 / 500000000000) (60279092339 / 31250000000) x193 := by
    apply bounds_mul hx188 hx192 <;> norm_num
  let x194 : ℝ := x188/x191
  have hx194 : Bounds (963550280269 / 500000000000) (60279092339 / 31250000000) x194 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx193
  let x195 : ℝ := Real.log x194
  have hx195 : Bounds (656016573 / 1000000000) (656965941 / 1000000000) x195 := by
    exact bounds_log hx194 (by norm_num) (by simpa only [div_one] using reflection_log_17.1) (by simpa only [div_one] using reflection_log_18.2)
  let x196 : ℝ := (2 / 1)⁻¹
  have hx196 : Bounds (1 / 2) (1 / 2) x196 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x197 : ℝ := x195*x196
  have hx197 : Bounds (656016573 / 2000000000) (656965941 / 2000000000) x197 := by
    apply bounds_mul hx195 hx196 <;> norm_num
  let x198 : ℝ := x195/(2 / 1)
  have hx198 : Bounds (656016573 / 2000000000) (656965941 / 2000000000) x198 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx197
  let x199 : ℝ := (1 / 1)+c
  have hx199 : Bounds (1230359 / 1000000) (38459 / 31250) x199 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hc <;> norm_num
  let x200 : ℝ := -c
  have hx200 : Bounds (-7209 / 31250) (-230359 / 1000000) x200 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hc
  let x201 : ℝ := (1 / 1)+x200
  have hx201 : Bounds (24041 / 31250) (769641 / 1000000) x201 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx200 <;> norm_num
  let x202 : ℝ := (1 / 1)-c
  have hx202 : Bounds (24041 / 31250) (769641 / 1000000) x202 := by
    exact hx201
  let x203 : ℝ := x202⁻¹
  have hx203 : Bounds (649653539767 / 500000000000) (40620710453 / 31250000000) x203 := by
    apply bounds_inv hx202 <;> norm_num
  let x204 : ℝ := x199*x203
  have hx204 : Bounds (399653539767 / 250000000000) (24995710453 / 15625000000) x204 := by
    apply bounds_mul hx199 hx203 <;> norm_num
  let x205 : ℝ := x199/x202
  have hx205 : Bounds (399653539767 / 250000000000) (24995710453 / 15625000000) x205 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx204
  let x206 : ℝ := Real.log x205
  have hx206 : Bounds (469137103 / 1000000000) (469832033 / 1000000000) x206 := by
    exact bounds_log hx205 (by norm_num) (by simpa only [div_one] using reflection_log_19.1) (by simpa only [div_one] using reflection_log_20.2)
  let x207 : ℝ := (2 / 1)⁻¹
  have hx207 : Bounds (1 / 2) (1 / 2) x207 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x208 : ℝ := x206*x207
  have hx208 : Bounds (469137103 / 2000000000) (469832033 / 2000000000) x208 := by
    apply bounds_mul hx206 hx207 <;> norm_num
  let x209 : ℝ := x206/(2 / 1)
  have hx209 : Bounds (469137103 / 2000000000) (469832033 / 2000000000) x209 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx208
  let x210 : ℝ := (2 / 1)*x50
  have hx210 : Bounds (668238666757 / 500000000000) (668304845873 / 500000000000) x210 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx50 <;> norm_num
  let x211 : ℝ := (2 / 1)*x98
  have hx211 : Bounds (641973974379 / 500000000000) (642113868053 / 500000000000) x211 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx98 <;> norm_num
  let x212 : ℝ := -x211
  have hx212 : Bounds (-642113868053 / 500000000000) (-641973974379 / 500000000000) x212 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx211
  let x213 : ℝ := x210+x212
  have hx213 : Bounds (1632799919 / 31250000000) (13165435747 / 250000000000) x213 := by
    apply bounds_add hx210 hx212 <;> norm_num
  let x214 : ℝ := x210-x211
  have hx214 : Bounds (1632799919 / 31250000000) (13165435747 / 250000000000) x214 := by
    exact hx213
  let x215 : ℝ := y*x198
  have hx215 : Bounds (103890064583 / 1000000000000) (4167226939 / 40000000000) x215 := by
    apply bounds_mul hy hx198 <;> norm_num
  let x216 : ℝ := -x215
  have hx216 : Bounds (-4167226939 / 40000000000) (-103890064583 / 1000000000000) x216 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx215
  let x217 : ℝ := x214+x216
  have hx217 : Bounds (-51931076067 / 1000000000000) (-10245664319 / 200000000000) x217 := by
    apply bounds_add hx214 hx216 <;> norm_num
  let x218 : ℝ := x214-x215
  have hx218 : Bounds (-51931076067 / 1000000000000) (-10245664319 / 200000000000) x218 := by
    exact hx217
  let x219 : ℝ := x3*x209
  have hx219 : Bounds (52067804449 / 1000000000000) (5221375523 / 100000000000) x219 := by
    apply bounds_mul hx3 hx209 <;> norm_num
  let x220 : ℝ := x218+x219
  have hx220 : Bounds (68364191 / 500000000000) (197086727 / 200000000000) x220 := by
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

theorem acceptedCertificate : DoubleCapBiasCellCertificate (1991 / 5120) (7967 / 20480) (fun m => (1 + H (2*m - 1/2))/2) where
  domain := by norm_num
  sound m hmLo hmHi := by
    exact cell_bias_nonneg m ⟨hmLo, hmHi⟩

theorem accepted_cell :
    ∀ m, (1991 / 5120) ≤ m → m ≤ (7967 / 20480) → 0 ≤ doubleCapHighResidual m := by
  intro m hmLo hmHi
  unfold doubleCapHighResidual
  apply doubleCapEndpointResidual_nonneg_of_biasCell acceptedCertificate hmLo hmHi
  exact div_pos (by linarith [H_nonneg (by linarith : 0 ≤ 2*m-1/2) (by linarith : 2*m-1/2 ≤ 1)]) two_pos

#print axioms cell_bias_nonneg
#print axioms accepted_cell

end GeneralCK.Certificates.DoubleCapMiddle.Cell0398

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0399 =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0399
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Reflection
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem cell_bias_nonneg (m : ℝ) (hm : Bounds (7967 / 20480) (797 / 2048) m) :
    let h := (1 + H (2*m - 1/2))/2
    let x := 1-2*m
    let y := 1-2*entropyInverse h
    let c := regularContact (x/(Real.log 2*h))
    0 ≤ 2*(biasE x-Real.log 2*h)-y*SmallMean.A y+x*SmallMean.A c := by
  have hEq : biasE (2-4*m) = Real.log 2 * H (2*m-1/2) := by
    have hmstrict : 1/4 < m := by
      have hlo : (1/4 : ℝ) < (7967 / 20480) := by norm_num
      exact lt_of_lt_of_le hlo hm.1
    rw [show 2-4*m = 1-2*(2*m-1/2) by ring,
      GeneralCK.Correction.Natural.biasE_probability (by linarith [hmstrict]) (by linarith [hm.2]),
      GeneralCK.Certificates.Mixed.hn_eq_H_mul_log]
    ring
  have hLh : Real.log 2 * ((1 + H (2*m - 1/2))/2) = (Real.log 2 + biasE (2-4*m))/2 := by
    rw [hEq]
    ring
  let x0 : ℝ := (2 / 1)*m
  have hx0 : Bounds (7967 / 10240) (797 / 1024) x0 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hm <;> norm_num
  let x1 : ℝ := -x0
  have hx1 : Bounds (-797 / 1024) (-7967 / 10240) x1 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx0
  let x2 : ℝ := (1 / 1)+x1
  have hx2 : Bounds (227 / 1024) (2273 / 10240) x2 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx1 <;> norm_num
  let x3 : ℝ := (1 / 1)-x0
  have hx3 : Bounds (227 / 1024) (2273 / 10240) x3 := by
    exact hx2
  let x4 : ℝ := (4 / 1)*m
  have hx4 : Bounds (7967 / 5120) (797 / 512) x4 := by
    apply bounds_mul (bounds_const ((4 / 1) : ℝ)) hm <;> norm_num
  let x5 : ℝ := -x4
  have hx5 : Bounds (-797 / 512) (-7967 / 5120) x5 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx4
  let x6 : ℝ := (2 / 1)+x5
  have hx6 : Bounds (227 / 512) (2273 / 5120) x6 := by
    apply bounds_add (bounds_const ((2 / 1) : ℝ)) hx5 <;> norm_num
  let x7 : ℝ := (2 / 1)-x4
  have hx7 : Bounds (227 / 512) (2273 / 5120) x7 := by
    exact hx6
  let x8 : ℝ := Real.log (2 / 1)
  have hx8 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x8 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x9 : ℝ := (1 / 1)+(2273 / 10240)
  have hx9 : Bounds (12513 / 10240) (12513 / 10240) x9 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((2273 / 10240) : ℝ)) <;> norm_num
  let x10 : ℝ := (1 / 1)+(2273 / 10240)
  have hx10 : Bounds (12513 / 10240) (12513 / 10240) x10 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((2273 / 10240) : ℝ)) <;> norm_num
  let x11 : ℝ := Real.log x10
  have hx11 : Bounds (50116621 / 250000000) (40093297 / 200000000) x11 := by
    exact bounds_log hx10 (by norm_num) (by simpa only [div_one] using reflection_log_1.1) (by simpa only [div_one] using reflection_log_1.2)
  let x12 : ℝ := x9*x11
  have hx12 : Bounds (122482280971 / 500000000000) (48992912633 / 200000000000) x12 := by
    apply bounds_mul hx9 hx11 <;> norm_num
  let x13 : ℝ := -(2273 / 10240)
  have hx13 : Bounds (-2273 / 10240) (-2273 / 10240) x13 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((2273 / 10240) : ℝ))
  let x14 : ℝ := (1 / 1)+x13
  have hx14 : Bounds (7967 / 10240) (7967 / 10240) x14 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx13 <;> norm_num
  let x15 : ℝ := (1 / 1)-(2273 / 10240)
  have hx15 : Bounds (7967 / 10240) (7967 / 10240) x15 := by
    exact hx14
  let x16 : ℝ := -(2273 / 10240)
  have hx16 : Bounds (-2273 / 10240) (-2273 / 10240) x16 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((2273 / 10240) : ℝ))
  let x17 : ℝ := (1 / 1)+x16
  have hx17 : Bounds (7967 / 10240) (7967 / 10240) x17 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx16 <;> norm_num
  let x18 : ℝ := (1 / 1)-(2273 / 10240)
  have hx18 : Bounds (7967 / 10240) (7967 / 10240) x18 := by
    exact hx17
  let x19 : ℝ := Real.log x18
  have hx19 : Bounds (-25099361 / 100000000) (-250993609 / 1000000000) x19 := by
    exact bounds_log hx18 (by norm_num) (by simpa only [div_one] using reflection_log_2.1) (by simpa only [div_one] using reflection_log_2.2)
  let x20 : ℝ := x15*x19
  have hx20 : Bounds (-195279891687 / 1000000000000) (-48819972727 / 250000000000) x20 := by
    apply bounds_mul hx15 hx19 <;> norm_num
  let x21 : ℝ := x12+x20
  have hx21 : Bounds (9936934051 / 200000000000) (49684672257 / 1000000000000) x21 := by
    apply bounds_add hx12 hx20 <;> norm_num
  let x22 : ℝ := (2 / 1)⁻¹
  have hx22 : Bounds (1 / 2) (1 / 2) x22 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x23 : ℝ := x21*x22
  have hx23 : Bounds (24842335127 / 1000000000000) (24842336129 / 1000000000000) x23 := by
    apply bounds_mul hx21 hx22 <;> norm_num
  let x24 : ℝ := x21/(2 / 1)
  have hx24 : Bounds (24842335127 / 1000000000000) (24842336129 / 1000000000000) x24 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx23
  let x25 : ℝ := -x24
  have hx25 : Bounds (-24842336129 / 1000000000000) (-24842335127 / 1000000000000) x25 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx24
  let x26 : ℝ := x8+x25
  have hx26 : Bounds (668304843871 / 1000000000000) (668304845873 / 1000000000000) x26 := by
    apply bounds_add hx8 hx25 <;> norm_num
  let x27 : ℝ := x8-x24
  have hx27 : Bounds (668304843871 / 1000000000000) (668304845873 / 1000000000000) x27 := by
    exact hx26
  let x28 : ℝ := biasE (2273 / 10240)
  have hx28 : Bounds (668304843871 / 1000000000000) (668304845873 / 1000000000000) x28 := by
    simpa +zetaDelta only [biasE, div_one] using hx27
  let x29 : ℝ := Real.log (2 / 1)
  have hx29 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x29 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x30 : ℝ := (1 / 1)+(227 / 1024)
  have hx30 : Bounds (1251 / 1024) (1251 / 1024) x30 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((227 / 1024) : ℝ)) <;> norm_num
  let x31 : ℝ := (1 / 1)+(227 / 1024)
  have hx31 : Bounds (1251 / 1024) (1251 / 1024) x31 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((227 / 1024) : ℝ)) <;> norm_num
  let x32 : ℝ := Real.log x31
  have hx32 : Bounds (12514169 / 62500000) (40045341 / 200000000) x32 := by
    exact bounds_log hx31 (by norm_num) (by simpa only [div_one] using reflection_log_3.1) (by simpa only [div_one] using reflection_log_3.2)
  let x33 : ℝ := x30*x32
  have hx33 : Bounds (244612897171 / 1000000000000) (122306449197 / 500000000000) x33 := by
    apply bounds_mul hx30 hx32 <;> norm_num
  let x34 : ℝ := -(227 / 1024)
  have hx34 : Bounds (-227 / 1024) (-227 / 1024) x34 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((227 / 1024) : ℝ))
  let x35 : ℝ := (1 / 1)+x34
  have hx35 : Bounds (797 / 1024) (797 / 1024) x35 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx34 <;> norm_num
  let x36 : ℝ := (1 / 1)-(227 / 1024)
  have hx36 : Bounds (797 / 1024) (797 / 1024) x36 := by
    exact hx35
  let x37 : ℝ := -(227 / 1024)
  have hx37 : Bounds (-227 / 1024) (-227 / 1024) x37 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((227 / 1024) : ℝ))
  let x38 : ℝ := (1 / 1)+x37
  have hx38 : Bounds (797 / 1024) (797 / 1024) x38 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx37 <;> norm_num
  let x39 : ℝ := (1 / 1)-(227 / 1024)
  have hx39 : Bounds (797 / 1024) (797 / 1024) x39 := by
    exact hx38
  let x40 : ℝ := Real.log x39
  have hx40 : Bounds (-250617127 / 1000000000) (-125308563 / 500000000) x40 := by
    exact bounds_log hx39 (by norm_num) (by simpa only [div_one] using reflection_log_4.1) (by simpa only [div_one] using reflection_log_4.2)
  let x41 : ℝ := x36*x40
  have hx41 : Bounds (-39012080121 / 200000000000) (-97530199913 / 500000000000) x41 := by
    apply bounds_mul hx36 hx40 <;> norm_num
  let x42 : ℝ := x33+x41
  have hx42 : Bounds (24776248283 / 500000000000) (6194062321 / 125000000000) x42 := by
    apply bounds_add hx33 hx41 <;> norm_num
  let x43 : ℝ := (2 / 1)⁻¹
  have hx43 : Bounds (1 / 2) (1 / 2) x43 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x44 : ℝ := x42*x43
  have hx44 : Bounds (24776248283 / 1000000000000) (6194062321 / 250000000000) x44 := by
    apply bounds_mul hx42 hx43 <;> norm_num
  let x45 : ℝ := x42/(2 / 1)
  have hx45 : Bounds (24776248283 / 1000000000000) (6194062321 / 250000000000) x45 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx44
  let x46 : ℝ := -x45
  have hx46 : Bounds (-6194062321 / 250000000000) (-24776248283 / 1000000000000) x46 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx45
  let x47 : ℝ := x29+x46
  have hx47 : Bounds (167092732679 / 250000000000) (668370932717 / 1000000000000) x47 := by
    apply bounds_add hx29 hx46 <;> norm_num
  let x48 : ℝ := x29-x45
  have hx48 : Bounds (167092732679 / 250000000000) (668370932717 / 1000000000000) x48 := by
    exact hx47
  let x49 : ℝ := biasE (227 / 1024)
  have hx49 : Bounds (167092732679 / 250000000000) (668370932717 / 1000000000000) x49 := by
    simpa +zetaDelta only [biasE, div_one] using hx48
  let x50 : ℝ := biasE x3
  have hx50 : Bounds (668304843871 / 1000000000000) (668370932717 / 1000000000000) x50 := by
    exact bounds_biasE hx3 (by norm_num) (by norm_num) hx28.1 hx49.2
  let x51 : ℝ := Real.log (2 / 1)
  have hx51 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x51 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x52 : ℝ := (1 / 1)+(2273 / 5120)
  have hx52 : Bounds (7393 / 5120) (7393 / 5120) x52 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((2273 / 5120) : ℝ)) <;> norm_num
  let x53 : ℝ := (1 / 1)+(2273 / 5120)
  have hx53 : Bounds (7393 / 5120) (7393 / 5120) x53 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((2273 / 5120) : ℝ)) <;> norm_num
  let x54 : ℝ := Real.log x53
  have hx54 : Bounds (367379167 / 1000000000) (11480599 / 31250000) x54 := by
    exact bounds_log hx53 (by norm_num) (by simpa only [div_one] using reflection_log_5.1) (by simpa only [div_one] using reflection_log_5.2)
  let x55 : ℝ := x52*x54
  have hx55 : Bounds (530475426099 / 1000000000000) (66309428443 / 125000000000) x55 := by
    apply bounds_mul hx52 hx54 <;> norm_num
  let x56 : ℝ := -(2273 / 5120)
  have hx56 : Bounds (-2273 / 5120) (-2273 / 5120) x56 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((2273 / 5120) : ℝ))
  let x57 : ℝ := (1 / 1)+x56
  have hx57 : Bounds (2847 / 5120) (2847 / 5120) x57 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx56 <;> norm_num
  let x58 : ℝ := (1 / 1)-(2273 / 5120)
  have hx58 : Bounds (2847 / 5120) (2847 / 5120) x58 := by
    exact hx57
  let x59 : ℝ := -(2273 / 5120)
  have hx59 : Bounds (-2273 / 5120) (-2273 / 5120) x59 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((2273 / 5120) : ℝ))
  let x60 : ℝ := (1 / 1)+x59
  have hx60 : Bounds (2847 / 5120) (2847 / 5120) x60 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx59 <;> norm_num
  let x61 : ℝ := (1 / 1)-(2273 / 5120)
  have hx61 : Bounds (2847 / 5120) (2847 / 5120) x61 := by
    exact hx60
  let x62 : ℝ := Real.log x61
  have hx62 : Bounds (-586888631 / 1000000000) (-58688863 / 100000000) x62 := by
    exact bounds_log hx61 (by norm_num) (by simpa only [div_one] using reflection_log_6.1) (by simpa only [div_one] using reflection_log_6.2)
  let x63 : ℝ := x58*x62
  have hx63 : Bounds (-326342174309 / 1000000000000) (-326342173751 / 1000000000000) x63 := by
    apply bounds_mul hx58 hx62 <;> norm_num
  let x64 : ℝ := x55+x63
  have hx64 : Bounds (20413325179 / 100000000000) (204133253793 / 1000000000000) x64 := by
    apply bounds_add hx55 hx63 <;> norm_num
  let x65 : ℝ := (2 / 1)⁻¹
  have hx65 : Bounds (1 / 2) (1 / 2) x65 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x66 : ℝ := x64*x65
  have hx66 : Bounds (20413325179 / 200000000000) (102066626897 / 1000000000000) x66 := by
    apply bounds_mul hx64 hx65 <;> norm_num
  let x67 : ℝ := x64/(2 / 1)
  have hx67 : Bounds (20413325179 / 200000000000) (102066626897 / 1000000000000) x67 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx66
  let x68 : ℝ := -x67
  have hx68 : Bounds (-102066626897 / 1000000000000) (-20413325179 / 200000000000) x68 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx67
  let x69 : ℝ := x51+x68
  have hx69 : Bounds (591080553103 / 1000000000000) (118216111021 / 200000000000) x69 := by
    apply bounds_add hx51 hx68 <;> norm_num
  let x70 : ℝ := x51-x67
  have hx70 : Bounds (591080553103 / 1000000000000) (118216111021 / 200000000000) x70 := by
    exact hx69
  let x71 : ℝ := biasE (2273 / 5120)
  have hx71 : Bounds (591080553103 / 1000000000000) (118216111021 / 200000000000) x71 := by
    simpa +zetaDelta only [biasE, div_one] using hx70
  let x72 : ℝ := Real.log (2 / 1)
  have hx72 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x72 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x73 : ℝ := (1 / 1)+(227 / 512)
  have hx73 : Bounds (739 / 512) (739 / 512) x73 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((227 / 512) : ℝ)) <;> norm_num
  let x74 : ℝ := (1 / 1)+(227 / 512)
  have hx74 : Bounds (739 / 512) (739 / 512) x74 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((227 / 512) : ℝ)) <;> norm_num
  let x75 : ℝ := Real.log x74
  have hx75 : Bounds (73394659 / 200000000) (22935831 / 62500000) x75 := by
    exact bounds_log hx74 (by norm_num) (by simpa only [div_one] using reflection_log_7.1) (by simpa only [div_one] using reflection_log_7.2)
  let x76 : ℝ := x73*x75
  have hx76 : Bounds (33104646607 / 62500000000) (529674347157 / 1000000000000) x76 := by
    apply bounds_mul hx73 hx75 <;> norm_num
  let x77 : ℝ := -(227 / 512)
  have hx77 : Bounds (-227 / 512) (-227 / 512) x77 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((227 / 512) : ℝ))
  let x78 : ℝ := (1 / 1)+x77
  have hx78 : Bounds (285 / 512) (285 / 512) x78 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx77 <;> norm_num
  let x79 : ℝ := (1 / 1)-(227 / 512)
  have hx79 : Bounds (285 / 512) (285 / 512) x79 := by
    exact hx78
  let x80 : ℝ := -(227 / 512)
  have hx80 : Bounds (-227 / 512) (-227 / 512) x80 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((227 / 512) : ℝ))
  let x81 : ℝ := (1 / 1)+x80
  have hx81 : Bounds (285 / 512) (285 / 512) x81 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx80 <;> norm_num
  let x82 : ℝ := (1 / 1)-(227 / 512)
  have hx82 : Bounds (285 / 512) (285 / 512) x82 := by
    exact hx81
  let x83 : ℝ := Real.log x82
  have hx83 : Bounds (-117167089 / 200000000) (-146458861 / 250000000) x83 := by
    exact bounds_log hx82 (by norm_num) (by simpa only [div_one] using reflection_log_8.1) (by simpa only [div_one] using reflection_log_8.2)
  let x84 : ℝ := x79*x83
  have hx84 : Bounds (-81524952063 / 250000000000) (-65219961539 / 200000000000) x84 := by
    apply bounds_mul hx79 hx83 <;> norm_num
  let x85 : ℝ := x76+x84
  have hx85 : Bounds (10178726873 / 50000000000) (101787269731 / 500000000000) x85 := by
    apply bounds_add hx76 hx84 <;> norm_num
  let x86 : ℝ := (2 / 1)⁻¹
  have hx86 : Bounds (1 / 2) (1 / 2) x86 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x87 : ℝ := x85*x86
  have hx87 : Bounds (10178726873 / 100000000000) (101787269731 / 1000000000000) x87 := by
    apply bounds_mul hx85 hx86 <;> norm_num
  let x88 : ℝ := x85/(2 / 1)
  have hx88 : Bounds (10178726873 / 100000000000) (101787269731 / 1000000000000) x88 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx87
  let x89 : ℝ := -x88
  have hx89 : Bounds (-101787269731 / 1000000000000) (-10178726873 / 100000000000) x89 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx88
  let x90 : ℝ := x72+x89
  have hx90 : Bounds (591359910269 / 1000000000000) (59135991227 / 100000000000) x90 := by
    apply bounds_add hx72 hx89 <;> norm_num
  let x91 : ℝ := x72-x88
  have hx91 : Bounds (591359910269 / 1000000000000) (59135991227 / 100000000000) x91 := by
    exact hx90
  let x92 : ℝ := biasE (227 / 512)
  have hx92 : Bounds (591359910269 / 1000000000000) (59135991227 / 100000000000) x92 := by
    simpa +zetaDelta only [biasE, div_one] using hx91
  let x93 : ℝ := biasE x7
  have hx93 : Bounds (591080553103 / 1000000000000) (59135991227 / 100000000000) x93 := by
    exact bounds_biasE hx7 (by norm_num) (by norm_num) hx71.1 hx92.2
  let x94 : ℝ := Real.log (2 / 1)
  have hx94 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x94 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x95 : ℝ := x94+x93
  have hx95 : Bounds (1284227733103 / 1000000000000) (128450709327 / 100000000000) x95 := by
    apply bounds_add hx94 hx93 <;> norm_num
  let x96 : ℝ := (2 / 1)⁻¹
  have hx96 : Bounds (1 / 2) (1 / 2) x96 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x97 : ℝ := x95*x96
  have hx97 : Bounds (642113866551 / 1000000000000) (128450709327 / 200000000000) x97 := by
    apply bounds_mul hx95 hx96 <;> norm_num
  let x98 : ℝ := x95/(2 / 1)
  have hx98 : Bounds (642113866551 / 1000000000000) (128450709327 / 200000000000) x98 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx97
  let x99 : ℝ := Real.log (2 / 1)
  have hx99 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x99 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x100 : ℝ := (1 / 1)+(19769 / 62500)
  have hx100 : Bounds (82269 / 62500) (82269 / 62500) x100 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((19769 / 62500) : ℝ)) <;> norm_num
  let x101 : ℝ := (1 / 1)+(19769 / 62500)
  have hx101 : Bounds (82269 / 62500) (82269 / 62500) x101 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((19769 / 62500) : ℝ)) <;> norm_num
  let x102 : ℝ := Real.log x101
  have hx102 : Bounds (274827809 / 1000000000) (27482781 / 100000000) x102 := by
    exact bounds_log hx101 (by norm_num) (by simpa only [div_one] using reflection_log_9.1) (by simpa only [div_one] using reflection_log_9.2)
  let x103 : ℝ := x100*x102
  have hx103 : Bounds (361756944297 / 1000000000000) (72351389123 / 200000000000) x103 := by
    apply bounds_mul hx100 hx102 <;> norm_num
  let x104 : ℝ := -(19769 / 62500)
  have hx104 : Bounds (-19769 / 62500) (-19769 / 62500) x104 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((19769 / 62500) : ℝ))
  let x105 : ℝ := (1 / 1)+x104
  have hx105 : Bounds (42731 / 62500) (42731 / 62500) x105 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx104 <;> norm_num
  let x106 : ℝ := (1 / 1)-(19769 / 62500)
  have hx106 : Bounds (42731 / 62500) (42731 / 62500) x106 := by
    exact hx105
  let x107 : ℝ := -(19769 / 62500)
  have hx107 : Bounds (-19769 / 62500) (-19769 / 62500) x107 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((19769 / 62500) : ℝ))
  let x108 : ℝ := (1 / 1)+x107
  have hx108 : Bounds (42731 / 62500) (42731 / 62500) x108 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx107 <;> norm_num
  let x109 : ℝ := (1 / 1)-(19769 / 62500)
  have hx109 : Bounds (42731 / 62500) (42731 / 62500) x109 := by
    exact hx108
  let x110 : ℝ := Real.log x109
  have hx110 : Bounds (-76048381 / 200000000) (-23765119 / 62500000) x110 := by
    exact bounds_log hx109 (by norm_num) (by simpa only [div_one] using reflection_log_10.1) (by simpa only [div_one] using reflection_log_10.2)
  let x111 : ℝ := x106*x110
  have hx111 : Bounds (-259969869481 / 1000000000000) (-259969868797 / 1000000000000) x111 := by
    apply bounds_mul hx106 hx110 <;> norm_num
  let x112 : ℝ := x103+x111
  have hx112 : Bounds (397605761 / 3906250000) (50893538409 / 500000000000) x112 := by
    apply bounds_add hx103 hx111 <;> norm_num
  let x113 : ℝ := (2 / 1)⁻¹
  have hx113 : Bounds (1 / 2) (1 / 2) x113 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x114 : ℝ := x112*x113
  have hx114 : Bounds (397605761 / 7812500000) (50893538409 / 1000000000000) x114 := by
    apply bounds_mul hx112 hx113 <;> norm_num
  let x115 : ℝ := x112/(2 / 1)
  have hx115 : Bounds (397605761 / 7812500000) (50893538409 / 1000000000000) x115 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx114
  let x116 : ℝ := -x115
  have hx116 : Bounds (-50893538409 / 1000000000000) (-397605761 / 7812500000) x116 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx115
  let x117 : ℝ := x99+x116
  have hx117 : Bounds (642253641591 / 1000000000000) (80281705449 / 125000000000) x117 := by
    apply bounds_add hx99 hx116 <;> norm_num
  let x118 : ℝ := x99-x115
  have hx118 : Bounds (642253641591 / 1000000000000) (80281705449 / 125000000000) x118 := by
    exact hx117
  let x119 : ℝ := biasE (19769 / 62500)
  have hx119 : Bounds (642253641591 / 1000000000000) (80281705449 / 125000000000) x119 := by
    simpa +zetaDelta only [biasE, div_one] using hx118
  let x120 : ℝ := Real.log (2 / 1)
  have hx120 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x120 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x121 : ℝ := (1 / 1)+(316731 / 1000000)
  have hx121 : Bounds (1316731 / 1000000) (1316731 / 1000000) x121 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((316731 / 1000000) : ℝ)) <;> norm_num
  let x122 : ℝ := (1 / 1)+(316731 / 1000000)
  have hx122 : Bounds (1316731 / 1000000) (1316731 / 1000000) x122 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((316731 / 1000000) : ℝ)) <;> norm_num
  let x123 : ℝ := Real.log x122
  have hx123 : Bounds (275152149 / 1000000000) (5503043 / 20000000) x123 := by
    exact bounds_log hx122 (by norm_num) (by simpa only [div_one] using reflection_log_11.1) (by simpa only [div_one] using reflection_log_11.2)
  let x124 : ℝ := x121*x123
  have hx124 : Bounds (22643835269 / 62500000000) (181150682811 / 500000000000) x124 := by
    apply bounds_mul hx121 hx123 <;> norm_num
  let x125 : ℝ := -(316731 / 1000000)
  have hx125 : Bounds (-316731 / 1000000) (-316731 / 1000000) x125 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((316731 / 1000000) : ℝ))
  let x126 : ℝ := (1 / 1)+x125
  have hx126 : Bounds (683269 / 1000000) (683269 / 1000000) x126 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx125 <;> norm_num
  let x127 : ℝ := (1 / 1)-(316731 / 1000000)
  have hx127 : Bounds (683269 / 1000000) (683269 / 1000000) x127 := by
    exact hx126
  let x128 : ℝ := -(316731 / 1000000)
  have hx128 : Bounds (-316731 / 1000000) (-316731 / 1000000) x128 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((316731 / 1000000) : ℝ))
  let x129 : ℝ := (1 / 1)+x128
  have hx129 : Bounds (683269 / 1000000) (683269 / 1000000) x129 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx128 <;> norm_num
  let x130 : ℝ := (1 / 1)-(316731 / 1000000)
  have hx130 : Bounds (683269 / 1000000) (683269 / 1000000) x130 := by
    exact hx129
  let x131 : ℝ := Real.log x130
  have hx131 : Bounds (-380866647 / 1000000000) (-190433323 / 500000000) x131 := by
    exact bounds_log hx130 (by norm_num) (by simpa only [div_one] using reflection_log_12.1) (by simpa only [div_one] using reflection_log_12.2)
  let x132 : ℝ := x127*x131
  have hx132 : Bounds (-26023437303 / 100000000000) (-52046874469 / 200000000000) x132 := by
    apply bounds_mul hx127 hx131 <;> norm_num
  let x133 : ℝ := x124+x132
  have hx133 : Bounds (51033495637 / 500000000000) (102066993277 / 1000000000000) x133 := by
    apply bounds_add hx124 hx132 <;> norm_num
  let x134 : ℝ := (2 / 1)⁻¹
  have hx134 : Bounds (1 / 2) (1 / 2) x134 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x135 : ℝ := x133*x134
  have hx135 : Bounds (51033495637 / 1000000000000) (51033496639 / 1000000000000) x135 := by
    apply bounds_mul hx133 hx134 <;> norm_num
  let x136 : ℝ := x133/(2 / 1)
  have hx136 : Bounds (51033495637 / 1000000000000) (51033496639 / 1000000000000) x136 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx135
  let x137 : ℝ := -x136
  have hx137 : Bounds (-51033496639 / 1000000000000) (-51033495637 / 1000000000000) x137 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx136
  let x138 : ℝ := x120+x137
  have hx138 : Bounds (642113683361 / 1000000000000) (642113685363 / 1000000000000) x138 := by
    apply bounds_add hx120 hx137 <;> norm_num
  let x139 : ℝ := x120-x136
  have hx139 : Bounds (642113683361 / 1000000000000) (642113685363 / 1000000000000) x139 := by
    exact hx138
  let x140 : ℝ := biasE (316731 / 1000000)
  have hx140 : Bounds (642113683361 / 1000000000000) (642113685363 / 1000000000000) x140 := by
    simpa +zetaDelta only [biasE, div_one] using hx139
  let y : ℝ := 1 - 2 * entropyInverse ((1 + H (2*m - 1/2))/2)
  have hLh' : Real.log 2 * ((1 + H (2*m - 1/2))/2) = x98 := by
    simpa +zetaDelta only [div_one] using hLh
  have hy : Bounds (19769 / 62500) (316731 / 1000000) y := by
    apply entropyInverseBias_bracket
    · exact div_nonneg (add_nonneg zero_le_one
        (H_nonneg (by linarith [hm.1]) (by linarith [hm.2]))) two_pos.le
    · linarith [H_le_one (2*m-1/2)]
    · norm_num
    · norm_num
    · norm_num
    · have h1 : biasE (316731 / 1000000) ≤ (642113685363 / 1000000000000) := hx140.2
      have h2 : (642113866551 / 1000000000000) ≤ x98 := hx98.1
      linarith [hLh']
    · have h1 : x98 ≤ (128450709327 / 200000000000) := hx98.2
      have h2 : (642253641591 / 1000000000000) ≤ biasE (19769 / 62500) := hx119.1
      linarith [hLh']
  let x141 : ℝ := x3⁻¹
  have hx141 : Bounds (563132424109 / 125000000000) (225550660793 / 50000000000) x141 := by
    apply bounds_inv hx3 <;> norm_num
  let x142 : ℝ := x98*x141
  have hx142 : Bounds (1446380552899 / 500000000000) (724303559201 / 250000000000) x142 := by
    apply bounds_mul hx98 hx141 <;> norm_num
  let x143 : ℝ := x98/x3
  have hx143 : Bounds (1446380552899 / 500000000000) (724303559201 / 250000000000) x143 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx142
  let x144 : ℝ := Real.log (2 / 1)
  have hx144 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x144 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x145 : ℝ := (1 / 1)+(230031 / 1000000)
  have hx145 : Bounds (1230031 / 1000000) (1230031 / 1000000) x145 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((230031 / 1000000) : ℝ)) <;> norm_num
  let x146 : ℝ := (1 / 1)+(230031 / 1000000)
  have hx146 : Bounds (1230031 / 1000000) (1230031 / 1000000) x146 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((230031 / 1000000) : ℝ)) <;> norm_num
  let x147 : ℝ := Real.log x146
  have hx147 : Bounds (51759843 / 250000000) (207039373 / 1000000000) x147 := by
    exact bounds_log hx146 (by norm_num) (by simpa only [div_one] using reflection_log_13.1) (by simpa only [div_one] using reflection_log_13.2)
  let x148 : ℝ := x145*x147
  have hx148 : Bounds (12733242289 / 50000000000) (254664847011 / 1000000000000) x148 := by
    apply bounds_mul hx145 hx147 <;> norm_num
  let x149 : ℝ := -(230031 / 1000000)
  have hx149 : Bounds (-230031 / 1000000) (-230031 / 1000000) x149 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((230031 / 1000000) : ℝ))
  let x150 : ℝ := (1 / 1)+x149
  have hx150 : Bounds (769969 / 1000000) (769969 / 1000000) x150 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx149 <;> norm_num
  let x151 : ℝ := (1 / 1)-(230031 / 1000000)
  have hx151 : Bounds (769969 / 1000000) (769969 / 1000000) x151 := by
    exact hx150
  let x152 : ℝ := -(230031 / 1000000)
  have hx152 : Bounds (-230031 / 1000000) (-230031 / 1000000) x152 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((230031 / 1000000) : ℝ))
  let x153 : ℝ := (1 / 1)+x152
  have hx153 : Bounds (769969 / 1000000) (769969 / 1000000) x153 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx152 <;> norm_num
  let x154 : ℝ := (1 / 1)-(230031 / 1000000)
  have hx154 : Bounds (769969 / 1000000) (769969 / 1000000) x154 := by
    exact hx153
  let x155 : ℝ := Real.log x154
  have hx155 : Bounds (-10456201 / 40000000) (-8168907 / 31250000) x155 := by
    exact bounds_log hx154 (by norm_num) (by simpa only [div_one] using reflection_log_14.1) (by simpa only [div_one] using reflection_log_14.2)
  let x156 : ℝ := x151*x155
  have hx156 : Bounds (-40254753139 / 200000000000) (-50318441231 / 250000000000) x156 := by
    apply bounds_mul hx151 hx155 <;> norm_num
  let x157 : ℝ := x148+x156
  have hx157 : Bounds (10678216017 / 200000000000) (53391082087 / 1000000000000) x157 := by
    apply bounds_add hx148 hx156 <;> norm_num
  let x158 : ℝ := (2 / 1)⁻¹
  have hx158 : Bounds (1 / 2) (1 / 2) x158 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x159 : ℝ := x157*x158
  have hx159 : Bounds (13347770021 / 500000000000) (6673885261 / 250000000000) x159 := by
    apply bounds_mul hx157 hx158 <;> norm_num
  let x160 : ℝ := x157/(2 / 1)
  have hx160 : Bounds (13347770021 / 500000000000) (6673885261 / 250000000000) x160 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx159
  let x161 : ℝ := -x160
  have hx161 : Bounds (-6673885261 / 250000000000) (-13347770021 / 500000000000) x161 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx160
  let x162 : ℝ := x144+x161
  have hx162 : Bounds (166612909739 / 250000000000) (333225820479 / 500000000000) x162 := by
    apply bounds_add hx144 hx161 <;> norm_num
  let x163 : ℝ := x144-x160
  have hx163 : Bounds (166612909739 / 250000000000) (333225820479 / 500000000000) x163 := by
    exact hx162
  let x164 : ℝ := biasE (230031 / 1000000)
  have hx164 : Bounds (166612909739 / 250000000000) (333225820479 / 500000000000) x164 := by
    simpa +zetaDelta only [biasE, div_one] using hx163
  let x165 : ℝ := Real.log (2 / 1)
  have hx165 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x165 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x166 : ℝ := (1 / 1)+(5759 / 25000)
  have hx166 : Bounds (30759 / 25000) (30759 / 25000) x166 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((5759 / 25000) : ℝ)) <;> norm_num
  let x167 : ℝ := (1 / 1)+(5759 / 25000)
  have hx167 : Bounds (30759 / 25000) (30759 / 25000) x167 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((5759 / 25000) : ℝ)) <;> norm_num
  let x168 : ℝ := Real.log x167
  have hx168 : Bounds (207306809 / 1000000000) (20730681 / 100000000) x168 := by
    exact bounds_log hx167 (by norm_num) (by simpa only [div_one] using reflection_log_15.1) (by simpa only [div_one] using reflection_log_15.2)
  let x169 : ℝ := x166*x168
  have hx169 : Bounds (255062005521 / 1000000000000) (7970687711 / 31250000000) x169 := by
    apply bounds_mul hx166 hx168 <;> norm_num
  let x170 : ℝ := -(5759 / 25000)
  have hx170 : Bounds (-5759 / 25000) (-5759 / 25000) x170 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((5759 / 25000) : ℝ))
  let x171 : ℝ := (1 / 1)+x170
  have hx171 : Bounds (19241 / 25000) (19241 / 25000) x171 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx170 <;> norm_num
  let x172 : ℝ := (1 / 1)-(5759 / 25000)
  have hx172 : Bounds (19241 / 25000) (19241 / 25000) x172 := by
    exact hx171
  let x173 : ℝ := -(5759 / 25000)
  have hx173 : Bounds (-5759 / 25000) (-5759 / 25000) x173 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((5759 / 25000) : ℝ))
  let x174 : ℝ := (1 / 1)+x173
  have hx174 : Bounds (19241 / 25000) (19241 / 25000) x174 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx173 <;> norm_num
  let x175 : ℝ := (1 / 1)-(5759 / 25000)
  have hx175 : Bounds (19241 / 25000) (19241 / 25000) x175 := by
    exact hx174
  let x176 : ℝ := Real.log x175
  have hx176 : Bounds (-130916203 / 500000000) (-52366481 / 200000000) x176 := by
    exact bounds_log hx175 (by norm_num) (by simpa only [div_one] using reflection_log_16.1) (by simpa only [div_one] using reflection_log_16.2)
  let x177 : ℝ := x172*x176
  have hx177 : Bounds (-100758346477 / 500000000000) (-25189586523 / 125000000000) x177 := by
    apply bounds_mul hx172 hx176 <;> norm_num
  let x178 : ℝ := x169+x177
  have hx178 : Bounds (53545312567 / 1000000000000) (6693164321 / 125000000000) x178 := by
    apply bounds_add hx169 hx177 <;> norm_num
  let x179 : ℝ := (2 / 1)⁻¹
  have hx179 : Bounds (1 / 2) (1 / 2) x179 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x180 : ℝ := x178*x179
  have hx180 : Bounds (26772656283 / 1000000000000) (6693164321 / 250000000000) x180 := by
    apply bounds_mul hx178 hx179 <;> norm_num
  let x181 : ℝ := x178/(2 / 1)
  have hx181 : Bounds (26772656283 / 1000000000000) (6693164321 / 250000000000) x181 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx180
  let x182 : ℝ := -x181
  have hx182 : Bounds (-6693164321 / 250000000000) (-26772656283 / 1000000000000) x182 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx181
  let x183 : ℝ := x165+x182
  have hx183 : Bounds (166593630679 / 250000000000) (666374524717 / 1000000000000) x183 := by
    apply bounds_add hx165 hx182 <;> norm_num
  let x184 : ℝ := x165-x181
  have hx184 : Bounds (166593630679 / 250000000000) (666374524717 / 1000000000000) x184 := by
    exact hx183
  let x185 : ℝ := biasE (5759 / 25000)
  have hx185 : Bounds (166593630679 / 250000000000) (666374524717 / 1000000000000) x185 := by
    simpa +zetaDelta only [biasE, div_one] using hx184
  let x186 : ℝ := x143*(230031 / 1000000)
  have hx186 : Bounds (665424729927 / 1000000000000) (666449088107 / 1000000000000) x186 := by
    apply bounds_mul hx143 (bounds_const ((230031 / 1000000) : ℝ)) <;> norm_num
  let x187 : ℝ := x143*(5759 / 25000)
  have hx187 : Bounds (666376448331 / 1000000000000) (667402271591 / 1000000000000) x187 := by
    apply bounds_mul hx143 (bounds_const ((5759 / 25000) : ℝ)) <;> norm_num
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
  have hc : Bounds (230031 / 1000000) (5759 / 25000) c := by
    apply contact_bracket hc0 hcMem.2.le (by norm_num) (by norm_num) (by norm_num)
      (show 0 < x143 by linarith [hx143.1]) hcEq
    · have h1 : x143 * (230031 / 1000000) ≤ (666449088107 / 1000000000000) := hx186.2
      have h2 : (166612909739 / 250000000000) ≤ biasE (230031 / 1000000) := hx164.1
      linarith
    · have h1 : biasE (5759 / 25000) ≤ (666374524717 / 1000000000000) := hx185.2
      have h2 : (666376448331 / 1000000000000) ≤ x143 * (5759 / 25000) := hx187.1
      linarith
  let x188 : ℝ := (1 / 1)+y
  have hx188 : Bounds (82269 / 62500) (1316731 / 1000000) x188 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hy <;> norm_num
  let x189 : ℝ := -y
  have hx189 : Bounds (-316731 / 1000000) (-19769 / 62500) x189 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hy
  let x190 : ℝ := (1 / 1)+x189
  have hx190 : Bounds (683269 / 1000000) (42731 / 62500) x190 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx189 <;> norm_num
  let x191 : ℝ := (1 / 1)-y
  have hx191 : Bounds (683269 / 1000000) (42731 / 62500) x191 := by
    exact hx190
  let x192 : ℝ := x191⁻¹
  have hx192 : Bounds (1462638365589 / 1000000000000) (1463552422253 / 1000000000000) x192 := by
    apply bounds_inv hx191 <;> norm_num
  let x193 : ℝ := x188*x192
  have hx193 : Bounds (962638365589 / 500000000000) (963552422253 / 500000000000) x193 := by
    apply bounds_mul hx188 hx192 <;> norm_num
  let x194 : ℝ := x188/x191
  have hx194 : Bounds (962638365589 / 500000000000) (963552422253 / 500000000000) x194 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx193
  let x195 : ℝ := Real.log x194
  have hx195 : Bounds (655069713 / 1000000000) (656018797 / 1000000000) x195 := by
    exact bounds_log hx194 (by norm_num) (by simpa only [div_one] using reflection_log_17.1) (by simpa only [div_one] using reflection_log_18.2)
  let x196 : ℝ := (2 / 1)⁻¹
  have hx196 : Bounds (1 / 2) (1 / 2) x196 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x197 : ℝ := x195*x196
  have hx197 : Bounds (655069713 / 2000000000) (656018797 / 2000000000) x197 := by
    apply bounds_mul hx195 hx196 <;> norm_num
  let x198 : ℝ := x195/(2 / 1)
  have hx198 : Bounds (655069713 / 2000000000) (656018797 / 2000000000) x198 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx197
  let x199 : ℝ := (1 / 1)+c
  have hx199 : Bounds (1230031 / 1000000) (30759 / 25000) x199 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hc <;> norm_num
  let x200 : ℝ := -c
  have hx200 : Bounds (-5759 / 25000) (-230031 / 1000000) x200 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hc
  let x201 : ℝ := (1 / 1)+x200
  have hx201 : Bounds (19241 / 25000) (769969 / 1000000) x201 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx200 <;> norm_num
  let x202 : ℝ := (1 / 1)-c
  have hx202 : Bounds (19241 / 25000) (769969 / 1000000) x202 := by
    exact hx201
  let x203 : ℝ := x202⁻¹
  have hx203 : Bounds (1298753586183 / 1000000000000) (162413595967 / 125000000000) x203 := by
    apply bounds_inv hx202 <;> norm_num
  let x204 : ℝ := x199*x203
  have hx204 : Bounds (798753586183 / 500000000000) (99913595967 / 62500000000) x204 := by
    apply bounds_mul hx199 hx203 <;> norm_num
  let x205 : ℝ := x199/x202
  have hx205 : Bounds (798753586183 / 500000000000) (99913595967 / 62500000000) x205 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx204
  let x206 : ℝ := Real.log x205
  have hx206 : Bounds (468444397 / 1000000000) (29321201 / 62500000) x206 := by
    exact bounds_log hx205 (by norm_num) (by simpa only [div_one] using reflection_log_19.1) (by simpa only [div_one] using reflection_log_20.2)
  let x207 : ℝ := (2 / 1)⁻¹
  have hx207 : Bounds (1 / 2) (1 / 2) x207 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x208 : ℝ := x206*x207
  have hx208 : Bounds (468444397 / 2000000000) (29321201 / 125000000) x208 := by
    apply bounds_mul hx206 hx207 <;> norm_num
  let x209 : ℝ := x206/(2 / 1)
  have hx209 : Bounds (468444397 / 2000000000) (29321201 / 125000000) x209 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx208
  let x210 : ℝ := (2 / 1)*x50
  have hx210 : Bounds (668304843871 / 500000000000) (668370932717 / 500000000000) x210 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx50 <;> norm_num
  let x211 : ℝ := (2 / 1)*x98
  have hx211 : Bounds (642113866551 / 500000000000) (128450709327 / 100000000000) x211 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx98 <;> norm_num
  let x212 : ℝ := -x211
  have hx212 : Bounds (-128450709327 / 100000000000) (-642113866551 / 500000000000) x212 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx211
  let x213 : ℝ := x210+x212
  have hx213 : Bounds (6512824309 / 125000000000) (13128533083 / 250000000000) x213 := by
    apply bounds_add hx210 hx212 <;> norm_num
  let x214 : ℝ := x210-x211
  have hx214 : Bounds (6512824309 / 125000000000) (13128533083 / 250000000000) x214 := by
    exact hx213
  let x215 : ℝ := y*x198
  have hx215 : Bounds (414402341 / 4000000000) (103890744797 / 1000000000000) x215 := by
    apply bounds_mul hy hx198 <;> norm_num
  let x216 : ℝ := -x215
  have hx216 : Bounds (-103890744797 / 1000000000000) (-414402341 / 4000000000) x216 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx215
  let x217 : ℝ := x214+x216
  have hx217 : Bounds (-2071526013 / 40000000000) (-25543226459 / 500000000000) x217 := by
    apply bounds_add hx214 hx216 <;> norm_num
  let x218 : ℝ := x214-x215
  have hx218 : Bounds (-2071526013 / 40000000000) (-25543226459 / 500000000000) x218 := by
    exact hx217
  let x219 : ℝ := x3*x209
  have hx219 : Bounds (51922303769 / 1000000000000) (13017009741 / 250000000000) x219 := by
    apply bounds_mul hx3 hx209 <;> norm_num
  let x220 : ℝ := x218+x219
  have hx220 : Bounds (33538361 / 250000000000) (490793023 / 500000000000) x220 := by
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

theorem acceptedCertificate : DoubleCapBiasCellCertificate (7967 / 20480) (797 / 2048) (fun m => (1 + H (2*m - 1/2))/2) where
  domain := by norm_num
  sound m hmLo hmHi := by
    exact cell_bias_nonneg m ⟨hmLo, hmHi⟩

theorem accepted_cell :
    ∀ m, (7967 / 20480) ≤ m → m ≤ (797 / 2048) → 0 ≤ doubleCapHighResidual m := by
  intro m hmLo hmHi
  unfold doubleCapHighResidual
  apply doubleCapEndpointResidual_nonneg_of_biasCell acceptedCertificate hmLo hmHi
  exact div_pos (by linarith [H_nonneg (by linarith : 0 ≤ 2*m-1/2) (by linarith : 2*m-1/2 ≤ 1)]) two_pos

#print axioms cell_bias_nonneg
#print axioms accepted_cell

end GeneralCK.Certificates.DoubleCapMiddle.Cell0399

end


