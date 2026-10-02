-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0164__4_q00
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0164__4_q00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T12:15:22.750507+00:00
-- url     : https://prove2.me/theorems/6df004fa-46c1-4651-99a6-46fffff1a83d
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0164 (+3 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0165, GeneralCK.Certificates…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0164 (+3 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0165, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0166, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0167) (piece 1 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0164 (+3 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0165, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0166, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0167) (piece 1 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0164 (+3 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0165, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0166, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0167) (piece 1 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0164 (+3 modules: GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0165, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0166, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0167) (piece 1 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0162Logs__7

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0164 =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0164
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Reflection
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem cell_bias_nonneg (m : ℝ) (hm : Bounds (1263 / 25600) (641 / 12800) m) :
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
  have hx0 : Bounds (1263 / 12800) (641 / 6400) x0 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hm <;> norm_num
  let x1 : ℝ := -x0
  have hx1 : Bounds (-641 / 6400) (-1263 / 12800) x1 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx0
  let x2 : ℝ := (1 / 1)+x1
  have hx2 : Bounds (5759 / 6400) (11537 / 12800) x2 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx1 <;> norm_num
  let x3 : ℝ := (1 / 1)-x0
  have hx3 : Bounds (5759 / 6400) (11537 / 12800) x3 := by
    exact hx2
  let x4 : ℝ := (4 / 1)*m
  have hx4 : Bounds (1263 / 6400) (641 / 3200) x4 := by
    apply bounds_mul (bounds_const ((4 / 1) : ℝ)) hm <;> norm_num
  let x5 : ℝ := -x4
  have hx5 : Bounds (-641 / 3200) (-1263 / 6400) x5 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx4
  let x6 : ℝ := (1 / 1)+x5
  have hx6 : Bounds (2559 / 3200) (5137 / 6400) x6 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx5 <;> norm_num
  let x7 : ℝ := (1 / 1)-x4
  have hx7 : Bounds (2559 / 3200) (5137 / 6400) x7 := by
    exact hx6
  let x8 : ℝ := Real.log (2 / 1)
  have hx8 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x8 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x9 : ℝ := (1 / 1)+(11537 / 12800)
  have hx9 : Bounds (24337 / 12800) (24337 / 12800) x9 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((11537 / 12800) : ℝ)) <;> norm_num
  let x10 : ℝ := (1 / 1)+(11537 / 12800)
  have hx10 : Bounds (24337 / 12800) (24337 / 12800) x10 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((11537 / 12800) : ℝ)) <;> norm_num
  let x11 : ℝ := Real.log x10
  have hx11 : Bounds (128510531 / 200000000) (40159541 / 62500000) x11 := by
    exact bounds_log hx10 (by norm_num) (by simpa only [div_one] using reflection_log_1.1) (by simpa only [div_one] using reflection_log_1.2)
  let x12 : ℝ := x9*x11
  have hx12 : Bounds (152712929343 / 125000000000) (1221703436647 / 1000000000000) x12 := by
    apply bounds_mul hx9 hx11 <;> norm_num
  let x13 : ℝ := -(11537 / 12800)
  have hx13 : Bounds (-11537 / 12800) (-11537 / 12800) x13 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((11537 / 12800) : ℝ))
  let x14 : ℝ := (1 / 1)+x13
  have hx14 : Bounds (1263 / 12800) (1263 / 12800) x14 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx13 <;> norm_num
  let x15 : ℝ := (1 / 1)-(11537 / 12800)
  have hx15 : Bounds (1263 / 12800) (1263 / 12800) x15 := by
    exact hx14
  let x16 : ℝ := -(11537 / 12800)
  have hx16 : Bounds (-11537 / 12800) (-11537 / 12800) x16 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((11537 / 12800) : ℝ))
  let x17 : ℝ := (1 / 1)+x16
  have hx17 : Bounds (1263 / 12800) (1263 / 12800) x17 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx16 <;> norm_num
  let x18 : ℝ := (1 / 1)-(11537 / 12800)
  have hx18 : Bounds (1263 / 12800) (1263 / 12800) x18 := by
    exact hx17
  let x19 : ℝ := Real.log x18
  have hx19 : Bounds (-2315955329 / 1000000000) (-92638213 / 40000000) x19 := by
    exact bounds_log hx18 (by norm_num) (by simpa only [div_one] using reflection_log_2.1) (by simpa only [div_one] using reflection_log_2.2)
  let x20 : ℝ := x15*x19
  have hx20 : Bounds (-228519654729 / 1000000000000) (-228519654333 / 1000000000000) x20 := by
    apply bounds_mul hx15 hx19 <;> norm_num
  let x21 : ℝ := x12+x20
  have hx21 : Bounds (198636756003 / 200000000000) (496591891157 / 500000000000) x21 := by
    apply bounds_add hx12 hx20 <;> norm_num
  let x22 : ℝ := (2 / 1)⁻¹
  have hx22 : Bounds (1 / 2) (1 / 2) x22 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x23 : ℝ := x21*x22
  have hx23 : Bounds (496591890007 / 1000000000000) (496591891157 / 1000000000000) x23 := by
    apply bounds_mul hx21 hx22 <;> norm_num
  let x24 : ℝ := x21/(2 / 1)
  have hx24 : Bounds (496591890007 / 1000000000000) (496591891157 / 1000000000000) x24 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx23
  let x25 : ℝ := -x24
  have hx25 : Bounds (-496591891157 / 1000000000000) (-496591890007 / 1000000000000) x25 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx24
  let x26 : ℝ := x8+x25
  have hx26 : Bounds (196555288843 / 1000000000000) (196555290993 / 1000000000000) x26 := by
    apply bounds_add hx8 hx25 <;> norm_num
  let x27 : ℝ := x8-x24
  have hx27 : Bounds (196555288843 / 1000000000000) (196555290993 / 1000000000000) x27 := by
    exact hx26
  let x28 : ℝ := biasE (11537 / 12800)
  have hx28 : Bounds (196555288843 / 1000000000000) (196555290993 / 1000000000000) x28 := by
    simpa +zetaDelta only [biasE, div_one] using hx27
  let x29 : ℝ := Real.log (2 / 1)
  have hx29 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x29 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x30 : ℝ := (1 / 1)+(5759 / 6400)
  have hx30 : Bounds (12159 / 6400) (12159 / 6400) x30 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((5759 / 6400) : ℝ)) <;> norm_num
  let x31 : ℝ := (1 / 1)+(5759 / 6400)
  have hx31 : Bounds (12159 / 6400) (12159 / 6400) x31 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((5759 / 6400) : ℝ)) <;> norm_num
  let x32 : ℝ := Real.log x31
  have hx32 : Bounds (128354329 / 200000000) (320885823 / 500000000) x32 := by
    exact bounds_log hx31 (by norm_num) (by simpa only [div_one] using reflection_log_3.1) (by simpa only [div_one] using reflection_log_3.2)
  let x33 : ℝ := x30*x32
  have hx33 : Bounds (30481646217 / 25000000000) (1219265850581 / 1000000000000) x33 := by
    apply bounds_mul hx30 hx32 <;> norm_num
  let x34 : ℝ := -(5759 / 6400)
  have hx34 : Bounds (-5759 / 6400) (-5759 / 6400) x34 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((5759 / 6400) : ℝ))
  let x35 : ℝ := (1 / 1)+x34
  have hx35 : Bounds (641 / 6400) (641 / 6400) x35 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx34 <;> norm_num
  let x36 : ℝ := (1 / 1)-(5759 / 6400)
  have hx36 : Bounds (641 / 6400) (641 / 6400) x36 := by
    exact hx35
  let x37 : ℝ := -(5759 / 6400)
  have hx37 : Bounds (-5759 / 6400) (-5759 / 6400) x37 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((5759 / 6400) : ℝ))
  let x38 : ℝ := (1 / 1)+x37
  have hx38 : Bounds (641 / 6400) (641 / 6400) x38 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx37 <;> norm_num
  let x39 : ℝ := (1 / 1)-(5759 / 6400)
  have hx39 : Bounds (641 / 6400) (641 / 6400) x39 := by
    exact hx38
  let x40 : ℝ := Real.log x39
  have hx40 : Bounds (-1150511907 / 500000000) (-230102381 / 100000000) x40 := by
    exact bounds_log hx39 (by norm_num) (by simpa only [div_one] using reflection_log_4.1) (by simpa only [div_one] using reflection_log_4.2)
  let x41 : ℝ := x36*x40
  have hx41 : Bounds (-230461916371 / 1000000000000) (-23046191597 / 100000000000) x41 := by
    apply bounds_mul hx36 hx40 <;> norm_num
  let x42 : ℝ := x33+x41
  have hx42 : Bounds (988803932309 / 1000000000000) (988803934611 / 1000000000000) x42 := by
    apply bounds_add hx33 hx41 <;> norm_num
  let x43 : ℝ := (2 / 1)⁻¹
  have hx43 : Bounds (1 / 2) (1 / 2) x43 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x44 : ℝ := x42*x43
  have hx44 : Bounds (247200983077 / 500000000000) (247200983653 / 500000000000) x44 := by
    apply bounds_mul hx42 hx43 <;> norm_num
  let x45 : ℝ := x42/(2 / 1)
  have hx45 : Bounds (247200983077 / 500000000000) (247200983653 / 500000000000) x45 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx44
  let x46 : ℝ := -x45
  have hx46 : Bounds (-247200983653 / 500000000000) (-247200983077 / 500000000000) x46 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx45
  let x47 : ℝ := x29+x46
  have hx47 : Bounds (99372606347 / 500000000000) (99372607423 / 500000000000) x47 := by
    apply bounds_add hx29 hx46 <;> norm_num
  let x48 : ℝ := x29-x45
  have hx48 : Bounds (99372606347 / 500000000000) (99372607423 / 500000000000) x48 := by
    exact hx47
  let x49 : ℝ := biasE (5759 / 6400)
  have hx49 : Bounds (99372606347 / 500000000000) (99372607423 / 500000000000) x49 := by
    simpa +zetaDelta only [biasE, div_one] using hx48
  let x50 : ℝ := biasE x3
  have hx50 : Bounds (196555288843 / 1000000000000) (99372607423 / 500000000000) x50 := by
    exact bounds_biasE hx3 (by norm_num) (by norm_num) hx28.1 hx49.2
  let x51 : ℝ := Real.log (2 / 1)
  have hx51 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x51 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x52 : ℝ := (1 / 1)+(5137 / 6400)
  have hx52 : Bounds (11537 / 6400) (11537 / 6400) x52 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((5137 / 6400) : ℝ)) <;> norm_num
  let x53 : ℝ := (1 / 1)+(5137 / 6400)
  have hx53 : Bounds (11537 / 6400) (11537 / 6400) x53 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((5137 / 6400) : ℝ)) <;> norm_num
  let x54 : ℝ := Real.log x53
  have hx54 : Bounds (589261271 / 1000000000) (73657659 / 125000000) x54 := by
    exact bounds_log hx53 (by norm_num) (by simpa only [div_one] using reflection_log_5.1) (by simpa only [div_one] using reflection_log_5.2)
  let x55 : ℝ := x52*x54
  have hx55 : Bounds (1062235513051 / 1000000000000) (531117757427 / 500000000000) x55 := by
    apply bounds_mul hx52 hx54 <;> norm_num
  let x56 : ℝ := -(5137 / 6400)
  have hx56 : Bounds (-5137 / 6400) (-5137 / 6400) x56 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((5137 / 6400) : ℝ))
  let x57 : ℝ := (1 / 1)+x56
  have hx57 : Bounds (1263 / 6400) (1263 / 6400) x57 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx56 <;> norm_num
  let x58 : ℝ := (1 / 1)-(5137 / 6400)
  have hx58 : Bounds (1263 / 6400) (1263 / 6400) x58 := by
    exact hx57
  let x59 : ℝ := -(5137 / 6400)
  have hx59 : Bounds (-5137 / 6400) (-5137 / 6400) x59 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((5137 / 6400) : ℝ))
  let x60 : ℝ := (1 / 1)+x59
  have hx60 : Bounds (1263 / 6400) (1263 / 6400) x60 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx59 <;> norm_num
  let x61 : ℝ := (1 / 1)-(5137 / 6400)
  have hx61 : Bounds (1263 / 6400) (1263 / 6400) x61 := by
    exact hx60
  let x62 : ℝ := Real.log x61
  have hx62 : Bounds (-405702037 / 250000000) (-324561629 / 200000000) x62 := by
    exact bounds_log hx61 (by norm_num) (by simpa only [div_one] using reflection_log_6.1) (by simpa only [div_one] using reflection_log_6.2)
  let x63 : ℝ := x58*x62
  have hx63 : Bounds (-320251045457 / 1000000000000) (-312745161 / 976562500) x63 := by
    apply bounds_mul hx58 hx62 <;> norm_num
  let x64 : ℝ := x55+x63
  have hx64 : Bounds (370992233797 / 500000000000) (74198446999 / 100000000000) x64 := by
    apply bounds_add hx55 hx63 <;> norm_num
  let x65 : ℝ := (2 / 1)⁻¹
  have hx65 : Bounds (1 / 2) (1 / 2) x65 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x66 : ℝ := x64*x65
  have hx66 : Bounds (370992233797 / 1000000000000) (74198446999 / 200000000000) x66 := by
    apply bounds_mul hx64 hx65 <;> norm_num
  let x67 : ℝ := x64/(2 / 1)
  have hx67 : Bounds (370992233797 / 1000000000000) (74198446999 / 200000000000) x67 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx66
  let x68 : ℝ := -x67
  have hx68 : Bounds (-74198446999 / 200000000000) (-370992233797 / 1000000000000) x68 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx67
  let x69 : ℝ := x51+x68
  have hx69 : Bounds (64430989001 / 200000000000) (322154947203 / 1000000000000) x69 := by
    apply bounds_add hx51 hx68 <;> norm_num
  let x70 : ℝ := x51-x67
  have hx70 : Bounds (64430989001 / 200000000000) (322154947203 / 1000000000000) x70 := by
    exact hx69
  let x71 : ℝ := biasE (5137 / 6400)
  have hx71 : Bounds (64430989001 / 200000000000) (322154947203 / 1000000000000) x71 := by
    simpa +zetaDelta only [biasE, div_one] using hx70
  let x72 : ℝ := Real.log (2 / 1)
  have hx72 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x72 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x73 : ℝ := (1 / 1)+(2559 / 3200)
  have hx73 : Bounds (5759 / 3200) (5759 / 3200) x73 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((2559 / 3200) : ℝ)) <;> norm_num
  let x74 : ℝ := (1 / 1)+(2559 / 3200)
  have hx74 : Bounds (5759 / 3200) (5759 / 3200) x74 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((2559 / 3200) : ℝ)) <;> norm_num
  let x75 : ℝ := Real.log x74
  have hx75 : Bounds (293806519 / 500000000) (587613039 / 1000000000) x75 := by
    exact bounds_log hx74 (by norm_num) (by simpa only [div_one] using reflection_log_7.1) (by simpa only [div_one] using reflection_log_7.2)
  let x76 : ℝ := x73*x75
  have hx76 : Bounds (42300793573 / 40000000000) (528759920563 / 500000000000) x76 := by
    apply bounds_mul hx73 hx75 <;> norm_num
  let x77 : ℝ := -(2559 / 3200)
  have hx77 : Bounds (-2559 / 3200) (-2559 / 3200) x77 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((2559 / 3200) : ℝ))
  let x78 : ℝ := (1 / 1)+x77
  have hx78 : Bounds (641 / 3200) (641 / 3200) x78 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx77 <;> norm_num
  let x79 : ℝ := (1 / 1)-(2559 / 3200)
  have hx79 : Bounds (641 / 3200) (641 / 3200) x79 := by
    exact hx78
  let x80 : ℝ := -(2559 / 3200)
  have hx80 : Bounds (-2559 / 3200) (-2559 / 3200) x80 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((2559 / 3200) : ℝ))
  let x81 : ℝ := (1 / 1)+x80
  have hx81 : Bounds (641 / 3200) (641 / 3200) x81 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx80 <;> norm_num
  let x82 : ℝ := (1 / 1)-(2559 / 3200)
  have hx82 : Bounds (641 / 3200) (641 / 3200) x82 := by
    exact hx81
  let x83 : ℝ := Real.log x82
  have hx83 : Bounds (-1607876633 / 1000000000) (-160787663 / 100000000) x83 := by
    exact bounds_log hx82 (by norm_num) (by simpa only [div_one] using reflection_log_8.1) (by simpa only [div_one] using reflection_log_8.2)
  let x84 : ℝ := x79*x83
  have hx84 : Bounds (-20129861753 / 62500000000) (-161038893723 / 500000000000) x84 := by
    apply bounds_mul hx79 hx83 <;> norm_num
  let x85 : ℝ := x76+x84
  have hx85 : Bounds (735442051277 / 1000000000000) (9193025671 / 12500000000) x85 := by
    apply bounds_add hx76 hx84 <;> norm_num
  let x86 : ℝ := (2 / 1)⁻¹
  have hx86 : Bounds (1 / 2) (1 / 2) x86 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x87 : ℝ := x85*x86
  have hx87 : Bounds (183860512819 / 500000000000) (9193025671 / 25000000000) x87 := by
    apply bounds_mul hx85 hx86 <;> norm_num
  let x88 : ℝ := x85/(2 / 1)
  have hx88 : Bounds (183860512819 / 500000000000) (9193025671 / 25000000000) x88 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx87
  let x89 : ℝ := -x88
  have hx89 : Bounds (-9193025671 / 25000000000) (-183860512819 / 500000000000) x89 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx88
  let x90 : ℝ := x72+x89
  have hx90 : Bounds (8135653829 / 25000000000) (162713077681 / 500000000000) x90 := by
    apply bounds_add hx72 hx89 <;> norm_num
  let x91 : ℝ := x72-x88
  have hx91 : Bounds (8135653829 / 25000000000) (162713077681 / 500000000000) x91 := by
    exact hx90
  let x92 : ℝ := biasE (2559 / 3200)
  have hx92 : Bounds (8135653829 / 25000000000) (162713077681 / 500000000000) x92 := by
    simpa +zetaDelta only [biasE, div_one] using hx91
  let x93 : ℝ := biasE x7
  have hx93 : Bounds (64430989001 / 200000000000) (162713077681 / 500000000000) x93 := by
    exact bounds_biasE hx7 (by norm_num) (by norm_num) hx71.1 hx92.2
  let x94 : ℝ := (2 / 1)⁻¹
  have hx94 : Bounds (1 / 2) (1 / 2) x94 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x95 : ℝ := x93*x94
  have hx95 : Bounds (80538736251 / 500000000000) (162713077681 / 1000000000000) x95 := by
    apply bounds_mul hx93 hx94 <;> norm_num
  let x96 : ℝ := x93/(2 / 1)
  have hx96 : Bounds (80538736251 / 500000000000) (162713077681 / 1000000000000) x96 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx95
  let x97 : ℝ := Real.log (2 / 1)
  have hx97 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x97 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x98 : ℝ := (1 / 1)+(923269 / 1000000)
  have hx98 : Bounds (1923269 / 1000000) (1923269 / 1000000) x98 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((923269 / 1000000) : ℝ)) <;> norm_num
  let x99 : ℝ := (1 / 1)+(923269 / 1000000)
  have hx99 : Bounds (1923269 / 1000000) (1923269 / 1000000) x99 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((923269 / 1000000) : ℝ)) <;> norm_num
  let x100 : ℝ := Real.log x99
  have hx100 : Bounds (327013171 / 500000000) (654026343 / 1000000000) x100 := by
    exact bounds_log hx99 (by norm_num) (by simpa only [div_one] using reflection_log_9.1) (by simpa only [div_one] using reflection_log_9.2)
  let x101 : ℝ := x98*x100
  have hx101 : Bounds (1257868588751 / 1000000000000) (314467147669 / 250000000000) x101 := by
    apply bounds_mul hx98 hx100 <;> norm_num
  let x102 : ℝ := -(923269 / 1000000)
  have hx102 : Bounds (-923269 / 1000000) (-923269 / 1000000) x102 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((923269 / 1000000) : ℝ))
  let x103 : ℝ := (1 / 1)+x102
  have hx103 : Bounds (76731 / 1000000) (76731 / 1000000) x103 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx102 <;> norm_num
  let x104 : ℝ := (1 / 1)-(923269 / 1000000)
  have hx104 : Bounds (76731 / 1000000) (76731 / 1000000) x104 := by
    exact hx103
  let x105 : ℝ := -(923269 / 1000000)
  have hx105 : Bounds (-923269 / 1000000) (-923269 / 1000000) x105 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((923269 / 1000000) : ℝ))
  let x106 : ℝ := (1 / 1)+x105
  have hx106 : Bounds (76731 / 1000000) (76731 / 1000000) x106 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx105 <;> norm_num
  let x107 : ℝ := (1 / 1)-(923269 / 1000000)
  have hx107 : Bounds (76731 / 1000000) (76731 / 1000000) x107 := by
    exact hx106
  let x108 : ℝ := Real.log x107
  have hx108 : Bounds (-1283724741 / 500000000) (-1283724739 / 500000000) x108 := by
    exact bounds_log hx107 (by norm_num) (by simpa only [div_one] using reflection_log_10.1) (by simpa only [div_one] using reflection_log_10.2)
  let x109 : ℝ := x104*x108
  have hx109 : Bounds (-49250741551 / 250000000000) (-24625370737 / 125000000000) x109 := by
    apply bounds_mul hx104 hx108 <;> norm_num
  let x110 : ℝ := x101+x109
  have hx110 : Bounds (1060865622547 / 1000000000000) (53043281239 / 50000000000) x110 := by
    apply bounds_add hx101 hx109 <;> norm_num
  let x111 : ℝ := (2 / 1)⁻¹
  have hx111 : Bounds (1 / 2) (1 / 2) x111 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x112 : ℝ := x110*x111
  have hx112 : Bounds (530432811273 / 1000000000000) (53043281239 / 100000000000) x112 := by
    apply bounds_mul hx110 hx111 <;> norm_num
  let x113 : ℝ := x110/(2 / 1)
  have hx113 : Bounds (530432811273 / 1000000000000) (53043281239 / 100000000000) x113 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx112
  let x114 : ℝ := -x113
  have hx114 : Bounds (-53043281239 / 100000000000) (-530432811273 / 1000000000000) x114 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx113
  let x115 : ℝ := x97+x114
  have hx115 : Bounds (16271436761 / 100000000000) (162714369727 / 1000000000000) x115 := by
    apply bounds_add hx97 hx114 <;> norm_num
  let x116 : ℝ := x97-x113
  have hx116 : Bounds (16271436761 / 100000000000) (162714369727 / 1000000000000) x116 := by
    exact hx115
  let x117 : ℝ := biasE (923269 / 1000000)
  have hx117 : Bounds (16271436761 / 100000000000) (162714369727 / 1000000000000) x117 := by
    simpa +zetaDelta only [biasE, div_one] using hx116
  let x118 : ℝ := Real.log (2 / 1)
  have hx118 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x118 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x119 : ℝ := (1 / 1)+(231071 / 250000)
  have hx119 : Bounds (481071 / 250000) (481071 / 250000) x119 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((231071 / 250000) : ℝ)) <;> norm_num
  let x120 : ℝ := (1 / 1)+(231071 / 250000)
  have hx120 : Bounds (481071 / 250000) (481071 / 250000) x120 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((231071 / 250000) : ℝ)) <;> norm_num
  let x121 : ℝ := Real.log x120
  have hx121 : Bounds (13091079 / 20000000) (654553951 / 1000000000) x121 := by
    exact bounds_log hx120 (by norm_num) (by simpa only [div_one] using reflection_log_11.1) (by simpa only [div_one] using reflection_log_11.2)
  let x122 : ℝ := x119*x121
  have hx122 : Bounds (1259547693121 / 1000000000000) (1259547695047 / 1000000000000) x122 := by
    apply bounds_mul hx119 hx121 <;> norm_num
  let x123 : ℝ := -(231071 / 250000)
  have hx123 : Bounds (-231071 / 250000) (-231071 / 250000) x123 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((231071 / 250000) : ℝ))
  let x124 : ℝ := (1 / 1)+x123
  have hx124 : Bounds (18929 / 250000) (18929 / 250000) x124 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx123 <;> norm_num
  let x125 : ℝ := (1 / 1)-(231071 / 250000)
  have hx125 : Bounds (18929 / 250000) (18929 / 250000) x125 := by
    exact hx124
  let x126 : ℝ := -(231071 / 250000)
  have hx126 : Bounds (-231071 / 250000) (-231071 / 250000) x126 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((231071 / 250000) : ℝ))
  let x127 : ℝ := (1 / 1)+x126
  have hx127 : Bounds (18929 / 250000) (18929 / 250000) x127 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx126 <;> norm_num
  let x128 : ℝ := (1 / 1)-(231071 / 250000)
  have hx128 : Bounds (18929 / 250000) (18929 / 250000) x128 := by
    exact hx127
  let x129 : ℝ := Real.log x128
  have hx129 : Bounds (-1290382891 / 500000000) (-1290382889 / 500000000) x129 := by
    exact bounds_log hx128 (by norm_num) (by simpa only [div_one] using reflection_log_12.1) (by simpa only [div_one] using reflection_log_12.2)
  let x130 : ℝ := x125*x129
  have hx130 : Bounds (-3908105239 / 20000000000) (-195405261647 / 1000000000000) x130 := by
    apply bounds_mul hx125 hx129 <;> norm_num
  let x131 : ℝ := x122+x130
  have hx131 : Bounds (1064142431171 / 1000000000000) (5320712167 / 5000000000) x131 := by
    apply bounds_add hx122 hx130 <;> norm_num
  let x132 : ℝ := (2 / 1)⁻¹
  have hx132 : Bounds (1 / 2) (1 / 2) x132 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x133 : ℝ := x131*x132
  have hx133 : Bounds (106414243117 / 200000000000) (5320712167 / 10000000000) x133 := by
    apply bounds_mul hx131 hx132 <;> norm_num
  let x134 : ℝ := x131/(2 / 1)
  have hx134 : Bounds (106414243117 / 200000000000) (5320712167 / 10000000000) x134 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx133
  let x135 : ℝ := -x134
  have hx135 : Bounds (-5320712167 / 10000000000) (-106414243117 / 200000000000) x135 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx134
  let x136 : ℝ := x118+x135
  have hx136 : Bounds (1610759633 / 10000000000) (32215193083 / 200000000000) x136 := by
    apply bounds_add hx118 hx135 <;> norm_num
  let x137 : ℝ := x118-x134
  have hx137 : Bounds (1610759633 / 10000000000) (32215193083 / 200000000000) x137 := by
    exact hx136
  let x138 : ℝ := biasE (231071 / 250000)
  have hx138 : Bounds (1610759633 / 10000000000) (32215193083 / 200000000000) x138 := by
    simpa +zetaDelta only [biasE, div_one] using hx137
  let y : ℝ := 1 - 2 * entropyInverse (H (2*m)/2)
  have hLh' : Real.log 2 * (H (2*m)/2) = x96 := by
    simpa +zetaDelta only [div_one] using hLh
  have hy : Bounds (923269 / 1000000) (231071 / 250000) y := by
    apply entropyInverseBias_bracket
    · exact (div_nonneg (H_nonneg (by linarith [hm.1]) (by linarith [hm.2])) two_pos.le)
    · linarith [H_le_one (2*m)]
    · norm_num
    · norm_num
    · norm_num
    · have h1 : biasE (231071 / 250000) ≤ (32215193083 / 200000000000) := hx138.2
      have h2 : (80538736251 / 500000000000) ≤ x96 := hx96.1
      linarith [hLh']
    · have h1 : x96 ≤ (162713077681 / 1000000000000) := hx96.2
      have h2 : (16271436761 / 100000000000) ≤ biasE (923269 / 1000000) := hx117.1
      linarith [hLh']
  let x139 : ℝ := x3⁻¹
  have hx139 : Bounds (1109473866689 / 1000000000000) (555652022921 / 500000000000) x139 := by
    apply bounds_inv hx3 <;> norm_num
  let x140 : ℝ := x96*x139
  have hx140 : Bounds (178711246253 / 1000000000000) (180823701539 / 1000000000000) x140 := by
    apply bounds_mul hx96 hx139 <;> norm_num
  let x141 : ℝ := x96/x3
  have hx141 : Bounds (178711246253 / 1000000000000) (180823701539 / 1000000000000) x141 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx140
  let x142 : ℝ := Real.log (2 / 1)
  have hx142 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x142 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x143 : ℝ := (1 / 1)+(460447 / 500000)
  have hx143 : Bounds (960447 / 500000) (960447 / 500000) x143 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((460447 / 500000) : ℝ)) <;> norm_num
  let x144 : ℝ := (1 / 1)+(460447 / 500000)
  have hx144 : Bounds (960447 / 500000) (960447 / 500000) x144 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((460447 / 500000) : ℝ)) <;> norm_num
  let x145 : ℝ := Real.log x144
  have hx145 : Bounds (326395351 / 500000000) (652790703 / 1000000000) x145 := by
    exact bounds_log hx144 (by norm_num) (by simpa only [div_one] using reflection_log_13.1) (by simpa only [div_one] using reflection_log_13.2)
  let x146 : ℝ := x143*x145
  have hx146 : Bounds (1253941742727 / 1000000000000) (1253941744649 / 1000000000000) x146 := by
    apply bounds_mul hx143 hx145 <;> norm_num
  let x147 : ℝ := -(460447 / 500000)
  have hx147 : Bounds (-460447 / 500000) (-460447 / 500000) x147 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((460447 / 500000) : ℝ))
  let x148 : ℝ := (1 / 1)+x147
  have hx148 : Bounds (39553 / 500000) (39553 / 500000) x148 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx147 <;> norm_num
  let x149 : ℝ := (1 / 1)-(460447 / 500000)
  have hx149 : Bounds (39553 / 500000) (39553 / 500000) x149 := by
    exact hx148
  let x150 : ℝ := -(460447 / 500000)
  have hx150 : Bounds (-460447 / 500000) (-460447 / 500000) x150 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((460447 / 500000) : ℝ))
  let x151 : ℝ := (1 / 1)+x150
  have hx151 : Bounds (39553 / 500000) (39553 / 500000) x151 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx150 <;> norm_num
  let x152 : ℝ := (1 / 1)-(460447 / 500000)
  have hx152 : Bounds (39553 / 500000) (39553 / 500000) x152 := by
    exact hx151
  let x153 : ℝ := Real.log x152
  have hx153 : Bounds (-634241639 / 250000000) (-317120819 / 125000000) x153 := by
    exact bounds_log hx152 (by norm_num) (by simpa only [div_one] using reflection_log_14.1) (by simpa only [div_one] using reflection_log_14.2)
  let x154 : ℝ := x149*x153
  have hx154 : Bounds (-200689276379 / 1000000000000) (-100344638031 / 500000000000) x154 := by
    apply bounds_mul hx149 hx153 <;> norm_num
  let x155 : ℝ := x146+x154
  have hx155 : Bounds (263313116587 / 250000000000) (1053252468587 / 1000000000000) x155 := by
    apply bounds_add hx146 hx154 <;> norm_num
  let x156 : ℝ := (2 / 1)⁻¹
  have hx156 : Bounds (1 / 2) (1 / 2) x156 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x157 : ℝ := x155*x156
  have hx157 : Bounds (263313116587 / 500000000000) (263313117147 / 500000000000) x157 := by
    apply bounds_mul hx155 hx156 <;> norm_num
  let x158 : ℝ := x155/(2 / 1)
  have hx158 : Bounds (263313116587 / 500000000000) (263313117147 / 500000000000) x158 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx157
  let x159 : ℝ := -x158
  have hx159 : Bounds (-263313117147 / 500000000000) (-263313116587 / 500000000000) x159 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx158
  let x160 : ℝ := x142+x159
  have hx160 : Bounds (83260472853 / 500000000000) (83260473913 / 500000000000) x160 := by
    apply bounds_add hx142 hx159 <;> norm_num
  let x161 : ℝ := x142-x158
  have hx161 : Bounds (83260472853 / 500000000000) (83260473913 / 500000000000) x161 := by
    exact hx160
  let x162 : ℝ := biasE (460447 / 500000)
  have hx162 : Bounds (83260472853 / 500000000000) (83260473913 / 500000000000) x162 := by
    simpa +zetaDelta only [biasE, div_one] using hx161
  let x163 : ℝ := Real.log (2 / 1)
  have hx163 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x163 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x164 : ℝ := (1 / 1)+(92199 / 100000)
  have hx164 : Bounds (192199 / 100000) (192199 / 100000) x164 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((92199 / 100000) : ℝ)) <;> norm_num
  let x165 : ℝ := (1 / 1)+(92199 / 100000)
  have hx165 : Bounds (192199 / 100000) (192199 / 100000) x165 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((92199 / 100000) : ℝ)) <;> norm_num
  let x166 : ℝ := Real.log x165
  have hx166 : Bounds (653361107 / 1000000000) (163340277 / 250000000) x166 := by
    exact bounds_log hx165 (by norm_num) (by simpa only [div_one] using reflection_log_15.1) (by simpa only [div_one] using reflection_log_15.2)
  let x167 : ℝ := x164*x166
  have hx167 : Bounds (627876757021 / 500000000000) (251150703193 / 200000000000) x167 := by
    apply bounds_mul hx164 hx166 <;> norm_num
  let x168 : ℝ := -(92199 / 100000)
  have hx168 : Bounds (-92199 / 100000) (-92199 / 100000) x168 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((92199 / 100000) : ℝ))
  let x169 : ℝ := (1 / 1)+x168
  have hx169 : Bounds (7801 / 100000) (7801 / 100000) x169 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx168 <;> norm_num
  let x170 : ℝ := (1 / 1)-(92199 / 100000)
  have hx170 : Bounds (7801 / 100000) (7801 / 100000) x170 := by
    exact hx169
  let x171 : ℝ := -(92199 / 100000)
  have hx171 : Bounds (-92199 / 100000) (-92199 / 100000) x171 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((92199 / 100000) : ℝ))
  let x172 : ℝ := (1 / 1)+x171
  have hx172 : Bounds (7801 / 100000) (7801 / 100000) x172 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx171 <;> norm_num
  let x173 : ℝ := (1 / 1)-(92199 / 100000)
  have hx173 : Bounds (7801 / 100000) (7801 / 100000) x173 := by
    exact hx172
  let x174 : ℝ := Real.log x173
  have hx174 : Bounds (-2550918257 / 1000000000) (-2550918253 / 1000000000) x174 := by
    exact bounds_log hx173 (by norm_num) (by simpa only [div_one] using reflection_log_16.1) (by simpa only [div_one] using reflection_log_16.2)
  let x175 : ℝ := x170*x174
  have hx175 : Bounds (-198997133229 / 1000000000000) (-49749283229 / 250000000000) x175 := by
    apply bounds_mul hx170 hx174 <;> norm_num
  let x176 : ℝ := x167+x175
  have hx176 : Bounds (1056756380813 / 1000000000000) (1056756383049 / 1000000000000) x176 := by
    apply bounds_add hx167 hx175 <;> norm_num
  let x177 : ℝ := (2 / 1)⁻¹
  have hx177 : Bounds (1 / 2) (1 / 2) x177 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x178 : ℝ := x176*x177
  have hx178 : Bounds (264189095203 / 500000000000) (21135127661 / 40000000000) x178 := by
    apply bounds_mul hx176 hx177 <;> norm_num
  let x179 : ℝ := x176/(2 / 1)
  have hx179 : Bounds (264189095203 / 500000000000) (21135127661 / 40000000000) x179 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx178
  let x180 : ℝ := -x179
  have hx180 : Bounds (-21135127661 / 40000000000) (-264189095203 / 500000000000) x180 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx179
  let x181 : ℝ := x163+x180
  have hx181 : Bounds (6590759539 / 40000000000) (82384495297 / 500000000000) x181 := by
    apply bounds_add hx163 hx180 <;> norm_num
  let x182 : ℝ := x163-x179
  have hx182 : Bounds (6590759539 / 40000000000) (82384495297 / 500000000000) x182 := by
    exact hx181
  let x183 : ℝ := biasE (92199 / 100000)
  have hx183 : Bounds (6590759539 / 40000000000) (82384495297 / 500000000000) x183 := by
    simpa +zetaDelta only [biasE, div_one] using hx182
  let x184 : ℝ := x141*(460447 / 500000)
  have hx184 : Bounds (82287057203 / 500000000000) (83259730903 / 500000000000) x184 := by
    apply bounds_mul hx141 (bounds_const ((460447 / 500000) : ℝ)) <;> norm_num
  let x185 : ℝ := x141*(92199 / 100000)
  have hx185 : Bounds (41192495483 / 250000000000) (83358822291 / 500000000000) x185 := by
    apply bounds_mul hx141 (bounds_const ((92199 / 100000) : ℝ)) <;> norm_num
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
  have hc : Bounds (460447 / 500000) (92199 / 100000) c := by
    apply contact_bracket hc0 hcMem.2.le (by norm_num) (by norm_num) (by norm_num)
      (show 0 < x141 by linarith [hx141.1]) hcEq
    · have h1 : x141 * (460447 / 500000) ≤ (83259730903 / 500000000000) := hx184.2
      have h2 : (83260472853 / 500000000000) ≤ biasE (460447 / 500000) := hx162.1
      linarith
    · have h1 : biasE (92199 / 100000) ≤ (82384495297 / 500000000000) := hx183.2
      have h2 : (41192495483 / 250000000000) ≤ x141 * (92199 / 100000) := hx185.1
      linarith
  let x186 : ℝ := (1 / 1)+y
  have hx186 : Bounds (1923269 / 1000000) (481071 / 250000) x186 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hy <;> norm_num
  let x187 : ℝ := -y
  have hx187 : Bounds (-231071 / 250000) (-923269 / 1000000) x187 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hy
  let x188 : ℝ := (1 / 1)+x187
  have hx188 : Bounds (18929 / 250000) (76731 / 1000000) x188 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx187 <;> norm_num
  let x189 : ℝ := (1 / 1)-y
  have hx189 : Bounds (18929 / 250000) (76731 / 1000000) x189 := by
    exact hx188
  let x190 : ℝ := x189⁻¹
  have hx190 : Bounds (6516271129009 / 500000000000) (13207248137779 / 1000000000000) x190 := by
    apply bounds_inv hx189 <;> norm_num
  let x191 : ℝ := x186*x190
  have hx191 : Bounds (6266271129009 / 250000000000) (12707248137779 / 500000000000) x191 := by
    apply bounds_mul hx186 hx190 <;> norm_num
  let x192 : ℝ := x186/x189
  have hx192 : Bounds (6266271129009 / 250000000000) (12707248137779 / 500000000000) x192 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx191
  let x193 : ℝ := Real.log x192
  have hx193 : Bounds (161073791 / 50000000) (3235319733 / 1000000000) x193 := by
    exact bounds_log hx192 (by norm_num) (by simpa only [div_one] using reflection_log_17.1) (by simpa only [div_one] using reflection_log_18.2)
  let x194 : ℝ := (2 / 1)⁻¹
  have hx194 : Bounds (1 / 2) (1 / 2) x194 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x195 : ℝ := x193*x194
  have hx195 : Bounds (161073791 / 100000000) (3235319733 / 2000000000) x195 := by
    apply bounds_mul hx193 hx194 <;> norm_num
  let x196 : ℝ := x193/(2 / 1)
  have hx196 : Bounds (161073791 / 100000000) (3235319733 / 2000000000) x196 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx195
  let x197 : ℝ := (1 / 1)+c
  have hx197 : Bounds (960447 / 500000) (192199 / 100000) x197 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hc <;> norm_num
  let x198 : ℝ := -c
  have hx198 : Bounds (-92199 / 100000) (-460447 / 500000) x198 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hc
  let x199 : ℝ := (1 / 1)+x198
  have hx199 : Bounds (7801 / 100000) (39553 / 500000) x199 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx198 <;> norm_num
  let x200 : ℝ := (1 / 1)-c
  have hx200 : Bounds (7801 / 100000) (39553 / 500000) x200 := by
    exact hx199
  let x201 : ℝ := x200⁻¹
  have hx201 : Bounds (12641266149217 / 1000000000000) (6409434687861 / 500000000000) x201 := by
    apply bounds_inv hx200 <;> norm_num
  let x202 : ℝ := x197*x201
  have hx202 : Bounds (12141266149217 / 500000000000) (6159434687861 / 250000000000) x202 := by
    apply bounds_mul hx197 hx201 <;> norm_num
  let x203 : ℝ := x197/x200
  have hx203 : Bounds (12141266149217 / 500000000000) (6159434687861 / 250000000000) x203 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx202
  let x204 : ℝ := Real.log x203
  have hx204 : Bounds (1594878627 / 500000000) (640855873 / 200000000) x204 := by
    exact bounds_log hx203 (by norm_num) (by simpa only [div_one] using reflection_log_19.1) (by simpa only [div_one] using reflection_log_20.2)
  let x205 : ℝ := (2 / 1)⁻¹
  have hx205 : Bounds (1 / 2) (1 / 2) x205 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x206 : ℝ := x204*x205
  have hx206 : Bounds (1594878627 / 1000000000) (640855873 / 400000000) x206 := by
    apply bounds_mul hx204 hx205 <;> norm_num
  let x207 : ℝ := x204/(2 / 1)
  have hx207 : Bounds (1594878627 / 1000000000) (640855873 / 400000000) x207 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx206
  let x208 : ℝ := (2 / 1)*x50
  have hx208 : Bounds (196555288843 / 500000000000) (99372607423 / 250000000000) x208 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx50 <;> norm_num
  let x209 : ℝ := (2 / 1)*x96
  have hx209 : Bounds (80538736251 / 250000000000) (162713077681 / 500000000000) x209 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx96 <;> norm_num
  let x210 : ℝ := -x209
  have hx210 : Bounds (-162713077681 / 500000000000) (-80538736251 / 250000000000) x210 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx209
  let x211 : ℝ := x208+x210
  have hx211 : Bounds (16921105581 / 250000000000) (4708467793 / 62500000000) x211 := by
    apply bounds_add hx208 hx210 <;> norm_num
  let x212 : ℝ := x208-x209
  have hx212 : Bounds (16921105581 / 250000000000) (4708467793 / 62500000000) x212 := by
    exact hx211
  let x213 : ℝ := y*x196
  have hx213 : Bounds (1487144379427 / 1000000000000) (1495177132049 / 1000000000000) x213 := by
    apply bounds_mul hy hx196 <;> norm_num
  let x214 : ℝ := -x213
  have hx214 : Bounds (-1495177132049 / 1000000000000) (-1487144379427 / 1000000000000) x214 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx213
  let x215 : ℝ := x212+x214
  have hx215 : Bounds (-57099708389 / 40000000000) (-1411808894739 / 1000000000000) x215 := by
    apply bounds_add hx212 hx214 <;> norm_num
  let x216 : ℝ := x212-x213
  have hx216 : Bounds (-57099708389 / 40000000000) (-1411808894739 / 1000000000000) x216 := by
    exact hx215
  let x217 : ℝ := x3*x207
  have hx217 : Bounds (717570782257 / 500000000000) (90253347251 / 62500000000) x217 := by
    apply bounds_mul hx3 hx207 <;> norm_num
  let x218 : ℝ := x216+x217
  have hx218 : Bounds (7648854789 / 1000000000000) (32244661277 / 1000000000000) x218 := by
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

theorem acceptedCertificate : DoubleCapBiasCellCertificate (1263 / 25600) (641 / 12800) (fun m => H (2*m)/2) where
  domain := by norm_num
  sound m hmLo hmHi := by
    exact cell_bias_nonneg m ⟨hmLo, hmHi⟩

theorem accepted_cell :
    ∀ m, (1263 / 25600) ≤ m → m ≤ (641 / 12800) → 0 ≤ doubleCapLowResidual m := by
  intro m hmLo hmHi
  unfold doubleCapLowResidual
  apply doubleCapEndpointResidual_nonneg_of_biasCell acceptedCertificate hmLo hmHi
  exact div_pos (H_pos (by linarith) (by linarith)) two_pos

#print axioms cell_bias_nonneg
#print axioms accepted_cell

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0164

end


