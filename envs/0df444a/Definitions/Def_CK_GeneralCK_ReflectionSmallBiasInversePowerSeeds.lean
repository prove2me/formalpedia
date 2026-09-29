-- Prove2me | Definitions.Def_CK_GeneralCK_ReflectionSmallBiasInversePowerSeeds
-- name    : CK_GeneralCK_ReflectionSmallBiasInversePowerSeeds
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T16:04:52.050412+00:00
-- url     : https://prove2.me/theorems/727e9d74-7755-43c6-9c73-0a43fcaf678e
-- title:
--   Courtade–Kumar proof module `GeneralCK.ReflectionSmallBiasInversePowerSeeds` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.ReflectionSmallBiasInversePowerSeeds` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.ReflectionSmallBiasInversePowerSeeds` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.ReflectionSmallBiasInversePowerSeeds (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/ReflectionSmallBiasInversePowerSeeds.lean)

import Definitions.Def_CK_GeneralCK_ReflectionSmallBiasJetReplay

-- ===== source module GeneralCK.ReflectionSmallBiasInversePowerSeeds =====
section

namespace GeneralCK.Reflection.SmallBiasInversePowerSeeds

open SmallBiasPolynomial SmallBiasJet

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def seed1 : List Term :=
  [⟨0, 0, 0, (1 / 1 : ℚ)⟩,
   ⟨1, 0, 0, (1 / 1 : ℚ)⟩,
   ⟨2, 0, 0, (1 / 1 : ℚ)⟩,
   ⟨3, 0, 0, (1 / 1 : ℚ)⟩,
   ⟨4, 0, 0, (1 / 1 : ℚ)⟩,
   ⟨5, 0, 0, (1 / 1 : ℚ)⟩,
   ⟨6, 0, 0, (1 / 1 : ℚ)⟩,
   ⟨7, 0, 0, (1 / 1 : ℚ)⟩,
   ⟨8, 0, 0, (1 / 1 : ℚ)⟩,
   ⟨9, 0, 0, (1 / 1 : ℚ)⟩,
   ⟨10, 0, 0, (1 / 1 : ℚ)⟩,
   ⟨11, 0, 0, (1 / 1 : ℚ)⟩,
   ⟨12, 0, 0, (1 / 1 : ℚ)⟩,
   ⟨13, 0, 0, (1 / 1 : ℚ)⟩,
   ⟨14, 0, 0, (1 / 1 : ℚ)⟩,
   ⟨15, 0, 0, (1 / 1 : ℚ)⟩,
   ⟨16, 0, 0, (1 / 1 : ℚ)⟩,
   ⟨17, 0, 0, (1 / 1 : ℚ)⟩,
   ⟨18, 0, 0, (1 / 1 : ℚ)⟩,
   ⟨19, 0, 0, (1 / 1 : ℚ)⟩,
   ⟨20, 0, 0, (1 / 1 : ℚ)⟩,
   ⟨21, 0, 0, (1 / 1 : ℚ)⟩,
   ⟨22, 0, 0, (1 / 1 : ℚ)⟩,
   ⟨23, 0, 0, (1 / 1 : ℚ)⟩]

theorem seed1_checked : equalityCheck (geometric 24 coordinateA) seed1 = true := by
  decide +kernel

theorem seed1_approximates {k : ℂ} (hk : k ≠ 0) :
    Approximates 24 k (fun z => ((1-z.1)⁻¹)^1) seed1 := by
  simpa only [pow_one] using
    ((Approximates.coordinateA 24 k).inverse_one_sub hk (by rfl)).replacePolynomial
      (equalityCheck_sound seed1_checked k)

def seed2 : List Term :=
  [⟨0, 0, 0, (1 / 1 : ℚ)⟩,
   ⟨1, 0, 0, (2 / 1 : ℚ)⟩,
   ⟨2, 0, 0, (3 / 1 : ℚ)⟩,
   ⟨3, 0, 0, (4 / 1 : ℚ)⟩,
   ⟨4, 0, 0, (5 / 1 : ℚ)⟩,
   ⟨5, 0, 0, (6 / 1 : ℚ)⟩,
   ⟨6, 0, 0, (7 / 1 : ℚ)⟩,
   ⟨7, 0, 0, (8 / 1 : ℚ)⟩,
   ⟨8, 0, 0, (9 / 1 : ℚ)⟩,
   ⟨9, 0, 0, (10 / 1 : ℚ)⟩,
   ⟨10, 0, 0, (11 / 1 : ℚ)⟩,
   ⟨11, 0, 0, (12 / 1 : ℚ)⟩,
   ⟨12, 0, 0, (13 / 1 : ℚ)⟩,
   ⟨13, 0, 0, (14 / 1 : ℚ)⟩,
   ⟨14, 0, 0, (15 / 1 : ℚ)⟩,
   ⟨15, 0, 0, (16 / 1 : ℚ)⟩,
   ⟨16, 0, 0, (17 / 1 : ℚ)⟩,
   ⟨17, 0, 0, (18 / 1 : ℚ)⟩,
   ⟨18, 0, 0, (19 / 1 : ℚ)⟩,
   ⟨19, 0, 0, (20 / 1 : ℚ)⟩,
   ⟨20, 0, 0, (21 / 1 : ℚ)⟩,
   ⟨21, 0, 0, (22 / 1 : ℚ)⟩,
   ⟨22, 0, 0, (23 / 1 : ℚ)⟩,
   ⟨23, 0, 0, (24 / 1 : ℚ)⟩]

theorem seed2_checked : equalityCheck (mulTrunc 24 seed1 seed1) seed2 = true := by
  decide +kernel

theorem seed2_approximates {k : ℂ} (hk : k ≠ 0) :
    Approximates 24 k (fun z => ((1-z.1)⁻¹)^2) seed2 := by
  convert ((seed1_approximates hk).mul hk (seed1_approximates hk)).replacePolynomial
    (equalityCheck_sound seed2_checked k) using 1
  funext z
  ring

def seed3 : List Term :=
  [⟨0, 0, 0, (1 / 1 : ℚ)⟩,
   ⟨1, 0, 0, (3 / 1 : ℚ)⟩,
   ⟨2, 0, 0, (6 / 1 : ℚ)⟩,
   ⟨3, 0, 0, (10 / 1 : ℚ)⟩,
   ⟨4, 0, 0, (15 / 1 : ℚ)⟩,
   ⟨5, 0, 0, (21 / 1 : ℚ)⟩,
   ⟨6, 0, 0, (28 / 1 : ℚ)⟩,
   ⟨7, 0, 0, (36 / 1 : ℚ)⟩,
   ⟨8, 0, 0, (45 / 1 : ℚ)⟩,
   ⟨9, 0, 0, (55 / 1 : ℚ)⟩,
   ⟨10, 0, 0, (66 / 1 : ℚ)⟩,
   ⟨11, 0, 0, (78 / 1 : ℚ)⟩,
   ⟨12, 0, 0, (91 / 1 : ℚ)⟩,
   ⟨13, 0, 0, (105 / 1 : ℚ)⟩,
   ⟨14, 0, 0, (120 / 1 : ℚ)⟩,
   ⟨15, 0, 0, (136 / 1 : ℚ)⟩,
   ⟨16, 0, 0, (153 / 1 : ℚ)⟩,
   ⟨17, 0, 0, (171 / 1 : ℚ)⟩,
   ⟨18, 0, 0, (190 / 1 : ℚ)⟩,
   ⟨19, 0, 0, (210 / 1 : ℚ)⟩,
   ⟨20, 0, 0, (231 / 1 : ℚ)⟩,
   ⟨21, 0, 0, (253 / 1 : ℚ)⟩,
   ⟨22, 0, 0, (276 / 1 : ℚ)⟩,
   ⟨23, 0, 0, (300 / 1 : ℚ)⟩]

theorem seed3_checked : equalityCheck (mulTrunc 24 seed2 seed1) seed3 = true := by
  decide +kernel

theorem seed3_approximates {k : ℂ} (hk : k ≠ 0) :
    Approximates 24 k (fun z => ((1-z.1)⁻¹)^3) seed3 := by
  convert ((seed2_approximates hk).mul hk (seed1_approximates hk)).replacePolynomial
    (equalityCheck_sound seed3_checked k) using 1
  funext z
  ring

def seed4 : List Term :=
  [⟨0, 0, 0, (1 / 1 : ℚ)⟩,
   ⟨1, 0, 0, (4 / 1 : ℚ)⟩,
   ⟨2, 0, 0, (10 / 1 : ℚ)⟩,
   ⟨3, 0, 0, (20 / 1 : ℚ)⟩,
   ⟨4, 0, 0, (35 / 1 : ℚ)⟩,
   ⟨5, 0, 0, (56 / 1 : ℚ)⟩,
   ⟨6, 0, 0, (84 / 1 : ℚ)⟩,
   ⟨7, 0, 0, (120 / 1 : ℚ)⟩,
   ⟨8, 0, 0, (165 / 1 : ℚ)⟩,
   ⟨9, 0, 0, (220 / 1 : ℚ)⟩,
   ⟨10, 0, 0, (286 / 1 : ℚ)⟩,
   ⟨11, 0, 0, (364 / 1 : ℚ)⟩,
   ⟨12, 0, 0, (455 / 1 : ℚ)⟩,
   ⟨13, 0, 0, (560 / 1 : ℚ)⟩,
   ⟨14, 0, 0, (680 / 1 : ℚ)⟩,
   ⟨15, 0, 0, (816 / 1 : ℚ)⟩,
   ⟨16, 0, 0, (969 / 1 : ℚ)⟩,
   ⟨17, 0, 0, (1140 / 1 : ℚ)⟩,
   ⟨18, 0, 0, (1330 / 1 : ℚ)⟩,
   ⟨19, 0, 0, (1540 / 1 : ℚ)⟩,
   ⟨20, 0, 0, (1771 / 1 : ℚ)⟩,
   ⟨21, 0, 0, (2024 / 1 : ℚ)⟩,
   ⟨22, 0, 0, (2300 / 1 : ℚ)⟩,
   ⟨23, 0, 0, (2600 / 1 : ℚ)⟩]

theorem seed4_checked : equalityCheck (mulTrunc 24 seed3 seed1) seed4 = true := by
  decide +kernel

theorem seed4_approximates {k : ℂ} (hk : k ≠ 0) :
    Approximates 24 k (fun z => ((1-z.1)⁻¹)^4) seed4 := by
  convert ((seed3_approximates hk).mul hk (seed1_approximates hk)).replacePolynomial
    (equalityCheck_sound seed4_checked k) using 1
  funext z
  ring

def seed5 : List Term :=
  [⟨0, 0, 0, (1 / 1 : ℚ)⟩,
   ⟨1, 0, 0, (5 / 1 : ℚ)⟩,
   ⟨2, 0, 0, (15 / 1 : ℚ)⟩,
   ⟨3, 0, 0, (35 / 1 : ℚ)⟩,
   ⟨4, 0, 0, (70 / 1 : ℚ)⟩,
   ⟨5, 0, 0, (126 / 1 : ℚ)⟩,
   ⟨6, 0, 0, (210 / 1 : ℚ)⟩,
   ⟨7, 0, 0, (330 / 1 : ℚ)⟩,
   ⟨8, 0, 0, (495 / 1 : ℚ)⟩,
   ⟨9, 0, 0, (715 / 1 : ℚ)⟩,
   ⟨10, 0, 0, (1001 / 1 : ℚ)⟩,
   ⟨11, 0, 0, (1365 / 1 : ℚ)⟩,
   ⟨12, 0, 0, (1820 / 1 : ℚ)⟩,
   ⟨13, 0, 0, (2380 / 1 : ℚ)⟩,
   ⟨14, 0, 0, (3060 / 1 : ℚ)⟩,
   ⟨15, 0, 0, (3876 / 1 : ℚ)⟩,
   ⟨16, 0, 0, (4845 / 1 : ℚ)⟩,
   ⟨17, 0, 0, (5985 / 1 : ℚ)⟩,
   ⟨18, 0, 0, (7315 / 1 : ℚ)⟩,
   ⟨19, 0, 0, (8855 / 1 : ℚ)⟩,
   ⟨20, 0, 0, (10626 / 1 : ℚ)⟩,
   ⟨21, 0, 0, (12650 / 1 : ℚ)⟩,
   ⟨22, 0, 0, (14950 / 1 : ℚ)⟩,
   ⟨23, 0, 0, (17550 / 1 : ℚ)⟩]

theorem seed5_checked : equalityCheck (mulTrunc 24 seed4 seed1) seed5 = true := by
  decide +kernel

theorem seed5_approximates {k : ℂ} (hk : k ≠ 0) :
    Approximates 24 k (fun z => ((1-z.1)⁻¹)^5) seed5 := by
  convert ((seed4_approximates hk).mul hk (seed1_approximates hk)).replacePolynomial
    (equalityCheck_sound seed5_checked k) using 1
  funext z
  ring

def seed6 : List Term :=
  [⟨0, 0, 0, (1 / 1 : ℚ)⟩,
   ⟨1, 0, 0, (6 / 1 : ℚ)⟩,
   ⟨2, 0, 0, (21 / 1 : ℚ)⟩,
   ⟨3, 0, 0, (56 / 1 : ℚ)⟩,
   ⟨4, 0, 0, (126 / 1 : ℚ)⟩,
   ⟨5, 0, 0, (252 / 1 : ℚ)⟩,
   ⟨6, 0, 0, (462 / 1 : ℚ)⟩,
   ⟨7, 0, 0, (792 / 1 : ℚ)⟩,
   ⟨8, 0, 0, (1287 / 1 : ℚ)⟩,
   ⟨9, 0, 0, (2002 / 1 : ℚ)⟩,
   ⟨10, 0, 0, (3003 / 1 : ℚ)⟩,
   ⟨11, 0, 0, (4368 / 1 : ℚ)⟩,
   ⟨12, 0, 0, (6188 / 1 : ℚ)⟩,
   ⟨13, 0, 0, (8568 / 1 : ℚ)⟩,
   ⟨14, 0, 0, (11628 / 1 : ℚ)⟩,
   ⟨15, 0, 0, (15504 / 1 : ℚ)⟩,
   ⟨16, 0, 0, (20349 / 1 : ℚ)⟩,
   ⟨17, 0, 0, (26334 / 1 : ℚ)⟩,
   ⟨18, 0, 0, (33649 / 1 : ℚ)⟩,
   ⟨19, 0, 0, (42504 / 1 : ℚ)⟩,
   ⟨20, 0, 0, (53130 / 1 : ℚ)⟩,
   ⟨21, 0, 0, (65780 / 1 : ℚ)⟩,
   ⟨22, 0, 0, (80730 / 1 : ℚ)⟩,
   ⟨23, 0, 0, (98280 / 1 : ℚ)⟩]

theorem seed6_checked : equalityCheck (mulTrunc 24 seed5 seed1) seed6 = true := by
  decide +kernel

theorem seed6_approximates {k : ℂ} (hk : k ≠ 0) :
    Approximates 24 k (fun z => ((1-z.1)⁻¹)^6) seed6 := by
  convert ((seed5_approximates hk).mul hk (seed1_approximates hk)).replacePolynomial
    (equalityCheck_sound seed6_checked k) using 1
  funext z
  ring

def seed7 : List Term :=
  [⟨0, 0, 0, (1 / 1 : ℚ)⟩,
   ⟨1, 0, 0, (7 / 1 : ℚ)⟩,
   ⟨2, 0, 0, (28 / 1 : ℚ)⟩,
   ⟨3, 0, 0, (84 / 1 : ℚ)⟩,
   ⟨4, 0, 0, (210 / 1 : ℚ)⟩,
   ⟨5, 0, 0, (462 / 1 : ℚ)⟩,
   ⟨6, 0, 0, (924 / 1 : ℚ)⟩,
   ⟨7, 0, 0, (1716 / 1 : ℚ)⟩,
   ⟨8, 0, 0, (3003 / 1 : ℚ)⟩,
   ⟨9, 0, 0, (5005 / 1 : ℚ)⟩,
   ⟨10, 0, 0, (8008 / 1 : ℚ)⟩,
   ⟨11, 0, 0, (12376 / 1 : ℚ)⟩,
   ⟨12, 0, 0, (18564 / 1 : ℚ)⟩,
   ⟨13, 0, 0, (27132 / 1 : ℚ)⟩,
   ⟨14, 0, 0, (38760 / 1 : ℚ)⟩,
   ⟨15, 0, 0, (54264 / 1 : ℚ)⟩,
   ⟨16, 0, 0, (74613 / 1 : ℚ)⟩,
   ⟨17, 0, 0, (100947 / 1 : ℚ)⟩,
   ⟨18, 0, 0, (134596 / 1 : ℚ)⟩,
   ⟨19, 0, 0, (177100 / 1 : ℚ)⟩,
   ⟨20, 0, 0, (230230 / 1 : ℚ)⟩,
   ⟨21, 0, 0, (296010 / 1 : ℚ)⟩,
   ⟨22, 0, 0, (376740 / 1 : ℚ)⟩,
   ⟨23, 0, 0, (475020 / 1 : ℚ)⟩]

theorem seed7_checked : equalityCheck (mulTrunc 24 seed6 seed1) seed7 = true := by
  decide +kernel

theorem seed7_approximates {k : ℂ} (hk : k ≠ 0) :
    Approximates 24 k (fun z => ((1-z.1)⁻¹)^7) seed7 := by
  convert ((seed6_approximates hk).mul hk (seed1_approximates hk)).replacePolynomial
    (equalityCheck_sound seed7_checked k) using 1
  funext z
  ring

def seed8 : List Term :=
  [⟨0, 0, 0, (1 / 1 : ℚ)⟩,
   ⟨1, 0, 0, (8 / 1 : ℚ)⟩,
   ⟨2, 0, 0, (36 / 1 : ℚ)⟩,
   ⟨3, 0, 0, (120 / 1 : ℚ)⟩,
   ⟨4, 0, 0, (330 / 1 : ℚ)⟩,
   ⟨5, 0, 0, (792 / 1 : ℚ)⟩,
   ⟨6, 0, 0, (1716 / 1 : ℚ)⟩,
   ⟨7, 0, 0, (3432 / 1 : ℚ)⟩,
   ⟨8, 0, 0, (6435 / 1 : ℚ)⟩,
   ⟨9, 0, 0, (11440 / 1 : ℚ)⟩,
   ⟨10, 0, 0, (19448 / 1 : ℚ)⟩,
   ⟨11, 0, 0, (31824 / 1 : ℚ)⟩,
   ⟨12, 0, 0, (50388 / 1 : ℚ)⟩,
   ⟨13, 0, 0, (77520 / 1 : ℚ)⟩,
   ⟨14, 0, 0, (116280 / 1 : ℚ)⟩,
   ⟨15, 0, 0, (170544 / 1 : ℚ)⟩,
   ⟨16, 0, 0, (245157 / 1 : ℚ)⟩,
   ⟨17, 0, 0, (346104 / 1 : ℚ)⟩,
   ⟨18, 0, 0, (480700 / 1 : ℚ)⟩,
   ⟨19, 0, 0, (657800 / 1 : ℚ)⟩,
   ⟨20, 0, 0, (888030 / 1 : ℚ)⟩,
   ⟨21, 0, 0, (1184040 / 1 : ℚ)⟩,
   ⟨22, 0, 0, (1560780 / 1 : ℚ)⟩,
   ⟨23, 0, 0, (2035800 / 1 : ℚ)⟩]

theorem seed8_checked : equalityCheck (mulTrunc 24 seed7 seed1) seed8 = true := by
  decide +kernel

theorem seed8_approximates {k : ℂ} (hk : k ≠ 0) :
    Approximates 24 k (fun z => ((1-z.1)⁻¹)^8) seed8 := by
  convert ((seed7_approximates hk).mul hk (seed1_approximates hk)).replacePolynomial
    (equalityCheck_sound seed8_checked k) using 1
  funext z
  ring

def seed9 : List Term :=
  [⟨0, 0, 0, (1 / 1 : ℚ)⟩,
   ⟨1, 0, 0, (9 / 1 : ℚ)⟩,
   ⟨2, 0, 0, (45 / 1 : ℚ)⟩,
   ⟨3, 0, 0, (165 / 1 : ℚ)⟩,
   ⟨4, 0, 0, (495 / 1 : ℚ)⟩,
   ⟨5, 0, 0, (1287 / 1 : ℚ)⟩,
   ⟨6, 0, 0, (3003 / 1 : ℚ)⟩,
   ⟨7, 0, 0, (6435 / 1 : ℚ)⟩,
   ⟨8, 0, 0, (12870 / 1 : ℚ)⟩,
   ⟨9, 0, 0, (24310 / 1 : ℚ)⟩,
   ⟨10, 0, 0, (43758 / 1 : ℚ)⟩,
   ⟨11, 0, 0, (75582 / 1 : ℚ)⟩,
   ⟨12, 0, 0, (125970 / 1 : ℚ)⟩,
   ⟨13, 0, 0, (203490 / 1 : ℚ)⟩,
   ⟨14, 0, 0, (319770 / 1 : ℚ)⟩,
   ⟨15, 0, 0, (490314 / 1 : ℚ)⟩,
   ⟨16, 0, 0, (735471 / 1 : ℚ)⟩,
   ⟨17, 0, 0, (1081575 / 1 : ℚ)⟩,
   ⟨18, 0, 0, (1562275 / 1 : ℚ)⟩,
   ⟨19, 0, 0, (2220075 / 1 : ℚ)⟩,
   ⟨20, 0, 0, (3108105 / 1 : ℚ)⟩,
   ⟨21, 0, 0, (4292145 / 1 : ℚ)⟩,
   ⟨22, 0, 0, (5852925 / 1 : ℚ)⟩,
   ⟨23, 0, 0, (7888725 / 1 : ℚ)⟩]

theorem seed9_checked : equalityCheck (mulTrunc 24 seed8 seed1) seed9 = true := by
  decide +kernel

theorem seed9_approximates {k : ℂ} (hk : k ≠ 0) :
    Approximates 24 k (fun z => ((1-z.1)⁻¹)^9) seed9 := by
  convert ((seed8_approximates hk).mul hk (seed1_approximates hk)).replacePolynomial
    (equalityCheck_sound seed9_checked k) using 1
  funext z
  ring

def seed10 : List Term :=
  [⟨0, 0, 0, (1 / 1 : ℚ)⟩,
   ⟨1, 0, 0, (10 / 1 : ℚ)⟩,
   ⟨2, 0, 0, (55 / 1 : ℚ)⟩,
   ⟨3, 0, 0, (220 / 1 : ℚ)⟩,
   ⟨4, 0, 0, (715 / 1 : ℚ)⟩,
   ⟨5, 0, 0, (2002 / 1 : ℚ)⟩,
   ⟨6, 0, 0, (5005 / 1 : ℚ)⟩,
   ⟨7, 0, 0, (11440 / 1 : ℚ)⟩,
   ⟨8, 0, 0, (24310 / 1 : ℚ)⟩,
   ⟨9, 0, 0, (48620 / 1 : ℚ)⟩,
   ⟨10, 0, 0, (92378 / 1 : ℚ)⟩,
   ⟨11, 0, 0, (167960 / 1 : ℚ)⟩,
   ⟨12, 0, 0, (293930 / 1 : ℚ)⟩,
   ⟨13, 0, 0, (497420 / 1 : ℚ)⟩,
   ⟨14, 0, 0, (817190 / 1 : ℚ)⟩,
   ⟨15, 0, 0, (1307504 / 1 : ℚ)⟩,
   ⟨16, 0, 0, (2042975 / 1 : ℚ)⟩,
   ⟨17, 0, 0, (3124550 / 1 : ℚ)⟩,
   ⟨18, 0, 0, (4686825 / 1 : ℚ)⟩,
   ⟨19, 0, 0, (6906900 / 1 : ℚ)⟩,
   ⟨20, 0, 0, (10015005 / 1 : ℚ)⟩,
   ⟨21, 0, 0, (14307150 / 1 : ℚ)⟩,
   ⟨22, 0, 0, (20160075 / 1 : ℚ)⟩,
   ⟨23, 0, 0, (28048800 / 1 : ℚ)⟩]

theorem seed10_checked : equalityCheck (mulTrunc 24 seed9 seed1) seed10 = true := by
  decide +kernel

theorem seed10_approximates {k : ℂ} (hk : k ≠ 0) :
    Approximates 24 k (fun z => ((1-z.1)⁻¹)^10) seed10 := by
  convert ((seed9_approximates hk).mul hk (seed1_approximates hk)).replacePolynomial
    (equalityCheck_sound seed10_checked k) using 1
  funext z
  ring

def seed11 : List Term :=
  [⟨0, 0, 0, (1 / 1 : ℚ)⟩,
   ⟨1, 0, 0, (11 / 1 : ℚ)⟩,
   ⟨2, 0, 0, (66 / 1 : ℚ)⟩,
   ⟨3, 0, 0, (286 / 1 : ℚ)⟩,
   ⟨4, 0, 0, (1001 / 1 : ℚ)⟩,
   ⟨5, 0, 0, (3003 / 1 : ℚ)⟩,
   ⟨6, 0, 0, (8008 / 1 : ℚ)⟩,
   ⟨7, 0, 0, (19448 / 1 : ℚ)⟩,
   ⟨8, 0, 0, (43758 / 1 : ℚ)⟩,
   ⟨9, 0, 0, (92378 / 1 : ℚ)⟩,
   ⟨10, 0, 0, (184756 / 1 : ℚ)⟩,
   ⟨11, 0, 0, (352716 / 1 : ℚ)⟩,
   ⟨12, 0, 0, (646646 / 1 : ℚ)⟩,
   ⟨13, 0, 0, (1144066 / 1 : ℚ)⟩,
   ⟨14, 0, 0, (1961256 / 1 : ℚ)⟩,
   ⟨15, 0, 0, (3268760 / 1 : ℚ)⟩,
   ⟨16, 0, 0, (5311735 / 1 : ℚ)⟩,
   ⟨17, 0, 0, (8436285 / 1 : ℚ)⟩,
   ⟨18, 0, 0, (13123110 / 1 : ℚ)⟩,
   ⟨19, 0, 0, (20030010 / 1 : ℚ)⟩,
   ⟨20, 0, 0, (30045015 / 1 : ℚ)⟩,
   ⟨21, 0, 0, (44352165 / 1 : ℚ)⟩,
   ⟨22, 0, 0, (64512240 / 1 : ℚ)⟩,
   ⟨23, 0, 0, (92561040 / 1 : ℚ)⟩]

theorem seed11_checked : equalityCheck (mulTrunc 24 seed10 seed1) seed11 = true := by
  decide +kernel

theorem seed11_approximates {k : ℂ} (hk : k ≠ 0) :
    Approximates 24 k (fun z => ((1-z.1)⁻¹)^11) seed11 := by
  convert ((seed10_approximates hk).mul hk (seed1_approximates hk)).replacePolynomial
    (equalityCheck_sound seed11_checked k) using 1
  funext z
  ring

def seed12 : List Term :=
  [⟨0, 0, 0, (1 / 1 : ℚ)⟩,
   ⟨1, 0, 0, (12 / 1 : ℚ)⟩,
   ⟨2, 0, 0, (78 / 1 : ℚ)⟩,
   ⟨3, 0, 0, (364 / 1 : ℚ)⟩,
   ⟨4, 0, 0, (1365 / 1 : ℚ)⟩,
   ⟨5, 0, 0, (4368 / 1 : ℚ)⟩,
   ⟨6, 0, 0, (12376 / 1 : ℚ)⟩,
   ⟨7, 0, 0, (31824 / 1 : ℚ)⟩,
   ⟨8, 0, 0, (75582 / 1 : ℚ)⟩,
   ⟨9, 0, 0, (167960 / 1 : ℚ)⟩,
   ⟨10, 0, 0, (352716 / 1 : ℚ)⟩,
   ⟨11, 0, 0, (705432 / 1 : ℚ)⟩,
   ⟨12, 0, 0, (1352078 / 1 : ℚ)⟩,
   ⟨13, 0, 0, (2496144 / 1 : ℚ)⟩,
   ⟨14, 0, 0, (4457400 / 1 : ℚ)⟩,
   ⟨15, 0, 0, (7726160 / 1 : ℚ)⟩,
   ⟨16, 0, 0, (13037895 / 1 : ℚ)⟩,
   ⟨17, 0, 0, (21474180 / 1 : ℚ)⟩,
   ⟨18, 0, 0, (34597290 / 1 : ℚ)⟩,
   ⟨19, 0, 0, (54627300 / 1 : ℚ)⟩,
   ⟨20, 0, 0, (84672315 / 1 : ℚ)⟩,
   ⟨21, 0, 0, (129024480 / 1 : ℚ)⟩,
   ⟨22, 0, 0, (193536720 / 1 : ℚ)⟩,
   ⟨23, 0, 0, (286097760 / 1 : ℚ)⟩]

theorem seed12_checked : equalityCheck (mulTrunc 24 seed11 seed1) seed12 = true := by
  decide +kernel

theorem seed12_approximates {k : ℂ} (hk : k ≠ 0) :
    Approximates 24 k (fun z => ((1-z.1)⁻¹)^12) seed12 := by
  convert ((seed11_approximates hk).mul hk (seed1_approximates hk)).replacePolynomial
    (equalityCheck_sound seed12_checked k) using 1
  funext z
  ring

def seed13 : List Term :=
  [⟨0, 0, 0, (1 / 1 : ℚ)⟩,
   ⟨1, 0, 0, (13 / 1 : ℚ)⟩,
   ⟨2, 0, 0, (91 / 1 : ℚ)⟩,
   ⟨3, 0, 0, (455 / 1 : ℚ)⟩,
   ⟨4, 0, 0, (1820 / 1 : ℚ)⟩,
   ⟨5, 0, 0, (6188 / 1 : ℚ)⟩,
   ⟨6, 0, 0, (18564 / 1 : ℚ)⟩,
   ⟨7, 0, 0, (50388 / 1 : ℚ)⟩,
   ⟨8, 0, 0, (125970 / 1 : ℚ)⟩,
   ⟨9, 0, 0, (293930 / 1 : ℚ)⟩,
   ⟨10, 0, 0, (646646 / 1 : ℚ)⟩,
   ⟨11, 0, 0, (1352078 / 1 : ℚ)⟩,
   ⟨12, 0, 0, (2704156 / 1 : ℚ)⟩,
   ⟨13, 0, 0, (5200300 / 1 : ℚ)⟩,
   ⟨14, 0, 0, (9657700 / 1 : ℚ)⟩,
   ⟨15, 0, 0, (17383860 / 1 : ℚ)⟩,
   ⟨16, 0, 0, (30421755 / 1 : ℚ)⟩,
   ⟨17, 0, 0, (51895935 / 1 : ℚ)⟩,
   ⟨18, 0, 0, (86493225 / 1 : ℚ)⟩,
   ⟨19, 0, 0, (141120525 / 1 : ℚ)⟩,
   ⟨20, 0, 0, (225792840 / 1 : ℚ)⟩,
   ⟨21, 0, 0, (354817320 / 1 : ℚ)⟩,
   ⟨22, 0, 0, (548354040 / 1 : ℚ)⟩,
   ⟨23, 0, 0, (834451800 / 1 : ℚ)⟩]

theorem seed13_checked : equalityCheck (mulTrunc 24 seed12 seed1) seed13 = true := by
  decide +kernel

theorem seed13_approximates {k : ℂ} (hk : k ≠ 0) :
    Approximates 24 k (fun z => ((1-z.1)⁻¹)^13) seed13 := by
  convert ((seed12_approximates hk).mul hk (seed1_approximates hk)).replacePolynomial
    (equalityCheck_sound seed13_checked k) using 1
  funext z
  ring

def seed14 : List Term :=
  [⟨0, 0, 0, (1 / 1 : ℚ)⟩,
   ⟨1, 0, 0, (14 / 1 : ℚ)⟩,
   ⟨2, 0, 0, (105 / 1 : ℚ)⟩,
   ⟨3, 0, 0, (560 / 1 : ℚ)⟩,
   ⟨4, 0, 0, (2380 / 1 : ℚ)⟩,
   ⟨5, 0, 0, (8568 / 1 : ℚ)⟩,
   ⟨6, 0, 0, (27132 / 1 : ℚ)⟩,
   ⟨7, 0, 0, (77520 / 1 : ℚ)⟩,
   ⟨8, 0, 0, (203490 / 1 : ℚ)⟩,
   ⟨9, 0, 0, (497420 / 1 : ℚ)⟩,
   ⟨10, 0, 0, (1144066 / 1 : ℚ)⟩,
   ⟨11, 0, 0, (2496144 / 1 : ℚ)⟩,
   ⟨12, 0, 0, (5200300 / 1 : ℚ)⟩,
   ⟨13, 0, 0, (10400600 / 1 : ℚ)⟩,
   ⟨14, 0, 0, (20058300 / 1 : ℚ)⟩,
   ⟨15, 0, 0, (37442160 / 1 : ℚ)⟩,
   ⟨16, 0, 0, (67863915 / 1 : ℚ)⟩,
   ⟨17, 0, 0, (119759850 / 1 : ℚ)⟩,
   ⟨18, 0, 0, (206253075 / 1 : ℚ)⟩,
   ⟨19, 0, 0, (347373600 / 1 : ℚ)⟩,
   ⟨20, 0, 0, (573166440 / 1 : ℚ)⟩,
   ⟨21, 0, 0, (927983760 / 1 : ℚ)⟩,
   ⟨22, 0, 0, (1476337800 / 1 : ℚ)⟩,
   ⟨23, 0, 0, (2310789600 / 1 : ℚ)⟩]

theorem seed14_checked : equalityCheck (mulTrunc 24 seed13 seed1) seed14 = true := by
  decide +kernel

theorem seed14_approximates {k : ℂ} (hk : k ≠ 0) :
    Approximates 24 k (fun z => ((1-z.1)⁻¹)^14) seed14 := by
  convert ((seed13_approximates hk).mul hk (seed1_approximates hk)).replacePolynomial
    (equalityCheck_sound seed14_checked k) using 1
  funext z
  ring

def seed15 : List Term :=
  [⟨0, 0, 0, (1 / 1 : ℚ)⟩,
   ⟨1, 0, 0, (15 / 1 : ℚ)⟩,
   ⟨2, 0, 0, (120 / 1 : ℚ)⟩,
   ⟨3, 0, 0, (680 / 1 : ℚ)⟩,
   ⟨4, 0, 0, (3060 / 1 : ℚ)⟩,
   ⟨5, 0, 0, (11628 / 1 : ℚ)⟩,
   ⟨6, 0, 0, (38760 / 1 : ℚ)⟩,
   ⟨7, 0, 0, (116280 / 1 : ℚ)⟩,
   ⟨8, 0, 0, (319770 / 1 : ℚ)⟩,
   ⟨9, 0, 0, (817190 / 1 : ℚ)⟩,
   ⟨10, 0, 0, (1961256 / 1 : ℚ)⟩,
   ⟨11, 0, 0, (4457400 / 1 : ℚ)⟩,
   ⟨12, 0, 0, (9657700 / 1 : ℚ)⟩,
   ⟨13, 0, 0, (20058300 / 1 : ℚ)⟩,
   ⟨14, 0, 0, (40116600 / 1 : ℚ)⟩,
   ⟨15, 0, 0, (77558760 / 1 : ℚ)⟩,
   ⟨16, 0, 0, (145422675 / 1 : ℚ)⟩,
   ⟨17, 0, 0, (265182525 / 1 : ℚ)⟩,
   ⟨18, 0, 0, (471435600 / 1 : ℚ)⟩,
   ⟨19, 0, 0, (818809200 / 1 : ℚ)⟩,
   ⟨20, 0, 0, (1391975640 / 1 : ℚ)⟩,
   ⟨21, 0, 0, (2319959400 / 1 : ℚ)⟩,
   ⟨22, 0, 0, (3796297200 / 1 : ℚ)⟩,
   ⟨23, 0, 0, (6107086800 / 1 : ℚ)⟩]

theorem seed15_checked : equalityCheck (mulTrunc 24 seed14 seed1) seed15 = true := by
  decide +kernel

theorem seed15_approximates {k : ℂ} (hk : k ≠ 0) :
    Approximates 24 k (fun z => ((1-z.1)⁻¹)^15) seed15 := by
  convert ((seed14_approximates hk).mul hk (seed1_approximates hk)).replacePolynomial
    (equalityCheck_sound seed15_checked k) using 1
  funext z
  ring

def seed16 : List Term :=
  [⟨0, 0, 0, (1 / 1 : ℚ)⟩,
   ⟨1, 0, 0, (16 / 1 : ℚ)⟩,
   ⟨2, 0, 0, (136 / 1 : ℚ)⟩,
   ⟨3, 0, 0, (816 / 1 : ℚ)⟩,
   ⟨4, 0, 0, (3876 / 1 : ℚ)⟩,
   ⟨5, 0, 0, (15504 / 1 : ℚ)⟩,
   ⟨6, 0, 0, (54264 / 1 : ℚ)⟩,
   ⟨7, 0, 0, (170544 / 1 : ℚ)⟩,
   ⟨8, 0, 0, (490314 / 1 : ℚ)⟩,
   ⟨9, 0, 0, (1307504 / 1 : ℚ)⟩,
   ⟨10, 0, 0, (3268760 / 1 : ℚ)⟩,
   ⟨11, 0, 0, (7726160 / 1 : ℚ)⟩,
   ⟨12, 0, 0, (17383860 / 1 : ℚ)⟩,
   ⟨13, 0, 0, (37442160 / 1 : ℚ)⟩,
   ⟨14, 0, 0, (77558760 / 1 : ℚ)⟩,
   ⟨15, 0, 0, (155117520 / 1 : ℚ)⟩,
   ⟨16, 0, 0, (300540195 / 1 : ℚ)⟩,
   ⟨17, 0, 0, (565722720 / 1 : ℚ)⟩,
   ⟨18, 0, 0, (1037158320 / 1 : ℚ)⟩,
   ⟨19, 0, 0, (1855967520 / 1 : ℚ)⟩,
   ⟨20, 0, 0, (3247943160 / 1 : ℚ)⟩,
   ⟨21, 0, 0, (5567902560 / 1 : ℚ)⟩,
   ⟨22, 0, 0, (9364199760 / 1 : ℚ)⟩,
   ⟨23, 0, 0, (15471286560 / 1 : ℚ)⟩]

theorem seed16_checked : equalityCheck (mulTrunc 24 seed15 seed1) seed16 = true := by
  decide +kernel

theorem seed16_approximates {k : ℂ} (hk : k ≠ 0) :
    Approximates 24 k (fun z => ((1-z.1)⁻¹)^16) seed16 := by
  convert ((seed15_approximates hk).mul hk (seed1_approximates hk)).replacePolynomial
    (equalityCheck_sound seed16_checked k) using 1
  funext z
  ring

def seed17 : List Term :=
  [⟨0, 0, 0, (1 / 1 : ℚ)⟩,
   ⟨1, 0, 0, (17 / 1 : ℚ)⟩,
   ⟨2, 0, 0, (153 / 1 : ℚ)⟩,
   ⟨3, 0, 0, (969 / 1 : ℚ)⟩,
   ⟨4, 0, 0, (4845 / 1 : ℚ)⟩,
   ⟨5, 0, 0, (20349 / 1 : ℚ)⟩,
   ⟨6, 0, 0, (74613 / 1 : ℚ)⟩,
   ⟨7, 0, 0, (245157 / 1 : ℚ)⟩,
   ⟨8, 0, 0, (735471 / 1 : ℚ)⟩,
   ⟨9, 0, 0, (2042975 / 1 : ℚ)⟩,
   ⟨10, 0, 0, (5311735 / 1 : ℚ)⟩,
   ⟨11, 0, 0, (13037895 / 1 : ℚ)⟩,
   ⟨12, 0, 0, (30421755 / 1 : ℚ)⟩,
   ⟨13, 0, 0, (67863915 / 1 : ℚ)⟩,
   ⟨14, 0, 0, (145422675 / 1 : ℚ)⟩,
   ⟨15, 0, 0, (300540195 / 1 : ℚ)⟩,
   ⟨16, 0, 0, (601080390 / 1 : ℚ)⟩,
   ⟨17, 0, 0, (1166803110 / 1 : ℚ)⟩,
   ⟨18, 0, 0, (2203961430 / 1 : ℚ)⟩,
   ⟨19, 0, 0, (4059928950 / 1 : ℚ)⟩,
   ⟨20, 0, 0, (7307872110 / 1 : ℚ)⟩,
   ⟨21, 0, 0, (12875774670 / 1 : ℚ)⟩,
   ⟨22, 0, 0, (22239974430 / 1 : ℚ)⟩,
   ⟨23, 0, 0, (37711260990 / 1 : ℚ)⟩]

theorem seed17_checked : equalityCheck (mulTrunc 24 seed16 seed1) seed17 = true := by
  decide +kernel

theorem seed17_approximates {k : ℂ} (hk : k ≠ 0) :
    Approximates 24 k (fun z => ((1-z.1)⁻¹)^17) seed17 := by
  convert ((seed16_approximates hk).mul hk (seed1_approximates hk)).replacePolynomial
    (equalityCheck_sound seed17_checked k) using 1
  funext z
  ring

def seed18 : List Term :=
  [⟨0, 0, 0, (1 / 1 : ℚ)⟩,
   ⟨1, 0, 0, (18 / 1 : ℚ)⟩,
   ⟨2, 0, 0, (171 / 1 : ℚ)⟩,
   ⟨3, 0, 0, (1140 / 1 : ℚ)⟩,
   ⟨4, 0, 0, (5985 / 1 : ℚ)⟩,
   ⟨5, 0, 0, (26334 / 1 : ℚ)⟩,
   ⟨6, 0, 0, (100947 / 1 : ℚ)⟩,
   ⟨7, 0, 0, (346104 / 1 : ℚ)⟩,
   ⟨8, 0, 0, (1081575 / 1 : ℚ)⟩,
   ⟨9, 0, 0, (3124550 / 1 : ℚ)⟩,
   ⟨10, 0, 0, (8436285 / 1 : ℚ)⟩,
   ⟨11, 0, 0, (21474180 / 1 : ℚ)⟩,
   ⟨12, 0, 0, (51895935 / 1 : ℚ)⟩,
   ⟨13, 0, 0, (119759850 / 1 : ℚ)⟩,
   ⟨14, 0, 0, (265182525 / 1 : ℚ)⟩,
   ⟨15, 0, 0, (565722720 / 1 : ℚ)⟩,
   ⟨16, 0, 0, (1166803110 / 1 : ℚ)⟩,
   ⟨17, 0, 0, (2333606220 / 1 : ℚ)⟩,
   ⟨18, 0, 0, (4537567650 / 1 : ℚ)⟩,
   ⟨19, 0, 0, (8597496600 / 1 : ℚ)⟩,
   ⟨20, 0, 0, (15905368710 / 1 : ℚ)⟩,
   ⟨21, 0, 0, (28781143380 / 1 : ℚ)⟩,
   ⟨22, 0, 0, (51021117810 / 1 : ℚ)⟩,
   ⟨23, 0, 0, (88732378800 / 1 : ℚ)⟩]

theorem seed18_checked : equalityCheck (mulTrunc 24 seed17 seed1) seed18 = true := by
  decide +kernel

theorem seed18_approximates {k : ℂ} (hk : k ≠ 0) :
    Approximates 24 k (fun z => ((1-z.1)⁻¹)^18) seed18 := by
  convert ((seed17_approximates hk).mul hk (seed1_approximates hk)).replacePolynomial
    (equalityCheck_sound seed18_checked k) using 1
  funext z
  ring

def seed19 : List Term :=
  [⟨0, 0, 0, (1 / 1 : ℚ)⟩,
   ⟨1, 0, 0, (19 / 1 : ℚ)⟩,
   ⟨2, 0, 0, (190 / 1 : ℚ)⟩,
   ⟨3, 0, 0, (1330 / 1 : ℚ)⟩,
   ⟨4, 0, 0, (7315 / 1 : ℚ)⟩,
   ⟨5, 0, 0, (33649 / 1 : ℚ)⟩,
   ⟨6, 0, 0, (134596 / 1 : ℚ)⟩,
   ⟨7, 0, 0, (480700 / 1 : ℚ)⟩,
   ⟨8, 0, 0, (1562275 / 1 : ℚ)⟩,
   ⟨9, 0, 0, (4686825 / 1 : ℚ)⟩,
   ⟨10, 0, 0, (13123110 / 1 : ℚ)⟩,
   ⟨11, 0, 0, (34597290 / 1 : ℚ)⟩,
   ⟨12, 0, 0, (86493225 / 1 : ℚ)⟩,
   ⟨13, 0, 0, (206253075 / 1 : ℚ)⟩,
   ⟨14, 0, 0, (471435600 / 1 : ℚ)⟩,
   ⟨15, 0, 0, (1037158320 / 1 : ℚ)⟩,
   ⟨16, 0, 0, (2203961430 / 1 : ℚ)⟩,
   ⟨17, 0, 0, (4537567650 / 1 : ℚ)⟩,
   ⟨18, 0, 0, (9075135300 / 1 : ℚ)⟩,
   ⟨19, 0, 0, (17672631900 / 1 : ℚ)⟩,
   ⟨20, 0, 0, (33578000610 / 1 : ℚ)⟩,
   ⟨21, 0, 0, (62359143990 / 1 : ℚ)⟩,
   ⟨22, 0, 0, (113380261800 / 1 : ℚ)⟩,
   ⟨23, 0, 0, (202112640600 / 1 : ℚ)⟩]

theorem seed19_checked : equalityCheck (mulTrunc 24 seed18 seed1) seed19 = true := by
  decide +kernel

theorem seed19_approximates {k : ℂ} (hk : k ≠ 0) :
    Approximates 24 k (fun z => ((1-z.1)⁻¹)^19) seed19 := by
  convert ((seed18_approximates hk).mul hk (seed1_approximates hk)).replacePolynomial
    (equalityCheck_sound seed19_checked k) using 1
  funext z
  ring

def seed20 : List Term :=
  [⟨0, 0, 0, (1 / 1 : ℚ)⟩,
   ⟨1, 0, 0, (20 / 1 : ℚ)⟩,
   ⟨2, 0, 0, (210 / 1 : ℚ)⟩,
   ⟨3, 0, 0, (1540 / 1 : ℚ)⟩,
   ⟨4, 0, 0, (8855 / 1 : ℚ)⟩,
   ⟨5, 0, 0, (42504 / 1 : ℚ)⟩,
   ⟨6, 0, 0, (177100 / 1 : ℚ)⟩,
   ⟨7, 0, 0, (657800 / 1 : ℚ)⟩,
   ⟨8, 0, 0, (2220075 / 1 : ℚ)⟩,
   ⟨9, 0, 0, (6906900 / 1 : ℚ)⟩,
   ⟨10, 0, 0, (20030010 / 1 : ℚ)⟩,
   ⟨11, 0, 0, (54627300 / 1 : ℚ)⟩,
   ⟨12, 0, 0, (141120525 / 1 : ℚ)⟩,
   ⟨13, 0, 0, (347373600 / 1 : ℚ)⟩,
   ⟨14, 0, 0, (818809200 / 1 : ℚ)⟩,
   ⟨15, 0, 0, (1855967520 / 1 : ℚ)⟩,
   ⟨16, 0, 0, (4059928950 / 1 : ℚ)⟩,
   ⟨17, 0, 0, (8597496600 / 1 : ℚ)⟩,
   ⟨18, 0, 0, (17672631900 / 1 : ℚ)⟩,
   ⟨19, 0, 0, (35345263800 / 1 : ℚ)⟩,
   ⟨20, 0, 0, (68923264410 / 1 : ℚ)⟩,
   ⟨21, 0, 0, (131282408400 / 1 : ℚ)⟩,
   ⟨22, 0, 0, (244662670200 / 1 : ℚ)⟩,
   ⟨23, 0, 0, (446775310800 / 1 : ℚ)⟩]

theorem seed20_checked : equalityCheck (mulTrunc 24 seed19 seed1) seed20 = true := by
  decide +kernel

theorem seed20_approximates {k : ℂ} (hk : k ≠ 0) :
    Approximates 24 k (fun z => ((1-z.1)⁻¹)^20) seed20 := by
  convert ((seed19_approximates hk).mul hk (seed1_approximates hk)).replacePolynomial
    (equalityCheck_sound seed20_checked k) using 1
  funext z
  ring

def seed21 : List Term :=
  [⟨0, 0, 0, (1 / 1 : ℚ)⟩,
   ⟨1, 0, 0, (21 / 1 : ℚ)⟩,
   ⟨2, 0, 0, (231 / 1 : ℚ)⟩,
   ⟨3, 0, 0, (1771 / 1 : ℚ)⟩,
   ⟨4, 0, 0, (10626 / 1 : ℚ)⟩,
   ⟨5, 0, 0, (53130 / 1 : ℚ)⟩,
   ⟨6, 0, 0, (230230 / 1 : ℚ)⟩,
   ⟨7, 0, 0, (888030 / 1 : ℚ)⟩,
   ⟨8, 0, 0, (3108105 / 1 : ℚ)⟩,
   ⟨9, 0, 0, (10015005 / 1 : ℚ)⟩,
   ⟨10, 0, 0, (30045015 / 1 : ℚ)⟩,
   ⟨11, 0, 0, (84672315 / 1 : ℚ)⟩,
   ⟨12, 0, 0, (225792840 / 1 : ℚ)⟩,
   ⟨13, 0, 0, (573166440 / 1 : ℚ)⟩,
   ⟨14, 0, 0, (1391975640 / 1 : ℚ)⟩,
   ⟨15, 0, 0, (3247943160 / 1 : ℚ)⟩,
   ⟨16, 0, 0, (7307872110 / 1 : ℚ)⟩,
   ⟨17, 0, 0, (15905368710 / 1 : ℚ)⟩,
   ⟨18, 0, 0, (33578000610 / 1 : ℚ)⟩,
   ⟨19, 0, 0, (68923264410 / 1 : ℚ)⟩,
   ⟨20, 0, 0, (137846528820 / 1 : ℚ)⟩,
   ⟨21, 0, 0, (269128937220 / 1 : ℚ)⟩,
   ⟨22, 0, 0, (513791607420 / 1 : ℚ)⟩,
   ⟨23, 0, 0, (960566918220 / 1 : ℚ)⟩]

theorem seed21_checked : equalityCheck (mulTrunc 24 seed20 seed1) seed21 = true := by
  decide +kernel

theorem seed21_approximates {k : ℂ} (hk : k ≠ 0) :
    Approximates 24 k (fun z => ((1-z.1)⁻¹)^21) seed21 := by
  convert ((seed20_approximates hk).mul hk (seed1_approximates hk)).replacePolynomial
    (equalityCheck_sound seed21_checked k) using 1
  funext z
  ring

def seed22 : List Term :=
  [⟨0, 0, 0, (1 / 1 : ℚ)⟩,
   ⟨1, 0, 0, (22 / 1 : ℚ)⟩,
   ⟨2, 0, 0, (253 / 1 : ℚ)⟩,
   ⟨3, 0, 0, (2024 / 1 : ℚ)⟩,
   ⟨4, 0, 0, (12650 / 1 : ℚ)⟩,
   ⟨5, 0, 0, (65780 / 1 : ℚ)⟩,
   ⟨6, 0, 0, (296010 / 1 : ℚ)⟩,
   ⟨7, 0, 0, (1184040 / 1 : ℚ)⟩,
   ⟨8, 0, 0, (4292145 / 1 : ℚ)⟩,
   ⟨9, 0, 0, (14307150 / 1 : ℚ)⟩,
   ⟨10, 0, 0, (44352165 / 1 : ℚ)⟩,
   ⟨11, 0, 0, (129024480 / 1 : ℚ)⟩,
   ⟨12, 0, 0, (354817320 / 1 : ℚ)⟩,
   ⟨13, 0, 0, (927983760 / 1 : ℚ)⟩,
   ⟨14, 0, 0, (2319959400 / 1 : ℚ)⟩,
   ⟨15, 0, 0, (5567902560 / 1 : ℚ)⟩,
   ⟨16, 0, 0, (12875774670 / 1 : ℚ)⟩,
   ⟨17, 0, 0, (28781143380 / 1 : ℚ)⟩,
   ⟨18, 0, 0, (62359143990 / 1 : ℚ)⟩,
   ⟨19, 0, 0, (131282408400 / 1 : ℚ)⟩,
   ⟨20, 0, 0, (269128937220 / 1 : ℚ)⟩,
   ⟨21, 0, 0, (538257874440 / 1 : ℚ)⟩,
   ⟨22, 0, 0, (1052049481860 / 1 : ℚ)⟩,
   ⟨23, 0, 0, (2012616400080 / 1 : ℚ)⟩]

theorem seed22_checked : equalityCheck (mulTrunc 24 seed21 seed1) seed22 = true := by
  decide +kernel

theorem seed22_approximates {k : ℂ} (hk : k ≠ 0) :
    Approximates 24 k (fun z => ((1-z.1)⁻¹)^22) seed22 := by
  convert ((seed21_approximates hk).mul hk (seed1_approximates hk)).replacePolynomial
    (equalityCheck_sound seed22_checked k) using 1
  funext z
  ring

def seed23 : List Term :=
  [⟨0, 0, 0, (1 / 1 : ℚ)⟩,
   ⟨1, 0, 0, (23 / 1 : ℚ)⟩,
   ⟨2, 0, 0, (276 / 1 : ℚ)⟩,
   ⟨3, 0, 0, (2300 / 1 : ℚ)⟩,
   ⟨4, 0, 0, (14950 / 1 : ℚ)⟩,
   ⟨5, 0, 0, (80730 / 1 : ℚ)⟩,
   ⟨6, 0, 0, (376740 / 1 : ℚ)⟩,
   ⟨7, 0, 0, (1560780 / 1 : ℚ)⟩,
   ⟨8, 0, 0, (5852925 / 1 : ℚ)⟩,
   ⟨9, 0, 0, (20160075 / 1 : ℚ)⟩,
   ⟨10, 0, 0, (64512240 / 1 : ℚ)⟩,
   ⟨11, 0, 0, (193536720 / 1 : ℚ)⟩,
   ⟨12, 0, 0, (548354040 / 1 : ℚ)⟩,
   ⟨13, 0, 0, (1476337800 / 1 : ℚ)⟩,
   ⟨14, 0, 0, (3796297200 / 1 : ℚ)⟩,
   ⟨15, 0, 0, (9364199760 / 1 : ℚ)⟩,
   ⟨16, 0, 0, (22239974430 / 1 : ℚ)⟩,
   ⟨17, 0, 0, (51021117810 / 1 : ℚ)⟩,
   ⟨18, 0, 0, (113380261800 / 1 : ℚ)⟩,
   ⟨19, 0, 0, (244662670200 / 1 : ℚ)⟩,
   ⟨20, 0, 0, (513791607420 / 1 : ℚ)⟩,
   ⟨21, 0, 0, (1052049481860 / 1 : ℚ)⟩,
   ⟨22, 0, 0, (2104098963720 / 1 : ℚ)⟩,
   ⟨23, 0, 0, (4116715363800 / 1 : ℚ)⟩]

theorem seed23_checked : equalityCheck (mulTrunc 24 seed22 seed1) seed23 = true := by
  decide +kernel

theorem seed23_approximates {k : ℂ} (hk : k ≠ 0) :
    Approximates 24 k (fun z => ((1-z.1)⁻¹)^23) seed23 := by
  convert ((seed22_approximates hk).mul hk (seed1_approximates hk)).replacePolynomial
    (equalityCheck_sound seed23_checked k) using 1
  funext z
  ring

end GeneralCK.Reflection.SmallBiasInversePowerSeeds

end


