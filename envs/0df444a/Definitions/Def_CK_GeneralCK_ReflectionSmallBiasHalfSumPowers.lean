-- Prove2me | Definitions.Def_CK_GeneralCK_ReflectionSmallBiasHalfSumPowers
-- name    : CK_GeneralCK_ReflectionSmallBiasHalfSumPowers
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T16:21:44.504881+00:00
-- url     : https://prove2.me/theorems/2c2d70c2-e8fc-4d4c-aab3-733963bb8f94
-- title:
--   Courtade–Kumar proof module `GeneralCK.ReflectionSmallBiasHalfSumPowers` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.ReflectionSmallBiasHalfSumPowers` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.ReflectionSmallBiasHalfSumPowers` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.ReflectionSmallBiasHalfSumPowers (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/ReflectionSmallBiasHalfSumPowers.lean)

import Definitions.Def_CK_GeneralCK_ReflectionSmallBiasJetRawSum

-- ===== source module GeneralCK.ReflectionSmallBiasHalfSumPowers =====
section

namespace GeneralCK.Reflection.SmallBiasHalfSumPowers

open SmallBiasPolynomial SmallBiasJet

set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def halfSum (z : ℂ × ℂ) : ℂ := (z.1+z.2)/2

def halfPower1 : List Term :=
  [⟨0, 1, 0, (1 / 2 : ℚ)⟩,
   ⟨1, 0, 0, (1 / 2 : ℚ)⟩]

theorem halfPower1_checked : equalityCheck (scale (1/2) (add coordinateA coordinateB)) halfPower1 = true := by
  decide +kernel

theorem halfPower1_approximates {k : ℂ} (hk : k ≠ 0) :
    Approximates 24 k (fun z => halfSum z^1) halfPower1 := by
  convert (((Approximates.coordinateA 24 k).add (Approximates.coordinateB 24 k)).scale (1/2)).replacePolynomial
    (equalityCheck_sound halfPower1_checked k) using 1
  funext z
  norm_num [halfSum]
  <;> ring

def halfPower2 : List Term :=
  [⟨0, 2, 0, (1 / 4 : ℚ)⟩,
   ⟨1, 1, 0, (1 / 2 : ℚ)⟩,
   ⟨2, 0, 0, (1 / 4 : ℚ)⟩]

theorem halfPower2_checked : equalityCheck (mulTrunc 24 halfPower1 halfPower1) halfPower2 = true := by
  decide +kernel

theorem halfPower2_approximates {k : ℂ} (hk : k ≠ 0) :
    Approximates 24 k (fun z => halfSum z^2) halfPower2 := by
  convert ((halfPower1_approximates hk).mul hk (halfPower1_approximates hk)).replacePolynomial
    (equalityCheck_sound halfPower2_checked k) using 1
  funext z
  ring

def halfPower3 : List Term :=
  [⟨0, 3, 0, (1 / 8 : ℚ)⟩,
   ⟨1, 2, 0, (3 / 8 : ℚ)⟩,
   ⟨2, 1, 0, (3 / 8 : ℚ)⟩,
   ⟨3, 0, 0, (1 / 8 : ℚ)⟩]

theorem halfPower3_checked : equalityCheck (mulTrunc 24 halfPower1 halfPower2) halfPower3 = true := by
  decide +kernel

theorem halfPower3_approximates {k : ℂ} (hk : k ≠ 0) :
    Approximates 24 k (fun z => halfSum z^3) halfPower3 := by
  convert ((halfPower1_approximates hk).mul hk (halfPower2_approximates hk)).replacePolynomial
    (equalityCheck_sound halfPower3_checked k) using 1
  funext z
  ring

def halfPower4 : List Term :=
  [⟨0, 4, 0, (1 / 16 : ℚ)⟩,
   ⟨1, 3, 0, (1 / 4 : ℚ)⟩,
   ⟨2, 2, 0, (3 / 8 : ℚ)⟩,
   ⟨3, 1, 0, (1 / 4 : ℚ)⟩,
   ⟨4, 0, 0, (1 / 16 : ℚ)⟩]

theorem halfPower4_checked : equalityCheck (mulTrunc 24 halfPower1 halfPower3) halfPower4 = true := by
  decide +kernel

theorem halfPower4_approximates {k : ℂ} (hk : k ≠ 0) :
    Approximates 24 k (fun z => halfSum z^4) halfPower4 := by
  convert ((halfPower1_approximates hk).mul hk (halfPower3_approximates hk)).replacePolynomial
    (equalityCheck_sound halfPower4_checked k) using 1
  funext z
  ring

def halfPower5 : List Term :=
  [⟨0, 5, 0, (1 / 32 : ℚ)⟩,
   ⟨1, 4, 0, (5 / 32 : ℚ)⟩,
   ⟨2, 3, 0, (5 / 16 : ℚ)⟩,
   ⟨3, 2, 0, (5 / 16 : ℚ)⟩,
   ⟨4, 1, 0, (5 / 32 : ℚ)⟩,
   ⟨5, 0, 0, (1 / 32 : ℚ)⟩]

theorem halfPower5_checked : equalityCheck (mulTrunc 24 halfPower1 halfPower4) halfPower5 = true := by
  decide +kernel

theorem halfPower5_approximates {k : ℂ} (hk : k ≠ 0) :
    Approximates 24 k (fun z => halfSum z^5) halfPower5 := by
  convert ((halfPower1_approximates hk).mul hk (halfPower4_approximates hk)).replacePolynomial
    (equalityCheck_sound halfPower5_checked k) using 1
  funext z
  ring

def halfPower6 : List Term :=
  [⟨0, 6, 0, (1 / 64 : ℚ)⟩,
   ⟨1, 5, 0, (3 / 32 : ℚ)⟩,
   ⟨2, 4, 0, (15 / 64 : ℚ)⟩,
   ⟨3, 3, 0, (5 / 16 : ℚ)⟩,
   ⟨4, 2, 0, (15 / 64 : ℚ)⟩,
   ⟨5, 1, 0, (3 / 32 : ℚ)⟩,
   ⟨6, 0, 0, (1 / 64 : ℚ)⟩]

theorem halfPower6_checked : equalityCheck (mulTrunc 24 halfPower1 halfPower5) halfPower6 = true := by
  decide +kernel

theorem halfPower6_approximates {k : ℂ} (hk : k ≠ 0) :
    Approximates 24 k (fun z => halfSum z^6) halfPower6 := by
  convert ((halfPower1_approximates hk).mul hk (halfPower5_approximates hk)).replacePolynomial
    (equalityCheck_sound halfPower6_checked k) using 1
  funext z
  ring

def halfPower7 : List Term :=
  [⟨0, 7, 0, (1 / 128 : ℚ)⟩,
   ⟨1, 6, 0, (7 / 128 : ℚ)⟩,
   ⟨2, 5, 0, (21 / 128 : ℚ)⟩,
   ⟨3, 4, 0, (35 / 128 : ℚ)⟩,
   ⟨4, 3, 0, (35 / 128 : ℚ)⟩,
   ⟨5, 2, 0, (21 / 128 : ℚ)⟩,
   ⟨6, 1, 0, (7 / 128 : ℚ)⟩,
   ⟨7, 0, 0, (1 / 128 : ℚ)⟩]

theorem halfPower7_checked : equalityCheck (mulTrunc 24 halfPower1 halfPower6) halfPower7 = true := by
  decide +kernel

theorem halfPower7_approximates {k : ℂ} (hk : k ≠ 0) :
    Approximates 24 k (fun z => halfSum z^7) halfPower7 := by
  convert ((halfPower1_approximates hk).mul hk (halfPower6_approximates hk)).replacePolynomial
    (equalityCheck_sound halfPower7_checked k) using 1
  funext z
  ring

def halfPower8 : List Term :=
  [⟨0, 8, 0, (1 / 256 : ℚ)⟩,
   ⟨1, 7, 0, (1 / 32 : ℚ)⟩,
   ⟨2, 6, 0, (7 / 64 : ℚ)⟩,
   ⟨3, 5, 0, (7 / 32 : ℚ)⟩,
   ⟨4, 4, 0, (35 / 128 : ℚ)⟩,
   ⟨5, 3, 0, (7 / 32 : ℚ)⟩,
   ⟨6, 2, 0, (7 / 64 : ℚ)⟩,
   ⟨7, 1, 0, (1 / 32 : ℚ)⟩,
   ⟨8, 0, 0, (1 / 256 : ℚ)⟩]

theorem halfPower8_checked : equalityCheck (mulTrunc 24 halfPower1 halfPower7) halfPower8 = true := by
  decide +kernel

theorem halfPower8_approximates {k : ℂ} (hk : k ≠ 0) :
    Approximates 24 k (fun z => halfSum z^8) halfPower8 := by
  convert ((halfPower1_approximates hk).mul hk (halfPower7_approximates hk)).replacePolynomial
    (equalityCheck_sound halfPower8_checked k) using 1
  funext z
  ring

def halfPower9 : List Term :=
  [⟨0, 9, 0, (1 / 512 : ℚ)⟩,
   ⟨1, 8, 0, (9 / 512 : ℚ)⟩,
   ⟨2, 7, 0, (9 / 128 : ℚ)⟩,
   ⟨3, 6, 0, (21 / 128 : ℚ)⟩,
   ⟨4, 5, 0, (63 / 256 : ℚ)⟩,
   ⟨5, 4, 0, (63 / 256 : ℚ)⟩,
   ⟨6, 3, 0, (21 / 128 : ℚ)⟩,
   ⟨7, 2, 0, (9 / 128 : ℚ)⟩,
   ⟨8, 1, 0, (9 / 512 : ℚ)⟩,
   ⟨9, 0, 0, (1 / 512 : ℚ)⟩]

theorem halfPower9_checked : equalityCheck (mulTrunc 24 halfPower1 halfPower8) halfPower9 = true := by
  decide +kernel

theorem halfPower9_approximates {k : ℂ} (hk : k ≠ 0) :
    Approximates 24 k (fun z => halfSum z^9) halfPower9 := by
  convert ((halfPower1_approximates hk).mul hk (halfPower8_approximates hk)).replacePolynomial
    (equalityCheck_sound halfPower9_checked k) using 1
  funext z
  ring

def halfPower10 : List Term :=
  [⟨0, 10, 0, (1 / 1024 : ℚ)⟩,
   ⟨1, 9, 0, (5 / 512 : ℚ)⟩,
   ⟨2, 8, 0, (45 / 1024 : ℚ)⟩,
   ⟨3, 7, 0, (15 / 128 : ℚ)⟩,
   ⟨4, 6, 0, (105 / 512 : ℚ)⟩,
   ⟨5, 5, 0, (63 / 256 : ℚ)⟩,
   ⟨6, 4, 0, (105 / 512 : ℚ)⟩,
   ⟨7, 3, 0, (15 / 128 : ℚ)⟩,
   ⟨8, 2, 0, (45 / 1024 : ℚ)⟩,
   ⟨9, 1, 0, (5 / 512 : ℚ)⟩,
   ⟨10, 0, 0, (1 / 1024 : ℚ)⟩]

theorem halfPower10_checked : equalityCheck (mulTrunc 24 halfPower1 halfPower9) halfPower10 = true := by
  decide +kernel

theorem halfPower10_approximates {k : ℂ} (hk : k ≠ 0) :
    Approximates 24 k (fun z => halfSum z^10) halfPower10 := by
  convert ((halfPower1_approximates hk).mul hk (halfPower9_approximates hk)).replacePolynomial
    (equalityCheck_sound halfPower10_checked k) using 1
  funext z
  ring

def halfPower11 : List Term :=
  [⟨0, 11, 0, (1 / 2048 : ℚ)⟩,
   ⟨1, 10, 0, (11 / 2048 : ℚ)⟩,
   ⟨2, 9, 0, (55 / 2048 : ℚ)⟩,
   ⟨3, 8, 0, (165 / 2048 : ℚ)⟩,
   ⟨4, 7, 0, (165 / 1024 : ℚ)⟩,
   ⟨5, 6, 0, (231 / 1024 : ℚ)⟩,
   ⟨6, 5, 0, (231 / 1024 : ℚ)⟩,
   ⟨7, 4, 0, (165 / 1024 : ℚ)⟩,
   ⟨8, 3, 0, (165 / 2048 : ℚ)⟩,
   ⟨9, 2, 0, (55 / 2048 : ℚ)⟩,
   ⟨10, 1, 0, (11 / 2048 : ℚ)⟩,
   ⟨11, 0, 0, (1 / 2048 : ℚ)⟩]

theorem halfPower11_checked : equalityCheck (mulTrunc 24 halfPower1 halfPower10) halfPower11 = true := by
  decide +kernel

theorem halfPower11_approximates {k : ℂ} (hk : k ≠ 0) :
    Approximates 24 k (fun z => halfSum z^11) halfPower11 := by
  convert ((halfPower1_approximates hk).mul hk (halfPower10_approximates hk)).replacePolynomial
    (equalityCheck_sound halfPower11_checked k) using 1
  funext z
  ring

def halfPower12 : List Term :=
  [⟨0, 12, 0, (1 / 4096 : ℚ)⟩,
   ⟨1, 11, 0, (3 / 1024 : ℚ)⟩,
   ⟨2, 10, 0, (33 / 2048 : ℚ)⟩,
   ⟨3, 9, 0, (55 / 1024 : ℚ)⟩,
   ⟨4, 8, 0, (495 / 4096 : ℚ)⟩,
   ⟨5, 7, 0, (99 / 512 : ℚ)⟩,
   ⟨6, 6, 0, (231 / 1024 : ℚ)⟩,
   ⟨7, 5, 0, (99 / 512 : ℚ)⟩,
   ⟨8, 4, 0, (495 / 4096 : ℚ)⟩,
   ⟨9, 3, 0, (55 / 1024 : ℚ)⟩,
   ⟨10, 2, 0, (33 / 2048 : ℚ)⟩,
   ⟨11, 1, 0, (3 / 1024 : ℚ)⟩,
   ⟨12, 0, 0, (1 / 4096 : ℚ)⟩]

theorem halfPower12_checked : equalityCheck (mulTrunc 24 halfPower1 halfPower11) halfPower12 = true := by
  decide +kernel

theorem halfPower12_approximates {k : ℂ} (hk : k ≠ 0) :
    Approximates 24 k (fun z => halfSum z^12) halfPower12 := by
  convert ((halfPower1_approximates hk).mul hk (halfPower11_approximates hk)).replacePolynomial
    (equalityCheck_sound halfPower12_checked k) using 1
  funext z
  ring

def halfPower13 : List Term :=
  [⟨0, 13, 0, (1 / 8192 : ℚ)⟩,
   ⟨1, 12, 0, (13 / 8192 : ℚ)⟩,
   ⟨2, 11, 0, (39 / 4096 : ℚ)⟩,
   ⟨3, 10, 0, (143 / 4096 : ℚ)⟩,
   ⟨4, 9, 0, (715 / 8192 : ℚ)⟩,
   ⟨5, 8, 0, (1287 / 8192 : ℚ)⟩,
   ⟨6, 7, 0, (429 / 2048 : ℚ)⟩,
   ⟨7, 6, 0, (429 / 2048 : ℚ)⟩,
   ⟨8, 5, 0, (1287 / 8192 : ℚ)⟩,
   ⟨9, 4, 0, (715 / 8192 : ℚ)⟩,
   ⟨10, 3, 0, (143 / 4096 : ℚ)⟩,
   ⟨11, 2, 0, (39 / 4096 : ℚ)⟩,
   ⟨12, 1, 0, (13 / 8192 : ℚ)⟩,
   ⟨13, 0, 0, (1 / 8192 : ℚ)⟩]

theorem halfPower13_checked : equalityCheck (mulTrunc 24 halfPower1 halfPower12) halfPower13 = true := by
  decide +kernel

theorem halfPower13_approximates {k : ℂ} (hk : k ≠ 0) :
    Approximates 24 k (fun z => halfSum z^13) halfPower13 := by
  convert ((halfPower1_approximates hk).mul hk (halfPower12_approximates hk)).replacePolynomial
    (equalityCheck_sound halfPower13_checked k) using 1
  funext z
  ring

def halfPower14 : List Term :=
  [⟨0, 14, 0, (1 / 16384 : ℚ)⟩,
   ⟨1, 13, 0, (7 / 8192 : ℚ)⟩,
   ⟨2, 12, 0, (91 / 16384 : ℚ)⟩,
   ⟨3, 11, 0, (91 / 4096 : ℚ)⟩,
   ⟨4, 10, 0, (1001 / 16384 : ℚ)⟩,
   ⟨5, 9, 0, (1001 / 8192 : ℚ)⟩,
   ⟨6, 8, 0, (3003 / 16384 : ℚ)⟩,
   ⟨7, 7, 0, (429 / 2048 : ℚ)⟩,
   ⟨8, 6, 0, (3003 / 16384 : ℚ)⟩,
   ⟨9, 5, 0, (1001 / 8192 : ℚ)⟩,
   ⟨10, 4, 0, (1001 / 16384 : ℚ)⟩,
   ⟨11, 3, 0, (91 / 4096 : ℚ)⟩,
   ⟨12, 2, 0, (91 / 16384 : ℚ)⟩,
   ⟨13, 1, 0, (7 / 8192 : ℚ)⟩,
   ⟨14, 0, 0, (1 / 16384 : ℚ)⟩]

theorem halfPower14_checked : equalityCheck (mulTrunc 24 halfPower1 halfPower13) halfPower14 = true := by
  decide +kernel

theorem halfPower14_approximates {k : ℂ} (hk : k ≠ 0) :
    Approximates 24 k (fun z => halfSum z^14) halfPower14 := by
  convert ((halfPower1_approximates hk).mul hk (halfPower13_approximates hk)).replacePolynomial
    (equalityCheck_sound halfPower14_checked k) using 1
  funext z
  ring

def halfPower15 : List Term :=
  [⟨0, 15, 0, (1 / 32768 : ℚ)⟩,
   ⟨1, 14, 0, (15 / 32768 : ℚ)⟩,
   ⟨2, 13, 0, (105 / 32768 : ℚ)⟩,
   ⟨3, 12, 0, (455 / 32768 : ℚ)⟩,
   ⟨4, 11, 0, (1365 / 32768 : ℚ)⟩,
   ⟨5, 10, 0, (3003 / 32768 : ℚ)⟩,
   ⟨6, 9, 0, (5005 / 32768 : ℚ)⟩,
   ⟨7, 8, 0, (6435 / 32768 : ℚ)⟩,
   ⟨8, 7, 0, (6435 / 32768 : ℚ)⟩,
   ⟨9, 6, 0, (5005 / 32768 : ℚ)⟩,
   ⟨10, 5, 0, (3003 / 32768 : ℚ)⟩,
   ⟨11, 4, 0, (1365 / 32768 : ℚ)⟩,
   ⟨12, 3, 0, (455 / 32768 : ℚ)⟩,
   ⟨13, 2, 0, (105 / 32768 : ℚ)⟩,
   ⟨14, 1, 0, (15 / 32768 : ℚ)⟩,
   ⟨15, 0, 0, (1 / 32768 : ℚ)⟩]

theorem halfPower15_checked : equalityCheck (mulTrunc 24 halfPower1 halfPower14) halfPower15 = true := by
  decide +kernel

theorem halfPower15_approximates {k : ℂ} (hk : k ≠ 0) :
    Approximates 24 k (fun z => halfSum z^15) halfPower15 := by
  convert ((halfPower1_approximates hk).mul hk (halfPower14_approximates hk)).replacePolynomial
    (equalityCheck_sound halfPower15_checked k) using 1
  funext z
  ring

def halfPower16 : List Term :=
  [⟨0, 16, 0, (1 / 65536 : ℚ)⟩,
   ⟨1, 15, 0, (1 / 4096 : ℚ)⟩,
   ⟨2, 14, 0, (15 / 8192 : ℚ)⟩,
   ⟨3, 13, 0, (35 / 4096 : ℚ)⟩,
   ⟨4, 12, 0, (455 / 16384 : ℚ)⟩,
   ⟨5, 11, 0, (273 / 4096 : ℚ)⟩,
   ⟨6, 10, 0, (1001 / 8192 : ℚ)⟩,
   ⟨7, 9, 0, (715 / 4096 : ℚ)⟩,
   ⟨8, 8, 0, (6435 / 32768 : ℚ)⟩,
   ⟨9, 7, 0, (715 / 4096 : ℚ)⟩,
   ⟨10, 6, 0, (1001 / 8192 : ℚ)⟩,
   ⟨11, 5, 0, (273 / 4096 : ℚ)⟩,
   ⟨12, 4, 0, (455 / 16384 : ℚ)⟩,
   ⟨13, 3, 0, (35 / 4096 : ℚ)⟩,
   ⟨14, 2, 0, (15 / 8192 : ℚ)⟩,
   ⟨15, 1, 0, (1 / 4096 : ℚ)⟩,
   ⟨16, 0, 0, (1 / 65536 : ℚ)⟩]

theorem halfPower16_checked : equalityCheck (mulTrunc 24 halfPower1 halfPower15) halfPower16 = true := by
  decide +kernel

theorem halfPower16_approximates {k : ℂ} (hk : k ≠ 0) :
    Approximates 24 k (fun z => halfSum z^16) halfPower16 := by
  convert ((halfPower1_approximates hk).mul hk (halfPower15_approximates hk)).replacePolynomial
    (equalityCheck_sound halfPower16_checked k) using 1
  funext z
  ring

def halfPower17 : List Term :=
  [⟨0, 17, 0, (1 / 131072 : ℚ)⟩,
   ⟨1, 16, 0, (17 / 131072 : ℚ)⟩,
   ⟨2, 15, 0, (17 / 16384 : ℚ)⟩,
   ⟨3, 14, 0, (85 / 16384 : ℚ)⟩,
   ⟨4, 13, 0, (595 / 32768 : ℚ)⟩,
   ⟨5, 12, 0, (1547 / 32768 : ℚ)⟩,
   ⟨6, 11, 0, (1547 / 16384 : ℚ)⟩,
   ⟨7, 10, 0, (2431 / 16384 : ℚ)⟩,
   ⟨8, 9, 0, (12155 / 65536 : ℚ)⟩,
   ⟨9, 8, 0, (12155 / 65536 : ℚ)⟩,
   ⟨10, 7, 0, (2431 / 16384 : ℚ)⟩,
   ⟨11, 6, 0, (1547 / 16384 : ℚ)⟩,
   ⟨12, 5, 0, (1547 / 32768 : ℚ)⟩,
   ⟨13, 4, 0, (595 / 32768 : ℚ)⟩,
   ⟨14, 3, 0, (85 / 16384 : ℚ)⟩,
   ⟨15, 2, 0, (17 / 16384 : ℚ)⟩,
   ⟨16, 1, 0, (17 / 131072 : ℚ)⟩,
   ⟨17, 0, 0, (1 / 131072 : ℚ)⟩]

theorem halfPower17_checked : equalityCheck (mulTrunc 24 halfPower1 halfPower16) halfPower17 = true := by
  decide +kernel

theorem halfPower17_approximates {k : ℂ} (hk : k ≠ 0) :
    Approximates 24 k (fun z => halfSum z^17) halfPower17 := by
  convert ((halfPower1_approximates hk).mul hk (halfPower16_approximates hk)).replacePolynomial
    (equalityCheck_sound halfPower17_checked k) using 1
  funext z
  ring

def halfPower18 : List Term :=
  [⟨0, 18, 0, (1 / 262144 : ℚ)⟩,
   ⟨1, 17, 0, (9 / 131072 : ℚ)⟩,
   ⟨2, 16, 0, (153 / 262144 : ℚ)⟩,
   ⟨3, 15, 0, (51 / 16384 : ℚ)⟩,
   ⟨4, 14, 0, (765 / 65536 : ℚ)⟩,
   ⟨5, 13, 0, (1071 / 32768 : ℚ)⟩,
   ⟨6, 12, 0, (4641 / 65536 : ℚ)⟩,
   ⟨7, 11, 0, (1989 / 16384 : ℚ)⟩,
   ⟨8, 10, 0, (21879 / 131072 : ℚ)⟩,
   ⟨9, 9, 0, (12155 / 65536 : ℚ)⟩,
   ⟨10, 8, 0, (21879 / 131072 : ℚ)⟩,
   ⟨11, 7, 0, (1989 / 16384 : ℚ)⟩,
   ⟨12, 6, 0, (4641 / 65536 : ℚ)⟩,
   ⟨13, 5, 0, (1071 / 32768 : ℚ)⟩,
   ⟨14, 4, 0, (765 / 65536 : ℚ)⟩,
   ⟨15, 3, 0, (51 / 16384 : ℚ)⟩,
   ⟨16, 2, 0, (153 / 262144 : ℚ)⟩,
   ⟨17, 1, 0, (9 / 131072 : ℚ)⟩,
   ⟨18, 0, 0, (1 / 262144 : ℚ)⟩]

theorem halfPower18_checked : equalityCheck (mulTrunc 24 halfPower1 halfPower17) halfPower18 = true := by
  decide +kernel

theorem halfPower18_approximates {k : ℂ} (hk : k ≠ 0) :
    Approximates 24 k (fun z => halfSum z^18) halfPower18 := by
  convert ((halfPower1_approximates hk).mul hk (halfPower17_approximates hk)).replacePolynomial
    (equalityCheck_sound halfPower18_checked k) using 1
  funext z
  ring

def halfPower19 : List Term :=
  [⟨0, 19, 0, (1 / 524288 : ℚ)⟩,
   ⟨1, 18, 0, (19 / 524288 : ℚ)⟩,
   ⟨2, 17, 0, (171 / 524288 : ℚ)⟩,
   ⟨3, 16, 0, (969 / 524288 : ℚ)⟩,
   ⟨4, 15, 0, (969 / 131072 : ℚ)⟩,
   ⟨5, 14, 0, (2907 / 131072 : ℚ)⟩,
   ⟨6, 13, 0, (6783 / 131072 : ℚ)⟩,
   ⟨7, 12, 0, (12597 / 131072 : ℚ)⟩,
   ⟨8, 11, 0, (37791 / 262144 : ℚ)⟩,
   ⟨9, 10, 0, (46189 / 262144 : ℚ)⟩,
   ⟨10, 9, 0, (46189 / 262144 : ℚ)⟩,
   ⟨11, 8, 0, (37791 / 262144 : ℚ)⟩,
   ⟨12, 7, 0, (12597 / 131072 : ℚ)⟩,
   ⟨13, 6, 0, (6783 / 131072 : ℚ)⟩,
   ⟨14, 5, 0, (2907 / 131072 : ℚ)⟩,
   ⟨15, 4, 0, (969 / 131072 : ℚ)⟩,
   ⟨16, 3, 0, (969 / 524288 : ℚ)⟩,
   ⟨17, 2, 0, (171 / 524288 : ℚ)⟩,
   ⟨18, 1, 0, (19 / 524288 : ℚ)⟩,
   ⟨19, 0, 0, (1 / 524288 : ℚ)⟩]

theorem halfPower19_checked : equalityCheck (mulTrunc 24 halfPower1 halfPower18) halfPower19 = true := by
  decide +kernel

theorem halfPower19_approximates {k : ℂ} (hk : k ≠ 0) :
    Approximates 24 k (fun z => halfSum z^19) halfPower19 := by
  convert ((halfPower1_approximates hk).mul hk (halfPower18_approximates hk)).replacePolynomial
    (equalityCheck_sound halfPower19_checked k) using 1
  funext z
  ring

def halfPower20 : List Term :=
  [⟨0, 20, 0, (1 / 1048576 : ℚ)⟩,
   ⟨1, 19, 0, (5 / 262144 : ℚ)⟩,
   ⟨2, 18, 0, (95 / 524288 : ℚ)⟩,
   ⟨3, 17, 0, (285 / 262144 : ℚ)⟩,
   ⟨4, 16, 0, (4845 / 1048576 : ℚ)⟩,
   ⟨5, 15, 0, (969 / 65536 : ℚ)⟩,
   ⟨6, 14, 0, (4845 / 131072 : ℚ)⟩,
   ⟨7, 13, 0, (4845 / 65536 : ℚ)⟩,
   ⟨8, 12, 0, (62985 / 524288 : ℚ)⟩,
   ⟨9, 11, 0, (20995 / 131072 : ℚ)⟩,
   ⟨10, 10, 0, (46189 / 262144 : ℚ)⟩,
   ⟨11, 9, 0, (20995 / 131072 : ℚ)⟩,
   ⟨12, 8, 0, (62985 / 524288 : ℚ)⟩,
   ⟨13, 7, 0, (4845 / 65536 : ℚ)⟩,
   ⟨14, 6, 0, (4845 / 131072 : ℚ)⟩,
   ⟨15, 5, 0, (969 / 65536 : ℚ)⟩,
   ⟨16, 4, 0, (4845 / 1048576 : ℚ)⟩,
   ⟨17, 3, 0, (285 / 262144 : ℚ)⟩,
   ⟨18, 2, 0, (95 / 524288 : ℚ)⟩,
   ⟨19, 1, 0, (5 / 262144 : ℚ)⟩,
   ⟨20, 0, 0, (1 / 1048576 : ℚ)⟩]

theorem halfPower20_checked : equalityCheck (mulTrunc 24 halfPower1 halfPower19) halfPower20 = true := by
  decide +kernel

theorem halfPower20_approximates {k : ℂ} (hk : k ≠ 0) :
    Approximates 24 k (fun z => halfSum z^20) halfPower20 := by
  convert ((halfPower1_approximates hk).mul hk (halfPower19_approximates hk)).replacePolynomial
    (equalityCheck_sound halfPower20_checked k) using 1
  funext z
  ring

def halfPower21 : List Term :=
  [⟨0, 21, 0, (1 / 2097152 : ℚ)⟩,
   ⟨1, 20, 0, (21 / 2097152 : ℚ)⟩,
   ⟨2, 19, 0, (105 / 1048576 : ℚ)⟩,
   ⟨3, 18, 0, (665 / 1048576 : ℚ)⟩,
   ⟨4, 17, 0, (5985 / 2097152 : ℚ)⟩,
   ⟨5, 16, 0, (20349 / 2097152 : ℚ)⟩,
   ⟨6, 15, 0, (6783 / 262144 : ℚ)⟩,
   ⟨7, 14, 0, (14535 / 262144 : ℚ)⟩,
   ⟨8, 13, 0, (101745 / 1048576 : ℚ)⟩,
   ⟨9, 12, 0, (146965 / 1048576 : ℚ)⟩,
   ⟨10, 11, 0, (88179 / 524288 : ℚ)⟩,
   ⟨11, 10, 0, (88179 / 524288 : ℚ)⟩,
   ⟨12, 9, 0, (146965 / 1048576 : ℚ)⟩,
   ⟨13, 8, 0, (101745 / 1048576 : ℚ)⟩,
   ⟨14, 7, 0, (14535 / 262144 : ℚ)⟩,
   ⟨15, 6, 0, (6783 / 262144 : ℚ)⟩,
   ⟨16, 5, 0, (20349 / 2097152 : ℚ)⟩,
   ⟨17, 4, 0, (5985 / 2097152 : ℚ)⟩,
   ⟨18, 3, 0, (665 / 1048576 : ℚ)⟩,
   ⟨19, 2, 0, (105 / 1048576 : ℚ)⟩,
   ⟨20, 1, 0, (21 / 2097152 : ℚ)⟩,
   ⟨21, 0, 0, (1 / 2097152 : ℚ)⟩]

theorem halfPower21_checked : equalityCheck (mulTrunc 24 halfPower1 halfPower20) halfPower21 = true := by
  decide +kernel

theorem halfPower21_approximates {k : ℂ} (hk : k ≠ 0) :
    Approximates 24 k (fun z => halfSum z^21) halfPower21 := by
  convert ((halfPower1_approximates hk).mul hk (halfPower20_approximates hk)).replacePolynomial
    (equalityCheck_sound halfPower21_checked k) using 1
  funext z
  ring

def halfPower22 : List Term :=
  [⟨0, 22, 0, (1 / 4194304 : ℚ)⟩,
   ⟨1, 21, 0, (11 / 2097152 : ℚ)⟩,
   ⟨2, 20, 0, (231 / 4194304 : ℚ)⟩,
   ⟨3, 19, 0, (385 / 1048576 : ℚ)⟩,
   ⟨4, 18, 0, (7315 / 4194304 : ℚ)⟩,
   ⟨5, 17, 0, (13167 / 2097152 : ℚ)⟩,
   ⟨6, 16, 0, (74613 / 4194304 : ℚ)⟩,
   ⟨7, 15, 0, (10659 / 262144 : ℚ)⟩,
   ⟨8, 14, 0, (159885 / 2097152 : ℚ)⟩,
   ⟨9, 13, 0, (124355 / 1048576 : ℚ)⟩,
   ⟨10, 12, 0, (323323 / 2097152 : ℚ)⟩,
   ⟨11, 11, 0, (88179 / 524288 : ℚ)⟩,
   ⟨12, 10, 0, (323323 / 2097152 : ℚ)⟩,
   ⟨13, 9, 0, (124355 / 1048576 : ℚ)⟩,
   ⟨14, 8, 0, (159885 / 2097152 : ℚ)⟩,
   ⟨15, 7, 0, (10659 / 262144 : ℚ)⟩,
   ⟨16, 6, 0, (74613 / 4194304 : ℚ)⟩,
   ⟨17, 5, 0, (13167 / 2097152 : ℚ)⟩,
   ⟨18, 4, 0, (7315 / 4194304 : ℚ)⟩,
   ⟨19, 3, 0, (385 / 1048576 : ℚ)⟩,
   ⟨20, 2, 0, (231 / 4194304 : ℚ)⟩,
   ⟨21, 1, 0, (11 / 2097152 : ℚ)⟩,
   ⟨22, 0, 0, (1 / 4194304 : ℚ)⟩]

theorem halfPower22_checked : equalityCheck (mulTrunc 24 halfPower1 halfPower21) halfPower22 = true := by
  decide +kernel

theorem halfPower22_approximates {k : ℂ} (hk : k ≠ 0) :
    Approximates 24 k (fun z => halfSum z^22) halfPower22 := by
  convert ((halfPower1_approximates hk).mul hk (halfPower21_approximates hk)).replacePolynomial
    (equalityCheck_sound halfPower22_checked k) using 1
  funext z
  ring

end GeneralCK.Reflection.SmallBiasHalfSumPowers

end


