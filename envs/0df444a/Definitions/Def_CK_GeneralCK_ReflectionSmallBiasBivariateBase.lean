-- Prove2me | Definitions.Def_CK_GeneralCK_ReflectionSmallBiasBivariateBase
-- name    : CK_GeneralCK_ReflectionSmallBiasBivariateBase
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T18:03:27.497896+00:00
-- url     : https://prove2.me/theorems/3f3b87ce-2653-4984-a524-1c18750ccade
-- title:
--   Courtade–Kumar proof module `GeneralCK.ReflectionSmallBiasBivariateBase` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.ReflectionSmallBiasBivariateBase` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.ReflectionSmallBiasBivariateBase` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.ReflectionSmallBiasBivariateBase (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/ReflectionSmallBiasBivariateBase.lean)

import Definitions.Def_CK_GeneralCK_ReflectionSmallBiasJetRawSum

-- ===== source module GeneralCK.ReflectionSmallBiasBivariateBase =====
section

namespace GeneralCK.Reflection.SmallBiasBivariateBase

open SmallBiasPolynomial SmallBiasJet

set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def meanFunction (z : ℂ × ℂ) : ℂ := SmallBiasComplexDomain.meanEntropy z.1 z.2
noncomputable def lossFunction (k : ℂ) (z : ℂ × ℂ) : ℂ := 1-k⁻¹*meanFunction z

def entropyA : List Term :=
  [⟨0, 0, 1, (1 / 1 : ℚ)⟩,
   ⟨2, 0, 0, (-1 / 2 : ℚ)⟩,
   ⟨4, 0, 0, (-1 / 12 : ℚ)⟩,
   ⟨6, 0, 0, (-1 / 30 : ℚ)⟩,
   ⟨8, 0, 0, (-1 / 56 : ℚ)⟩,
   ⟨10, 0, 0, (-1 / 90 : ℚ)⟩,
   ⟨12, 0, 0, (-1 / 132 : ℚ)⟩,
   ⟨14, 0, 0, (-1 / 182 : ℚ)⟩,
   ⟨16, 0, 0, (-1 / 240 : ℚ)⟩,
   ⟨18, 0, 0, (-1 / 306 : ℚ)⟩,
   ⟨20, 0, 0, (-1 / 380 : ℚ)⟩,
   ⟨22, 0, 0, (-1 / 462 : ℚ)⟩]

theorem entropyA_checked : equalityCheck (compactEntropy coordinateA) entropyA = true := by
  decide +kernel

def entropyB : List Term :=
  [⟨0, 0, 1, (1 / 1 : ℚ)⟩,
   ⟨0, 2, 0, (-1 / 2 : ℚ)⟩,
   ⟨0, 4, 0, (-1 / 12 : ℚ)⟩,
   ⟨0, 6, 0, (-1 / 30 : ℚ)⟩,
   ⟨0, 8, 0, (-1 / 56 : ℚ)⟩,
   ⟨0, 10, 0, (-1 / 90 : ℚ)⟩,
   ⟨0, 12, 0, (-1 / 132 : ℚ)⟩,
   ⟨0, 14, 0, (-1 / 182 : ℚ)⟩,
   ⟨0, 16, 0, (-1 / 240 : ℚ)⟩,
   ⟨0, 18, 0, (-1 / 306 : ℚ)⟩,
   ⟨0, 20, 0, (-1 / 380 : ℚ)⟩,
   ⟨0, 22, 0, (-1 / 462 : ℚ)⟩]

theorem entropyB_checked : equalityCheck (compactEntropy coordinateB) entropyB = true := by
  decide +kernel

def meanPolynomial : List Term :=
  [⟨0, 0, 1, (1 / 1 : ℚ)⟩,
   ⟨0, 2, 0, (-1 / 4 : ℚ)⟩,
   ⟨0, 4, 0, (-1 / 24 : ℚ)⟩,
   ⟨0, 6, 0, (-1 / 60 : ℚ)⟩,
   ⟨0, 8, 0, (-1 / 112 : ℚ)⟩,
   ⟨0, 10, 0, (-1 / 180 : ℚ)⟩,
   ⟨0, 12, 0, (-1 / 264 : ℚ)⟩,
   ⟨0, 14, 0, (-1 / 364 : ℚ)⟩,
   ⟨0, 16, 0, (-1 / 480 : ℚ)⟩,
   ⟨0, 18, 0, (-1 / 612 : ℚ)⟩,
   ⟨0, 20, 0, (-1 / 760 : ℚ)⟩,
   ⟨0, 22, 0, (-1 / 924 : ℚ)⟩,
   ⟨2, 0, 0, (-1 / 4 : ℚ)⟩,
   ⟨4, 0, 0, (-1 / 24 : ℚ)⟩,
   ⟨6, 0, 0, (-1 / 60 : ℚ)⟩,
   ⟨8, 0, 0, (-1 / 112 : ℚ)⟩,
   ⟨10, 0, 0, (-1 / 180 : ℚ)⟩,
   ⟨12, 0, 0, (-1 / 264 : ℚ)⟩,
   ⟨14, 0, 0, (-1 / 364 : ℚ)⟩,
   ⟨16, 0, 0, (-1 / 480 : ℚ)⟩,
   ⟨18, 0, 0, (-1 / 612 : ℚ)⟩,
   ⟨20, 0, 0, (-1 / 760 : ℚ)⟩,
   ⟨22, 0, 0, (-1 / 924 : ℚ)⟩]

theorem meanPolynomial_checked : equalityCheck (scale (1/2) (add entropyA entropyB)) meanPolynomial = true := by
  decide +kernel

def lossPolynomial : List Term :=
  [⟨0, 2, -1, (1 / 4 : ℚ)⟩,
   ⟨0, 4, -1, (1 / 24 : ℚ)⟩,
   ⟨0, 6, -1, (1 / 60 : ℚ)⟩,
   ⟨0, 8, -1, (1 / 112 : ℚ)⟩,
   ⟨0, 10, -1, (1 / 180 : ℚ)⟩,
   ⟨0, 12, -1, (1 / 264 : ℚ)⟩,
   ⟨0, 14, -1, (1 / 364 : ℚ)⟩,
   ⟨0, 16, -1, (1 / 480 : ℚ)⟩,
   ⟨0, 18, -1, (1 / 612 : ℚ)⟩,
   ⟨0, 20, -1, (1 / 760 : ℚ)⟩,
   ⟨0, 22, -1, (1 / 924 : ℚ)⟩,
   ⟨2, 0, -1, (1 / 4 : ℚ)⟩,
   ⟨4, 0, -1, (1 / 24 : ℚ)⟩,
   ⟨6, 0, -1, (1 / 60 : ℚ)⟩,
   ⟨8, 0, -1, (1 / 112 : ℚ)⟩,
   ⟨10, 0, -1, (1 / 180 : ℚ)⟩,
   ⟨12, 0, -1, (1 / 264 : ℚ)⟩,
   ⟨14, 0, -1, (1 / 364 : ℚ)⟩,
   ⟨16, 0, -1, (1 / 480 : ℚ)⟩,
   ⟨18, 0, -1, (1 / 612 : ℚ)⟩,
   ⟨20, 0, -1, (1 / 760 : ℚ)⟩,
   ⟨22, 0, -1, (1 / 924 : ℚ)⟩]

theorem lossPolynomial_checked : equalityCheck (add (const 1) (scale (-1) (mulTrunc 24 (parameter (-1)) meanPolynomial))) lossPolynomial = true := by
  decide +kernel

theorem mean_approximates {k : ℂ} (hk : k ≠ 0) (hklog : k = (Real.log 2:ℂ)) :
    Approximates 24 k meanFunction meanPolynomial := by
  have ha := ((Approximates.coordinateA 24 k).compactEntropy hk hklog (by rfl)).replacePolynomial
    (equalityCheck_sound entropyA_checked k)
  have hb := ((Approximates.coordinateB 24 k).compactEntropy hk hklog (by rfl)).replacePolynomial
    (equalityCheck_sound entropyB_checked k)
  convert ((ha.add hb).scale (1/2)).replacePolynomial (equalityCheck_sound meanPolynomial_checked k) using 1
  funext z
  simp only [meanFunction,SmallBiasComplexDomain.meanEntropy,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat]
  ring

theorem loss_approximates {k : ℂ} (hk : k ≠ 0) (hklog : k = (Real.log 2:ℂ)) :
    Approximates 24 k (lossFunction k) lossPolynomial := by
  have he := mean_approximates hk hklog
  have hh := (Approximates.const 24 k 1).add (((Approximates.parameter 24 k (-1)).mul hk he).scale (-1))
  convert hh.replacePolynomial (equalityCheck_sound lossPolynomial_checked k) using 1
  funext z
  simp only [lossFunction,zpow_neg_one,Rat.cast_neg,Rat.cast_one]
  ring

theorem loss_zero {k : ℂ} (hk : k ≠ 0) (hklog : k = (Real.log 2:ℂ)) : lossFunction k 0 = 0 := by
  have he : meanFunction 0 = (Real.log 2:ℂ) := by
    simp [meanFunction,SmallBiasComplexDomain.meanEntropy,ComplexEntropy.entropyExt]
  rw [lossFunction,he,← hklog,inv_mul_cancel₀ hk,sub_self]

def lossPower0 : List Term := const 1
def lossPower1 : List Term := lossPolynomial

theorem lossPower0_approximates {k : ℂ} (hk : k ≠ 0) (hklog : k = (Real.log 2:ℂ)) :
    Approximates 24 k (fun z => lossFunction k z ^ 0) lossPower0 := by
  simpa only [pow_zero,Rat.cast_one,lossPower0] using Approximates.const 24 k 1

theorem lossPower1_approximates {k : ℂ} (hk : k ≠ 0) (hklog : k = (Real.log 2:ℂ)) :
    Approximates 24 k (fun z => lossFunction k z ^ 1) lossPower1 := by
  simpa only [pow_one,lossPower1] using loss_approximates hk hklog

def lossPower2 : List Term :=
  [⟨0, 4, -2, (1 / 16 : ℚ)⟩,
   ⟨0, 6, -2, (1 / 48 : ℚ)⟩,
   ⟨0, 8, -2, (29 / 2880 : ℚ)⟩,
   ⟨0, 10, -2, (59 / 10080 : ℚ)⟩,
   ⟨0, 12, -2, (383 / 100800 : ℚ)⟩,
   ⟨0, 14, -2, (883 / 332640 : ℚ)⟩,
   ⟨0, 16, -2, (2366149 / 1210809600 : ℚ)⟩,
   ⟨0, 18, -2, (4313 / 2882880 : ℚ)⟩,
   ⟨0, 20, -2, (5207771 / 4410806400 : ℚ)⟩,
   ⟨0, 22, -2, (31112971 / 32590958400 : ℚ)⟩,
   ⟨2, 2, -2, (1 / 8 : ℚ)⟩,
   ⟨2, 4, -2, (1 / 48 : ℚ)⟩,
   ⟨2, 6, -2, (1 / 120 : ℚ)⟩,
   ⟨2, 8, -2, (1 / 224 : ℚ)⟩,
   ⟨2, 10, -2, (1 / 360 : ℚ)⟩,
   ⟨2, 12, -2, (1 / 528 : ℚ)⟩,
   ⟨2, 14, -2, (1 / 728 : ℚ)⟩,
   ⟨2, 16, -2, (1 / 960 : ℚ)⟩,
   ⟨2, 18, -2, (1 / 1224 : ℚ)⟩,
   ⟨2, 20, -2, (1 / 1520 : ℚ)⟩,
   ⟨4, 0, -2, (1 / 16 : ℚ)⟩,
   ⟨4, 2, -2, (1 / 48 : ℚ)⟩,
   ⟨4, 4, -2, (1 / 288 : ℚ)⟩,
   ⟨4, 6, -2, (1 / 720 : ℚ)⟩,
   ⟨4, 8, -2, (1 / 1344 : ℚ)⟩,
   ⟨4, 10, -2, (1 / 2160 : ℚ)⟩,
   ⟨4, 12, -2, (1 / 3168 : ℚ)⟩,
   ⟨4, 14, -2, (1 / 4368 : ℚ)⟩,
   ⟨4, 16, -2, (1 / 5760 : ℚ)⟩,
   ⟨4, 18, -2, (1 / 7344 : ℚ)⟩,
   ⟨6, 0, -2, (1 / 48 : ℚ)⟩,
   ⟨6, 2, -2, (1 / 120 : ℚ)⟩,
   ⟨6, 4, -2, (1 / 720 : ℚ)⟩,
   ⟨6, 6, -2, (1 / 1800 : ℚ)⟩,
   ⟨6, 8, -2, (1 / 3360 : ℚ)⟩,
   ⟨6, 10, -2, (1 / 5400 : ℚ)⟩,
   ⟨6, 12, -2, (1 / 7920 : ℚ)⟩,
   ⟨6, 14, -2, (1 / 10920 : ℚ)⟩,
   ⟨6, 16, -2, (1 / 14400 : ℚ)⟩,
   ⟨8, 0, -2, (29 / 2880 : ℚ)⟩,
   ⟨8, 2, -2, (1 / 224 : ℚ)⟩,
   ⟨8, 4, -2, (1 / 1344 : ℚ)⟩,
   ⟨8, 6, -2, (1 / 3360 : ℚ)⟩,
   ⟨8, 8, -2, (1 / 6272 : ℚ)⟩,
   ⟨8, 10, -2, (1 / 10080 : ℚ)⟩,
   ⟨8, 12, -2, (1 / 14784 : ℚ)⟩,
   ⟨8, 14, -2, (1 / 20384 : ℚ)⟩,
   ⟨10, 0, -2, (59 / 10080 : ℚ)⟩,
   ⟨10, 2, -2, (1 / 360 : ℚ)⟩,
   ⟨10, 4, -2, (1 / 2160 : ℚ)⟩,
   ⟨10, 6, -2, (1 / 5400 : ℚ)⟩,
   ⟨10, 8, -2, (1 / 10080 : ℚ)⟩,
   ⟨10, 10, -2, (1 / 16200 : ℚ)⟩,
   ⟨10, 12, -2, (1 / 23760 : ℚ)⟩,
   ⟨12, 0, -2, (383 / 100800 : ℚ)⟩,
   ⟨12, 2, -2, (1 / 528 : ℚ)⟩,
   ⟨12, 4, -2, (1 / 3168 : ℚ)⟩,
   ⟨12, 6, -2, (1 / 7920 : ℚ)⟩,
   ⟨12, 8, -2, (1 / 14784 : ℚ)⟩,
   ⟨12, 10, -2, (1 / 23760 : ℚ)⟩,
   ⟨14, 0, -2, (883 / 332640 : ℚ)⟩,
   ⟨14, 2, -2, (1 / 728 : ℚ)⟩,
   ⟨14, 4, -2, (1 / 4368 : ℚ)⟩,
   ⟨14, 6, -2, (1 / 10920 : ℚ)⟩,
   ⟨14, 8, -2, (1 / 20384 : ℚ)⟩,
   ⟨16, 0, -2, (2366149 / 1210809600 : ℚ)⟩,
   ⟨16, 2, -2, (1 / 960 : ℚ)⟩,
   ⟨16, 4, -2, (1 / 5760 : ℚ)⟩,
   ⟨16, 6, -2, (1 / 14400 : ℚ)⟩,
   ⟨18, 0, -2, (4313 / 2882880 : ℚ)⟩,
   ⟨18, 2, -2, (1 / 1224 : ℚ)⟩,
   ⟨18, 4, -2, (1 / 7344 : ℚ)⟩,
   ⟨20, 0, -2, (5207771 / 4410806400 : ℚ)⟩,
   ⟨20, 2, -2, (1 / 1520 : ℚ)⟩,
   ⟨22, 0, -2, (31112971 / 32590958400 : ℚ)⟩]

theorem lossPower2_checked : equalityCheck (mulTrunc 24 lossPower1 lossPolynomial) lossPower2 = true := by
  decide +kernel

theorem lossPower2_approximates {k : ℂ} (hk : k ≠ 0) (hklog : k = (Real.log 2:ℂ)) :
    Approximates 24 k (fun z => lossFunction k z ^ 2) lossPower2 := by
  convert ((lossPower1_approximates hk hklog).mul hk (loss_approximates hk hklog)).replacePolynomial
    (equalityCheck_sound lossPower2_checked k) using 1
  funext z
  ring

def lossPower3 : List Term :=
  [⟨0, 6, -3, (1 / 64 : ℚ)⟩,
   ⟨0, 8, -3, (1 / 128 : ℚ)⟩,
   ⟨0, 10, -3, (17 / 3840 : ℚ)⟩,
   ⟨0, 12, -3, (1349 / 483840 : ℚ)⟩,
   ⟨0, 14, -3, (191 / 100800 : ℚ)⟩,
   ⟨0, 16, -3, (24161 / 17740800 : ℚ)⟩,
   ⟨0, 18, -3, (24731947 / 24216192000 : ℚ)⟩,
   ⟨0, 20, -3, (7668901 / 9686476800 : ℚ)⟩,
   ⟨0, 22, -3, (86485933 / 137225088000 : ℚ)⟩,
   ⟨2, 4, -3, (3 / 64 : ℚ)⟩,
   ⟨2, 6, -3, (1 / 64 : ℚ)⟩,
   ⟨2, 8, -3, (29 / 3840 : ℚ)⟩,
   ⟨2, 10, -3, (59 / 13440 : ℚ)⟩,
   ⟨2, 12, -3, (383 / 134400 : ℚ)⟩,
   ⟨2, 14, -3, (883 / 443520 : ℚ)⟩,
   ⟨2, 16, -3, (2366149 / 1614412800 : ℚ)⟩,
   ⟨2, 18, -3, (4313 / 3843840 : ℚ)⟩,
   ⟨2, 20, -3, (5207771 / 5881075200 : ℚ)⟩,
   ⟨4, 2, -3, (3 / 64 : ℚ)⟩,
   ⟨4, 4, -3, (1 / 64 : ℚ)⟩,
   ⟨4, 6, -3, (11 / 1920 : ℚ)⟩,
   ⟨4, 8, -3, (473 / 161280 : ℚ)⟩,
   ⟨4, 10, -3, (143 / 80640 : ℚ)⟩,
   ⟨4, 12, -3, (10513 / 8870400 : ℚ)⟩,
   ⟨4, 14, -3, (29299 / 34594560 : ℚ)⟩,
   ⟨4, 16, -3, (6149929 / 9686476800 : ℚ)⟩,
   ⟨4, 18, -3, (193441 / 392071680 : ℚ)⟩,
   ⟨6, 0, -3, (1 / 64 : ℚ)⟩,
   ⟨6, 2, -3, (1 / 64 : ℚ)⟩,
   ⟨6, 4, -3, (11 / 1920 : ℚ)⟩,
   ⟨6, 6, -3, (1 / 480 : ℚ)⟩,
   ⟨6, 8, -3, (107 / 100800 : ℚ)⟩,
   ⟨6, 10, -3, (43 / 67200 : ℚ)⟩,
   ⟨6, 12, -3, (9463 / 22176000 : ℚ)⟩,
   ⟨6, 14, -3, (26329 / 86486400 : ℚ)⟩,
   ⟨6, 16, -3, (5519299 / 24216192000 : ℚ)⟩,
   ⟨8, 0, -3, (1 / 128 : ℚ)⟩,
   ⟨8, 2, -3, (29 / 3840 : ℚ)⟩,
   ⟨8, 4, -3, (473 / 161280 : ℚ)⟩,
   ⟨8, 6, -3, (107 / 100800 : ℚ)⟩,
   ⟨8, 8, -3, (29 / 53760 : ℚ)⟩,
   ⟨8, 10, -3, (5497 / 16934400 : ℚ)⟩,
   ⟨8, 12, -3, (26849 / 124185600 : ℚ)⟩,
   ⟨8, 14, -3, (24877 / 161441280 : ℚ)⟩,
   ⟨10, 0, -3, (17 / 3840 : ℚ)⟩,
   ⟨10, 2, -3, (59 / 13440 : ℚ)⟩,
   ⟨10, 4, -3, (143 / 80640 : ℚ)⟩,
   ⟨10, 6, -3, (43 / 67200 : ℚ)⟩,
   ⟨10, 8, -3, (5497 / 16934400 : ℚ)⟩,
   ⟨10, 10, -3, (59 / 302400 : ℚ)⟩,
   ⟨10, 12, -3, (617 / 4752000 : ℚ)⟩,
   ⟨12, 0, -3, (1349 / 483840 : ℚ)⟩,
   ⟨12, 2, -3, (383 / 134400 : ℚ)⟩,
   ⟨12, 4, -3, (10513 / 8870400 : ℚ)⟩,
   ⟨12, 6, -3, (9463 / 22176000 : ℚ)⟩,
   ⟨12, 8, -3, (26849 / 124185600 : ℚ)⟩,
   ⟨12, 10, -3, (617 / 4752000 : ℚ)⟩,
   ⟨14, 0, -3, (191 / 100800 : ℚ)⟩,
   ⟨14, 2, -3, (883 / 443520 : ℚ)⟩,
   ⟨14, 4, -3, (29299 / 34594560 : ℚ)⟩,
   ⟨14, 6, -3, (26329 / 86486400 : ℚ)⟩,
   ⟨14, 8, -3, (24877 / 161441280 : ℚ)⟩,
   ⟨16, 0, -3, (24161 / 17740800 : ℚ)⟩,
   ⟨16, 2, -3, (2366149 / 1614412800 : ℚ)⟩,
   ⟨16, 4, -3, (6149929 / 9686476800 : ℚ)⟩,
   ⟨16, 6, -3, (5519299 / 24216192000 : ℚ)⟩,
   ⟨18, 0, -3, (24731947 / 24216192000 : ℚ)⟩,
   ⟨18, 2, -3, (4313 / 3843840 : ℚ)⟩,
   ⟨18, 4, -3, (193441 / 392071680 : ℚ)⟩,
   ⟨20, 0, -3, (7668901 / 9686476800 : ℚ)⟩,
   ⟨20, 2, -3, (5207771 / 5881075200 : ℚ)⟩,
   ⟨22, 0, -3, (86485933 / 137225088000 : ℚ)⟩]

theorem lossPower3_checked : equalityCheck (mulTrunc 24 lossPower2 lossPolynomial) lossPower3 = true := by
  decide +kernel

theorem lossPower3_approximates {k : ℂ} (hk : k ≠ 0) (hklog : k = (Real.log 2:ℂ)) :
    Approximates 24 k (fun z => lossFunction k z ^ 3) lossPower3 := by
  convert ((lossPower2_approximates hk hklog).mul hk (loss_approximates hk hklog)).replacePolynomial
    (equalityCheck_sound lossPower3_checked k) using 1
  funext z
  ring

def lossPower4 : List Term :=
  [⟨0, 8, -4, (1 / 256 : ℚ)⟩,
   ⟨0, 10, -4, (1 / 384 : ℚ)⟩,
   ⟨0, 12, -4, (13 / 7680 : ℚ)⟩,
   ⟨0, 14, -4, (557 / 483840 : ℚ)⟩,
   ⟨0, 16, -4, (47623 / 58060800 : ℚ)⟩,
   ⟨0, 18, -4, (97079 / 159667200 : ℚ)⟩,
   ⟨0, 20, -4, (5638231 / 12108096000 : ℚ)⟩,
   ⟨0, 22, -4, (159698531 / 435891456000 : ℚ)⟩,
   ⟨2, 6, -4, (1 / 64 : ℚ)⟩,
   ⟨2, 8, -4, (1 / 128 : ℚ)⟩,
   ⟨2, 10, -4, (17 / 3840 : ℚ)⟩,
   ⟨2, 12, -4, (1349 / 483840 : ℚ)⟩,
   ⟨2, 14, -4, (191 / 100800 : ℚ)⟩,
   ⟨2, 16, -4, (24161 / 17740800 : ℚ)⟩,
   ⟨2, 18, -4, (24731947 / 24216192000 : ℚ)⟩,
   ⟨2, 20, -4, (7668901 / 9686476800 : ℚ)⟩,
   ⟨4, 4, -4, (3 / 128 : ℚ)⟩,
   ⟨4, 6, -4, (1 / 96 : ℚ)⟩,
   ⟨4, 8, -4, (13 / 2560 : ℚ)⟩,
   ⟨4, 10, -4, (473 / 161280 : ℚ)⟩,
   ⟨4, 12, -4, (27427 / 14515200 : ℚ)⟩,
   ⟨4, 14, -4, (17447 / 13305600 : ℚ)⟩,
   ⟨4, 16, -4, (4648549 / 4843238400 : ℚ)⟩,
   ⟨4, 18, -4, (9658877 / 13208832000 : ℚ)⟩,
   ⟨6, 2, -4, (1 / 64 : ℚ)⟩,
   ⟨6, 4, -4, (1 / 96 : ℚ)⟩,
   ⟨6, 6, -4, (3 / 640 : ℚ)⟩,
   ⟨6, 8, -4, (377 / 161280 : ℚ)⟩,
   ⟨6, 10, -4, (277 / 201600 : ℚ)⟩,
   ⟨6, 12, -4, (8957 / 9979200 : ℚ)⟩,
   ⟨6, 14, -4, (544727 / 864864000 : ℚ)⟩,
   ⟨6, 16, -4, (682859 / 1467648000 : ℚ)⟩,
   ⟨8, 0, -4, (1 / 256 : ℚ)⟩,
   ⟨8, 2, -4, (1 / 128 : ℚ)⟩,
   ⟨8, 4, -4, (13 / 2560 : ℚ)⟩,
   ⟨8, 6, -4, (377 / 161280 : ℚ)⟩,
   ⟨8, 8, -4, (11287 / 9676800 : ℚ)⟩,
   ⟨8, 10, -4, (829 / 1209600 : ℚ)⟩,
   ⟨8, 12, -4, (92623 / 206976000 : ℚ)⟩,
   ⟨8, 14, -4, (912181 / 2905943040 : ℚ)⟩,
   ⟨10, 0, -4, (1 / 384 : ℚ)⟩,
   ⟨10, 2, -4, (17 / 3840 : ℚ)⟩,
   ⟨10, 4, -4, (473 / 161280 : ℚ)⟩,
   ⟨10, 6, -4, (277 / 201600 : ℚ)⟩,
   ⟨10, 8, -4, (829 / 1209600 : ℚ)⟩,
   ⟨10, 10, -4, (757 / 1881600 : ℚ)⟩,
   ⟨10, 12, -4, (4400383 / 16765056000 : ℚ)⟩,
   ⟨12, 0, -4, (13 / 7680 : ℚ)⟩,
   ⟨12, 2, -4, (1349 / 483840 : ℚ)⟩,
   ⟨12, 4, -4, (27427 / 14515200 : ℚ)⟩,
   ⟨12, 6, -4, (8957 / 9979200 : ℚ)⟩,
   ⟨12, 8, -4, (92623 / 206976000 : ℚ)⟩,
   ⟨12, 10, -4, (4400383 / 16765056000 : ℚ)⟩,
   ⟨14, 0, -4, (557 / 483840 : ℚ)⟩,
   ⟨14, 2, -4, (191 / 100800 : ℚ)⟩,
   ⟨14, 4, -4, (17447 / 13305600 : ℚ)⟩,
   ⟨14, 6, -4, (544727 / 864864000 : ℚ)⟩,
   ⟨14, 8, -4, (912181 / 2905943040 : ℚ)⟩,
   ⟨16, 0, -4, (47623 / 58060800 : ℚ)⟩,
   ⟨16, 2, -4, (24161 / 17740800 : ℚ)⟩,
   ⟨16, 4, -4, (4648549 / 4843238400 : ℚ)⟩,
   ⟨16, 6, -4, (682859 / 1467648000 : ℚ)⟩,
   ⟨18, 0, -4, (97079 / 159667200 : ℚ)⟩,
   ⟨18, 2, -4, (24731947 / 24216192000 : ℚ)⟩,
   ⟨18, 4, -4, (9658877 / 13208832000 : ℚ)⟩,
   ⟨20, 0, -4, (5638231 / 12108096000 : ℚ)⟩,
   ⟨20, 2, -4, (7668901 / 9686476800 : ℚ)⟩,
   ⟨22, 0, -4, (159698531 / 435891456000 : ℚ)⟩]

theorem lossPower4_checked : equalityCheck (mulTrunc 24 lossPower3 lossPolynomial) lossPower4 = true := by
  decide +kernel

theorem lossPower4_approximates {k : ℂ} (hk : k ≠ 0) (hklog : k = (Real.log 2:ℂ)) :
    Approximates 24 k (fun z => lossFunction k z ^ 4) lossPower4 := by
  convert ((lossPower3_approximates hk hklog).mul hk (loss_approximates hk hklog)).replacePolynomial
    (equalityCheck_sound lossPower4_checked k) using 1
  funext z
  ring

def lossPower5 : List Term :=
  [⟨0, 10, -5, (1 / 1024 : ℚ)⟩,
   ⟨0, 12, -5, (5 / 6144 : ℚ)⟩,
   ⟨0, 14, -5, (11 / 18432 : ℚ)⟩,
   ⟨0, 16, -5, (169 / 387072 : ℚ)⟩,
   ⟨0, 18, -5, (15151 / 46448640 : ℚ)⟩,
   ⟨0, 20, -5, (765613 / 3065610240 : ℚ)⟩,
   ⟨0, 22, -5, (136484171 / 697426329600 : ℚ)⟩,
   ⟨2, 8, -5, (5 / 1024 : ℚ)⟩,
   ⟨2, 10, -5, (5 / 1536 : ℚ)⟩,
   ⟨2, 12, -5, (13 / 6144 : ℚ)⟩,
   ⟨2, 14, -5, (557 / 387072 : ℚ)⟩,
   ⟨2, 16, -5, (47623 / 46448640 : ℚ)⟩,
   ⟨2, 18, -5, (97079 / 127733760 : ℚ)⟩,
   ⟨2, 20, -5, (5638231 / 9686476800 : ℚ)⟩,
   ⟨4, 6, -5, (5 / 512 : ℚ)⟩,
   ⟨4, 8, -5, (35 / 6144 : ℚ)⟩,
   ⟨4, 10, -5, (61 / 18432 : ℚ)⟩,
   ⟨4, 12, -5, (811 / 387072 : ℚ)⟩,
   ⟨4, 14, -5, (16537 / 11612160 : ℚ)⟩,
   ⟨4, 16, -5, (3133241 / 3065610240 : ℚ)⟩,
   ⟨4, 18, -5, (66689617 / 87178291200 : ℚ)⟩,
   ⟨6, 4, -5, (5 / 512 : ℚ)⟩,
   ⟨6, 6, -5, (5 / 768 : ℚ)⟩,
   ⟨6, 8, -5, (65 / 18432 : ℚ)⟩,
   ⟨6, 10, -5, (265 / 129024 : ℚ)⟩,
   ⟨6, 12, -5, (15277 / 11612160 : ℚ)⟩,
   ⟨6, 14, -5, (57829 / 63866880 : ℚ)⟩,
   ⟨6, 16, -5, (458502623 / 697426329600 : ℚ)⟩,
   ⟨8, 2, -5, (5 / 1024 : ℚ)⟩,
   ⟨8, 4, -5, (35 / 6144 : ℚ)⟩,
   ⟨8, 6, -5, (65 / 18432 : ℚ)⟩,
   ⟨8, 8, -5, (31 / 16128 : ℚ)⟩,
   ⟨8, 10, -5, (8731 / 7741440 : ℚ)⟩,
   ⟨8, 12, -5, (222913 / 306561024 : ℚ)⟩,
   ⟨8, 14, -5, (58494881 / 116237721600 : ℚ)⟩,
   ⟨10, 0, -5, (1 / 1024 : ℚ)⟩,
   ⟨10, 2, -5, (5 / 1536 : ℚ)⟩,
   ⟨10, 4, -5, (61 / 18432 : ℚ)⟩,
   ⟨10, 6, -5, (265 / 129024 : ℚ)⟩,
   ⟨10, 8, -5, (8731 / 7741440 : ℚ)⟩,
   ⟨10, 10, -5, (1283 / 1935360 : ℚ)⟩,
   ⟨10, 12, -5, (358559 / 838252800 : ℚ)⟩,
   ⟨12, 0, -5, (5 / 6144 : ℚ)⟩,
   ⟨12, 2, -5, (13 / 6144 : ℚ)⟩,
   ⟨12, 4, -5, (811 / 387072 : ℚ)⟩,
   ⟨12, 6, -5, (15277 / 11612160 : ℚ)⟩,
   ⟨12, 8, -5, (222913 / 306561024 : ℚ)⟩,
   ⟨12, 10, -5, (358559 / 838252800 : ℚ)⟩,
   ⟨14, 0, -5, (11 / 18432 : ℚ)⟩,
   ⟨14, 2, -5, (557 / 387072 : ℚ)⟩,
   ⟨14, 4, -5, (16537 / 11612160 : ℚ)⟩,
   ⟨14, 6, -5, (57829 / 63866880 : ℚ)⟩,
   ⟨14, 8, -5, (58494881 / 116237721600 : ℚ)⟩,
   ⟨16, 0, -5, (169 / 387072 : ℚ)⟩,
   ⟨16, 2, -5, (47623 / 46448640 : ℚ)⟩,
   ⟨16, 4, -5, (3133241 / 3065610240 : ℚ)⟩,
   ⟨16, 6, -5, (458502623 / 697426329600 : ℚ)⟩,
   ⟨18, 0, -5, (15151 / 46448640 : ℚ)⟩,
   ⟨18, 2, -5, (97079 / 127733760 : ℚ)⟩,
   ⟨18, 4, -5, (66689617 / 87178291200 : ℚ)⟩,
   ⟨20, 0, -5, (765613 / 3065610240 : ℚ)⟩,
   ⟨20, 2, -5, (5638231 / 9686476800 : ℚ)⟩,
   ⟨22, 0, -5, (136484171 / 697426329600 : ℚ)⟩]

theorem lossPower5_checked : equalityCheck (mulTrunc 24 lossPower4 lossPolynomial) lossPower5 = true := by
  decide +kernel

theorem lossPower5_approximates {k : ℂ} (hk : k ≠ 0) (hklog : k = (Real.log 2:ℂ)) :
    Approximates 24 k (fun z => lossFunction k z ^ 5) lossPower5 := by
  convert ((lossPower4_approximates hk hklog).mul hk (loss_approximates hk hklog)).replacePolynomial
    (equalityCheck_sound lossPower5_checked k) using 1
  funext z
  ring

def lossPower6 : List Term :=
  [⟨0, 12, -6, (1 / 4096 : ℚ)⟩,
   ⟨0, 14, -6, (1 / 4096 : ℚ)⟩,
   ⟨0, 16, -6, (49 / 245760 : ℚ)⟩,
   ⟨0, 18, -6, (121 / 774144 : ℚ)⟩,
   ⟨0, 20, -6, (7579 / 61931520 : ℚ)⟩,
   ⟨0, 22, -6, (197941 / 2043740160 : ℚ)⟩,
   ⟨2, 10, -6, (3 / 2048 : ℚ)⟩,
   ⟨2, 12, -6, (5 / 4096 : ℚ)⟩,
   ⟨2, 14, -6, (11 / 12288 : ℚ)⟩,
   ⟨2, 16, -6, (169 / 258048 : ℚ)⟩,
   ⟨2, 18, -6, (15151 / 30965760 : ℚ)⟩,
   ⟨2, 20, -6, (765613 / 2043740160 : ℚ)⟩,
   ⟨4, 8, -6, (15 / 4096 : ℚ)⟩,
   ⟨4, 10, -6, (11 / 4096 : ℚ)⟩,
   ⟨4, 12, -6, (11 / 6144 : ℚ)⟩,
   ⟨4, 14, -6, (317 / 258048 : ℚ)⟩,
   ⟨4, 16, -6, (7769 / 8847360 : ℚ)⟩,
   ⟨4, 18, -6, (1331609 / 2043740160 : ℚ)⟩,
   ⟨6, 6, -6, (5 / 1024 : ℚ)⟩,
   ⟨6, 8, -6, (15 / 4096 : ℚ)⟩,
   ⟨6, 10, -6, (47 / 20480 : ℚ)⟩,
   ⟨6, 12, -6, (1147 / 774144 : ℚ)⟩,
   ⟨6, 14, -6, (7831 / 7741440 : ℚ)⟩,
   ⟨6, 16, -6, (1482881 / 2043740160 : ℚ)⟩,
   ⟨8, 4, -6, (15 / 4096 : ℚ)⟩,
   ⟨8, 6, -6, (15 / 4096 : ℚ)⟩,
   ⟨8, 8, -6, (59 / 24576 : ℚ)⟩,
   ⟨8, 10, -6, (191 / 129024 : ℚ)⟩,
   ⟨8, 12, -6, (29651 / 30965760 : ℚ)⟩,
   ⟨8, 14, -6, (671837 / 1021870080 : ℚ)⟩,
   ⟨10, 2, -6, (3 / 2048 : ℚ)⟩,
   ⟨10, 4, -6, (11 / 4096 : ℚ)⟩,
   ⟨10, 6, -6, (47 / 20480 : ℚ)⟩,
   ⟨10, 8, -6, (191 / 129024 : ℚ)⟩,
   ⟨10, 10, -6, (1573 / 1720320 : ℚ)⟩,
   ⟨10, 12, -6, (606197 / 1021870080 : ℚ)⟩,
   ⟨12, 0, -6, (1 / 4096 : ℚ)⟩,
   ⟨12, 2, -6, (5 / 4096 : ℚ)⟩,
   ⟨12, 4, -6, (11 / 6144 : ℚ)⟩,
   ⟨12, 6, -6, (1147 / 774144 : ℚ)⟩,
   ⟨12, 8, -6, (29651 / 30965760 : ℚ)⟩,
   ⟨12, 10, -6, (606197 / 1021870080 : ℚ)⟩,
   ⟨14, 0, -6, (1 / 4096 : ℚ)⟩,
   ⟨14, 2, -6, (11 / 12288 : ℚ)⟩,
   ⟨14, 4, -6, (317 / 258048 : ℚ)⟩,
   ⟨14, 6, -6, (7831 / 7741440 : ℚ)⟩,
   ⟨14, 8, -6, (671837 / 1021870080 : ℚ)⟩,
   ⟨16, 0, -6, (49 / 245760 : ℚ)⟩,
   ⟨16, 2, -6, (169 / 258048 : ℚ)⟩,
   ⟨16, 4, -6, (7769 / 8847360 : ℚ)⟩,
   ⟨16, 6, -6, (1482881 / 2043740160 : ℚ)⟩,
   ⟨18, 0, -6, (121 / 774144 : ℚ)⟩,
   ⟨18, 2, -6, (15151 / 30965760 : ℚ)⟩,
   ⟨18, 4, -6, (1331609 / 2043740160 : ℚ)⟩,
   ⟨20, 0, -6, (7579 / 61931520 : ℚ)⟩,
   ⟨20, 2, -6, (765613 / 2043740160 : ℚ)⟩,
   ⟨22, 0, -6, (197941 / 2043740160 : ℚ)⟩]

theorem lossPower6_checked : equalityCheck (mulTrunc 24 lossPower5 lossPolynomial) lossPower6 = true := by
  decide +kernel

theorem lossPower6_approximates {k : ℂ} (hk : k ≠ 0) (hklog : k = (Real.log 2:ℂ)) :
    Approximates 24 k (fun z => lossFunction k z ^ 6) lossPower6 := by
  convert ((lossPower5_approximates hk hklog).mul hk (loss_approximates hk hklog)).replacePolynomial
    (equalityCheck_sound lossPower6_checked k) using 1
  funext z
  ring

def lossPower7 : List Term :=
  [⟨0, 14, -7, (1 / 16384 : ℚ)⟩,
   ⟨0, 16, -7, (7 / 98304 : ℚ)⟩,
   ⟨0, 18, -7, (21 / 327680 : ℚ)⟩,
   ⟨0, 20, -7, (949 / 17694720 : ℚ)⟩,
   ⟨0, 22, -7, (23339 / 530841600 : ℚ)⟩,
   ⟨2, 12, -7, (7 / 16384 : ℚ)⟩,
   ⟨2, 14, -7, (7 / 16384 : ℚ)⟩,
   ⟨2, 16, -7, (343 / 983040 : ℚ)⟩,
   ⟨2, 18, -7, (121 / 442368 : ℚ)⟩,
   ⟨2, 20, -7, (7579 / 35389440 : ℚ)⟩,
   ⟨4, 10, -7, (21 / 16384 : ℚ)⟩,
   ⟨4, 12, -7, (7 / 6144 : ℚ)⟩,
   ⟨4, 14, -7, (7 / 8192 : ℚ)⟩,
   ⟨4, 16, -7, (1241 / 1966080 : ℚ)⟩,
   ⟨4, 18, -7, (50293 / 106168320 : ℚ)⟩,
   ⟨6, 8, -7, (35 / 16384 : ℚ)⟩,
   ⟨6, 10, -7, (91 / 49152 : ℚ)⟩,
   ⟨6, 12, -7, (161 / 122880 : ℚ)⟩,
   ⟨6, 14, -7, (2033 / 2211840 : ℚ)⟩,
   ⟨6, 16, -7, (351863 / 530841600 : ℚ)⟩,
   ⟨8, 6, -7, (35 / 16384 : ℚ)⟩,
   ⟨8, 8, -7, (35 / 16384 : ℚ)⟩,
   ⟨8, 10, -7, (749 / 491520 : ℚ)⟩,
   ⟨8, 12, -7, (1825 / 1769472 : ℚ)⟩,
   ⟨8, 14, -7, (4219 / 5898240 : ℚ)⟩,
   ⟨10, 4, -7, (21 / 16384 : ℚ)⟩,
   ⟨10, 6, -7, (91 / 49152 : ℚ)⟩,
   ⟨10, 8, -7, (749 / 491520 : ℚ)⟩,
   ⟨10, 10, -7, (193 / 184320 : ℚ)⟩,
   ⟨10, 12, -7, (186817 / 265420800 : ℚ)⟩,
   ⟨12, 2, -7, (7 / 16384 : ℚ)⟩,
   ⟨12, 4, -7, (7 / 6144 : ℚ)⟩,
   ⟨12, 6, -7, (161 / 122880 : ℚ)⟩,
   ⟨12, 8, -7, (1825 / 1769472 : ℚ)⟩,
   ⟨12, 10, -7, (186817 / 265420800 : ℚ)⟩,
   ⟨14, 0, -7, (1 / 16384 : ℚ)⟩,
   ⟨14, 2, -7, (7 / 16384 : ℚ)⟩,
   ⟨14, 4, -7, (7 / 8192 : ℚ)⟩,
   ⟨14, 6, -7, (2033 / 2211840 : ℚ)⟩,
   ⟨14, 8, -7, (4219 / 5898240 : ℚ)⟩,
   ⟨16, 0, -7, (7 / 98304 : ℚ)⟩,
   ⟨16, 2, -7, (343 / 983040 : ℚ)⟩,
   ⟨16, 4, -7, (1241 / 1966080 : ℚ)⟩,
   ⟨16, 6, -7, (351863 / 530841600 : ℚ)⟩,
   ⟨18, 0, -7, (21 / 327680 : ℚ)⟩,
   ⟨18, 2, -7, (121 / 442368 : ℚ)⟩,
   ⟨18, 4, -7, (50293 / 106168320 : ℚ)⟩,
   ⟨20, 0, -7, (949 / 17694720 : ℚ)⟩,
   ⟨20, 2, -7, (7579 / 35389440 : ℚ)⟩,
   ⟨22, 0, -7, (23339 / 530841600 : ℚ)⟩]

theorem lossPower7_checked : equalityCheck (mulTrunc 24 lossPower6 lossPolynomial) lossPower7 = true := by
  decide +kernel

theorem lossPower7_approximates {k : ℂ} (hk : k ≠ 0) (hklog : k = (Real.log 2:ℂ)) :
    Approximates 24 k (fun z => lossFunction k z ^ 7) lossPower7 := by
  convert ((lossPower6_approximates hk hklog).mul hk (loss_approximates hk hklog)).replacePolynomial
    (equalityCheck_sound lossPower7_checked k) using 1
  funext z
  ring

def lossPower8 : List Term :=
  [⟨0, 16, -8, (1 / 65536 : ℚ)⟩,
   ⟨0, 18, -8, (1 / 49152 : ℚ)⟩,
   ⟨0, 20, -8, (59 / 2949120 : ℚ)⟩,
   ⟨0, 22, -8, (1103 / 61931520 : ℚ)⟩,
   ⟨2, 14, -8, (1 / 8192 : ℚ)⟩,
   ⟨2, 16, -8, (7 / 49152 : ℚ)⟩,
   ⟨2, 18, -8, (21 / 163840 : ℚ)⟩,
   ⟨2, 20, -8, (949 / 8847360 : ℚ)⟩,
   ⟨4, 12, -8, (7 / 16384 : ℚ)⟩,
   ⟨4, 14, -8, (11 / 24576 : ℚ)⟩,
   ⟨4, 16, -8, (1099 / 2949120 : ℚ)⟩,
   ⟨4, 18, -8, (2609 / 8847360 : ℚ)⟩,
   ⟨6, 10, -8, (7 / 8192 : ℚ)⟩,
   ⟨6, 12, -8, (7 / 8192 : ℚ)⟩,
   ⟨6, 14, -8, (31 / 46080 : ℚ)⟩,
   ⟨6, 16, -8, (4493 / 8847360 : ℚ)⟩,
   ⟨8, 8, -8, (35 / 32768 : ℚ)⟩,
   ⟨8, 10, -8, (7 / 6144 : ℚ)⟩,
   ⟨8, 12, -8, (1309 / 1474560 : ℚ)⟩,
   ⟨8, 14, -8, (20099 / 30965760 : ℚ)⟩,
   ⟨10, 6, -8, (7 / 8192 : ℚ)⟩,
   ⟨10, 8, -8, (7 / 6144 : ℚ)⟩,
   ⟨10, 10, -8, (707 / 737280 : ℚ)⟩,
   ⟨10, 12, -8, (3109 / 4423680 : ℚ)⟩,
   ⟨12, 4, -8, (7 / 16384 : ℚ)⟩,
   ⟨12, 6, -8, (7 / 8192 : ℚ)⟩,
   ⟨12, 8, -8, (1309 / 1474560 : ℚ)⟩,
   ⟨12, 10, -8, (3109 / 4423680 : ℚ)⟩,
   ⟨14, 2, -8, (1 / 8192 : ℚ)⟩,
   ⟨14, 4, -8, (11 / 24576 : ℚ)⟩,
   ⟨14, 6, -8, (31 / 46080 : ℚ)⟩,
   ⟨14, 8, -8, (20099 / 30965760 : ℚ)⟩,
   ⟨16, 0, -8, (1 / 65536 : ℚ)⟩,
   ⟨16, 2, -8, (7 / 49152 : ℚ)⟩,
   ⟨16, 4, -8, (1099 / 2949120 : ℚ)⟩,
   ⟨16, 6, -8, (4493 / 8847360 : ℚ)⟩,
   ⟨18, 0, -8, (1 / 49152 : ℚ)⟩,
   ⟨18, 2, -8, (21 / 163840 : ℚ)⟩,
   ⟨18, 4, -8, (2609 / 8847360 : ℚ)⟩,
   ⟨20, 0, -8, (59 / 2949120 : ℚ)⟩,
   ⟨20, 2, -8, (949 / 8847360 : ℚ)⟩,
   ⟨22, 0, -8, (1103 / 61931520 : ℚ)⟩]

theorem lossPower8_checked : equalityCheck (mulTrunc 24 lossPower7 lossPolynomial) lossPower8 = true := by
  decide +kernel

theorem lossPower8_approximates {k : ℂ} (hk : k ≠ 0) (hklog : k = (Real.log 2:ℂ)) :
    Approximates 24 k (fun z => lossFunction k z ^ 8) lossPower8 := by
  convert ((lossPower7_approximates hk hklog).mul hk (loss_approximates hk hklog)).replacePolynomial
    (equalityCheck_sound lossPower8_checked k) using 1
  funext z
  ring

def lossPower9 : List Term :=
  [⟨0, 18, -9, (1 / 262144 : ℚ)⟩,
   ⟨0, 20, -9, (3 / 524288 : ℚ)⟩,
   ⟨0, 22, -9, (1 / 163840 : ℚ)⟩,
   ⟨2, 16, -9, (9 / 262144 : ℚ)⟩,
   ⟨2, 18, -9, (3 / 65536 : ℚ)⟩,
   ⟨2, 20, -9, (59 / 1310720 : ℚ)⟩,
   ⟨4, 14, -9, (9 / 65536 : ℚ)⟩,
   ⟨4, 16, -9, (87 / 524288 : ℚ)⟩,
   ⟨4, 18, -9, (199 / 1310720 : ℚ)⟩,
   ⟨6, 12, -9, (21 / 65536 : ℚ)⟩,
   ⟨6, 14, -9, (3 / 8192 : ℚ)⟩,
   ⟨6, 16, -9, (13 / 40960 : ℚ)⟩,
   ⟨8, 10, -9, (63 / 131072 : ℚ)⟩,
   ⟨8, 12, -9, (147 / 262144 : ℚ)⟩,
   ⟨8, 14, -9, (39 / 81920 : ℚ)⟩,
   ⟨10, 8, -9, (63 / 131072 : ℚ)⟩,
   ⟨10, 10, -9, (21 / 32768 : ℚ)⟩,
   ⟨10, 12, -9, (371 / 655360 : ℚ)⟩,
   ⟨12, 6, -9, (21 / 65536 : ℚ)⟩,
   ⟨12, 8, -9, (147 / 262144 : ℚ)⟩,
   ⟨12, 10, -9, (371 / 655360 : ℚ)⟩,
   ⟨14, 4, -9, (9 / 65536 : ℚ)⟩,
   ⟨14, 6, -9, (3 / 8192 : ℚ)⟩,
   ⟨14, 8, -9, (39 / 81920 : ℚ)⟩,
   ⟨16, 2, -9, (9 / 262144 : ℚ)⟩,
   ⟨16, 4, -9, (87 / 524288 : ℚ)⟩,
   ⟨16, 6, -9, (13 / 40960 : ℚ)⟩,
   ⟨18, 0, -9, (1 / 262144 : ℚ)⟩,
   ⟨18, 2, -9, (3 / 65536 : ℚ)⟩,
   ⟨18, 4, -9, (199 / 1310720 : ℚ)⟩,
   ⟨20, 0, -9, (3 / 524288 : ℚ)⟩,
   ⟨20, 2, -9, (59 / 1310720 : ℚ)⟩,
   ⟨22, 0, -9, (1 / 163840 : ℚ)⟩]

theorem lossPower9_checked : equalityCheck (mulTrunc 24 lossPower8 lossPolynomial) lossPower9 = true := by
  decide +kernel

theorem lossPower9_approximates {k : ℂ} (hk : k ≠ 0) (hklog : k = (Real.log 2:ℂ)) :
    Approximates 24 k (fun z => lossFunction k z ^ 9) lossPower9 := by
  convert ((lossPower8_approximates hk hklog).mul hk (loss_approximates hk hklog)).replacePolynomial
    (equalityCheck_sound lossPower9_checked k) using 1
  funext z
  ring

def lossPower10 : List Term :=
  [⟨0, 20, -10, (1 / 1048576 : ℚ)⟩,
   ⟨0, 22, -10, (5 / 3145728 : ℚ)⟩,
   ⟨2, 18, -10, (5 / 524288 : ℚ)⟩,
   ⟨2, 20, -10, (15 / 1048576 : ℚ)⟩,
   ⟨4, 16, -10, (45 / 1048576 : ℚ)⟩,
   ⟨4, 18, -10, (185 / 3145728 : ℚ)⟩,
   ⟨6, 14, -10, (15 / 131072 : ℚ)⟩,
   ⟨6, 16, -10, (155 / 1048576 : ℚ)⟩,
   ⟨8, 12, -10, (105 / 524288 : ℚ)⟩,
   ⟨8, 14, -10, (135 / 524288 : ℚ)⟩,
   ⟨10, 10, -10, (63 / 262144 : ℚ)⟩,
   ⟨10, 12, -10, (175 / 524288 : ℚ)⟩,
   ⟨12, 8, -10, (105 / 524288 : ℚ)⟩,
   ⟨12, 10, -10, (175 / 524288 : ℚ)⟩,
   ⟨14, 6, -10, (15 / 131072 : ℚ)⟩,
   ⟨14, 8, -10, (135 / 524288 : ℚ)⟩,
   ⟨16, 4, -10, (45 / 1048576 : ℚ)⟩,
   ⟨16, 6, -10, (155 / 1048576 : ℚ)⟩,
   ⟨18, 2, -10, (5 / 524288 : ℚ)⟩,
   ⟨18, 4, -10, (185 / 3145728 : ℚ)⟩,
   ⟨20, 0, -10, (1 / 1048576 : ℚ)⟩,
   ⟨20, 2, -10, (15 / 1048576 : ℚ)⟩,
   ⟨22, 0, -10, (5 / 3145728 : ℚ)⟩]

theorem lossPower10_checked : equalityCheck (mulTrunc 24 lossPower9 lossPolynomial) lossPower10 = true := by
  decide +kernel

theorem lossPower10_approximates {k : ℂ} (hk : k ≠ 0) (hklog : k = (Real.log 2:ℂ)) :
    Approximates 24 k (fun z => lossFunction k z ^ 10) lossPower10 := by
  convert ((lossPower9_approximates hk hklog).mul hk (loss_approximates hk hklog)).replacePolynomial
    (equalityCheck_sound lossPower10_checked k) using 1
  funext z
  ring

def lossPower11 : List Term :=
  [⟨0, 22, -11, (1 / 4194304 : ℚ)⟩,
   ⟨2, 20, -11, (11 / 4194304 : ℚ)⟩,
   ⟨4, 18, -11, (55 / 4194304 : ℚ)⟩,
   ⟨6, 16, -11, (165 / 4194304 : ℚ)⟩,
   ⟨8, 14, -11, (165 / 2097152 : ℚ)⟩,
   ⟨10, 12, -11, (231 / 2097152 : ℚ)⟩,
   ⟨12, 10, -11, (231 / 2097152 : ℚ)⟩,
   ⟨14, 8, -11, (165 / 2097152 : ℚ)⟩,
   ⟨16, 6, -11, (165 / 4194304 : ℚ)⟩,
   ⟨18, 4, -11, (55 / 4194304 : ℚ)⟩,
   ⟨20, 2, -11, (11 / 4194304 : ℚ)⟩,
   ⟨22, 0, -11, (1 / 4194304 : ℚ)⟩]

theorem lossPower11_checked : equalityCheck (mulTrunc 24 lossPower10 lossPolynomial) lossPower11 = true := by
  decide +kernel

theorem lossPower11_approximates {k : ℂ} (hk : k ≠ 0) (hklog : k = (Real.log 2:ℂ)) :
    Approximates 24 k (fun z => lossFunction k z ^ 11) lossPower11 := by
  convert ((lossPower10_approximates hk hklog).mul hk (loss_approximates hk hklog)).replacePolynomial
    (equalityCheck_sound lossPower11_checked k) using 1
  funext z
  ring

def lossPower12 : List Term :=
  []

theorem lossPower12_checked : equalityCheck (mulTrunc 24 lossPower11 lossPolynomial) lossPower12 = true := by
  decide +kernel

theorem lossPower12_approximates {k : ℂ} (hk : k ≠ 0) (hklog : k = (Real.log 2:ℂ)) :
    Approximates 24 k (fun z => lossFunction k z ^ 12) lossPower12 := by
  convert ((lossPower11_approximates hk hklog).mul hk (loss_approximates hk hklog)).replacePolynomial
    (equalityCheck_sound lossPower12_checked k) using 1
  funext z
  ring

def lossPower13 : List Term :=
  []

theorem lossPower13_checked : equalityCheck (mulTrunc 24 lossPower12 lossPolynomial) lossPower13 = true := by
  decide +kernel

theorem lossPower13_approximates {k : ℂ} (hk : k ≠ 0) (hklog : k = (Real.log 2:ℂ)) :
    Approximates 24 k (fun z => lossFunction k z ^ 13) lossPower13 := by
  convert ((lossPower12_approximates hk hklog).mul hk (loss_approximates hk hklog)).replacePolynomial
    (equalityCheck_sound lossPower13_checked k) using 1
  funext z
  ring

def lossPower14 : List Term :=
  []

theorem lossPower14_checked : equalityCheck (mulTrunc 24 lossPower13 lossPolynomial) lossPower14 = true := by
  decide +kernel

theorem lossPower14_approximates {k : ℂ} (hk : k ≠ 0) (hklog : k = (Real.log 2:ℂ)) :
    Approximates 24 k (fun z => lossFunction k z ^ 14) lossPower14 := by
  convert ((lossPower13_approximates hk hklog).mul hk (loss_approximates hk hklog)).replacePolynomial
    (equalityCheck_sound lossPower14_checked k) using 1
  funext z
  ring

def lossPower15 : List Term :=
  []

theorem lossPower15_checked : equalityCheck (mulTrunc 24 lossPower14 lossPolynomial) lossPower15 = true := by
  decide +kernel

theorem lossPower15_approximates {k : ℂ} (hk : k ≠ 0) (hklog : k = (Real.log 2:ℂ)) :
    Approximates 24 k (fun z => lossFunction k z ^ 15) lossPower15 := by
  convert ((lossPower14_approximates hk hklog).mul hk (loss_approximates hk hklog)).replacePolynomial
    (equalityCheck_sound lossPower15_checked k) using 1
  funext z
  ring

def lossPower16 : List Term :=
  []

theorem lossPower16_checked : equalityCheck (mulTrunc 24 lossPower15 lossPolynomial) lossPower16 = true := by
  decide +kernel

theorem lossPower16_approximates {k : ℂ} (hk : k ≠ 0) (hklog : k = (Real.log 2:ℂ)) :
    Approximates 24 k (fun z => lossFunction k z ^ 16) lossPower16 := by
  convert ((lossPower15_approximates hk hklog).mul hk (loss_approximates hk hklog)).replacePolynomial
    (equalityCheck_sound lossPower16_checked k) using 1
  funext z
  ring

def lossPower17 : List Term :=
  []

theorem lossPower17_checked : equalityCheck (mulTrunc 24 lossPower16 lossPolynomial) lossPower17 = true := by
  decide +kernel

theorem lossPower17_approximates {k : ℂ} (hk : k ≠ 0) (hklog : k = (Real.log 2:ℂ)) :
    Approximates 24 k (fun z => lossFunction k z ^ 17) lossPower17 := by
  convert ((lossPower16_approximates hk hklog).mul hk (loss_approximates hk hklog)).replacePolynomial
    (equalityCheck_sound lossPower17_checked k) using 1
  funext z
  ring

def lossPower18 : List Term :=
  []

theorem lossPower18_checked : equalityCheck (mulTrunc 24 lossPower17 lossPolynomial) lossPower18 = true := by
  decide +kernel

theorem lossPower18_approximates {k : ℂ} (hk : k ≠ 0) (hklog : k = (Real.log 2:ℂ)) :
    Approximates 24 k (fun z => lossFunction k z ^ 18) lossPower18 := by
  convert ((lossPower17_approximates hk hklog).mul hk (loss_approximates hk hklog)).replacePolynomial
    (equalityCheck_sound lossPower18_checked k) using 1
  funext z
  ring

def lossPower19 : List Term :=
  []

theorem lossPower19_checked : equalityCheck (mulTrunc 24 lossPower18 lossPolynomial) lossPower19 = true := by
  decide +kernel

theorem lossPower19_approximates {k : ℂ} (hk : k ≠ 0) (hklog : k = (Real.log 2:ℂ)) :
    Approximates 24 k (fun z => lossFunction k z ^ 19) lossPower19 := by
  convert ((lossPower18_approximates hk hklog).mul hk (loss_approximates hk hklog)).replacePolynomial
    (equalityCheck_sound lossPower19_checked k) using 1
  funext z
  ring

def lossPower20 : List Term :=
  []

theorem lossPower20_checked : equalityCheck (mulTrunc 24 lossPower19 lossPolynomial) lossPower20 = true := by
  decide +kernel

theorem lossPower20_approximates {k : ℂ} (hk : k ≠ 0) (hklog : k = (Real.log 2:ℂ)) :
    Approximates 24 k (fun z => lossFunction k z ^ 20) lossPower20 := by
  convert ((lossPower19_approximates hk hklog).mul hk (loss_approximates hk hklog)).replacePolynomial
    (equalityCheck_sound lossPower20_checked k) using 1
  funext z
  ring

def lossPower21 : List Term :=
  []

theorem lossPower21_checked : equalityCheck (mulTrunc 24 lossPower20 lossPolynomial) lossPower21 = true := by
  decide +kernel

theorem lossPower21_approximates {k : ℂ} (hk : k ≠ 0) (hklog : k = (Real.log 2:ℂ)) :
    Approximates 24 k (fun z => lossFunction k z ^ 21) lossPower21 := by
  convert ((lossPower20_approximates hk hklog).mul hk (loss_approximates hk hklog)).replacePolynomial
    (equalityCheck_sound lossPower21_checked k) using 1
  funext z
  ring

def lossPower22 : List Term :=
  []

theorem lossPower22_checked : equalityCheck (mulTrunc 24 lossPower21 lossPolynomial) lossPower22 = true := by
  decide +kernel

theorem lossPower22_approximates {k : ℂ} (hk : k ≠ 0) (hklog : k = (Real.log 2:ℂ)) :
    Approximates 24 k (fun z => lossFunction k z ^ 22) lossPower22 := by
  convert ((lossPower21_approximates hk hklog).mul hk (loss_approximates hk hklog)).replacePolynomial
    (equalityCheck_sound lossPower22_checked k) using 1
  funext z
  ring

def lossPower23 : List Term :=
  []

theorem lossPower23_checked : equalityCheck (mulTrunc 24 lossPower22 lossPolynomial) lossPower23 = true := by
  decide +kernel

theorem lossPower23_approximates {k : ℂ} (hk : k ≠ 0) (hklog : k = (Real.log 2:ℂ)) :
    Approximates 24 k (fun z => lossFunction k z ^ 23) lossPower23 := by
  convert ((lossPower22_approximates hk hklog).mul hk (loss_approximates hk hklog)).replacePolynomial
    (equalityCheck_sound lossPower23_checked k) using 1
  funext z
  ring


theorem mean_inverse_eq {k : ℂ} (hk : k ≠ 0) (z : ℂ × ℂ) :
    (meanFunction z)⁻¹ = k⁻¹*(1-lossFunction k z)⁻¹ := by
  have he : 1-lossFunction k z = k⁻¹*meanFunction z := by unfold lossFunction; ring
  rw [he,mul_inv_rev,inv_inv]
  calc
    (meanFunction z)⁻¹ = (meanFunction z)⁻¹*(k⁻¹*k) := by rw [inv_mul_cancel₀ hk,mul_one]
    _ = _ := by ring

end GeneralCK.Reflection.SmallBiasBivariateBase

end


