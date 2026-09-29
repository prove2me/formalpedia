-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_ReflectionSmallBiasPicardReplay1
-- name    : CK_GeneralCK_Certificates_ReflectionSmallBiasPicardReplay1
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T16:04:08.023109+00:00
-- url     : https://prove2.me/theorems/96511ce3-f7d6-4048-aae5-8381dbf1f848
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.ReflectionSmallBiasPicardReplay1` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.ReflectionSmallBiasPicardReplay1` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.ReflectionSmallBiasPicardReplay1` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.ReflectionSmallBiasPicardReplay1 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/ReflectionSmallBiasPicardReplay1.lean)

import Definitions.Def_CK_GeneralCK_Certificates_ReflectionSmallBiasPicardData
import Definitions.Def_CK_GeneralCK_ReflectionSmallBiasJetReplay

-- ===== source module GeneralCK.Certificates.ReflectionSmallBiasPicardReplay1 =====
section

namespace GeneralCK.Reflection.SmallBiasPicardData

open SmallBiasPolynomial SmallBiasJet

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def replay1p2 : List Term :=
  []

theorem replay1p2_checked : equalityCheck (mulTrunc 24 stage0 stage0) replay1p2 = true := by
  decide +kernel

def replay1p4 : List Term :=
  []

theorem replay1p4_checked : equalityCheck (mulTrunc 24 replay1p2 replay1p2) replay1p4 = true := by
  decide +kernel

def replay1p6 : List Term :=
  []

theorem replay1p6_checked : equalityCheck (mulTrunc 24 replay1p2 replay1p4) replay1p6 = true := by
  decide +kernel

def replay1p8 : List Term :=
  []

theorem replay1p8_checked : equalityCheck (mulTrunc 24 replay1p2 replay1p6) replay1p8 = true := by
  decide +kernel

def replay1p10 : List Term :=
  []

theorem replay1p10_checked : equalityCheck (mulTrunc 24 replay1p2 replay1p8) replay1p10 = true := by
  decide +kernel

def replay1p12 : List Term :=
  []

theorem replay1p12_checked : equalityCheck (mulTrunc 24 replay1p2 replay1p10) replay1p12 = true := by
  decide +kernel

def replay1p14 : List Term :=
  []

theorem replay1p14_checked : equalityCheck (mulTrunc 24 replay1p2 replay1p12) replay1p14 = true := by
  decide +kernel

def replay1p16 : List Term :=
  []

theorem replay1p16_checked : equalityCheck (mulTrunc 24 replay1p2 replay1p14) replay1p16 = true := by
  decide +kernel

def replay1p18 : List Term :=
  []

theorem replay1p18_checked : equalityCheck (mulTrunc 24 replay1p2 replay1p16) replay1p18 = true := by
  decide +kernel

def replay1p20 : List Term :=
  []

theorem replay1p20_checked : equalityCheck (mulTrunc 24 replay1p2 replay1p18) replay1p20 = true := by
  decide +kernel

def replay1p22 : List Term :=
  []

theorem replay1p22_checked : equalityCheck (mulTrunc 24 replay1p2 replay1p20) replay1p22 = true := by
  decide +kernel

def replay1e1 : List Term :=
  [⟨0, 0, 1, (1 / 1 : ℚ)⟩]

theorem replay1e1_checked : equalityCheck (add (parameter 1) (scale (-1 / 2 : ℚ) replay1p2)) replay1e1 = true := by
  decide +kernel

def replay1e2 : List Term :=
  [⟨0, 0, 1, (1 / 1 : ℚ)⟩]

theorem replay1e2_checked : equalityCheck (add (replay1e1) (scale (-1 / 12 : ℚ) replay1p4)) replay1e2 = true := by
  decide +kernel

def replay1e3 : List Term :=
  [⟨0, 0, 1, (1 / 1 : ℚ)⟩]

theorem replay1e3_checked : equalityCheck (add (replay1e2) (scale (-1 / 30 : ℚ) replay1p6)) replay1e3 = true := by
  decide +kernel

def replay1e4 : List Term :=
  [⟨0, 0, 1, (1 / 1 : ℚ)⟩]

theorem replay1e4_checked : equalityCheck (add (replay1e3) (scale (-1 / 56 : ℚ) replay1p8)) replay1e4 = true := by
  decide +kernel

def replay1e5 : List Term :=
  [⟨0, 0, 1, (1 / 1 : ℚ)⟩]

theorem replay1e5_checked : equalityCheck (add (replay1e4) (scale (-1 / 90 : ℚ) replay1p10)) replay1e5 = true := by
  decide +kernel

def replay1e6 : List Term :=
  [⟨0, 0, 1, (1 / 1 : ℚ)⟩]

theorem replay1e6_checked : equalityCheck (add (replay1e5) (scale (-1 / 132 : ℚ) replay1p12)) replay1e6 = true := by
  decide +kernel

def replay1e7 : List Term :=
  [⟨0, 0, 1, (1 / 1 : ℚ)⟩]

theorem replay1e7_checked : equalityCheck (add (replay1e6) (scale (-1 / 182 : ℚ) replay1p14)) replay1e7 = true := by
  decide +kernel

def replay1e8 : List Term :=
  [⟨0, 0, 1, (1 / 1 : ℚ)⟩]

theorem replay1e8_checked : equalityCheck (add (replay1e7) (scale (-1 / 240 : ℚ) replay1p16)) replay1e8 = true := by
  decide +kernel

def replay1e9 : List Term :=
  [⟨0, 0, 1, (1 / 1 : ℚ)⟩]

theorem replay1e9_checked : equalityCheck (add (replay1e8) (scale (-1 / 306 : ℚ) replay1p18)) replay1e9 = true := by
  decide +kernel

def replay1e10 : List Term :=
  [⟨0, 0, 1, (1 / 1 : ℚ)⟩]

theorem replay1e10_checked : equalityCheck (add (replay1e9) (scale (-1 / 380 : ℚ) replay1p20)) replay1e10 = true := by
  decide +kernel

def replay1e11 : List Term :=
  [⟨0, 0, 1, (1 / 1 : ℚ)⟩]

theorem replay1e11_checked : equalityCheck (add (replay1e10) (scale (-1 / 462 : ℚ) replay1p22)) replay1e11 = true := by
  decide +kernel

theorem replay1_final_checked :
    equalityCheck (mulTrunc 24 coordinateA replay1e11) stage1 = true := by
  decide +kernel

theorem stage1_replay {k : ℂ} {f : ℂ × ℂ → ℂ}
    (hk : k ≠ 0) (hklog : k = (Real.log 2 : ℂ))
    (hf : Approximates 24 k f stage0) (hf0 : f 0 = 0) :
    Approximates 24 k (fun z => z.1 * ComplexEntropy.entropyExt (f z)) stage1 := by
  have h2 : Approximates 24 k (fun z => f z ^ 2) replay1p2 := by
    convert (hf.mul hk hf).replacePolynomial (equalityCheck_sound replay1p2_checked k) using 1
    funext z
    ring
  have h4 : Approximates 24 k (fun z => f z ^ 4) replay1p4 := by
    convert (h2.mul hk h2).replacePolynomial (equalityCheck_sound replay1p4_checked k) using 1
    funext z
    ring
  have h6 : Approximates 24 k (fun z => f z ^ 6) replay1p6 := by
    convert (h2.mul hk h4).replacePolynomial (equalityCheck_sound replay1p6_checked k) using 1
    funext z
    ring
  have h8 : Approximates 24 k (fun z => f z ^ 8) replay1p8 := by
    convert (h2.mul hk h6).replacePolynomial (equalityCheck_sound replay1p8_checked k) using 1
    funext z
    ring
  have h10 : Approximates 24 k (fun z => f z ^ 10) replay1p10 := by
    convert (h2.mul hk h8).replacePolynomial (equalityCheck_sound replay1p10_checked k) using 1
    funext z
    ring
  have h12 : Approximates 24 k (fun z => f z ^ 12) replay1p12 := by
    convert (h2.mul hk h10).replacePolynomial (equalityCheck_sound replay1p12_checked k) using 1
    funext z
    ring
  have h14 : Approximates 24 k (fun z => f z ^ 14) replay1p14 := by
    convert (h2.mul hk h12).replacePolynomial (equalityCheck_sound replay1p14_checked k) using 1
    funext z
    ring
  have h16 : Approximates 24 k (fun z => f z ^ 16) replay1p16 := by
    convert (h2.mul hk h14).replacePolynomial (equalityCheck_sound replay1p16_checked k) using 1
    funext z
    ring
  have h18 : Approximates 24 k (fun z => f z ^ 18) replay1p18 := by
    convert (h2.mul hk h16).replacePolynomial (equalityCheck_sound replay1p18_checked k) using 1
    funext z
    ring
  have h20 : Approximates 24 k (fun z => f z ^ 20) replay1p20 := by
    convert (h2.mul hk h18).replacePolynomial (equalityCheck_sound replay1p20_checked k) using 1
    funext z
    ring
  have h22 : Approximates 24 k (fun z => f z ^ 22) replay1p22 := by
    convert (h2.mul hk h20).replacePolynomial (equalityCheck_sound replay1p22_checked k) using 1
    funext z
    ring
  have he0 := Approximates.parameter 24 k 1
  have he1 := (he0.add (h2.scale (-1 / 2 : ℚ))).replacePolynomial
    (equalityCheck_sound replay1e1_checked k)
  have he2 := (he1.add (h4.scale (-1 / 12 : ℚ))).replacePolynomial
    (equalityCheck_sound replay1e2_checked k)
  have he3 := (he2.add (h6.scale (-1 / 30 : ℚ))).replacePolynomial
    (equalityCheck_sound replay1e3_checked k)
  have he4 := (he3.add (h8.scale (-1 / 56 : ℚ))).replacePolynomial
    (equalityCheck_sound replay1e4_checked k)
  have he5 := (he4.add (h10.scale (-1 / 90 : ℚ))).replacePolynomial
    (equalityCheck_sound replay1e5_checked k)
  have he6 := (he5.add (h12.scale (-1 / 132 : ℚ))).replacePolynomial
    (equalityCheck_sound replay1e6_checked k)
  have he7 := (he6.add (h14.scale (-1 / 182 : ℚ))).replacePolynomial
    (equalityCheck_sound replay1e7_checked k)
  have he8 := (he7.add (h16.scale (-1 / 240 : ℚ))).replacePolynomial
    (equalityCheck_sound replay1e8_checked k)
  have he9 := (he8.add (h18.scale (-1 / 306 : ℚ))).replacePolynomial
    (equalityCheck_sound replay1e9_checked k)
  have he10 := (he9.add (h20.scale (-1 / 380 : ℚ))).replacePolynomial
    (equalityCheck_sound replay1e10_checked k)
  have he11 := (he10.add (h22.scale (-1 / 462 : ℚ))).replacePolynomial
    (equalityCheck_sound replay1e11_checked k)
  have hfinite : Approximates 24 k (fun z => eval k entropySeed (f z,0)) replay1e11 := by
    convert he11 using 1
    funext z
    norm_num [entropySeed, eval, evalTerm]
    <;> ring
  have he := hf.entropy_of_finite hk hklog hf0 hfinite
  exact ((Approximates.coordinateA 24 k).mul hk he).replacePolynomial
    (equalityCheck_sound replay1_final_checked k)

end GeneralCK.Reflection.SmallBiasPicardData

end


