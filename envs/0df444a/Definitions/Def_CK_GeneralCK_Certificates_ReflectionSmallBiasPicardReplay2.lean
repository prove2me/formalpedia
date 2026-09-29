-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_ReflectionSmallBiasPicardReplay2
-- name    : CK_GeneralCK_Certificates_ReflectionSmallBiasPicardReplay2
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T16:06:55.62399+00:00
-- url     : https://prove2.me/theorems/485d99c4-2792-4c78-a113-375d2771a4b3
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.ReflectionSmallBiasPicardReplay2` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.ReflectionSmallBiasPicardReplay2` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.ReflectionSmallBiasPicardReplay2` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.ReflectionSmallBiasPicardReplay2 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/ReflectionSmallBiasPicardReplay2.lean)

import Definitions.Def_CK_GeneralCK_Certificates_ReflectionSmallBiasPicardData
import Definitions.Def_CK_GeneralCK_ReflectionSmallBiasJetReplay

-- ===== source module GeneralCK.Certificates.ReflectionSmallBiasPicardReplay2 =====
section

namespace GeneralCK.Reflection.SmallBiasPicardData

open SmallBiasPolynomial SmallBiasJet

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def replay2p2 : List Term :=
  [⟨2, 0, 2, (1 / 1 : ℚ)⟩]

theorem replay2p2_checked : equalityCheck (mulTrunc 24 stage1 stage1) replay2p2 = true := by
  decide +kernel

def replay2p4 : List Term :=
  [⟨4, 0, 4, (1 / 1 : ℚ)⟩]

theorem replay2p4_checked : equalityCheck (mulTrunc 24 replay2p2 replay2p2) replay2p4 = true := by
  decide +kernel

def replay2p6 : List Term :=
  [⟨6, 0, 6, (1 / 1 : ℚ)⟩]

theorem replay2p6_checked : equalityCheck (mulTrunc 24 replay2p2 replay2p4) replay2p6 = true := by
  decide +kernel

def replay2p8 : List Term :=
  [⟨8, 0, 8, (1 / 1 : ℚ)⟩]

theorem replay2p8_checked : equalityCheck (mulTrunc 24 replay2p2 replay2p6) replay2p8 = true := by
  decide +kernel

def replay2p10 : List Term :=
  [⟨10, 0, 10, (1 / 1 : ℚ)⟩]

theorem replay2p10_checked : equalityCheck (mulTrunc 24 replay2p2 replay2p8) replay2p10 = true := by
  decide +kernel

def replay2p12 : List Term :=
  [⟨12, 0, 12, (1 / 1 : ℚ)⟩]

theorem replay2p12_checked : equalityCheck (mulTrunc 24 replay2p2 replay2p10) replay2p12 = true := by
  decide +kernel

def replay2p14 : List Term :=
  [⟨14, 0, 14, (1 / 1 : ℚ)⟩]

theorem replay2p14_checked : equalityCheck (mulTrunc 24 replay2p2 replay2p12) replay2p14 = true := by
  decide +kernel

def replay2p16 : List Term :=
  [⟨16, 0, 16, (1 / 1 : ℚ)⟩]

theorem replay2p16_checked : equalityCheck (mulTrunc 24 replay2p2 replay2p14) replay2p16 = true := by
  decide +kernel

def replay2p18 : List Term :=
  [⟨18, 0, 18, (1 / 1 : ℚ)⟩]

theorem replay2p18_checked : equalityCheck (mulTrunc 24 replay2p2 replay2p16) replay2p18 = true := by
  decide +kernel

def replay2p20 : List Term :=
  [⟨20, 0, 20, (1 / 1 : ℚ)⟩]

theorem replay2p20_checked : equalityCheck (mulTrunc 24 replay2p2 replay2p18) replay2p20 = true := by
  decide +kernel

def replay2p22 : List Term :=
  [⟨22, 0, 22, (1 / 1 : ℚ)⟩]

theorem replay2p22_checked : equalityCheck (mulTrunc 24 replay2p2 replay2p20) replay2p22 = true := by
  decide +kernel

def replay2e1 : List Term :=
  [⟨0, 0, 1, (1 / 1 : ℚ)⟩,
   ⟨2, 0, 2, (-1 / 2 : ℚ)⟩]

theorem replay2e1_checked : equalityCheck (add (parameter 1) (scale (-1 / 2 : ℚ) replay2p2)) replay2e1 = true := by
  decide +kernel

def replay2e2 : List Term :=
  [⟨0, 0, 1, (1 / 1 : ℚ)⟩,
   ⟨2, 0, 2, (-1 / 2 : ℚ)⟩,
   ⟨4, 0, 4, (-1 / 12 : ℚ)⟩]

theorem replay2e2_checked : equalityCheck (add (replay2e1) (scale (-1 / 12 : ℚ) replay2p4)) replay2e2 = true := by
  decide +kernel

def replay2e3 : List Term :=
  [⟨0, 0, 1, (1 / 1 : ℚ)⟩,
   ⟨2, 0, 2, (-1 / 2 : ℚ)⟩,
   ⟨4, 0, 4, (-1 / 12 : ℚ)⟩,
   ⟨6, 0, 6, (-1 / 30 : ℚ)⟩]

theorem replay2e3_checked : equalityCheck (add (replay2e2) (scale (-1 / 30 : ℚ) replay2p6)) replay2e3 = true := by
  decide +kernel

def replay2e4 : List Term :=
  [⟨0, 0, 1, (1 / 1 : ℚ)⟩,
   ⟨2, 0, 2, (-1 / 2 : ℚ)⟩,
   ⟨4, 0, 4, (-1 / 12 : ℚ)⟩,
   ⟨6, 0, 6, (-1 / 30 : ℚ)⟩,
   ⟨8, 0, 8, (-1 / 56 : ℚ)⟩]

theorem replay2e4_checked : equalityCheck (add (replay2e3) (scale (-1 / 56 : ℚ) replay2p8)) replay2e4 = true := by
  decide +kernel

def replay2e5 : List Term :=
  [⟨0, 0, 1, (1 / 1 : ℚ)⟩,
   ⟨2, 0, 2, (-1 / 2 : ℚ)⟩,
   ⟨4, 0, 4, (-1 / 12 : ℚ)⟩,
   ⟨6, 0, 6, (-1 / 30 : ℚ)⟩,
   ⟨8, 0, 8, (-1 / 56 : ℚ)⟩,
   ⟨10, 0, 10, (-1 / 90 : ℚ)⟩]

theorem replay2e5_checked : equalityCheck (add (replay2e4) (scale (-1 / 90 : ℚ) replay2p10)) replay2e5 = true := by
  decide +kernel

def replay2e6 : List Term :=
  [⟨0, 0, 1, (1 / 1 : ℚ)⟩,
   ⟨2, 0, 2, (-1 / 2 : ℚ)⟩,
   ⟨4, 0, 4, (-1 / 12 : ℚ)⟩,
   ⟨6, 0, 6, (-1 / 30 : ℚ)⟩,
   ⟨8, 0, 8, (-1 / 56 : ℚ)⟩,
   ⟨10, 0, 10, (-1 / 90 : ℚ)⟩,
   ⟨12, 0, 12, (-1 / 132 : ℚ)⟩]

theorem replay2e6_checked : equalityCheck (add (replay2e5) (scale (-1 / 132 : ℚ) replay2p12)) replay2e6 = true := by
  decide +kernel

def replay2e7 : List Term :=
  [⟨0, 0, 1, (1 / 1 : ℚ)⟩,
   ⟨2, 0, 2, (-1 / 2 : ℚ)⟩,
   ⟨4, 0, 4, (-1 / 12 : ℚ)⟩,
   ⟨6, 0, 6, (-1 / 30 : ℚ)⟩,
   ⟨8, 0, 8, (-1 / 56 : ℚ)⟩,
   ⟨10, 0, 10, (-1 / 90 : ℚ)⟩,
   ⟨12, 0, 12, (-1 / 132 : ℚ)⟩,
   ⟨14, 0, 14, (-1 / 182 : ℚ)⟩]

theorem replay2e7_checked : equalityCheck (add (replay2e6) (scale (-1 / 182 : ℚ) replay2p14)) replay2e7 = true := by
  decide +kernel

def replay2e8 : List Term :=
  [⟨0, 0, 1, (1 / 1 : ℚ)⟩,
   ⟨2, 0, 2, (-1 / 2 : ℚ)⟩,
   ⟨4, 0, 4, (-1 / 12 : ℚ)⟩,
   ⟨6, 0, 6, (-1 / 30 : ℚ)⟩,
   ⟨8, 0, 8, (-1 / 56 : ℚ)⟩,
   ⟨10, 0, 10, (-1 / 90 : ℚ)⟩,
   ⟨12, 0, 12, (-1 / 132 : ℚ)⟩,
   ⟨14, 0, 14, (-1 / 182 : ℚ)⟩,
   ⟨16, 0, 16, (-1 / 240 : ℚ)⟩]

theorem replay2e8_checked : equalityCheck (add (replay2e7) (scale (-1 / 240 : ℚ) replay2p16)) replay2e8 = true := by
  decide +kernel

def replay2e9 : List Term :=
  [⟨0, 0, 1, (1 / 1 : ℚ)⟩,
   ⟨2, 0, 2, (-1 / 2 : ℚ)⟩,
   ⟨4, 0, 4, (-1 / 12 : ℚ)⟩,
   ⟨6, 0, 6, (-1 / 30 : ℚ)⟩,
   ⟨8, 0, 8, (-1 / 56 : ℚ)⟩,
   ⟨10, 0, 10, (-1 / 90 : ℚ)⟩,
   ⟨12, 0, 12, (-1 / 132 : ℚ)⟩,
   ⟨14, 0, 14, (-1 / 182 : ℚ)⟩,
   ⟨16, 0, 16, (-1 / 240 : ℚ)⟩,
   ⟨18, 0, 18, (-1 / 306 : ℚ)⟩]

theorem replay2e9_checked : equalityCheck (add (replay2e8) (scale (-1 / 306 : ℚ) replay2p18)) replay2e9 = true := by
  decide +kernel

def replay2e10 : List Term :=
  [⟨0, 0, 1, (1 / 1 : ℚ)⟩,
   ⟨2, 0, 2, (-1 / 2 : ℚ)⟩,
   ⟨4, 0, 4, (-1 / 12 : ℚ)⟩,
   ⟨6, 0, 6, (-1 / 30 : ℚ)⟩,
   ⟨8, 0, 8, (-1 / 56 : ℚ)⟩,
   ⟨10, 0, 10, (-1 / 90 : ℚ)⟩,
   ⟨12, 0, 12, (-1 / 132 : ℚ)⟩,
   ⟨14, 0, 14, (-1 / 182 : ℚ)⟩,
   ⟨16, 0, 16, (-1 / 240 : ℚ)⟩,
   ⟨18, 0, 18, (-1 / 306 : ℚ)⟩,
   ⟨20, 0, 20, (-1 / 380 : ℚ)⟩]

theorem replay2e10_checked : equalityCheck (add (replay2e9) (scale (-1 / 380 : ℚ) replay2p20)) replay2e10 = true := by
  decide +kernel

def replay2e11 : List Term :=
  [⟨0, 0, 1, (1 / 1 : ℚ)⟩,
   ⟨2, 0, 2, (-1 / 2 : ℚ)⟩,
   ⟨4, 0, 4, (-1 / 12 : ℚ)⟩,
   ⟨6, 0, 6, (-1 / 30 : ℚ)⟩,
   ⟨8, 0, 8, (-1 / 56 : ℚ)⟩,
   ⟨10, 0, 10, (-1 / 90 : ℚ)⟩,
   ⟨12, 0, 12, (-1 / 132 : ℚ)⟩,
   ⟨14, 0, 14, (-1 / 182 : ℚ)⟩,
   ⟨16, 0, 16, (-1 / 240 : ℚ)⟩,
   ⟨18, 0, 18, (-1 / 306 : ℚ)⟩,
   ⟨20, 0, 20, (-1 / 380 : ℚ)⟩,
   ⟨22, 0, 22, (-1 / 462 : ℚ)⟩]

theorem replay2e11_checked : equalityCheck (add (replay2e10) (scale (-1 / 462 : ℚ) replay2p22)) replay2e11 = true := by
  decide +kernel

theorem replay2_final_checked :
    equalityCheck (mulTrunc 24 coordinateA replay2e11) stage2 = true := by
  decide +kernel

theorem stage2_replay {k : ℂ} {f : ℂ × ℂ → ℂ}
    (hk : k ≠ 0) (hklog : k = (Real.log 2 : ℂ))
    (hf : Approximates 24 k f stage1) (hf0 : f 0 = 0) :
    Approximates 24 k (fun z => z.1 * ComplexEntropy.entropyExt (f z)) stage2 := by
  have h2 : Approximates 24 k (fun z => f z ^ 2) replay2p2 := by
    convert (hf.mul hk hf).replacePolynomial (equalityCheck_sound replay2p2_checked k) using 1
    funext z
    ring
  have h4 : Approximates 24 k (fun z => f z ^ 4) replay2p4 := by
    convert (h2.mul hk h2).replacePolynomial (equalityCheck_sound replay2p4_checked k) using 1
    funext z
    ring
  have h6 : Approximates 24 k (fun z => f z ^ 6) replay2p6 := by
    convert (h2.mul hk h4).replacePolynomial (equalityCheck_sound replay2p6_checked k) using 1
    funext z
    ring
  have h8 : Approximates 24 k (fun z => f z ^ 8) replay2p8 := by
    convert (h2.mul hk h6).replacePolynomial (equalityCheck_sound replay2p8_checked k) using 1
    funext z
    ring
  have h10 : Approximates 24 k (fun z => f z ^ 10) replay2p10 := by
    convert (h2.mul hk h8).replacePolynomial (equalityCheck_sound replay2p10_checked k) using 1
    funext z
    ring
  have h12 : Approximates 24 k (fun z => f z ^ 12) replay2p12 := by
    convert (h2.mul hk h10).replacePolynomial (equalityCheck_sound replay2p12_checked k) using 1
    funext z
    ring
  have h14 : Approximates 24 k (fun z => f z ^ 14) replay2p14 := by
    convert (h2.mul hk h12).replacePolynomial (equalityCheck_sound replay2p14_checked k) using 1
    funext z
    ring
  have h16 : Approximates 24 k (fun z => f z ^ 16) replay2p16 := by
    convert (h2.mul hk h14).replacePolynomial (equalityCheck_sound replay2p16_checked k) using 1
    funext z
    ring
  have h18 : Approximates 24 k (fun z => f z ^ 18) replay2p18 := by
    convert (h2.mul hk h16).replacePolynomial (equalityCheck_sound replay2p18_checked k) using 1
    funext z
    ring
  have h20 : Approximates 24 k (fun z => f z ^ 20) replay2p20 := by
    convert (h2.mul hk h18).replacePolynomial (equalityCheck_sound replay2p20_checked k) using 1
    funext z
    ring
  have h22 : Approximates 24 k (fun z => f z ^ 22) replay2p22 := by
    convert (h2.mul hk h20).replacePolynomial (equalityCheck_sound replay2p22_checked k) using 1
    funext z
    ring
  have he0 := Approximates.parameter 24 k 1
  have he1 := (he0.add (h2.scale (-1 / 2 : ℚ))).replacePolynomial
    (equalityCheck_sound replay2e1_checked k)
  have he2 := (he1.add (h4.scale (-1 / 12 : ℚ))).replacePolynomial
    (equalityCheck_sound replay2e2_checked k)
  have he3 := (he2.add (h6.scale (-1 / 30 : ℚ))).replacePolynomial
    (equalityCheck_sound replay2e3_checked k)
  have he4 := (he3.add (h8.scale (-1 / 56 : ℚ))).replacePolynomial
    (equalityCheck_sound replay2e4_checked k)
  have he5 := (he4.add (h10.scale (-1 / 90 : ℚ))).replacePolynomial
    (equalityCheck_sound replay2e5_checked k)
  have he6 := (he5.add (h12.scale (-1 / 132 : ℚ))).replacePolynomial
    (equalityCheck_sound replay2e6_checked k)
  have he7 := (he6.add (h14.scale (-1 / 182 : ℚ))).replacePolynomial
    (equalityCheck_sound replay2e7_checked k)
  have he8 := (he7.add (h16.scale (-1 / 240 : ℚ))).replacePolynomial
    (equalityCheck_sound replay2e8_checked k)
  have he9 := (he8.add (h18.scale (-1 / 306 : ℚ))).replacePolynomial
    (equalityCheck_sound replay2e9_checked k)
  have he10 := (he9.add (h20.scale (-1 / 380 : ℚ))).replacePolynomial
    (equalityCheck_sound replay2e10_checked k)
  have he11 := (he10.add (h22.scale (-1 / 462 : ℚ))).replacePolynomial
    (equalityCheck_sound replay2e11_checked k)
  have hfinite : Approximates 24 k (fun z => eval k entropySeed (f z,0)) replay2e11 := by
    convert he11 using 1
    funext z
    norm_num [entropySeed, eval, evalTerm]
    <;> ring
  have he := hf.entropy_of_finite hk hklog hf0 hfinite
  exact ((Approximates.coordinateA 24 k).mul hk he).replacePolynomial
    (equalityCheck_sound replay2_final_checked k)

end GeneralCK.Reflection.SmallBiasPicardData

end


