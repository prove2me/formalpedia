-- Prove2me | Definitions.Def_Submission_ThreeSum_EncodedColorPrimeReadyData
-- name    : Submission_ThreeSum_EncodedColorPrimeReadyData
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T13:34:12.620336+00:00
-- url     : https://prove2.me/theorems/7b577e6d-8ff4-4d9e-9453-ed839a7b2007
-- title:
--   Encoded Color Prime Ready Data
-- statement:
--   Definitions and structural lemmas for Encoded Color Prime Ready Data, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/EncodedColorPrimeReadyData.lean

import Definitions.Def_Submission_ThreeSum_EncodedColorNormalizedData
import Theorems.Thm_ThreeSum_BandScales_bandSize_pos

set_option autoImplicit false
namespace ThreeSum.EncodedColorPrimeReadyData
open Light Scales BandScales ColorClassLists EncodedColorLayout EncodedColorNormalizedData
def moduli (n : ℕ) (A B C : List ℤ) (hsA : A.Pairwise (· < ·))
    (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) : ℕ → ℕ :=
  LightEncodedColorPrime.moduli A B C (bandSize n) (bandSize_pos n) hsA hsB hsC (primeWindow n)
def selected (n : ℕ) (A B C : List ℤ) (hsA : A.Pairwise (· < ·))
    (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) : ℕ :=
  moduli n A B C hsA hsB hsC (LightBandPrimeDepth.depth (radix n) (primeWindow n))
def Output (μ : ℕ → ℤ) (free n : ℕ) (color : Coloring.Parameter (inputBits n+1)) (x : Fin n → ℤ) : Prop :=
  Seg μ free (normalizedHeads free n (bandSize n)) ∧
  ∃ (A : List ℤ) (hsA : A.Pairwise (· < ·)) (B : List ℤ) (hsB : B.Pairwise (· < ·))
    (C : List ℤ) (hsC : C.Pairwise (· < ·)),
    μ (normalizedEnd free n (bandSize n))=((incidences n A B C hsA hsB hsC).length : ℤ) ∧
    SourceFiniteData.Normalized μ (av free n) (ae free n) (bv free n) (be free n) (cv free n) (ce free n)
      (tables free n) (rec free n (bandSize n)) (vals free n (bandSize n)) (bandSize n) (bandSize_pos n)
      (classList color x 0 1) (classList color x 1 1) (classList color x 2 (-1))
      A B C hsA hsB hsC ((incidences n A B C hsA hsB hsC).length : ℤ) ∧
    EncodedColorPrimeData.Stored μ (prime free n (bandSize n)) (radix n) (primeWindow n)
      (moduli n A B C hsA hsB hsC)
end ThreeSum.EncodedColorPrimeReadyData


