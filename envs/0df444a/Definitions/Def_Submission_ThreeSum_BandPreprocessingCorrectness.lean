-- Prove2me | Definitions.Def_Submission_ThreeSum_BandPreprocessingCorrectness
-- name    : Submission_ThreeSum_BandPreprocessingCorrectness
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:45:07.76883+00:00
-- url     : https://prove2.me/theorems/382c6d96-aabf-4df9-8917-406ac8c4b249
-- title:
--   Band Preprocessing Correctness
-- statement:
--   Definitions and structural lemmas for Band Preprocessing Correctness, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandPreprocessingCorrectness.lean

import Definitions.Def_Submission_ThreeSum_LightBandPreprocessing
set_option autoImplicit false
namespace ThreeSum.LightBandPreprocessing
open Light ThreeSum.BandPartition
def storedCount (μ : ℕ → ℤ) (header : ℕ) : ℕ := (μ (header+1)).toNat
def InBand (μ : ℕ → ℤ) (header i : ℕ) (z : ℤ) : Prop :=
  μ (header+2+i) ≤ z ∧ z ≤ μ (header+2+(μ header).toNat+i)
def Candidate (μ : ℕ → ℤ) (ae be ce dst i j k : ℕ) : Prop :=
  i < storedCount μ ae ∧ j < storedCount μ be ∧ k < storedCount μ ce ∧
    (μ (dst+j*storedCount μ ce+k) = (i+1 : ℕ) ∨
      μ (dst+storedCount μ be*storedCount μ ce+i*storedCount μ be+j) = (k+1 : ℕ) ∨
      μ (dst+storedCount μ be*storedCount μ ce+storedCount μ ae*storedCount μ be+
        i*storedCount μ ce+k) = (j+1 : ℕ))
end ThreeSum.LightBandPreprocessing


