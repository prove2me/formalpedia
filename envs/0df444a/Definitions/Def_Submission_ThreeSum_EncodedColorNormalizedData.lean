-- Prove2me | Definitions.Def_Submission_ThreeSum_EncodedColorNormalizedData
-- name    : Submission_ThreeSum_EncodedColorNormalizedData
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T13:24:24.328732+00:00
-- url     : https://prove2.me/theorems/d07e253d-0756-462d-b44d-784eeff60d01
-- title:
--   Encoded Color Normalized Data
-- statement:
--   Definitions and structural lemmas for Encoded Color Normalized Data, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/EncodedColorNormalizedData.lean

import Definitions.Def_Submission_ThreeSum_EncodedColorLayout
import Definitions.Def_Submission_ThreeSum_EncodedColorParameterData
import Definitions.Def_Submission_ThreeSum_EncodedColorPrimeCosts
import Theorems.Thm_ThreeSum_BandScales_bandSize_pos

set_option autoImplicit false
namespace ThreeSum.EncodedColorNormalizedData
open Light Scales BandScales ColorClassLists BandRawA EncodedColorLayout
def incidences (n : ℕ) (A B C : List ℤ) (hsA : A.Pairwise (· < ·))
    (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) : List ℤ :=
  values (fun j => A.getD j 0)
    (items A.length (bandSize n) (sortedRecords A B C (bandSize n) (bandSize_pos n) hsA hsB hsC))
def Output (μ : ℕ → ℤ) (free n : ℕ) (color : Coloring.Parameter (inputBits n+1)) (x : Fin n → ℤ) : Prop :=
  Seg μ free (normalizedHeads free n (bandSize n)) ∧
  ∃ (A : List ℤ) (hsA : A.Pairwise (· < ·)) (B : List ℤ) (hsB : B.Pairwise (· < ·))
    (C : List ℤ) (hsC : C.Pairwise (· < ·)),
    μ (normalizedEnd free n (bandSize n))=((incidences n A B C hsA hsB hsC).length : ℤ) ∧
    SourceFiniteData.Normalized μ (av free n) (ae free n) (bv free n) (be free n) (cv free n) (ce free n)
      (tables free n) (rec free n (bandSize n)) (vals free n (bandSize n)) (bandSize n) (bandSize_pos n)
      (classList color x 0 1) (classList color x 1 1) (classList color x 2 (-1))
      A B C hsA hsB hsC ((incidences n A B C hsA hsB hsC).length : ℤ)
end ThreeSum.EncodedColorNormalizedData


