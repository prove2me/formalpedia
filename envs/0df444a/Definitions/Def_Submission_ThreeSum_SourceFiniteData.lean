-- Prove2me | Definitions.Def_Submission_ThreeSum_SourceFiniteData
-- name    : Submission_ThreeSum_SourceFiniteData
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T12:48:44.568835+00:00
-- url     : https://prove2.me/theorems/de88ec49-6333-49b2-aa18-7fc35bc5c7e7
-- title:
--   Source Finite Data
-- statement:
--   Definitions and structural lemmas for Source Finite Data, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceFiniteData.lean

import Definitions.Def_Submission_ThreeSum_SourceFiniteInputs
import Definitions.Def_Submission_ThreeSum_LightSourceControlsHostProgram
set_option autoImplicit false
namespace ThreeSum.SourceFiniteData
open Light GlobalEncoding OutputDecodeRecords BandPartition BandCandidateRows BandRawA
structure Stored (μ : ℕ → ℤ) (base g p h J cut : ℕ) (B C : List ℤ) (shift r : ℤ) : Prop where
  returned : r = (LightSourceControlsHost.finish base B.length C.length g h J cut : ℤ)
  controls : Seg μ base (SourceControlLayout.values h J cut)
  buckets :
    SourceBandPairData.Stored μ (fun j => B.getD j 0) (fun j => C.getD j 0) (LightSourceControlsHost.sourceBase base)
      B.length C.length g p (BlockSourceEncoding.modulus h J) shift
  banks :
    SourceBandBankData.Stored μ (fun j => B.getD j 0) (fun j => C.getD j 0)
      (LightSourceBandHost.bankHeader (LightSourceControlsHost.sourceBase base) B.length C.length g h J) B.length
      C.length g h J cut
      (LightSourceBandHost.occurrenceBase (LightSourceControlsHost.sourceBase base) B.length C.length g h J) (p : ℤ)
      shift
def Normalized (μ : ℕ → ℤ) (av ae bv be cv ce tables rec vals g : ℕ) (hg : 0 < g)
    (originalA originalB originalC A B C : List ℤ) (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·))
    (hsC : C.Pairwise (· < ·)) (r : ℤ) : Prop :=
  let rs := sortedRecords A B C g hg hsA hsB hsC
  r = ((items A.length g rs).length : ℤ) ∧
    LightBandPreprocessing.Represents μ av ae g hg originalA A hsA ∧
      LightBandPreprocessing.Represents μ bv be g hg originalB B hsB ∧
        LightBandPreprocessing.Represents μ cv ce g hg originalC C hsC ∧
          LightBandEnumeration.Tables μ tables
              (family (fun i => A.getD i 0) A.length g hg (LightSortedBands.getD_strict hsA))
              (family (fun i => B.getD i 0) B.length g hg (LightSortedBands.getD_strict hsB))
              (family (fun i => C.getD i 0) C.length g hg (LightSortedBands.getD_strict hsC)) ∧
            Seg μ rec (cells rs) ∧
              BandRawA.Stored μ vals (LightBandRawA.ownerBase vals rs.length g)
                (LightBandRawA.positionBase vals rs.length g) (fun i => A.getD i 0) (items A.length g rs)
end ThreeSum.SourceFiniteData


