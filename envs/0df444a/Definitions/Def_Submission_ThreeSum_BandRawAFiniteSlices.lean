-- Prove2me | Definitions.Def_Submission_ThreeSum_BandRawAFiniteSlices
-- name    : Submission_ThreeSum_BandRawAFiniteSlices
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T10:00:01.080121+00:00
-- url     : https://prove2.me/theorems/fce7e87d-0c04-4548-8560-a87af641c356
-- title:
--   Band Raw AFinite Slices
-- statement:
--   Definitions and structural lemmas for Band Raw AFinite Slices, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAFiniteSlices.lean

import Definitions.Def_Submission_ThreeSum_BandRawAFinite
import Theorems.Thm_ThreeSum_BandRawA_bandPositions_lt
import Theorems.Thm_ThreeSum_BandRawA_index_lt_items
import Theorems.Thm_ThreeSum_BandRawA_mem_aIndices
import Theorems.Thm_ThreeSum_BandRawA_mem_bandPositions
import Theorems.Thm_ThreeSum_BandRawA_mem_finiteAIndices
import Theorems.Thm_ThreeSum_BandRawA_mem_finiteBandPositions
attribute [local simp] ThreeSum.BandRawA.mem_finiteAIndices
attribute [local simp] ThreeSum.BandRawA.mem_finiteBandPositions


set_option autoImplicit false
namespace ThreeSum.BandRawA
open BandCandidateRows Finset
set_option maxHeartbeats 1500000
set_option maxRecDepth 7000
theorem local_band_mem {n g a j : ℕ} (hj : j < bandLength n g a) :
    BandPartition.start g a+j ∈ bandPositions n g a :=
  mem_image.mpr ⟨j,mem_range.mpr hj,rfl⟩
def finiteBandAt (n g a : ℕ) (j : Fin (bandLength n g a)) : Fin n :=
  ⟨BandPartition.start g a+j.val,bandPositions_lt (local_band_mem j.isLt)⟩
def finiteBandEquiv (n g a : ℕ) :
    Fin (bandLength n g a) ≃ {p : Fin n // p ∈ finiteBandPositions n g a} where
  toFun j := ⟨finiteBandAt n g a j,mem_finiteBandPositions.mpr (local_band_mem j.isLt)⟩
  invFun p := ⟨p.val.val-BandPartition.start g a,by
    have hp := mem_bandPositions.mp (mem_finiteBandPositions.mp p.property)
    unfold bandLength
    omega⟩
  left_inv j := by
    apply Fin.ext
    change BandPartition.start g a+j.val-BandPartition.start g a=j.val
    omega
  right_inv p := by
    apply Subtype.ext
    apply Fin.ext
    change BandPartition.start g a+(p.val.val-BandPartition.start g a)=p.val.val
    have hp := mem_bandPositions.mp (mem_finiteBandPositions.mp p.property)
    omega
def finiteAAt (n g : ℕ) (rs : List Record) (s : ℕ) (hs : s < rs.length)
    (j : Fin (row n g s (rs.getD s default)).length) : Fin (items n g rs).length :=
  ⟨count n g rs s+j.val,index_lt_items hs j.isLt⟩
def finiteAEquiv (n g : ℕ) (rs : List Record) (s : ℕ) (hs : s < rs.length) :
    Fin (row n g s (rs.getD s default)).length ≃
      {p : Fin (items n g rs).length // p ∈ finiteAIndices n g rs s} where
  toFun j := ⟨finiteAAt n g rs s hs j,
    mem_finiteAIndices.mpr (mem_aIndices.mpr ⟨j.val,j.isLt,rfl⟩)⟩
  invFun p := ⟨p.val.val-count n g rs s,by
    obtain ⟨j,hj,he⟩ := mem_aIndices.mp (mem_finiteAIndices.mp p.property)
    omega⟩
  left_inv j := by
    apply Fin.ext
    change count n g rs s+j.val-count n g rs s=j.val
    omega
  right_inv p := by
    apply Subtype.ext
    apply Fin.ext
    change count n g rs s+(p.val.val-count n g rs s)=p.val.val
    obtain ⟨j,hj,he⟩ := mem_aIndices.mp (mem_finiteAIndices.mp p.property)
    omega
end ThreeSum.BandRawA


