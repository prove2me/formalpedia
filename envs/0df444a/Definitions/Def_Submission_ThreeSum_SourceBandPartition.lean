-- Prove2me | Definitions.Def_Submission_ThreeSum_SourceBandPartition
-- name    : Submission_ThreeSum_SourceBandPartition
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:40:26.663171+00:00
-- url     : https://prove2.me/theorems/5b474c0e-c8de-4b55-a7bf-f8e027a6fd27
-- title:
--   Source Band Partition
-- statement:
--   Definitions and structural lemmas for Source Band Partition, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandPartition.lean

import Definitions.Def_Submission_ThreeSum_SourceBandLayout
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_LightHistogram_count_zero
import Theorems.Thm_ThreeSum_SourceBuckets_offset_zero
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.LightHistogram.count_zero
attribute [local simp] ThreeSum.SourceBuckets.offset_zero


set_option autoImplicit false
namespace ThreeSum.SourceBandPartition
open BandPartition SourceBandLayout
def source (n g i : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun t => start g i ≤ t.val ∧ t.val < stop n g i)
theorem mem_source {n g i : ℕ} {t : Fin n} :
    t ∈ source n g i ↔ start g i ≤ t.val ∧ t.val < stop n g i := by
  simp only [source,Finset.mem_filter,Finset.mem_univ,true_and]
theorem physical_lt {n g i j : ℕ} (hj : j < len n g i) : start g i+j < n := by
  have hs := stop_le n g i
  unfold len at hj
  omega
def equiv (n g i : ℕ) : Fin (len n g i) ≃ source n g i where
  toFun j := ⟨⟨start g i+j.val,physical_lt j.isLt⟩,mem_source.mpr
    ⟨by change start g i ≤ start g i+j.val; omega,
      by change start g i+j.val < stop n g i
         have hj := j.isLt
         unfold len at hj
         omega⟩⟩
  invFun t := ⟨t.val.val-start g i,by
    obtain ⟨hlo,hhi⟩ := mem_source.mp t.property
    unfold len
    omega⟩
  left_inv j := by
    apply Fin.ext
    simp only
    omega
  right_inv t := by
    apply Subtype.ext
    apply Fin.ext
    obtain ⟨hlo,hhi⟩ := mem_source.mp t.property
    simp only
    omega
end ThreeSum.SourceBandPartition


