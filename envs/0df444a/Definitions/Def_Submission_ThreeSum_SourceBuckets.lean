-- Prove2me | Definitions.Def_Submission_ThreeSum_SourceBuckets
-- name    : Submission_ThreeSum_SourceBuckets
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:24:08.210655+00:00
-- url     : https://prove2.me/theorems/b5148e91-be47-4416-9437-1cc3329c31b0
-- title:
--   Source Buckets
-- statement:
--   Definitions and structural lemmas for Source Buckets, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBuckets.lean

import Definitions.Def_Submission_ThreeSum_LightHistogram
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.OfFn
set_option autoImplicit false
namespace ThreeSum.SourceBuckets
open Finset LightHistogram
set_option maxHeartbeats 1400000
set_option maxRecDepth 10000
def offset (key : ℕ → ℕ) (N r : ℕ) : ℕ := ∑ s ∈ range r, count key s N
def position (key : ℕ → ℕ) (N i : ℕ) : ℕ := offset key N (key i)+count key (key i) i
structure Stored (μ : ℕ → ℤ) (key : ℕ → ℕ) (N M offsets flat : ℕ) : Prop where
  offsets : ∀ r ≤ M, μ (offsets+r) = (offset key N r : ℤ)
  indices : ∀ i < N, μ (flat+position key N i) = (i : ℤ)
def bucketList (μ : ℕ → ℤ) (flat start length : ℕ) : List ℕ :=
  List.ofFn (fun t : Fin length => (μ (flat+start+t.val)).toNat)
end ThreeSum.SourceBuckets


