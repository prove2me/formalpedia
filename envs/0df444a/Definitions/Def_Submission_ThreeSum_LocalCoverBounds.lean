-- Prove2me | Definitions.Def_Submission_ThreeSum_LocalCoverBounds
-- name    : Submission_ThreeSum_LocalCoverBounds
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:09:22.787429+00:00
-- url     : https://prove2.me/theorems/1d44c26a-dc13-4b7a-8cbe-44c16398bd82
-- title:
--   Local Cover Bounds
-- statement:
--   Definitions and structural lemmas for Local Cover Bounds, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalCoverBounds.lean

import Definitions.Def_Submission_ThreeSum_LayerCounts
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Nat.Sqrt
import Mathlib.NumberTheory.Bertrand
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices


set_option autoImplicit false
namespace ThreeSum.LocalCoverBounds
open scoped BigOperators
def outputCount (L h : ℕ) : ℕ := L.choose (2 * h)
def vertexCount (L h : ℕ) : ℕ := L.choose h
def degree (L h : ℕ) : ℕ := (L - h).choose h
def groupSize (h : ℕ) : ℕ := (2 * h).choose h
noncomputable def mean (L h p : ℕ) : ℝ :=
  (outputCount L h : ℝ) * groupSize h / (p : ℝ) ^ 2
def rootCeiling (N : ℕ) : ℕ := Nat.sqrt (N - 1) + 1
theorem rootCeiling_pos (N : ℕ) : 0 < rootCeiling N := by
  unfold rootCeiling
  omega
def primeCandidates (N : ℕ) : Finset ℕ :=
  (Finset.range (2 * rootCeiling N + 1)).filter
    (fun p => Nat.Prime p ∧ rootCeiling N < p)
theorem mem_primeCandidates {N p : ℕ} :
    p ∈ primeCandidates N ↔ Nat.Prime p ∧ rootCeiling N < p ∧ p ≤ 2 * rootCeiling N := by
  simp only [primeCandidates, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hup, hp, hlo⟩
    exact ⟨hp, hlo, by omega⟩
  · rintro ⟨hp, hlo, hup⟩
    exact ⟨by omega, hp, hlo⟩
theorem primeCandidates_nonempty (N : ℕ) : (primeCandidates N).Nonempty := by
  obtain ⟨p, hp, hlo, hup⟩ :=
    Nat.exists_prime_lt_and_le_two_mul (rootCeiling N) (rootCeiling_pos N).ne'
  exact ⟨p, mem_primeCandidates.mpr ⟨hp, hlo, hup⟩⟩
def selectedPrime (N : ℕ) : ℕ :=
  (primeCandidates N).min' (primeCandidates_nonempty N)
def bucketCap (V p : ℕ) : ℕ := (4 * (p + V)) ⌈/⌉ p
def localThreshold (h : ℕ) : ℕ := outputCount (512 * h) h * 2 ^ (2 * h)
def localPrime (h : ℕ) : ℕ := selectedPrime (localThreshold h)
def localBucketCap (h : ℕ) : ℕ := bucketCap (vertexCount (512 * h) h) (localPrime h)
end ThreeSum.LocalCoverBounds


