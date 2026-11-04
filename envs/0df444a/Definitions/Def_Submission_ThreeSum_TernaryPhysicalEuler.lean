-- Prove2me | Definitions.Def_Submission_ThreeSum_TernaryPhysicalEuler
-- name    : Submission_ThreeSum_TernaryPhysicalEuler
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:53:53.140918+00:00
-- url     : https://prove2.me/theorems/b361d390-c461-4258-b978-37901b0321b5
-- title:
--   Ternary Physical Euler
-- statement:
--   Definitions and structural lemmas for Ternary Physical Euler, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPhysicalEuler.lean

import Definitions.Def_Submission_ThreeSum_LightTernaryEulerMetadata
import Definitions.Def_Submission_ThreeSum_LightTernaryEulerMemo
import Definitions.Def_Submission_ThreeSum_TernaryPartialEuler
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_high
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_low

set_option autoImplicit false
noncomputable section
namespace ThreeSum.TernaryPhysicalEuler
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryEuler
open ThreeSum.TernaryCodeSemantics
set_option maxHeartbeats 3000000
def ordinal {N : ℕ} (words : ℕ → TritWord N) (n : ℕ) (w : TritWord N) : ℕ :=
  if h : ∃ j<n, words j=w then h.choose else 0
def physicalWord {N : ℕ} (bankWords nearWords : ℕ → TritWord N) (bv nv x : ℕ) : TritWord N :=
  if x<nv then bankWords (x-bv) else nearWords (x-nv)
def physicalValue {N : ℕ} (F : TritWord N → ℤ) (bankWords nearWords : ℕ → TritWord N)
    (bv nv x : ℕ) : ℤ := F (physicalWord bankWords nearWords bv nv x)
def rowWeight {N : ℕ} (R : TritWord N) (i : ℕ) : ℕ :=
  LightTernaryPredecessor.weight N (LightTernaryEulerMetadata.lowAt N i)
    (LightTernaryEulerMetadata.highAt N i) (address R) 1
def rowKey {N : ℕ} (R : TritWord N) (bankWords nearWords : ℕ → TritWord N)
    (nb nn T bv nv i : ℕ) : ℕ :=
  let low := LightTernaryEulerMetadata.lowAt N i
  let high := LightTernaryEulerMetadata.highAt N i
  let pred := if hi : i<N then predecessor R ⟨i,hi⟩ else R
  LightTernaryPredecessor.key N low high (address R) T 1 bv nv
    (ordinal bankWords nb pred) (ordinal nearWords nn pred)
def predecessorOrdinal {N : ℕ} (words : ℕ → TritWord N) (n : ℕ)
    (R : TritWord N) (i : ℕ) : ℕ :=
  ordinal words n (if hi : i<N then predecessor R ⟨i,hi⟩ else R)
end ThreeSum.TernaryPhysicalEuler


