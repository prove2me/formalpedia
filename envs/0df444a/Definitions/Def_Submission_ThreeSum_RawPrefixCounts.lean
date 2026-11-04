-- Prove2me | Definitions.Def_Submission_ThreeSum_RawPrefixCounts
-- name    : Submission_ThreeSum_RawPrefixCounts
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:18:39.565756+00:00
-- url     : https://prove2.me/theorems/481bc697-479f-484e-9de5-c886bbf1ccf1
-- title:
--   Raw Prefix Counts
-- statement:
--   Definitions and structural lemmas for Raw Prefix Counts, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/RawPrefixCounts.lean

import Definitions.Def_Submission_ThreeSum_RawReporting
set_option autoImplicit false
namespace ThreeSum.RawPrefixCounts
set_option maxRecDepth 8000
open Finset
open scoped BigOperators
open GlobalEncoding RawIncidences RawReporting
section Indices
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
def prefixItems {h J : ℕ} (I : Finset (RawItem h J α β γ)) (w : Wanted h J α)
    (k : ℕ) (pre : List (Finset (Fin (512 * h)))) :=
  (domain I w).filter fun r => (word r).take k = pre
def compatiblePairs {h J : ℕ} (P d : ℤ) (B : Finset β) (C : Finset γ)
    (b : β → ℤ) (c : γ → ℤ) (t : ChoiceTuple h J) :=
  (B ×ˢ C).filter fun p => globalModulus h J ∣ b p.1 % P - tupleLeft t ∧
    globalModulus h J ∣ c p.2 % P + d - tupleRight t
def completions {h J : ℕ} (q : GlobalOutput h J) (k : ℕ)
    (pre : List (Finset (Fin (512 * h)))) : Finset (ChoiceTuple h J) :=
  Finset.univ.filter fun t => tupleOutput t = q ∧ (partitionWord t).take k = pre
def pack {h J : ℕ} (w : Wanted h J α)
    (s : Σ _t : ChoiceTuple h J, β × γ) : RawItem h J α β γ :=
  ⟨(w.1, s.2), (s.1, w.2.1)⟩
def bucketPrefixMass {h J : ℕ} (P d : ℤ)
    (A : Finset α) (B : Finset β) (C : Finset γ)
    (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ) (w : Wanted h J α)
    (k : ℕ) (pre : List (Finset (Fin (512 * h)))) : ℕ :=
  if w.1 ∈ A ∧ globalModulus h J ∣
      (a w.1 % P + lift w.2.1 * P + d) - globalKey w.2.2 then
    ∑ t ∈ completions w.2.2 k pre, leftBucket P B b t * rightBucket P d C c t
  else 0
end Indices
end ThreeSum.RawPrefixCounts


