-- Prove2me | Definitions.Def_Submission_ThreeSum_StoredReporting
-- name    : Submission_ThreeSum_StoredReporting
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:28:28.486634+00:00
-- url     : https://prove2.me/theorems/e75f88e0-2d47-433b-a46a-5c95059a31d3
-- title:
--   Stored Reporting
-- statement:
--   Definitions and structural lemmas for Stored Reporting, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/StoredReporting.lean

import Definitions.Def_Submission_ThreeSum_BlockForced
set_option autoImplicit false
namespace ThreeSum.StoredReporting
set_option maxRecDepth 8000
open Finset
open scoped BigOperators
open GlobalEncoding LocalGraph LocalCoverBounds RawIncidences RawReporting RawPrefixCounts
open BlockRows BlockEncoding BlockForced
def prefixRows {J L : ℕ} (pre : List (Finset (Fin L))) : Fin J → Finset (Fin L) :=
  fun i => pre[i.val]?.getD ∅
def ValidPrefix {h J : ℕ} (q : GlobalOutput h J) (k : ℕ)
    (pre : List (Finset (Fin (512 * h)))) : Prop :=
  pre.length = k ∧ ∀ i : Fin J, i.val < k →
    prefixRows pre i ⊆ outputRows q i ∧ (prefixRows pre i).card = h
instance {h J : ℕ} (q : GlobalOutput h J) (k : ℕ)
    (pre : List (Finset (Fin (512 * h)))) : Decidable (ValidPrefix q k pre) := by
  unfold ValidPrefix
  infer_instance
section Indices
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
def storedQueryValue {h J : ℕ} (P d : ℤ)
    (A : Finset α) (B : Finset β) (C : Finset γ)
    (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ) (w : Wanted h J α)
    (k : ℕ) (pre : List (Finset (Fin (512 * h)))) : ℤ :=
  if ValidPrefix w.2.2 k pre then
    if w.1 ∈ A ∧ globalModulus h J ∣
        (a w.1 % P + lift w.2.1 * P + d) - globalKey w.2.2 then
      transformPrefixValue P d B C b c w.2.2 (prefixIndices J k) (prefixRows pre)
    else 0
  else 0
def storedQuery {h J : ℕ} (P d : ℤ)
    (A : Finset α) (B : Finset β) (C : Finset γ)
    (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ) (w : Wanted h J α)
    (k : ℕ) (pre : List (Finset (Fin (512 * h)))) : ℕ :=
  (storedQueryValue P d A B C a b c w k pre).toNat
def storedFrontier {h J : ℕ} (P d : ℤ)
    (A : Finset α) (B : Finset β) (C : Finset γ)
    (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ) (w : Wanted h J α) (k : ℕ) :=
  Reporting.frontier (children w.2.2) (storedQuery P d A B C a b c w) k
end Indices
end ThreeSum.StoredReporting


