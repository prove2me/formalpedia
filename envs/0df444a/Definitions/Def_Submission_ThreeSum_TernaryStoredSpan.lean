-- Prove2me | Definitions.Def_Submission_ThreeSum_TernaryStoredSpan
-- name    : Submission_ThreeSum_TernaryStoredSpan
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:46:40.989587+00:00
-- url     : https://prove2.me/theorems/d5dbca3d-1e41-41bc-91b6-519d4ef72919
-- title:
--   Ternary Stored Span
-- statement:
--   Definitions and structural lemmas for Ternary Stored Span, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryStoredSpan.lean

import Definitions.Def_Submission_ThreeSum_LightSpanCatalogTest
import Theorems.Thm_Light_Ends_next

set_option autoImplicit false
noncomputable section
namespace ThreeSum.TernaryStoredSpan
open ThreeSum
set_option maxHeartbeats 3000000
variable {p J n : ℕ}
def Represents (f : ℕ → ℕ → ℕ) (n : ℕ) (rows : List (Fin J → ZMod p)) : Prop :=
  ∀ w : Fin J → ZMod p, w∈Submodule.span (ZMod p) {v | v∈rows} ↔
    ∃ k<n, ∀ i : Fin J, (f k i.val : ZMod p)=w i
def next (f : ℕ → ℕ → ℕ) (row : ℕ → ℕ) (p n k i : ℕ) : ℕ :=
  (f (k%n) i+(k/n)*row i)%p
end ThreeSum.TernaryStoredSpan


