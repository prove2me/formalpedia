-- Prove2me | Definitions.Def_Submission_ThreeSum_SourceFlagProduct
-- name    : Submission_ThreeSum_SourceFlagProduct
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:53:00.201191+00:00
-- url     : https://prove2.me/theorems/9c282e89-b932-486a-aab0-9d19ad2340dd
-- title:
--   Source Flag Product
-- statement:
--   Shared definitions for the weighted-cache 3SUM development.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceFlagProduct.lean

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Tactic
set_option autoImplicit false
namespace ThreeSum.SourceFlagProduct
open Finset
open scoped BigOperators
def product (flag : ℕ → ℕ) (n : ℕ) : ℕ := ∏ i ∈ range n, flag i
end ThreeSum.SourceFlagProduct


