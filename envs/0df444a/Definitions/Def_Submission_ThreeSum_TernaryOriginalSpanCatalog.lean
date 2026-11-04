-- Prove2me | Definitions.Def_Submission_ThreeSum_TernaryOriginalSpanCatalog
-- name    : Submission_ThreeSum_TernaryOriginalSpanCatalog
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:11:21.118148+00:00
-- url     : https://prove2.me/theorems/a06b330a-7ae8-4e81-bcc6-d5abe8b59c37
-- title:
--   Ternary Original Span Catalog
-- statement:
--   Definitions and structural lemmas for Ternary Original Span Catalog, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryOriginalSpanCatalog.lean

import Definitions.Def_Submission_ThreeSum_TernaryOriginalSpan
set_option autoImplicit false
noncomputable section
namespace ThreeSum.TernaryOriginalSpanCatalog
open Finset
set_option maxHeartbeats 2000000
variable {p J : ℕ}
def values (p : ℕ) : List (Fin J → ZMod p) → List (Fin J → ZMod p)
  | [] => [0]
  | row::rows => (List.range p).flatMap fun a : ℕ =>
      (values p rows).map fun old => (a : ZMod p) • row+old
end ThreeSum.TernaryOriginalSpanCatalog


