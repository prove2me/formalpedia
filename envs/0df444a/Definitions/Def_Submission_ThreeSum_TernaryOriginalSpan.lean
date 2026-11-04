-- Prove2me | Definitions.Def_Submission_ThreeSum_TernaryOriginalSpan
-- name    : Submission_ThreeSum_TernaryOriginalSpan
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:09:15.461974+00:00
-- url     : https://prove2.me/theorems/647c98b4-3cfe-4762-84bb-73ff04896890
-- title:
--   Ternary Original Span
-- statement:
--   Definitions and structural lemmas for Ternary Original Span, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryOriginalSpan.lean

import Definitions.Def_Submission_ThreeSum_TernaryOriginalRowMenu
set_option autoImplicit false
noncomputable section
namespace ThreeSum.TernaryOriginalSpan
variable {K V : Type*} [Field K] [Fintype K] [DecidableEq K]
  [AddCommGroup V] [Module K V]
def values (K : Type*) [Field K] [Fintype K] [DecidableEq K] [Module K V] : List V → List V
  | [] => [0]
  | row::rows => (Finset.univ : Finset K).toList.flatMap fun a =>
      (values K rows).map fun v => a • row+v
end ThreeSum.TernaryOriginalSpan


