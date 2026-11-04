-- Prove2me | Definitions.Def_Submission_ThreeSum_TernaryPairedSelector
-- name    : Submission_ThreeSum_TernaryPairedSelector
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:51:54.261784+00:00
-- url     : https://prove2.me/theorems/7d33dbba-44da-4a7e-a036-7b36235a436c
-- title:
--   Ternary Paired Selector
-- statement:
--   Shared definitions for the weighted-cache 3SUM development.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPairedSelector.lean

import Mathlib.Tactic
set_option autoImplicit false
namespace ThreeSum.TernaryPairedSelector
open Finset
open scoped BigOperators
variable {Ω : Type*} [DecidableEq Ω]
def score (f : Fin 3 → Ω → ℚ) (normalizer : Fin 3 → ℚ) (seed : Ω) : ℚ :=
  ∑ i, if normalizer i = 0 then 0 else f i seed / normalizer i
end ThreeSum.TernaryPairedSelector


