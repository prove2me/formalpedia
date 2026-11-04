-- Prove2me | Definitions.Def_Submission_ThreeSum_Reporting
-- name    : Submission_ThreeSum_Reporting
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:17:41.822692+00:00
-- url     : https://prove2.me/theorems/203b7a68-19a1-446f-be48-1fb431a37c59
-- title:
--   Reporting
-- statement:
--   Definitions and structural lemmas for Reporting, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Reporting.lean

import Definitions.Def_Submission_ThreeSum_Subset
import Mathlib.Data.List.Nodup
import Mathlib.Data.Finset.Card
set_option autoImplicit false
namespace ThreeSum.Reporting
open Finset
open scoped BigOperators
variable {ι α : Type*} [DecidableEq α]
def mass (I : Finset ι) (word : ι → List α) (weight : ι → ℕ)
    (k : ℕ) (pre : List α) : ℕ :=
  Subset.fiberMass I (fun i => (word i).take k) weight pre
def frontier (children : ℕ → List α) (query : ℕ → List α → ℕ) : ℕ → List (List α)
  | 0 => if 0 < query 0 [] then [[]] else []
  | k + 1 =>
      ((frontier children query k).flatMap fun pre =>
        (children k).map fun x => pre ++ [x]).filter fun pre => 0 < query (k + 1) pre
end ThreeSum.Reporting


