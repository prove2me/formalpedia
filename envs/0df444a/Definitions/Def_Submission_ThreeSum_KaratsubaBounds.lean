-- Prove2me | Definitions.Def_Submission_ThreeSum_KaratsubaBounds
-- name    : Submission_ThreeSum_KaratsubaBounds
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:09:32.485634+00:00
-- url     : https://prove2.me/theorems/7e5a545a-ffef-40c2-8d9c-5a063669951b
-- title:
--   Karatsuba Bounds
-- statement:
--   Definitions and structural lemmas for Karatsuba Bounds, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/KaratsubaBounds.lean

import Definitions.Def_Submission_ThreeSum_Karatsuba
import Mathlib.Data.List.GetD
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
set_option autoImplicit false
namespace ThreeSum.Karatsuba
open Polynomial
open scoped BigOperators
def CoeffBound (as : List ℤ) (U : ℤ) : Prop := ∀ j, |as.getD j 0| ≤ U
end ThreeSum.Karatsuba


