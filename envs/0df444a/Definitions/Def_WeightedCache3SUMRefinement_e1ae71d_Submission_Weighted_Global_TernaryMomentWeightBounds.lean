-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryMomentWeightBounds
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryMomentWeightBounds
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T12:20:47.713135+00:00
-- url     : https://prove2.me/theorems/3efa3348-ed7f-4151-b479-d12e1d73e16a
-- title:
--   TernaryMomentWeightBounds
-- statement:
--   Definitions and structural lemmas for TernaryMomentWeightBounds, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryMomentWeightBounds.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryNativeMomentBounds
import Mathlib.Data.Nat.Choose.Bounds
set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
namespace ThreeSum.WeightedGlobalMomentWeightBounds
open LightWeightedGlobalMomentChannelFactory
def leftBound (U K : ℕ) : ℕ :=2^K*(U+1)^K
def rightBound (U K : ℕ) : ℕ :=(U+1)^K
def leftWord (U K : ℕ) : ℕ :=U+2*(2^K+1)*(U+2)^K
def rightWord (U K : ℕ) : ℕ :=U+2*(U+1)^K
end ThreeSum.WeightedGlobalMomentWeightBounds
end WeightedCache3SUMRefinement_e1ae71d


