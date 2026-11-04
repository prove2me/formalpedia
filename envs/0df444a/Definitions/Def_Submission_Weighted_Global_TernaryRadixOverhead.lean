-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryRadixOverhead
-- name    : Submission_Weighted_Global_TernaryRadixOverhead
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T12:55:45.148777+00:00
-- url     : https://prove2.me/theorems/f645cdcb-a942-46e3-ac54-5fd50d8c2118
-- title:
--   Ternary Radix Overhead
-- statement:
--   Definitions and structural lemmas for Ternary Radix Overhead, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryRadixOverhead.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryPrincipalDimensions
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalRadixOverhead
open Filter Real Asymptotics WeightedGlobalCoverScale WeightedGlobalPrincipalDimensions
open scoped Topology
end ThreeSum.WeightedGlobalRadixOverhead


