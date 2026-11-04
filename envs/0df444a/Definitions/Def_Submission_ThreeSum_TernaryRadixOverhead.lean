-- Prove2me | Definitions.Def_Submission_ThreeSum_TernaryRadixOverhead
-- name    : Submission_ThreeSum_TernaryRadixOverhead
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:45:35.803205+00:00
-- url     : https://prove2.me/theorems/e13e17be-872b-4122-8c52-5fdaea283f24
-- title:
--   Ternary Radix Overhead
-- statement:
--   Definitions and structural lemmas for Ternary Radix Overhead, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryRadixOverhead.lean

import Definitions.Def_Submission_ThreeSum_TernaryPrincipalDimensions
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
set_option autoImplicit false
noncomputable section
namespace ThreeSum.TernaryRadixOverhead
open Filter Real Asymptotics TernaryCoverScale TernaryPrincipalDimensions
open scoped Topology
end ThreeSum.TernaryRadixOverhead


