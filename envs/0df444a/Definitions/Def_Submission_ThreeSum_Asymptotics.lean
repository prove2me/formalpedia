-- Prove2me | Definitions.Def_Submission_ThreeSum_Asymptotics
-- name    : Submission_ThreeSum_Asymptotics
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:50:41.334205+00:00
-- url     : https://prove2.me/theorems/3025d8af-2de9-4b8c-a581-00f29ee26686
-- title:
--   Asymptotics
-- statement:
--   Shared definitions for the weighted-cache 3SUM development.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Asymptotics.lean

import Definitions.Def_Submission_ThreeSum_Parameters
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
set_option autoImplicit false
noncomputable section
namespace ThreeSum.Asymptotics
open Filter Real _root_.Asymptotics
open ThreeSum.Parameters
open scoped Topology
set_option maxRecDepth 10000
def overheadExponent (C : ℝ) (n : ℕ) : ℝ :=
  C * ((Real.log n) ^ (-(1 / 3 : ℝ)) +
    (Real.log n) ^ (-(1 / 2 : ℝ)) +
    Real.log (Real.log n) / (Real.log n) ^ (1 / 3 : ℝ) +
    (Real.log n)⁻¹)
def overheadEnvelope (C : ℝ) (n : ℕ) : ℝ := (n : ℝ) ^ overheadExponent C n
end ThreeSum.Asymptotics


