-- Prove2me | Definitions.Def_Submission_ThreeSum_BinomialEntropy
-- name    : Submission_ThreeSum_BinomialEntropy
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:50:40.904071+00:00
-- url     : https://prove2.me/theorems/cba3a072-c8d9-419e-87f5-e826fc78de44
-- title:
--   Binomial Entropy
-- statement:
--   Shared definitions for the weighted-cache 3SUM development.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BinomialEntropy.lean

import Definitions.Def_Submission_ThreeSum_Parameters
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Order.Monotone.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
set_option autoImplicit false
noncomputable section
namespace ThreeSum.BinomialEntropy
open Finset Real Set Filter
open scoped Topology
set_option maxRecDepth 10000
def weight (n k j : ℕ) : ℝ :=
  (n.choose j : ℝ) * (k : ℝ) ^ j * ((n - k : ℕ) : ℝ) ^ (n - j)
end ThreeSum.BinomialEntropy


