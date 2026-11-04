-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryMomentReporterBudget
-- name    : Submission_Weighted_Global_TernaryMomentReporterBudget
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T15:20:50.527206+00:00
-- url     : https://prove2.me/theorems/52cc5a6d-eac9-480a-a851-ad89355cc4f1
-- title:
--   Ternary Moment Reporter Budget
-- statement:
--   Definitions and structural lemmas for Ternary Moment Reporter Budget, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryMomentReporterBudget.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryMomentReporter
set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalMomentReporterBudget
open Light TernaryMomentSchedule TernaryWeightChannels
def circuitCost (c : ℕ×ℕ) : ℕ :=
  ((leftMoment c.1 c.2).compile LightTernaryScalarChannel.atoms).cost+
  ((rightMoment c.1 c.2).compile LightTernaryScalarChannel.atoms).cost+1000
def weightBudget (terms : ℕ) : ℕ :=
  (channels terms).foldr (fun c n => max (circuitCost c) n) 1000
def base {N : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N) : ℕ :=
  S.left.NL+S.right.NL+S.front.count+S.runtime+1
def driverConstant (terms : ℕ) : ℕ :=
  terms^2*(weightBudget terms+117)+13*terms+106
def reporterConstant (H : ℕ) : ℕ :=
  driverConstant (2*H+1)+LightTernaryMomentRow.time H+500
end ThreeSum.WeightedGlobalMomentReporterBudget


