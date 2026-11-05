-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryMomentReporterBudget
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryMomentReporterBudget
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T12:32:10.667507+00:00
-- url     : https://prove2.me/theorems/5fff8723-88a8-40b9-a4f9-fdb5313f5df1
-- title:
--   TernaryMomentReporterBudget
-- statement:
--   Definitions and structural lemmas for TernaryMomentReporterBudget, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryMomentReporterBudget.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryMomentReporter
set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
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
end
end WeightedCache3SUMRefinement_e1ae71d


