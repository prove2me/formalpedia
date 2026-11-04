-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryCoverActualMoment
-- name    : Submission_Weighted_Global_TernaryCoverActualMoment
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:12:45.622599+00:00
-- url     : https://prove2.me/theorems/6e1e1bf4-d273-4402-b684-f48e7cccd258
-- title:
--   Ternary Cover Actual Moment
-- statement:
--   Definitions and structural lemmas for Ternary Cover Actual Moment, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryCoverActualMoment.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_ThreeSum_TernaryCoverHighMoment
import Definitions.Def_Submission_Weighted_GlobalLocalParameters
set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalCoverActualMoment
open Finset TernaryJointType TernaryCoverLocal TernaryCoverHashes
open TernaryCoverHighMoment TernaryCoverRankFibers WeightedGlobalLocalParameters
open TernaryCoverOutputCap
open scoped BigOperators
def taggedLeft {L : ℕ} {α π : DigitType} (e : LocalEdge L α π) : Coordinate (Fin L) → Fin 3 :=
  Sum.elim (left e) (fun b => if b then 0 else 1)
def taggedRight {L : ℕ} {α π : DigitType} (e : LocalEdge L α π) : Coordinate (Fin L) → Fin 3 :=
  Sum.elim (right e) (fun b => if b then 1 else 0)
end ThreeSum.WeightedGlobalCoverActualMoment


