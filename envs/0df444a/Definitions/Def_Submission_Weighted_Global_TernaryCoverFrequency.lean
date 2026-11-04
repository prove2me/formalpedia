-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryCoverFrequency
-- name    : Submission_Weighted_Global_TernaryCoverFrequency
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:24:58.567961+00:00
-- url     : https://prove2.me/theorems/9321f552-9a84-44d7-93d2-c77a924cdd28
-- title:
--   Ternary Cover Frequency
-- statement:
--   Definitions and structural lemmas for Ternary Cover Frequency, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryCoverFrequency.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryCoverGoodMaps
import Definitions.Def_Submission_ThreeSum_Greedy
import Definitions.Def_Submission_Weighted_Global_TernaryPartitionCount
set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalCoverFrequency
open Finset TernaryJointType TernaryCoverLocal WeightedGlobalLocalParameters
open WeightedGlobalCoverGoodMaps
open scoped BigOperators
variable (m p : ℕ) [Fact p.Prime]
def Covers (B τ : ℕ) (w : Weight m p) (t : ZMod p × ZMod p) : Prop :=
  prunedHit m p B τ w t.1 t.2 ≠ 0
instance (B τ : ℕ) : DecidableRel (Covers m p B τ) := fun _ _ => inferInstanceAs (Decidable (_ ≠ (0 : ℕ)))
def frequencyFactor (m : ℕ) : ℕ :=
  4*3^16*(16*WeightedGlobalPartitionCount.partitionLoss (2380004124000*m) (292746547000*m))^2
end ThreeSum.WeightedGlobalCoverFrequency


