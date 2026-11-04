-- Prove2me | Definitions.Def_Submission_ThreeSum_TernaryPhysicalTensorChannels
-- name    : Submission_ThreeSum_TernaryPhysicalTensorChannels
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:41:26.26813+00:00
-- url     : https://prove2.me/theorems/2253db73-f451-4270-83de-4b055a2c54d2
-- title:
--   Ternary Physical Tensor Channels
-- statement:
--   Definitions and structural lemmas for Ternary Physical Tensor Channels, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPhysicalTensorChannels.lean

import Definitions.Def_Submission_ThreeSum_TernaryWeightChannels
import Definitions.Def_Submission_ThreeSum_TernaryPairedTensor
set_option autoImplicit false
noncomputable section
namespace ThreeSum.TernaryPhysicalTensorChannels
open Finset TernaryJointType TernaryWeightedPhysicalSources TernaryWeightChannels
open scoped BigOperators
variable {ι κ I : Type*}
def records {N : ℕ} (S : Finset ι) (T : Finset κ)
    (left : ι→TritWord N) (right : κ→TritWord N) (Q : TritWord N) : Finset (ι×κ) := by
  classical
  exact (S×ˢT).filter fun x => TernaryConvolution.Adds (left x.1) (right x.2) Q
end ThreeSum.TernaryPhysicalTensorChannels


