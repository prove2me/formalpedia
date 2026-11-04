-- Prove2me | Definitions.Def_Submission_ThreeSum_TernaryPairedTensorScaled
-- name    : Submission_ThreeSum_TernaryPairedTensorScaled
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:53:22.239194+00:00
-- url     : https://prove2.me/theorems/44811746-dbcf-4ec2-9d7a-bd4b7a61bdea
-- title:
--   Ternary Paired Tensor Scaled
-- statement:
--   Definitions and structural lemmas for Ternary Paired Tensor Scaled, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPairedTensorScaled.lean

import Definitions.Def_Submission_ThreeSum_LightTernaryPairedPotentialBatch
set_option autoImplicit false
noncomputable section
namespace ThreeSum.TernaryPairedTensorScaled
open LightTernaryPairedPolynomial LightTernaryPairedPotential
open TernaryPairedTensor TernaryPairedColumnEnumeration
open scoped BigOperators
end ThreeSum.TernaryPairedTensorScaled


