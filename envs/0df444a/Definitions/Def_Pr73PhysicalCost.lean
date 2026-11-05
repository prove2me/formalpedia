-- Prove2me | Definitions.Def_Pr73PhysicalCost
-- name    : Pr73PhysicalCost
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T08:44:10.131245+00:00
-- url     : https://prove2.me/theorems/e9c0f69b-6476-4598-aa8b-f1017eac91ed
-- title:
--   Pr73PhysicalCost definitions
-- statement:
--   The PR73 conditional physical-cost bound, under explicit implementation and recurrence hypotheses. These results retain their stated hypotheses and do not establish the complete fixed-tape multiplication algorithm.
--
--   [Original Lean source](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/machine-transfer-verification/full-transfer/latest-analytic/Pr73PhysicalCost.lean). Imported from CrocSwap/integer-mult-bounds at `7c49fe32c55d`. Original authorship and assistance credits are retained in the upstream NOTICE and package documentation. [Attribution notice](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/NOTICE). Apache-2.0. Imported by marwahaha using lean-splitter.
-- source:
--   https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/machine-transfer-verification/full-transfer/latest-analytic/Pr73PhysicalCost.lean | Apache-2.0 | CrocSwap contributors; see pinned NOTICE | lean-splitter import, independently validated on Hetzner

import Definitions.Def_PhysicalCostTransfer
import Definitions.Def_Pr73ProfileReal
set_option autoImplicit true
namespace Pr73PhysicalCost
open Pr73ProfileCertificate
open scoped BigOperators
noncomputable def costConstant (B C : ℝ) : ℝ :=
  PhysicalCostTransfer.uniformConstant B C Pr73ProfileReal.powerCharacteristic
end Pr73PhysicalCost


