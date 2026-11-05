-- Prove2me | Definitions.Def_PhysicalCostTransfer
-- name    : PhysicalCostTransfer
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T08:44:10.131245+00:00
-- url     : https://prove2.me/theorems/b648b504-f77e-4eb0-8157-4b07adf2a817
-- title:
--   PhysicalCostTransfer definitions
-- statement:
--   Conditional bounds for abstract physical state costs, assuming the stated recurrence and volume identities. These results retain their stated hypotheses and do not establish the complete fixed-tape multiplication algorithm.
--
--   [Original Lean source](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/machine-transfer-verification/transfer-proof/recurrence/PhysicalCostTransfer.lean). Imported from CrocSwap/integer-mult-bounds at `7c49fe32c55d`. Original authorship and assistance credits are retained in the upstream NOTICE and package documentation. [Attribution notice](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/NOTICE). Apache-2.0. Imported by marwahaha using lean-splitter.
-- source:
--   https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/machine-transfer-verification/transfer-proof/recurrence/PhysicalCostTransfer.lean | Apache-2.0 | CrocSwap contributors; see pinned NOTICE | lean-splitter import, independently validated on Hetzner

import Definitions.Def_SelectedFloorTransfer
set_option autoImplicit true
namespace PhysicalCostTransfer
open scoped BigOperators
noncomputable def uniformConstant (B C γ : ℝ) : ℝ := max 0 B + |C| / (1 - γ)
open SelectedProfileCertificate
noncomputable def selectedConstant (B C : ℝ) : ℝ :=
  uniformConstant B C SelectedProfileReal.powerCharacteristic
end PhysicalCostTransfer


