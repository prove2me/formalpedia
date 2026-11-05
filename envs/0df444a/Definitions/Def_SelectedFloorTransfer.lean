-- Prove2me | Definitions.Def_SelectedFloorTransfer
-- name    : SelectedFloorTransfer
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T08:44:10.131245+00:00
-- url     : https://prove2.me/theorems/bf52eaab-d085-4a74-bc2a-bd87f5804587
-- title:
--   SelectedFloorTransfer definitions
-- statement:
--   Specialization of floor-depth and recurrence bounds to the selected profile. These results retain their stated hypotheses and do not establish the complete fixed-tape multiplication algorithm.
--
--   [Original Lean source](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/machine-transfer-verification/transfer-proof/recurrence/SelectedFloorTransfer.lean). Imported from CrocSwap/integer-mult-bounds at `7c49fe32c55d`. Original authorship and assistance credits are retained in the upstream NOTICE and package documentation. [Attribution notice](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/NOTICE). Apache-2.0. Imported by marwahaha using lean-splitter.
-- source:
--   https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/machine-transfer-verification/transfer-proof/recurrence/SelectedFloorTransfer.lean | Apache-2.0 | CrocSwap contributors; see pinned NOTICE | lean-splitter import, independently validated on Hetzner

import Definitions.Def_FloorRecurrence
import Definitions.Def_SelectedProfileReal
set_option autoImplicit true
namespace SelectedFloorTransfer
open SelectedProfileCertificate
def maxChild : ℕ := 529
theorem maxChild_lt : maxChild < m := by norm_num [maxChild, m]
def depth (e : ℕ) : ℕ := FloorDepth.depth m maxChild maxChild_lt e
noncomputable def costConstant (f : ℕ → ℝ) (C : ℝ) : ℝ :=
  FloorRecurrence.boundConstant m f C SelectedProfileReal.powerCharacteristic
end SelectedFloorTransfer


