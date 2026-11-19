-- Prove2me | Definitions.Def_DeletionCode_RedundancyBounds
-- name    : DeletionCode_RedundancyBounds
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T05:36:57.580979+00:00
-- url     : https://prove2.me/theorems/26f1679c-ba22-4403-8381-1ceed9d39fa6
-- title:
--   Redundancy Bounds
-- statement:
--   Definitions and structural lemmas for Redundancy Bounds, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RedundancyBounds.lean

import Definitions.Def_DeletionCode_PaperParameters
import Definitions.Def_DeletionCode_WitnessCost
set_option autoImplicit true
namespace DeletionCode.RedundancyBounds
open HeaderRecovery
noncomputable def redundancy (n : ℕ) (C : Finset (Bits n)) : ℝ :=
  (n : ℝ) - Real.logb 2 (C.card : ℝ)
def labelCount (t n : ℕ) : ℕ :=
  8 * n ^ (2 * t - 1) * (PaperParameters.L n) ^ (WitnessCost.exponent t)
end DeletionCode.RedundancyBounds


