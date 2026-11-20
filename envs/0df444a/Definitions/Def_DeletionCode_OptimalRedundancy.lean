-- Prove2me | Definitions.Def_DeletionCode_OptimalRedundancy
-- name    : DeletionCode_OptimalRedundancy
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T07:08:25.093002+00:00
-- url     : https://prove2.me/theorems/10002954-2e4c-42fa-9ad5-bdb880ae5fb0
-- title:
--   Optimal Redundancy
-- statement:
--   Definitions and structural lemmas for Optimal Redundancy, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/OptimalRedundancy.lean

import Definitions.Def_DeletionCode_CodeExistence
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Lattice.Fold
set_option autoImplicit true
namespace DeletionCode.OptimalRedundancy
open HeaderRecovery Filter
noncomputable def correctingCodes (t n : ℕ) : Finset (Finset (Bits n)) := by
  classical
  exact Finset.univ.filter (CodeSelection.Corrects t)
noncomputable def optimalCodeSize (t n : ℕ) : ℕ :=
  (correctingCodes t n).sup Finset.card
noncomputable def optimalRedundancy (t n : ℕ) : ℝ :=
  (n : ℝ) - Real.logb 2 (optimalCodeSize t n : ℝ)
end DeletionCode.OptimalRedundancy


