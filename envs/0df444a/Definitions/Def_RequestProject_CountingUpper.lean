-- Prove2me | Definitions.Def_RequestProject_CountingUpper
-- name    : RequestProject_CountingUpper
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T12:41:13.269246+00:00
-- url     : https://prove2.me/theorems/068894ea-a35f-46fc-aec8-8483804cbba7
-- title:
--   Counting Upper
-- statement:
--   Definitions and structural lemmas for Counting Upper, from sawan201 (sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees; see pinned CC0-1.0 LICENSE)'s pinned First-derivative chromatic symmetric function reconstruction for proper trees development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/CountingUpper.lean

import Definitions.Def_RequestProject_Truncation
import Definitions.Def_RequestProject_Forest
set_option autoImplicit true
open Finset
open scoped Classical
noncomputable section
namespace ChromaticReconstruction
def bigParts {k : ℕ} (μ : Nat.Partition k) : Multiset ℕ := μ.parts.filter (2 ≤ ·)
end ChromaticReconstruction


