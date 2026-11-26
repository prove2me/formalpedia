-- Prove2me | Definitions.Def_FD1D_PotentialBounds
-- name    : FD1D_PotentialBounds
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T10:02:03.776606+00:00
-- url     : https://prove2.me/theorems/635c4f92-e6e3-4472-ac33-cafbbd87cd45
-- title:
--   Potential Bounds
-- statement:
--   Definitions and structural lemmas for Potential Bounds, from Yash Kanoria (ykanoria/FD1d-Lean; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Tight upper bound for fully dynamic matching on the line development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/PotentialBounds.lean

import Definitions.Def_FD1D_Potential
import Definitions.Def_FD1D_Parameters
set_option autoImplicit true
namespace FD1D
noncomputable section
open Set intervalIntegral
open scoped BigOperators
end
end FD1D


