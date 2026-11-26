-- Prove2me | Definitions.Def_FD1D_V5_Parameters
-- name    : FD1D_V5_Parameters
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T10:11:37.711865+00:00
-- url     : https://prove2.me/theorems/186320a5-d24b-59ed-a053-1378dc866ebb
-- title:
--   Parameters
-- statement:
--   Definitions and structural lemmas for Parameters, from Yash Kanoria (ykanoria/FD1d-Lean; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Tight upper bound for fully dynamic matching on the line development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/Parameters.lean

import Definitions.Def_FD1D_Tree
set_option autoImplicit true
namespace FD1D.V5
noncomputable section
open Filter Asymptotics
def parameterA (m : ℕ) : ℕ :=
  2000 * Nat.clog 2 (m + 1)
def depthTarget (m : ℕ) : ℕ :=
  max 1 (m / parameterA m)
def treeDepth (m : ℕ) : ℕ :=
  Nat.log 2 (depthTarget m)
def leafCount (m : ℕ) : ℕ :=
  2 ^ treeDepth m
end
end FD1D.V5


