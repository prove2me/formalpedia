-- Prove2me | Definitions.Def_FD1D_Drift
-- name    : FD1D_Drift
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T09:50:56.452969+00:00
-- url     : https://prove2.me/theorems/a9812860-8602-45e8-85d6-a9cbb3c108ce
-- title:
--   Drift
-- statement:
--   Definitions and structural lemmas for Drift, from Yash Kanoria (ykanoria/FD1d-Lean; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Tight upper bound for fully dynamic matching on the line development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Drift.lean

import Definitions.Def_FD1D_Arithmetic
set_option autoImplicit true
namespace FD1D
noncomputable section
def harmonicPotential (a : ℝ) (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 k, 1 / (j + a)
end
end FD1D


