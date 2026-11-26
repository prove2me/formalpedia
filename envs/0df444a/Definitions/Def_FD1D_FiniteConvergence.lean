-- Prove2me | Definitions.Def_FD1D_FiniteConvergence
-- name    : FD1D_FiniteConvergence
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T10:06:08.062054+00:00
-- url     : https://prove2.me/theorems/052d2460-b79d-4a9c-88d0-5d34176650d0
-- title:
--   Finite Convergence
-- statement:
--   Definitions and structural lemmas for Finite Convergence, from Yash Kanoria (ykanoria/FD1d-Lean; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Tight upper bound for fully dynamic matching on the line development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/FiniteConvergence.lean

import Definitions.Def_FD1D_Expectations
set_option autoImplicit true
namespace FD1D
noncomputable section
open Filter
open scoped BigOperators Topology
namespace FiniteKernel
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
noncomputable def reachTime
    (K : FiniteKernel α) (hirr : K.Irreducible) (x y : α) : ℕ :=
  Classical.choose (hirr x y)
def lawL1 (μ ν : FiniteLaw α) : ℝ :=
  ∑ x, |μ.mass x - ν.mass x|
end FiniteKernel
end
end FD1D


