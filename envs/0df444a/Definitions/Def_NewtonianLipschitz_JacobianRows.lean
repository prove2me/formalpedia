-- Prove2me | Definitions.Def_NewtonianLipschitz_JacobianRows
-- name    : NewtonianLipschitz_JacobianRows
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T03:19:43.123551+00:00
-- url     : https://prove2.me/theorems/bca1b8a0-b9b4-4091-a31f-2af01e88eded
-- title:
--   Jacobian Rows
-- statement:
--   Definitions and structural lemmas for Jacobian Rows, from alexodas and contributors's pinned Sharp Newtonian field Lipschitz bounds development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianRows.lean

module
public import Mathlib
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
namespace NewtonianLipschitz
def dominantRowNumerator (u v : ℝ) : ℝ :=
  2 - u ^ 2 - v ^ 2 + 3 * (u + v)
def lateralRowNumerator (u v : ℝ) : ℝ :=
  |2 * u ^ 2 - 1 - v ^ 2| + 3 * u * (1 + v)
noncomputable def diagonalParameter (u v : ℝ) : ℝ :=
  Real.sqrt ((u ^ 2 + v ^ 2) / 2)
end NewtonianLipschitz


