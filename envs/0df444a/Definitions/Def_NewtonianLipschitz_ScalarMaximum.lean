-- Prove2me | Definitions.Def_NewtonianLipschitz_ScalarMaximum
-- name    : NewtonianLipschitz_ScalarMaximum
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T03:20:13.531127+00:00
-- url     : https://prove2.me/theorems/37aba40c-a203-479c-b6e4-643abd92cadf
-- title:
--   Scalar Maximum
-- statement:
--   Definitions and structural lemmas for Scalar Maximum, from alexodas and contributors's pinned Sharp Newtonian field Lipschitz bounds development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/ScalarMaximum.lean

module
public import Definitions.Def_NewtonianLipschitz_CubicCandidate
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
namespace NewtonianLipschitz
noncomputable def candidateMaximum : ℝ :=
  candidateCoefficient candidateCriticalPoint
end NewtonianLipschitz


