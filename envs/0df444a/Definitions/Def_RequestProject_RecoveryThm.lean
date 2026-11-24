-- Prove2me | Definitions.Def_RequestProject_RecoveryThm
-- name    : RequestProject_RecoveryThm
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T11:25:41.447745+00:00
-- url     : https://prove2.me/theorems/445ee308-53b4-4b45-b0fc-5f91efe5ac93
-- title:
--   Recovery Thm
-- statement:
--   Definitions and structural lemmas for Recovery Thm, from sawan201 (sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees; see pinned CC0-1.0 LICENSE)'s pinned First-derivative chromatic symmetric function reconstruction for proper trees development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/RecoveryThm.lean

import Definitions.Def_RequestProject_Recovery
set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
namespace ChromaticReconstruction
variable {K : Type*} [Fintype K] (S : SimpleGraph K) (m : K → ℕ)
end ChromaticReconstruction


