-- Prove2me | Definitions.Def_RequestProject_Psi_RiseComp
-- name    : RequestProject_Psi_RiseComp
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T22:52:19.387798+00:00
-- url     : https://prove2.me/theorems/4b13045f-6d4c-40d1-aa63-451139ec4d43
-- title:
--   Rise Comp
-- statement:
--   Definitions and structural lemmas for Rise Comp, from SashaIr/leaving-the-hall contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Dyck-path algebra and decorated-Dyck-path bijection development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/RiseComp.lean

import Definitions.Def_RequestProject_Psi_Area
set_option autoImplicit true
namespace Psi
def ppart (n : ℕ) : List ℕ := if n > 0 then [n] else []
def leadN : List Bool → ℕ
  | true :: r => leadN r + 1
  | _ => 0
def afterLeadRun : List Bool → List Bool
  | true :: r => afterLeadRun r
  | false :: r => r
  | [] => []
end Psi


