-- Prove2me | Definitions.Def_RequestProject_Psi_Bijection
-- name    : RequestProject_Psi_Bijection
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T22:55:29.844029+00:00
-- url     : https://prove2.me/theorems/4276938a-95a0-4233-9774-b0dde4a09ce5
-- title:
--   Bijection
-- statement:
--   Definitions and structural lemmas for Bijection, from SashaIr/leaving-the-hall contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Dyck-path algebra and decorated-Dyck-path bijection development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Bijection.lean

import Definitions.Def_RequestProject_Psi_Inverse
set_option autoImplicit true
namespace Psi
def numNBeforeDD : List Bool → ℕ
  | [] => 0
  | true :: r => numNBeforeDD r + 1
  | false :: false :: _ => 0
  | false :: r => numNBeforeDD r
end Psi


