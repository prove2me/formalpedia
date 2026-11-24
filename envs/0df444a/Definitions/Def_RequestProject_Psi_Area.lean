-- Prove2me | Definitions.Def_RequestProject_Psi_Area
-- name    : RequestProject_Psi_Area
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T22:51:21.022434+00:00
-- url     : https://prove2.me/theorems/e9bfbb74-ccad-4c9b-8584-176bb268f9a1
-- title:
--   Area
-- statement:
--   Definitions and structural lemmas for Area, from SashaIr/leaving-the-hall contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Dyck-path algebra and decorated-Dyck-path bijection development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Area.lean

import Definitions.Def_RequestProject_Psi_PhiBasic
set_option autoImplicit true
namespace Psi
def numE (p : List Bool) : ℕ := (p.filter (· = false)).length
def areaH : List Bool → Int → Bool → Int
  | [], _, _ => 0
  | true :: r, ht, le => (if le then ht else 0) + areaH r (ht + 1) false
  | false :: r, ht, _ => areaH r (ht - 1) true
def hasDD : List Bool → Bool
  | false :: false :: _ => true
  | _ :: r => hasDD r
  | [] => false
end Psi


