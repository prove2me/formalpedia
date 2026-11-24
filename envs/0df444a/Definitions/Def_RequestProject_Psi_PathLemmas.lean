-- Prove2me | Definitions.Def_RequestProject_Psi_PathLemmas
-- name    : RequestProject_Psi_PathLemmas
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T22:49:42.464817+00:00
-- url     : https://prove2.me/theorems/57ca9dcc-acc8-4d03-9bc0-57af496492a8
-- title:
--   Path Lemmas
-- statement:
--   Definitions and structural lemmas for Path Lemmas, from SashaIr/leaving-the-hall contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Dyck-path algebra and decorated-Dyck-path bijection development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/PathLemmas.lean

import Definitions.Def_RequestProject_Psi_Defs
set_option autoImplicit true
namespace Psi
def runHeight : List Bool → Int → Int
  | [], h => h
  | true :: r, h => runHeight r (h + 1)
  | false :: r, h => runHeight r (h - 1)
def validFrom : List Bool → Int → Prop
  | [], _ => True
  | true :: r, h => validFrom r (h + 1)
  | false :: r, h => 0 < h ∧ validFrom r (h - 1)
def stEast : List Bool → Bool → Bool
  | [], le => le
  | true :: r, _ => stEast r false
  | false :: r, _ => stEast r true
def fUD (a : Nat) : List Bool := (List.replicate a [true, false]).flatten
end Psi


