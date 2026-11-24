-- Prove2me | Definitions.Def_ULHC_Planar
-- name    : ULHC_Planar
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:40:16.50124+00:00
-- url     : https://prove2.me/theorems/63c56233-1135-4f78-804e-4f42f31d06a6
-- title:
--   Planar
-- statement:
--   Definitions and structural lemmas for Planar, from zzyzek/SolidGridGraphHamiltonianCycle2D-Lean contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Umans-Lenhart Hamiltonian-cycle algorithm for solid grid graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Planar.lean

import Definitions.Def_ULHC_Conn
set_option autoImplicit true
namespace ULHC
open Finset
def rot (f : Edge → ℤ) (e : Edge) : ℤ :=
  match e.d with
  | .h => f e
  | .v => - f e
def edgesAt (L : List Pt) : Finset Edge :=
  L.toFinset.biUnion (fun z => {eR z, eU z})
section around
variable {E : Finset Edge} {w : Edge → ℤ} (hS : Supp E w) (hb : Balanced w)
include hS hb
end around
end ULHC


