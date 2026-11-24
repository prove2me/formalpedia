-- Prove2me | Definitions.Def_ULHC_Reroute
-- name    : ULHC_Reroute
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T02:29:54.625592+00:00
-- url     : https://prove2.me/theorems/8d77cd2e-3a15-4911-9fa4-6c605b68826d
-- title:
--   Reroute
-- statement:
--   Definitions and structural lemmas for Reroute, from zzyzek/SolidGridGraphHamiltonianCycle2D-Lean contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Umans-Lenhart Hamiltonian-cycle algorithm for solid grid graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Reroute.lean

import Definitions.Def_ULHC_V2Seq
import Theorems.Thm_ULHC_Ends_swap

set_option autoImplicit true
namespace ULHC
open Finset Classical
section swap
variable (c : Pt) (s : Side)
def Tsw (j : ℕ) : Finset Edge :=
  {lat1 (cellJ c s j) s, lat2 (cellJ c s j) s, lat1 (cellJ c s (j + 1)) s,
    lat2 (cellJ c s (j + 1)) s, outer1 (cellJ c s j) s, outer2 (cellJ c s j) s}
end swap
section reroute
variable {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
  (hF : Deg2 V F) (hk : k % 2 = 0) (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j))
  (hpat : StripPat F c s (k + 2))
include hF hk hcell hpat
end reroute
end ULHC


