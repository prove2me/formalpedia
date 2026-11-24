-- Prove2me | Definitions.Def_ULHC_Created
-- name    : ULHC_Created
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T02:31:02.106194+00:00
-- url     : https://prove2.me/theorems/6a932bb3-99f5-42f5-9d82-321498e3de66
-- title:
--   Created
-- statement:
--   Definitions and structural lemmas for Created, from zzyzek/SolidGridGraphHamiltonianCycle2D-Lean contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Umans-Lenhart Hamiltonian-cycle algorithm for solid grid graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Created.lean

import Definitions.Def_ULHC_Reroute
set_option autoImplicit true
namespace ULHC
open Finset Classical
section created
variable {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
  (hs : Solid V) (x0 : Pt) (hconn : ∀ z ∈ V, Conn (GE V) x0 z)
  (hF : Deg2 V F) (hT : NoTypeIII V F) (hk : k % 2 = 0)
  (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j)) (hpat : StripPat F c s (k + 2))
  (hsep : ¬ Conn F (back1 c s) (front1 c s)) (hT' : NoTypeIII V (flipCol F c s (k + 2)))
include hs x0 hconn hF hT hk hcell hpat hsep hT'
end created
end ULHC


