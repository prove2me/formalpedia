-- Prove2me | Definitions.Def_ULHC_Flip
-- name    : ULHC_Flip
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:42:17.582473+00:00
-- url     : https://prove2.me/theorems/7872feb6-36b8-41d1-b8c6-de44886d8474
-- title:
--   Flip
-- statement:
--   Definitions and structural lemmas for Flip, from zzyzek/SolidGridGraphHamiltonianCycle2D-Lean contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Umans-Lenhart Hamiltonian-cycle algorithm for solid grid graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Flip.lean

import Definitions.Def_ULHC_Graph
set_option autoImplicit true
namespace ULHC
open Finset Classical
section cell
variable {V : Finset Pt} {F : Finset Edge} {x y : ℤ}
  (hV : Inside V F) (hc : IsCell V (x, y))
  (hb : bot (x, y) ∈ F) (ht : top (x, y) ∈ F) (hl : lft (x, y) ∉ F) (hr : rgt (x, y) ∉ F)
  (h2 : ∀ z, (Conn F (x, y) z ∨ Conn F (x, y + 1) z) → deg F z = 2)
include hV hc hb ht hl hr h2
end cell
end ULHC


