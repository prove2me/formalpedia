-- Prove2me | Definitions.Def_ULHC_L57
-- name    : ULHC_L57
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T02:26:08.384221+00:00
-- url     : https://prove2.me/theorems/dfae13c1-5bff-4dba-9ba2-af125273d15a
-- title:
--   L57
-- statement:
--   Definitions and structural lemmas for L57, from zzyzek/SolidGridGraphHamiltonianCycle2D-Lean contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Umans-Lenhart Hamiltonian-cycle algorithm for solid grid graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/L57.lean

import Definitions.Def_ULHC_Chain
set_option autoImplicit true
namespace ULHC
open Finset Classical
section geo3
variable (c : Pt) (s : Side)
end geo3
section after
variable {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
  (hk : k % 2 = 0) (hpat : StripPat F c s (k + 2))
include hk hpat
end after
def AllConn (F : Finset Edge) (d : Pt) : Prop :=
  Conn F d (d.1 + 1, d.2) ∧ Conn F d (d.1, d.2 + 1) ∧ Conn F d (d.1 + 1, d.2 + 1)
section l57
variable {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
  (hF : Deg2 V F) (hT : NoTypeIII V F) (hk : k % 2 = 0)
  (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j)) (hpat : StripPat F c s (k + 2))
  (hsep : ¬ Conn F (back1 c s) (front1 c s))
end l57
end ULHC


