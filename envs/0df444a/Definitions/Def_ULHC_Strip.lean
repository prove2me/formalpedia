-- Prove2me | Definitions.Def_ULHC_Strip
-- name    : ULHC_Strip
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:45:07.363801+00:00
-- url     : https://prove2.me/theorems/a8a666fd-d125-419a-9ef6-b1971aee9e46
-- title:
--   Strip
-- statement:
--   Definitions and structural lemmas for Strip, from zzyzek/SolidGridGraphHamiltonianCycle2D-Lean contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Umans-Lenhart Hamiltonian-cycle algorithm for solid grid graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Strip.lean

import Definitions.Def_ULHC_Iso
set_option autoImplicit true
namespace ULHC
open Finset
def front (c : Pt) (s : Side) : Edge := sideEdge c s
def back (c : Pt) (s : Side) : Edge := sideEdge c s.opp
def lat1 (c : Pt) : Side → Edge
  | .t => lft c
  | .b => lft c
  | .r => bot c
  | .l => bot c
def lat2 (c : Pt) : Side → Edge
  | .t => rgt c
  | .b => rgt c
  | .r => top c
  | .l => top c
def back1 (c : Pt) : Side → Pt
  | .t => (c.1, c.2)
  | .b => (c.1, c.2 + 1)
  | .r => (c.1, c.2)
  | .l => (c.1 + 1, c.2)
def back2 (c : Pt) : Side → Pt
  | .t => (c.1 + 1, c.2)
  | .b => (c.1 + 1, c.2 + 1)
  | .r => (c.1, c.2 + 1)
  | .l => (c.1 + 1, c.2 + 1)
def front1 (c : Pt) : Side → Pt
  | .t => (c.1, c.2 + 1)
  | .b => (c.1, c.2)
  | .r => (c.1 + 1, c.2)
  | .l => (c.1, c.2)
def front2 (c : Pt) : Side → Pt
  | .t => (c.1 + 1, c.2 + 1)
  | .b => (c.1 + 1, c.2)
  | .r => (c.1 + 1, c.2 + 1)
  | .l => (c.1, c.2 + 1)
def outer1 (c : Pt) : Side → Edge
  | .t => ⟨.h, (c.1 - 1, c.2 + 1)⟩
  | .b => ⟨.h, (c.1 - 1, c.2)⟩
  | .r => ⟨.v, (c.1 + 1, c.2 - 1)⟩
  | .l => ⟨.v, (c.1, c.2 - 1)⟩
def outer2 (c : Pt) : Side → Edge
  | .t => ⟨.h, (c.1 + 1, c.2 + 1)⟩
  | .b => ⟨.h, (c.1 + 1, c.2)⟩
  | .r => ⟨.v, (c.1 + 1, c.2 + 1)⟩
  | .l => ⟨.v, (c.1, c.2 + 1)⟩
def cellJ (c : Pt) (s : Side) (j : ℕ) : Pt :=
  match s with
  | .t => (c.1, c.2 + j)
  | .b => (c.1, c.2 - j)
  | .r => (c.1 + j, c.2)
  | .l => (c.1 - j, c.2)
section geo
variable (c : Pt) (s : Side)
end geo
end ULHC


