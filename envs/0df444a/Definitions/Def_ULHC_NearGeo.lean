-- Prove2me | Definitions.Def_ULHC_NearGeo
-- name    : ULHC_NearGeo
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T02:58:05.842799+00:00
-- url     : https://prove2.me/theorems/f2471840-245c-45a0-a24d-308cca4ad8b0
-- title:
--   Near Geo
-- statement:
--   Definitions and structural lemmas for Near Geo, from zzyzek/SolidGridGraphHamiltonianCycle2D-Lean contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Umans-Lenhart Hamiltonian-cycle algorithm for solid grid graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/NearGeo.lean

import Definitions.Def_ULHC_Touch
import Definitions.Def_ULHC_Stacked
set_option autoImplicit true
namespace ULHC
open Finset
def Touches (a z : StripSpec) : Prop :=
  ∃ i < z.n, ∃ j < a.n, ∃ x ∈ cellE (cellJ z.c z.s i), x ∈ cellE (cellJ a.c a.s j)
section mid
variable {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
  (hF : Deg2 V F) (hpat : StripPat F c s (k + 2))
  (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j))
include hF hpat hcell
end mid
end ULHC


