-- Prove2me | Definitions.Def_ULHC_Complete
-- name    : ULHC_Complete
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T03:02:22.998012+00:00
-- url     : https://prove2.me/theorems/b1d4e105-7771-4ac2-a4b5-9597091d1369
-- title:
--   Complete
-- statement:
--   Definitions and structural lemmas for Complete, from zzyzek/SolidGridGraphHamiltonianCycle2D-Lean contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Umans-Lenhart Hamiltonian-cycle algorithm for solid grid graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Complete.lean

import Definitions.Def_ULHC_Reverse
import Definitions.Def_ULHC_ChainLinks
set_option autoImplicit true
namespace ULHC
open Finset
section t3
variable {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
  (hF : Deg2 V F) (hT : NoTypeIII V F) (hk : k % 2 = 0)
  (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j)) (hpat : StripPat F c s (k + 2))
  (hsep : ¬ Conn F (back1 c s) (front1 c s))
include hF hT hk hcell hpat hsep
end t3
end ULHC


