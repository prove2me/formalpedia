-- Prove2me | Definitions.Def_ULHC_Cr2
-- name    : ULHC_Cr2
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T02:52:27.552862+00:00
-- url     : https://prove2.me/theorems/5ee6b0a5-c1a9-4d0e-8268-ccb981737afe
-- title:
--   Cr2
-- statement:
--   Definitions and structural lemmas for Cr2, from zzyzek/SolidGridGraphHamiltonianCycle2D-Lean contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Umans-Lenhart Hamiltonian-cycle algorithm for solid grid graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Cr2.lean

import Definitions.Def_ULHC_Created
import Theorems.Thm_ULHC_Good_step

set_option autoImplicit true
namespace ULHC
open Finset Classical
section step
variable {V : Finset Pt} {G : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
end step
section count
variable {V : Finset Pt} {G : Finset Edge}
end count
section osi
variable {V : Finset Pt} {G : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
  (hG : Deg2 V G) (hk : k % 2 = 0) (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j))
  (hpat : StripPat G c s (k + 2)) (hsep : ¬ Conn G (back1 c s) (front1 c s))
  (hsame : Conn G (back1 (cellJ c s (k + 1)) s) (back2 (cellJ c s (k + 1)) s))
  (hT' : NoTypeIII V (flipCol G c s (k + 2)))
include hG hk hcell hpat hsep hsame hT'
end osi
end ULHC


