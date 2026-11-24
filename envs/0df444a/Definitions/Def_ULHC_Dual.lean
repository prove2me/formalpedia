-- Prove2me | Definitions.Def_ULHC_Dual
-- name    : ULHC_Dual
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T02:27:57.643799+00:00
-- url     : https://prove2.me/theorems/50789469-5e67-4bfa-b306-92cbed219d10
-- title:
--   Dual
-- statement:
--   Definitions and structural lemmas for Dual, from zzyzek/SolidGridGraphHamiltonianCycle2D-Lean contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Umans-Lenhart Hamiltonian-cycle algorithm for solid grid graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Dual.lean

import Definitions.Def_ULHC_L57
set_option autoImplicit true
namespace ULHC
open Finset Classical
inductive DStep (V : Finset Pt) (F : Finset Edge) : Pt → Pt → Finset Edge → Prop
  | inner (c : Pt) (tf : Side) : IsCell V c → IsCell V (nb c tf) → sideEdge c tf ∉ F →
      DStep V F c (nb c tf) {sideEdge c tf}
  | outer (c c' : Pt) (tf t' : Side) : IsCell V c → IsCell V c' → ¬ IsCell V (nb c tf) →
      ¬ IsCell V (nb c' t') → sideEdge c tf ∉ F → sideEdge c' t' ∉ F →
      DStep V F c c' (symmDiff {sideEdge c tf} {sideEdge c' t'})
inductive DWalk (V : Finset Pt) (F : Finset Edge) : Pt → Pt → Finset Edge → Prop
  | nil (a : Pt) : DWalk V F a a ∅
  | cons {a d b : Pt} {E B : Finset Edge} : DStep V F a d E → DWalk V F d b B →
      DWalk V F a b (symmDiff E B)
section dual
variable {V : Finset Pt} {F : Finset Edge}
end dual
end ULHC


