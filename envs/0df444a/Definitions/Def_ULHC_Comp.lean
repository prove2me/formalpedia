-- Prove2me | Definitions.Def_ULHC_Comp
-- name    : ULHC_Comp
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T02:20:13.625811+00:00
-- url     : https://prove2.me/theorems/96fd2f3f-611f-4680-b32f-05a9847965d1
-- title:
--   Comp
-- statement:
--   Definitions and structural lemmas for Comp, from zzyzek/SolidGridGraphHamiltonianCycle2D-Lean contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Umans-Lenhart Hamiltonian-cycle algorithm for solid grid graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Comp.lean

import Definitions.Def_ULHC_TwoFactor
set_option autoImplicit true
namespace ULHC
open Finset
def fnbr (F : Finset Edge) (u : Pt) : Finset Pt :=
  (((TF.inc4 u).filter (fun e => decide (e ∈ F))).map (fun e => other e u)).toFinset
def creach (F : Finset Edge) (x : Pt) : ℕ → Finset Pt
  | 0 => {x}
  | k + 1 =>
    let C := creach F x k
    C ∪ C.biUnion (fnbr F)
def ccls (V : Finset Pt) (F : Finset Edge) (x : Pt) : Finset Pt := creach F x V.card
def cncomp (V : Finset Pt) (F : Finset Edge) : ℕ := (V.image (ccls V F)).card
section comp
variable {V : Finset Pt} {F : Finset Edge}
end comp
end ULHC


