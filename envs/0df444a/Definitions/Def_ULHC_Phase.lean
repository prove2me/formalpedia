-- Prove2me | Definitions.Def_ULHC_Phase
-- name    : ULHC_Phase
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T02:20:11.381001+00:00
-- url     : https://prove2.me/theorems/269120e0-a98c-411e-bce1-a85712ee2c90
-- title:
--   Phase
-- statement:
--   Definitions and structural lemmas for Phase, from zzyzek/SolidGridGraphHamiltonianCycle2D-Lean contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Umans-Lenhart Hamiltonian-cycle algorithm for solid grid graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Phase.lean

import Definitions.Def_ULHC_Walk
set_option autoImplicit true
namespace ULHC
open Finset Classical
def Good (o : Bool) (d : ℤ) : Prop := if o then 2 ≤ d else d ≤ -2
section dmono
variable {V : Finset Pt} {F H : Finset Edge} (hF : Deg2 V F) (hH : Deg2 V H)
include hF hH
end dmono
section phase1
variable {V : Finset Pt} {F H : Finset Edge} {P : Finset Pt}
  (hF : Deg2 V F) (hH : Deg2 V H) (hs : Solid V) (hB : Border V F P) (hT : NoTypeIII V F)
  (o : Bool)
def Out (F : Finset Edge) (P : Finset Pt) (o : Bool) (w : Pt) : Prop :=
  ∃ so, Cut P (sideEdge w so) ∧ outArc F w so = o
def Entered (F : Finset Edge) (P : Finset Pt) (o : Bool) (w : Pt) : Prop :=
  ∃ si, Cut P (sideEdge w si) ∧ outArc F w si = !o
noncomputable def sig (F : Finset Edge) (P : Finset Pt) (o : Bool) (w : Pt) : Pt :=
  if h : Out F P o w then nb w (Classical.choose h) else w
def Stop (F : Finset Edge) (P : Finset Pt) (o : Bool) (w : Pt) : Prop :=
  ∃ d, sideEdge w d ∈ F ∧ sideEdge w d.opp ∉ F ∧ sideEdge w (latA d) ∉ F ∧
    sideEdge w (latB d) ∉ F ∧
    (∃ si, (si = latA d ∨ si = latB d) ∧ Cut P (sideEdge w si) ∧ outArc F w si = !o) ∧
    ¬ Cut P (sideEdge w d.opp) ∧ outArc F w d.opp = o
end phase1
end ULHC


