-- Prove2me | Definitions.Def_ULHC_Walk
-- name    : ULHC_Walk
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T02:18:56.492605+00:00
-- url     : https://prove2.me/theorems/6dcae070-310d-4187-9df9-5383fb21055e
-- title:
--   Walk
-- statement:
--   Definitions and structural lemmas for Walk, from zzyzek/SolidGridGraphHamiltonianCycle2D-Lean contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Umans-Lenhart Hamiltonian-cycle algorithm for solid grid graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Walk.lean

import Definitions.Def_ULHC_StripCount
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v


set_option autoImplicit true
namespace ULHC
open Finset Classical
instance : Fintype Side := ⟨{.b, .t, .l, .r}, by intro x; cases x <;> simp⟩
def mS (mb mt ml mr : Bool) : Side → Bool
  | .b => mb
  | .t => mt
  | .l => ml
  | .r => mr
def cutS (pbl pbr ptl ptr : Bool) : Side → Bool
  | .b => pbl != pbr
  | .t => ptl != ptr
  | .l => pbl != ptl
  | .r => pbr != ptr
def outS (q : Bool) (m : Side → Bool) : Side → Bool
  | .b => q == m .b
  | .t => q == m .t
  | .l => !(q == m .l)
  | .r => !(q == m .r)
def latA : Side → Side
  | .b => .l
  | .t => .l
  | .l => .b
  | .r => .b
def latB : Side → Side
  | .b => .r
  | .t => .r
  | .l => .t
  | .r => .t
def Border (V : Finset Pt) (F : Finset Edge) (P : Finset Pt) : Prop :=
  P ⊆ V ∧ ∀ x ∈ P, ∀ y, Adj F x y → y ∈ P
def Cut (P : Finset Pt) (e : Edge) : Prop := (e.p ∈ P ↔ e.q ∉ P)
instance (P : Finset Pt) (e : Edge) : Decidable (Cut P e) := by unfold Cut; infer_instance
def corner (w : Pt) : Side → Side → Pt
  | _, _ => w
def NoTypeIII (V : Finset Pt) (F : Finset Edge) : Prop :=
  ∀ c, IsCell V c → ∀ s, back c s ∈ F → front c s ∈ F → lat1 c s ∉ F → lat2 c s ∉ F →
    Conn F (back1 c s) (front1 c s)
def NotTypeIII (_V : Finset Pt) (F : Finset Edge) (c : Pt) : Prop :=
  ∀ s, back c s ∈ F → front c s ∈ F → lat1 c s ∉ F → lat2 c s ∉ F →
    Conn F (back1 c s) (front1 c s)
section hypsLocal
variable {V : Finset Pt} {F : Finset Edge} {P : Finset Pt}
  (hF : Deg2 V F) (hB : Border V F P)
include hF hB
end hypsLocal
section hyps
variable {V : Finset Pt} {F : Finset Edge} {P : Finset Pt}
  (hF : Deg2 V F) (hB : Border V F P) (hT : NoTypeIII V F)
include hF hB hT
end hyps
end ULHC


