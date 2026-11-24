-- Prove2me | Definitions.Def_ULHC_Arcs
-- name    : ULHC_Arcs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:37:02.966904+00:00
-- url     : https://prove2.me/theorems/df9a2e94-d675-42fd-aa05-5a32c9473b2f
-- title:
--   Arcs
-- statement:
--   Definitions and structural lemmas for Arcs, from zzyzek/SolidGridGraphHamiltonianCycle2D-Lean contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Umans-Lenhart Hamiltonian-cycle algorithm for solid grid graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Arcs.lean

import Definitions.Def_ULHC_Potential
set_option autoImplicit true
namespace ULHC
def par (c : Pt) : Bool := decide ((c.1 + c.2) % 2 = 1)
def inE1 (F : Finset Edge) (e : Edge) : Bool :=
  match e.d with
  | .h => decide (e ∈ F)
  | .v => !decide (e ∈ F)
def up (F : Finset Edge) (e : Edge) : Bool := (par e.lo == inE1 F e)
inductive Side
  | b
  | t
  | l
  | r
  deriving DecidableEq, Repr
def sideEdge (c : Pt) : Side → Edge
  | .b => bot c
  | .t => top c
  | .l => lft c
  | .r => rgt c
def nb (c : Pt) : Side → Pt
  | .b => (c.1, c.2 - 1)
  | .t => (c.1, c.2 + 1)
  | .l => (c.1 - 1, c.2)
  | .r => (c.1 + 1, c.2)
def Side.opp : Side → Side
  | .b => .t
  | .t => .b
  | .l => .r
  | .r => .l
def Side.horiz : Side → Bool
  | .b => true
  | .t => true
  | .l => false
  | .r => false
def outArc (F : Finset Edge) (c : Pt) (s : Side) : Bool :=
  match s with
  | .b => !up F (bot c)
  | .t => up F (top c)
  | .l => !up F (lft c)
  | .r => up F (rgt c)
def darkB (F : Finset Edge) (c : Pt) : Bool := decide (bot c ∈ F)
def darkT (F : Finset Edge) (c : Pt) : Bool := decide (top c ∈ F)
def darkL (F : Finset Edge) (c : Pt) : Bool := decide (lft c ∈ F)
def darkR (F : Finset Edge) (c : Pt) : Bool := decide (rgt c ∈ F)
def Alt (F : Finset Edge) (c : Pt) : Prop :=
  (bot c ∈ F ∧ top c ∈ F ∧ lft c ∉ F ∧ rgt c ∉ F) ∨
  (bot c ∉ F ∧ top c ∉ F ∧ lft c ∈ F ∧ rgt c ∈ F)
instance (F : Finset Edge) (c : Pt) : Decidable (Alt F c) := by
  unfold Alt; infer_instance
def Source (F : Finset Edge) (c : Pt) : Prop := ∀ s, outArc F c s = true
def Sink (F : Finset Edge) (c : Pt) : Prop := ∀ s, outArc F c s = false
end ULHC


