-- Prove2me | Definitions.Def_ULHC_Enum
-- name    : ULHC_Enum
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T02:54:50.900454+00:00
-- url     : https://prove2.me/theorems/b7d19709-fb0b-403e-bcba-3691563e26bb
-- title:
--   Enum
-- statement:
--   Definitions and structural lemmas for Enum, from zzyzek/SolidGridGraphHamiltonianCycle2D-Lean contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Umans-Lenhart Hamiltonian-cycle algorithm for solid grid graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Enum.lean

import Definitions.Def_ULHC_CrPath
import Definitions.Def_ULHC_Comp
import Definitions.Def_ULHC_Phase2
import Theorems.Thm_ULHC_APair_flip
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
open Finset
instance : DecidableEq StripSpec := fun a b =>
  decidable_of_iff (a.c = b.c ∧ a.s = b.s ∧ a.n = b.n) (by
    cases a; cases b; simp)
section enum
variable (V : Finset Pt) (F : Finset Edge) (c : Pt) (s : Side)
def LatOK (j : ℕ) : Prop :=
  (lat1 (cellJ c s j) s ∈ F ↔ j % 2 = 1) ∧ (lat2 (cellJ c s j) s ∈ F ↔ j % 2 = 1)
instance (j : ℕ) : Decidable (LatOK F c s j) := by unfold LatOK; infer_instance
def stripScan : ℕ → ℕ → Option ℕ
  | 0, _ => none
  | k + 1, j =>
    if IsCell V (cellJ c s j) ∧ LatOK F c s j then
      if (front (cellJ c s j) s ∈ F ↔ j % 2 = 0) then some (j + 1) else stripScan k (j + 1)
    else none
def stripLen : Option ℕ := if back c s ∈ F then stripScan V F c s V.card 0 else none
variable {V F c s}
variable (V F)
def sidesF : Finset Side := {.b, .t, .l, .r}
def allStrips : Finset StripSpec :=
  (V.filter (IsCell V)).biUnion fun c => sidesF.biUnion fun s =>
    ((stripLen V F c s).map (fun n => StripSpec.mk c s n)).toFinset
variable {V F}
end enum
section decide
variable {V : Finset Pt} {F G : Finset Edge}
def connB (V : Finset Pt) (F : Finset Edge) (x y : Pt) : Bool := decide (y ∈ ccls V F x)
def validB (V : Finset Pt) (F : Finset Edge) (σ : StripSpec) : Bool :=
  decide (σ ∈ allStrips V F) && !connB V F (back1 σ.c σ.s) (front1 σ.c σ.s)
def sideOffB (b c : StripSpec) : Bool :=
  (List.range c.n).all fun j => (List.range (b.n - 1)).all fun i =>
    decide (∀ e ∈ cellE (cellJ c.c c.s j), e ∉ cellE (cellJ b.c b.s i))
def midB (b : StripSpec) (z : Pt) : Bool :=
  (List.range (b.n - 2)).any fun j =>
    decide (j % 2 = 1 ∧ (z = front1 (cellJ b.c b.s j) b.s ∨ z = front2 (cellJ b.c b.s j) b.s))
def endOffB (b c : StripSpec) : Bool :=
  decide (c.n % 2 = 0 → ∀ e ∈ cellE (endCell c), e ∉ cellE (endCell b))
def notEndB (b c : StripSpec) : Bool :=
  (List.range c.n).all fun j => decide (cellJ c.c c.s j ≠ endCell b)
def cr2B (V : Finset Pt) (G : Finset Edge) (b c : StripSpec) : Bool :=
  decide (2 ≤ b.n ∧ b.n % 2 = 0) && decide (c ∈ allStrips V (flip G (endCell b))) &&
    sideOffB b c && notEndB b c && endOffB b c && !midB b (back1 c.c c.s) &&
    !midB b (front1 c.c c.s) && connB V G (back1 c.c c.s) (front1 c.c c.s) &&
    !connB V (flip G (endCell b)) (back1 c.c c.s) (front1 c.c c.s)
end decide
end ULHC


