-- Prove2me | Definitions.Def_ULHC_D
-- name    : ULHC_D
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:37:56.839051+00:00
-- url     : https://prove2.me/theorems/6dd4dee8-c68b-433f-8a2b-7ba32bddfc98
-- title:
--   D
-- statement:
--   Definitions and structural lemmas for D, from zzyzek/SolidGridGraphHamiltonianCycle2D-Lean contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Umans-Lenhart Hamiltonian-cycle algorithm for solid grid graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/D.lean

import Definitions.Def_ULHC_Arcs
set_option autoImplicit true
namespace ULHC
open Finset
def wb (inS u : Bool) : ℤ := if inS then (if u then 2 else -2) else 0
def wD (F H : Finset Edge) (e : Edge) : ℤ :=
  wb (decide (e ∈ F) ^^ decide (e ∈ H)) (up F e)
def D (F H : Finset Edge) (c : Pt) : ℤ := pot (symmDiff F H) (wD F H) c
section jumps
variable {V : Finset Pt} {d : Pt → ℕ} {F H : Finset Edge}
  (hF : IsFactor V d F) (hH : IsFactor V d H)
include hF hH
end jumps
section solid
variable {V : Finset Pt} {d : Pt → ℕ} {F H : Finset Edge}
def Around (a c : Pt) : Prop :=
  (c.1 = a.1 - 1 ∨ c.1 = a.1) ∧ (c.2 = a.2 - 1 ∨ c.2 = a.2)
variable (hF : IsFactor V d F) (hH : IsFactor V d H)
include hF hH
end solid
def cellE (c : Pt) : Finset Edge := {bot c, top c, lft c, rgt c}
def flip (F : Finset Edge) (c : Pt) : Finset Edge := symmDiff F (cellE c)
def cells (V : Finset Pt) : Finset Pt := V.filter (IsCell V)
def mu (V : Finset Pt) (F H : Finset Edge) : ℕ := ∑ c ∈ cells V, (D F H c).natAbs
end ULHC


