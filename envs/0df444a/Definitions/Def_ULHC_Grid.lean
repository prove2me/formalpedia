-- Prove2me | Definitions.Def_ULHC_Grid
-- name    : ULHC_Grid
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:35:42.540701+00:00
-- url     : https://prove2.me/theorems/d00c48f7-6c18-4184-81b8-d3f53aca1f65
-- title:
--   Grid
-- statement:
--   Definitions and structural lemmas for Grid, from zzyzek/SolidGridGraphHamiltonianCycle2D-Lean contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Umans-Lenhart Hamiltonian-cycle algorithm for solid grid graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Grid.lean

import Mathlib
set_option autoImplicit true
namespace ULHC
abbrev Pt := ℤ × ℤ
inductive Dir
  | h
  | v
  deriving DecidableEq, Repr
structure Edge where
  d : Dir
  p : Pt
  deriving DecidableEq, Repr
namespace Edge
def q (e : Edge) : Pt :=
  match e.d with
  | .h => (e.p.1 + 1, e.p.2)
  | .v => (e.p.1, e.p.2 + 1)
def lo (e : Edge) : Pt :=
  match e.d with
  | .h => (e.p.1, e.p.2 - 1)
  | .v => (e.p.1 - 1, e.p.2)
def hi (e : Edge) : Pt := e.p
end Edge
def bot (c : Pt) : Edge := ⟨.h, c⟩
def top (c : Pt) : Edge := ⟨.h, (c.1, c.2 + 1)⟩
def lft (c : Pt) : Edge := ⟨.v, c⟩
def rgt (c : Pt) : Edge := ⟨.v, (c.1 + 1, c.2)⟩
def eR (p : Pt) : Edge := ⟨.h, p⟩
def eL (p : Pt) : Edge := ⟨.h, (p.1 - 1, p.2)⟩
def eU (p : Pt) : Edge := ⟨.v, p⟩
def eD (p : Pt) : Edge := ⟨.v, (p.1, p.2 - 1)⟩
def ind (F : Finset Edge) (e : Edge) : ℕ := if e ∈ F then 1 else 0
def deg (F : Finset Edge) (p : Pt) : ℕ :=
  ind F (eR p) + ind F (eL p) + ind F (eU p) + ind F (eD p)
def IsEdge (V : Finset Pt) (e : Edge) : Prop := e.p ∈ V ∧ e.q ∈ V
instance (V : Finset Pt) (e : Edge) : Decidable (IsEdge V e) := by
  unfold IsEdge; infer_instance
def IsCell (V : Finset Pt) (c : Pt) : Prop :=
  c ∈ V ∧ (c.1 + 1, c.2) ∈ V ∧ (c.1, c.2 + 1) ∈ V ∧ (c.1 + 1, c.2 + 1) ∈ V
instance (V : Finset Pt) (c : Pt) : Decidable (IsCell V c) := by
  unfold IsCell; infer_instance
def IsFactor (V : Finset Pt) (d : Pt → ℕ) (F : Finset Edge) : Prop :=
  (∀ e ∈ F, IsEdge V e) ∧ ∀ p ∈ V, deg F p = d p
def Is2Factor (V : Finset Pt) (F : Finset Edge) : Prop := IsFactor V (fun _ => 2) F
def MissAdj (V : Finset Pt) (a b : Pt) : Prop :=
  a ∉ V ∧ b ∉ V ∧ |a.1 - b.1| ≤ 1 ∧ |a.2 - b.2| ≤ 1
def Solid (V : Finset Pt) : Prop :=
  ∀ a, a ∉ V → ∃ b, Relation.ReflTransGen (MissAdj V) a b ∧ ∀ p ∈ V, b.1 < p.1
end ULHC


