-- Prove2me | Definitions.Def_ULHC_Conn
-- name    : ULHC_Conn
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:38:53.990467+00:00
-- url     : https://prove2.me/theorems/35103fbe-daf4-490d-a6b8-0e3df4711c76
-- title:
--   Conn
-- statement:
--   Definitions and structural lemmas for Conn, from zzyzek/SolidGridGraphHamiltonianCycle2D-Lean contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Umans-Lenhart Hamiltonian-cycle algorithm for solid grid graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Conn.lean

import Definitions.Def_ULHC_D
set_option autoImplicit true
namespace ULHC
def Adj (F : Finset Edge) (a b : Pt) : Prop :=
  ∃ e ∈ F, (e.p = a ∧ e.q = b) ∨ (e.p = b ∧ e.q = a)
def Conn (F : Finset Edge) : Pt → Pt → Prop := Relation.ReflTransGen (Adj F)
def Unit (a b : Pt) : Prop := |a.1 - b.1| + |a.2 - b.2| = 1
def stepFlow (u v : Pt) (e : Edge) : ℤ :=
  (if e.p = u ∧ e.q = v then 1 else 0) - (if e.p = v ∧ e.q = u then 1 else 0)
def flowL : Pt → List Pt → Edge → ℤ
  | _, [], _ => 0
  | u, v :: l, e => stepFlow u v e + flowL v l e
def outflow (f : Edge → ℤ) (x : Pt) : ℤ := f (eR x) + f (eU x) - f (eL x) - f (eD x)
def oneE (a : Edge) (e : Edge) : ℤ := if e = a then 1 else 0
end ULHC


