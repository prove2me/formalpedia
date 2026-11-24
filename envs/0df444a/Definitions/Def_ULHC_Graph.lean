-- Prove2me | Definitions.Def_ULHC_Graph
-- name    : ULHC_Graph
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:41:33.589799+00:00
-- url     : https://prove2.me/theorems/04c2e3d9-1e59-4080-a7d0-d7a9965633a5
-- title:
--   Graph
-- statement:
--   Definitions and structural lemmas for Graph, from zzyzek/SolidGridGraphHamiltonianCycle2D-Lean contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Umans-Lenhart Hamiltonian-cycle algorithm for solid grid graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Graph.lean

import Definitions.Def_ULHC_Planar
set_option autoImplicit true
namespace ULHC
open Finset Classical
noncomputable def cls (V : Finset Pt) (F : Finset Edge) (x : Pt) : Finset Pt := V.filter (Conn F x)
noncomputable def ncomp (V : Finset Pt) (F : Finset Edge) : ℕ := (V.image (cls V F)).card
def inc (y : Pt) : Finset Edge := {eR y, eU y, eL y, eD y}
def Closed (F : Finset Edge) (K : Finset Pt) : Prop := ∀ x ∈ K, ∀ y, Adj F x y → y ∈ K
def Inside (V : Finset Pt) (F : Finset Edge) : Prop := ∀ e ∈ F, e.p ∈ V ∧ e.q ∈ V
def other (e : Edge) (y : Pt) : Pt := if e.p = y then e.q else e.p
end ULHC


