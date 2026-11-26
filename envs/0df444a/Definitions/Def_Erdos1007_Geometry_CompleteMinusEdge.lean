-- Prove2me | Definitions.Def_Erdos1007_Geometry_CompleteMinusEdge
-- name    : Erdos1007_Geometry_CompleteMinusEdge
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T06:52:53.488094+00:00
-- url     : https://prove2.me/theorems/2fb26221-d16a-48e7-b6dd-14a2e9064521
-- title:
--   Complete Minus Edge
-- statement:
--   Definitions and structural lemmas for Complete Minus Edge, from Dishant Shah (Dishah3241/Erdos1007; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Unit-distance graphs of dimension four with nine edges (Erdos Problem 1007 extremal half) development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Dishah3241/Erdos1007/blob/43f89415a6663848a1445effbda8b3abe77b052b/Erdos1007/Geometry/CompleteMinusEdge.lean

module
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
set_option autoImplicit false
@[expose] public section
namespace Erdos1007
noncomputable section
def xCoord_cme : Fin 5 → ℝ
  | 0 => 0
  | 1 => 1
  | 2 => 1 / 2
  | 3 => 1 / 2
  | 4 => 1 / 2
def yCoord_cme : Fin 5 → ℝ
  | 0 => 0
  | 1 => 0
  | 2 => Real.sqrt 3 / 2
  | 3 => Real.sqrt 3 / 6
  | 4 => Real.sqrt 3 / 6
def zCoord_cme : Fin 5 → ℝ
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => Real.sqrt (2 / 3)
  | 4 => -Real.sqrt (2 / 3)
def pt_cme (i : Fin 5) : EuclideanSpace ℝ (Fin 3) := !₂[xCoord_cme i, yCoord_cme i, zCoord_cme i]
@[expose] public section
end
end
end Erdos1007


