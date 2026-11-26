-- Prove2me | Definitions.Def_Erdos1007_Geometry_Prism
-- name    : Erdos1007_Geometry_Prism
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T06:52:56.136191+00:00
-- url     : https://prove2.me/theorems/33849275-33bd-5490-9a2c-f68bf19558a7
-- title:
--   Prism
-- statement:
--   Definitions and structural lemmas for Prism, from Dishant Shah (Dishah3241/Erdos1007; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Unit-distance graphs of dimension four with nine edges (Erdos Problem 1007 extremal half) development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Dishah3241/Erdos1007/blob/43f89415a6663848a1445effbda8b3abe77b052b/Erdos1007/Geometry/Prism.lean

module
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
set_option autoImplicit false
@[expose] public section
namespace Erdos1007
noncomputable section
def xCoord_prism : Fin 6 → ℝ
  | 0 => 0
  | 1 => 1 / 2
  | 2 => 1
  | 3 => 0
  | 4 => 1 / 2
  | 5 => 1
def yCoord_prism : Fin 6 → ℝ
  | 0 => 0
  | 1 => 1 + Real.sqrt 3 / 2
  | 2 => 0
  | 3 => 1
  | 4 => Real.sqrt 3 / 2
  | 5 => 1
def pt_prism (i : Fin 6) : EuclideanSpace ℝ (Fin 2) := !₂[xCoord_prism i, yCoord_prism i]
@[expose] public section
end
end
end Erdos1007


