-- Prove2me | Definitions.Def_Erdos1007_Geometry_FinLe
-- name    : Erdos1007_Geometry_FinLe
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T06:52:54.993799+00:00
-- url     : https://prove2.me/theorems/3a278112-fcd6-559d-801e-c8075f66038b
-- title:
--   Fin Le
-- statement:
--   Definitions and structural lemmas for Fin Le, from Dishant Shah (Dishah3241/Erdos1007; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Unit-distance graphs of dimension four with nine edges (Erdos Problem 1007 extremal half) development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Dishah3241/Erdos1007/blob/43f89415a6663848a1445effbda8b3abe77b052b/Erdos1007/Geometry/FinLe.lean

module
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Data.Fin.SuccPred
public import Mathlib.Data.Set.Operations
public import Mathlib.Logic.Function.Basic
set_option autoImplicit false
@[expose] public section
namespace Erdos1007
noncomputable section
def appendZero {n m : ℕ} (h : n ≤ m) (x : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2
    (Function.extend (Fin.castLE h) (fun i => x i) (fun _ => (0 : ℝ)))
@[expose] public section
end
end
end Erdos1007


