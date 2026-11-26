-- Prove2me | Definitions.Def_Erdos1007_Geometry_CompleteBipartite
-- name    : Erdos1007_Geometry_CompleteBipartite
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T06:52:54.144804+00:00
-- url     : https://prove2.me/theorems/ac4a22a4-9943-58ba-89a8-9ec66b1bd005
-- title:
--   Complete Bipartite
-- statement:
--   Definitions and structural lemmas for Complete Bipartite, from Dishant Shah (Dishah3241/Erdos1007; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Unit-distance graphs of dimension four with nine edges (Erdos Problem 1007 extremal half) development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Dishah3241/Erdos1007/blob/43f89415a6663848a1445effbda8b3abe77b052b/Erdos1007/Geometry/CompleteBipartite.lean

module
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Combinatorics.SimpleGraph.Basic
set_option autoImplicit false
@[expose] public section
namespace Erdos1007
def svec (i : Fin 4) (a : ℝ) : EuclideanSpace ℝ (Fin 4) := PiLp.single 2 i a
def pt (r : ℝ) : Fin 3 ⊕ Fin 3 → EuclideanSpace ℝ (Fin 4)
  | .inl 0 => svec (0 : Fin 4) r
  | .inl 1 => svec (0 : Fin 4) (-r)
  | .inl 2 => svec (1 : Fin 4) r
  | .inr 0 => svec (2 : Fin 4) r
  | .inr 1 => svec (2 : Fin 4) (-r)
  | .inr 2 => svec (3 : Fin 4) r
@[expose] public section
end
end Erdos1007


