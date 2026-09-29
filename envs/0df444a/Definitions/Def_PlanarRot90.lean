-- Prove2me | Definitions.Def_PlanarRot90
-- name    : PlanarRot90
-- status  : Definition
-- author  : @xuanji
-- created : 2026-09-27T21:35:15.588797+00:00
-- url     : https://prove2.me/theorems/6fd3bb5f-17e8-46bc-b647-3dd75025dde3
-- title:
--   Planar plane quarter-turn operator
-- statement:
--   A coordinate-level quarter-turn operator on the Euclidean plane. It sends a vector \(v\) to the vector with coordinates \((-v_1,v_0)\), providing the oriented normal direction used by the polygonal-arc collar constructions.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PlanarRot90.lean

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic

open Classical
noncomputable section

-- [TABLET NODE: PlanarRot90]
-- Source: https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PlanarRot90.lean#L1-L9
def PlanarRot90 (v : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 (fun k : Fin 2 => if k = 0 then -(v 1) else v 0)


