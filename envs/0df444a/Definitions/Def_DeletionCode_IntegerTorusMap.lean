-- Prove2me | Definitions.Def_DeletionCode_IntegerTorusMap
-- name    : DeletionCode_IntegerTorusMap
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T05:26:59.326497+00:00
-- url     : https://prove2.me/theorems/1ac45b5d-0988-4607-8f96-e60c59cca072
-- title:
--   Integer Torus Map
-- statement:
--   Definitions and structural lemmas for Integer Torus Map, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/IntegerTorusMap.lean

import Definitions.Def_DeletionCode_CircleHash
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Topology.Algebra.Group.Basic
set_option autoImplicit true
namespace DeletionCode.IntegerTorusMap
open scoped BigOperators Matrix
open CircleHash
variable {I J : Type*} [Fintype I]
noncomputable def jointHash (w : J → I → ℤ) :
    (I → UnitAddCircle) →+ (J → UnitAddCircle) where
  toFun weights j := weightedHash weights (w j)
  map_zero' := by
    funext j
    simp [weightedHash]
  map_add' weights weights' := by
    funext j
    change (∑ i, w j i • (weights i + weights' i)) =
      (∑ i, w j i • weights i) + (∑ i, w j i • weights' i)
    simp only [smul_add, Finset.sum_add_distrib]
variable [Fintype J]
end DeletionCode.IntegerTorusMap


