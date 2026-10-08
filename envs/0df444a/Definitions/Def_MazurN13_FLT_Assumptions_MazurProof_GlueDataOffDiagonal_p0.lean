-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_GlueDataOffDiagonal_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_GlueDataOffDiagonal_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T22:31:23.279976+00:00
-- url     : https://prove2.me/theorems/7f5a3f99-dcce-4dbb-bec3-cb8ae63a1ad0
-- title:
--   FLT.Assumptions.MazurProof.GlueDataOffDiagonal source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.GlueDataOffDiagonal

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.GlueDataOffDiagonal
Original leading source comments and nonproject imports are retained below. -/
import Mathlib.CategoryTheory.GlueData

set_option autoImplicit false




/-!
# Off-diagonal adapters for `GlueData.ofGlueData'`

The full glue data constructed from `GlueData'` stores its overlap
objects behind a diagonal/off-diagonal conditional.  For distinct
indices, this file gives the canonical comparison with the original
off-diagonal object and records its compatibility with the transition
map.
-/

noncomputable section

open CategoryTheory

namespace CategoryTheory.GlueData'

universe v u

variable {C : Type u} [Category.{v} C] (D : GlueData' C)

open scoped Classical

/-- The canonical identification of an original off-diagonal overlap
with the corresponding overlap of `GlueData.ofGlueData'`. -/
def offDiagonalIso {i j : D.J} (h : i ≠ j) :
    D.V i j h ≅ (GlueData.ofGlueData' D).V (i, j) :=
  eqToIso (dif_neg h).symm

/-- The canonical off-diagonal identification recovers the original
overlap inclusion. -/
@[simp, reassoc]
theorem offDiagonalIso_hom_f {i j : D.J} (h : i ≠ j) :
    (offDiagonalIso D h).hom ≫ (GlueData.ofGlueData' D).f i j =
      D.f i j h := by
  simp [offDiagonalIso, GlueData.ofGlueData', GlueData'.f', h]

/-- The canonical off-diagonal identification intertwines the original
and promoted transition maps. -/
@[reassoc]
theorem offDiagonalIso_hom_t {i j : D.J} (h : i ≠ j) :
    (offDiagonalIso D h).hom ≫ (GlueData.ofGlueData' D).t i j =
      D.t i j h ≫ (offDiagonalIso D h.symm).hom := by
  simp [offDiagonalIso, GlueData.ofGlueData', h]

end CategoryTheory.GlueData'


