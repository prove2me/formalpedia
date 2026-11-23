-- Prove2me | Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Tiling
-- name    : AM_Mathlib_Combinatorics_Tiling_Function_Tiling
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T05:57:18.745808+00:00
-- url     : https://prove2.me/theorems/71c731dd-0d91-49bc-aff6-3a6f77511856
-- title:
--   Tiling
-- statement:
--   Definitions and structural lemmas for Tiling, from jsm28/AperiodicMonotilesLean contributors (see pinned LICENSE and source headers)'s pinned Periodicity and isohedrality of tilings development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Function/Tiling.lean

module
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Disjoint
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Union
set_option autoImplicit false
@[expose] public section
@[expose] public section
noncomputable section
namespace DiscreteTiling
open Function
open scoped Pointwise
variable {G X ιₚ : Type*} [Group G] [MulAction G X]
variable {ps : Protoset G X ιₚ} {ιₜ : Type*}
namespace TileSet
def IsTilingOf : VarTileSetFunction (Set X) ps Prop ⊤ :=
  (TileSet.Disjoint.toVarTileSetFunction (Set X)).comp₂ UnionEq (· ∧ ·)
def IsTiling : TileSetFunction ps Prop ⊤ := TileSet.Disjoint.comp₂ (UnionEqUniv) (· ∧ ·)
end TileSet
end DiscreteTiling


