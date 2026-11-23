-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ExistenceOfSandwichStatement
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ExistenceOfSandwichStatement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T09:52:14.870027+00:00
-- url     : https://prove2.me/theorems/5e3df0d7-696d-442b-a94d-d79956b87435
-- title:
--   Existence Of Sandwich Statement
-- statement:
--   Definitions and structural lemmas for Existence Of Sandwich Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ExistenceOfSandwichStatement.lean

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Rg.FlB
noncomputable section
namespace GlobalTheory.CompanionTheory.RgFl.MaxLat
variable {L : Type} [NontriviallyNormedField L] [IsUltrametricDist L]
  {V : Type} [AddCommGroup V] [Module L V]
def hLin {s : L →+* L} {h : V → V → L} (hh : IsHerm s h) (z : V) : V →ₗ[L] L where
  toFun := h z
  map_add' := hh.1 z
  map_smul' a y := by simpa using hh.2.1 a z y
def ball {ι : Type} (b : Module.Basis ι L V) : AddSubgroup V where
  carrier := {x | ∀ i, ‖b.repr x i‖ ≤ 1}
  add_mem' {x y} hx hy i := by
    simpa using (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hx i) (hy i))
  zero_mem' i := by simp
  neg_mem' {x} hx i := by simpa using hx i
end GlobalTheory.CompanionTheory.RgFl.MaxLat
end


