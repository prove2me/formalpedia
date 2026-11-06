-- Prove2me | Definitions.Def_TC433_LinearAlgebra_Matrix_GeneralLinearGroup_Map_f923b9e09c
-- name    : TC433_LinearAlgebra_Matrix_GeneralLinearGroup_Map_f923b9e09c
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T10:19:47.851724+00:00
-- url     : https://prove2.me/theorems/e1eb4904-cb9b-472f-883c-aced6218a9c7
-- title:
--   TauCeti: LinearAlgebra / Matrix / GeneralLinearGroup / Map
-- statement:
--   Compatibility port of the definitions and proved supporting lemmas in TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Map for the concrete CFSG catalog. This module does not assert the classification theorem.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/6e0c6acab5f4c6f42e5f5bab9bd5e4e84f74c380/TauCeti/LinearAlgebra/Matrix/GeneralLinearGroup/Map.lean

/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Change of scalars on general linear groups

`Matrix.GeneralLinearGroup.map f : GL n R →* GL n S` applies a ring hom `f : R →+* S` entrywise.
Mathlib gives its functoriality (`map_id`, `map_comp`, `map_comp_apply`) but says nothing about
injectivity, nor about how the map interacts with the positive-determinant subgroup — both of
which a construction transporting a group of matrices along a change of scalars needs.

## Main results

* `Matrix.GeneralLinearGroup.map_injective`: entrywise application of an injective ring hom is
  injective on general linear groups.
* `Matrix.GeneralLinearGroup.map_mem_glpos`: a strictly monotone ring hom carries `GLPos` to
  `GLPos`, so a change of scalars restricts to the positive-determinant subgroups.
* `Subgroup.map_mapGL`: extending a subgroup of `SL(n, R)` to `GL n S` and then to `GL n T`
  agrees with extending it directly to `GL n T`.
-/

public section
set_option backward.isDefEq.respectTransparency.types false

namespace Matrix.GeneralLinearGroup

variable {n R S : Type*} [DecidableEq n] [Fintype n] [CommRing R] [CommRing S]

/-- **Entrywise application of an injective ring hom is injective on `GL n`.** A matrix over `R`
is determined by its image over `S`, and a unit by its underlying matrix. -/
theorem map_injective {f : R →+* S} (hf : Function.Injective f) :
    Function.Injective (Matrix.GeneralLinearGroup.map (n := n) f) :=
  Units.map_injective (Matrix.map_injective hf)

section StrictOrdered

variable [LinearOrder R] [IsStrictOrderedRing R] [LinearOrder S] [IsStrictOrderedRing S]

/-- A strictly monotone change of scalars restricts to the positive-determinant subgroups.

This is the side condition for cutting `Matrix.GeneralLinearGroup.map f` down to a homomorphism
`GLPos n R →* GLPos n S`; for `f = algebraMap ℚ ℝ` the hypothesis is `Rat.cast_strictMono`.
Contrast `Matrix.SpecialLinearGroup.toGLPos`, which lands in `GLPos` because the determinant
is `1`: here it is only positive, and monotonicity of `f` is what keeps it so. -/
theorem map_mem_glpos {f : R →+* S} (hf : StrictMono f) {g : GL n R} (hg : g ∈ GLPos n R) :
    g.map f ∈ GLPos n S := by
  -- the determinant commutes with the ring hom, and a strictly monotone ring hom is positive
  simpa [GeneralLinearGroup.map_det] using hf.lt_iff_lt.mpr hg

end StrictOrdered

end Matrix.GeneralLinearGroup

namespace Subgroup

open Matrix.SpecialLinearGroup in
/-- Extending a subgroup of the special linear group first to `S` and then to `T` agrees with
extending it directly to `T`. This is the subgroup form of `Matrix.SpecialLinearGroup.map_mapGL`,
used for instance for integral levels extended to `ℚ` and then to `ℝ`. -/
@[simp] theorem map_mapGL {n R S T : Type*} [DecidableEq n] [Fintype n] [CommRing R]
    [CommRing S] [CommRing T] [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    (G : Subgroup (Matrix.SpecialLinearGroup n R)) :
    (G.map (mapGL S)).map (Matrix.GeneralLinearGroup.map (algebraMap S T)) = G.map (mapGL T) := by
  rw [Subgroup.map_map]
  exact congrArg (Subgroup.map · G) (MonoidHom.ext fun g ↦ Matrix.SpecialLinearGroup.map_mapGL g)

end Subgroup


