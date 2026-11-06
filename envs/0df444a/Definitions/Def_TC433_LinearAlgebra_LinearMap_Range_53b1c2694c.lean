-- Prove2me | Definitions.Def_TC433_LinearAlgebra_LinearMap_Range_53b1c2694c
-- name    : TC433_LinearAlgebra_LinearMap_Range_53b1c2694c
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T17:31:46.50179+00:00
-- url     : https://prove2.me/theorems/c1889379-6779-47e0-b510-bf9ce1f9ab56
-- title:
--   TauCeti: LinearAlgebra / LinearMap / Range
-- statement:
--   Compatibility port of the definitions and proved supporting lemmas in TauCeti.LinearAlgebra.LinearMap.Range for the concrete CFSG catalog. This module does not assert the classification theorem.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/6e0c6acab5f4c6f42e5f5bab9bd5e4e84f74c380/TauCeti/LinearAlgebra/LinearMap/Range.lean

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Submodule.Range

/-!
# Ranges of composite linear maps

Range identities for factoring a composite through a linear map's image.
-/

public section
set_option backward.isDefEq.respectTransparency.types false

theorem LinearMap.subtype_comp_rangeRestrict {R M N : Type*} [Semiring R]
    [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N] (f : M →ₗ[R] N) :
    f.range.subtype.comp f.rangeRestrict = f := rfl


namespace LinearMap

/-- Composing through the range restriction does not change a composite linear map's range. -/
theorem range_comp_rangeRestrict
    {R V W N : Type*} [Semiring R]
    [AddCommMonoid V] [Module R V] [AddCommMonoid W] [Module R W]
    [AddCommMonoid N] [Module R N]
    (f : V →ₗ[R] W) (g : W →ₗ[R] N) :
    Set.range (g.comp f) = Set.range (g.comp f.range.subtype) := by
  have h : (g.comp f).range = (g.comp f.range.subtype).range := by
    simpa only [LinearMap.comp_assoc, LinearMap.subtype_comp_rangeRestrict] using
      (LinearMap.range_comp_of_range_eq_top (g.comp f.range.subtype)
        (LinearMap.range_rangeRestrict f))
  simpa only [LinearMap.coe_range] using
    congrArg (fun p : Submodule R N => (p : Set N)) h

/-- Mapping a submodule into a linear map's range does not change the composite range. -/
theorem range_comp_map_subtype
    {R V W N : Type*} [Semiring R]
    [AddCommMonoid V] [Module R V] [AddCommMonoid W] [Module R W]
    [AddCommMonoid N] [Module R N]
    (f : V →ₗ[R] W) (I : Submodule R V) (g : W →ₗ[R] N) :
    Set.range (g.comp (f.comp I.subtype)) =
      Set.range ((g.comp f.range.subtype).comp (I.map f.rangeRestrict).subtype) := by
  have h : (g.comp (f.comp I.subtype)).range =
      ((g.comp f.range.subtype).comp (I.map f.rangeRestrict).subtype).range := by
    simp only [LinearMap.range_comp, Submodule.range_subtype, ← Submodule.map_comp,
      LinearMap.comp_assoc, LinearMap.subtype_comp_rangeRestrict]
  simpa only [LinearMap.coe_range] using
    congrArg (fun p : Submodule R N => (p : Set N)) h

end LinearMap


