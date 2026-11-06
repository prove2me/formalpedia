-- Prove2me | Definitions.Def_TC433_Algebra_Module_Submodule_Map_7a4c32f823
-- name    : TC433_Algebra_Module_Submodule_Map_7a4c32f823
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T17:32:29.322198+00:00
-- url     : https://prove2.me/theorems/508812e2-2010-4786-bf81-2f5396452ee7
-- title:
--   TauCeti: Algebra / Module / Submodule / Map
-- statement:
--   Compatibility port of the definitions and proved supporting lemmas in TauCeti.Algebra.Module.Submodule.Map for the concrete CFSG catalog. This module does not assert the classification theorem.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/6e0c6acab5f4c6f42e5f5bab9bd5e4e84f74c380/TauCeti/Algebra/Module/Submodule/Map.lean

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.Algebra.Module.Submodule.Range
public import Mathlib.Order.SupIndep
public import Mathlib.LinearAlgebra.Basis.Basic

/-!
# Finite families of submodules under a linear map

`Submodule.map` preserves arbitrary suprema (`Submodule.map_iSup`), and along an injective map it
also preserves infima (`Submodule.map_inf`) and hence disjointness (`Submodule.disjoint_map`).  This
file records what those facts say about a family of submodules indexed by a `Finset`: pushing it
forward along a linear map turns a spanning family into one spanning the range of the map, and along
an injective map it leaves an independent family independent.

The finite-set form is what a decomposition of a module into a `Finset` of submodules needs, as in
`TauCeti/RingTheory/KrullSchmidt/Existence.lean`, when it is transported along a linear map.

## Main results

* `LinearMap.sup_image_map_eq_range_of_sup_eq_top`: a finite family of submodules spanning the
  whole module is carried to one spanning the range of the map.
* `LinearMap.supIndep_image_map`: an injective linear map carries an independent finite
  family of submodules to an independent one.
* `Submodule.map_eq_span_basis`: the image of a based submodule is spanned by the images of
  its basis vectors.
-/

public section
set_option backward.isDefEq.respectTransparency.types false

namespace Submodule

/-- The image of a based submodule is spanned by the images of its basis vectors. -/
theorem map_eq_span_basis
    {R V W ι : Type*} [Semiring R] [AddCommMonoid V] [Module R V]
    [AddCommMonoid W] [Module R W]
    (p : Submodule R V) (b : Module.Basis ι R p) (f : V →ₗ[R] W) :
    p.map f = Submodule.span R (Set.range fun i => f (b i : V)) := by
  have h := congrArg (Submodule.map (f.comp p.subtype)) b.span_eq
  rw [Submodule.map_span, Submodule.map_top, LinearMap.range_comp,
    Submodule.range_subtype] at h
  simpa only [← Set.range_comp, Function.comp_def, LinearMap.comp_apply,
    Submodule.subtype_apply] using h.symm

end Submodule

namespace LinearMap

universe u v v'

variable {R : Type u} [Semiring R]
variable {M : Type v} [AddCommMonoid M] [Module R M]
variable {M' : Type v'} [AddCommMonoid M'] [Module R M']

/-- **A linear map carries a spanning finite family of submodules to a family spanning its
range**: the images of the members of a finite family with supremum `⊤` have supremum
`LinearMap.range f`. -/
theorem sup_image_map_eq_range_of_sup_eq_top [DecidableEq (Submodule R M')] (f : M →ₗ[R] M')
    {s : Finset (Submodule R M)} (hs : s.sup _root_.id = ⊤) :
    (s.image (Submodule.map f)).sup _root_.id = LinearMap.range f := by
  rw [Finset.sup_image]
  simpa only [Function.comp_def, id_eq, Finset.sup_eq_iSup, Submodule.map_iSup,
    Submodule.map_top] using congrArg (Submodule.map f) hs

/-- **An injective linear map preserves independence of a finite family of submodules**: the images
of the members are again independent. -/
theorem supIndep_image_map [DecidableEq (Submodule R M')] (f : M →ₗ[R] M')
    (hf : Function.Injective f) {s : Finset (Submodule R M)}
    (hs : s.SupIndep _root_.id) :
    (s.image (Submodule.map f)).SupIndep _root_.id := by
  refine Finset.SupIndep.image fun t hts P hP hPt ↦ ?_
  simpa only [Function.comp_def, id_eq, Finset.sup_eq_iSup, Submodule.map_iSup] using
    Submodule.disjoint_map hf (hs hts hP hPt)

end LinearMap


