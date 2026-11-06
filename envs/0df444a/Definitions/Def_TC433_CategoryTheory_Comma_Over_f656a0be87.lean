-- Prove2me | Definitions.Def_TC433_CategoryTheory_Comma_Over_f656a0be87
-- name    : TC433_CategoryTheory_Comma_Over_f656a0be87
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T10:39:17.113199+00:00
-- url     : https://prove2.me/theorems/c9f32406-a87e-4e56-b416-764146b629d2
-- title:
--   TauCeti: CategoryTheory / Comma / Over
-- statement:
--   Compatibility port of the definitions and proved supporting lemmas in TauCeti.CategoryTheory.Comma.Over for the concrete CFSG catalog. This module does not assert the classification theorem.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/6e0c6acab5f4c6f42e5f5bab9bd5e4e84f74c380/TauCeti/CategoryTheory/Comma/Over.lean

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
# Isomorphisms of objects over a base

An isomorphism in `Over X` is an isomorphism of the underlying objects. Mathlib records this
for comma categories (`CategoryTheory.Comma.instIsIsoLeft`) and for arrow categories
(`CategoryTheory.Arrow.isIso_left`), but `Over X` is a `def` rather than an abbreviation for
a comma category, so instance search does not see through it to the comma statement. This file
supplies the missing `Over` form, which lets `infer_instance` discharge `IsIso φ.left` goals
that otherwise have to name the forgetful functor by hand.

## Main declarations

* `CategoryTheory.Over.isIso_left`: the underlying morphism of an isomorphism over a base is
  an isomorphism.
-/

public section
set_option backward.isDefEq.respectTransparency.types false

universe v u

namespace CategoryTheory

namespace Over

/-- The underlying morphism of an isomorphism in `Over X` is an isomorphism. -/
instance isIso_left {T : Type u} [Category.{v} T] {X : T} {f g : Over X} (φ : f ⟶ g)
    [IsIso φ] : IsIso φ.left :=
  (Over.forget X).map_isIso φ

end Over

end CategoryTheory


