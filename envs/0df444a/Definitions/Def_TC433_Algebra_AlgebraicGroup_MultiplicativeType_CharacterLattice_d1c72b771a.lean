-- Prove2me | Definitions.Def_TC433_Algebra_AlgebraicGroup_MultiplicativeType_CharacterLattice_d1c72b771a
-- name    : TC433_Algebra_AlgebraicGroup_MultiplicativeType_CharacterLattice_d1c72b771a
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T11:25:27.489971+00:00
-- url     : https://prove2.me/theorems/c1dc2819-1443-4956-98e7-56bc7921075f
-- title:
--   TauCeti: Algebra / AlgebraicGroup / MultiplicativeType / CharacterLattice
-- statement:
--   Compatibility port of the definitions and proved supporting lemmas in TauCeti.Algebra.AlgebraicGroup.MultiplicativeType.CharacterLattice for the concrete CFSG catalog. This module does not assert the classification theorem.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/6e0c6acab5f4c6f42e5f5bab9bd5e4e84f74c380/TauCeti/Algebra/AlgebraicGroup/MultiplicativeType/CharacterLattice.lean

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Definitions.Def_TC433_Algebra_AlgebraicGroup_DiagonalizableGroup_CharacterLattice_592740330c
public import Definitions.Def_TC433_Algebra_AlgebraicGroup_MultiplicativeType_Basic_45b9f95108

/-!
# Character groups of groups of multiplicative type

The geometric character group of a finite-type commutative Hopf algebra of multiplicative type
is finitely generated. Indeed, the multiplicative-type hypothesis says that the group-like
elements span the coordinate algebra after extension to an algebraic closure, and finite type
then forces the group of group-like elements to be finitely generated.

## Main declarations

* `TauCeti.CommHopfAlgCat.exists_geometricCharacterGroup_mulEquiv_of_multiplicativeType`: a
  multiplicative-type character group is equivalent to a finitely generated commutative group.
* `TauCeti.CommHopfAlgCat.geometricCharacterGroup_fg_of_multiplicativeType`: the geometric
  character group of a group of multiplicative type is finitely generated.
* `TauCeti.CommHopfAlgCat.additiveCharacterGroup_fg_of_multiplicativeType`: its additive form is
  finitely generated.

## References

See J. S. Milne, *Algebraic Groups* (2017), Definition 12.14.
-/

public section
set_option backward.isDefEq.respectTransparency.types false

namespace TauCeti

universe u

namespace CommHopfAlgCat

variable {k : Type u} [Field k]

/-- The geometric character group of a finite-type commutative Hopf algebra of multiplicative
type is equivalent to a finitely generated commutative group. -/
theorem exists_geometricCharacterGroup_mulEquiv_of_multiplicativeType
    (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (hH : multiplicativeTypeCommHopfAlgProperty k H) :
    ∃ G : FGCommGrpCat.{u}, Nonempty (geometricCharacterGroup H.obj ≃* G) := by
  rw [multiplicativeTypeCommHopfAlgProperty_iff_exists_iso_coordinateRing] at hH
  obtain ⟨G, ⟨i⟩⟩ := hH
  exact ⟨G, ⟨geometricCharacterGroupEquivOfIso k H G i⟩⟩

/-- The geometric character group of a finite-type commutative Hopf algebra of multiplicative
type is finitely generated. -/
theorem geometricCharacterGroup_fg_of_multiplicativeType
    (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (hH : multiplicativeTypeCommHopfAlgProperty k H) :
    Group.FG (geometricCharacterGroup H.obj) := by
  obtain ⟨G, ⟨e⟩⟩ := exists_geometricCharacterGroup_mulEquiv_of_multiplicativeType H hH
  exact Group.fg_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective

/-- The additive character group of a finite-type commutative Hopf algebra of multiplicative type
is finitely generated. -/
theorem additiveCharacterGroup_fg_of_multiplicativeType
    (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (hH : multiplicativeTypeCommHopfAlgProperty k H) :
    AddGroup.FG (additiveCharacterGroup H.obj) := by
  let _ : Group.FG (geometricCharacterGroup H.obj) :=
    geometricCharacterGroup_fg_of_multiplicativeType H hH
  infer_instance

end CommHopfAlgCat

end TauCeti


