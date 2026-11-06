-- Prove2me | Definitions.Def_TC433_Algebra_AlgebraicGroup_Torus_CharacterLattice_Basic_874c1bd346
-- name    : TC433_Algebra_AlgebraicGroup_Torus_CharacterLattice_Basic_874c1bd346
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T11:26:31.767257+00:00
-- url     : https://prove2.me/theorems/02ba3f46-000a-46c5-b199-f39401d1deb8
-- title:
--   TauCeti: Algebra / AlgebraicGroup / Torus / CharacterLattice / Basic
-- statement:
--   Compatibility port of the definitions and proved supporting lemmas in TauCeti.Algebra.AlgebraicGroup.Torus.CharacterLattice.Basic for the concrete CFSG catalog. This module does not assert the classification theorem.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/6e0c6acab5f4c6f42e5f5bab9bd5e4e84f74c380/TauCeti/Algebra/AlgebraicGroup/Torus/CharacterLattice/Basic.lean

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Definitions.Def_TC433_Algebra_AlgebraicGroup_DiagonalizableGroup_CharacterLattice_592740330c
public import Definitions.Def_TC433_Algebra_AlgebraicGroup_CommHopfAlgCat_CharacterLattice_Continuous_705115c8e9
public import Definitions.Def_TC433_Algebra_AlgebraicGroup_Torus_Basic_fbfd1066fd

/-!
# The character lattice of a torus

The geometric characters of a torus are the group-like elements of its coordinate algebra after
extension to an algebraic closure. The generic construction and its absolute-Galois action are in
`TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.CharacterLattice.Basic`.

The defining splitting over the algebraic closure identifies the underlying additive character
group, noncanonically, with a finite-rank free abelian group. The absolute-Galois action and its
continuity for the discrete topology are constructed in the generic character-group modules. An
equivariant classification of non-split tori is not formalized here.

## Main declarations

* `TauCeti.exists_characterLattice_addEquiv_of_torus`: the character lattice of any torus is
  finite-rank free.
* `TauCeti.characterLattice_module_free_of_torus`: a torus character lattice is a free `ℤ`-module.
* `TauCeti.characterLattice_module_finite_of_torus`: a torus character lattice is a finite
  `ℤ`-module.

## References

See J. S. Milne, *Algebraic Groups* (2017), Definitions 12.14 and 12.17, and W. C. Waterhouse,
*Introduction to Affine Group Schemes*, Chapter 2.
-/

public section
set_option backward.isDefEq.respectTransparency.types false

namespace TauCeti

universe u

/-- The character lattice of a torus is a finite-rank free abelian group. The equivalence is
noncanonical: it uses the splitting over the chosen algebraic closure from the torus predicate. -/
theorem exists_characterLattice_addEquiv_of_torus (k : Type u) [Field k]
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) (hH : torusCommHopfAlgProperty k H) :
    ∃ n : ℕ, Nonempty
      (CommHopfAlgCat.additiveCharacterGroup H.obj ≃+ (Fin n →₀ ℤ)) := by
  rw [torusCommHopfAlgProperty_iff] at hH
  obtain ⟨n, ⟨i⟩⟩ := hH
  exact ⟨n, ⟨(MulEquiv.toAdditive
    (CommHopfAlgCat.geometricCharacterGroupEquivOfIso k H
      (SplitTorus.characterGroup (ULift.{u} (Fin n))) i)).trans
      ((AddEquiv.additiveMultiplicative (ULift.{u} (Fin n) →₀ ℤ)).trans
        (Finsupp.domCongr Equiv.ulift))⟩⟩

/-- The character lattice of a torus is a free `ℤ`-module. -/
theorem characterLattice_module_free_of_torus (k : Type u) [Field k]
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) (hH : torusCommHopfAlgProperty k H) :
    Module.Free ℤ (CommHopfAlgCat.additiveCharacterGroup H.obj) := by
  obtain ⟨n, ⟨e⟩⟩ := exists_characterLattice_addEquiv_of_torus k H hH
  exact Module.Free.of_equiv e.toIntLinearEquiv.symm

/-- The character lattice of a torus is a finite `ℤ`-module. -/
theorem characterLattice_module_finite_of_torus (k : Type u) [Field k]
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) (hH : torusCommHopfAlgProperty k H) :
    Module.Finite ℤ (CommHopfAlgCat.additiveCharacterGroup H.obj) := by
  obtain ⟨n, ⟨e⟩⟩ := exists_characterLattice_addEquiv_of_torus k H hH
  exact Module.Finite.equiv e.toIntLinearEquiv.symm

end TauCeti


