-- Prove2me | Definitions.Def_TC433_Algebra_AlgebraicGroup_Torus_Cocharacter_Basic_581a63d325
-- name    : TC433_Algebra_AlgebraicGroup_Torus_Cocharacter_Basic_581a63d325
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T11:28:17.485178+00:00
-- url     : https://prove2.me/theorems/4de57ab5-05d2-41e2-80db-2916f9f522c1
-- title:
--   TauCeti: Algebra / AlgebraicGroup / Torus / Cocharacter / Basic
-- statement:
--   Compatibility port of the definitions and proved supporting lemmas in TauCeti.Algebra.AlgebraicGroup.Torus.Cocharacter.Basic for the concrete CFSG catalog. This module does not assert the classification theorem.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/6e0c6acab5f4c6f42e5f5bab9bd5e4e84f74c380/TauCeti/Algebra/AlgebraicGroup/Torus/Cocharacter/Basic.lean

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.PerfectPairing.Basic
public import Definitions.Def_TC433_Algebra_AlgebraicGroup_MultiplicativeType_Cocharacter_d7ccec5273
public import Definitions.Def_TC433_Algebra_AlgebraicGroup_Torus_CharacterLattice_Basic_874c1bd346

/-!
# Cocharacter lattices of tori

The geometric cocharacter lattice, its dual comparison, Galois action, and evaluation pairing are
defined for every group of multiplicative type in
`TauCeti.Algebra.AlgebraicGroup.MultiplicativeType.Cocharacter`. This file specializes that API to
tori and uses the finite freeness of their character lattices to prove perfectness, finite
freeness, and rank equality for their cocharacter lattices.

## Main declarations

* `TauCeti.TorusCommHopfAlgCat.toMultiplicativeTypeCommHopfAlgCat`: a torus regarded as a group of
  multiplicative type.
* `TauCeti.TorusCommHopfAlgCat.instCharacterCocharacterPairingIsPerfPair`: the character--
  cocharacter pairing of a torus is perfect.
* `TauCeti.TorusCommHopfAlgCat.cocharacterLattice_module_free` and
  `TauCeti.TorusCommHopfAlgCat.cocharacterLattice_module_finite`: the cocharacter lattice is
  finite free over `ℤ`.

## References

See J. S. Milne, *Algebraic Groups* (2017), Definitions 12.14 and 12.17.
-/

public section
set_option backward.isDefEq.respectTransparency.types false

namespace TauCeti

universe u

namespace TorusCommHopfAlgCat

variable {k : Type u} [Field k]

/-- A torus regarded as a group of multiplicative type. -/
noncomputable abbrev toMultiplicativeTypeCommHopfAlgCat (T : TorusCommHopfAlgCat k) :
    MultiplicativeTypeCommHopfAlgCat k :=
  ⟨T.obj, torusCommHopfAlgProperty.multiplicativeType k T.obj T.property⟩

/-- The character--cocharacter pairing of a torus is perfect. -/
noncomputable instance instCharacterCocharacterPairingIsPerfPair (T : TorusCommHopfAlgCat k) :
    (MultiplicativeTypeCommHopfAlgCat.characterCocharacterPairing
      (toMultiplicativeTypeCommHopfAlgCat T)).IsPerfPair := by
  let _ := characterLattice_module_free_of_torus k T.obj T.property
  let _ := characterLattice_module_finite_of_torus k T.obj T.property
  apply LinearMap.IsPerfPair.congr
    (p := Module.Dual.eval ℤ (CommHopfAlgCat.additiveCharacterGroup T.obj.obj))
    (LinearEquiv.refl ℤ _) (MultiplicativeTypeCommHopfAlgCat.cocharacterLatticeLinearEquivDual
      (toMultiplicativeTypeCommHopfAlgCat T))
  ext x f
  simp

/-- The cocharacter lattice of a torus is free over the integers. -/
theorem cocharacterLattice_module_free (T : TorusCommHopfAlgCat k) :
    Module.Free ℤ (MultiplicativeTypeCommHopfAlgCat.cocharacterLattice
      (toMultiplicativeTypeCommHopfAlgCat T)) := by
  let _ := characterLattice_module_free_of_torus k T.obj T.property
  let _ := characterLattice_module_finite_of_torus k T.obj T.property
  exact Module.Free.of_equiv
    (MultiplicativeTypeCommHopfAlgCat.cocharacterLatticeLinearEquivDual
      (toMultiplicativeTypeCommHopfAlgCat T)).symm

/-- The cocharacter lattice of a torus is finitely generated over the integers. -/
theorem cocharacterLattice_module_finite (T : TorusCommHopfAlgCat k) :
    Module.Finite ℤ (MultiplicativeTypeCommHopfAlgCat.cocharacterLattice
      (toMultiplicativeTypeCommHopfAlgCat T)) := by
  let _ := characterLattice_module_free_of_torus k T.obj T.property
  let _ := characterLattice_module_finite_of_torus k T.obj T.property
  exact Module.Finite.equiv
    (MultiplicativeTypeCommHopfAlgCat.cocharacterLatticeLinearEquivDual
      (toMultiplicativeTypeCommHopfAlgCat T)).symm

/-- The character and cocharacter lattices of a torus have the same rank. -/
theorem finrank_cocharacterLattice_eq_characterLattice (T : TorusCommHopfAlgCat k) :
    Module.finrank ℤ (MultiplicativeTypeCommHopfAlgCat.cocharacterLattice
      (toMultiplicativeTypeCommHopfAlgCat T)) =
      Module.finrank ℤ (CommHopfAlgCat.additiveCharacterGroup T.obj.obj) := by
  let _ := characterLattice_module_free_of_torus k T.obj T.property
  let _ := characterLattice_module_finite_of_torus k T.obj T.property
  exact (Module.finrank_of_isPerfPair
    (MultiplicativeTypeCommHopfAlgCat.characterCocharacterPairing
      (toMultiplicativeTypeCommHopfAlgCat T))).symm

/-- A torus cocharacter lattice is noncanonically a finite-rank free abelian group. -/
theorem exists_cocharacterLattice_linearEquiv (T : TorusCommHopfAlgCat k) :
    ∃ n : ℕ, Nonempty
      (MultiplicativeTypeCommHopfAlgCat.cocharacterLattice
        (toMultiplicativeTypeCommHopfAlgCat T) ≃ₗ[ℤ] (Fin n → ℤ)) := by
  obtain ⟨n, ⟨e⟩⟩ := exists_characterLattice_addEquiv_of_torus k T.obj T.property
  exact ⟨n, ⟨
    (MultiplicativeTypeCommHopfAlgCat.cocharacterLatticeLinearEquivDual
      (toMultiplicativeTypeCommHopfAlgCat T)).trans
        (e.toIntLinearEquiv.symm.dualMap.trans (Finsupp.llift ℤ ℤ ℤ (Fin n)).symm)⟩⟩

end TorusCommHopfAlgCat

end TauCeti


