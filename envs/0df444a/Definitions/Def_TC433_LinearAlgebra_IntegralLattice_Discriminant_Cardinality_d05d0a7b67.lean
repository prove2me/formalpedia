-- Prove2me | Definitions.Def_TC433_LinearAlgebra_IntegralLattice_Discriminant_Cardinality_d05d0a7b67
-- name    : TC433_LinearAlgebra_IntegralLattice_Discriminant_Cardinality_d05d0a7b67
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T17:13:27.15455+00:00
-- url     : https://prove2.me/theorems/c84a2712-3a0c-46ee-af6e-93dbaf3b5dcd
-- title:
--   TauCeti: LinearAlgebra / IntegralLattice / Discriminant / Cardinality
-- statement:
--   Compatibility port of the definitions and proved supporting lemmas in TauCeti.LinearAlgebra.IntegralLattice.Discriminant.Cardinality for the concrete CFSG catalog. This module does not assert the classification theorem.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/6e0c6acab5f4c6f42e5f5bab9bd5e4e84f74c380/TauCeti/LinearAlgebra/IntegralLattice/Discriminant/Cardinality.lean

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
public import Definitions.Def_TC433_LinearAlgebra_IntegralLattice_Discriminant_Group_ee427d755d
public import Definitions.Def_TC433_LinearAlgebra_IntegralLattice_Gram_751af3ecf1

/-!
# Cardinality of an integral lattice's discriminant group

For a nondegenerate integral lattice `L`, the order of its discriminant group is the absolute
value of any Gram determinant:

```text
#(Lᵛ / L) = |det Gram(L)|.
```

The proof uses Mathlib's quotient-cardinality theorem for full-rank free `ℤ`-submodules.  Given
a carrier basis `b`, the corresponding bilinear dual basis is a basis of `Lᵛ`, while `b` itself
gives a basis of the copy of `L` inside `Lᵛ`.  The change-of-basis matrix between them is the
Gram matrix of `b`: the coefficient of `b j` along the dual vector indexed by `i` is
`B(b j, b i)`, which equals `B(b i, b j)` by symmetry.

## Main results

* `TauCeti.IntegralLattice.dualCarrierBasis_toMatrix_carrierInDualBasis`: the associated
  change-of-basis matrix is the Gram matrix.
* `TauCeti.IntegralLattice.natCard_discriminantGroup_eq_natAbs_gramDet`: the basis-relative
  cardinality formula.
* `TauCeti.IntegralLattice.natCard_discriminantGroup`: the discriminant-group cardinality is the
  lattice discriminant.
* `TauCeti.IntegralLattice.natCard_discriminantGroup_ofGramMatrix`: the formula for a lattice
  constructed from a nonsingular integral symmetric matrix.

## References

* W. Ebeling, *Lattices and Codes*, Chapter 1.
* `TauCetiRoadmap/IntegralLattices/README.md` (Layer 2).
* `TauCetiRoadmap/IntegralLattices/Suggested.lean`.
-/

public section
set_option backward.isDefEq.respectTransparency.types false

open Module

namespace TauCeti.IntegralLattice

universe u v

variable {V : Type u} [AddCommGroup V] [Module ℚ V]

open Classical in
/-- The change-of-basis matrix from the dual basis to the embedded carrier basis is the Gram
matrix. -/
theorem dualCarrierBasis_toMatrix_carrierInDualBasis (L : IntegralLattice V)
    [L.IsNondegenerate] {ι : Type v} [Finite ι]
    (b : Basis ι ℤ L) :
    (L.dualCarrierBasis b).toMatrix
        ((↑) ∘ L.carrierInDualBasis b) = L.gramMatrix b := by
  ext i j
  rw [Basis.toMatrix_apply]
  apply Int.cast_injective (α := ℚ)
  rw [L.intCast_gramMatrix_apply]
  simp only [L.dualCarrierBasis_repr, Function.comp_apply, Basis.dualBasis_repr,
    L.dualPairingEquiv_cast, coe_carrierInDualBasis_apply]
  exact L.isSymm.eq _ _

open Classical in
/-- The determinant of the carrier basis inside the dual basis is the signed Gram determinant. -/
theorem dualCarrierBasis_det_carrierInDualBasis (L : IntegralLattice V)
    [L.IsNondegenerate] {ι : Type v} [Fintype ι]
    (b : Basis ι ℤ L) :
    (L.dualCarrierBasis b).det ((↑) ∘ L.carrierInDualBasis b) = L.gramDet b := by
  rw [Basis.det_apply, L.dualCarrierBasis_toMatrix_carrierInDualBasis b, L.gramDet_def]

open Classical in
/-- The discriminant group has cardinality equal to the absolute value of the Gram determinant in
any carrier basis. -/
theorem natCard_discriminantGroup_eq_natAbs_gramDet (L : IntegralLattice V)
    [L.IsNondegenerate] {ι : Type v} [Fintype ι]
    (b : Basis ι ℤ L) :
    Nat.card L.DiscriminantGroup = (L.gramDet b).natAbs := by
  rw [← L.dualCarrierBasis_det_carrierInDualBasis b]
  exact (Submodule.natAbs_det_basis_change (L.dualCarrierBasis b) L.carrierInDual
    (L.carrierInDualBasis b)).symm

/-- **The order of the discriminant group is the lattice discriminant.** -/
theorem natCard_discriminantGroup (L : IntegralLattice V) [L.IsNondegenerate] :
    Nat.card L.DiscriminantGroup = L.discriminant := by
  classical
  rw [L.natCard_discriminantGroup_eq_natAbs_gramDet (Module.Free.chooseBasis ℤ L),
    L.discriminant_eq_natAbs_gramDet (Module.Free.chooseBasis ℤ L)]

open Classical in
/-- The discriminant group of a lattice constructed from a nonsingular integral symmetric matrix
has cardinality equal to the absolute value of that matrix's determinant. -/
@[simp]
theorem natCard_discriminantGroup_ofGramMatrix {ι : Type v} [Fintype ι]
    (b : Basis ι ℚ V) (G : Matrix ι ι ℤ) (hG : G.IsSymm) (hdet : G.det ≠ 0) :
    Nat.card (ofGramMatrix b G hG).DiscriminantGroup = G.det.natAbs := by
  have : (ofGramMatrix b G hG).IsNondegenerate :=
    isNondegenerate_ofGramMatrix b G hG hdet
  rw [natCard_discriminantGroup, discriminant_ofGramMatrix]

end TauCeti.IntegralLattice


