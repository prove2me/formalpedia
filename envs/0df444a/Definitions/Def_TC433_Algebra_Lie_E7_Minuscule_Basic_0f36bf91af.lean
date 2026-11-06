-- Prove2me | Definitions.Def_TC433_Algebra_Lie_E7_Minuscule_Basic_0f36bf91af
-- name    : TC433_Algebra_Lie_E7_Minuscule_Basic_0f36bf91af
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T17:02:49.542195+00:00
-- url     : https://prove2.me/theorems/0ce9de39-9ce7-41e3-b32e-bbea06d8bf48
-- title:
--   TauCeti: Algebra / Lie / E7 / Minuscule / Basic
-- statement:
--   Compatibility port of the definitions and proved supporting lemmas in TauCeti.Algebra.Lie.E7.Minuscule.Basic for the concrete CFSG catalog. This module does not assert the classification theorem.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/6e0c6acab5f4c6f42e5f5bab9bd5e4e84f74c380/TauCeti/Algebra/Lie/E7/Minuscule/Basic.lean

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Definitions.Def_TC433_Algebra_Lie_Presentation_MinusculeWeightTable_Basic_5da9994795
public import Definitions.Def_TC433_LinearAlgebra_RootSystem_SimplyConnectedRootDatum_E7_MinusculeWeight_c01675d0bb

/-!
# The integral minuscule representation of type E7

This file realizes the Chevalley generators of type `E₇` on the fifty-six-element weight
diagram `TauCeti.DynkinType.e7MinusculeWeight`. On the coordinate vector belonging to a weight
`lambda`, the Cartan generator `H_i` acts by the simple-coroot coordinate `lambda_i`; the raising
generator `E_i` carries `lambda` to its simple reflection when `lambda_i = -1`; and the lowering
generator `F_i` makes the reverse move when `lambda_i = 1`.

The resulting integer matrices satisfy the Chevalley--Serre relations for the Bourbaki Cartan
matrix. The universal property of the Serre presentation gives the explicit integral
fifty-six-dimensional minuscule representation. Each raising and lowering matrix squares to
zero. See `TauCeti.Algebra.Lie.E7.Minuscule.AdmissibleLattice` for the rational extension and
the admissibility of its coordinate lattice.

No identification with the abstract irreducible highest-weight module is asserted here. The
construction is explicit: every matrix entry is read from the already audited weight and
reflection tables.

## Main definitions

* `TauCeti.E7Minuscule.cartanMatrix`, `raisingMatrix`, and `loweringMatrix`: the integral Cartan,
  raising, and lowering matrices.
* `TauCeti.E7Minuscule.isSl2Triple`: the three matrices at a simple node form an `sl₂` triple.
* `TauCeti.E7Minuscule.isSerreSystem`: the Chevalley--Serre relations between them over `ℤ`.
* `TauCeti.E7Minuscule.serreRepresentation`: the induced representation of the type-`E₇` Serre
  Lie algebra.

## References

The numbering and weight diagram follow Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*,
Plate VI. The minuscule action follows J. E. Humphreys, *Introduction to Lie Algebras and
Representation Theory*, §13.4, and J. C. Jantzen, *Representations of Algebraic Groups*, II.2.

This advances the explicit Chevalley--Demazure construction in Layer 9 of
`TauCetiRoadmap/ReductiveGroups/README.md`. Its consumer is milestone L0 of
`TauCetiRoadmap/CFSGStatement/README.md`, which needs an explicit simply connected type-`E₇`
carrier.
-/

public section
set_option backward.isDefEq.respectTransparency.types false

open scoped Matrix

namespace TauCeti.E7Minuscule

open LieAlgebra TauCeti.DynkinType

attribute [local instance 100] LieRing.ofAssociativeRing

/-! ## The weight table -/

/-- The coordinate change under a simple reflection, in the fundamental-weight basis. -/
private theorem e7MinusculeWeight_reflection_apply (i : Fin 7) (a : Fin 56) (j : Fin 7) :
    e7MinusculeWeight (e7MinusculeReflection i a) j =
      e7MinusculeWeight a j - e7MinusculeWeight a i * CartanMatrix.E 7 i j := by
  have h := congrFun (e7MinusculeWeight_reflection i a) j
  rw [root_e7SimpleIndex] at h
  simpa only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] using h

/-- **The fifty-six minuscule weights of type `E₇`, as a minuscule weight table.** -/
def weightTable : TauCeti.MinusculeWeightTable (Fin 7) (Fin 56) where
  cartanMatrix := CartanMatrix.E 7
  weight := e7MinusculeWeight
  reflection i := e7MinusculeReflection i
  cartanMatrix_diag := CartanMatrix.E_diag 7
  cartanMatrix_offDiag_nonpos := CartanMatrix.E_off_diag_nonpos 7
  cartanMatrix_zero_comm i j := by rw [(CartanMatrix.E_isSymm 7).apply]
  weight_eq_neg_one_or_eq_zero_or_eq_one :=
    e7MinusculeWeight_apply_eq_neg_one_or_eq_zero_or_eq_one
  weight_reflection i a j := by
    rw [(CartanMatrix.E_isSymm 7).apply]
    exact e7MinusculeWeight_reflection_apply i a j
  weight_injective := e7MinusculeWeight_injective

/-- The Cartan matrix of the type-`E₇` minuscule weight table is the `E₇` Cartan matrix. -/
@[simp]
theorem weightTable_cartanMatrix : weightTable.cartanMatrix = CartanMatrix.E 7 := by
  rw [weightTable]

/-- The weights of the type-`E₇` minuscule weight table are the minuscule weights. -/
@[simp]
theorem weightTable_weight : weightTable.weight = e7MinusculeWeight := by
  rw [weightTable]

/-- The simple reflections of the type-`E₇` minuscule weight table are the minuscule
reflections. -/
@[simp]
theorem weightTable_reflection (i : Fin 7) :
    weightTable.reflection i = e7MinusculeReflection i := by
  rw [weightTable]

/-! ## The integral generator matrices -/

/-- The Cartan generator `H_i` in the minuscule weight basis. -/
def cartanMatrix (i : Fin 7) : Matrix (Fin 56) (Fin 56) ℤ :=
  weightTable.cartanGeneratorMatrix i

/-- The raising generator `E_i` in the minuscule weight basis. -/
def raisingMatrix (i : Fin 7) : Matrix (Fin 56) (Fin 56) ℤ :=
  weightTable.raisingMatrix i

/-- The lowering generator `F_i` in the minuscule weight basis. -/
def loweringMatrix (i : Fin 7) : Matrix (Fin 56) (Fin 56) ℤ :=
  weightTable.loweringMatrix i

/-- The entrywise formula for the diagonal Cartan generator matrix. -/
@[simp]
theorem cartanMatrix_apply (i : Fin 7) (a b : Fin 56) :
    cartanMatrix i a b = if a = b then e7MinusculeWeight a i else 0 := by
  rw [cartanMatrix, weightTable.cartanGeneratorMatrix_apply, weightTable_weight]
  split <;> simp_all

/-- The entrywise formula for the raising generator matrix. -/
@[simp]
theorem raisingMatrix_apply (i : Fin 7) (a b : Fin 56) :
    raisingMatrix i a b =
      if e7MinusculeWeight b i = -1 ∧ a = e7MinusculeReflection i b then 1 else 0 :=
  by simpa only [raisingMatrix, weightTable_weight, weightTable_reflection] using
    weightTable.raisingMatrix_apply i a b

/-- The entrywise formula for the lowering generator matrix. -/
@[simp]
theorem loweringMatrix_apply (i : Fin 7) (a b : Fin 56) :
    loweringMatrix i a b =
      if e7MinusculeWeight b i = 1 ∧ a = e7MinusculeReflection i b then 1 else 0 :=
  by simpa only [loweringMatrix, weightTable_weight, weightTable_reflection] using
    weightTable.loweringMatrix_apply i a b

/-! ## Chevalley--Serre relations -/

/-- At each simple node, the three integral minuscule generator matrices form an `sl₂` triple. -/
theorem isSl2Triple (i : Fin 7) :
    _root_.IsSl2Triple (cartanMatrix i) (raisingMatrix i) (loweringMatrix i) :=
  weightTable.isSl2Triple i (exists_e7MinusculeWeight_apply_eq_neg_one i)

/-- The integral minuscule generator matrices satisfy the Chevalley--Serre relations of type
`E₇`, in Bourbaki numbering. -/
theorem isSerreSystem :
    IsSerreSystem ℤ (CartanMatrix.E 7)
      cartanMatrix raisingMatrix loweringMatrix :=
  weightTable.isSerreSystem

/-- The explicit integral fifty-six-dimensional representation of the type-`E₇` Serre Lie
algebra. -/
noncomputable def serreRepresentation :
    Matrix.ToLieAlgebra ℤ (CartanMatrix.E 7) →ₗ⁅ℤ⁆ Matrix (Fin 56) (Fin 56) ℤ :=
  weightTable.serreRepresentation

/-- The integral Serre representation sends `H_i` to the Cartan generator matrix. -/
@[simp]
theorem serreRepresentation_serreH (i : Fin 7) :
    serreRepresentation (serreH ℤ (CartanMatrix.E 7) i) = cartanMatrix i :=
  weightTable.serreRepresentation_serreH i

/-- The integral Serre representation sends `E_i` to the raising generator matrix. -/
@[simp]
theorem serreRepresentation_serreE (i : Fin 7) :
    serreRepresentation (serreE ℤ (CartanMatrix.E 7) i) = raisingMatrix i :=
  weightTable.serreRepresentation_serreE i

/-- The integral Serre representation sends `F_i` to the lowering generator matrix. -/
@[simp]
theorem serreRepresentation_serreF (i : Fin 7) :
    serreRepresentation (serreF ℤ (CartanMatrix.E 7) i) = loweringMatrix i :=
  weightTable.serreRepresentation_serreF i

/-- Every minuscule raising generator squares to zero. -/
@[simp]
theorem raisingMatrix_mul_self (i : Fin 7) : raisingMatrix i * raisingMatrix i = 0 := by
  simpa only [raisingMatrix, pow_two] using weightTable.raisingMatrix_pow_two i

/-- Every minuscule lowering generator squares to zero. -/
@[simp]
theorem loweringMatrix_mul_self (i : Fin 7) : loweringMatrix i * loweringMatrix i = 0 := by
  simpa only [loweringMatrix, pow_two] using weightTable.loweringMatrix_pow_two i

end TauCeti.E7Minuscule


