-- Prove2me | Definitions.Def_TC433_Algebra_Lie_E6_RootCharacters_cac3b6e6d5
-- name    : TC433_Algebra_Lie_E6_RootCharacters_cac3b6e6d5
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T11:45:39.354605+00:00
-- url     : https://prove2.me/theorems/b97d5956-d90a-4dd4-8188-b17ce85038eb
-- title:
--   TauCeti: Algebra / Lie / E6 / RootCharacters
-- statement:
--   Compatibility port of the definitions and proved supporting lemmas in TauCeti.Algebra.Lie.E6.RootCharacters for the concrete CFSG catalog. This module does not assert the classification theorem.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/6e0c6acab5f4c6f42e5f5bab9bd5e4e84f74c380/TauCeti/Algebra/Lie/E6/RootCharacters.lean

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Definitions.Def_TC433_Algebra_Lie_UniversalEnveloping_Kostant_Serre_c2f7eb379b
public import Definitions.Def_TC433_LinearAlgebra_RootSystem_SimplyConnectedRootDatum_E6_Basic_05ec2ee350

/-!
# Type-E₆ simple-root characters

The positive and negative numbered Serre generators have the corresponding simple-root
characters for the Cartan action. Each positive character is primitive, as witnessed by an
explicit Bézout certificate for its row of the type-`E₆` Cartan matrix.

These characters and the certificate depend only on the type-`E₆` Serre presentation, so they
apply to both the minuscule and doubled minuscule carriers.

The root numbering follows N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate V.
-/

public section
set_option backward.isDefEq.respectTransparency.types false

open scoped Matrix

namespace TauCeti.E6

open TauCeti.DynkinType

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The character through which the Cartan torus acts on a positive or negative numbered
type-`E₆` root generator. -/
def rootGeneratorWeight : Fin 6 ⊕ Fin 6 → Fin 6 → ℤ
  | .inl i => fun j ↦ CartanMatrix.E 6 i j
  | .inr i => fun j ↦ -CartanMatrix.E 6 i j

@[simp]
theorem rootGeneratorWeight_inl (i j : Fin 6) :
    rootGeneratorWeight (.inl i) j = CartanMatrix.E 6 i j := by
  rw [rootGeneratorWeight]

@[simp]
theorem rootGeneratorWeight_inr (i j : Fin 6) :
    rootGeneratorWeight (.inr i) j = -CartanMatrix.E 6 i j := by
  rw [rootGeneratorWeight]

private def cartanNeighbor : Fin 6 → Fin 6 :=
  ![2, 3, 0, 1, 3, 4]

/-- A Bézout certificate for the rows of the type-`E₆` Cartan matrix: the coefficient `-1` at a
neighbour of `i` whose Cartan entry is `-1`, and `0` elsewhere. -/
def cartanBezout (i j : Fin 6) : ℤ :=
  if j = cartanNeighbor i then -1 else 0

private theorem cartan_sum_mul_bezout (i : Fin 6) :
    ∑ j, CartanMatrix.E 6 i j * cartanBezout i j = 1 := by
  fin_cases i <;> decide

/-- **Every positive simple-root character of type `E₆` is primitive**, with the explicit
certificate `TauCeti.E6.cartanBezout`. -/
theorem rootGeneratorWeight_sum_mul_cartanBezout (i : Fin 6) :
    ∑ j, rootGeneratorWeight (.inl i) j * cartanBezout i j = 1 := by
  simpa only [rootGeneratorWeight_inl] using cartan_sum_mul_bezout i

/-- The negative simple-root character at a node is the negative of the positive one. -/
theorem rootGeneratorWeight_inr_eq_neg_inl (i : Fin 6) :
    rootGeneratorWeight (.inr i) = -rootGeneratorWeight (.inl i) := by
  ext j
  simp

/-- The character of a raising generator is the corresponding simple root of the pinned
simply connected type-`E₆` root datum. -/
theorem rootGeneratorWeight_inl_eq_e6Root_e6SimpleIndex (i : Fin 6) :
    rootGeneratorWeight (.inl i) = e6Root (e6SimpleIndex i) := by
  ext j
  rw [rootGeneratorWeight_inl, root_e6SimpleIndex]

/-- The character of a lowering generator is the negative of the corresponding simple root. -/
theorem rootGeneratorWeight_inr_eq_neg_e6Root_e6SimpleIndex (i : Fin 6) :
    rootGeneratorWeight (.inr i) = -e6Root (e6SimpleIndex i) := by
  ext j
  rw [rootGeneratorWeight_inr, Pi.neg_apply, root_e6SimpleIndex]

/-- The numbered Serre root generators are weight vectors for the Cartan generators. -/
theorem lie_serreH_rootGenerator (k : Fin 6 ⊕ Fin 6) (j : Fin 6) :
    ⁅TauCeti.serreH ℚ ((CartanMatrix.E 6)ᵀ) j,
        TauCeti.serreRootGenerator ((CartanMatrix.E 6)ᵀ) k⁆ =
      ((rootGeneratorWeight k j : ℤ) : ℚ) •
        TauCeti.serreRootGenerator ((CartanMatrix.E 6)ᵀ) k := by
  cases k with
  | inl i =>
      rw [TauCeti.lie_serreH_serreRootGenerator_inl, Matrix.transpose_apply,
        rootGeneratorWeight_inl]
  | inr i =>
      rw [TauCeti.lie_serreH_serreRootGenerator_inr, Matrix.transpose_apply,
        rootGeneratorWeight_inr]

end TauCeti.E6


