-- Prove2me | Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_CharacterCount
-- name    : OddOrder_GroupTheory_RepresentationTheory_CharacterCount
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:01:14.172427+00:00
-- url     : https://prove2.me/theorems/2de1fff1-2926-4deb-b6bc-8dfc99edd319
-- title:
--   Finiteness of $\mathrm{Irr}\,G$ and the bound $|\mathrm{Irr}\,G|\le|\mathrm{ConjClasses}\,G|$
-- statement:
--   Using first orthogonality, the irreducible characters of a finite group are linearly independent in the finite-dimensional space of class functions, which has dimension equal to the number of conjugacy classes. Hence $\mathrm{Irr}(G)$ is finite and has at most as many elements as there are conjugacy classes. This is the $\le$ half of $|\mathrm{Irr}\,G|=|\mathrm{ConjClasses}\,G|$; the reverse inequality is treated separately.
--
--   Main definitions: `classFunctionEquivConjClasses` (a class function is determined by its values on conjugacy classes), `instFiniteDimensionalClassFunction` (finite-dimensionality of the class-function space), and `innerDual` (Peterfalvi's inner product against a fixed class function as a linear functional).
--
--   The bundle also proves 5 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/RepresentationTheory/CharacterCount.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/RepresentationTheory/CharacterCount.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_CharacterRowOrthogonality
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

namespace OddOrder.RepresentationTheory

open Module (finrank)

variable {G : Type*} [Group G]

/-- A class function is determined by, and determines, its values on conjugacy classes:
the linear isomorphism `ClassFunction G ℂ ≃ₗ[ℂ] (ConjClasses G → ℂ)`. -/
noncomputable def classFunctionEquivConjClasses :
    ClassFunction G ℂ ≃ₗ[ℂ] (ConjClasses G → ℂ) where
  toFun φ C := φ (conjugacyClassRepresentative C)
  map_add' φ ψ := rfl
  map_smul' c φ := rfl
  invFun f := ⟨fun g => f (ConjClasses.mk g), fun g h =>
    congrArg f (ConjClasses.mk_eq_mk_iff_isConj.mpr (isConj_iff.mpr ⟨h, rfl⟩).symm)⟩
  left_inv φ := by
    apply ClassFunction.ext
    intro g
    exact φ.of_isConj
      (ConjClasses.mk_eq_mk_iff_isConj.mp (conjugacyClassRepresentative_mk_eq (ConjClasses.mk g)))
  right_inv f := by
    funext C
    exact congrArg f (conjugacyClassRepresentative_mk_eq C)

/-- The space of complex class functions on a finite group is finite-dimensional. -/
instance instFiniteDimensionalClassFunction [Finite G] :
    FiniteDimensional ℂ (ClassFunction G ℂ) := by
  have : Finite (ConjClasses G) := Finite.of_surjective _ ConjClasses.mk_surjective
  exact Module.Finite.equiv classFunctionEquivConjClasses.symm

/-- The space of complex class functions on a finite group has dimension equal to the number
of conjugacy classes. -/
theorem finrank_classFunction [Finite G] :
    finrank ℂ (ClassFunction G ℂ) = Nat.card (ConjClasses G) := by
  have : Fintype (ConjClasses G) := Fintype.ofFinite _
  rw [classFunctionEquivConjClasses.finrank_eq, Module.finrank_fintype_fun_eq_card,
    Nat.card_eq_fintype_card]

/-- Peterfalvi's inner product against a fixed class function `ψ`, as a linear functional. -/
noncomputable def innerDual [Fintype G] [Invertible (Nat.card G : ℂ)]
    (ψ : ClassFunction G ℂ) : Module.Dual ℂ (ClassFunction G ℂ) where
  toFun φ := ClassFunction.inner φ ψ
  map_add' φ₁ φ₂ := ClassFunction.inner_add_left φ₁ φ₂ ψ
  map_smul' c φ := by simpa using ClassFunction.inner_smul_left c φ ψ

@[simp] theorem innerDual_apply [Fintype G] [Invertible (Nat.card G : ℂ)]
    (ψ φ : ClassFunction G ℂ) : innerDual ψ φ = ClassFunction.inner φ ψ := rfl

/-- **The irreducible characters are linearly independent** (over `ℂ`), via the first
orthogonality relation and the biorthogonal system of inner-product functionals. -/
theorem linearIndependent_irreducibleCharacter [Finite G] :
    LinearIndependent ℂ (fun χ : IrreducibleCharacter G => (χ : ClassFunction G ℂ)) := by
  have : Fintype G := Fintype.ofFinite G
  have : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  refine LinearIndependent.of_pairwise_dual_eq_zero_one _
    (fun ψ => innerDual (ψ : ClassFunction G ℂ)) (fun χ ψ hχψ => ?_) (fun χ => ?_)
  · simp only [innerDual_apply, irreducibleCharacter_inner]
    rw [if_neg (Ne.symm hχψ)]
  · simp only [innerDual_apply, irreducibleCharacter_inner, if_true]

/-- **There are finitely many irreducible characters** of a finite group. -/
theorem finite_irreducibleCharacter [Finite G] : Finite (IrreducibleCharacter G) :=
  (linearIndependent_irreducibleCharacter (G := G)).finite

/-- **`|Irr G| ≤ |ConjClasses G|`**: the number of irreducible characters is at most the number
of conjugacy classes. (The reverse inequality — completeness — is the harder direction.) -/
theorem card_irreducibleCharacter_le [Finite G] :
    Nat.card (IrreducibleCharacter G) ≤ Nat.card (ConjClasses G) := by
  have := finite_irreducibleCharacter (G := G)
  have : Fintype (IrreducibleCharacter G) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, ← finrank_classFunction (G := G)]
  exact (linearIndependent_irreducibleCharacter (G := G)).fintype_card_le_finrank

end OddOrder.RepresentationTheory


