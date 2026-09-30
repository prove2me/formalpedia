-- Prove2me | Definitions.Def_CQM_DaggerCategory
-- name    : CQM_DaggerCategory
-- status  : Definition
-- author  : @Bingyu Xia
-- created : 2026-09-29T08:53:59.693678+00:00
-- url     : https://prove2.me/theorems/1cfef7bf-f828-4630-b107-cda354c98d97
-- title:
--   Dagger categories: isometries, unitaries and positive elements
-- statement:
--   A dagger category is a category with a contravariant, identity-fixing, involutive endofunctor. On top of it this bundle defines the morphism classes the rest of the development needs: projections, isometries ($f^\dagger \circ f = \mathrm{id}$), unitaries and positive elements, plus dagger kernels and monoidal dagger categories.
-- source:
--   Reutter & Vicary, *Categorical Quantum Mechanics*, §2.3 (Daggers), Definitions 2.29–2.38
--
--   Lean source: https://github.com/BryceT233/Categorical-Quantum-Mechanics/blob/dd7d4573fabdb5ca8af0811c1af6396a49365b42/FQFP/CQM/Category/DaggerCategory.lean

/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib.Algebra.Group.Idempotent
import Mathlib.CategoryTheory.Endomorphism
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import Mathlib.CategoryTheory.Limits.Shapes.Kernels
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.Combinatorics.Quiver.ReflQuiver

/-!
# Dagger categories

This file defines the categorical abstraction of the dagger (adjoint) operation: a
contravariant, involutive involution on morphisms that fixes identities and reverses
composition. It also introduces the standard classes of morphisms used in categorical
quantum mechanics — projections, isometries, unitaries, and positive maps — together
with monoidal dagger categories, where the dagger is compatible with the monoidal
structure, and dagger kernels, where the canonical kernel map is an isometry.

## Main definitions

* `DaggerCategory`: a category equipped with a dagger.
* `DaggerCategory.IsProj`: an idempotent self-adjoint endomorphism, i.e. a projection.
* `DaggerCategory.IsIsometry`: a morphism `f` satisfying `f ≫ f† = 𝟙`.
* `DaggerCategory.IsUnitary`: an isometry `f` that also satisfies `f† ≫ f = 𝟙`.
* `DaggerCategory.IsPositive`: an endomorphism of the form `g ≫ g†`.
* `MonoidalDaggerCategory`: a dagger category that is also monoidal, with the dagger
  compatible with the tensor product and the structural isomorphisms.

## Notation

* `f†` is notation for `DaggerCategory.dagger f`.

## Main results

* `dagger_zero`: the dagger of a zero morphism is zero.
* `isZero_of_isInitial` and `isZero_of_isTerminal`: in a dagger category, initial and
  terminal objects are zero objects.
* `DaggerCategory.IsIsometry.eq_dagger_comp_of_comp_eq`: a factorization through an
  isometry is unique, given by `x ≫ f†`.
* `DaggerCategory.kernelLift_eq_dagger_comp`: when `kernel.ι f` is an isometry, the
  canonical factorization through `kernel f` is `g ≫ (kernel.ι f)†`.
* `DaggerCategory.kernelIso_daggerKernel`: any dagger kernel of `f` is unitarily
  isomorphic to the canonical `kernel f`.

**Assisted by Deepseek Harness**
-/

@[expose] public section

open CategoryTheory

section DaggerCategory

universe u v

variable {C : Type u} [Category.{v} C]

/-- A category equipped with a contravariant dagger that fixes identities, reverses
composition, and is involutive. -/
class CategoryTheory.DaggerCategory (C : Type u) [Category.{v} C] where
  /-- The contravariant dagger of a morphism, reversing its direction. -/
  dagger {c₁ c₂ : C} (f : c₁ ⟶ c₂) : c₂ ⟶ c₁
  dagger_comp {c₁ c₂ c₃ : C} (f : c₁ ⟶ c₂) (g : c₂ ⟶ c₃) : dagger (f ≫ g) = dagger g ≫ dagger f
  dagger_id (c : C) : dagger (𝟙 c) = 𝟙 c
  involutive_dagger {c₁ c₂ : C} (f : c₁ ⟶ c₂) : dagger (dagger f) = f

/-- Notation `f†` for the dagger of a morphism `f`. -/
notation:max f "†" => DaggerCategory.dagger f

namespace CategoryTheory.DaggerCategory

attribute [simp] dagger_comp dagger_id involutive_dagger

variable [DaggerCategory C]


/-- An idempotent self-adjoint endomorphism, i.e. a projection. -/
class IsProj [DaggerCategory C] {c : C} (f : End c) where
  idem (f) : IsIdempotentElem f
  selfAdjoint (f) : f† = f

attribute [simp] IsProj.selfAdjoint


/-- A morphism satisfying `f ≫ f† = 𝟙`, i.e. an isometry. -/
class IsIsometry [DaggerCategory C] {c₁ c₂ : C} (f : c₁ ⟶ c₂) where
  comp_dagger_eq_id (f) : f ≫ f† = 𝟙 c₁

attribute [simp] IsIsometry.comp_dagger_eq_id


/-- An isometry that also satisfies `f† ≫ f = 𝟙`, i.e. a unitary morphism. -/
class IsUnitary [DaggerCategory C] {c₁ c₂ : C} (f : c₁ ⟶ c₂) extends IsIsometry f where
  dagger_comp_eq_id (f) : f† ≫ f = 𝟙 c₂

attribute [simp] IsUnitary.dagger_comp_eq_id


/-- An endomorphism of the form `g ≫ g†` for some morphism `g`, i.e. a positive morphism. -/
class IsPositive {c : C} (f : End c) where
  out (f) : ∃ (c' : C) (g : c ⟶ c'), f = g ≫ g†


open Limits


section kernel


/-- `HasDaggerKernels C` asserts that every morphism has a kernel and that the canonical kernel
map `kernel.ι f` is an isometry, i.e. that `C` has dagger kernels of arbitrary morphisms. -/
class HasDaggerKernels (C : Type u) [Category.{v} C] [DaggerCategory C] [HasZeroMorphisms C]
extends HasKernels C where
  isIsometry {X Y : C} (f : X ⟶ Y) : IsIsometry (kernel.ι f)

attribute [instance] HasDaggerKernels.isIsometry


end kernel

end CategoryTheory.DaggerCategory

open Category
open MonoidalCategory

/-- A dagger category that is also monoidal, with the dagger compatible with the tensor product
and the structural isomorphisms. -/
class CategoryTheory.MonoidalDaggerCategory (C : Type u) [Category.{v} C] extends
    DaggerCategory C, MonoidalCategory C where
  dagger_tensor {H₁ H₂ K₁ K₂ : C} (f₁ : H₁ ⟶ K₁) (f₂ : H₂ ⟶ K₂) : (f₁ ⊗ₘ f₂)† = f₁† ⊗ₘ f₂†
  isUnitary_associator (H₁ H₂ H₃ : C) : DaggerCategory.IsUnitary (α_ H₁ H₂ H₃).hom
  isUnitary_leftUnitor (H : C) : DaggerCategory.IsUnitary (λ_ H).hom
  isUnitary_rightUnitor (H : C) : DaggerCategory.IsUnitary (ρ_ H).hom

attribute [instance] MonoidalDaggerCategory.isUnitary_associator
MonoidalDaggerCategory.isUnitary_leftUnitor MonoidalDaggerCategory.isUnitary_rightUnitor

end DaggerCategory


