-- Prove2me | Definitions.Def_CQM_DaggerBiproduct
-- name    : CQM_DaggerBiproduct
-- status  : Definition
-- author  : @Bingyu Xia
-- created : 2026-09-29T08:57:02.547933+00:00
-- url     : https://prove2.me/theorems/a54729ee-f64a-4172-8c32-42ddfd955312
-- title:
--   Dagger biproducts
-- statement:
--   A biproduct is a *dagger biproduct* when each injection is the dagger of the corresponding projection. The condition is given both for an arbitrary finite family and in the binary form matching Mathlib's `biprod`, together with the `entry` map that reads off the $(i,j)$ component of a morphism of biproducts.
-- source:
--   Reutter & Vicary, *Categorical Quantum Mechanics*, §2.3.3, Definition 2.39
--
--   Lean source: https://github.com/BryceT233/Categorical-Quantum-Mechanics/blob/dd7d4573fabdb5ca8af0811c1af6396a49365b42/FQFP/CQM/Category/DaggerBiproduct.lean

/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Definitions.Def_CQM_DaggerCategory
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# Dagger biproducts

This file develops Definition 2.39 of the source notes — dagger biproducts — together with
the two results the notes draw from it: Lemma 2.41 (the adjoint of a matrix is its conjugate
transpose) and Corollary 2.42 (daggers distribute over addition).

A biproduct `⨁ f` is a *dagger biproduct* when every injection is the dagger of the
corresponding projection. The condition is stated both for an arbitrary finite family
(`IsDaggerBiproduct`) and in the binary form matching Mathlib's `biprod`
(`IsDaggerBinaryBiproduct`).

## Main definitions

* `DaggerCategory.IsDaggerBiproduct`: a biproduct whose injections are the daggers of its
  projections.
* `DaggerCategory.IsDaggerBinaryBiproduct`: the binary form of the same condition.
* `DaggerCategory.entry`: the `(i, j)` entry of a morphism of biproducts.

## Main results

* `DaggerCategory.dagger_entry`: **Lemma 2.41** in intrinsic form — transposing a morphism
  of biproducts daggers every entry.
* `DaggerCategory.dagger_biproduct_matrix`: **Lemma 2.41** in `biproduct.matrix` form.
* `DaggerCategory.dagger_add`: **Corollary 2.42** — `(f + g)† = f† + g†`.

## Implementation notes

Mathlib's `biproduct.matrix` is monomorphic in its index types (`J : Type`, not `Type*`),
so `dagger_biproduct_matrix` is stated at `Type 0`. The intrinsic `dagger_entry` form has no
such restriction and is the one to use for general statements.

**Assisted by Deepseek Harness**
-/

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory.DaggerCategory

universe u v

section Family

variable {C : Type u} [Category.{v} C] [DaggerCategory C] [HasZeroMorphisms C]

/-- A biproduct `⨁ f` is a **dagger biproduct** when every injection is the dagger of the
corresponding projection. -/
class IsDaggerBiproduct {ι : Type*} (f : ι → C) [HasBiproduct f] : Prop where
  /-- Every injection is the dagger of the corresponding projection. -/
  dagger_ι : ∀ i, (biproduct.ι f i)† = biproduct.π f i

namespace IsDaggerBiproduct

variable {ι : Type*} {f : ι → C} [HasBiproduct f] [IsDaggerBiproduct f]


end IsDaggerBiproduct

variable {ι : Type*} {f : ι → C} [HasBiproduct f] [IsDaggerBiproduct f]
variable {κ : Type*} {G : κ → C} [HasBiproduct G] [IsDaggerBiproduct G]

/-- The `(i, j)` entry of a morphism of biproducts. Unlike Mathlib's
`biproduct.components`, this needs neither `HasFiniteBiproducts` nor index types at
`Type 0`. -/
noncomputable def entry (x : ⨁ f ⟶ ⨁ G) (i : ι) (j : κ) : f i ⟶ G j :=
  biproduct.ι f i ≫ x ≫ biproduct.π G j


end Family

section MatrixForm

variable {C : Type u} [Category.{v} C] [DaggerCategory C] [HasZeroMorphisms C]


end MatrixForm

section Additive

variable {C : Type u} [Category.{v} C] [DaggerCategory C] [Preadditive C]

/-- Binary form of Definition 2.39, matching Mathlib's `biprod`. -/
class IsDaggerBinaryBiproduct (X Y : C) [HasBinaryBiproduct X Y] : Prop where
  /-- The first injection is the dagger of the first projection. -/
  dagger_inl : (biprod.inl : X ⟶ X ⊞ Y)† = biprod.fst
  /-- The second injection is the dagger of the second projection. -/
  dagger_inr : (biprod.inr : Y ⟶ X ⊞ Y)† = biprod.snd

section

variable {X Y Z : C} [HasBinaryBiproduct X Y] [IsDaggerBinaryBiproduct X Y]


lemma IsDaggerBinaryBiproduct.dagger_snd : (biprod.snd : X ⊞ Y ⟶ Y)† = biprod.inr := by
  rw [← IsDaggerBinaryBiproduct.dagger_inr]
  simp


end


end Additive

end CategoryTheory.DaggerCategory


