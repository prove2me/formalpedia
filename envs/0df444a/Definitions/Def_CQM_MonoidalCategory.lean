-- Prove2me | Definitions.Def_CQM_MonoidalCategory
-- name    : CQM_MonoidalCategory
-- status  : Definition
-- author  : @Bingyu Xia
-- created : 2026-09-29T08:59:57.111206+00:00
-- url     : https://prove2.me/theorems/6f17b4d2-7bb5-42a3-970b-347c162577a6
-- title:
--   Scalars, states, effects and probabilities
-- statement:
--   The probabilistic vocabulary of categorical quantum mechanics, stated for a monoidal dagger category: the scalar monoid $\mathrm{End}(I)$, states $I \to A$, effects $A \to I$, the probability $\mathrm{Prob}(a,x) = a^\dagger \circ x^\dagger \circ x \circ a$ of an effect $x$ on a state $a$, and the completeness and disjointness conditions on a family of effects.
-- source:
--   Reutter & Vicary, *Categorical Quantum Mechanics*, §2.4 (Measurement), Definitions 2.43–2.51
--
--   Lean source: https://github.com/BryceT233/Categorical-Quantum-Mechanics/blob/dd7d4573fabdb5ca8af0811c1af6396a49365b42/FQFP/CQM/Category/MonoidalCategory.lean

/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Definitions.Def_CQM_DaggerCategory
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas

/-!
# Scalars, states and effects in a monoidal category

This file develops the basic ingredients of categorical quantum mechanics in an arbitrary
monoidal category `C`. The scalars of `C` are the endomorphisms of its monoidal unit `𝟙_ C`;
they form a commutative monoid (by the Eckmann-Hilton argument) and act on every hom-set by
scalar multiplication. We also define states, joint states and entanglement, effects, and the
Born-rule probability of an effect in a state (for a monoidal dagger category).

## Main definitions

* `Scalar`: the scalars of a monoidal category, i.e. `End (𝟙_ C)`.
* `State` and `JointState`: morphisms from the monoidal unit into an object, resp. a tensor
  product of two objects.
* `JointState.Entangled`: the property that a joint state is not a product state.
* `Effect`: morphisms into the monoidal unit.
* `probability`: the Born-rule probability of an effect in a state.

## Main results

* `Scalar.commMonoid`: the scalars of a monoidal category form a commutative monoid.
* `comp_comm`: endomorphisms of the monoidal unit commute under composition.
* `smul_assoc` and `smul_comp_smul`: the scalar action is associative and satisfies the
  interchange law with composition.
* `JointState.not_entangled_iff`: a joint state is not entangled iff it is a product state.

**Assisted by Deepseek Harness**
-/

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory.MonoidalCategory

universe u v

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C]

section scalar

/-- The scalars of a monoidal category `C`, i.e. the endomorphisms of its monoidal unit
`𝟙_ C`. They form a commutative monoid (see `Scalar.commMonoid`) and act on every hom-set by
scalar multiplication (see the `SMul` instance below). -/
abbrev Scalar (C : Type u) [Category.{v} C] [MonoidalCategory.{v} C] : Type _ := End (𝟙_ C)

@[reassoc]
private lemma whiskerRight_leftUnitor (s : Scalar C) :
    (s ▷ 𝟙_ C) ≫ (λ_ (𝟙_ C)).hom = (λ_ (𝟙_ C)).hom ≫ s :=
  unitors_equal (C := C) ▸ rightUnitor_naturality s

private lemma scalar_tensor_eq_comp (s t : Scalar C) :
    (λ_ (𝟙_ C)).inv ≫ (s ⊗ₘ t) ≫ (λ_ (𝟙_ C)).hom = s ≫ t := by
  rw [tensorHom_def, Category.assoc, leftUnitor_naturality, whiskerRight_leftUnitor_assoc]
  simp

private lemma scalar_tensor_eq_comp_rev (s t : Scalar C) :
    (λ_ (𝟙_ C)).inv ≫ (s ⊗ₘ t) ≫ (λ_ (𝟙_ C)).hom = t ≫ s := by
  have : s ⊗ₘ t = (𝟙_ C ◁ t) ≫ (s ▷ 𝟙_ C) := by
    rw [← id_tensorHom, ← tensorHom_id, tensorHom_comp_tensorHom, Category.id_comp,
      Category.comp_id]
  rw [this, Category.assoc, whiskerRight_leftUnitor, leftUnitor_naturality_assoc]
  simp

/-- Endomorphisms of the monoidal unit commute under composition. -/
@[reassoc]
lemma comp_comm {s t : End (𝟙_ C)} : s ≫ t = t ≫ s := by
  rw [← scalar_tensor_eq_comp, scalar_tensor_eq_comp_rev]

/-- Scalar endomorphisms of the monoidal unit commute. -/
instance Scalar.commMonoid : CommMonoid (Scalar C) where
  mul_comm _ _ := by rw [End.mul_def, End.mul_def, comp_comm]

instance {c₁ c₂ : C} : SMul (Scalar C) (c₁ ⟶ c₂) where
  smul s f := (λ_ c₁).inv ≫ (s ⊗ₘ f) ≫ (λ_ c₂).hom


end scalar

/-- A state of an object `c` is a morphism from the monoidal unit `𝟙_ C` into `c`. -/
abbrev State (c : C) : Type _ := 𝟙_ C ⟶ c


/-- An effect on an object `c` is a morphism from `c` into the monoidal unit `𝟙_ C`. -/
abbrev Effect (c : C) : Type _ := c ⟶ 𝟙_ C

/-- A set of effects `xᵢ : c ⟶ 𝟙_ C` is complete if every nonzero process yields a nonzero
effect, i.e. if a morphism `f : c' ⟶ c` vanishes after postcomposition with every `xᵢ`, then
`f = 0`. -/
def Effect.Complete [HasZeroMorphisms C] {ι : Type*} {c : C} (x : ι → Effect c) : Prop :=
  ∀ {c' : C} (f : c' ⟶ c), (∀ (i : ι), f ≫ x i = 0) → f = 0

section daggerCat

variable [DaggerCategory C]

/-- disjoint set of effects -/
def Effect.Disjoint [HasZeroMorphisms C] {ι : Type*} {c : C} (x : ι → Effect c) : Prop :=
  (∀ (i : ι), (x i)† ≫ x i = 𝟙 (𝟙_ C)) ∧ _root_.Pairwise (fun i j ↦ (x j)† ≫ x i = 0)


-- The two characterizations of `Effect.Complete` and `Effect.Disjoint` by the associated
-- biproduct map `biproduct.lift x` are proved in `FQFP.CQM.Category.Measurement`:
-- `Effect.complete_iff_kernel_iota_eq_zero` and `Effect.disjoint_iff_isIsometry_dagger`.

/-- The probability associated to a state and an effect of an object in a monoidal dagger category,
given by the scalar `a ≫ x ≫ x† ≫ a†`. -/
abbrev probability {c : C} (a : State c) (x : Effect c) : Scalar C := a ≫ x ≫ x† ≫ a†

end daggerCat

end CategoryTheory.MonoidalCategory


