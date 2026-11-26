-- Prove2me | Definitions.Def_ProEtale_Mathlib_Algebra_Homology_DerivedCategory_Ext_SequentialLimit
-- name    : ProEtale_Mathlib_Algebra_Homology_DerivedCategory_Ext_SequentialLimit
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T17:37:23.014981+00:00
-- url     : https://prove2.me/theorems/c60c5418-5d4e-4d74-9bac-89cd2db43608
-- title:
--   Levelwise Ext systems of an inverse system and their connecting morphisms
-- statement:
--   Let $\mathcal A$ be an abelian category with Ext groups, such that the category of inverse systems $\mathcal A^{\mathbb N^{\mathrm{op}}}$ also has Ext groups. Fix an object $Z$. The module containing this file compares $\operatorname{Ext}^i(\Delta Z, F)$, computed in the category of inverse systems, with $\varprojlim_n \operatorname{Ext}^i(Z, F_n)$. The comparison holds in degree $0$, and in degree $i+1$ under a Mittag-Leffler hypothesis on the degree-$i$ levelwise system. This file contains the basic constructions for that comparison.
--
--   1. Limits of $\mathbb N^{\mathrm{op}}$-shaped diagrams of abelian groups exist.
--   2. For an inverse system $F : \mathbb N^{\mathrm{op}} \to \mathcal A$ and $i \ge 0$, the **levelwise Ext system** is the inverse system of abelian groups
--   $$n \longmapsto \operatorname{Ext}^i(Z, F_n),$$
--   with transition maps given by composing with the transition maps of $F$.
--   3. Assume moreover that $\mathcal A$ has enough injectives and countable products. Let $0 \to F_1 \to F_2 \to F_3 \to 0$ be a sequence of inverse systems that is short exact in each level. The levelwise connecting maps $\operatorname{Ext}^i(Z,(F_3)_n) \to \operatorname{Ext}^{i+1}(Z,(F_1)_n)$ are compatible with the transition maps, and so form a morphism of inverse systems. Its components are composition with the levelwise extension class.
--   4. A componentwise description of whiskering the map $F_2 \to F_3$ with the levelwise Ext functor.
--
--   The module docstring says that the comparison theorems themselves are proved by dimension shifting. They are `zeroAddEquivLimitLevelSystem`, `nonempty_addEquiv_limit_levelSystem` and `nonempty_addEquiv_limit_levelSystem_of_surjective`, and they are not part of this file.
--
--   **Formalization Note** The declarations are `CategoryTheory.Abelian.Ext.levelSystem` (defined as `F ⋙ extFunctorObj Z i`), `levelSystem_map_apply`, `levelDelta`, `levelDelta_app_apply` and `whiskerRight_extFunctorObj_app_apply`, with Ext groups in universe `w`. Levelwise short exactness is phrased via evaluation functors `(evaluation ℕᵒᵖ A).obj k`. The general discrepancy between the two sides is attributed in the docstring to a $\lim^1$-term (Jannsen).
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014); cited in the code: Jannsen (named in the docstring without a precise citation). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Mathlib/Algebra/Homology/DerivedCategory/Ext/SequentialLimit.lean (declarations needed by the transplanted proofs, unused ones removed).

/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.CofilteredSystem
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Definitions.Def_ProEtale_Mathlib_Algebra_Homology_DerivedCategory_Ext_Product
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_Abelian_SequentialSystem
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_Abelian_SequentialSystem_Lib

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
/-!
# `Ext` out of a constant system versus the limit of levelwise `Ext`-groups

Let `A` be an abelian category with enough injectives and countable products, and let
`Z : A`. For an inverse system `F : ℕᵒᵖ ⥤ A` we compare the `Ext`-groups
`Ext (Δ Z) F i` in the category of inverse systems (the right derived functors of
`F ↦ lim Hom(Z, Fₙ)`, e.g. continuous étale cohomology) with the inverse limit of the
levelwise `Ext`-groups `Ext Z Fₙ i`.

In general the two differ by a `lim¹`-term (Jannsen). We prove the comparison
isomorphism in degree `0` unconditionally, and in degree `i + 1` under the hypothesis
that the degree-`i` levelwise `Ext`-system satisfies the Mittag-Leffler condition
(`CategoryTheory.Functor.IsMittagLeffler`, which forces the relevant `lim¹` to
vanish); the latter holds in particular when the transition maps of that system are
surjective, or when its groups are finite:

- `CategoryTheory.Abelian.Ext.zeroAddEquivLimitLevelSystem`
- `CategoryTheory.Abelian.Ext.nonempty_addEquiv_limit_levelSystem`
- `CategoryTheory.Abelian.Ext.nonempty_addEquiv_limit_levelSystem_of_surjective`

The proof is by dimension shifting along `0 → F → I → Q → 0` with `I` injective: the
degree-one case is an explicit Mittag-Leffler eventual-image argument for the
four-term exact sequences of systems
`0 → Hom(Z,F•) → Hom(Z,I•) → Hom(Z,Q•) → Ext¹(Z,F•) → 0`
(using that the transition maps of `Hom(Z,I•)` are split surjections), and the
inductive step uses the connecting isomorphisms on both sides, with naturality in the
system direction provided by `ShortComplex.ShortExact.extClass_naturality`.
-/

universe w t v u

open CategoryTheory Limits Opposite

namespace CategoryTheory
namespace Abelian
namespace Ext

variable {A : Type u} [Category.{v} A] [Abelian A] [HasExt.{w} A] [HasExt.{w} (ℕᵒᵖ ⥤ A)]

/-- Limits of `ℕᵒᵖ`-shaped diagrams of abelian groups, registered explicitly. -/
instance inst_MathlibAlgebraHomologyDerivedCategoryExtSequentialLimit_L50 : HasLimitsOfShape ℕᵒᵖ AddCommGrpCat.{w} := inferInstance

section LevelSystem

variable (Z : A) (F : ℕᵒᵖ ⥤ A)

/-- The inverse system of levelwise `Ext`-groups `n ↦ Ext Z (F.obj (op n)) i`. -/
noncomputable def levelSystem (i : ℕ) : ℕᵒᵖ ⥤ AddCommGrpCat.{w} :=
  F ⋙ extFunctorObj Z i

variable {Z F} in
omit [HasExt.{w} (ℕᵒᵖ ⥤ A)] in
lemma levelSystem_map_apply (i : ℕ) {k k' : ℕᵒᵖ} (f : k ⟶ k') (x : Ext Z (F.obj k) i) :
    ConcreteCategory.hom ((levelSystem Z F i).map f) x = x.comp (Ext.mk₀ (F.map f)) (add_zero i) :=
  rfl


end LevelSystem


section Main

variable [EnoughInjectives A] [HasProductsOfShape ℕ A]

variable (Z : A)

/-- The connecting maps of the levelwise covariant long exact sequences assemble into a
morphism of systems. -/
noncomputable def levelDelta {SC : ShortComplex (ℕᵒᵖ ⥤ A)}
    (hSC : ∀ k : ℕᵒᵖ, (SC.map ((evaluation ℕᵒᵖ A).obj k)).ShortExact) (i : ℕ) :
    levelSystem Z SC.X₃ i ⟶ levelSystem Z SC.X₁ (i + 1) where
  app k := AddCommGrpCat.ofHom ((hSC k).extClass.postcomp Z rfl)
  naturality {k k'} f := by
    have hnat : (hSC k).extClass.comp (Ext.mk₀ (SC.X₁.map f)) (add_zero 1) =
        (Ext.mk₀ (SC.X₃.map f)).comp (hSC k').extClass (zero_add 1) :=
      ShortComplex.ShortExact.extClass_naturality (hSC k) (hSC k')
        (ShortComplex.homMk (SC.X₁.map f) (SC.X₂.map f) (SC.X₃.map f)
          (SC.f.naturality f) (SC.g.naturality f))
    apply ConcreteCategory.hom_ext
    intro x
    refine (ConcreteCategory.comp_apply _ _ _).trans
      (Eq.trans ?_ (ConcreteCategory.comp_apply _ _ _).symm)
    change (Ext.comp x (Ext.mk₀ (SC.X₃.map f)) (add_zero i)).comp (hSC k').extClass rfl =
      Ext.comp (Ext.comp x (hSC k).extClass rfl) (Ext.mk₀ (SC.X₁.map f))
        (add_zero (i + 1))
    calc (Ext.comp x (Ext.mk₀ (SC.X₃.map f)) (add_zero i)).comp (hSC k').extClass rfl
        = Ext.comp x ((Ext.mk₀ (SC.X₃.map f)).comp (hSC k').extClass (zero_add 1))
            rfl :=
          Ext.comp_assoc_of_second_deg_zero _ _ _ _
      _ = Ext.comp x ((hSC k).extClass.comp (Ext.mk₀ (SC.X₁.map f)) (add_zero 1))
            rfl :=
          congrArg (fun e ↦ Ext.comp x e rfl) hnat.symm
      _ = Ext.comp (Ext.comp x (hSC k).extClass rfl) (Ext.mk₀ (SC.X₁.map f))
            (add_zero (i + 1)) :=
          (Ext.comp_assoc_of_third_deg_zero _ _ _ _).symm

variable {SC : ShortComplex (ℕᵒᵖ ⥤ A)}

omit [HasExt.{w} (ℕᵒᵖ ⥤ A)] [EnoughInjectives A] [HasProductsOfShape ℕ A] in
/-- Componentwise, `levelDelta` is postcomposition with the levelwise extension class. -/
lemma levelDelta_app_apply
    (hSCk : ∀ k : ℕᵒᵖ, (SC.map ((evaluation ℕᵒᵖ A).obj k)).ShortExact) (i : ℕ) (k : ℕᵒᵖ)
    (x : Ext Z (SC.X₃.obj k) i) :
    ConcreteCategory.hom ((levelDelta Z hSCk i).app k) x = x.comp (hSCk k).extClass rfl :=
  rfl

omit [HasExt.{w} (ℕᵒᵖ ⥤ A)] [EnoughInjectives A] [HasProductsOfShape ℕ A] in
/-- Componentwise, whiskering `SC.g` with the `Ext`-functor is postcomposition with
`mk₀` of the corresponding component of `SC.g`. -/
lemma whiskerRight_extFunctorObj_app_apply (i : ℕ) (k : ℕᵒᵖ)
    (x : Ext Z (SC.X₂.obj k) i) :
    ConcreteCategory.hom ((Functor.whiskerRight SC.g (extFunctorObj Z i)).app k) x =
      x.comp (Ext.mk₀ ((SC.map ((evaluation ℕᵒᵖ A).obj k)).g)) (add_zero i) :=
  rfl


end Main

end Ext
end Abelian
end CategoryTheory


