-- Prove2me | Definitions.Def_ProEtale_Mathlib_AlgebraicGeometry_Extensive
-- name    : ProEtale_Mathlib_AlgebraicGeometry_Extensive
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T17:37:01.495391+00:00
-- url     : https://prove2.me/theorems/b04f4a57-e13c-4318-b239-edc7e8487bc9
-- title:
--   Affine schemes form a finitary extensive category; sheaf composition preserves limits
-- statement:
--   This file proves:
--
--   1. Let $(\mathcal C, J)$ be a site and $F : \mathcal A \to \mathcal B$ a functor such that composing with $F$ sends $J$-sheaves to $J$-sheaves. If $F$ preserves limits of shape $K$ and $\mathcal A$ has such limits, then the induced functor on sheaves $\mathrm{Sh}_J(\mathcal A) \to \mathrm{Sh}_J(\mathcal B)$ preserves limits of shape $K$.
--   2. For a finite type $\iota$, the discrete category on $\iota$ is finite.
--   3. For a finite (and $u$-small) index type $\iota$, the inclusion of affine schemes into schemes creates coproducts indexed by $\iota$: a finite disjoint union of affine schemes is affine.
--   4. The category of affine schemes is finitary extensive: finite coproducts exist, are disjoint, and are stable under pullback.
--
--   Finitary extensivity of affine schemes is used to handle finite disjoint unions of affine objects in the affine pro-étale and étale sites (e.g. for the coherence of these sites).
--
--   **Formalization Note** The results are anonymous instances: `PreservesLimitsOfShape K (sheafCompose J F)`, `Finite (Discrete ι)`, `CreatesColimitsOfShape (Discrete ι) AffineScheme.forgetToScheme`, and `FinitaryExtensive AffineScheme.{u}`. Item 4 is deduced from the extensivity of schemes since the inclusion preserves and reflects the relevant (co)limits.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Mathlib/AlgebraicGeometry/Extensive.lean (declarations needed by the transplanted proofs, unused ones removed).

/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Sites.BigZariski
import Mathlib.AlgebraicGeometry.Sites.MorphismProperty
import Mathlib.AlgebraicGeometry.Sites.Pretopology
import Mathlib.CategoryTheory.Limits.MonoCoprod
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Limits.Preserves.Ulift
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import Mathlib.CategoryTheory.Limits.Shapes.DisjointCoproduct
import Mathlib.CategoryTheory.Sites.EffectiveEpimorphic
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Sites.Preserves
import Mathlib.CategoryTheory.Sites.SheafOfTypes
import Mathlib.CategoryTheory.Sites.Sieves
import Mathlib.CategoryTheory.Sites.Subcanonical
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_Sites_Sieves

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
universe v u

open CategoryTheory Limits

namespace CategoryTheory

variable {C : Type*} [Category C] {A B : Type*} [Category A] [Category B]
  (J : GrothendieckTopology C) (F : A ⥤ B) [J.HasSheafCompose F]

instance inst_MathlibAlgebraicGeometryExtensive_L24 (K : Type*) [Category K] [PreservesLimitsOfShape K F] [HasLimitsOfShape K A] :
    PreservesLimitsOfShape K (sheafCompose J F) :=
  have : PreservesLimitsOfShape K (sheafCompose J F ⋙ sheafToPresheaf J B) :=
    inferInstanceAs <| PreservesLimitsOfShape K
      (sheafToPresheaf J A ⋙ (Functor.whiskeringRight Cᵒᵖ A B).obj F)
  CategoryTheory.Limits.preservesLimitsOfShape_of_reflects_of_preserves _
    (sheafToPresheaf J B)

end CategoryTheory

namespace AlgebraicGeometry

instance inst_MathlibAlgebraicGeometryExtensive_L36 {ι : Type*} [Finite ι] : Finite (Discrete ι) :=
  discreteEquiv.finite_iff.mpr inferInstance

noncomputable instance inst_MathlibAlgebraicGeometryExtensive_L39 {ι : Type*} [Small.{u} ι] [Finite ι] :
    CreatesColimitsOfShape (Discrete ι) AffineScheme.forgetToScheme.{u} := by
  let ι' := Shrink.{u} ι
  suffices CreatesColimitsOfShape (Discrete ι') AffineScheme.forgetToScheme.{u} by
    exact createsColimitsOfShapeOfEquiv (Discrete.equivalence (equivShrink ι)).symm
      AffineScheme.forgetToScheme
  refine ⟨fun {K} ↦ ?_⟩
  have : CreatesColimit (Discrete.functor (K.obj ∘ Discrete.mk))
      AffineScheme.forgetToScheme := by
    apply createsColimitOfFullyFaithfulOfIso (.mk (∐ fun i ↦ (K.obj ⟨i⟩).1) inferInstance)
    apply HasColimit.isoOfNatIso
    exact Discrete.natIso fun i ↦ Iso.refl _
  exact createsColimitOfIsoDiagram AffineScheme.forgetToScheme Discrete.natIsoFunctor.symm

instance inst_MathlibAlgebraicGeometryExtensive_L53 : FinitaryExtensive AffineScheme.{u} :=
  finitaryExtensive_of_preserves_and_reflects (AffineScheme.forgetToScheme)

end AlgebraicGeometry


