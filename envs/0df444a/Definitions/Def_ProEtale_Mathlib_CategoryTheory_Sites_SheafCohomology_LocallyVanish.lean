-- Prove2me | Definitions.Def_ProEtale_Mathlib_CategoryTheory_Sites_SheafCohomology_LocallyVanish
-- name    : ProEtale_Mathlib_CategoryTheory_Sites_SheafCohomology_LocallyVanish
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T17:37:18.160287+00:00
-- url     : https://prove2.me/theorems/1ac4dcac-7fbd-48c2-9940-5b493899eabb
-- title:
--   Naturality of the free abelian sheaf adjunction and associativity of degree-zero Ext composition
-- statement:
--   This file gives the supporting lemmas for the module showing that positive-degree classes in $\mathrm{Ext}^{p+1}(\mathbb Z[U], F)$ vanish locally on $U$. That main result itself is not part of this file.
--
--   For a site $(C, J)$ and an object $U \in C$, let $\mathbb Z[U]$ be the free abelian sheaf on $U$. A morphism $\mathbb Z[U] \to F$ of abelian sheaves corresponds to a section in $F(U)$, and we write $s \mapsto \hat s$ for this bijection.
--
--   Results:
--
--   1. **Ext composition with degree zero.** In an abelian category with Ext groups, for $f : X' \to X$ and classes $\alpha \in \mathrm{Ext}^a(X, Y)$ and $\beta \in \mathrm{Ext}^b(Y, Z)$,
--   $$[f] \cdot (\alpha \cdot \beta) = ([f] \cdot \alpha) \cdot \beta,$$
--   where $[f] \in \mathrm{Ext}^0$ is the class of $f$.
--   2. **Naturality in the object.** For $g : W \to U$ and $s : \mathbb Z[U] \to F$, the section corresponding to $\mathbb Z[g] \circ s$ is the restriction $\hat s|_W$ along $g$.
--   3. **Naturality in the sheaf.** For $s : \mathbb Z[U] \to F$ and $\varphi : F \to G$, the section corresponding to $\varphi \circ s$ is $\varphi_U(\hat s)$.
--
--   **Formalization Note** $C$ is a `Type (u+1)` with morphisms in `Type u` (a large site such as the pro-étale site), and sheaves take values in `AddCommGrpCat.{u+1}`. Sheafification is assumed to exist. Declarations: `CategoryTheory.Abelian.Ext.mk₀_comp_comp`, `CategoryTheory.freeAbelianSheafHomEquiv_naturality_left` and `CategoryTheory.freeAbelianSheafHomEquiv_naturality_right`, about `freeAbelianSheafHomEquiv` and `freeAbelianSheafFunctor J` from the published *FreeAbelianSheaf* file. The file ends by declaring section variables (`HasExt`, `EnoughInjectives`, sheaf compatibility of `forget`, `WEqualsLocallyBijective`) for the main theorem, which is not included.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Mathlib/CategoryTheory/Sites/SheafCohomology/LocallyVanish.lean (declarations needed by the transplanted proofs, unused ones removed).

/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_Sites_SheafCohomology_FreeAbelianSheaf

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
/-!
# Positive degree Ext classes from free abelian sheaves vanish locally

Let `(C, J)` be a site and `F` a sheaf of abelian groups on it. We show that any class
`ξ : Ext (ℤ[U]) F (p + 1)`, where `ℤ[U]` is the free abelian sheaf on `U : C`, vanishes
locally: there exists a covering sieve `R` of `U` such that for every `g : W ⟶ U` in `R`,
the restriction of `ξ` along `g` is zero.

The proof is by induction on `p`, generalizing over `F`. Embedding `F` into an injective
sheaf `I` with quotient `Q`, the long exact sequence for `Ext (ℤ[U]) -` shows that `ξ` is
the product of a class `η : Ext (ℤ[U]) Q p` with the extension class of
`0 ⟶ F ⟶ I ⟶ Q ⟶ 0`. For `p = 0`, the class `η` is a section of `Q` over `U`, which
locally lifts to `I` since `I ⟶ Q` is an epimorphism of sheaves, hence locally surjective;
restrictions of `ξ` then factor through the zero composite `(ℤ[W] ⟶ I ⟶ Q) ⋅ extClass`.
For `p > 0` the claim follows directly from the inductive hypothesis applied to `η`.
-/

universe w u

open CategoryTheory Limits Opposite

namespace CategoryTheory

namespace Abelian
namespace Ext

universe w₂ v₂ u₂

variable {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasExt.{w₂} D]

/-- Associativity of `Ext`-composition when the first factor has degree zero. -/
lemma mk₀_comp_comp {X' X Y Z : D} (f : X' ⟶ X) {a b c : ℕ}
    (α : Ext X Y a) (β : Ext Y Z b) (h : a + b = c) :
    (mk₀ f).comp (α.comp β h) (zero_add c) = ((mk₀ f).comp α (zero_add a)).comp β h :=
  (comp_assoc (mk₀ f) α β (zero_add a) h (by lia)).symm

end Ext
end Abelian

open Abelian

variable {C : Type (u + 1)} [Category.{u} C]
variable {J : GrothendieckTopology C} [HasSheafify J AddCommGrpCat.{u + 1}]

/-- `freeAbelianSheafHomEquiv` is natural in the base object: precomposition with
`ℤ[g] : ℤ[W] ⟶ ℤ[U]` corresponds to restriction of sections along `g`. -/
lemma freeAbelianSheafHomEquiv_naturality_left {U W : C} (g : W ⟶ U)
    {F : Sheaf J AddCommGrpCat.{u + 1}} (s : (freeAbelianSheafFunctor J).obj U ⟶ F) :
    freeAbelianSheafHomEquiv ((freeAbelianSheafFunctor J).map g ≫ s) =
      ((sheafToPresheaf J _).obj F ⋙ forget AddCommGrpCat.{u + 1}).map g.op
        (freeAbelianSheafHomEquiv s) := by
  have h₁ := (sheafificationAdjunction J AddCommGrpCat.{u + 1}).homEquiv_naturality_left
    (((Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free).map (uliftYoneda.{u + 1}.map g)) s
  have h₂ := (Adjunction.whiskerRight Cᵒᵖ AddCommGrpCat.adj.{u + 1}).homEquiv_naturality_left
    (uliftYoneda.{u + 1}.map g)
    ((sheafificationAdjunction J AddCommGrpCat.{u + 1}).homEquiv _ _ s)
  have h₃ := (uliftYonedaEquiv_naturality
    ((Adjunction.whiskerRight Cᵒᵖ AddCommGrpCat.adj.{u + 1}).homEquiv _ _
      ((sheafificationAdjunction J AddCommGrpCat.{u + 1}).homEquiv _ _ s)) g.op).symm
  exact (congrArg (fun x ↦ uliftYonedaEquiv
      ((Adjunction.whiskerRight Cᵒᵖ AddCommGrpCat.adj.{u + 1}).homEquiv _ _ x)) h₁).trans
    ((congrArg uliftYonedaEquiv h₂).trans h₃)

/-- `freeAbelianSheafHomEquiv` is natural in the sheaf: postcomposition with `φ : F ⟶ G`
corresponds to applying `φ` to sections. -/
lemma freeAbelianSheafHomEquiv_naturality_right {U : C} {F G : Sheaf J AddCommGrpCat.{u + 1}}
    (s : (freeAbelianSheafFunctor J).obj U ⟶ F) (φ : F ⟶ G) :
    freeAbelianSheafHomEquiv (s ≫ φ) =
      (forget AddCommGrpCat.{u + 1}).map (φ.hom.app (op U)) (freeAbelianSheafHomEquiv s) := by
  simp only [freeAbelianSheafHomEquiv, Equiv.trans_apply]
  erw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_right,
    uliftYonedaEquiv_comp]

variable [J.HasSheafCompose (forget AddCommGrpCat.{u + 1})]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
variable [HasExt.{w} (Sheaf J AddCommGrpCat.{u + 1})]
variable [EnoughInjectives (Sheaf J AddCommGrpCat.{u + 1})]


end CategoryTheory


