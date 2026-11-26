-- Prove2me | Definitions.Def_ProEtale_Mathlib_CategoryTheory_Sites_SheafCohomology_FreeAbelianSheaf
-- name    : ProEtale_Mathlib_CategoryTheory_Sites_SheafCohomology_FreeAbelianSheaf
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T16:59:31.904775+00:00
-- url     : https://prove2.me/theorems/a2d605b8-b543-5675-8eee-700059cc620a
-- title:
--   The free abelian sheaf on an object of a site and its sections adjunction
-- statement:
--   Let $(\mathcal C, J)$ be a site such that sheafification of abelian presheaves exists (in the universe of the coefficients). For an object $U \in \mathcal C$, the **free abelian sheaf** $\mathbb Z_U$ is the sheafification of the presheaf $V \mapsto \mathbb Z[\operatorname{Hom}(V, U)]$ of free abelian groups on the presheaf represented by $U$. This gives a functor
--   $$ \mathcal C \longrightarrow \mathrm{Sh}(\mathcal C, J; \mathrm{Ab}), \qquad U \mapsto \mathbb Z_U .$$
--
--   Principal result: for every abelian sheaf $F$ there is a natural bijection
--   $$ \operatorname{Hom}(\mathbb Z_U, F) \;\cong\; F(U), $$
--   obtained by composing the sheafification adjunction, the free–forgetful adjunction for abelian groups and the Yoneda lemma.
--
--   This functor is the one appearing in the definition of sheaf cohomology as a presheaf, and is used to compute cohomology via free abelian sheaves on objects of the pro-étale site.
--
--   **Formalization Note** The category is large: `C : Type (u + 1)` with morphisms in `Type u`, and sheaves are valued in `AddCommGrpCat.{u + 1}`, assuming `[HasWeakSheafify J AddCommGrpCat.{u + 1}]`; representable presheaves are lifted to universe `u+1` via `uliftYoneda`. The declarations are `CategoryTheory.freeAbelianSheafFunctor J` and `CategoryTheory.freeAbelianSheafHomEquiv`, an `Equiv` between `(freeAbelianSheafFunctor J).obj U ⟶ F` and the underlying set of `F` evaluated at `op U`.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Mathlib/CategoryTheory/Sites/SheafCohomology/FreeAbelianSheaf.lean (declarations needed by the transplanted proofs, unused ones removed).

/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
/-!
# Free abelian sheaves on objects of a site

For a site `(C, J)` we define the free abelian sheaf functor sending `U : C` to the
sheafification of the free abelian group presheaf on the (universe-lifted) presheaf
represented by `U`. This is the composite appearing in mathlib's
`Sheaf.cohomologyPresheafFunctor`, in a universe setting where the coefficients live
one universe above the morphisms of `C`.

We provide the basic "sections" adjunction: morphisms from the free abelian sheaf on `U`
to a sheaf `F` are in bijection with the sections of `F` over `U`.
-/

universe u

open CategoryTheory Limits Opposite

namespace CategoryTheory

variable {C : Type (u + 1)} [Category.{u} C]
variable (J : GrothendieckTopology C) [HasWeakSheafify J AddCommGrpCat.{u + 1}]

/-- The free abelian sheaf functor, sending `U : C` to the sheafification of the
free abelian group presheaf on the (universe-lifted) presheaf represented by `U`.
This is the composite appearing in `Sheaf.cohomologyPresheafFunctor`. -/
noncomputable def freeAbelianSheafFunctor : C ⥤ Sheaf J AddCommGrpCat.{u + 1} :=
  uliftYoneda.{u + 1} ⋙ (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free ⋙
    presheafToSheaf J _

variable {J}

/-- Morphisms from the free abelian sheaf on `U` to a sheaf `F` are sections of `F`
over `U`. -/
noncomputable def freeAbelianSheafHomEquiv {U : C} {F : Sheaf J AddCommGrpCat.{u + 1}} :
    ((freeAbelianSheafFunctor J).obj U ⟶ F) ≃
      ((sheafToPresheaf J _).obj F ⋙ forget AddCommGrpCat.{u + 1}).obj (op U) :=
  ((sheafificationAdjunction J _).homEquiv _ _).trans <|
    (((Adjunction.whiskerRight Cᵒᵖ AddCommGrpCat.adj.{u + 1}).homEquiv _ _).trans
      uliftYonedaEquiv)

end CategoryTheory


