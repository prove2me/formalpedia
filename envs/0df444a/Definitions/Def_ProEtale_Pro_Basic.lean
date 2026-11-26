-- Prove2me | Definitions.Def_ProEtale_Pro_Basic
-- name    : ProEtale_Pro_Basic
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T12:13:27.784581+00:00
-- url     : https://prove2.me/theorems/dc316ae5-0ff8-4095-b829-2452317ebc1d
-- title:
--   Presheaves that turn cofiltered limits coming from a subcategory into colimits
-- statement:
--   For a functor $F : C \to D$ and a presheaf $P$ on $D$, the property `Functor.PreservesRelativeFilteredColimits F P`: for every small cofiltered diagram $K$ in $C$ and every limit cone over $F \circ K$ in $D$, $P$ sends that cone to a colimit cocone. With $F$ the inclusion of affine étale schemes into pro-étale affines, this is the condition $G(U) = \varinjlim_i G(U_i)$ of Lemma 5.1.2.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014), Lemma 5.1.1 and Lemma 5.1.2. Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Pro/Basic.lean (declarations kept unchanged, unused ones removed).

/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
/-!
# Sheafs in the pro category

In this file we develop conditions for when a presheaf on the pro-category
is a sheaf.
-/

universe s t w v₁ v₂ u₁ u₂


namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D)


open Limits Opposite


variable {J : Type*} [Category J] {X : D} {F : C ⥤ D} {E : PreOneHypercover.{w} X}
  {K : GrothendieckTopology C}


variable {A : Type*} [Category A]


section

variable (J : GrothendieckTopology C) (K : GrothendieckTopology D)


/-- A presheaf `P` on `D` sends limits of small cofiltered diagrams factoring through
`F : C ⥤ D` to colimits in `A`. This is implied by `PreservesFilteredColimitsOfSize.{w, w} P`
(see the instance below), but unlike the latter it can hold for presheaves that do not
preserve arbitrary filtered colimits, e.g. pointwise left Kan extensions along `F.op`. -/
class Functor.PreservesRelativeFilteredColimits (F : C ⥤ D) (P : Dᵒᵖ ⥤ A) : Prop where
  nonempty_isColimit : ∀ {I : Type w} [SmallCategory I] [IsCofiltered I] {K : I ⥤ C}
    (c : Cone (K ⋙ F)), IsLimit c → Nonempty (IsColimit (P.mapCocone c.op))


end

end CategoryTheory


