-- Prove2me | Definitions.Def_ProEtale_Pro_PresheafColimit
-- name    : ProEtale_Pro_PresheafColimit
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T17:37:46.53119+00:00
-- url     : https://prove2.me/theorems/f017aabb-3420-473c-a8d2-1073d3719277
-- title:
--   Left Kan extensions along a fully faithful functor preserve filtered colimits whose terms are finitely presentable relative to the colimit
-- statement:
--   Let $L \colon \mathcal C \to \mathcal D$ be a fully faithful functor such that every functor $F \colon \mathcal C \to \mathcal A$ has a pointwise left Kan extension $\operatorname{Lan}_L F$ along $L$ (the abstract form of presheaf pushforward). Let $K \colon J \to \mathcal C$ be a diagram indexed by a small filtered category $J$, let $c$ be a colimit cocone of $L \circ K$ in $\mathcal D$, and assume that for every $X \in \mathcal C$ the functor $\operatorname{Hom}_{\mathcal D}(LX, -)$ preserves the colimit of $L\circ K$ (each $LX$ is finitely presentable with respect to this colimit).
--
--   Principal results, for any $F\colon \mathcal C \to \mathcal A$:
--   1. The functor $J \to (L \downarrow c_{\mathrm{pt}})$ into the comma category of objects of $\mathcal C$ over the colimit, induced by the cocone $c$, is final.
--   2. $F \circ K$ has a colimit.
--   3. The cocone over $F\circ K$ with apex $(\operatorname{Lan}_L F)(c_{\mathrm{pt}})$, built from the Kan extension unit, is a colimit cocone:
--   $$ \operatorname{colim}_{j} F(K_j) \;\cong\; (\operatorname{Lan}_L F)\big(\operatorname{colim}_j L K_j\big). $$
--   4. Hence $\operatorname{Lan}_L F$ preserves the colimit of $L \circ K$.
--
--   Taking $\operatorname{Lan}_L$ to be pushforward of presheaves, this says that presheaf pushforward preserves such filtered colimits, a compactness statement used for pro-objects in this development.
--
--   **Formalization Note** Categories `C D E A` are arbitrary (`Category*`); `E` and `R : E ⥤ D` are declared but unused in the results. The finite-presentability hypothesis is `∀ X : C, PreservesColimit (K ⋙ L) (coyoneda.obj (op (L.obj X)))` together with `[L.Full] [L.Faithful]`, and `J : Type w` is a `SmallCategory` with `[IsFiltered J]`. The declarations are `CategoryTheory.final_costructuredArrowLift_of_isFinitelyPresentable`, `CategoryTheory.hasColimit_of_isFinitelyPresentable`, `CategoryTheory.cocone`, `CategoryTheory.isColimitCocone` and an instance `PreservesColimit (K ⋙ L) (L.leftKanExtension F)`.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Pro/PresheafColimit.lean (declarations needed by the transplanted proofs, unused ones removed).

/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.CategoryTheory.Adjunction.Opposites
import Mathlib.CategoryTheory.Adjunction.Whiskering
import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
import Mathlib.CategoryTheory.Limits.Indization.Category
import Mathlib.CategoryTheory.Limits.Lattice
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import Mathlib.CategoryTheory.Limits.Shapes.FiniteMultiequalizer
import Mathlib.CategoryTheory.Presentable.Basic
import Mathlib.CategoryTheory.Presentable.Finite
import Mathlib.CategoryTheory.Sites.Continuous
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Finite.Sigma
import Mathlib.Data.Finite.Sum
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_Comma_StructuredArrow_Basic
import Definitions.Def_ProEtale_Pro_Basic
import Definitions.Def_ProEtale_Pro_Basic_Lib

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
/-!
# Presheaf pushforward preserves certain colimit

In this file we show that under certain compactness assumptions,
the presheaf pushforward preserves filtered colimits.

Instead of considering presheafs, we consider arbitrary left Kan extensions.
-/

universe w u

open CategoryTheory MorphismProperty Limits

namespace CategoryTheory


section

-- `F` is a presheaf
-- `L` is a continuous functor
variable {C D E A : Type*} [Category* C] [Category* D] [Category* A] [Category* E]
    (L : C ⥤ D) (F : C ⥤ A) [∀ (F : C ⥤ A), L.HasPointwiseLeftKanExtension F]
    (R : E ⥤ D)

variable {J : Type w} [SmallCategory J] (K : J ⥤ C) [IsFiltered J]
variable {c : Cocone (K ⋙ L)} (hc : IsColimit c)

include hc in
lemma final_costructuredArrowLift_of_isFinitelyPresentable
    [∀ X : C, PreservesColimit (K ⋙ L) (coyoneda.obj (.op <| L.obj X))] [L.Full] [L.Faithful] :
    (CostructuredArrow.lift _ c.ι).Final := by
  apply Functor.final_of_exists_of_isFiltered
  · intro d
    obtain ⟨j, p, hp⟩ := exists_hom_of_preservesColimit_coyoneda hc d.hom
    use j
    exact ⟨CostructuredArrow.homMk (L.preimage p)⟩
  · intro d j s s'
    obtain ⟨k, a, heq⟩ := exists_eq_of_preservesColimit_coyoneda_self hc (L.map s.left)
        (L.map s'.left) <| by
      trans d.hom
      · simpa using CostructuredArrow.w s
      · simpa using (CostructuredArrow.w s').symm
    refine ⟨k, a, ?_⟩
    ext
    exact L.map_injective (by simpa using heq)

variable [∀ X : C, PreservesColimit (K ⋙ L) (coyoneda.obj (.op <| L.obj X))] [L.Full] [L.Faithful]

include hc in
lemma hasColimit_of_isFinitelyPresentable : HasColimit (K ⋙ F) := by
  rw [← CostructuredArrow.lift_forget _ c.ι]
  suffices HasColimit (CostructuredArrow.lift K c.ι ⋙ CostructuredArrow.proj L c.pt ⋙ F) by
    exact hasColimit_of_iso (Functor.associator _ _ _)
  have := final_costructuredArrowLift_of_isFinitelyPresentable _ _ hc
  exact Functor.Final.comp_hasColimit _

variable (c) in
@[simps]
noncomputable def cocone : Cocone (K ⋙ F) where
  pt := (L.leftKanExtension F).obj c.pt
  ι :=
    Functor.whiskerLeft K (L.leftKanExtensionUnit F) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight c.ι _ ≫
    (Functor.constComp _ _ _).hom

include L F

noncomputable def isColimitCocone : IsColimit (cocone L F K c) := by
  have : HasColimit (K ⋙ F) := hasColimit_of_isFinitelyPresentable _ _ _ hc
  have : HasColimit ((CostructuredArrow.lift K c.ι ⋙ CostructuredArrow.proj L c.pt) ⋙ F) := this
  have := final_costructuredArrowLift_of_isFinitelyPresentable _ _ hc
  let e : colimit (K ⋙ F) ⟶ _ :=
    (HasColimit.isoOfNatIso
      (Functor.associator (CostructuredArrow.lift K c.ι) (CostructuredArrow.proj L c.pt) _)).hom ≫
      colimit.pre _ _ ≫
      (Functor.leftKanExtensionObjIsoColimit L F c.pt).inv
  have heq : e = colimit.desc _ (cocone L F K c) :=
    colimit.hom_ext fun j ↦ by simp [e]
  suffices IsIso (colimit.desc _ (cocone L F K c)) by
    convert IsColimit.ofPointIso (colimit.isColimit <| K ⋙ F)
    assumption
  rw [← heq]
  infer_instance

instance inst_ProPresheafColimit_L104 : PreservesColimit (K ⋙ L) (L.leftKanExtension F) := by
  constructor
  intro c hc
  let natIso : K ⋙ L ⋙ L.leftKanExtension F ≅ K ⋙ F :=
    Functor.isoWhiskerLeft K (asIso <| (L.lanAdjunction A).unit.app F).symm
  refine ⟨?_⟩
  refine IsColimit.equivOfNatIsoOfIso natIso.symm (cocone L F K c)
      ((L.leftKanExtension F).mapCocone c) ?_ ?_
  · refine Cocone.ext (Iso.refl _) ?_
    intro j
    simp [natIso]
    rfl
  · exact isColimitCocone _ _ _ hc

end

end CategoryTheory


