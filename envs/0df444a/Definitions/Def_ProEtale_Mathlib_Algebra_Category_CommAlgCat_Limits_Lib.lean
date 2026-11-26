-- Prove2me | Definitions.Def_ProEtale_Mathlib_Algebra_Category_CommAlgCat_Limits_Lib
-- name    : ProEtale_Mathlib_Algebra_Category_CommAlgCat_Limits_Lib
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T17:36:55.041388+00:00
-- url     : https://prove2.me/theorems/414f000f-0201-5327-8612-885693ac15e4
-- title:
--   Commutative algebras: tensoring preserves filtered colimits, products are cartesian products, and filtered colimits commute with products
-- statement:
--   This file continues the published file of the same module on limits in the category $\mathrm{CAlg}_R$ of commutative $R$-algebras ($R$ a commutative ring). It proves:
--
--   1. For every commutative $R$-algebra $M$, the functor $N \mapsto M \otimes_R N$ preserves filtered colimits (the tensor product is the coproduct in $\mathrm{CAlg}_R$).
--   2. The forgetful functor $\mathrm{CAlg}_R \to \mathrm{Set}$ preserves (small) limits and reflects filtered colimits.
--   3. $\mathrm{CAlg}_R$ satisfies the IPC property: filtered colimits commute with products, i.e. for families of filtered diagrams $(F_i)_{i}$ the comparison
--   $$\operatorname*{colim}_{(j_i) \in \prod_i J_i} \prod_i F_i(j_i) \longrightarrow \prod_i \operatorname*{colim}_{J_i} F_i$$
--   is an isomorphism.
--   4. The categorical product of a family $(S_i)_{i\in\iota}$ of $R$-algebras is the set-theoretic product $\prod_i S_i$ with the evaluation maps.
--   5. Elementwise simp lemmas for colimit presentations in $\mathrm{CAlg}_R$: compatibility of the colimit injections with transition maps, functoriality of transition maps on elements, and compatibility with algebra maps from $R$.
--
--   These facts are used when manipulating ind-étale and ind-Zariski algebras as filtered colimits, in particular products of such.
--
--   **Formalization Note** Everything lives in universe `u` (`CommAlgCat.{u} R`, index types in `Type u`). Main declarations: `CommAlgCat.preservesColimitsOfShape_tensorLeft`, `CommAlgCat.preservesLimitsOfSize_forget`, the `ReflectsFilteredColimitsOfSize` and `IsIPC.{u}` instances, `CommAlgCat.piFan`, `CommAlgCat.isLimitPiFan`, and `CategoryTheory.Limits.ColimitPresentation.ι_app_diag_map_apply`, `diag_map_id_apply`, `diag_map_comp_apply`, `ι_app_algebraMap_apply`. The tensor-product statement is phrased for `MonoidalCategory.tensorLeft M` and arbitrary filtered index categories.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Mathlib/Algebra/Category/CommAlgCat/Limits.lean (declarations needed by the transplanted proofs, unused ones removed). Continues the published definition file Def_ProEtale_Mathlib_Algebra_Category_CommAlgCat_Limits of the same module.

import Mathlib.Algebra.Category.AlgCat.Basic
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.Algebra.Category.CommAlgCat.Monoidal
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.CategoryTheory.Filtered.Connected
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesProduct
import Mathlib.CategoryTheory.Limits.Presentation
import Mathlib.CategoryTheory.Limits.Preserves.Filtered
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Definitions.Def_ProEtale_Mathlib_Algebra_Category_AlgCat_FilteredColimits
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_Limits_FilteredColimitCommutesProduct
import Definitions.Def_ProEtale_Mathlib_Algebra_Category_CommAlgCat_Limits

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
universe u

open CategoryTheory Limits
open scoped MonoidalCategory

namespace CommAlgCat

variable {R : Type u} [CommRing R]

-- `AI generated`
instance preservesColimitsOfShape_tensorLeft
    {J : Type*} [Category J] [IsFiltered J] (M : CommAlgCat R) :
    PreservesColimitsOfShape J (MonoidalCategory.tensorLeft M) := by
  classical
  haveI : CategoryTheory.IsConnected J := CategoryTheory.IsFiltered.isConnected J
  refine ⟨?_⟩
  intro K
  refine ⟨?_⟩
  intro c hc
  refine ⟨?_⟩
  let t : Cocone (K ⋙ MonoidalCategory.tensorLeft M) :=
    (MonoidalCategory.tensorLeft M).mapCocone c
  -- A cocone on the constant diagram `M`, induced by left injections.
  let leftCocone (s : Cocone (K ⋙ MonoidalCategory.tensorLeft M)) :
      Cocone ((Functor.const J).obj M) :=
    { pt := s.pt
      ι :=
        { app := fun j => (binaryCofan M (K.obj j)).inl ≫ s.ι.app j
          naturality := by
            intro j j' u
            have hu := s.w u
            have hinl :
                (binaryCofan M (K.obj j)).inl ≫ (M ◁ K.map u) = (binaryCofan M (K.obj j')).inl := by
              apply CommAlgCat.hom_ext
              ext x
              simp [binaryCofan, whiskerLeft_hom]
            have hu' := congrArg (fun f => (binaryCofan M (K.obj j)).inl ≫ f) hu
            -- Rewrite the left-hand side using `hinl`.
            -- `hu' : inl_j ≫ (M ◁ K.map u) ≫ s.ι.app j' = inl_j ≫ s.ι.app j`.
            have step1 :
                (binaryCofan M (K.obj j')).inl ≫ s.ι.app j' =
                  (binaryCofan M (K.obj j)).inl ≫ (M ◁ K.map u) ≫ s.ι.app j' := by
              simpa [Category.assoc] using congrArg (fun f => f ≫ s.ι.app j') hinl.symm
            simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp,
              Category.comp_id]
            exact step1.trans hu' } }
  let leftMap (s : Cocone (K ⋙ MonoidalCategory.tensorLeft M)) : M ⟶ s.pt :=
    (isColimitConstCocone J M).desc (leftCocone s)
  -- A cocone on `K`, induced by right injections.
  let rightCocone (s : Cocone (K ⋙ MonoidalCategory.tensorLeft M)) : Cocone K :=
    { pt := s.pt
      ι :=
        { app := fun j => (binaryCofan M (K.obj j)).inr ≫ s.ι.app j
          naturality := by
            intro j j' u
            have hu := s.w u
            have hinr :
                (binaryCofan M (K.obj j)).inr ≫ (M ◁ K.map u) =
                  K.map u ≫ (binaryCofan M (K.obj j')).inr := by
              apply CommAlgCat.hom_ext
              ext x
              simp [binaryCofan, whiskerLeft_hom]
            simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id]
            rw [← Category.assoc, ← hinr, Category.assoc]
            exact congrArg (fun f => (binaryCofan M (K.obj j)).inr ≫ f) hu } }
  let rightMap (s : Cocone (K ⋙ MonoidalCategory.tensorLeft M)) : c.pt ⟶ s.pt :=
    hc.desc (rightCocone s)
  let descFun (s : Cocone (K ⋙ MonoidalCategory.tensorLeft M)) : t.pt ⟶ s.pt :=
    (binaryCofanIsColimit M c.pt).desc (BinaryCofan.mk (leftMap s) (rightMap s))
  have leftMap_eq (s : Cocone (K ⋙ MonoidalCategory.tensorLeft M)) (j : J) :
      leftMap s = (binaryCofan M (K.obj j)).inl ≫ s.ι.app j := by
    simpa [leftMap, leftCocone] using (isColimitConstCocone J M).fac (leftCocone s) j
  have rightMap_eq (s : Cocone (K ⋙ MonoidalCategory.tensorLeft M)) (j : J) :
      c.ι.app j ≫ rightMap s = (binaryCofan M (K.obj j)).inr ≫ s.ι.app j :=
    hc.fac (rightCocone s) j
  have descFun_inl (s : Cocone (K ⋙ MonoidalCategory.tensorLeft M)) :
      (binaryCofan M c.pt).inl ≫ descFun s = leftMap s := by
    simpa [descFun, BinaryCofan.ι_app_left] using
      (binaryCofanIsColimit M c.pt).fac (BinaryCofan.mk (leftMap s) (rightMap s))
        (Discrete.mk WalkingPair.left)
  have descFun_inr (s : Cocone (K ⋙ MonoidalCategory.tensorLeft M)) :
      (binaryCofan M c.pt).inr ≫ descFun s = rightMap s := by
    simpa [descFun, BinaryCofan.ι_app_right] using
      (binaryCofanIsColimit M c.pt).fac (BinaryCofan.mk (leftMap s) (rightMap s))
        (Discrete.mk WalkingPair.right)
  refine (show IsColimit t from ?_)
  refine ⟨descFun, ?_, ?_⟩
  · intro s j
    apply (BinaryCofan.IsColimit.hom_ext (binaryCofanIsColimit M (K.obj j)))
    · have hinl :
          (binaryCofan M (K.obj j)).inl ≫ (M ◁ c.ι.app j) = (binaryCofan M c.pt).inl := by
        apply CommAlgCat.hom_ext
        ext x
        simp [binaryCofan, whiskerLeft_hom]
      -- left part
      have step1 : (binaryCofan M (K.obj j)).inl ≫ t.ι.app j ≫ descFun s =
            (binaryCofan M (K.obj j)).inl ≫ (M ◁ c.ι.app j) ≫ descFun s := by simp [t]
      have step2 : (binaryCofan M (K.obj j)).inl ≫ (M ◁ c.ι.app j) ≫ descFun s =
            (binaryCofan M c.pt).inl ≫ descFun s := by
        simpa [Category.assoc] using congrArg (fun f => f ≫ descFun s) hinl
      exact step1.trans (step2.trans ((descFun_inl s).trans (leftMap_eq s j)))
    · have hinr :
          (binaryCofan M (K.obj j)).inr ≫ (M ◁ c.ι.app j) =
            c.ι.app j ≫ (binaryCofan M c.pt).inr := by
        apply CommAlgCat.hom_ext
        ext x
        simp [binaryCofan, whiskerLeft_hom]
      -- right part
      have rstep1 : (binaryCofan M (K.obj j)).inr ≫ t.ι.app j ≫ descFun s =
            (binaryCofan M (K.obj j)).inr ≫ (M ◁ c.ι.app j) ≫ descFun s := by simp [t]
      have rstep2 : (binaryCofan M (K.obj j)).inr ≫ (M ◁ c.ι.app j) ≫ descFun s =
            c.ι.app j ≫ (binaryCofan M c.pt).inr ≫ descFun s := by
        simpa [Category.assoc] using congrArg (fun f => f ≫ descFun s) hinr
      have rstep3 : c.ι.app j ≫ (binaryCofan M c.pt).inr ≫ descFun s =
            c.ι.app j ≫ rightMap s := by
        simpa [Category.assoc] using congrArg (fun f => c.ι.app j ≫ f) (descFun_inr s)
      have rstep4 : c.ι.app j ≫ rightMap s =
            (binaryCofan M (K.obj j)).inr ≫ s.ι.app j := by simpa using rightMap_eq s j
      exact rstep1.trans (rstep2.trans (rstep3.trans rstep4))
  · intro s m hm
    apply (BinaryCofan.IsColimit.hom_ext (binaryCofanIsColimit M c.pt))
    · -- equality after `inl`
      have hleft : (binaryCofan M c.pt).inl ≫ m = leftMap s := by
        -- Use uniqueness for the colimit of the constant diagram.
        refine (isColimitConstCocone J M).uniq (leftCocone s) ((binaryCofan M c.pt).inl ≫ m) ?_
        intro j
        have hinl :
            (binaryCofan M (K.obj j)).inl ≫ (M ◁ c.ι.app j) = (binaryCofan M c.pt).inl := by
          apply CommAlgCat.hom_ext
          ext x
          simp [binaryCofan, whiskerLeft_hom]
        have h := congrArg (fun f => (binaryCofan M (K.obj j)).inl ≫ f) (hm j)
        have h' :
            (binaryCofan M (K.obj j)).inl ≫ (M ◁ c.ι.app j) ≫ m =
              (binaryCofan M (K.obj j)).inl ≫ s.ι.app j := by
          simpa [t] using h
        have h'' :
            (binaryCofan M c.pt).inl ≫ m =
              (binaryCofan M (K.obj j)).inl ≫ s.ι.app j := by
          have h₁ :
              ((binaryCofan M (K.obj j)).inl ≫ (M ◁ c.ι.app j)) ≫ m =
                (binaryCofan M (K.obj j)).inl ≫ s.ι.app j := by
            simpa [Category.assoc] using h'
          have h₂ :
              (binaryCofan M c.pt).inl ≫ m =
                ((binaryCofan M (K.obj j)).inl ≫ (M ◁ c.ι.app j)) ≫ m := by
            simpa [Category.assoc] using (congrArg (fun f => f ≫ m) hinl).symm
          exact h₂.trans h₁
        simpa [leftCocone] using h''
      exact hleft.trans (by simpa using (descFun_inl s).symm)
    · -- equality after `inr`
      have hright : (binaryCofan M c.pt).inr ≫ m = rightMap s := by
        -- Use that `c` is a colimit cocone.
        apply hc.hom_ext
        intro j
        have hinr :
            (binaryCofan M (K.obj j)).inr ≫ (M ◁ c.ι.app j) =
              c.ι.app j ≫ (binaryCofan M c.pt).inr := by
          apply CommAlgCat.hom_ext
          ext x
          simp [binaryCofan, whiskerLeft_hom]
        have h := congrArg (fun f => (binaryCofan M (K.obj j)).inr ≫ f) (hm j)
        have h' :
            (binaryCofan M (K.obj j)).inr ≫ (M ◁ c.ι.app j) ≫ m =
              (binaryCofan M (K.obj j)).inr ≫ s.ι.app j := by
          simpa [t] using h
        have h'' :
            c.ι.app j ≫ (binaryCofan M c.pt).inr ≫ m =
              (binaryCofan M (K.obj j)).inr ≫ s.ι.app j := by
          rw [← Category.assoc, ← hinr, Category.assoc]
          exact h'
        -- Rewrite the RHS using the definition of `rightMap`.
        rw [rightMap_eq s j]
        simpa [Category.assoc] using h''
      exact hright.trans (by simpa using (descFun_inr s).symm)

-- `forget₂ (CommAlgCat R) CommRingCat` preserves filtered colimits because it factors as
-- `(commAlgCatEquivUnder R).functor ⋙ Under.forget R`, where the equivalence preserves all
-- colimits and `Under.forget` preserves connected (hence filtered) colimits.


instance preservesLimitsOfSize_forget (R : Type u) [CommRing R] :
    PreservesLimitsOfSize.{u, u} (forget (CommAlgCat.{u} R)) := by
  have hfunctor : forget₂ (CommAlgCat.{u} R) CommRingCat.{u} =
      (commAlgCatEquivUnder (CommRingCat.of R)).functor ⋙ Under.forget (CommRingCat.of R) := rfl
  have : PreservesLimitsOfSize.{u, u} (forget₂ (CommAlgCat.{u} R) CommRingCat.{u}) := by
    rw [hfunctor]
    infer_instance
  have h : forget₂ (CommAlgCat.{u} R) CommRingCat.{u} ⋙ forget CommRingCat.{u} =
      forget (CommAlgCat.{u} R) := HasForget₂.forget_comp
  rw [← h]
  infer_instance

instance inst_MathlibAlgebraCategoryCommAlgCatLimits_L237 : ReflectsFilteredColimitsOfSize.{u, u} (forget (CommAlgCat.{u} R)) where
  reflects_filtered_colimits _ _ _ := reflectsColimitsOfShape_of_reflectsIsomorphisms

instance inst_MathlibAlgebraCategoryCommAlgCatLimits_L240 : IsIPC.{u} (CommAlgCat.{u} R) :=
  .of_preservesFilteredColimitsOfSize (forget (CommAlgCat.{u} R))

section Pi

variable {ι : Type u} (S : ι → CommAlgCat.{u} R)

/-- The fan given by the type theoretic product. -/
@[simps! pt]
def piFan : Fan S :=
  Fan.mk (.of R (∀ i, S i)) fun i ↦ ofHom <| Pi.evalAlgHom _ _ i

/-- The categorical product of `R`-algebras is the type theoretic product. -/
def isLimitPiFan : IsLimit (piFan S) where
  lift s := ofHom <| Pi.algHom R (fun i ↦ S i) (fun i ↦ (s.π.app ⟨i⟩).hom)
  fac s := fun ⟨i⟩ ↦ by
    apply CommAlgCat.hom_ext
    ext x
    rfl
  uniq s m hm := by
    apply CommAlgCat.hom_ext
    ext x
    funext i
    have hi := DFunLike.congr_fun (congrArg CommAlgCat.Hom.hom (hm ⟨i⟩)) x
    simp only [piFan_pt, Functor.const_obj_obj, Discrete.functor_obj_eq_as,
      ConcreteCategory.hom_ofHom, Pi.algHom_apply] at hi ⊢
    exact hi

end Pi


end CommAlgCat

namespace CategoryTheory
namespace Limits
namespace ColimitPresentation

variable {R : Type u} [CommRing R] {X : CommAlgCat.{u} R} {ι : Type u} [SmallCategory ι]

/-- For a colimit presentation in `CommAlgCat R`, the colimit injection at the target of a
transition map, applied to the image of an element under that transition map, agrees with the
colimit injection at the source. -/
@[simp]
lemma ι_app_diag_map_apply (P : ColimitPresentation ι X) {i j : ι} (f : i ⟶ j) (x : P.diag.obj i) :
    (P.ι.app j).hom ((P.diag.map f).hom x) = (P.ι.app i).hom x :=
  DFunLike.congr_fun (congrArg CommAlgCat.Hom.hom (P.w f)) x

lemma diag_map_id_apply (P : ColimitPresentation ι X) (i : ι) (x : P.diag.obj i) :
    (P.diag.map (𝟙 i)).hom x = x :=
  DFunLike.congr_fun (congrArg CommAlgCat.Hom.hom (P.diag.map_id i)) x

lemma diag_map_comp_apply (P : ColimitPresentation ι X) {i j k : ι} (f : i ⟶ j) (g : j ⟶ k)
    (x : P.diag.obj i) :
    (P.diag.map (f ≫ g)).hom x = (P.diag.map g).hom ((P.diag.map f).hom x) :=
  DFunLike.congr_fun (congrArg CommAlgCat.Hom.hom (P.diag.map_comp f g)) x

variable {S : Type u} [CommRing S] [Algebra R S] in
/-- For a colimit presentation of `S` as a colimit of `R`-algebras, the colimit injection at `i`
sends the image of `r : R` in the `i`-th object of the diagram to the image of `r` in `S`. -/
lemma ι_app_algebraMap_apply (P : ColimitPresentation ι (CommAlgCat.of R S)) (i : ι) (r : R) :
    (P.ι.app i).hom (algebraMap R (P.diag.obj i) r) = algebraMap R S r :=
  (P.ι.app i).hom.commutes r

end ColimitPresentation
end Limits
end CategoryTheory


